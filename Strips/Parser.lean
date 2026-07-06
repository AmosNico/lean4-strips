module

import Mathlib.Data.Nat.Notation
import Mathlib.Data.String.Defs
import Init.Data.String.Bootstrap
import Std.Data.Iterators.Combinators.TakeWhile

import Parser

public import Strips.Core

namespace STRIPS.Parser
/-! # Parser for STRIPS Planning Tasks

This file defines a parser for STRIPS planning tasks (TODO : refer to Erikson).
-/

abbrev Parser := SimpleParser String.Slice Char

/-! ## Error Handling for STRIPS parser. -/

/--
Get the line, line number and position in the line of the position `p` in `s`.
Panicks if `p` is not a valid position in `s`.
-/
def positionInfo (s : String) (p : String.Pos.Raw) : String × ℕ × ℕ :=
  if h : p.IsValid s then
    let pos : s.Pos := ⟨p, h⟩
    let startPos := (String.Pos.revFind? pos '\n' >>= String.Pos.next?).getD s.startPos
    let endPos := String.Pos.find pos '\n'
    let line_nb := (s.sliceTo pos).lines.length
    let offset := (s.extract startPos pos).positions.length
    (s.extract startPos endPos, line_nb, offset)
  else
    unreachable!

/--
Format the given error. The second argument is the context where the error occured.
In case of a parsing error this is the input string and for an error related to the certificate this
is the line of the certifcate causing the error.
-/
def formatWithContext : Parser.Error.Simple String.Slice Char → String → Std.Format
  | .unexpected pos none, context =>
    let ⟨line, k, offset⟩ := positionInfo context pos
    f!"Unexpect character on line {k}:\n{line}\n{String.replicate offset ' '}^\n"
  | .unexpected pos (some t), context =>
    let ⟨line, k, offset⟩ := positionInfo context pos
    f!"Unexpect character '{t}' on line {k}:\n{line}\n{String.replicate (offset - 1) ' '}^\n"
  | .addMessage e pos msg, context =>
    let ⟨_, n, k⟩ := positionInfo context pos
    f!"{msg} (line {n}, pos {k})" ++ .indentD (formatWithContext e context)

/-! ## General Parsing functionality -/

def parseSpaces : Parser Unit :=
  Parser.dropMany (Parser.Char.char ' ')

def parseSpaces1 : Parser Unit :=
  Parser.dropMany1 (Parser.Char.char ' ')

-- TODO : check whether allowing semicoloms makes sense
def parseEol : Parser Unit :=
  parseSpaces <* Parser.optional (Parser.Char.char ';') <* Parser.Char.eol

def checkString (s : String) : Parser Unit :=
  Parser.Char.chars s *> parseSpaces

def checkLine (s : String) : Parser Unit :=
  Parser.Char.chars s *> parseEol

-- TODO : rename
def readLine {α} (s : String) (p : Parser α) : Parser α :=
  checkString s *> p <* parseEol

def dropLine : Parser Unit :=
  Parser.dropUntil Parser.Char.eol Parser.anyToken *> pure ()

def parseLine : Parser String :=
  do
    let ⟨⟨l⟩, _⟩ ← Parser.takeUntil Parser.Char.eol Parser.anyToken
    return String.ofList l

def parseWord : Parser String :=
  do
    let stop : Parser Unit := parseSpaces1 <|> (Parser.lookAhead Parser.Char.eol *> pure ())
    let ⟨⟨l⟩, _⟩ ← Parser.takeUntil stop Parser.anyToken
    return String.ofList l

def parseNat : Parser ℕ :=
  Parser.Char.ASCII.parseNat <* parseSpaces

def parseListNat : Parser (List ℕ) := do
  let n ← parseNat
  let ⟨l⟩ ← Parser.take n parseNat
  return l

abbrev push? {α} : Array α → Option α → Array α
| xs, none => xs
| xs, some x => xs.push x

/--
For each tuple `(p, p', e)` in the given list, try the parser `p`. If it succeeds,
run the parser `p'`, otherwise proceed with the next tuple in the list. The optional
error messages `e` are combined into one error message if none of the parsers `p` succeed.
-/
-- Based on `Parser.first`
def parseCases' {α} (ps : List (Parser Unit × Parser α × Option String)) :
  Parser α :=
  go ps #[]
where
  go : List (Parser Unit × Parser α × Option String) → Array String → Parser α
    | [], ⟨e⟩, s, pos =>
      Parser.throwUnexpectedWithMessage none s!"expected one of the following : {e}" s pos
    | (p, p', descr) :: ps, e, s, pos =>
      p s pos >>= fun
      | .ok s pos () => p' s pos
      | .error s _ _ => go ps (push? e descr) s pos

/--
For each of the pairs `(s, p)` in `ps1`, try to parse the string `s`. If it succeeds,
run the parser `p`, otherwise proceed with the next pair in the list. If none of parsers for
`s` is successfull, continue with the list `ps2`. For each pair `(p, p')` in this list, try the
parser `p`, and if it succeed, run `p'` and return its result. If it fails continue with the next
pair. If all pairs fail, combine the strings in `ps1` into one error message.
-/
def parseCases {α} (ps1 : List (String × Parser α)) (ps2 : List (Parser Unit × Parser α) := []) :
  Parser α :=
  let ps1' := ps1.map fun ⟨s, p⟩ ↦ ⟨checkString s, p, s⟩
  let ps2' := ps2.map fun ⟨p, p'⟩ ↦ ⟨p, p', none⟩
  parseCases' (ps1' ++ ps2')


/-! ## STRIPS Parser -/

def parseAtoms : Parser (Array String) :=
  Parser.withErrorMessage "error while parsing atoms"
  do
    let n ← readLine "begin_atoms:" parseNat
    let atoms ← Parser.take n parseLine
    checkLine "end_atoms"
    return atoms

def parseVar {n} : Parser (Fin n) :=
  Parser.withErrorMessage
    s!"expected a reference to an atom, this should be a natural number smaller then {n}"
  do
    let i ← parseNat
    if h : i < n
    then return Fin.mk i h
    else Parser.throwUnexpected

def parseVarLn {n} : Parser (Fin n) := parseVar <* parseEol

def parseVarSet {n} : Parser (VarSet n) :=
  VarSet.ofList <$> Array.toList <$> Parser.takeMany parseVarLn

def parseInit n : Parser (VarSet n) :=
  Parser.withErrorMessage "error while parsing the inital state"
    (checkLine "begin_init" *> parseVarSet <* checkLine "end_init")

def parseGoal n : Parser (VarSet n) :=
  Parser.withErrorMessage "error while parsing the goal"
    (checkLine "begin_goal" *> parseVarSet <* checkLine "end_goal")

structure Conditions n where
  pre : List (Fin n)
  add : List (Fin n)
  del : List (Fin n)

partial def parseConditions {n} (cs : Conditions n) : Parser (Conditions n) :=
  parseCases [
    ("PRE:", return ← parseConditions {cs with pre := (← parseVarLn) :: cs.pre}),
    ("ADD:", return ← parseConditions {cs with add := (← parseVarLn) :: cs.add}),
    ("DEL:", return ← parseConditions {cs with del := (← parseVarLn) :: cs.del}),
    ("end_action", parseEol *> pure cs)
  ]

def parseAction n : Parser (Action n) :=
  do
    checkLine "begin_action"
    let name ← parseLine
    let cost ← readLine "cost:" parseNat
    let ⟨pre, add, del⟩ ← parseConditions (@Conditions.mk n [] [] [])
    return Action.mk name (VarSet.ofList pre) (VarSet.ofList add) (VarSet.ofList del) cost

def parseActions n : Parser (List (Action n)) :=
  Parser.withErrorMessage "error while parsing the actions"
  do
    let k ← readLine "begin_actions:" parseNat
    let as ← Parser.take k (parseAction n)
    checkLine "end_actions"
    return as.toList

def parseSTRIPS : Parser (Σ n, PlanningTask n) :=
  do
    let atoms ← parseAtoms
    let n := atoms.size
    let atoms : Vector String n := ⟨atoms, by rfl⟩
    let init ← parseInit n
    let goal ← parseGoal n
    let actions ← parseActions n
    Parser.endOfInput
    return Sigma.mk n (PlanningTask.mk atoms actions init goal)

public def parseFile (path : System.FilePath) : IO (Σ n, PlanningTask n) :=
  do
    let content ← IO.FS.readFile path
    let p := Parser.withErrorMessage
      s!"An error occured when parsing the STRIPS planning problem at \"{path}\""
      parseSTRIPS
    match p.run content with
    | .ok _ _ res => return res
    | .error _ _ e => throw (IO.userError (formatWithContext e content).pretty)

end STRIPS.Parser
