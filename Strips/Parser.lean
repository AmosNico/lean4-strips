module

import Mathlib.Data.Nat.Notation
import Mathlib.Data.String.Defs
import Init.Data.String.Bootstrap
import Std.Data.Iterators.Combinators.TakeWhile

import ParseIt.Input
import ParseIt.Char

public import Strips.PlanningTask

namespace STRIPS
/-! # Parser for STRIPS Planning Tasks

This file defines a parser for STRIPS planning tasks in the format used by the certificate checker
helve, see https://github.com/salome-eriksson/helve.
-/

/-- Error that keeps the input slice, so it can show the offending line. -/
inductive ParserError where
  | unexpected (s : String.Slice) (pos : String.Pos.Raw) (tok : Option Char)
  | addMessage (e : ParserError) (pos : String.Pos.Raw) (m : String)

/-- The stream that was being parsed when the error happened. -/
def ParserError.stream : ParserError → String.Slice
  | .unexpected s _ _ => s
  | .addMessage e _ _ => e.stream

/-- The position in the stream where the error happened. -/
def ParserError.pos : ParserError → String.Pos.Raw
  | .unexpected _ p _ => p
  | .addMessage e _ _ => e.pos

instance : ParseIt.Error ParserError ParseIt.CharIterator Char where
  unexpected it t := .unexpected it.internalState.slice it.internalState.pos.offset t
  addMessage e it m := .addMessage e it.internalState.pos.offset m
  merge e₁ e₂ := if e₁.pos.byteIdx ≤ e₂.pos.byteIdx then e₂ else e₁

/-- Line number, column, and text of the line that contains position `pos`. -/
def lineInfo (s : String.Slice) (pos : String.Pos.Raw) : Nat × Nat × String :=
  -- lines before `pos` in reverse order
  -- TODO : there is currently a bug in `revSplit`, check whether it has been fixed.
  -- https://github.com/leanprover/lean4/issues/16305
  let before := (s.take pos.byteIdx).revSplit '\n'
  -- lines after `pos`
  let after := (s.drop pos.byteIdx).split '\n'
  let lineNo := before.length - 1
  -- first part of the current line
  let pre := before.first?.getD ""
  let col := pre.positions.length
  -- last part of the current line
  let post := after.first?.getD ""
  (lineNo, col, pre.toString ++ post.toString)

/-- Format the given error. -/
def ParserError.format : ParserError → Std.Format
  | .unexpected s pos none =>
    let ⟨k, offset, line⟩ := lineInfo s pos
    f!"Unexpect character on line {k}:\n{line}\n{String.replicate offset ' '}^\n"
  | .unexpected s p (some t) =>
    let ⟨k, offset, line⟩ := lineInfo s p
    f!"Unexpect character '{t}' on line {k}:\n{line}\n{String.replicate offset ' '}^\n"
  | .addMessage e pos msg =>
    let ⟨n, k, _⟩ := lineInfo e.stream pos
    f!"{msg} (line {n}, pos {k})" ++ .indentD e.format

abbrev Parser := ParseIt.Parser ParserError ParseIt.CharIterator Char

def dropSpaces : Parser Unit :=
  ParseIt.dropMany (ParseIt.Char.char ' ')

def dropEol : Parser Unit :=
  dropSpaces <* ParseIt.Char.eol

def dropString (s : String) : Parser Unit :=
  ParseIt.Char.string s *> dropSpaces

def dropLine (s : String) : Parser Unit :=
  ParseIt.Char.string s *> dropEol

def readLine {α} (s : String) (p : Parser α) : Parser α :=
  dropString s *> p <* dropEol

def parseLine : Parser String :=
  do
    let ⟨⟨l⟩, _⟩ ← ParseIt.takeUntil ParseIt.Char.eol ParseIt.anyToken
    return String.ofList l

def parseNat : Parser ℕ :=
  ParseIt.Char.ASCII.parseNat <* dropSpaces

abbrev push? {α} : Array α → Option α → Array α
| xs, none => xs
| xs, some x => xs.push x

/--
For each tuple `(p, p', e)` in the given list, try the parser `p`. If it succeeds,
run the parser `p'`, otherwise proceed with the next tuple in the list. The optional
error messages `e` are combined into one error message if none of the parsers `p` succeed.
-/
-- Based on `ParseIt.first`
def parseCases' {α} (ps : List (Parser Unit × Parser α × Option String)) :
  Parser α :=
  go ps #[]
where
  go : List (Parser Unit × Parser α × Option String) → Array String → Parser α
    | [], ⟨e⟩, it =>
      ParseIt.throwUnexpectedWithMessage none s!"expected one of the following : {e}" it
    | (p, p', descr) :: ps, es, it => do
      match ← p it with
      | .ok it1 h1 () =>
        match ← p' it1 with
        | .ok it2 h2 x => pure (.ok it2 (.trans h2 h1) x)
        | .error e => .error e
      | .error _  => go ps (push? es descr) it

/--
For each of the pairs `(s, p)` in `ps1`, try to parse the string `s`. If it succeeds,
run the parser `p`, otherwise proceed with the next pair in the list. If none of parsers for
`s` is successfull, continue with the list `ps2`. For each pair `(p, p')` in this list, try the
parser `p`, and if it succeed, run `p'` and return its result. If it fails continue with the next
pair. If all pairs fail, combine the strings in `ps1` into one error message.
-/
def parseCases {α} (ps1 : List (String × Parser α)) (ps2 : List (Parser Unit × Parser α) := []) :
  Parser α :=
  let ps1' := ps1.map fun ⟨s, p⟩ ↦ ⟨dropString s, p, s⟩
  let ps2' := ps2.map fun ⟨p, p'⟩ ↦ ⟨p, p', none⟩
  parseCases' (ps1' ++ ps2')

def parseAtoms : Parser (Array String) :=
  ParseIt.withErrorMessage "error while parsing atoms"
  do
    let n ← readLine "begin_atoms:" parseNat
    let atoms ← ParseIt.take n parseLine
    dropLine "end_atoms"
    return atoms

def parseVar {n} : Parser (Fin n) :=
  ParseIt.withErrorMessage
    s!"expected a reference to an atom, this should be a natural number smaller then {n}"
  do
    let i ← parseNat
    if h : i < n
    then return Fin.mk i h
    else ParseIt.throwUnexpected

def parseVarLn {n} : Parser (Fin n) := parseVar <* dropEol

def parseVarSet {n} : Parser (VarSet n) :=
  VarSet.ofList <$> Array.toList <$> ParseIt.takeMany parseVarLn

def parseInit n : Parser (VarSet n) :=
  ParseIt.withErrorMessage "error while parsing the inital state"
    (dropLine "begin_init" *> parseVarSet <* dropLine "end_init")

def parseGoal n : Parser (VarSet n) :=
  ParseIt.withErrorMessage "error while parsing the goal"
    (dropLine "begin_goal" *> parseVarSet <* dropLine "end_goal")

structure Conditions n where
  pre : List (Fin n)
  add : List (Fin n)
  del : List (Fin n)

partial def parseConditions {n} (cs : Conditions n) : Parser (Conditions n) :=
  parseCases [
    ("PRE:", return ← parseConditions {cs with pre := (← parseVarLn) :: cs.pre}),
    ("ADD:", return ← parseConditions {cs with add := (← parseVarLn) :: cs.add}),
    ("DEL:", return ← parseConditions {cs with del := (← parseVarLn) :: cs.del}),
    ("end_action", dropEol *> pure cs)
  ]

def parseAction n : Parser (Action n) :=
  do
    dropLine "begin_action"
    let name ← parseLine
    let cost ← readLine "cost:" parseNat
    let ⟨pre, add, del⟩ ← parseConditions (@Conditions.mk n [] [] [])
    return Action.mk name (VarSet.ofList pre) (VarSet.ofList add) (VarSet.ofList del) cost

def parseActions n : Parser (List (Action n)) :=
  ParseIt.withErrorMessage "error while parsing the actions"
  do
    let k ← readLine "begin_actions:" parseNat
    let as ← ParseIt.take k (parseAction n)
    dropLine "end_actions"
    return as.toList

def parsePlanningTask : Parser (Σ n, PlanningTask n) :=
  do
    let atoms ← parseAtoms
    let n := atoms.size
    let atoms : Vector String n := ⟨atoms, by rfl⟩
    let init ← parseInit n
    let goal ← parseGoal n
    let actions ← parseActions n
    ParseIt.endOfInput
    return Sigma.mk n (PlanningTask.mk atoms actions init goal)

/--
Parse a STRIPS planning problem from the given file. The file is expected to have the following
format:

    begin_atoms: <#atoms>
    <atom 0>
    <atom 1>
    . . . (names of all atoms, one on each line)
    end_atoms
    begin_init
    <initital state atom index 0>
    <initital state atom index 1>
    . . . (indexes of atoms that are true in initial state, one on each line)
    end_init
    begin_goal
    <goal atom index 0>
    <goal atom index 1>
    . . . (indexes of atoms that are true in goal, one on each line)
    end_goal
    begin_actions: <#actions>
    begin_action
    <action_name>
    cost: <action_cost>
    PRE: <precondition atom index 0>
    ADD: <added atom index 0>
    DEL: <deleted atom index 0>
    . . . (more PRE, ADD and DEL in any order, one on each line)
    end_action
    . . . (more actions)
    end_actions

-/
public def readPlanningTask (path : System.FilePath) : IO (Σ n, PlanningTask n) :=
  do
    let content ← IO.FS.readFile path
    let p : Parser ((n : ℕ) × PlanningTask n) := ParseIt.withErrorMessage
      s!"An error occured when parsing the STRIPS planning problem at \"{path}\""
      parsePlanningTask
    match p.parseString content with
    | .ok res => return res
    | .error e => throw (IO.userError e.format.pretty)

end STRIPS
