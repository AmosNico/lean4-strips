import Strips.Parser

open STRIPS

def main : IO Unit :=
  do
    try
      let path <- IO.currentDir
      let pt_path := path / "test" / "task1.txt"
      let ⟨_, pt⟩ <- Parser.parseFile pt_path
      IO.println (repr pt)
    catch e =>
      IO.println e
