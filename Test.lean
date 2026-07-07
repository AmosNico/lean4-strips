import Strips.Parser

open STRIPS

def main : IO Unit :=
  do
    try
      let path <- IO.currentDir
      let pt_path := path / "test" / "task1.txt"
      let ⟨_, pt⟩ <- readPlanningTask pt_path
      IO.println pt
    catch e =>
      IO.println e
