import Lean.Elab.Import

/-! Prints the position (1-based line, 0-based column)
of the first token after the header of a Lean file. -/

open Lean

def headerEnd (input : String) (fileName : String) : IO Position := do
  let (_, pos, messages) ← Lean.Elab.parseImports input fileName
  if messages.hasErrors then
    for msg in messages.toArray do
      IO.eprintln (← msg.toString)
    throw <| IO.userError s!"failed to parse the header of '{fileName}'"
  return pos

def main (args : List String) : IO Unit := do
  let [pathArg] := args
    | throw <| IO.userError "usage: lean --run HeaderEnd.lean <file>"
  let text ← IO.FS.readFile ⟨pathArg⟩
  let pos ← headerEnd text pathArg
  IO.println s!"{pos.line}:{pos.column}"
