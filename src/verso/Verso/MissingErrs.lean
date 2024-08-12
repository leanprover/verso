import Verso.Doc.Elab.Incremental

import Lean

open Lean Elab Command Term
open Verso.Elab

structure Snapshot where
  theList : Task (Array Syntax)
deriving TypeName, Nonempty

instance : IncrementalSnapshot Snapshot (Array Syntax) where
  getIncrState := Snapshot.theList
  mkSnap xs := ⟨xs⟩

abbrev M := StateT (Array Syntax) TermElabM


def myElabTerm (stx : Syntax) : M Unit := do
  let stx : Term := ⟨stx⟩
  match stx with
  | `("magic") =>
    modifyThe (Array Syntax) (·.push (← `(($stx, $stx))))
    IO.sleep 500
  | _ =>
    logInfoAt stx m!"hello {stx}"
    modifyThe (Array Syntax) (·.push (← `(($stx, $stx))))
    IO.sleep 500


declare_syntax_cat bullet
syntax "*" term:max : bullet
declare_syntax_cat bullets
syntax withPosition((colEq bullet)+) : bullets

def _root_.Lean.TSyntax.getBullets (stx : TSyntax `bullets) : Array (TSyntax `term) :=
  match stx with
  | `(bullets|$bs:bullet*) =>
    bs.map fun
      | `(bullet|* $t:term) => t
      | _ => ⟨.missing⟩
  | _ => panic! "Mismatch"

syntax (name := mklist) "make_list" ident bullets : command


-- @[command_elab mklist]
@[command_elab mklist, incremental]
def elabMkList : CommandElab
  | `(make_list $x:ident $entries:bullets) => do
    incrementallyElabCommand entries.getBullets (logInfo "Beginning") myElabTerm
      (run := fun act => do
        let (val, _) ← liftTermElabM <| act #[]
        pure val)
      (endAct := fun st => do
        elabCommand (← `(def $x := [$[$(st.map (⟨·⟩))],*]))
        logInfo "Defined it!")
  | _ => throwUnsupportedSyntax



set_option trace.Elab.reuse true

make_list foo
  * "a"

  * "b"

  * "c"

  * ("d" ())

  * "e"

  * "e'"

  * ("f" ())

  * "magi"

  * "aaaaaa"

  * "magi"


#eval foo
