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
  logInfoAt stx m!"hello {stx}"
  let stx := ⟨stx⟩
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
    let (done, st') ← incrementallyElabCommand entries.getBullets (logInfo "Beginning") (logInfo "Done") myElabTerm fun act => do
      let (val, _) ← liftTermElabM <| act #[]
      pure val
    elabCommand (← `(def $x := [$[$(st'.map (⟨·⟩))],*]))
    logInfo "Defined it!"
    done
  | _ => throwUnsupportedSyntax



set_option trace.Elab.reuse true


-- Incrementality issue reproducer!
--
-- To experience:
-- 1. Restart the file
-- 2. Edit "d" below to be "(d ())", but don't restart the file
--
-- Observations:
--  * Messages from earlier lines "a"-"c" are not shown anymore
--  * The expected elaboration error for ("d" ()) is not shown at all, but its output is
--  * From time to time, editing the file gets elaboration stuck entirely - probably an unresolved
--    promise somewhere?
--  * The expected elaboration error from "(d ())" never appears, even when restarting the file.
--    Removing the `incremental` attribute above fixes this problem, but elaboration does still seem
--    to get stuck with the whole file yellow sometimes (e.g. while editing this comment right now).

make_list foo
  * "a"

  * "b"

  * "c"

  * "d"

  * "e"

  * "f"


#eval foo
