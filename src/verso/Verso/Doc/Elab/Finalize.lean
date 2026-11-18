module
public import Lean
import Verso.Doc

open Lean
namespace Verso.Doc.Elab.Finalize

public meta initialize docFinalizeAttr : TagAttribute ←
  registerTagAttribute `doc_finalize "Indicate to Verso that this function should be run on documents post-parsing" fun declName => do
    let decl ← getConstInfo declName
    match decl.type with
      | (.app (.const ``Elab.Command.CommandElabM []) (.const ``Unit [])) => return
      | _ => throwError "Decl does not have type `CommandElabM Unit` expected for a document finalizer"

meta def runFinalizer (finalizerName : Name) : Elab.Command.CommandElabM Unit := do
  let finalizer := mkIdent finalizerName
  Elab.Command.elabCommand (← `(#eval $finalizer))

public meta def runFinalizers : Elab.Command.CommandElabM Unit := do
  let state := docFinalizeAttr.ext.toEnvExtension.getState (← getEnv)
  for list in state.importedEntries do
    for finalizerName in list do
      runFinalizer finalizerName
  for finalizerName in state.state do
    runFinalizer finalizerName
