module
public import Lean
import Verso.Doc

open Lean
namespace Verso.Doc.Elab.Finalize

public meta initialize docFinalizeAttr : TagAttribute ←
  registerTagAttribute `doc_finalize "Indicate to Verso that this function should be run on documents post-parsing" fun declName => do
    let decl ← getConstInfo declName
    match decl.type with
      | .forallE _
          (.app (.app (.app (.const `Lean.Doc.Part [.zero, .zero, .zero])
            (.const `Verso.Genre.Manual.Inline []))
            (.const `Verso.Genre.Manual.Block []))
            (.const `Verso.Genre.Manual.PartMetadata []))
          (.app (.const ``Elab.Command.CommandElabM []) (.const ``Unit []))
          _ =>
          return
      | _ => throwError "Decl does not have the expected type for a doc finalize attribute"

meta def runFinalizer (docName : Ident) (finalizerName : Name) : Elab.Command.CommandElabM Unit := do
  let finalizer := mkIdent finalizerName
  let doc ← ``(VersoDoc.toPart $docName)
  Elab.Command.elabCommand (← `(#eval $finalizer $doc))

public meta def runFinalizers (docName : Ident) : Elab.Command.CommandElabM Unit := do
  let state := docFinalizeAttr.ext.toEnvExtension.getState (← getEnv)
  for list in state.importedEntries do
    for finalizerName in list do
      runFinalizer docName finalizerName
  for finalizerName in state.state do
    runFinalizer docName finalizerName
