/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.IsTest
public import Errata.Runner
public import Errata.TestRegistry
public import Lean
public meta import Lean
public meta import Errata.TestRegistry
public meta import Errata.NameJson
public meta import Errata.Widget

open Lean Meta Elab Term

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
Builds the action that runs a declaration as a test, using the {name}`IsTest` instance for its type
that is visible at the declaration. The declaration must not be {lit}`meta` or universe polymorphic.
-/
meta def testAction (decl : Name) : MetaM Expr := do
  let env ← getEnv
  if isMarkedMeta env decl then
    throwError m!"A test must not be `meta`"
  let info ← getConstInfo decl
  unless info.levelParams.isEmpty do
    throwError m!"A test must not be universe polymorphic"
  let goal := mkApp (mkConst ``IsTest) info.type
  match ← trySynthInstance goal with
  | .some inst =>
    return mkApp3 (mkConst ``IsTest.toTest) info.type (← instantiateMVars inst) (mkConst decl)
  | _ =>
    throwError m!"`@[test]` requires an `Errata.IsTest` instance for the test's type{indentExpr info.type}"

/--
Records a declaration as a test. The action that runs it is compiled into a private definition
beside it, so the {name}`IsTest` instance in force here is the one that runs it wherever it is run.
The docstring is read here, while it is still in the live environment, since a downstream build does
not load the imported docstrings.
-/
meta def recordTest (decl : Name) : AttrM Unit := do
  if (testExt.getState (← getEnv)).any (·.name == decl) then
    throwError m!"`{privateToUserName decl}` is already marked as a test"
  let action ← (testAction decl).run'
  let run := mkPrivateName (← getEnv) (← mkFreshUserName (privateToUserName decl ++ `run))
  let type := mkApp (mkConst ``TestM) (mkConst ``Unit)
  let val ← mkDefinitionValInferringUnsafe run [] type action .opaque
  addAndCompile (.defnDecl val)
  let docstring? ← findDocString? (← getEnv) decl
  modifyEnv (testExt.addEntry · {
    name := decl, run, isUnsafe := val.safety == .unsafe, file := ← getFileName, docstring?
  })

/-- A synthetic syntax carrying the given source range, used to position the widget. -/
meta def rangeSyntax [Monad m] [MonadFileMap m]
    (startPos stopPos : String.Pos.Raw) : m Syntax := do
  let str := (← getFileMap).source
  let leading : Substring.Raw := { str, startPos, stopPos := startPos }
  let trailing : Substring.Raw := { str, startPos := stopPos, stopPos }
  return Syntax.atom (.original leading startPos trailing stopPos) ""

/-- The text of line {lean}`i`, trimmed of surrounding whitespace. -/
private meta def lineText (lines : Array String) (i : Nat) : String :=
  ((lines[i]?).getD "").trimAscii.copy

/-- The first non-blank line at or above {lean}`i`, or {lean}`none` if all are blank up to the top. -/
private meta partial def firstNonBlankUp (lines : Array String) (i : Nat) : Option Nat :=
  if (lineText lines i).isEmpty then
    if i == 0 then none else firstNonBlankUp lines (i - 1)
  else some i

/-- Scanning up from {lean}`i`, the line that opens a doc comment, stopping at a non-comment line. -/
private meta partial def docOpenLine (lines : Array String) (i : Nat) : Option Nat :=
  if (lineText lines i).startsWith "/--" then some i
  else if (lineText lines i).startsWith "/-" then none
  else if i == 0 then none
  else docOpenLine lines (i - 1)

/--
The 0-based start line of a doc comment immediately above {lean}`markerLineIdx`, if any. To avoid
mistaking an unrelated trailing comment for one, the comment must be a single-line doc comment or
have its closing delimiter on its own line opened by a doc-comment line.
-/
private meta def docStartLine? (lines : Array String) (markerLineIdx : Nat) : Option Nat := do
  guard (markerLineIdx > 0)
  let endLine ← firstNonBlankUp lines (markerLineIdx - 1)
  let t := lineText lines endLine
  if t.startsWith "/--" && t.endsWith "-/" then return endLine
  guard (t == "-/" && endLine > 0)
  docOpenLine lines (endLine - 1)

/--
The source range to show the test's widget over: the whole declaration, including a doc comment above
it. The recorded declaration range is used when available; otherwise the command is re-parsed from the
start of the marker's line, extending up over an immediately preceding doc comment. Falls back to the
marker itself.
-/
meta def widgetRangeSyntax (decl : Name) (attrStx : Syntax) : AttrM Syntax := do
  let fileMap ← getFileMap
  if let some ranges ← findDeclarationRanges? decl then
    let stx ← rangeSyntax (fileMap.ofPosition ranges.range.pos) (fileMap.ofPosition ranges.range.endPos)
    return stx
  let some attrPos := attrStx.getPos? | return attrStx
  let lineStart := fileMap.ofPosition ⟨(fileMap.toPosition attrPos).line, 0⟩
  let inputCtx := Parser.mkInputContext fileMap.source (← getFileName)
  let pmctx : Parser.ParserModuleContext := { env := ← getEnv, options := ← getOptions }
  let (cmdStx, _, _) := Parser.parseCommand inputCtx pmctx { pos := lineStart } {}
  match cmdStx.getRange? with
  | some range =>
    -- Extend the span up over a doc comment immediately above the marker, when there is one.
    let lines := (fileMap.source.splitOn "\n").toArray
    let startPos := match docStartLine? lines ((fileMap.toPosition attrPos).line - 1) with
      | some docIdx => fileMap.ofPosition ⟨docIdx + 1, 0⟩
      | none => range.start
    rangeSyntax startPos range.stop
  | none => return attrStx

/-- Marks a definition as a test, discovered and run by the Errata test runner. -/
meta initialize
  registerBuiltinAttribute {
    ref := `Errata.test
    name := `test
    descr := "Marks a definition as a test, discovered and run by the Errata test runner."
    -- Applied after compilation so the declaration's docstring is in the environment to capture.
    applicationTime := .afterCompilation
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `test kind
      recordTest decl
      -- Show the widget when the cursor is anywhere on the declaration, not just on the marker.
      let widgetStx ← widgetRangeSyntax decl stx
      -- A hash of the test's source, so a run is invalidated when the test is edited.
      let source := (← getFileMap).source
      let version := match widgetStx.getRange? with
        | some range =>
          let sub : Substring.Raw := { str := source, startPos := range.start, stopPos := range.stop }
          toString sub.toString.hash
        | none => ""
      let props := pure <| json% {
        decl: $(Errata.nameToJson decl),
        module: $(toString (← getMainModule)),
        name: $(toString (privateToUserName decl)),
        version: $version
      }
      Lean.Widget.savePanelWidgetInfo Errata.Widget.runTestWidget.javascriptHash.val props widgetStx
  }

/-- The test's name below its module: the declaration's components past the module prefix, dotted. -/
meta def testNameBelow (moduleName declName : Name) : String :=
  let below :=
    if moduleName.isPrefixOf declName then declName.components.drop moduleName.components.length
    else declName.components
  ".".intercalate (below.map (·.toString))

/--
A module to read tests from: the module itself, or, with a trailing {lit}`.*`, the module and every
imported module below it.
-/
syntax testModules := ident ("." "*")?

/--
{lit}`getAllTests% "package" Mod.A Mod.B.* ...` reads the tests recorded by {lit}`@[test]` in the
named modules, and expands to the array of {name}`TestEntry` values that run them. A name with a
trailing {lit}`.*` also names every imported module below it. Even if a module is named more than
once, its tests are not duplicated. Each module must be imported, with {lit}`import all` for
module-system modules, so its tests are reachable. Unsafe tests are wrapped in
{kw (of := Lean.Parser.Term.unsafe)}`unsafe`.
-/
syntax (name := getAllTests) "getAllTests%" str testModules* : term

/-- Expands {lit}`getAllTests%` by reading the recorded tests of the named modules. -/
@[term_elab getAllTests]
meta def elabGetAllTests : TermElab := fun stx expectedType? => do
  let `(getAllTests% $pkg:str $specs:testModules*) := stx
    | throwUnsupportedSyntax
  let package := pkg.getString
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let mut entries : Array Term := #[]
  -- A module may be named twice, or be selected by a name that ends in `.*`. Nonetheless, its tests
  -- are gathered only once.
  let mut seen : NameSet := {}
  for spec in specs do
    let (modStx, below) ← match spec with
      | `(testModules| $m:ident.*) => pure (m, true)
      | `(testModules| $m:ident) => pure (m, false)
      | _ => throwUnsupportedSyntax
    let rootName := modStx.getId
    let some rootIdx := env.getModuleIdx? rootName
      | throwErrorAt modStx "Module `{rootName}` is not imported, so its tests cannot be \
          reached. Import it, using `import all {rootName}` if it belongs to the module system."
    let mut chosen : Array (Name × ModuleIdx) := #[(rootName, rootIdx)]
    if below then
      for h : idx in [0 : moduleNames.size] do
        if rootName.isPrefixOf moduleNames[idx] then chosen := chosen.push (moduleNames[idx], idx)
    for (moduleName, idx) in chosen do
      if seen.contains moduleName then continue
      seen := seen.insert moduleName
      let moduleStr := moduleName.toString
      for test in testExt.getModuleEntries env idx do
        -- The internal name is used here, because the user-facing name can be ambiguous for private
        -- tests
        let userName := privateToUserName test.name
        let testName := testNameBelow moduleName userName
        let range ← findDeclarationRanges? test.name
        let location : Location := {
          file := test.file
          startPos := (range.map (·.range.pos)).getD ⟨0, 0⟩
          endPos := (range.map (·.range.endPos)).getD ⟨0, 0⟩
        }
        -- The docstring captured when the attribute was applied, so the report and widget can show it.
        let docStx ← match test.docstring? with
          | some doc => `(some $(quote doc))
          | none => `((none : Option String))
        let ref ← `(@$(mkCIdent test.run))
        let run ← if test.isUnsafe then `(unsafe $ref) else pure ref
        entries := entries.push <| ←
          `({ package := $(quote package), moduleName := $(quote moduleStr),
              test := $(quote testName), location := $(← exprToSyntax (toExpr location)),
              docstring? := $docStx, run := $run : Errata.TestEntry })
  elabTerm (← `(#[$entries,*])) expectedType?
