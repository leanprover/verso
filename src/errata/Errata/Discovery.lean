/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Errata.IsTest
public import Errata.Runner
public import Lean
public meta import Lean
public meta import Errata.NameJson
public meta import Errata.Widget

open Lean Meta Elab Term

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata

/--
Verifies that a tagged declaration can be run as a test: it is not {lit}`meta`, and it has an
{name}`IsTest` instance.
-/
meta def checkIsTest (decl : Name) : MetaM Unit := do
  let env ← getEnv
  if isMarkedMeta env decl then
    throwError m!"A test must not be `meta`"
  let info ← getConstInfo decl
  let goal := mkApp (mkConst ``IsTest) info.type
  match ← trySynthInstance goal with
  | .some _ => pure ()
  | _ =>
    throwError m!"`@[test]` requires an `Errata.IsTest` instance for the test's type{indentExpr info.type}"

/--
A recorded test: its declaration name and the source file that defines it. The file is captured
when the attribute is applied; the declaration's line and column are recovered later, once the
declaration ranges are available.
-/
structure TestDecl where
  /-- The test declaration's name. -/
  name : Name
  /-- The source file that defines the test. -/
  file : String
  /-- The test's docstring, rendered as Markdown, captured when the attribute is applied. -/
  docstring? : Option String := none
deriving Inhabited

/--
The tests recorded by {lit}`@[test]`, per module. The attribute is an elaboration-time feature:
tests are recorded as modules are elaborated, and {lit}`getAllTests%` reads them back at elaboration
time to build the runnable test array.
-/
meta initialize testExt : SimplePersistentEnvExtension TestDecl (Array TestDecl) ←
  registerSimplePersistentEnvExtension {
    name := `Errata.test
    addEntryFn := Array.push
    addImportedFn := fun es => es.foldl Array.append #[]
  }

/-- Records a declaration as a test, capturing the source file that defines it and its docstring.
The docstring is read here, while it is still in the live environment, since a downstream build does
not load the imported docstrings. -/
meta def recordTest (decl : Name) : AttrM Unit := do
  (checkIsTest decl).run'
  let docstring? ← findDocString? (← getEnv) decl
  modifyEnv (testExt.addEntry · { name := decl, file := ← getFileName, docstring? })

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
{lit}`getAllTests% "package" Mod.A Mod.B ...` reads the tests recorded by {lit}`@[test]` in the
named modules and expands to the array of {name}`TestEntry` values that run them. Each module must
be imported, with {lit}`import all` for module-system modules, so its tests are reachable.
-/
syntax (name := getAllTests) "getAllTests%" str ident* : term

/-- Expands {lit}`getAllTests%` by reading the recorded tests of the named modules. -/
@[term_elab getAllTests]
meta def elabGetAllTests : TermElab := fun stx expectedType? => do
  let `(getAllTests% $pkg:str $mods:ident*) := stx
    | throwUnsupportedSyntax
  let package := pkg.getString
  let env ← getEnv
  let mut entries : Array Term := #[]
  for modStx in mods do
    let moduleName := modStx.getId
    let some idx := env.getModuleIdx? moduleName | continue
    let moduleStr := moduleName.toString
    for test in testExt.getModuleEntries env idx do
      let userName := privateToUserName test.name
      let testName := testNameBelow moduleName userName
      let range ← findDeclarationRanges? test.name
      let pos := (range.map (·.range.pos)).getD ⟨0, 0⟩
      let endPos := (range.map (·.range.endPos)).getD ⟨0, 0⟩
      -- The docstring captured when the attribute was applied, so the report and widget can show it.
      let docStx ← match test.docstring? with
        | some doc => `(some $(quote doc))
        | none => `((none : Option String))
      entries := entries.push <| ←
        `(Errata.TestEntry.of $(quote package) $(quote moduleStr) $(quote testName)
            (Errata.Location.mk $(quote test.file)
              (Errata.Position.mk $(quote pos.line) $(quote pos.column))
              (Errata.Position.mk $(quote endPos.line) $(quote endPos.column)))
            (@$(mkIdent userName)) (docstring? := $docStx))
  elabTerm (← `(#[$entries,*])) expectedType?
