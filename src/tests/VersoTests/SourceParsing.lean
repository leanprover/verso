/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio Jesús Gallego Arias
-/
import Errata
import Lean.Parser.Module
import Verso.SyntaxUtils

/-!
The source parser borrows a region of an existing file map. These tests supply their own file maps
so that CRLF coordinates are tested before Lean's ordinary frontend can normalize them.
-/

namespace Verso.Tests.SourceParsing

open Lean Elab Command
open Verso.SyntaxUtils

private def checkCondition (condition : Bool) (message : String) : CommandElabM Unit :=
  unless condition do throwError message

private def inSource (source : String) (act : CommandElabM α) : CommandElabM α :=
  withReader ({ · with fileName := "SourceParsing.lean", fileMap := .ofString source }) act

private def sourceAtom (source : String) (start stop : String.Pos.Raw) : Syntax :=
  .atom (.original ⟨source, start, start⟩ start ⟨source, stop, stop⟩ stop)
    (start.extract source stop)

private def checkSourceRegion (newline : String) : CommandElabM Unit := do
  let preamble := "Document λ 🐈" ++ newline
  let content := "Nat.succ 1"
  -- A parser without the upper bound would accept this operator as part of the term.
  let source := preamble ++ content ++ " + 100" ++ newline ++ "outside the region"
  let start := preamble.rawEndPos
  let stop := (preamble ++ content).rawEndPos
  let atom := sourceAtom source start stop
  inSource source do
    let originalMap ← getFileMap
    let (ctx, pos) ← strLitInputContext atom "SourceParsing.lean"
    checkCondition (ctx.inputString == source && ctx.fileMap.source == source &&
      ctx.fileMap.positions == originalMap.positions) "The source file map was changed"
    checkCondition (pos == start && ctx.endPos == stop) "The region bounds were changed"
    match ← parseSourceCategory `term atom with
    | .error e => throwError "Source parsing failed: {e}"
    | .ok parsed =>
      checkCondition (parsed.reprint == some content) "Parsed text outside the region"
      checkCondition (parsed.getPos? == some start && parsed.getTailPos? == some stop)
        "The parsed term lost its absolute UTF-8 positions"

elab "#check_source_region " newline:str : command => checkSourceRegion newline.getString

#test_msgs in
#check_source_region "\n"

#test_msgs in
#check_source_region "\r\n"

private def checkSourceHeader (newline : String) : CommandElabM Unit := do
  let preamble := "Document λ" ++ newline ++ "```leanInit" ++ newline
  -- The parsed region has Lean's normal LF line endings. CRLF in the preamble must not move it.
  let content := "prelude\n"
  let source := preamble ++ content ++ "import OutsideTheRegion" ++ newline
  let start := preamble.rawEndPos
  let stop := (preamble ++ content).rawEndPos
  inSource source do
    let (ctx, pos) ← strLitInputContext (sourceAtom source start stop) "SourceParsing.lean"
    let (header, state, messages) ← Parser.parseHeader ctx pos
    checkCondition (!messages.hasErrors) "Header parsing reported errors"
    checkCondition (header.raw[1].getPos? == some start) "The prelude token moved"
    checkCondition (header.raw[2].getArgs.isEmpty && state.pos == stop)
      "Header parsing consumed an import outside the region"

elab "#check_source_header " newline:str : command => checkSourceHeader newline.getString

#test_msgs in
#check_source_header "\n"

#test_msgs in
#check_source_header "\r\n"

private def checkEmptyHeader (newline : String) : CommandElabM Unit := do
  let preamble := "Document λ" ++ newline
  let content := "  -- local comment\n#check Nat\n"
  let source := preamble ++ content ++ "import OutsideTheRegion"
  let start := preamble.rawEndPos
  let stop := (preamble ++ content).rawEndPos
  inSource source do
    let (ctx, pos) ← strLitInputContext (sourceAtom source start stop) "SourceParsing.lean"
    let (_, state, messages) ← Parser.parseHeader ctx pos
    checkCondition (!messages.hasErrors && state.leadingStartPos? == some start)
      "An empty header lost the start of its region"
    let (cmd, state, messages) := Parser.parseCommand ctx
      { env := ← getEnv, options := ← getOptions } state messages
    checkCondition (!messages.hasErrors && state.pos ≤ stop) "Command parsing left its region"
    let some (.original leading ..) := cmd.getHeadInfo?
      | throwError "The first command has no original source information"
    checkCondition (leading.startPos == start) "Leading whitespace absorbed the document preamble"

elab "#check_empty_source_header " newline:str : command => checkEmptyHeader newline.getString

#test_msgs in
#check_empty_source_header "\n"

#test_msgs in
#check_empty_source_header "\r\n"

private def expectSourceContractError (input : Syntax) (expected : String) : CommandElabM Unit := do
  let caught : Option String ← try
    discard <| parseSourceCategory `term input
    pure none
  catch e => pure (some (← e.toMessageData.toString))
  checkCondition (caught == some expected) "Source validation did not report the expected contract error"

elab "#check_source_contract_errors" : command => inSource "Nat" do
  expectSourceContractError (Syntax.mkStrLit "Nat")
    "Expected source positions for parsing a source region"
  expectSourceContractError (.atom (.synthetic ⟨2⟩ ⟨1⟩ false) "")
    "Invalid source region: start position is past its end"
  expectSourceContractError (.atom (.synthetic ⟨10⟩ ⟨20⟩ false) "")
    "Invalid source region: start position is past its end"

#test_msgs in
#check_source_contract_errors

elab "#check_positioned_synthetic_source" : command => inSource "Nat" do
  -- Source positions, rather than this generated payload, select what is parsed. Preserve the
  -- existing end-clamping behavior for positioned syntax produced during partial elaboration.
  let input := Syntax.atom (.synthetic 0 ⟨20⟩ false) "different generated text"
  match ← parseSourceCategory `term input with
  | .error e => throwError "Positioned synthetic input failed: {e}"
  | .ok parsed =>
    checkCondition (parsed.reprint == some "Nat" && parsed.getPos? == some 0 &&
      parsed.getTailPos? == some ⟨3⟩) "The positioned source contract was not respected"

#test_msgs in
#check_positioned_synthetic_source

elab "#check_source_error_coordinates" : command => do
  let preamble := "Document λ\n"
  let content := "Nat.succ 1 )"
  let source := preamble ++ content
  inSource source do
    let input := sourceAtom source preamble.rawEndPos source.rawEndPos
    match ← parseSourceCategory `term input with
    | .ok _ => throwError "The source parser accepted trailing input"
    | .error e =>
      checkCondition (e.startsWith "SourceParsing.lean:2:")
        "The source diagnostic lost its filename or absolute line"

#test_msgs in
#check_source_error_coordinates

elab "#check_source_line_endings" : command => do
  let source := "Nat\r\n"
  inSource source do
    match ← parseSourceCategory `term (sourceAtom source 0 source.rawEndPos) with
    | .ok _ => throwError "Source parsing silently normalized the input"
    | .error _ => pure () -- Lean rejects raw carriage returns; the source wrapper preserves them.

#test_msgs in
#check_source_line_endings

end Verso.Tests.SourceParsing
