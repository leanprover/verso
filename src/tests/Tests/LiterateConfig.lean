/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoLiterate

open Lean
open VersoLiterate

namespace Tests.LiterateConfig

/-- Parses a TOML string directly into a `LiterateConfig`. -/
private def loadFromString (toml : String) : IO LiterateConfig :=
  parseLiterateConfig toml

/-- Asserts that `actual` equals `expected`, throwing with a descriptive message on failure. -/
private def assertEq [BEq α] [Repr α] (desc : String) (actual expected : α) : IO Unit :=
  unless actual == expected do
    throw <| IO.userError s!"{desc}: expected {repr expected}, got {repr actual}"

private def assertTrue (desc : String) (b : Bool) : IO Unit :=
  unless b do
    throw <| IO.userError s!"{desc}: expected true, got false"

private def assertFalse (desc : String) (b : Bool) : IO Unit := do
  if b then
    throw <| IO.userError s!"{desc}: expected false, got true"

private def assertSome [Repr α] (desc : String) (o : Option α) : IO α :=
  match o with
  | some v => pure v
  | none => throw <| IO.userError s!"{desc}: expected Some, got None"

private def assertNone [Repr α] (desc : String) (o : Option α) : IO Unit := do
  if o.isSome then
    throw <| IO.userError s!"{desc}: expected None, got {repr o}"

-- ===== Individual test cases =====

/-- A missing file results in the default config. -/
private def testMissingFile : IO Unit := do
  let config ← loadLiterateConfig "/nonexistent/path/literate.toml"
  assertEq "missing file: exclude" config.exclude #[]
  assertEq "missing file: order" config.order #[]
  assertEq "missing file: targets" config.targets #[]
  assertNone "missing file: landingPage" config.landingPage

/-- An empty file results in the default config. -/
private def testEmptyFile : IO Unit := do
  let config ← loadFromString ""
  assertEq "empty file: exclude" config.exclude #[]
  assertEq "empty file: order" config.order #[]
  assertEq "empty file: targets" config.targets #[]
  assertNone "empty file: landingPage" config.landingPage

/-- A whitespace-only file results in the default config. -/
private def testWhitespaceFile : IO Unit := do
  let config ← loadFromString "   \n  \n  "
  assertEq "whitespace file: exclude" config.exclude #[]

/-- The `exclude` list is parsed into an array of `Name` values. -/
private def testExclude : IO Unit := do
  let config ← loadFromString "exclude = [\"Foo.Bar\", \"Baz\"]\n"
  assertEq "exclude length" config.exclude.size 2
  assertEq "exclude[0]" config.exclude[0]! `Foo.Bar
  assertEq "exclude[1]" config.exclude[1]! `Baz

/-- The `order` list is parsed into an array of `Name` values preserving order. -/
private def testOrder : IO Unit := do
  let config ← loadFromString "order = [\"C\", \"A\", \"B\"]\n"
  assertEq "order length" config.order.size 3
  assertEq "order[0]" config.order[0]! `C
  assertEq "order[1]" config.order[1]! `A
  assertEq "order[2]" config.order[2]! `B

/-- The `landing_page` field is parsed as `some` of a `Name`. -/
private def testLandingPage : IO Unit := do
  let config ← loadFromString "landing_page = \"MyLib.Overview\"\n"
  let lp ← assertSome "landing_page" config.landingPage
  assertEq "landing_page value" lp `MyLib.Overview

/-- `[order_children]` entries are parsed into per-parent child orderings. -/
private def testOrderChildren : IO Unit := do
  let config ← loadFromString "[order_children]\n\"Foo\" = [\"Foo.B\", \"Foo.A\"]\n\"Bar\" = [\"Bar.Z\"]\n"
  let fooChildren := config.orderChildren.find? `Foo
  let fc ← assertSome "order_children: Foo" fooChildren
  assertEq "order_children: Foo length" fc.size 2
  assertEq "order_children: Foo[0]" fc[0]! `Foo.B
  assertEq "order_children: Foo[1]" fc[1]! `Foo.A
  let barChildren := config.orderChildren.find? `Bar
  let bc ← assertSome "order_children: Bar" barChildren
  assertEq "order_children: Bar length" bc.size 1
  assertEq "order_children: Bar[0]" bc[0]! `Bar.Z

/-- `[[targets]]` table entries are parsed into `Target` values with optional fields. -/
private def testTargets : IO Unit := do
  let config ← loadFromString "[[targets]]\nmodule = \"Foo\"\n\n[[targets]]\nlibrary = \"Bar\"\n"
  assertEq "targets length" config.targets.size 2
  let t0 ← assertSome "targets[0].module" config.targets[0]!.module
  assertEq "targets[0].module value" t0 `Foo
  assertNone "targets[0].library" config.targets[0]!.library
  let t1 ← assertSome "targets[1].library" config.targets[1]!.library
  assertEq "targets[1].library value" t1 `Bar
  assertNone "targets[1].module" config.targets[1]!.module

/-- Multiple fields in the same file are all parsed correctly. -/
private def testCombined : IO Unit := do
  let toml := "exclude = [\"Private\"]\norder = [\"Public\", \"Examples\"]\nlanding_page = \"Public\"\n"
  let config ← loadFromString toml
  assertEq "combined: exclude length" config.exclude.size 1
  assertEq "combined: exclude[0]" config.exclude[0]! `Private
  assertEq "combined: order length" config.order.size 2
  assertEq "combined: order[0]" config.order[0]! `Public
  assertEq "combined: order[1]" config.order[1]! `Examples
  let lp ← assertSome "combined: landing_page" config.landingPage
  assertEq "combined: landing_page value" lp `Public

/-- Invalid TOML produces an error. -/
private def testInvalidToml : IO Unit := do
  let mut caught := false
  try
    let _ ← loadFromString "this is not valid toml {{{"
  catch _ =>
    caught := true
  assertTrue "invalid TOML should throw" caught

/-- `hide_commands` is parsed into an array of `Name` values. -/
private def testHideCommands : IO Unit := do
  let config ← loadFromString "hide_commands = [\"Lean.Parser.Command.set_option\", \"Lean.Parser.Command.check\"]\n"
  assertEq "hide_commands length" config.hideCommands.size 2
  assertEq "hide_commands[0]" config.hideCommands[0]! `Lean.Parser.Command.set_option
  assertEq "hide_commands[1]" config.hideCommands[1]! `Lean.Parser.Command.check

/-- `[metadata]` table is parsed into a `Metadata` value. -/
private def testMetadata : IO Unit := do
  let config ← loadFromString "[metadata]\ntitle = \"My Site\"\ndescription = \"A test site\"\nfavicon = \"favicon.ico\"\n"
  let title ← assertSome "metadata.title" config.metadata.title
  assertEq "metadata.title value" title "My Site"
  let desc ← assertSome "metadata.description" config.metadata.description
  assertEq "metadata.description value" desc "A test site"
  let fav ← assertSome "metadata.favicon" config.metadata.favicon
  assertEq "metadata.favicon value" fav "favicon.ico"

/-- `extra_css` and `extra_js` are parsed into string arrays. -/
private def testExtraCssJs : IO Unit := do
  let config ← loadFromString "extra_css = [\"custom.css\", \"theme.css\"]\nextra_js = [\"analytics.js\"]\n"
  assertEq "extra_css length" config.extraCss.size 2
  assertEq "extra_css[0]" config.extraCss[0]! "custom.css"
  assertEq "extra_css[1]" config.extraCss[1]! "theme.css"
  assertEq "extra_js length" config.extraJs.size 1
  assertEq "extra_js[0]" config.extraJs[0]! "analytics.js"

/-- `show_docstrings = false` is parsed correctly. -/
private def testShowDocstrings : IO Unit := do
  let config ← loadFromString "show_docstrings = false\n"
  assertFalse "show_docstrings" config.showDocstrings

/-- `show_docstrings_for` is parsed into an array of `Name` values. -/
private def testShowDocstringsFor : IO Unit := do
  let config ← loadFromString "show_docstrings = false\nshow_docstrings_for = [\"Foo.bar\", \"Baz.qux\"]\n"
  assertFalse "show_docstrings" config.showDocstrings
  assertEq "show_docstrings_for length" config.showDocstringsFor.size 2
  assertEq "show_docstrings_for[0]" config.showDocstringsFor[0]! `Foo.bar
  assertEq "show_docstrings_for[1]" config.showDocstringsFor[1]! `Baz.qux

/-- `hide_docstrings_for` is parsed into an array of `Name` values. -/
private def testHideDocstringsFor : IO Unit := do
  let config ← loadFromString "hide_docstrings_for = [\"Foo.internal\"]\n"
  assertTrue "show_docstrings default" config.showDocstrings
  assertEq "hide_docstrings_for length" config.hideDocstringsFor.size 1
  assertEq "hide_docstrings_for[0]" config.hideDocstringsFor[0]! `Foo.internal

/-- Multiple new fields combined in one config. -/
private def testCombinedNew : IO Unit := do
  let toml := String.intercalate "\n" [
    "exclude = [\"Private\"]",
    "hide_commands = [\"Lean.Parser.Command.set_option\"]",
    "extra_css = [\"style.css\"]",
    "show_docstrings = false",
    "show_docstrings_for = [\"Public.api\"]",
    "[metadata]",
    "title = \"Test\"",
    ""
  ]
  let config ← loadFromString toml
  assertEq "combined new: exclude" config.exclude.size 1
  assertEq "combined new: hide_commands" config.hideCommands.size 1
  assertEq "combined new: extra_css" config.extraCss.size 1
  assertFalse "combined new: show_docstrings" config.showDocstrings
  assertEq "combined new: show_docstrings_for" config.showDocstringsFor.size 1
  let title ← assertSome "combined new: metadata.title" config.metadata.title
  assertEq "combined new: metadata.title value" title "Test"

-- ===== Test runner =====

private def configTests : List (String × IO Unit) := [
  ("missing file", testMissingFile),
  ("empty file", testEmptyFile),
  ("whitespace file", testWhitespaceFile),
  ("exclude", testExclude),
  ("order", testOrder),
  ("landing_page", testLandingPage),
  ("order_children", testOrderChildren),
  ("targets", testTargets),
  ("combined", testCombined),
  ("invalid TOML", testInvalidToml),
  ("hide_commands", testHideCommands),
  ("metadata", testMetadata),
  ("extra_css/js", testExtraCssJs),
  ("show_docstrings", testShowDocstrings),
  ("show_docstrings_for", testShowDocstringsFor),
  ("hide_docstrings_for", testHideDocstringsFor),
  ("combined new", testCombinedNew)
]

def runLiterateConfigTests : IO Nat := do
  IO.println "Running literate config unit tests..."
  let mut failures := 0
  for (name, test) in configTests do
    try
      test
      IO.println s!"  {name}: passed"
    catch e =>
      IO.eprintln s!"  {name}: FAILED - {e}"
      failures := failures + 1
  if failures == 0 then
    IO.println "  All literate config tests passed."
  else
    IO.eprintln s!"  {failures} literate config test(s) failed."
  return failures

end Tests.LiterateConfig
