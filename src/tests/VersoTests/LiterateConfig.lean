/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

Unit tests for the literate-document TOML configuration parser. This is a non-`module` file because
`VersoLiterate` is not part of the module system; the Errata runner imports it through its
non-module main.
-/
import VersoLiterate
import Errata

open Lean
open VersoLiterate
open Errata

/-- Parses a TOML string directly into a `LiterateConfig`. -/
private def loadFromString (toml : String) : IO LiterateConfig :=
  parseLiterateConfig toml

/-- A missing file results in the default config. -/
@[test]
def missingFile : Test := do
  let config ← loadLiterateConfig "/nonexistent/path/literate.toml"
  assertEq #[] config.exclude
  assertEq #[] config.order
  assertEq #[] config.targets
  assertNone config.landingPage

/-- An empty file results in the default config. -/
@[test]
def emptyFile : Test := do
  let config ← loadFromString ""
  assertEq #[] config.exclude
  assertEq #[] config.order
  assertEq #[] config.targets
  assertNone config.landingPage

/-- A whitespace-only file results in the default config. -/
@[test]
def whitespaceFile : Test := do
  let config ← loadFromString "   \n  \n  "
  assertEq #[] config.exclude

/-- The `exclude` list is parsed into an array of names. -/
@[test]
def exclude : Test := do
  let config ← loadFromString "exclude = [\"Foo.Bar\", \"Baz\"]\n"
  assertEq 2 config.exclude.size
  assertEq `Foo.Bar config.exclude[0]!
  assertEq `Baz config.exclude[1]!

/-- The `order` list is parsed into an array of names, preserving order. -/
@[test]
def order : Test := do
  let config ← loadFromString "order = [\"C\", \"A\", \"B\"]\n"
  assertEq 3 config.order.size
  assertEq `C config.order[0]!
  assertEq `A config.order[1]!
  assertEq `B config.order[2]!

/-- The `landing_page` field is parsed as a name. -/
@[test]
def landingPage : Test := do
  let config ← loadFromString "landing_page = \"MyLib.Overview\"\n"
  let lp ← assertSome config.landingPage
  assertEq `MyLib.Overview lp

/-- The `[order_children]` table is parsed into per-parent child orderings. -/
@[test]
def orderChildren : Test := do
  let config ← loadFromString "[order_children]\n\"Foo\" = [\"Foo.B\", \"Foo.A\"]\n\"Bar\" = [\"Bar.Z\"]\n"
  let fc ← assertSome (config.orderChildren.find? `Foo)
  assertEq 2 fc.size
  assertEq `Foo.B fc[0]!
  assertEq `Foo.A fc[1]!
  let bc ← assertSome (config.orderChildren.find? `Bar)
  assertEq 1 bc.size
  assertEq `Bar.Z bc[0]!

/-- The `[[targets]]` entries are parsed into targets with optional fields. -/
@[test]
def targets : Test := do
  let config ← loadFromString "[[targets]]\nmodule = \"Foo\"\n\n[[targets]]\nlibrary = \"Bar\"\n"
  assertEq 2 config.targets.size
  let t0 ← assertSome config.targets[0]!.module
  assertEq `Foo t0
  assertNone config.targets[0]!.library
  let t1 ← assertSome config.targets[1]!.library
  assertEq `Bar t1
  assertNone config.targets[1]!.module

/-- Multiple fields in one file are all parsed. -/
@[test]
def combined : Test := do
  let toml := "exclude = [\"Private\"]\norder = [\"Public\", \"Examples\"]\nlanding_page = \"Public\"\n"
  let config ← loadFromString toml
  assertEq 1 config.exclude.size
  assertEq `Private config.exclude[0]!
  assertEq 2 config.order.size
  assertEq `Public config.order[0]!
  assertEq `Examples config.order[1]!
  let lp ← assertSome config.landingPage
  assertEq `Public lp

/-- Invalid TOML produces an error. -/
@[test]
def invalidToml : Test := do
  let threw ← show IO Bool from do
    try
      let _ ← loadFromString "this is not valid toml {{{"
      return false
    catch _ =>
      return true
  assert threw "invalid TOML should throw"

/-- `hide_commands` is parsed into keyword pattern strings. -/
@[test]
def hideCommands : Test := do
  let config ← loadFromString "hide_commands = [\"set_option\", \"#check\"]\n"
  assertEq 2 config.hideCommands.size
  assertEq "set_option" config.hideCommands[0]!
  assertEq "#check" config.hideCommands[1]!

/-- The `[metadata]` table is parsed. -/
@[test]
def metadata : Test := do
  let config ← loadFromString "[metadata]\ntitle = \"My Site\"\ndescription = \"A test site\"\nfavicon = \"favicon.ico\"\n"
  let title ← assertSome config.metadata.title
  assertEq "My Site" title
  let desc ← assertSome config.metadata.description
  assertEq "A test site" desc
  let fav ← assertSome config.metadata.favicon
  assertEq "favicon.ico" fav

/-- `extra_css` and `extra_js` are parsed into string arrays. -/
@[test]
def extraCssJs : Test := do
  let config ← loadFromString "extra_css = [\"custom.css\", \"theme.css\"]\nextra_js = [\"analytics.js\"]\n"
  assertEq 2 config.extraCss.size
  assertEq "custom.css" config.extraCss[0]!
  assertEq "theme.css" config.extraCss[1]!
  assertEq 1 config.extraJs.size
  assertEq "analytics.js" config.extraJs[0]!

/-- `show_docstrings = false` is parsed. -/
@[test]
def showDocstrings : Test := do
  let config ← loadFromString "show_docstrings = false\n"
  assert (!config.showDocstrings) "show_docstrings"

/-- `show_docstrings_for` is parsed into names. -/
@[test]
def showDocstringsFor : Test := do
  let config ← loadFromString "show_docstrings = false\nshow_docstrings_for = [\"Foo.bar\", \"Baz.qux\"]\n"
  assert (!config.showDocstrings) "show_docstrings"
  assertEq 2 config.showDocstringsFor.size
  assertEq `Foo.bar config.showDocstringsFor[0]!
  assertEq `Baz.qux config.showDocstringsFor[1]!

/-- `hide_docstrings_for` is parsed into names. -/
@[test]
def hideDocstringsFor : Test := do
  let config ← loadFromString "hide_docstrings_for = [\"Foo.internal\"]\n"
  assert config.showDocstrings "show_docstrings default"
  assertEq 1 config.hideDocstringsFor.size
  assertEq `Foo.internal config.hideDocstringsFor[0]!

/-- `show_output` is parsed into keyword pattern strings. -/
@[test]
def showOutput : Test := do
  let config ← loadFromString "show_output = [\"#eval\"]\n"
  assertEq 1 config.showOutput.size
  assertEq "#eval" config.showOutput[0]!

/-- `show_output` defaults to the standard four-element list. -/
@[test]
def showOutputDefault : Test := do
  let config ← loadFromString ""
  assertEq 4 config.showOutput.size

/-- `show_imports = false` is parsed. -/
@[test]
def showImports : Test := do
  let config ← loadFromString "show_imports = false\n"
  assert (!config.showImports) "show_imports"

/-- `show_imports` defaults to true. -/
@[test]
def showImportsDefault : Test := do
  let config ← loadFromString ""
  assert config.showImports "show_imports default"

/-- Multiple new fields combine in one config. -/
@[test]
def combinedNew : Test := do
  let toml := String.intercalate "\n"
    ["exclude = [\"Private\"]", "hide_commands = [\"set_option\"]", "extra_css = [\"style.css\"]",
     "show_docstrings = false", "show_docstrings_for = [\"Public.api\"]", "[metadata]",
     "title = \"Test\"", ""]
  let config ← loadFromString toml
  assertEq 1 config.exclude.size
  assertEq 1 config.hideCommands.size
  assertEq 1 config.extraCss.size
  assert (!config.showDocstrings) "combined new: show_docstrings"
  assertEq 1 config.showDocstringsFor.size
  let title ← assertSome config.metadata.title
  assertEq "Test" title

/-- The `[theme]` light variables are parsed into the theme map. -/
@[test]
def themeLight : Test := do
  let config ← loadFromString "[theme]\ncode_box_background_color = \"#fff\"\ntext_color = \"#111\"\n"
  assertEq 2 config.theme.size
  let bg ← assertSome (config.theme.get? "code_box_background_color")
  assertEq "#fff" bg
  let tc ← assertSome (config.theme.get? "text_color")
  assertEq "#111" tc

/-- The `[theme.dark]` variables are parsed into the dark theme map. -/
@[test]
def themeDark : Test := do
  let config ← loadFromString "[theme]\ntext_color = \"#333\"\n\n[theme.dark]\ntext_color = \"#eee\"\nbackground_color = \"#111\"\n"
  assertEq 1 config.theme.size
  assertEq 2 config.themeDark.size
  let dt ← assertSome (config.themeDark.get? "text_color")
  assertEq "#eee" dt
  let db ← assertSome (config.themeDark.get? "background_color")
  assertEq "#111" db

/-- An empty theme produces empty maps. -/
@[test]
def themeEmpty : Test := do
  let config ← loadFromString ""
  assertEq 0 config.theme.size
  assertEq 0 config.themeDark.size

/-- A `[modules."Foo.Bar"]` table is parsed into a module config. -/
@[test]
def modulesConfig : Test := do
  let toml := "[modules.\"Foo.Bar\"]\ntitle = \"Custom Title\"\nurl = \"custom-url\"\nhide_commands = [\"set_option\"]\nshow_imports = false\n"
  let config ← loadFromString toml
  let mc ← assertSome (config.modules.find? `Foo.Bar)
  let t ← assertSome mc.title
  assertEq "Custom Title" t
  let u ← assertSome mc.url
  assertEq "custom-url" u
  let hc ← assertSome mc.hideCommands
  assertEq 1 hc.size
  let si ← assertSome mc.showImports
  assert (!si) "modules Foo.Bar showImports value"

/-- `resolveForModule` returns global defaults when no module config matches. -/
@[test]
def resolveNoMatch : Test := do
  let config ← loadFromString "hide_commands = [\"set_option\"]\n"
  let resolved := config.resolveForModule `Unmatched.Module
  assertEq 1 resolved.hideCommands.size
  assert resolved.showImports "resolve no match: showImports"
  assertNone resolved.title

/-- `resolveForModule` picks the most-specific prefix match. -/
@[test]
def resolvePrefixMatch : Test := do
  let toml := String.intercalate "\n"
    ["hide_commands = [\"set_option\"]", "[modules.\"Foo\"]", "show_imports = false",
     "[modules.\"Foo.Bar\"]", "title = \"Bar Title\"", "show_imports = true", ""]
  let config ← loadFromString toml
  let resolved := config.resolveForModule `Foo.Bar.Baz
  let t ← assertSome resolved.title
  assertEq "Bar Title" t
  assert resolved.showImports "resolve prefix: showImports"
  let resolved2 := config.resolveForModule `Foo.Qux
  assert (!resolved2.showImports) "resolve Foo prefix: showImports"
  assertNone resolved2.title
  let resolved3 := config.resolveForModule `Foo.Bar
  let t3 ← assertSome resolved3.title
  assertEq "Bar Title" t3

/-- A module-level config overrides global defaults. -/
@[test]
def resolveOverridesGlobal : Test := do
  let toml := String.intercalate "\n"
    ["show_imports = true", "show_docstrings = true", "[modules.\"MyMod\"]",
     "show_imports = false", "show_docstrings = false", ""]
  let config ← loadFromString toml
  let resolved := config.resolveForModule `MyMod
  assert (!resolved.showImports) "resolve override: showImports"
  assert (!resolved.showDocstrings) "resolve override: showDocstrings"
  let resolved2 := config.resolveForModule `Other
  assert resolved2.showImports "resolve global: showImports"
  assert resolved2.showDocstrings "resolve global: showDocstrings"
