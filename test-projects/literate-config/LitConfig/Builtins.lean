import LitConfig.Core
import Lean.Elab.DocString

set_option doc.verso true
set_option doc.verso.module true

namespace Builtins

/-!
# Built-in Docstring Extensions

This module exercises every built-in extension from Lean's docstring elaborator. The literate HTML
pipeline must accept all of them and render their contents.
-/

/-- A target for {name}`builtinName` and {lean}`builtinName` references. -/
def builtinName : Nat := 42

-- Untested roles: `assert'`, because it cannot be used after the equality type's notation is defined.
set_option doc.verso.suggestions false in
/--
{name}`builtinName` is a constant reference.

{lean}`1 + 2 * 3` is an inline Lean term.

{module}`LitConfig.Core` is a module reference, {module -checked}`LitConfig.Bogus` is an invalid module reference.

{tactic}`rfl` is a tactic; {conv}`lhs` is a conv tactic.

{attr}`@[simp]` is an attribute.

{syntaxCat}`term` is a syntax category, and {syntax term}`1 + [] - (· / ·)` is syntax in it.

{kw (of := Lean.«command__Unif_hint____Where_|_-⊢__»)}`unif_hint` is a keyword atom.
{kw? (of := Lean.«command__Unif_hint____Where_|_-⊢__»)}`where` is also a keyword atom, and
{kw! (of := Lean.Parser.Command.definition)}`def` is an unchecked keyword atom.

{option}`maxHeartbeats` is an option name; {option}`set_option maxHeartbeats 1000` is a `set_option`.

{lit}`anything goes here` is a literal code element.

{manual section "some-section"}`a manual link` references a section.

The {assert}`Nat.zero = Nat.zero` defeq assertion.

Given {given}`n : Nat`, the function operates on {name}`n`. Given {givenInstance}`Add Nat`, addition is available.
-/
def inlineRoleDemos (n : Nat) : Nat := n + 1

/--
Code blocks:

```lean
example : True := trivial
```

```leanTerm
1 + 2
```

```lean (name := nb)
#eval 1 + 1
```

```output nb
2
```
-/
def codeBlockDemos : Nat := 0

/-!
Block commands on lines by themselves:

{open Nat}

{set_option pp.all false}

After opening, {lit}`Nat.succ` resolves through the opened namespace.
-/

end Builtins

/-
Built-in coverage snapshots.

The fixture above exercises every role, code block, and command currently registered as a docstring
builtin. The `#guard_msgs` snapshots below enumerate the registries the elaborator reads from, so
that toolchain bumps surface as a snapshot mismatch whenever Lean adds, removes, or renames a
built-in. When a snapshot diverges, update both the expected list here and the fixture above (and,
if the new element needs more than the fallback rendering, add a corresponding handler in
`VersoLiterate.Builtin`).

This is deliberate coupling: a Lean release that adds e.g. `Lean.Doc.example` will fail this fixture
even though Verso itself is unchanged. The mismatch is the signal to add a handler for the new
builtin.
-/

section BuiltinCoverage

/--
Prints the keys of a {name (full := Lean.NameMap)}`NameMap`, sorted alphabetically, one per line; if {name}`m` is empty, {lit}`(none)` is printed.
-/
private def printKeys {α} (m : Lean.NameMap α) : IO Unit := do
  let names := m.toArray.map (·.1) |>.qsort (·.toString < ·.toString)
  if names.isEmpty then IO.println "(none)"
  else for n in names do IO.println n

/-- info:
Lean.Doc.assert
Lean.Doc.assert'
Lean.Doc.attr
Lean.Doc.conv
Lean.Doc.given
Lean.Doc.givenInstance
Lean.Doc.kw
Lean.Doc.kw!
Lean.Doc.kw?
Lean.Doc.lean
Lean.Doc.lit
Lean.Doc.manual
Lean.Doc.module
Lean.Doc.name
Lean.Doc.option
Lean.Doc.syntax
Lean.Doc.syntaxCat
Lean.Doc.tactic
-/
#guard_msgs in
#eval do printKeys (← Lean.Doc.builtinDocRoles.get)

/-- info:
Lean.Doc.lean
Lean.Doc.leanTerm
Lean.Doc.output
-/
#guard_msgs in
#eval do printKeys (← Lean.Doc.builtinDocCodeBlocks.get)

/-- info:
Lean.Doc.open
Lean.Doc.set_option
-/
#guard_msgs in
#eval do printKeys (← Lean.Doc.builtinDocCommands.get)

/-- info:
(none)
-/
#guard_msgs in
#eval do printKeys (← Lean.Doc.builtinDocDirectives.get)

end BuiltinCoverage
