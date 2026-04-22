/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso
import VersoManual

namespace Verso.LinterTests

set_option guard_msgs.diff true
set_option pp.rawOnError true

/-!
# `linter.typography.quotes` (default: false)
-/

/-!
By default, it is off: straight quotes in text do not result in warnings.
-/
#guard_msgs in
#docs (.none) quotesDefault "Quotes default" :=
:::::::

Say "hello" to the world.

:::::::

/-!
When it is enabled, straight quotes produce warnings.
-/
/--
warning: Use curly quotes ('“')

Hint: Replace with Unicode
  "̵“̲

Note: This linter can be disabled with `set_option linter.typography.quotes false`
---
warning: Use curly quotes ('”')

Hint: Replace with Unicode
  "̵”̲

Note: This linter can be disabled with `set_option linter.typography.quotes false`
-/
#guard_msgs in
set_option linter.typography.quotes true in
#docs (.none) quotesOn "Quotes on" :=
:::::::

Say "hello" to the world.

:::::::

/-!
# `linter.typography.dashes` (default: false)
-/

/-!
By default, it is off: a triple dash in text does not produce a warning.
-/
#guard_msgs in
#docs (.none) dashesDefault "Dashes default" :=
:::::::

An em dash --- really!

:::::::

/-!
When it is enabled, a triple dash produces a warning.
-/
/--
warning: Use an em dash ('—')

Hint: Replace with Unicode
   ̵-̵-̵-̵ ̵—̲

Note: This linter can be disabled with `set_option linter.typography.dashes false`
-/
#guard_msgs in
set_option linter.typography.dashes true in
#docs (.none) dashesOn "Dashes on" :=
:::::::

An em dash --- really!

:::::::

/-!
Regression test: checks that the two typography options are independent. When only `dashes` is
enabled, ASCII quotes in the same document must not produce quote warnings (and vice versa).
Previously both options shared a disjunctive gate and then logged unconditionally, so enabling one
leaked warnings for the other.
-/
/--
warning: Use an em dash ('—')

Hint: Replace with Unicode
   ̵-̵-̵-̵ ̵—̲

Note: This linter can be disabled with `set_option linter.typography.dashes false`
-/
#guard_msgs in
set_option linter.typography.dashes true in
#docs (.none) typoDashesOnlyMixed "Dashes only mixed" :=
:::::::

Say "hello" --- really!

:::::::

/--
warning: Use curly quotes ('“')

Hint: Replace with Unicode
  "̵“̲

Note: This linter can be disabled with `set_option linter.typography.quotes false`
---
warning: Use curly quotes ('”')

Hint: Replace with Unicode
  "̵”̲

Note: This linter can be disabled with `set_option linter.typography.quotes false`
-/
#guard_msgs in
set_option linter.typography.quotes true in
#docs (.none) typoQuotesOnlyMixed "Quotes only mixed" :=
:::::::

Say "hello" --- really!

:::::::

/-!
# `linter.verso.markup.emph` (default: true)
-/

/-!
By default, it is on: redundant `__` around emphasized text produces a warning.
-/
/--
warning: Unnecessary '_'

Hint: Use the minimal number of '_'s
  __̵emphatic__̵

Note: This linter can be disabled with `set_option linter.verso.markup.emph false`
-/
#guard_msgs in
#docs (.none) emphDefault "Emph default" :=
:::::::

This is __emphatic__ text.

:::::::

/-!
When it is disabled, redundant `__` does not produce a warning.
-/
#guard_msgs in
set_option linter.verso.markup.emph false in
#docs (.none) emphOff "Emph off" :=
:::::::

This is __emphatic__ text.

:::::::

/-!
# `linter.verso.markup.code` (default: true)
-/

/-!
By default, it is on: redundant backticks around inline code produce a warning.
-/
/--
warning: Unnecessary '`'

Hint: Use the minimal number of '`'s
  `̵`̵f̵o̵o̵`̵`̵`̲f̲o̲o̲`̲

Note: This linter can be disabled with `set_option linter.verso.markup.code false`
-/
#guard_msgs in
#docs (.none) codeDefault "Code default" :=
:::::::

See ``foo`` for details.

:::::::

/-!
When it is disabled, redundant inline-code backticks do not produce a warning.
-/
#guard_msgs in
set_option linter.verso.markup.code false in
#docs (.none) codeOff "Code off" :=
:::::::

See ``foo`` for details.

:::::::

/-!
# `linter.verso.markup.codeBlock` (default: true)
-/

/-!
By default, it is on: redundant backticks around a code block produce a warning.
-/
/--
warning: Unnecessary '`'

Hint: Use the minimal number of '`'s
  ````̵
  foo
  ````̵

Note: This linter can be disabled with `set_option linter.verso.markup.codeBlock false`
-/
#guard_msgs in
#docs (.none) codeBlockDefault "Code block default" :=
:::::::

````
foo
````

:::::::

/-!
When it is disabled, redundant code-block backticks do not produce a warning.
-/
#guard_msgs in
set_option linter.verso.markup.codeBlock false in
#docs (.none) codeBlockOff "Code block off" :=
:::::::

````
foo
````

:::::::

/-!
# `linter.verso.manual.headerTags` (default: false, `Manual` genre only)
-/

/-!
By default, it is off: untagged headers do not produce a warning.
-/
#guard_msgs in
#docs (Verso.Genre.Manual) headerTagsDefault "Header tags default" :=
:::::::

# Untagged section

Some text.

:::::::

/-!
When it is enabled, an untagged header produces a warning.
-/
/--
warning: Missing permalink tag

Hint: Add a metadata block with a tag or explicitly indicate that no tag is desired:
  • # Untagged section
    ̲%̲%̲%̲
    ̲t̲a̲g̲ ̲:̲=̲ ̲"̲u̲n̲t̲a̲g̲g̲e̲d̲-̲s̲e̲c̲t̲i̲o̲n̲"̲
    ̲%̲%̲%̲
  • # Untagged section
    ̲%̲%̲%̲
    ̲t̲a̲g̲ ̲:̲=̲ ̲n̲o̲n̲e̲
    ̲%̲%̲%̲

Note: The tag is used as a permanent name for the section or chapter. Writers of this or other documents may use it to link to the section, and it is used to share permanent links. In HTML content, they are used as IDs for headers. Section tags should remain unchanged over time.

Note: This linter can be disabled with `set_option linter.verso.manual.headerTags false`
-/
#guard_msgs in
set_option linter.verso.manual.headerTags true in
#docs (Verso.Genre.Manual) headerTagsOn "Header tags on" :=
:::::::

# Untagged section

Some text.

:::::::
