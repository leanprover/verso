/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Emilio Jesus Gallego Arias
-/
import VersoTests.DocElabExtensions.Middle

namespace Verso.Tests.DocElabExtensions

/-!
This module consumes the entries through `Middle`.
The command guard checks the test-only local-persistent extension directly: the final lookup state
contains the entry from `Define`, but `Middle` exported no entries for the extension. The `#docs`
block separately checks the real doc expander registries for role, code block, directive, and block
command expanders through the same transitive import.
-/

open Verso Genre Manual
open Lean Elab Command

elab "#guard_middle_exports_no_local_persistent_entries" : command => do
  let env ← getEnv
  let some middleIdx := env.getModuleIdxFor? ``importedThroughMiddle
    | throwError "could not find the module for importedThroughMiddle"
  let entries := testLocalExtensionEntries env `inheritedTestLocalExtension
  unless entries.contains `inheritedTestEntry do
    throwError "expected lookup state to include the entry imported through the middle module"
  let middleEntries := testLocalExtensionModuleEntries env middleIdx
  unless middleEntries.isEmpty do
    throwError "middle module should export no inherited local-persistent entries, but exported {middleEntries.size}"

#guard_middle_exports_no_local_persistent_entries

#docs (Manual) inheritedDocElabExtensions "Inherited Doc Elab Extensions" :=
:::::::
This custom {inheritedRole}[] is provided through a transitive import.

```inheritedCode
code block body
```

:::inheritedDirective
Directive body
:::

{inheritedCommand}
:::::::

#guard importedThroughMiddle
#guard inheritedDocElabExtensions.toPart.content.size == 4
