/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Environment

set_option doc.verso true
set_option linter.missingDocs true

public section

open Lean

namespace Verso.Theme

/--
Environment extension recording the set of declarations tagged with the {lit}`@[code_theme]`
attribute.
-/
initialize codeThemeExt :
    PersistentEnvExtension Name Name NameSet ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun s n => s.insert n,
    exportEntriesFn := fun s =>
      s.toArray.qsort Name.quickLt
  }
