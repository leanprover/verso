/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Environment

public section

open Lean

namespace Verso.Theme

/--
Environment extension that records every declaration tagged with the `@[manual_theme]`
attribute, keyed by the declaration name (with macro scopes erased). Kept distinct from the
code-theme registry so a consumer that enumerates code themes does not see a duplicate for every
manual theme.
-/
initialize manualThemeExt :
    PersistentEnvExtension Name Name NameSet ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun s n => s.insert n,
    exportEntriesFn := fun s =>
      s.toArray.qsort Name.quickLt
  }
