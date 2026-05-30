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
Environment extension that records every declaration tagged with the `@[code_theme]` attribute.
Each entry maps the registration name (the decl, erased of macro scopes) to itself, so the table
is keyed and iterated by registration name.
-/
initialize codeThemeExt :
    PersistentEnvExtension Name Name (NameSet) ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := fun _ => pure {},
    addEntryFn := fun s n => s.insert n,
    exportEntriesFn := fun s =>
      s.toArray.qsort Name.quickLt
  }
