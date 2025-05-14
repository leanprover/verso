/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Environment

import SubVerso.Module

open Lean

open SubVerso Highlighting Module Highlighted

namespace Verso.Genre.Manual.ExternalLean

initialize loadedModulesExt : (EnvExtension (NameMap (Array ModuleItem))) ← registerEnvExtension (pure {})

initialize loadedModuleAnchorExt : (EnvExtension (NameMap AnchoredExamples)) ← registerEnvExtension (pure {})
