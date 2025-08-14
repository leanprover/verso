/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Environment
import Std.Data.HashMap

import SubVerso.Module

open Lean
open Std

open SubVerso Highlighting Module Highlighted

namespace Verso.Code.External

initialize loadedModulesExt : (EnvExtension (HashMap String (NameMap (HashMap (List String) (Array ModuleItem))))) ← registerEnvExtension (pure {})

initialize loadedModuleAnchorExt : (EnvExtension (HashMap String (NameMap (HashMap (List String) AnchoredExamples)))) ← registerEnvExtension (pure {})
