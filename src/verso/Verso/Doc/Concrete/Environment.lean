/-
Copyright (c) 2023-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Environment
public meta import Lean.Elab.Term
public meta import Verso.Doc.Elab.Monad

namespace Verso.Doc.Concrete

open Lean Verso Doc Elab

/--
The elaboration state of a `#doc` document that persists from one top-level block to the next.
Each top-level block is a separate Lean command, so the environment extension `docEnvironmentExt`
stores this state.
-/
public meta structure DocElabEnvironment where
  genreSyntax : Term := ⟨.missing⟩
  ctx : DocElabContext := ⟨.missing, mkConst ``Unit, .always, .none⟩
  docState : DocElabM.State := { highlightDeduplicationTable := some {} }
  partState : PartElabM.State := .init (.node .none nullKind #[]) (.node .none nullKind #[])
deriving Inhabited

public meta initialize docEnvironmentExt : EnvExtension DocElabEnvironment ← registerEnvExtension (pure {})
