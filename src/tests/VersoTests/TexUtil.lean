/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jason Reed
-/
import Lean.Elab.Command
import VersoManual

/-!
Support for writing unit tests covering TeX output.
-/

open Verso Genre.Manual

/--
Render a Verso block in Manual Genre to TeX in isolation

This requires the `IO` monad because `TraverseM` does.
-/
def toTex (block : Doc.Block Genre.Manual) : IO Output.TeX := do
  let extension_impls := extension_impls%
  let logger ← Verso.Logger.new

  -- Traversal monadic data
  let traverseContext : TraverseContext := {}
  let traverseState : TraverseState := .initialize {}

  -- Traverse the block. This shadows both `block` and `traverseState`.
  -- This is where we engage with the IO at the bottom of TraverseM.
  let ⟨block, traverseState⟩ ←
    Doc.Genre.traverseBlock Genre.Manual block
      |>.run extension_impls traverseContext traverseState logger

  -- Options for TeX
  let options : Doc.TeX.Options Genre.Manual := {
    headerLevel := none
  }

  -- Convert the block to TeX
  block.toTeX
    |>.run ⟨options, traverseContext, traverseState, {}⟩
    |>.run' {} |>.run extension_impls |>.run logger
