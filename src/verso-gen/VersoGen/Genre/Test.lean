/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Verso
public meta import Verso

set_option doc.verso true

/-!
A small genre for generated test documents. Its extensions accept any valid arguments and contents,
so generated documents elaborate without errors whatever their structure.
-/

namespace VersoGen.Genre

open Lean Verso Doc Elab ArgParse

/-- The metadata that a part of a test document may set. -/
public structure TestGenre.PartMetadata where
  tag : Option String := none
  draft : Bool := false
  shortTitle : Option String := none
deriving Repr

/-- A genre with no extensions of its own, used by the minimal genre profile. -/
@[expose] public def TestGenre : Genre where
  PartMetadata := TestGenre.PartMetadata
  Block := Empty
  Inline := Empty
  TraverseContext := Unit
  TraverseState := Unit

/-- The arguments of the {lit}`aside` directive. -/
public structure AsideArgs where
  title : String

section

variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m]

public meta instance : FromArgs AsideArgs m := ⟨AsideArgs.mk <$> .positional `title .string⟩

end

/-- Groups its blocks. -/
@[directive]
public meta def note : DirectiveExpanderOf Unit
  | (), blocks => do
    let blocks ← blocks.mapM elabBlock
    ``(Verso.Doc.Block.concat #[$blocks,*])

/-- Groups its blocks under a title. -/
@[directive]
public meta def aside : DirectiveExpanderOf AsideArgs
  | {title}, blocks => do
    let blocks ← blocks.mapM elabBlock
    ``(Verso.Doc.Block.concat
        #[Verso.Doc.Block.para #[Verso.Doc.Inline.text $(quote title)], $blocks,*])

/-- Emphasizes its contents. -/
@[role]
public meta def highlight : RoleExpanderOf Unit
  | (), contents => do
    let contents ← contents.mapM elabInline
    ``(Verso.Doc.Inline.emph #[$contents,*])

/-- Inserts its contents unchanged. -/
@[role]
public meta def term : RoleExpanderOf Unit
  | (), contents => do
    let contents ← contents.mapM elabInline
    ``(Verso.Doc.Inline.concat #[$contents,*])

/-- Shows its contents as a code block. -/
@[code_block]
public meta def plain : CodeBlockExpanderOf Unit
  | (), str => ``(Verso.Doc.Block.code $(quote str.getVersoCodeBlock))

/-- A thematic break, which elaborates to an empty block. -/
@[block_command]
public meta def separator : BlockCommandOf Unit
  | () => ``(Verso.Doc.Block.concat #[])
