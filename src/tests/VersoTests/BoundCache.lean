/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual.Basic

open Lean Verso Verso.Genre Verso.Genre.Manual

-- Rehydration must preserve document state and never invoke traversal handlers.
#eval show IO Unit from do
  let invoked ← IO.mkRef false
  let blockDescr : RegisteredBlockDescr := ⟨String, {
    decode := fromJson?
    traverse := fun _ _ _ => do invoked.set true; pure none
  }⟩
  let inlineDescr : RegisteredInlineDescr := ⟨String, {
    decode := fromJson?
    traverse := fun _ _ _ => do invoked.set true; pure none
  }⟩
  let impls := ExtensionImpls.fromLists [(`test, inlineDescr)] [(`test, blockDescr)]
  let inl (s : String) : Doc.Inline Manual := .other { name := `test, data := .str s } #[]
  let blk : Doc.Block Manual := .other { name := `test, data := .str "block" }
    #[.para #[.bold #[inl "nested"]]]
  let text : Doc.Part Manual := {
    title := #[inl "title"]
    titleString := "title"
    metadata := none
    content := #[blk, blk]
    subParts := #[{
      title := #[inl "subtitle"], titleString := "subtitle", metadata := none, content := #[blk], subParts := #[]
    }]
  }
  let logger ← Logger.new
  let original := TraverseState.initialize {}
  let populated ← (rebuildBoundCache text original).run impls |>.run logger
  let .ok restored := (fromJson? (toJson populated) : Except String TraverseState)
    | throw <| IO.userError "Failed to restore traversal state"
  unless restored.boundCache.blocks.isEmpty && restored.boundCache.inlines.isEmpty do
    throw <| IO.userError "The cache should not be serialized"
  let rebuilt ← (rebuildBoundCache text restored).run impls |>.run logger
  unless rebuilt.boundCache.blocks.size == 1 && rebuilt.boundCache.inlines.size == 3 do
    throw <| IO.userError "Missing or duplicate cache entries"
  unless toJson rebuilt == toJson original do
    throw <| IO.userError "Rebuilding the cache changed document state"
  if ← invoked.get then throw <| IO.userError "Rebuilding invoked a traversal handler"
  -- A failing replacement decoder proves subsequent lookups use the cached handlers.
  let failing : RegisteredBlockDescr := ⟨Unit, { decode := fun _ => .error "cache miss" }⟩
  unless (failing.boundFor rebuilt.boundCache `test (.str "block")).isOk do
    throw <| IO.userError "Block cache lookup missed"
  let failingInline : RegisteredInlineDescr := ⟨Unit, { decode := fun _ => .error "cache miss" }⟩
  for s in ["title", "nested", "subtitle"] do
    unless (failingInline.boundFor rebuilt.boundCache `test (.str s)).isOk do
      throw <| IO.userError "Inline cache lookup missed"
  unless (← logger.errors).isEmpty do throw <| IO.userError "Unexpected build errors"
  let malformed : Doc.Part Manual := { text with
    title := #[], subParts := #[], content := #[
      .other { name := `test, data := .null }
        #[.para #[.other { name := `test, data := .null } #[]]]
    ]
  }
  let badState ← (rebuildBoundCache malformed restored).run impls |>.run logger
  unless (← logger.errors).size == 2 do
    throw <| IO.userError "Expected both block and inline decoding failures to be reported"
  unless badState.boundCache.blocks.isEmpty && badState.boundCache.inlines.isEmpty do
    throw <| IO.userError "Failed decodes should not populate the cache"
