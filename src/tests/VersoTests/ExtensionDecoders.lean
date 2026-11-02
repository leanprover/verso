/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import VersoManual.Basic

open Lean Verso.Genre.Manual

namespace VersoTests.ExtensionDecoders

-- Deliberately omit FromJson: these extensions must use their custom decoders.
structure Metadata where
  value : String

block_extension customBlock (value : String) where
  metadata := Metadata
  data := .str value
  decode data := Metadata.mk <$> data.getStr?

inline_extension customInline (value : String) where
  metadata := Metadata
  data := .str value
  decode (data : Json) := Metadata.mk <$> data.getStr?

#guard (customBlock.descr.bind (customBlock "block").data).isOk
#guard (customInline.descr.bind (customInline "inline").data).isOk
#guard !(customBlock.descr.bind .null).isOk
#guard !(customInline.descr.bind .null).isOk

end VersoTests.ExtensionDecoders
