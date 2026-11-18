/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rob Simmons
-/
module
public meta import Lean.Server.Rpc.RequestHandling
public meta import Lean.Server.Requests
public meta import VersoManual.LiveDocument.Extension

open Lean Server

namespace Verso

@[server_rpc_method]
public meta def getLiveDocument (_ : Unit) : RequestM (RequestTask VersoDocumentData) := do
  let doc ← RequestM.readDoc
  let endPos := doc.meta.text.source.rawEndPos
  RequestM.withWaitFindSnap doc (·.endPos >= endPos) (notFoundX := pure (.errors #["Internal invariant violated: notFoundX"]))
    fun snap =>
      match versoDocumentExt.getState snap.env with
      | .none => return .noDoc
      | .some s =>
        return s
