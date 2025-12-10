/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import SubVerso.Highlighting
meta import Verso.Instances.Deriving
import VersoManual.Docstring.Basic
import VersoManual.Docstring.PrettyPrint
import Lean.Data.Lsp.Internal
import Lean.Meta
import Lean.Widget.TaggedText
import Lean.Widget.InteractiveCode

open Lean
open SubVerso.Highlighting

namespace Verso.Genre.Manual.Block.Docstring


public structure DocName where
  name : Name
  hlName : Highlighted
  signature : Highlighted
  docstring? : Option String
deriving ToJson, FromJson, Repr, Quote


open Meta in
public def DocName.ofName (c : Name) (ppWidth : Nat := 40) (showUniverses := true) (showNamespace := true) (constantInfo := false) (openDecls : List OpenDecl := []) (checkDocstring : Bool := true) : MetaM DocName := do
  let env ← getEnv
  if let some _ := env.find? c then
    let ctx := {
      env           := (← getEnv)
      mctx          := (← getMCtx)
      options       := (← getOptions)
      currNamespace := (← getCurrNamespace)
      openDecls     := (← getOpenDecls)
      fileMap       := default
      ngen          := (← getNGen)
    }

    let ⟨fmt, infos⟩ ← withOptions (·.setBool `pp.tagAppFns true) <|
      ppSignature c (showNamespace := showNamespace) (openDecls := openDecls) (constantInfo := constantInfo)

    let ttSig := Lean.Widget.TaggedText.prettyTagged (w := ppWidth) fmt

    let sig ← Lean.Widget.tagCodeInfos ctx infos ttSig

    let ⟨fmt, infos⟩ ← withOptions (·.setBool `pp.tagAppFns true) <|
      ppName c (showUniverses := showUniverses) (showNamespace := showNamespace) (openDecls := openDecls)
    let ttName := Lean.Widget.TaggedText.prettyTagged (w := ppWidth) fmt
    let name ← Lean.Widget.tagCodeInfos ctx infos ttName

    let docstring? ← if checkDocstring then getDocString? env c else Lean.findDocString? env c

    let hlCtx : SubVerso.Highlighting.Context := ⟨{}, false, false, []⟩

    pure { name := c, hlName := (← renderTagged none name hlCtx), signature := (← renderTagged none sig hlCtx), docstring? }
  else
    pure { name := c, hlName := .token ⟨.const c "" none false, c.toString⟩, signature := Highlighted.seq #[], docstring? := none }
