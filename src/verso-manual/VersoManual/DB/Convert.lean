/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import DocGen4.RenderedCode
import SubVerso.Highlighting.Highlighted

/-! # RenderedCode → Highlighted Conversion

Doc-gen4 stores types as `RenderedCode` (`TaggedText RenderedCode.Tag`) binary blobs. Verso renders
all code using SubVerso's `Highlighted` type. This module converts between them.

The conversion is lossy: `RenderedCode` does not carry hover info, variable types, or go-to-definition
targets. The visual rendering is the same — tokens that were keywords, string literals, or constant
references are tagged appropriately for syntax highlighting and linking.
-/

namespace Verso.Genre.Manual.DB

open DocGen4 (RenderedCode SortFormer)
open SubVerso.Highlighting (Highlighted Token)

/-- Extract plain text content from a `RenderedCode` tree, discarding all tags. -/
partial def renderedCodeText : RenderedCode → String
  | .text s => s
  | .tag _ inner => renderedCodeText inner
  | .append xs => String.join (xs.toList.map renderedCodeText)

/--
Convert a `RenderedCode` value (from doc-gen4's database) to a `Highlighted` value (for Verso's
rendering pipeline). Tags are mapped as follows:

- `.keyword` → `Token.Kind.keyword` (no name or docs)
- `.string` → `Token.Kind.str`
- `.const name` → `Token.Kind.const` (with signature and docstring from `constInfo` if available)
- `.sort` → `Token.Kind.sort` (no docs)
- `.otherExpr` → plain `Highlighted.text` (no semantic info)

The `constInfo` parameter provides hover data for known constants: a map from `Name` to
`(signature, docstring?)`.
-/
partial def renderedCodeToHighlighted (constInfo : Lean.NameMap (String × Option String) := {})
    : RenderedCode → Highlighted
  | .text s => .text s
  | .tag t inner =>
    let content := renderedCodeText inner
    match t with
    | .keyword => .token ⟨.keyword none none none, content⟩
    | .string => .token ⟨.str content, content⟩
    | .const name =>
      let (sig, doc?) := constInfo.find? name |>.getD ("", none)
      .token ⟨.const name sig doc? false none, content⟩
    | .sort _former => .token ⟨.sort none, content⟩
    | .otherExpr => renderedCodeToHighlighted constInfo inner
  | .append xs => .seq (xs.map (renderedCodeToHighlighted constInfo))

/-- Collect all constant names referenced in a `RenderedCode` tree. -/
partial def renderedCodeConstNames (acc : Lean.NameSet := {}) : RenderedCode → Lean.NameSet
  | .text _ => acc
  | .tag (.const name) inner => renderedCodeConstNames (acc.insert name) inner
  | .tag _ inner => renderedCodeConstNames acc inner
  | .append xs => xs.foldl (init := acc) fun a x => renderedCodeConstNames a x

end Verso.Genre.Manual.DB
