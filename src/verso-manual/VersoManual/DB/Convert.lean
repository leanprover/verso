/-
Copyright (c) 2025-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import DocGen4.RenderedCode
public import SubVerso.Highlighting.Highlighted
public section

namespace Verso.Genre.Manual.DB

open DocGen4 (RenderedCode FormatCode SortFormer)
open SubVerso.Highlighting (Highlighted Token)

/-- Extracts plain text content from a `RenderedCode` tree, discarding all tags. -/
partial def renderedCodeText : RenderedCode → String
  | .text s => s
  | .tag _ inner => renderedCodeText inner
  | .append xs => String.join (xs.toList.map renderedCodeText)

/--
Converts a `RenderedCode` value to a `Highlighted` value (for Verso's rendering pipeline).

The `localVars` parameter (from `FormatCode.localVars`) maps local variable indices to
`(userName, typeFormat?)`. When a `.localVar idx isBinder` tag is encountered, a
`Token.Kind.var` token is emitted with the variable's type rendered as plain text.

The `constInfo` parameter provides hover data for known constants: a map from `Name` to
`(signature, docstring?)`.
-/
partial def renderedCodeToHighlighted
    (constInfo : Lean.NameMap (String × Option String) := {})
    (localVars : Array (Lean.Name × Option Lean.Format) := #[]) :
    RenderedCode → Highlighted
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
    | .localVar idx _isBinder =>
      match localVars[idx]? with
      | some (userName, typeFmt?) =>
        let typeStr := typeFmt?.map (·.pretty) |>.getD ""
        -- Use the userName as FVarId since we don't have real FVarIds from the DB
        .token ⟨.var ⟨userName⟩ typeStr none, content⟩
      | none => renderedCodeToHighlighted constInfo localVars inner
    | .otherExpr => renderedCodeToHighlighted constInfo localVars inner
  | .append xs => .seq (xs.map (renderedCodeToHighlighted constInfo localVars))

/-- Collects all constant names referenced in a `RenderedCode` tree. -/
partial def renderedCodeConstNames (acc : Lean.NameSet := {}) : RenderedCode → Lean.NameSet
  | .text _ => acc
  | .tag (.const name) inner => renderedCodeConstNames (acc.insert name) inner
  | .tag _ inner => renderedCodeConstNames acc inner
  | .append xs => xs.foldl (init := acc) fun a x => renderedCodeConstNames a x

/-- Extracts plain text from a `FormatCode` by rendering at the given width. -/
def formatCodeText (fc : FormatCode) (width : Nat := Std.Format.defWidth) : String :=
  renderedCodeText (fc.render width)

/--
Converts a `FormatCode` to `Highlighted` by rendering at the given width. Local variable
tags are resolved using the `FormatCode.localVars` array for hover information.
-/
def formatCodeToHighlighted (constInfo : Lean.NameMap (String × Option String) := {})
    (fc : FormatCode) (width : Nat := Std.Format.defWidth) : Highlighted :=
  renderedCodeToHighlighted constInfo fc.localVars (fc.render width)

/-- Collects all constant names referenced in a `FormatCode`. -/
def formatCodeConstNames (acc : Lean.NameSet := {}) (fc : FormatCode) : Lean.NameSet :=
  renderedCodeConstNames acc fc.render

/-- Remaps all `Format.tag` indices by adding `offset`, as preparation for combining documents. -/
private partial def offsetFormatTags (offset : Nat) : Lean.Format → Lean.Format
  | .tag n f => .tag (n + offset) (offsetFormatTags offset f)
  | .nest n f => .nest n (offsetFormatTags offset f)
  | .append a b => .append (offsetFormatTags offset a) (offsetFormatTags offset b)
  | .group f beh => .group (offsetFormatTags offset f) beh
  | f => f

/--
Prepares to append a `FormatCode` to another one whose metadata is given by `tags` and `localVars`.
The resulting data contains both sets of metadata, with data in `tags` and `localVars` unchanged.
This allows the code associated with `tags` and `localVars` to be appended unmodified to the result
of this function.
-/
private def prepareAppend (fc : FormatCode)
    (tags : Array RenderedCode.Tag) (localVars : Array (Lean.Name × Option Lean.Format)) :
    Lean.Format × Array RenderedCode.Tag × Array (Lean.Name × Option Lean.Format) :=
  let tagOff := tags.size
  let lvOff := localVars.size
  let fmt := offsetFormatTags tagOff fc.fmt
  let newTags := fc.tags.map fun
    | .localVar idx isBinder => .localVar (idx + lvOff) isBinder
    | t => t
  let newLVs := fc.localVars.map fun (n, tf?) =>
    (n, tf?.map (offsetFormatTags tagOff))
  (fmt, tags ++ newTags, localVars ++ newLVs)

/--
Builds a combined `FormatCode` for a full declaration signature: `name.{u, v} arg₁ arg₂ … : type`.
-/
def buildSignatureFormatCode (name : Lean.Name) (levelParams : List Lean.Name)
    (args : Array FormatCode) (type : FormatCode)
    : FormatCode := Id.run do
  -- Start with a const tag for the declaration name
  let mut tags : Array RenderedCode.Tag := #[.const name]
  let mut localVars : Array (Lean.Name × Option Lean.Format) := #[]
  -- Name with universe parameters
  let univSuffix := if levelParams.isEmpty then ""
    else ".{" ++ ", ".intercalate (levelParams.map Lean.Name.toString) ++ "}"
  let nameFmt : Lean.Format := .tag 0 (.text name.toString) ++ .text univSuffix
  -- The name, each argument, and the return type are all pieces in a single fill group
  -- with nest 2. The fill group packs greedily — fitting as many pieces per line as
  -- possible. The " :" is glued to the last argument so the colon stays on the same
  -- line, with a .line break before the return type. This gives results like:
  -- ```
  -- foo.{u, v} (x : A) (y z : B)
  --   (w : A) :
  --   SuperLongReturnType
  -- ```
  let mut body : Lean.Format := nameFmt
  for arg in args do
    let (fmt, tags', lvs') := prepareAppend arg tags localVars
    tags := tags'
    localVars := lvs'
    body := body ++ .line ++ fmt
  let (typeFmt, tags', lvs') := prepareAppend type tags localVars
  tags := tags'
  localVars := lvs'
  let sigFmt := .group (.nest 2 (body ++ " :" ++ .line ++ typeFmt)) .fill
  return { fmt := sigFmt, tags, localVars }
