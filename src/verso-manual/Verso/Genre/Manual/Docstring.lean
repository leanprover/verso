/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean
import Verso.Genre.Manual.Basic
import Verso.Code
import Verso.Doc.Elab.Monad
import Verso.Doc.ArgParse

import SubVerso.Highlighting

import MD4Lean

open Lean

open Verso.Doc.Elab.PartElabM
open Verso.Code

open SubVerso.Highlighting

namespace Verso.Genre.Manual

namespace Block

def docstring (name : Name) (signature : Option Highlighted) : Block where
  name := `Verso.Genre.Manual.Block.docstring
  data := ToJson.toJson (name, signature)

end Block

@[block_extension Block.docstring]
def docstring.descr : BlockDescr where
  traverse _ _ _ := pure none
  toHtml := some <| fun _goI goB _id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (name, signature) := FromJson.fromJson? info
        | do Verso.Doc.Html.HtmlT.logError ""; pure .empty
      let x : Html := Html.text true <| Name.toString name
      let sig : Html := Option.map Highlighted.toHtml signature |>.getD {{ {{x}} }}

      return {{
        <div class="docstring">
          <pre class="signature hl lean block">{{sig}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [highlightingStyle, r#"
.docstring .text {
  padding-left : 1em;
  padding-right : 1em;
}
.docstring .signature {
  font-family: var(--verso-code-font-family);
  font-size: larger;
}
"#]
  extraJs := [highlightingJs]

open Verso.Doc.Elab


namespace Markdown
open MD4Lean

def attrText : AttrText → Except String String
  | .normal str => pure str
  | .nullchar => throw "Null character"
  | .entity ent => throw s!"Unsupported entity {ent}"

def attr [Monad m] [MonadError m] (val : Array AttrText) : m Term := do
  match val.mapM attrText |>.map Array.toList |>.map String.join with
  | .error e => throwError e
  | .ok s => pure (quote s)

partial def inlineFromMarkdown [Monad m] [MonadQuotation m] [MonadError m] : Text → m Term
  | .normal str | .br str | .softbr str => ``(Verso.Doc.Inline.text $(quote str))
  | .nullchar => throwError "Null character"
  | .del _ => throwError "Strikethrough"
  | .em txt => do ``(Verso.Doc.Inline.emph #[$[$(← txt.mapM inlineFromMarkdown)],*])
  | .strong txt => do ``(Verso.Doc.Inline.bold #[$[$(← txt.mapM inlineFromMarkdown)],*])
  | .a href _ _ txt => do ``(Verso.Doc.Inline.link #[$[$(← txt.mapM inlineFromMarkdown)],*] $(quote (← attr href)))
  | .latexMath m => ``(Verso.Doc.Inline.math Verso.Doc.MathMode.inline $(quote <| String.join m.toList))
  | .latexMathDisplay m =>  ``(Verso.Doc.Inline.math Verso.Doc.MathMode.display $(quote <| String.join m.toList))
  | .u .. => throwError "Underline"
  | .code str => ``(Verso.Doc.Inline.code $(quote <| String.join str.toList))
  | .entity ent => throwError s!"Unsupported entity {ent}"
  | .img .. => throwError s!"Image"
  | .wikiLink .. => throwError s!"Wiki-style link"



partial def blockFromMarkdown [Monad m] [MonadQuotation m] [MonadError m] : MD4Lean.Block → m Term
  | .p txt => do ``(Verso.Doc.Block.para #[$[$(← txt.mapM inlineFromMarkdown)],*])
  | .blockquote bs => do ``(Verso.Doc.Block.blockquote #[$[$(← bs.mapM blockFromMarkdown)],*])
  | .code _ _ _ strs => do ``(Verso.Doc.Block.code $(quote <| String.join strs.toList))
  | .looseUl _ items => do ``(Verso.Doc.Block.ul #[$[$(← items.mapM looseItemFromMarkdown)],*])
  | .looseOl i _ items => do ``(Verso.Doc.Block.ol (Int.ofNat $(quote i)) #[$[$(← items.mapM looseItemFromMarkdown)],*])
  | .tightUl _ items => do
    let itemStx ← items.mapM tightItemFromMarkdown
    ``(Verso.Doc.Block.ul #[$itemStx,*])
  | .tightOl i _ items => do
    let itemStx ← items.mapM tightItemFromMarkdown
    ``(Verso.Doc.Block.ol (Int.ofNat $(quote i)) #[$itemStx,*])
  | .header .. => throwError "header"
  | .html .. => throwError "HTML"
  | .hr => throwError "Horizontal rule (thematic break)"
  | .table .. => throwError "Horizontal rule (thematic break)"
where
  looseItemFromMarkdown [Monad m] [MonadQuotation m] [MonadError m] (item : MD4Lean.Li MD4Lean.Block) : m Term := do
    if item.isTask then throwError "Tasks unsupported"
    else ``(Verso.Doc.ListItem.mk 0 #[$[$(← item.contents.mapM blockFromMarkdown)],*])
  tightItemFromMarkdown [Monad m] [MonadQuotation m] [MonadError m] (item : MD4Lean.Li MD4Lean.Text) : m Term := do
    if item.isTask then throwError "Tasks unsupported"
    else ``(Verso.Doc.ListItem.mk 0 #[Verso.Doc.Block.para #[$(← item.contents.mapM inlineFromMarkdown),*]])

end Markdown

open Lean.PrettyPrinter Delaborator in
def ppSignature (c : Name) : MetaM FormatWithInfos := do
  let decl ← getConstInfo c
  let e := .const c (decl.levelParams.map mkLevelParam)
  let (stx, infos) ← delabCore e (delab := delabConstWithSignature)
  match stx with
  | `(declSigWithId|$nameUniv $argsRet:declSig ) => do
    let mut doc : Std.Format := .nil
    match nameUniv with
    | `($x:ident.{$uni,*}) =>
      let unis : List Format ← uni.getElems.toList.mapM (ppCategory `level ·.raw)
      doc := Std.Format.text x.getId.toString ++ ".{" ++ .joinSep unis ", " ++ "}"
    | _ => doc ← ppTerm nameUniv
    let `(declSig| $args* : $ret) := argsRet
      | return ⟨← ppTerm ⟨stx⟩, infos⟩  -- HACK: not a term
    let mut argDoc := .line
    for arg in args do
      match arg with
      | `(binderIdent|$x:ident) => argDoc := argDoc ++ (← ppTerm x)
      | `(binderIdent|$x:hole) => argDoc := argDoc ++ (← ppTerm ⟨x⟩)
      | `(bracketedBinder|($xs:ident* $[: $ty]?)) =>
        let xs' ← xs.toList.mapM (fun (x : Ident) => ppTerm x)
        argDoc := argDoc ++ "(" ++ .joinSep xs' " "
        if let some t := ty then
          argDoc := argDoc ++ " : " ++ .group (← ppTerm t)
        argDoc := argDoc ++ ")"
      | `(bracketedBinder|{$xs:ident* $[: $ty]?}) =>
        let xs' ← xs.toList.mapM (fun (x : Ident) => ppTerm x)
        argDoc := argDoc ++ "{" ++ .joinSep xs' " "
        if let some t := ty then
          argDoc := argDoc ++ " : " ++ .group (← ppTerm t)
        argDoc := argDoc ++ "}"
      | `(bracketedBinder|⦃$xs:ident* $[: $ty]?⦄) =>
        let xs' ← xs.toList.mapM (fun (x : Ident) => ppTerm x)
        argDoc := argDoc ++ "⦃" ++ .joinSep xs' " "
        if let some t := ty then
          argDoc := argDoc ++ " : " ++ .group (← ppTerm t)
        argDoc := argDoc ++ "⦄"
      | `(bracketedBinder|[$ty]) => argDoc := argDoc ++ "[" ++ .group (← ppTerm ty) ++ "]"
      | _ => return ⟨← ppTerm ⟨stx⟩, infos⟩
      argDoc := argDoc ++ .line
    doc := .group (doc ++ .nest 4 (.group (.group (behavior := .fill) argDoc) ++ .line ++ ": " ++ (← ppTerm ret)))

    return ⟨doc, infos⟩
  | _ => return ⟨← ppTerm ⟨stx⟩, infos⟩  -- HACK: not a term


@[block_role_expander docstring]
def docstring : BlockRoleExpander
  | args, #[] => do
    match args with
    | #[.anon (.name x)] =>
      let name ← resolveGlobalConstNoOverload x
      match ← Lean.findDocString? (← getEnv) name with
      | none => throwErrorAt x "No docs found for '{x}'"
      | some docs =>
        let some ast := MD4Lean.parse docs
          | throwErrorAt x "Failed to parse docstring as Markdown"
        let blockStx ← ast.blocks.mapM Markdown.blockFromMarkdown
        let ⟨fmt, infos⟩ ← withOptions (·.setInt `format.width 60 |>.setBool `pp.tagAppFns true) <| ppSignature name
        let tt := Lean.Widget.TaggedText.prettyTagged (w := 80) fmt
        let ctx := {
          env           := (← getEnv)
          mctx          := (← getMCtx)
          options       := (← getOptions)
          currNamespace := (← getCurrNamespace)
          openDecls     := (← getOpenDecls)
          fileMap       := default
          ngen          := (← getNGen)
        }
        let sig := Lean.Widget.tagCodeInfos ctx infos tt
        let signature ← some <$> renderTagged {} sig
        pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstring $(quote name) $(quote signature)) #[$blockStx,*])]
    | _ => throwError "Expected exactly one positional argument that is a name"
  | _, more => throwErrorAt more[0]! "Unexpected block argument"
