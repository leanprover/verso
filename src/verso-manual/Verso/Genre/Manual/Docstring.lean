/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean
import Verso.Genre.Manual.Basic
import Verso.Genre.Manual.Index
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

namespace Docstring
deriving instance ToJson for BinderInfo
deriving instance FromJson for BinderInfo
deriving instance ToJson for DefinitionSafety
deriving instance FromJson for DefinitionSafety


structure FieldInfo where
  fieldName  : Name
  projFn     : Name
  /-- It is `some parentStructName` if it is a subobject, and `parentStructName` is the name of the parent structure -/
  subobject? : Option Name
  binderInfo : BinderInfo
  autoParam  : Bool
deriving Inhabited, Repr, ToJson, FromJson

open Syntax (mkCApp) in
instance : Quote BinderInfo where
  quote
    | .default => mkCApp ``BinderInfo.default #[]
    | .implicit => mkCApp ``BinderInfo.implicit #[]
    | .instImplicit => mkCApp ``BinderInfo.instImplicit #[]
    | .strictImplicit => mkCApp ``BinderInfo.strictImplicit #[]

open Syntax (mkCApp) in
instance : Quote DefinitionSafety where
  quote
    | .safe => mkCApp ``DefinitionSafety.safe #[]
    | .unsafe => mkCApp ``DefinitionSafety.unsafe #[]
    | .partial => mkCApp ``DefinitionSafety.partial #[]

open Syntax (mkCApp) in
instance : Quote FieldInfo where
  quote fi :=
    mkCApp ``FieldInfo.mk #[quote fi.fieldName, quote fi.projFn, quote fi.subobject?, quote fi.binderInfo, quote fi.autoParam]

inductive DeclType where
  | structure (fieldNames : Array Name) (fieldInfo : Array FieldInfo) (parents : Array Name) (ancestors : Array Name)
  | def (safety : DefinitionSafety)
  | other
deriving ToJson, FromJson

open Syntax (mkCApp) in
instance : Quote DeclType where
  quote
    | .structure fields infos parents ancestors => mkCApp ``DeclType.«structure» #[quote fields, quote infos, quote parents, quote ancestors]
    | .def safety => mkCApp ``DeclType.def #[quote safety]
    | .other => mkCApp ``DeclType.other #[]

def DeclType.label : DeclType → String
  | .structure .. => "structure"
  | .def .safe => "def"
  | .def .unsafe => "unsafe def"
  | .def .partial => "partial def"
  | other => ""

def DeclType.ofName (env : Environment) (c : Name) : DeclType :=
  if let some info := getStructureInfo? env c then
    let parents := getParentStructures env c
    let ancestors := getAllParentStructures env c
    let fieldInfo := info.fieldInfo.map fun {fieldName, projFn, subobject?, binderInfo, autoParam?} =>
      {fieldName, projFn, subobject?, binderInfo, autoParam := autoParam?.isSome}
    .structure info.fieldNames fieldInfo parents ancestors
  else if let some info := env.find? c then
    match info with
    | .defnInfo di => .def di.safety
    | _ => .other
  else
    .other
end Docstring

def docstring (name : Name) (declType : Docstring.DeclType) (signature : Option Highlighted) : Block where
  name := `Verso.Genre.Manual.Block.docstring
  data := ToJson.toJson (name, declType, signature)

end Block


instance [BEq α] [Hashable α] [FromJson α] : FromJson (HashSet α) where
  fromJson? v := do
    let xs ← v.getArr?
    let vs ← xs.mapM fromJson?
    pure <| HashSet.insertMany {} vs

instance [BEq α] [Hashable α] [ToJson α] : ToJson (HashSet α) where
  toJson v :=
    .arr <| v.toArray.map toJson



@[block_extension Block.docstring]
def docstring.descr : BlockDescr where
  traverse id info _ := do
    let .ok (name, _declType, _signature) := FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Option Highlighted) info
      | do logError "Failed to deserialize docstring data"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name.toString
    Index.addEntry id {term := Doc.Inline.code name.toString}
    if name.getPrefix != .anonymous then
      Index.addEntry id {term := Doc.Inline.code name.getString!, subterm := some <| Doc.Inline.code name.toString}

    -- Save a backreference
    match (← get).get? `Verso.Genre.Manual.docstring with
    | some (.error e) => logError e
    | some (.ok (v : Json)) =>
      let found : HashSet InternalId := (v.getObjVal? name.toString).bind fromJson? |>.toOption |>.getD {}
      modify (·.set `Verso.Genre.Manual.docstring <|  v.setObjVal! name.toString (toJson (found.insert id)))
    | none =>
      modify (·.set `Verso.Genre.Manual.docstring <| Json.mkObj [] |>.setObjVal! name.toString (toJson [id]))

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (name, declType, signature) := FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Option Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring data"; pure .empty
      let x : Html := Html.text true <| Name.toString name
      let sig : Html := Option.map Highlighted.toHtml signature |>.getD {{ {{x}} }}

      let (_, _, xref) ← read
      let idAttr :=
        if let some (_, htmlId) := xref.externalTags.find? id then
          #[("id", htmlId)]
        else #[]


      return {{
        <div class="namedocs" {{idAttr}}>
          <span class="label">{{declType.label}}</span>
          <pre class="signature hl lean block">{{sig}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [highlightingStyle, r#"
.namedocs {
  position: relative;
  border: solid 2px transparent;
  background-clip: padding-box;
  box-sizing: border-box;
  background-color: white;
  border-radius: 0.5em;
  padding: 1.5em;
}
.namedocs:before {
  content: "";
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 1em;
  max-height: 10em;
  z-index: -1;
  border-radius: inherit;
  background: linear-gradient(to bottom, #98B2C0, white);
  margin: -2px;
}
.namedocs .text {
}
.namedocs .signature {
  font-family: var(--verso-code-font-family);
  font-size: larger;
  margin-top: 0;
}
.namedocs .label {
  font-size: smaller;
  font-family: var(--verso-structure-font-family);
  position: absolute;
  right: 1em;
  top: 1em;
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
    doc := .group (doc ++ .nest 4 (.group (.group (behavior := .fill) argDoc) ++ ": " ++ (← ppTerm ret)))

    return ⟨doc, infos⟩
  | _ => return ⟨← ppTerm ⟨stx⟩, infos⟩  -- HACK: not a term


@[block_role_expander docstring]
def docstring : BlockRoleExpander
  | args, #[] => do
    match args with
    | #[.anon (.name x)] =>
      let name ← Elab.realizeGlobalConstNoOverloadWithInfo x
      let blockStx ← match ← Lean.findDocString? (← getEnv) name with
      | none => logWarningAt x m!"No docs found for '{x}'"; pure #[]
      | some docs =>
        let some ast := MD4Lean.parse docs
          | throwErrorAt x "Failed to parse docstring as Markdown"
        ast.blocks.mapM Markdown.blockFromMarkdown

      let declType := Block.Docstring.DeclType.ofName (← getEnv) name

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
      pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstring $(quote name) $(quote declType) $(quote signature)) #[$blockStx,*])]
    | _ => throwError "Expected exactly one positional argument that is a name"
  | _, more => throwErrorAt more[0]! "Unexpected block argument"

def Block.progress (namespaces exceptions : Array Name) (present : List (Name × List Name)) : Block where
  name := `Verso.Genre.Manual.Block.progress
  data := toJson (namespaces, exceptions, present)

@[directive_expander progress]
def progress : DirectiveExpander
  | args, blocks => do
    if h : args.size > 0 then
      throwErrorAt args[0].syntax  "Expected 0 arguments"
    let mut namespaces : NameSet := {}
    let mut exceptions : NameSet := {}
    for block in blocks do
      match block with
      | `<low|(Verso.Syntax.codeblock (column ~_col) ~_open ~(.node _ `null #[nameStx, .node _ `null argsStx]) ~(.atom _info contents) ~_close )> =>
        match nameStx.getId with
        | `namespace =>
          for str in contents.split Char.isWhitespace do
            if !str.isEmpty then
              namespaces := namespaces.insert str.toName
        | `exceptions =>
          for str in contents.split Char.isWhitespace do
            if !str.isEmpty then
              exceptions := exceptions.insert str.toName
        | _ => throwErrorAt nameStx "Expected 'namespace' or 'exceptions'"
      | _ => throwErrorAt block "Expected code block named 'namespace' or 'exceptions'"
    let mut present : NameMap NameSet := {}
    for ns in namespaces do
      present := present.insert ns {}
    for (x, info) in (← getEnv).constants do
      if ignore x then continue
      if exceptions.contains x then continue
      match info with
      | .thmInfo _ => continue -- don't document theorems
      | _ => pure ()
      if ← Meta.isInstance x then continue
      let mut ns := x
      while !ns.isAnonymous && !(ns.getString!.get 0 |>.isUpper) do
        ns := ns.getPrefix
      if let some v := present.find? ns then
        present := present.insert ns (v.insert x)
    let present' := present.toList.map (fun x => (x.1, x.2.toList))
    pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.progress $(quote namespaces.toArray) $(quote exceptions.toArray) $(quote present')) #[])]
where
  ignore (x : Name) : Bool :=
    isPrivateName x ||
    x.hasNum ||
    x.isInternalOrNum ||
    let str := x.getString!
    str ∈ ["sizeOf_spec", "sizeOf_eq", "brecOn", "ind", "ofNat_toCtorIdx", "inj", "injEq", "induct"] ||
    "proof_".isPrefixOf str && (str.drop 6).all (·.isDigit) ||
    "match_".isPrefixOf str && (str.drop 6).all (·.isDigit) ||
    "eq_".isPrefixOf str && (str.drop 3).all (·.isDigit)

@[block_extension Block.progress]
def progress.descr : BlockDescr where
  traverse _ _ _ := pure none
  toHtml := some fun goI goB id info _blocks => open Output.Html in do
    let documented ← match ((← Doc.Html.HtmlT.state).get? `Verso.Genre.Manual.docstring).getD (pure <| .mkObj []) >>= Json.getObj? with
      | .error e =>
        Doc.Html.HtmlT.logError e
        pure .leaf
      | .ok v =>
        pure v
    let mut ok : NameSet := {}
    for ⟨name, _⟩ in documented.toArray do
      let x := name.toName
      ok := ok.insert x

    let .ok ((namespaces : Array Name), (exceptions : Array Name), (present : List (Name × List Name))) := fromJson? info
      | panic! "Can't deserialize progress bar state"

    let check : NameMap (List Name) := present.foldr (init := {}) (fun x z => z.insert x.1 <| x.2)

    return {{
      <dl>
        {{namespaces.map fun ns =>
          let wanted := check.findD ns []
          let notDocumented := wanted.filter (!ok.contains ·)
          let percent := notDocumented.length.toFloat * 100.0 / wanted.length.toFloat
          {{
            <dt><code>{{ns.toString}}</code></dt>
            <dd><details><summary><progress id=s!"prog-{ns}" value=s!"{100 - percent.toUInt8.toNat}" min="0" max="100"></progress> <label for=s!"prog-ns">s!"Missing {percent}%"</label></summary> {{notDocumented |>.map (·.toString) |> String.intercalate ", " }}</details></dd>
          }}
        }}
      </dl>
    }}
  toTeX := some (fun _ _ _ _ _ => pure <| Output.TeX.text "Unsupported")
