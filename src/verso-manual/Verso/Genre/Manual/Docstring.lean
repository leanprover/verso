/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Data.HashSet

import Verso.Genre.Manual.Basic
import Verso.Genre.Manual.Index
import Verso.Genre.Manual.Markdown
import Verso.Code
import Verso.Doc.Elab.Monad
import Verso.Doc.ArgParse

import SubVerso.Highlighting

import MD4Lean

open Lean hiding HashSet
open Std (HashSet)

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


structure FieldInfo where
  fieldName : Highlighted
  type : Highlighted
  projFn : Name
  /-- It is `some parentStructName` if it is a subobject, and `parentStructName` is the name of the parent structure -/
  subobject? : Option Name
  binderInfo : BinderInfo
  autoParam  : Bool
  docString? : Option String
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
  quote
    | {fieldName, type, projFn, subobject?, binderInfo, autoParam, docString?} =>
      mkCApp ``FieldInfo.mk #[quote fieldName, quote type, quote projFn, quote subobject?, quote binderInfo, quote autoParam, quote docString?]

structure DocName where
  name : Name
  signature : Highlighted
  docstring? : Option String
deriving ToJson, FromJson

open Syntax (mkCApp) in
instance : Quote DocName where
  quote
    | {name, signature, docstring?} => mkCApp ``DocName.mk #[quote name, quote signature, quote docstring?]

inductive DeclType where
  | structure (constructor : DocName) (fieldNames : Array Name) (fieldInfo : Array FieldInfo) (parents : Array Name) (ancestors : Array Name)
  | def (safety : DefinitionSafety)
  | other
deriving ToJson, FromJson

open Syntax (mkCApp) in
instance : Quote DeclType where
  quote
    | .structure ctor fields infos parents ancestors => mkCApp ``DeclType.«structure» #[quote ctor, quote fields, quote infos, quote parents, quote ancestors]
    | .def safety => mkCApp ``DeclType.def #[quote safety]
    | .other => mkCApp ``DeclType.other #[]

def DeclType.label : DeclType → String
  | .structure .. => "structure"
  | .def .safe => "def"
  | .def .unsafe => "unsafe def"
  | .def .partial => "partial def"
  | other => ""

example := Meta.mkProjection

open Meta in
def DocName.ofName (c : Name) : MetaM DocName := do
  let env ← getEnv
  if let some _ := env.find? c then
    let ⟨fmt, infos⟩ ← withOptions (·.setBool `pp.tagAppFns true) <| ppSignature c
    let tt := Lean.Widget.TaggedText.prettyTagged (w := 48) fmt
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

    pure ⟨c, ← renderTagged {} sig, ← findDocString? env c⟩
  else pure ⟨c, Highlighted.seq #[], none⟩

open Meta in
def DeclType.ofName (c : Name) : MetaM DeclType := do
  let env ← getEnv
  if let some info := env.find? c then
    match info with
    | .defnInfo di => return .def di.safety
    | .inductInfo ii =>
      if let some info := getStructureInfo? env c then
        let ctor := getStructureCtor env c
        let parents := getParentStructures env c
        let ancestors := getAllParentStructures env c
        let fieldInfo ←
          forallTelescopeReducing ii.type fun params _ =>
            withLocalDeclD `self (mkAppN (mkConst c (ii.levelParams.map mkLevelParam)) params) fun s =>
              info.fieldInfo.mapM fun {fieldName, projFn, subobject?, binderInfo, autoParam?} => do
                let proj ← mkProjection s fieldName
                let type ← inferType proj >>= instantiateMVars
                let type' ← withOptions (·.setInt `format.width 40 |>.setBool `pp.tagAppFns true) <| (Widget.ppExprTagged type)
                let projType ← withOptions (·.setInt `format.width 40 |>.setBool `pp.tagAppFns true) <| ppExpr type
                let fieldName' := Highlighted.token ⟨.const projFn projType.pretty (← findDocString? env projFn), fieldName.toString⟩
                pure {fieldName := fieldName', type := ← renderTagged {} type', projFn, subobject?, binderInfo, autoParam := autoParam?.isSome, docString? := ← findDocString? env projFn}
        return .structure (← DocName.ofName ctor.name) info.fieldNames fieldInfo.reverse parents ancestors
      else return .other
    | _ => return .other
  else
    return .other

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


open Verso.Genre.Manual.Markdown in
@[block_extension Block.docstring]
def docstring.descr : BlockDescr where
  traverse id info _ := do
    let .ok (name, declType, _signature) := FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Option Highlighted) info
      | do logError "Failed to deserialize docstring data"; pure none

    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name.toString
    Index.addEntry id {term := Doc.Inline.code name.toString}
    if name.getPrefix != .anonymous then
      Index.addEntry id {term := Doc.Inline.code name.getString!, subterm := some <| Doc.Inline.code name.toString}

    match declType with
    | .structure _ctor fields fieldInfos _parents _ancestors =>
      for (f, i) in fields.zip fieldInfos do
        Index.addEntry id {term := Doc.Inline.code i.projFn.toString}
        if i.projFn.getPrefix != .anonymous then
          Index.addEntry id {
            term := Doc.Inline.code f.toString,
            subterm := some <| Doc.Inline.concat #[Doc.Inline.code i.projFn.toString, Doc.Inline.text " (structure field)"]
          }
    | _ => pure ()

    -- Save a backreference
    match (← get).get? `Verso.Genre.Manual.docstring with
    | some (.error e) => logError e
    | some (.ok (v : Json)) =>
      let found : HashSet InternalId := (v.getObjVal? name.toString).bind fromJson? |>.toOption |>.getD {}
      modify (·.set `Verso.Genre.Manual.docstring <|  v.setObjVal! name.toString (toJson (found.insert id)))
    | none =>
      modify (·.set `Verso.Genre.Manual.docstring <| Json.mkObj [] |>.setObjVal! name.toString (toJson [id]))

    -- Save a new-style backreference
    modify fun st => st.saveDomainObject `Verso.Manual.doc name.toString id

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (name, declType, signature) := FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Option Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring data"; pure .empty
      let x : Html := Html.text true <| Name.toString name
      let sig : Html ← Option.map Highlighted.toHtml signature |>.getD (pure {{ {{x}} }})

      let (_, _, xref) ← read
      let idAttr :=
        if let some (_, htmlId) := xref.externalTags[id]? then
          #[("id", htmlId)]
        else #[]

      let md2html (str : String) : HtmlT Manual (ReaderT ExtensionImpls IO) Html := do
        let some md := MD4Lean.parse str
          | HtmlT.logError "Markdown parsing failed for {str}"
            pure <| Html.text true str
        match md.blocks.mapM blockFromMarkdown' with
        | .error e => HtmlT.logError e; pure <| Html.text true str
        | .ok blks => blks.mapM goB

      let more : Html ← do
        match declType with
        | .structure ctor _fields infos _parents _ancestors =>
          let ctorRow ←
            if isPrivateName ctor.name then
              pure Html.empty
            else pure {{
                <h1>"Constructor"</h1>
                <table>
                  <tr><td><code class="hl lean inline">{{← ctor.signature.toHtml}}</code></td></tr>
                  {{ ← if let some d := ctor.docstring? then do
                      pure {{<tr><td>{{← md2html d}}</td></tr>}}
                    else pure Html.empty
                  }}
                </table>
              }}
          pure <| {{
            {{ ctorRow }}
            <h1>"Fields"</h1>
            <table>
              {{← infos.mapM fun i => do
                let docRow ←
                  if let some doc := i.docString? then do
                    let doc ← md2html doc
                    pure {{
                      <tr>
                        <td colspan="2"></td>
                        <td> {{ doc }}
                        </td>
                      </tr>
                    }}
                    else
                      pure Html.empty

                 pure <| {{
                  <tr>
                    <td><code class="hl lean inline">{{← i.fieldName.toHtml}}</code></td>
                    <td>":"</td>
                    <td><code class="hl lean inline">{{←  i.type.toHtml }}</code></td>
                  </tr>
                }} ++ docRow
              }}
            </table>
          }}
        | _ => pure .empty

      return {{
        <div class="namedocs" {{idAttr}}>
          <span class="label">{{declType.label}}</span>
          <pre class="signature hl lean block">{{sig}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
            {{ more }}
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
.namedocs h1 {
  font-size: inherit;
  font-weight: bold;
}
"#]
  extraJs := [highlightingJs]

open Verso.Doc.Elab


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

      let declType ← Block.Docstring.DeclType.ofName name

      let ⟨fmt, infos⟩ ← withOptions (·.setBool `pp.tagAppFns true) <| Block.Docstring.ppSignature name
      let tt := Lean.Widget.TaggedText.prettyTagged (w := 48) fmt
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
