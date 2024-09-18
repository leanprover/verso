/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Data.HashSet

import VersoManual.Basic
import VersoManual.Index
import VersoManual.Markdown
import Verso.Code
import Verso.Doc.Elab.Monad
import Verso.Doc.ArgParse

import SubVerso.Highlighting

import MD4Lean

open Lean hiding HashSet
open Std (HashSet)

open Verso.Doc.Elab.PartElabM
open Verso.Code
open Verso.ArgParse

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
  name : Name
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
    | {fieldName, type, name, projFn, subobject?, binderInfo, autoParam, docString?} =>
      mkCApp ``FieldInfo.mk #[quote fieldName, quote type, quote name, quote projFn, quote subobject?, quote binderInfo, quote autoParam, quote docString?]

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
  | structure (isClass : Bool) (constructor : DocName) (fieldNames : Array Name) (fieldInfo : Array FieldInfo) (parents : Array Name) (ancestors : Array Name)
  | def (safety : DefinitionSafety)
  | inductive (constructors : Array DocName) (numArgs : Nat) (propOnly : Bool)
  | other
deriving ToJson, FromJson

open Syntax (mkCApp) in
instance : Quote DeclType where
  quote
    | .structure isClass ctor fields infos parents ancestors =>
      mkCApp ``DeclType.«structure» #[quote isClass, quote ctor, quote fields, quote infos, quote parents, quote ancestors]
    | .def safety => mkCApp ``DeclType.def #[quote safety]
    | .inductive ctors numArgs propOnly => mkCApp ``DeclType.inductive #[quote ctors, quote numArgs, quote propOnly]
    | .other => mkCApp ``DeclType.other #[]

def DeclType.label : DeclType → String
  | .structure false .. => "structure"
  | .structure true .. => "type class"
  | .def .safe => "def"
  | .def .unsafe => "unsafe def"
  | .def .partial => "partial def"
  | .inductive _ _ false => "inductive type"
  | .inductive _ 0 true => "inductive proposition"
  | .inductive _ _ true => "inductive predicate"
  | other => ""


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

    pure ⟨c, ← renderTagged {} none sig, ← findDocString? env c⟩
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
              (info.fieldNames.zip info.fieldInfo).mapM fun (name, {fieldName, projFn, subobject?, binderInfo, autoParam?}) => do
                let proj ← mkProjection s fieldName
                let type ← inferType proj >>= instantiateMVars
                let type' ← withOptions (·.setInt `format.width 40 |>.setBool `pp.tagAppFns true) <| (Widget.ppExprTagged type)
                let projType ← withOptions (·.setInt `format.width 40 |>.setBool `pp.tagAppFns true) <| ppExpr type
                let fieldName' := Highlighted.token ⟨.const projFn projType.pretty (← findDocString? env projFn), fieldName.toString⟩
                pure {fieldName := fieldName', type := ← renderTagged {} none type', name, projFn, subobject?, binderInfo, autoParam := autoParam?.isSome, docString? := ← findDocString? env projFn}
        return .structure (isClass env c) (← DocName.ofName ctor.name) info.fieldNames fieldInfo parents ancestors

      else
        let ctors ← ii.ctors.mapM DocName.ofName
        let t ← inferType <| .const c (ii.levelParams.map .param)
        let t' ← reduceAll t
        return .inductive ctors.toArray (ii.numIndices + ii.numParams) (isPred t')
    | _ => return .other
  else
    return .other
where
  isPred : Expr → Bool
    | .sort u => u.isZero
    | .forallE _ _ e _ => isPred e
    | .mdata _ e => isPred e
    | .letE _ _ _ e _ => isPred e
    | _ => false

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

def docstringStyle := r#"
.namedocs {
  position: relative;
  border: solid 2px #99b3c0;
  background-color: #99b3c0;
  padding-left: 1px;
  padding-right: 1px;
  padding-bottom: 1px;
  padding-top: 1.5em;
  margin-bottom: 1em;
}

.namedocs .text {
  background-color: white;
  padding: 1.5em;
  margin-top: 0.5em;
}

.namedocs .text > pre {
  overflow-x: auto;
}

.namedocs .signature {
  font-family: var(--verso-code-font-family);
  font-size: larger;
  margin-top: 0;
  margin-left: 1.5em;
  margin-right: 1.5em;
}
.namedocs .label {
  font-size: smaller;
  font-family: var(--verso-structure-font-family);
  position: absolute;
  right: 0.5em;
  top: 0.5em;
}
.namedocs h1 {
  font-size: inherit;
  font-weight: bold;
}
.namedocs > .text > .constructors {
  text-indent: -1ex;
}
.namedocs > .text > .constructors > li {
  display: block;
}
.namedocs > .text > .constructors > li::before {
  content: '|';
  width: 1ex;
  display: inline-block;
  font-size: larger;
}
.namedocs > .text > .constructors > li > .doc {
  text-indent: 0;
}

"#

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
    | .structure isClass ctor fields fieldInfos _parents _ancestors =>
      if isClass then
        for (f, i) in fields.zip fieldInfos do
          Index.addEntry id {term := Doc.Inline.code i.projFn.toString}
          if i.projFn.getPrefix != .anonymous then
            Index.addEntry id {
              term := Doc.Inline.code f.toString,
              subterm := some <| Doc.Inline.concat #[Doc.Inline.code i.projFn.toString, Doc.Inline.text " (class method)"]
            }
      else
        Index.addEntry id {
          term := Doc.Inline.code ctor.name.toString,
          subterm := some <| Doc.Inline.concat #[Doc.Inline.text "Constructor of ", Doc.Inline.code name.toString]
        }
        modify fun st => st.saveDomainObject `Verso.Manual.doc ctor.name.toString id

        for (f, i) in fields.zip fieldInfos do
          Index.addEntry id {term := Doc.Inline.code i.projFn.toString}
          modify fun st => st.saveDomainObject `Verso.Manual.doc i.projFn.toString id
          if i.projFn.getPrefix != .anonymous then
            Index.addEntry id {
              term := Doc.Inline.code f.toString,
              subterm := some <| Doc.Inline.concat #[Doc.Inline.code i.projFn.toString, Doc.Inline.text " (structure field)"]
            }
    | .inductive ctors _ _ =>
      for c in ctors do
        Index.addEntry id {
          term := Doc.Inline.code c.name.toString,
          subterm := some <| Doc.Inline.concat #[Doc.Inline.text "Constructor of ", Doc.Inline.code name.toString]
        }
        modify fun st => st.saveDomainObject `Verso.Manual.doc c.name.toString id
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
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok (name, declType, signature) := FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Option Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring data while generating HTML"; pure .empty
      let x : Html := Html.text true <| Name.toString name
      let sig : Html ← Option.map Highlighted.toHtml signature |>.getD (pure {{ {{x}} }})

      let xref ← state
      let idAttr :=
        if let some (_, htmlId) := xref.externalTags[id]? then
          #[("id", htmlId)]
        else #[]

      return {{
        <div class="namedocs" {{idAttr}}>
          <span class="label">{{declType.label}}</span>
          <pre class="signature hl lean block">{{sig}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
            {{← moreDeclHtml goB declType}}
          </div>
        </div>
      }}
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [highlightingStyle, docstringStyle]
  extraJs := [highlightingJs]
where
  md2html (goB) (str : String) : Verso.Doc.Html.HtmlT Manual (ReaderT ExtensionImpls IO) Verso.Output.Html :=
    open Verso.Doc.Html in
    open Verso.Output Html in do
    let some md := MD4Lean.parse str
      | HtmlT.logError "Markdown parsing failed for {str}"
        pure <| Html.text true str
    match md.blocks.mapM (blockFromMarkdown' · Markdown.strongEmphHeaders') with
    | .error e => HtmlT.logError e; pure <| Html.text true str
    | .ok blks => blks.mapM goB
  moreDeclHtml (goB)
    | .structure false ctor fields infos _parents _ancestors =>
      open Verso.Doc.Html in
      open Verso.Output Html in do
      let ctorRow ←
        if isPrivateName ctor.name then
          pure Html.empty
        else pure {{
            <h1>"Constructor"</h1>
            <table>
              <tr><td><code class="hl lean inline">{{← ctor.signature.toHtml}}</code></td></tr>
              {{ ← if let some d := ctor.docstring? then do
                  pure {{<tr><td>{{← md2html goB d}}</td></tr>}}
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
                let doc ← md2html goB doc
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
    | .structure true ctor _fields infos _parents _ancestors =>
      open Verso.Doc.Html in
      open Verso.Output Html in do
      let ctorRow ←
        if isPrivateName ctor.name then
          pure Html.empty
        else pure {{
            <h1>"Instance Constructor"</h1>
            <table>
              <tr><td><code class="hl lean inline">{{← ctor.signature.toHtml}}</code></td></tr>
              {{ ← if let some d := ctor.docstring? then do
                  pure {{<tr><td>{{← md2html goB d}}</td></tr>}}
                else pure Html.empty
              }}
            </table>
          }}
      pure <| {{
        {{ ctorRow }}
        <h1>"Methods"</h1>
        <table>
          {{← infos.mapM fun i => do
            let docRow ←
              if let some doc := i.docString? then do
                let doc ← md2html goB doc
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

    | .inductive ctors _ _ =>
      open Verso.Doc.Html in
      open Verso.Output Html in do
      pure {{
        <h1>"Constructors"</h1>
        <ul class="constructors">
          {{← ctors.mapM fun c => do
              pure {{
                <li>
                  <code class="hl lean inline">{{← c.signature.toHtml}}</code>
                  {{← if let some d := c.docstring? then do
                      pure {{<div class="doc">{{← md2html goB d}}</div>}}
                    else pure Html.empty
                  }}
                </li>
              }}
          }}
        </ul>
      }}
    | _ => pure .empty

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
        ast.blocks.mapM (Markdown.blockFromMarkdown · Markdown.strongEmphHeaders)

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
      let signature ← some <$> renderTagged {} none sig
      pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstring $(quote name) $(quote declType) $(quote signature)) #[$blockStx,*])]
    | _ => throwError "Expected exactly one positional argument that is a name"
  | _, more => throwErrorAt more[0]! "Unexpected block argument"

def Block.optionDocs (name : Name) (defaultValue : Option Highlighted) : Block where
  name := `Verso.Genre.Manual.optionDocs
  data := ToJson.toJson (name, defaultValue)

open Lean Elab Term in
elab "docs_for%" name:ident : term => do
  let x ← realizeGlobalConstNoOverloadWithInfo name
  if let some docs ← findDocString? (← getEnv) x then
    pure <| .lit <| .strVal docs
  else
    throwErrorAt name "No docs for {x}"

open Lean Elab Term in
elab "sig_for%" name:ident : term => do
  let x ← realizeGlobalConstNoOverloadWithInfo name
  let ⟨fmt, _infos⟩ ← withOptions (·.setBool `pp.tagAppFns true) <| Block.Docstring.ppSignature x
  let tt := Lean.Widget.TaggedText.prettyTagged (w := 48) fmt
  pure <| .lit <| .strVal tt.stripTags


def highlightDataValue (v : DataValue) : Highlighted :=
  .token <|
    match v with
    | .ofString (v : String) => ⟨.str v, toString v⟩
    | .ofBool b =>
      if b then
        ⟨.const ``true (sig_for% true) (some <| docs_for% true), "true"⟩
      else
        ⟨.const ``false (sig_for% false) (some <| docs_for% false), "false"⟩
    | .ofName (v : Name) => ⟨.unknown, v.toString⟩
    | .ofNat (v : Nat) => ⟨.unknown, toString v⟩
    | .ofInt (v : Int) => ⟨.unknown, toString v⟩
    | .ofSyntax (v : Syntax) => ⟨.unknown, toString v⟩ -- TODO


@[block_role_expander optionDocs]
def optionDocs : BlockRoleExpander
  | args, #[] => do
    let #[.anon (.name x)] := args
      | throwError "Expected exactly one positional argument that is a name"
    let optDecl ← getOptionDecl x.getId
    let some mdAst := MD4Lean.parse optDecl.descr
      | throwErrorAt x "Failed to parse docstring as Markdown"
    let contents ← mdAst.blocks.mapM (Markdown.blockFromMarkdown · Markdown.strongEmphHeaders)
    pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.optionDocs $(quote x.getId) $(quote <| highlightDataValue optDecl.defValue)) #[$contents,*])]

  | _, more => throwErrorAt more[0]! "Unexpected block argument"

open Verso.Genre.Manual.Markdown in
@[block_extension optionDocs]
def optionDocs.descr : BlockDescr where
  traverse id info _ := do
    let .ok (name, _defaultValue) := FromJson.fromJson? (α := Name × Highlighted) info
      | do logError "Failed to deserialize docstring data while traversing an option"; pure none

    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name.toString
    Index.addEntry id {term := Doc.Inline.code name.toString}
    if name.getPrefix != .anonymous then
      Index.addEntry id {term := Doc.Inline.code name.getString!, subterm := some <| Doc.Inline.code name.toString}

    modify fun st => st.saveDomainObject `Verso.Manual.doc.option name.toString id

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (name, defaultValue) := FromJson.fromJson? (α := Name × Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring data while generating HTML for an option"; pure .empty
      let x : Html := Html.text true <| Name.toString name

      let xref ← HtmlT.state
      let idAttr :=
        if let some (_, htmlId) := xref.externalTags[id]? then
          #[("id", htmlId)]
        else #[]

      return {{
        <div class="namedocs" {{idAttr}}>
          <span class="label">"option"</span>
          <pre class="signature hl lean block">{{x}}</pre>
          <div class="text">
            <p>"Default value: " <code class="hl lean inline">{{← defaultValue.toHtml}}</code></p>
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [highlightingStyle, docstringStyle]
  extraJs := [highlightingJs]

open Lean.Syntax in
instance : Quote NameSet where
  quote xs := mkCApp ``RBTree.fromList #[quote xs.toList, ⟨mkHole .missing⟩]

instance : ToJson NameSet where
  toJson xs := toJson (xs.toArray : Array Name)

instance : FromJson NameSet where
  fromJson? xs := do
    let arr ← fromJson? (α := Array Name) xs
    pure <| RBTree.fromArray arr _

open Lean.Elab.Tactic.Doc in
deriving instance ToJson for TacticDoc
open Lean.Elab.Tactic.Doc in
deriving instance FromJson for TacticDoc

open Lean.Elab.Tactic.Doc in
open Lean.Syntax in
instance : Quote TacticDoc where
  quote
    | .mk internalName userName tags docString extensionDocs =>
      mkCApp ``TacticDoc.mk #[quote internalName, quote userName, quote tags, quote docString, quote extensionDocs]

def Block.tactic (name : Lean.Elab.Tactic.Doc.TacticDoc) («show» : Option String) : Block where
  name := `Verso.Genre.Manual.tactic
  data := ToJson.toJson (name, «show»)

structure TacticDocsOptions where
  name : String ⊕ Name
  «show» : Option String

def TacticDocsOptions.parse [Monad m] [MonadError m] : ArgParse m TacticDocsOptions :=
  TacticDocsOptions.mk <$> .positional `name strOrName <*> .named `show .string true
where
  strOrName : ValDesc m (String ⊕ Name) := {
    description := m!"First token in tactic, or canonical parser name"
    get := fun
      | .name x => pure (.inr x.getId)
      | .str s => pure (.inl s.getString)
      | .num n => throwErrorAt n "Expected tactic name (either first token as string, or internal parser name)"
  }


open Lean Elab Term Parser Tactic Doc in
private def getTactic (name : String ⊕ Name) : TermElabM TacticDoc := do
  for t in ← allTacticDocs do
    if .inr t.internalName == name || .inl t.userName == name then
      return t
  let n : MessageData :=
    match name with
    | .inl x => x
    | .inr x => x
  throwError m!"Tactic not found: {n}"

open Lean Elab Term Parser Tactic Doc in
private def getTactic? (name : String ⊕ Name) : TermElabM (Option TacticDoc) := do
  for t in ← allTacticDocs do
    if .inr t.internalName == name || .inl t.userName == name then
      return some t
  return none

@[directive_expander tactic]
def tactic : DirectiveExpander
  | args, more => do
    let opts ← TacticDocsOptions.parse.run args
    let tactic ← getTactic opts.name
    if tactic.userName == tactic.internalName.toString && opts.show.isNone then
      throwError "No `show` option provided, but the tactic has no user-facing token name"
    let some mdAst := tactic.docString >>= MD4Lean.parse
      | throwError "Failed to parse docstring as Markdown"
    let contents ← mdAst.blocks.mapM (Markdown.blockFromMarkdown · Markdown.strongEmphHeaders)
    let userContents ← more.mapM elabBlock
    pure #[← ``(Verso.Doc.Block.other (Block.tactic $(quote tactic) $(quote opts.show)) #[$(contents ++ userContents),*])]

open Verso.Genre.Manual.Markdown in
open Lean Elab Term Parser Tactic Doc in
@[block_extension tactic]
def tactic.descr : BlockDescr where
  traverse id info _ := do
    let .ok (tactic, «show») := FromJson.fromJson? (α := TacticDoc × Option String) info
      | do logError "Failed to deserialize docstring data while traversing a tactic"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path <| show.getD tactic.userName
    Index.addEntry id {term := Doc.Inline.code <| show.getD tactic.userName}

    modify fun st => st.saveDomainObject `Verso.Manual.doc.tactic tactic.internalName.toString id

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (tactic, «show») := FromJson.fromJson? (α := TacticDoc × Option String) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize tactic data while generating HTML for a tactic"; pure .empty
      let x : Highlighted := .token ⟨.keyword tactic.internalName none tactic.docString, show.getD tactic.userName⟩

      let xref ← HtmlT.state
      let idAttr :=
        if let some (_, htmlId) := xref.externalTags[id]? then
          #[("id", htmlId)]
        else #[]

      return {{
        <div class="namedocs" {{idAttr}}>
          <span class="label">"tactic"</span>
          <pre class="signature hl lean block">{{← x.toHtml}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [highlightingStyle, docstringStyle]
  extraJs := [highlightingJs]


def Inline.tactic : Inline where
  name := `Verso.Genre.Manual.tacticInline

deriving instance Repr for NameSet
deriving instance Repr for Lean.Elab.Tactic.Doc.TacticDoc

@[role_expander tactic]
def tacticInline : RoleExpander
  | args, inlines => do
    let () ← ArgParse.done.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code{ $tac:str }) := arg
      | throwErrorAt arg "Expected code literal with the option name"
    let tacTok := tac.getString
    let tacName := tac.getString.toName
    let some tacticDoc := (← getTactic? (.inl tacTok)) <|> (← getTactic? (.inr tacName))
      | throwErrorAt tac "Didn't find tactic named {tac}"

    let hl : Highlighted := tacToken tacticDoc

    pure #[← `(Verso.Doc.Inline.other {Inline.tactic with data := ToJson.toJson $(quote hl)} #[Verso.Doc.Inline.code $(quote tacticDoc.userName)])]
where
  tacToken (t : Lean.Elab.Tactic.Doc.TacticDoc) : Highlighted :=
    .token ⟨.keyword t.internalName none t.docString, t.userName⟩

@[inline_extension tacticInline]
def tacticInline.descr : InlineDescr where
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle, docstringStyle]
  extraJs := [highlightingJs]
  toHtml :=
    open Verso.Output.Html Verso.Doc.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean tactic code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml "examples"

-- TODO implement a system upstream like the one for normal tactics
def Block.conv (name : Name) («show» : String) (docs? : Option String) : Block where
  name := `Verso.Genre.Manual.conv
  data := ToJson.toJson (name, «show», docs?)

structure ConvTacticDoc where
  name : Name
  docs? : Option String

open Lean Elab Term Parser Tactic Doc in
def getConvTactic (name : String ⊕ Name) : TermElabM ConvTacticDoc := do
  let .inr kind := name
    | throwError "Strings not yet supported here"
  let parserState := parserExtension.getState (← getEnv)
  let some convs := parserState.categories.find? `conv
    | throwError "Couldn't find conv tactic list"
  for k in convs.kinds do
    if kind.isSuffixOf k.1 then
      return ⟨kind, ← findDocString? (← getEnv) kind⟩
  throwError m!"Conv tactic not found: {kind}"

@[directive_expander conv]
def conv : DirectiveExpander
  | args, more => do
    let opts ← TacticDocsOptions.parse.run args
    let tactic ← getConvTactic opts.name
    let contents ← if let some d := tactic.docs? then
        let some mdAst := MD4Lean.parse d
          | throwError "Failed to parse docstring as Markdown"
        mdAst.blocks.mapM (Markdown.blockFromMarkdown · Markdown.strongEmphHeaders)
      else pure #[]
    let userContents ← more.mapM elabBlock
    let some toShow := opts.show
      | throwError "An explicit 'show' is mandatory for conv docs (for now)"
    pure #[← ``(Verso.Doc.Block.other (Block.conv $(quote tactic.name) $(quote toShow) $(quote tactic.docs?)) #[$(contents ++ userContents),*])]

open Verso.Genre.Manual.Markdown in
open Lean Elab Term Parser Tactic Doc in
@[block_extension conv]
def conv.descr : BlockDescr where
  traverse id info _ := do
    let .ok (name, «show», _docs?) := FromJson.fromJson? (α := Name × String × Option String) info
      | do logError "Failed to deserialize conv docstring data"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path <| name.toString
    Index.addEntry id {term := Doc.Inline.code <| «show»}

    modify fun st => st.saveDomainObject `Verso.Manual.doc.tactic.conv name.toString id

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (name, «show», docs?) := FromJson.fromJson? (α := Name × String × Option String) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize conv tactic data"; pure .empty
      let x : Highlighted := .token ⟨.keyword (some name) none docs?, «show»⟩

      let xref ← HtmlT.state
      let idAttr :=
        if let some (_, htmlId) := xref.externalTags[id]? then
          #[("id", htmlId)]
        else #[]

      return {{
        <div class="namedocs" {{idAttr}}>
          <span class="label">"conv tactic"</span>
          <pre class="signature hl lean block">{{← x.toHtml}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
          </div>
        </div>
      }}
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [highlightingStyle, docstringStyle]
  extraJs := [highlightingJs]

def Block.progress
    (namespaces exceptions : Array Name)
    (present : List (Name × List Name))
    (tactics : Array String) :
    Block where
  name := `Verso.Genre.Manual.Block.progress
  data := toJson (namespaces, exceptions, present, tactics)

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
    let allTactics := (← Elab.Tactic.Doc.allTacticDocs).map (·.internalName.toString)

    pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.progress $(quote namespaces.toArray) $(quote exceptions.toArray) $(quote present') $(quote allTactics)) #[])]
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

    let .ok ((namespaces : Array Name), (exceptions : Array Name), (present : List (Name × List Name)), (allTactics : Array String)) := fromJson? info
      | panic! "Can't deserialize progress bar state"

    let check : NameMap (List Name) := present.foldr (init := {}) (fun x z => z.insert x.1 <| x.2)

    let undocTactics ← allTactics.filterM fun un => do
      let st ← Doc.Html.HtmlT.state (genre := Manual)
      pure !(TraverseState.getDomainObject? st `Verso.Manual.doc.tactic un).isSome

    let tacticPercent := undocTactics.size.toFloat * 100.0 / allTactics.size.toFloat

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
        <dt>"Tactics"</dt>
        <dd>
          <details><summary><progress id="progress-tactics" value=s!"{100 - tacticPercent.toUInt8.toNat}" min="0" max="100"></progress><label for="progress-tactics">s!"Missing {tacticPercent}% ({undocTactics.size}/{allTactics.size})"</label></summary> {{ undocTactics.toList |> String.intercalate ", "}}</details>
        </dd>
      </dl>
    }}
  toTeX := some (fun _ _ _ _ _ => pure <| Output.TeX.text "Unsupported")
