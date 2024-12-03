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
import Verso.Doc.PointOfInterest

import SubVerso.Highlighting

import MD4Lean

open Lean hiding HashSet
open Std (HashSet)

open Verso.Doc.Elab.PartElabM
open Verso.Code
open Verso.ArgParse
open Verso.Code.Highlighted.WebAssets

open SubVerso.Highlighting

namespace Verso.Genre.Manual

namespace Block

namespace Docstring

deriving instance ToJson for BinderInfo
deriving instance FromJson for BinderInfo
deriving instance ToJson for DefinitionSafety
deriving instance FromJson for DefinitionSafety

private def nameString (x : Name) (showNamespace : Bool) :=
  if showNamespace then x.toString
  else
    match x with
    | .str _ s => s
    | _ => x.toString

open Lean.PrettyPrinter Delaborator in
def ppName (c : Name) (showUniverses := true) (showNamespace : Bool := true) (openDecls : List OpenDecl := []) : MetaM FormatWithInfos :=
  MonadWithReaderOf.withReader (fun (ρ : Core.Context) => {ρ with openDecls := ρ.openDecls ++ openDecls}) <|do
  let decl ← getConstInfo c
  let e := .const c (decl.levelParams.map mkLevelParam)
  let (stx, infos) ← withOptions (pp.universes.set · true |> (pp.fullNames.set · true)) <|
    delabCore e (delab := delabConst)
  -- The special-casing here is to allow the `showNamespace` setting to work. This is perhaps too
  -- big of a hammer...
  match stx with
    | `($x:ident.{$uni,*}) =>
      let unis : Format ← do
        if showUniverses then
          let us ← uni.getElems.toList.mapM (ppCategory `level ·.raw)
          pure <| ".{" ++ Format.joinSep us ", " ++ "}"
        else
          pure .nil

      return ⟨Std.Format.tag SubExpr.Pos.root (.text (nameString x.getId showNamespace)) ++ unis, infos⟩
    | `($x:ident) =>
      return ⟨Std.Format.tag SubExpr.Pos.root (Std.Format.text (nameString x.getId showNamespace)), infos⟩
    | _ =>
      return ⟨← ppTerm stx, infos⟩

open Lean.PrettyPrinter Delaborator in
def ppSignature (c : Name) (showNamespace : Bool := true) (openDecls : List OpenDecl := []) : MetaM FormatWithInfos :=
  MonadWithReaderOf.withReader (fun (ρ : Core.Context) => {ρ with openDecls := ρ.openDecls ++ openDecls}) <|do
  let decl ← getConstInfo c
  let e := .const c (decl.levelParams.map mkLevelParam)
  let (stx, infos) ← delabCore e (delab := delabConstWithSignature)
  match stx with
  | `(declSigWithId|$nameUniv $argsRet:declSig ) => do
    let mut doc : Std.Format := .nil
    match nameUniv with
    | `($x:ident.{$uni,*}) =>
      let unis : List Format ← uni.getElems.toList.mapM (ppCategory `level ·.raw)
      doc := Std.Format.text (nameString x.getId showNamespace) ++ ".{" ++ .joinSep unis ", " ++ "}"
    | `($x:ident) =>
      doc := Std.Format.text (nameString x.getId showNamespace)
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
        argDoc := argDoc ++ "(" ++ .nest 1 (.fill (.joinSep xs' .line))
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

structure DocName where
  name : Name
  hlName : Highlighted
  signature : Highlighted
  docstring? : Option String
deriving ToJson, FromJson, Repr

open Syntax (mkCApp) in
instance : Quote DocName where
  quote
    | {name, hlName, signature, docstring?} => mkCApp ``DocName.mk #[quote name, quote hlName, quote signature, quote docstring?]


structure FieldInfo where
  fieldName : Highlighted
  /--
  What is the path by which the field was inherited?
  [] if not inherited.
  -/
  fieldFrom : List DocName
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
    | .mk fieldName fieldFrom? type projFn subobject? binderInfo autoParam docString? =>
      mkCApp ``FieldInfo.mk #[quote fieldName, quote fieldFrom?, quote type, quote projFn, quote subobject?, quote binderInfo, quote autoParam, quote docString?]

structure ParentInfo where
  projFn : Name
  name : Name
  parent : Highlighted
  index : Nat
deriving ToJson, FromJson

open Syntax (mkCApp) in
instance : Quote ParentInfo where
  quote
    | .mk projFn name parent index => mkCApp ``ParentInfo.mk #[quote projFn, quote name, quote parent, quote index]

inductive DeclType where
  | structure (isClass : Bool) (constructor : DocName) (fieldNames : Array Name) (fieldInfo : Array FieldInfo) (parents : Array ParentInfo) (ancestors : Array Name)
  | def (safety : DefinitionSafety)
  | opaque (safety : DefinitionSafety)
  | inductive (constructors : Array DocName) (numArgs : Nat) (propOnly : Bool)
  | other
deriving ToJson, FromJson

open Syntax (mkCApp) in
instance : Quote DeclType where
  quote
    | .structure isClass ctor fields infos parents ancestors =>
      mkCApp ``DeclType.«structure» #[quote isClass, quote ctor, quote fields, quote infos, quote parents, quote ancestors]
    | .def safety => mkCApp ``DeclType.def #[quote safety]
    | .opaque safety => mkCApp ``DeclType.opaque #[quote safety]
    | .inductive ctors numArgs propOnly => mkCApp ``DeclType.inductive #[quote ctors, quote numArgs, quote propOnly]
    | .other => mkCApp ``DeclType.other #[]

def DeclType.label : DeclType → String
  | .structure false .. => "structure"
  | .structure true .. => "type class"
  | .def .safe => "def"
  | .def .unsafe => "unsafe def"
  | .def .partial => "partial def"
  | .opaque .unsafe => "unsafe opaque"
  | .opaque _ => "opaque"
  | .inductive _ _ false => "inductive type"
  | .inductive _ 0 true => "inductive proposition"
  | .inductive _ _ true => "inductive predicate"
  | other => ""

set_option pp.fullNames false in
#check List.nil

open Meta in
def DocName.ofName (c : Name) (showUniverses := true) (showNamespace := true) (openDecls : List OpenDecl := []) : MetaM DocName := do
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
      ppSignature c (showNamespace := showNamespace) (openDecls := openDecls)
    let ttSig := Lean.Widget.TaggedText.prettyTagged (w := 40) fmt
    let sig := Lean.Widget.tagCodeInfos ctx infos ttSig

    let ⟨fmt, infos⟩ ← withOptions (·.setBool `pp.tagAppFns true) <|
      ppName c (showUniverses := showUniverses) (showNamespace := showNamespace) (openDecls := openDecls)
    let ttName := Lean.Widget.TaggedText.prettyTagged (w := 40) fmt
    let name := Lean.Widget.tagCodeInfos ctx infos ttName

    pure ⟨c, ← renderTagged none name ⟨{}, false⟩, ← renderTagged none sig ⟨{}, false⟩, ← findDocString? env c⟩
  else
    pure ⟨c, .token ⟨.const c "" none false, c.toString⟩, Highlighted.seq #[], none⟩

partial def getStructurePathToBaseStructureAux (env : Environment) (baseStructName : Name) (structName : Name) (path : List Name) : Option (List Name) :=
  if baseStructName == structName then
    some path.reverse
  else
    if let some info := getStructureInfo? env structName then
      -- Prefer subobject projections
      (info.fieldInfo.findSome? fun field =>
        match field.subobject? with
        | none                  => none
        | some parentStructName => getStructurePathToBaseStructureAux env baseStructName parentStructName (parentStructName :: path))
      -- Otherwise, consider other parents
      <|> info.parentInfo.findSome? fun parent =>
        if parent.subobject then
          none
        else
          getStructurePathToBaseStructureAux env baseStructName parent.structName (parent.structName :: path)
    else none

/--
If `baseStructName` is an ancestor structure for `structName`, then return a sequence of projection functions
to go from `structName` to `baseStructName`. Returns `[]` if `baseStructName == structName`.
-/
def getStructurePathToBaseStructure? (env : Environment) (baseStructName : Name) (structName : Name) : Option (List Name) :=
  getStructurePathToBaseStructureAux env baseStructName structName []


open Meta in
def DeclType.ofName (c : Name) : MetaM DeclType := do
  let env ← getEnv
  let openDecls : List OpenDecl :=
    match c with
    | .str _ s => [.explicit c.getPrefix s.toName]
    | _ => []
  if let some info := env.find? c then
    match info with
    | .defnInfo di => return .def di.safety
    | .inductInfo ii =>
      if let some info := getStructureInfo? env c then
        let ctor := getStructureCtor env c
        let parentProjFns := getStructureParentInfo env c |>.map (·.projFn)
        let parents ←
          forallTelescopeReducing ii.type fun params _ =>
            withLocalDeclD `self (mkAppN (mkConst c (ii.levelParams.map mkLevelParam)) params) fun s => do
              let selfType ← inferType s >>= whnf
              let .const _structName us := selfType.getAppFn
                | pure #[]
              let params := selfType.getAppArgs

              parentProjFns.mapIdxM fun i parentProj => do
                let proj := mkApp (mkAppN (.const parentProj us) params) s
                let type ← inferType proj >>= instantiateMVars
                let projType ← withOptions (·.setInt `format.width 40 |>.setBool `pp.tagAppFns true) <| Widget.ppExprTagged type
                if let .const parentName _  := type.getAppFn then
                  pure ⟨parentProj, parentName, ← renderTagged none projType ⟨{}, false⟩, i⟩
                else
                  pure ⟨parentProj, .anonymous, ← renderTagged none projType ⟨{}, false⟩, i⟩
        let ancestors ← getAllParentStructures c
        let allFields := getStructureFieldsFlattened env c (includeSubobjectFields := true)
        let fieldInfo ←
          forallTelescopeReducing ii.type fun params _ =>
            withLocalDeclD `self (mkAppN (mkConst c (ii.levelParams.map mkLevelParam)) params) fun s =>
              allFields.mapM fun fieldName => do
                let proj ← mkProjection s fieldName
                let type ← inferType proj >>= instantiateMVars
                let type' ← withOptions (·.setInt `format.width 40 |>.setBool `pp.tagAppFns true) <| (Widget.ppExprTagged type)
                let projType ← withOptions (·.setInt `format.width 40 |>.setBool `pp.tagAppFns true) <| ppExpr type
                let fieldFrom? := findField? env c fieldName
                let fieldPath? := fieldFrom? >>= (getStructurePathToBaseStructure? env · c)
                let fieldFrom ← fieldPath?.getD [] |>.mapM (DocName.ofName (showUniverses := false))
                let subobject? := isSubobjectField? env (fieldFrom?.getD c) fieldName
                let fieldInfo? := getFieldInfo? env (fieldFrom?.getD c) fieldName

                let binderInfo := fieldInfo?.map (·.binderInfo) |>.getD BinderInfo.default
                let autoParam := fieldInfo?.map (·.autoParam?.isSome) |>.getD false

                if let some projFn := getProjFnForField? env c fieldName then
                  let docString? ← findDocString? env projFn
                  let fieldName' := Highlighted.token ⟨.const projFn projType.pretty docString? true, fieldName.toString⟩
                  pure { fieldName := fieldName', fieldFrom, type := ← renderTagged none type' ⟨{}, false⟩, subobject?,  projFn, binderInfo, autoParam, docString?}
                else
                  let fieldName' := Highlighted.token ⟨.unknown, fieldName.toString⟩
                  pure { fieldName := fieldName', fieldFrom, type := ← renderTagged none type' ⟨{}, false⟩, subobject?,  projFn := .anonymous, binderInfo, autoParam, docString? := none}
        return .structure (isClass env c) (← DocName.ofName (showNamespace := true) ctor.name) info.fieldNames fieldInfo parents ancestors

      else
        let ctors ← ii.ctors.mapM (DocName.ofName (showNamespace := false) (openDecls := openDecls))
        let t ← inferType <| .const c (ii.levelParams.map .param)
        let t' ← reduceAll t
        return .inductive ctors.toArray (ii.numIndices + ii.numParams) (isPred t')
    | .opaqueInfo oi => return .opaque (if oi.isUnsafe then .unsafe else .safe)
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
  padding-top: 1.5rem;
  margin-bottom: 1rem;
}

.namedocs .text {
  background-color: white;
  padding: 1.5rem;
  margin-top: 0.5rem;
}

.namedocs .text > pre {
  overflow-x: auto;
}

.namedocs .signature {
  font-family: var(--verso-code-font-family);
  font-size: larger;
  margin-top: 0 !important;
  margin-left: 1.5rem !important;
  margin-right: 1.5rem;
}

.namedocs .label {
  font-size: smaller;
  font-family: var(--verso-structure-font-family);
  position: absolute;
  right: 0.5rem;
  top: 0.5rem;
}

/* Sticking content into the right margin is not good on narrow screens,
   so move the label to the left to make space for the permalink widget. */

@media screen and (max-width: 700px) {
  .namedocs:has(.permalink-widget.block) .label {
    right: 1.5rem;
  }
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
.namedocs .methods td, .namedocs .fields td {
  vertical-align: top;
}
.namedocs .inheritance td {
  vertical-align: top;
  font-size: smaller;
  font-family: var(--verso-structure-font-family);
}
.namedocs .inheritance ol {
  display: inline-block;
  margin: 0;
  padding: 0;
}
.namedocs .inheritance ol li {
  list-style-type: none;
  display: inline-block;
}
.namedocs .inheritance ol li::after {
  content: " > "
}
.namedocs .inheritance ol li:last-child::after {
  content: "";
}

.namedocs .extends {
  display: inline;
  margin: 0;
  padding: 0;
}
.namedocs .extends li {
  list-style-type: none;
  display: inline-block;
  padding-right: 1rem;
}

.namedocs:has(input[data-parent-idx="0"]) tr[data-inherited-from="0"] {
  display: none;
}

.namedocs:has(input[data-parent-idx="0"]:checked) tr[data-inherited-from="0"] {
  display: table-row;
}
"# ++ Id.run do
  let mut str := ""
  for i in [0:50] do
    str := str ++ mkFilterRule i
  str
where
  mkFilterRule (i : Nat) : String :=
    ".namedocs:has(input[data-parent-idx=\"" ++ toString i ++ "\"]) tr[data-inherited-from=\"" ++ toString i ++ "\"] {
  display: none;
}
.namedocs:has(input[data-parent-idx=\"" ++ toString i ++ "\"]:checked) tr[data-inherited-from=\"" ++ toString i ++"\"] {
  display: table-row;
}

"


open Verso.Genre.Manual.Markdown in
@[block_extension Block.docstring]
def docstring.descr : BlockDescr where
  init st := st
    |>.setDomainTitle docstringDomain "Lean constant reference"
    |>.setDomainDescription docstringDomain "Documentation for Lean constants"

  traverse id info _ := do
    let .ok (name, declType, _signature) := FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Option Highlighted) info
      | do logError "Failed to deserialize docstring data"; pure none

    match declType with
    | .structure true ctor fields fieldInfos _parents _ancestors =>
        saveRef id ctor.name <| some <| Doc.Inline.concat #[Doc.Inline.text "Instance constructor of ", Doc.Inline.code name.toString]

        for (f, i) in fields.zip fieldInfos do
          saveRef id i.projFn
            (some <| Doc.Inline.concat #[Doc.Inline.code i.projFn.toString, Doc.Inline.text " (class method)"])
            (showName := some f.toString)
    | .structure false ctor fields fieldInfos _parents _ancestors =>
        saveRef id ctor.name <| some <| Doc.Inline.concat #[Doc.Inline.text "Constructor of ", Doc.Inline.code name.toString]

        for (f, i) in fields.zip fieldInfos do
          saveRef id i.projFn
            (some <| Doc.Inline.concat #[Doc.Inline.code i.projFn.toString, Doc.Inline.text " (structure field)"])
            (showName := some f.toString)
    | .inductive ctors _ _ =>
      for c in ctors do
        saveRef id c.name <| some <| Doc.Inline.concat #[Doc.Inline.text "Constructor of ", Doc.Inline.code name.toString]
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
    modify fun st => st.saveDomainObject docstringDomain name.toString id
    saveRef id name none
    if name.getPrefix != .anonymous then
      Index.addEntry id {term := Doc.Inline.code name.getString!, subterm := some <| Doc.Inline.code name.toString}

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok (name, declType, signature) := FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Option Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring data while generating HTML"; pure .empty
      let x : Html := Html.text true <| Name.toString name
      let sig : Html ← Option.map Highlighted.toHtml signature |>.getD (pure {{ {{x}} }})

      let xref ← state
      let idAttr := xref.htmlId id

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
          <span class="label">{{declType.label}}</span>
          <pre class="signature hl lean block">{{sig}}</pre>
          <div class="text">
            {{← contents.mapM goB}}
            {{← moreDeclHtml name goB declType}}
          </div>
        </div>
      }}
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [highlightingStyle, docstringStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
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
  moreDeclHtml name (goB)
    | .structure isClass ctor _ infos parents ancestors =>
      open Verso.Doc.Html in
      open Verso.Output Html in do
      let parentRow ← do
        if parents.isEmpty then pure .empty
        else pure {{
            <h1>"Extends"</h1>
            <ul class="extends">
              {{← parents.mapM fun parent => do
                let filterId := s!"{parent.index}-{parent.name}-{name}"
                pure {{
                  <li>
                    <input type="checkbox" id={{filterId}} checked="checked" data-parent-idx={{toString parent.index}}/>
                    <label for={{filterId}}><code class="hl lean inline">{{← parent.parent.toHtml}}</code></label>
                  </li>}}
              }}
            </ul>
          }}
      let ctorRow ←
        if isPrivateName ctor.name then
          pure Html.empty
        else pure {{
            <h1>{{if isClass then "Instance Constructor" else "Constructor"}}</h1>
            <table>
              <tr><td><code class="hl lean inline">{{← ctor.hlName.toHtml}}</code></td></tr>
              {{ ← if let some d := ctor.docstring? then do
                  pure {{<tr><td>{{← md2html goB d}}</td></tr>}}
                else pure Html.empty
              }}
            </table>
          }}
      let infos := infos.filter (·.subobject?.isNone)
      pure {{
        {{ ctorRow }}
        {{ parentRow }}
        <h1>{{if isClass then "Methods" else "Fields"}}</h1>
        <table class={{if isClass then "methods" else "fields"}}>
          {{← infos.mapM fun i => do
            let inheritedAttrVal : Option String :=
              i.fieldFrom.head?.bind (fun n => parents.findIdx? (·.name == n.name)) |>.map toString
            let inheritedAttr : Array (String × String) := inheritedAttrVal.map (fun i => #[("data-inherited-from", i)]) |>.getD #[]

            let inheritedRow : Html ←
              if i.fieldFrom.isEmpty then pure Html.empty
              else
                  pure {{
                    <tr class="inheritance" {{inheritedAttr}}>
                      <td colspan="2"></td>
                      <td>
                        "Inherited from "
                        <ol>
                        {{ ← i.fieldFrom.mapM fun p => do
                            pure {{<li><code class="hl lean inline">{{ ← p.hlName.toHtml }}</code></li>}}
                        }}
                        </ol>
                      </td>
                    </tr>
                  }}

            let docRow : Html ←
              if let some doc := i.docString? then do
                let doc ← md2html goB doc
                pure {{
                  <tr class="doc" {{inheritedAttr}}>
                    <td colspan="2"></td>
                    <td> {{ doc }}
                    </td>
                  </tr>
                }}
                else
                  pure Html.empty

             pure <| {{
              <tr {{inheritedAttr}}>
                <td><code class="hl lean inline">{{← i.fieldName.toHtml}}</code></td>
                <td><code>" : "</code></td>
                <td><code class="hl lean inline">{{← i.type.toHtml }}</code></td>
              </tr>
            }} ++ inheritedRow ++ docRow
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

  saveRef
      (id : InternalId) (name : Name)
      (subterm : Option (Doc.Inline Manual))
      (showName : Option String := none) :
      ReaderT TraverseContext (StateT TraverseState IO) Unit := do
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name.toString
    Index.addEntry id {
      term := Doc.Inline.code (showName.getD name.toString),
      subterm := subterm
    }
    modify (·.saveDomainObject docstringDomain name.toString id)


open Verso.Doc.Elab

@[block_role_expander docstring]
def docstring : BlockRoleExpander
  | args, #[] => do
    match args with
    | #[.anon (.name x)] =>
      let name ← Elab.realizeGlobalConstNoOverloadWithInfo x
      Doc.PointOfInterest.save x name.toString
      let blockStx ← match ← Lean.findDocString? (← getEnv) name with
      | none => logWarningAt x m!"No docs found for '{x}'"; pure #[]
      | some docs =>
        let some ast := MD4Lean.parse docs
          | throwErrorAt x "Failed to parse docstring as Markdown"
        ast.blocks.mapM (Markdown.blockFromMarkdown · Markdown.strongEmphHeaders)

      if Lean.Linter.isDeprecated (← getEnv) name then
        logInfoAt x m!"'{x}' is deprecated"

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
      let signature ← some <$> renderTagged none sig ⟨{}, false⟩
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
        ⟨.const ``true (sig_for% true) (some <| docs_for% true) false, "true"⟩
      else
        ⟨.const ``false (sig_for% false) (some <| docs_for% false) false, "false"⟩
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
    Doc.PointOfInterest.save x optDecl.declName.toString
    let some mdAst := MD4Lean.parse optDecl.descr
      | throwErrorAt x "Failed to parse docstring as Markdown"
    let contents ← mdAst.blocks.mapM (Markdown.blockFromMarkdown · Markdown.strongEmphHeaders)
    pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.optionDocs $(quote x.getId) $(quote <| highlightDataValue optDecl.defValue)) #[$contents,*])]

  | _, more => throwErrorAt more[0]! "Unexpected block argument"

open Verso.Genre.Manual.Markdown in
@[block_extension optionDocs]
def optionDocs.descr : BlockDescr where
  init st := st
    |>.setDomainTitle optionDomain "Compiler options"

  traverse id info _ := do
    let .ok (name, _defaultValue) := FromJson.fromJson? (α := Name × Highlighted) info
      | do logError "Failed to deserialize docstring data while traversing an option"; pure none

    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path name.toString
    Index.addEntry id {term := Doc.Inline.code name.toString}
    if name.getPrefix != .anonymous then
      Index.addEntry id {term := Doc.Inline.code name.getString!, subterm := some <| Doc.Inline.code name.toString}

    modify fun st => st.saveDomainObject optionDomain name.toString id

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (name, defaultValue) := FromJson.fromJson? (α := Name × Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring data while generating HTML for an option"; pure .empty
      let x : Html := Html.text true <| Name.toString name

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
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
    Doc.PointOfInterest.save (← getRef) tactic.userName
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
  init st := st
    |>.setDomainTitle tacticDomain "Tactic Documentation"
    |>.setDomainDescription tacticDomain "Detailed descriptions of tactics"

  traverse id info _ := do
    let .ok (tactic, «show») := FromJson.fromJson? (α := TacticDoc × Option String) info
      | do logError "Failed to deserialize docstring data while traversing a tactic"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path <| show.getD tactic.userName
    Index.addEntry id {term := Doc.Inline.code <| show.getD tactic.userName}

    modify fun st => st.saveDomainObject tacticDomain tactic.internalName.toString id

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (tactic, «show») := FromJson.fromJson? (α := TacticDoc × Option String) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize tactic data while generating HTML for a tactic"; pure .empty
      let x : Highlighted := .token ⟨.keyword tactic.internalName none tactic.docString, show.getD tactic.userName⟩

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
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

structure TacticInlineOptions where
  «show» : Option String

def TacticInlineOptions.parse [Monad m] [MonadError m] : ArgParse m TacticInlineOptions :=
  TacticInlineOptions.mk <$> .named `show .string true

@[role_expander tactic]
def tacticInline : RoleExpander
  | args, inlines => do
    let {«show»} ← TacticInlineOptions.parse.run args
    let #[arg] := inlines
      | throwError "Expected exactly one argument"
    let `(inline|code{ $tac:str }) := arg
      | throwErrorAt arg "Expected code literal with the tactic name"
    let tacTok := tac.getString
    let tacName := tac.getString.toName
    let some tacticDoc := (← getTactic? (.inl tacTok)) <|> (← getTactic? (.inr tacName))
      | throwErrorAt tac "Didn't find tactic named {tac}"

    let hl : Highlighted := tacToken tacticDoc «show»

    pure #[← `(Verso.Doc.Inline.other {Inline.tactic with data := ToJson.toJson $(quote hl)} #[Verso.Doc.Inline.code $(quote tacticDoc.userName)])]
where
  tacToken (t : Lean.Elab.Tactic.Doc.TacticDoc) (overrideStr : Option String) : Highlighted :=
    .token ⟨.keyword t.internalName none t.docString, overrideStr.getD t.userName⟩


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
  for ⟨k, ()⟩ in convs.kinds do
    if kind.isSuffixOf k then
      return ⟨k, ← findDocString? (← getEnv) k⟩
  throwError m!"Conv tactic not found: {kind}"

@[directive_expander conv]
def conv : DirectiveExpander
  | args, more => do
    let opts ← TacticDocsOptions.parse.run args
    let tactic ← getConvTactic opts.name
    Doc.PointOfInterest.save (← getRef) tactic.name.toString
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
  init st := st
    |>.setDomainTitle convDomain "Conversion Tactics" |>.setDomainDescription convDomain "Tatics for performing targeted rewriting of subterms"

  traverse id info _ := do
    let .ok (name, «show», _docs?) := FromJson.fromJson? (α := Name × String × Option String) info
      | do logError "Failed to deserialize conv docstring data"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path <| name.toString
    Index.addEntry id {term := Doc.Inline.code <| «show»}

    modify fun st => st.saveDomainObject convDomain name.toString id

    pure none
  toHtml := some <| fun _goI goB id info contents =>
    open Verso.Doc.Html in
    open Verso.Output Html in do
      let .ok (name, «show», docs?) := FromJson.fromJson? (α := Name × String × Option String) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize conv tactic data"; pure .empty
      let x : Highlighted := .token ⟨.keyword (some name) none docs?, «show»⟩

      let xref ← HtmlT.state
      let idAttr := xref.htmlId id

      return {{
        <div class="namedocs" {{idAttr}}>
          {{permalink id xref false}}
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
    (tactics : Array Name) :
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
      if ignore (← getEnv) x then continue
      if exceptions.contains x then continue
      match info with
      | .thmInfo _ => continue -- don't document theorems
      | .ctorInfo _ => continue -- constructors are documented as children of their types
      | _ => pure ()
      if ← Meta.isInstance x then continue
      let mut ns := x
      while !ns.isAnonymous && !(ns.getString!.get 0 |>.isUpper) do
        ns := ns.getPrefix
      if let some v := present.find? ns then
        present := present.insert ns (v.insert x)
    let present' := present.toList.map (fun x => (x.1, x.2.toList))
    let allTactics : Array Name := (← Elab.Tactic.Doc.allTacticDocs).map (fun t => t.internalName)

    pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.progress $(quote namespaces.toArray) $(quote exceptions.toArray) $(quote present') $(quote allTactics)) #[])]
where
  ignore (env : Environment) (x : Name) : Bool :=
    isPrivateName x ||
    isAuxRecursor env x ||
    isNoConfusion env x ||
    isRecCore env x ||
    env.isProjectionFn x ||
    Lean.Linter.isDeprecated env x ||
    x.hasNum ||
    x.isInternalOrNum ||
    (`noConfusionType).isSuffixOf x ||
    let str := x.getString!
    str ∈ ["sizeOf_spec", "sizeOf_eq", "brecOn", "ind", "ofNat_toCtorIdx", "inj", "injEq", "induct"] ||
    "proof_".isPrefixOf str && (str.drop 6).all (·.isDigit) ||
    "match_".isPrefixOf str && (str.drop 6).all (·.isDigit) ||
    "eq_".isPrefixOf str && (str.drop 3).all (·.isDigit)

@[block_extension Block.progress]
def progress.descr : BlockDescr where
  traverse _ _ _ := pure none
  toHtml := some fun _ _ _ info _blocks => open Output.Html in do
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

    let .ok ((namespaces : Array Name), (exceptions : Array Name), (present : List (Name × List Name)), (allTactics : Array Name)) := fromJson? info
      | panic! "Can't deserialize progress bar state"

    let check : NameMap (List Name) := present.foldr (init := {}) (fun x z => z.insert x.1 <| x.2)

    let undocTactics ← allTactics.filterM fun tacticName => do
      let st ← Doc.Html.HtmlT.state (genre := Manual)
      pure <| (TraverseState.getDomainObject? st tacticDomain tacticName.toString).isNone && tacticName ∉ exceptions

    let tacticPercent := undocTactics.size.toFloat * 100.0 / allTactics.size.toFloat

    return {{
      <dl>
        {{namespaces.map fun ns =>
          let wanted := check.findD ns []
          let notDocumented := wanted.filter (!ok.contains ·)
          let percent := notDocumented.length.toFloat * 100.0 / wanted.length.toFloat
          {{
            <dt><code>{{ns.toString}}</code></dt>
            <dd>
              <details>
                <summary>
                  <progress id=s!"prog-{ns}" value=s!"{100 - percent.toUInt8.toNat}" min="0" max="100"></progress>
                  <label for=s!"prog-ns">s!"Missing {percent}%"</label>
                </summary>
                {{notDocumented |>.map (·.toString) |> String.intercalate ", " }}
                <pre>
                  {{ notDocumented.map ("{docstring " ++ ·.toString ++ "}\n") |> String.join }}
                </pre>
                <pre>
                  "```exceptions\n"
                  {{ notDocumented.map (·.toString ++ "\n") |> String.join }}
                  "```\n"
                </pre>
              </details>
            </dd>
          }}
        }}
        <dt>"Tactics"</dt>
        <dd>
          <details>
            <summary>
              <progress id="progress-tactics" value=s!"{100 - tacticPercent.toUInt8.toNat}" min="0" max="100"></progress>
              <label for="progress-tactics">s!"Missing {tacticPercent}% ({undocTactics.size}/{allTactics.size})"</label>
            </summary>
            {{ undocTactics.map (·.toString) |>.toList |> String.intercalate ", " }}
            <pre>
              {{ undocTactics.map ("{docstring " ++ ·.toString ++ "}\n") |>.toList |> String.join }}
            </pre>
            <pre>
              "```exceptions\n"
              {{ undocTactics.map (·.toString ++ "\n") |>.toList |> String.join }}
              "```\n"
            </pre>
          </details>
        </dd>
      </dl>
    }}
  toTeX := some (fun _ _ _ _ _ => pure <| Output.TeX.text "Unsupported")
