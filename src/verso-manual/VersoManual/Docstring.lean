/-
Copyright (c) 2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Data.HashSet

import VersoManual.Basic
import VersoManual.HighlightedCode
import VersoManual.Index
import VersoManual.Markdown
import VersoManual.Docstring.Config
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

def stripNS : Syntax → Syntax
  | .ident info substr x pre => .ident info substr x.getString!.toName pre
  | .node info kind args => .node info kind (args.map stripNS)
  | other => other

def stripInfo : Syntax → Syntax
  | .ident _ substr x pre => .ident .none substr x.getString!.toName pre
  | .node _ kind args => .node .none kind (args.map stripInfo)
  | .atom _ x => .atom .none x
  | .missing => .missing


/--
Strip an explicit `_root_` from each identifier, to work around configuration problems in the pretty
printer
-/
def stripRootPrefix (stx : Syntax) : Syntax :=
  stx.rewriteBottomUp fun
  | .ident info substr x pre => .ident info substr (x.replacePrefix `_root_ .anonymous) pre
  | s => s

open Lean.PrettyPrinter Delaborator in
/--
Postprocess Lean's own `ppSignature` to remove the namespace (used for constructors) and any
`_root_` prefixes that have snuck in. The latter is not strictly correctness preserving, but it's an
expedient hack. It also removes the info from the constant's name if requested, to avoid unwanted
linking from a definition site to itself.
-/
def ppSignature (c : Name) (showNamespace : Bool := true) (openDecls : List OpenDecl := []) (constantInfo : Bool := true) : MetaM FormatWithInfos :=
  withTheReader Core.Context (fun ρ => {ρ with openDecls := ρ.openDecls ++ openDecls}) <| do
  let decl ← getConstInfo c
  let e := .const c (decl.levelParams.map mkLevelParam)
  let (stx, infos) ← delabCore e (delab := delabConstWithSignature)
  let stx : Syntax ←
    stripRootPrefix <$>
    if showNamespace then pure stx.raw
    else
      match stx with
      | `(declSigWithId|$nameUniv $argsRet:declSig ) => do
        `(declSigWithId|$(⟨stripNS nameUniv⟩) $argsRet) <&> (·.raw)
      | _ => pure stx.raw
  let stx : Syntax ←
    if constantInfo then pure stx
    else
      match stx with
      | `(declSigWithId|$nameUniv $argsRet:declSig ) => do
        `(declSigWithId|$(⟨stripInfo nameUniv⟩) $argsRet) <&> (·.raw)
      | _ => pure stx

  return ⟨← ppTerm ⟨stx⟩, infos⟩  -- HACK: not a term


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
open BinderInfo in
instance : Quote BinderInfo where
  quote
    | .default => mkCApp ``BinderInfo.default #[]
    | .implicit => mkCApp ``implicit #[]
    | .instImplicit => mkCApp ``instImplicit #[]
    | .strictImplicit => mkCApp ``strictImplicit #[]

open Syntax (mkCApp) in
instance : Quote FieldInfo where
  quote
    | ⟨fieldName, fieldFrom, type, projFn, subobject?, binderInfo, autoParam, docString⟩ =>
      mkCApp ``FieldInfo.mk #[quote fieldName, quote fieldFrom, quote type, quote projFn, quote subobject?, quote binderInfo, quote autoParam, quote docString]


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

deriving instance Repr for OpenDecl

open Meta in
def DocName.ofName (c : Name) (ppWidth : Nat := 40) (showUniverses := true) (showNamespace := true) (constantInfo := false) (openDecls : List OpenDecl := []) : MetaM DocName := do
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

    let sig := Lean.Widget.tagCodeInfos ctx infos ttSig

    let ⟨fmt, infos⟩ ← withOptions (·.setBool `pp.tagAppFns true) <|
      ppName c (showUniverses := showUniverses) (showNamespace := showNamespace) (openDecls := openDecls)
    let ttName := Lean.Widget.TaggedText.prettyTagged (w := ppWidth) fmt
    let name := Lean.Widget.tagCodeInfos ctx infos ttName

    pure { name := c, hlName := (← renderTagged none name ⟨{}, false⟩), signature := (← renderTagged none sig ⟨{}, false⟩), docstring? := (← findDocString? env c) }
  else
    pure { name := c, hlName := .token ⟨.const c "" none false, c.toString⟩, signature := Highlighted.seq #[], docstring? := none }

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
        let ctors ← ii.ctors.mapM (DocName.ofName (ppWidth := 60) (showNamespace := false) (openDecls := openDecls))
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

def docstringSection (header : String) : Block where
  name := `Verso.Genre.Manual.Block.docstringSection
  data := ToJson.toJson header

def internalSignature (name : Highlighted) (signature : Option Highlighted) : Block where
  name := `Verso.Genre.Manual.Block.internalSignature
  data := ToJson.toJson (name, signature)

def fieldSignature (name : Highlighted) (signature : Highlighted) (inheritedFrom : Option Nat) (inheritance : Array Highlighted) : Block where
  name := `Verso.Genre.Manual.Block.fieldSignature
  data := ToJson.toJson (name, signature, inheritedFrom, inheritance)

def inheritance (within : Name) (inheritance : Array Block.Docstring.ParentInfo) : Block where
  name := `Verso.Genre.Manual.Block.inheritance
  data := ToJson.toJson (within, inheritance)

def constructorSignature (signature : Highlighted) : Block where
  name := `Verso.Genre.Manual.Block.constructorSignature
  data := ToJson.toJson signature

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

.namedocs > .text .constructor {
  padding-left: 0.5rem;
  padding-top: 0;
  padding-right: 0;
  padding-bottom: 0;
  margin-top: 0.5rem;
  margin-bottom: 1.5rem;
}

.namedocs > .text .constructor::before {
  content: '| ';
  display: block;
  font-family: var(--verso-code-font-family);
  font-weight: bold;
  float: left;
  width: 0.5rem;
  white-space: pre;
}

.namedocs > .text .constructor .name-and-type {
  padding-left: 0.5rem;
  float: left;
  margin-top: 0;
}
.namedocs > .text .constructor .docs {
  clear: both;
  padding-left: 1rem;
}


.namedocs .methods td, .namedocs .fields td {
  vertical-align: top;
}
.namedocs .inheritance {
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
}

.namedocs .extends li label {
  padding-right: 1rem;
}

.namedocs .subdocs .name-and-type {
  font-size: 1rem;
  margin-left: 0;
  margin-top: 0;
  margin-right: 0;
  margin-bottom: 0.5rem;
}

.namedocs .subdocs .docs {
  margin-left: 1.5rem;
  margin-top: 0;
  margin-right: 0;
  margin-bottom: 0.5rem;
}

.namedocs:has(input[data-parent-idx]) [data-inherited-from] {
  transition-property: opacity, display;
  transition-duration: 0.4s;
  transition-behavior: allow-discrete;
  @starting-style { opacity: 0 !important; }
}

#this-page-items .tactic-name { font-weight: bold; }
"# ++ Id.run do
  let mut str := ""
  for i in [0:50] do
    str := str ++ mkFilterRule i
  str
where
  mkFilterRule (i : Nat) : String :=
    ".namedocs:has(input[data-parent-idx=\"" ++ toString i ++ "\"]) [data-inherited-from=\"" ++ toString i ++ "\"] {
  display: none;
  opacity: 0;
}
.namedocs:has(input[data-parent-idx=\"" ++ toString i ++ "\"]:checked) [data-inherited-from=\"" ++ toString i ++"\"] {
  display: table-row;
  transform: none;
  opacity: 1;
}
.namedocs:has(input[data-parent-idx=\"" ++ toString i ++ "\"]:checked):has(.inheritance[data-inherited-from=\"" ++ toString i ++"\"]:hover) [data-inherited-from]:not([data-inherited-from=\"" ++ toString i ++"\"]) {
  opacity: 0.5;
}
"


@[block_extension Block.docstringSection]
def docstringSection.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id _info contents => contents.mapM goB
  toHtml := some fun _goI goB _id info contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok header := FromJson.fromJson? (α := String) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring section data while generating HTML"; pure .empty
      return {{
        <h1>{{header}}</h1>
        {{← contents.mapM goB}}
      }}

@[block_extension Block.internalSignature]
def internalSignature.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id _ contents => contents.mapM goB -- TODO
  toHtml := some fun _goI goB _id info contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok (name, signature) := FromJson.fromJson? (α := Highlighted × Option Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring section data while generating HTML"; pure .empty
      return {{
        <section class="subdocs">
          <pre class="name-and-type hl lean">
            {{← name.toHtml}}
            {{← if let some s := signature then do
                  pure {{" : " {{← s.toHtml}} }}
                else pure .empty}}
          </pre>
          <div class="docs">
            {{← contents.mapM goB}}
          </div>
        </section>
      }}



@[block_extension Block.inheritance]
def inheritance.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id _ contents => contents.mapM goB -- TODO
  toHtml := some fun _goI _goB _id info _contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok (name, parents) := FromJson.fromJson? (α := Name × Array Block.Docstring.ParentInfo) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring structure inheritance data while generating HTML"; pure .empty
      let parentRow ← do
        if parents.isEmpty then pure .empty
        else pure {{
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


@[block_extension Block.fieldSignature]
def fieldSignature.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id _ contents => contents.mapM goB -- TODO
  toHtml := some fun _goI goB _id info contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok (name, signature, inheritedFrom, parents) := FromJson.fromJson? (α := Highlighted × Highlighted × Option Nat × Array Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring section data while generating HTML"; pure .empty
      let inheritedAttr : Array (String × String) :=
        inheritedFrom.map (fun i => #[("data-inherited-from", toString i)]) |>.getD #[]
      return {{
        <section class="subdocs" {{inheritedAttr}}>
          <pre class="name-and-type hl lean">
            {{← name.toHtml}} " : " {{ ← signature.toHtml}}
          </pre>
          {{← if inheritedFrom.isSome then do
              pure {{
                <div class="inheritance docs" {{inheritedAttr}}>
                  "Inherited from "
                  <ol>
                  {{ ← parents.mapM fun p => do
                      pure {{<li><code class="hl lean inline">{{ ← p.toHtml }}</code></li>}}
                  }}
                  </ol>
                </div>}}
            else pure .empty}}
          <div class="docs">
            {{← contents.mapM goB}}
          </div>
        </section>
      }}

@[block_extension Block.constructorSignature]
def constructorSignature.descr : BlockDescr where
  traverse _ _ _ := pure none
  toTeX := some fun _goI goB _id _ contents => contents.mapM goB -- TODO
  toHtml := some fun _goI goB _id info contents =>
    open Verso.Doc.Html HtmlT in
    open Verso.Output Html in do
      let .ok signature := FromJson.fromJson? (α := Highlighted) info
        | do Verso.Doc.Html.HtmlT.logError "Failed to deserialize docstring section data while generating HTML"; pure .empty

      return {{
        <div class="constructor">
          <pre class="name-and-type hl lean">{{← signature.toHtml}}</pre>
          <div class="docs">
            {{← contents.mapM goB}}
          </div>
        </div>
      }}

open Verso.Genre.Manual.Markdown in
@[block_extension Block.docstring]
def docstring.descr : BlockDescr := withHighlighting {
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
          </div>
        </div>
      }}

  localContentItem := fun _id info _contents => open Verso.Output.Html in do
    let .ok (name, _declType, _signature) := FromJson.fromJson? (α := Name × Block.Docstring.DeclType × Option Highlighted) info
      | failure
    pure #[{{<code>{{name.getString!}}</code>}}]


  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [docstringStyle]
}
where
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

def leanFromMarkdown := ()

def Inline.leanFromMarkdown (hls : Highlighted) : Inline where
  name := ``Verso.Genre.Manual.leanFromMarkdown
  data := ToJson.toJson hls

def Block.leanFromMarkdown (hls : Highlighted) : Block where
  name := ``Verso.Genre.Manual.leanFromMarkdown
  data := ToJson.toJson hls


@[inline_extension leanFromMarkdown]
def leanFromMarkdown.inlinedescr : InlineDescr := withHighlighting {
  traverse _id _data _ := pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  toHtml :=
    open Verso.Output Html in
    open Verso.Doc.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? (α := Highlighted) data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering inline HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml "docstring-examples"
}

@[block_extension leanFromMarkdown]
def leanFromMarkdown.blockdescr : BlockDescr := withHighlighting {
  traverse _id _data _ := pure none
  toTeX :=
    some <| fun goI goB _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← goB b, .raw "\n"]
  toHtml :=
    open Verso.Output Html in
    open Verso.Doc.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? (α := Highlighted) data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering inline HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.blockHtml "docstring-examples"
}

open Lean Elab Term in
def tryElabCodeTermWith (mk : Highlighted → String → DocElabM α) (str : String) (ignoreElabErrors := false) (identOnly := false) : DocElabM α := do
  let loc := (← getRef).getPos?.map (← getFileMap).utf8PosToLspPos
  let src :=
    if let some ⟨line, col⟩ := loc then s!"<docstring at {← getFileName}:{line}:{col}>"
    else s!"<docstring at {← getFileName} (unknown line)>"
  match Parser.runParserCategory (← getEnv) `term str src with
  | .error e => throw (.error (← getRef) e)
  | .ok stx => DocElabM.withFileMap (.ofString str) <| do
    if stx.isIdent && (← readThe Term.Context).autoBoundImplicit then
      throwError m!"Didn't elaborate {stx} as term to avoid spurious auto-implicits"
    if identOnly && !stx.isIdent then
      throwError m!"Didn't elaborate {stx} as term because only identifiers are wanted here"
    let (newMsgs, tree, e) ← do
      let initMsgs ← Core.getMessageLog
      try
        Core.resetMessageLog
        -- TODO open decls/current namespace
        let (tree', e') ← do
          let e ← Elab.Term.elabTerm (catchExPostpone := true) stx none
          Term.synthesizeSyntheticMVarsNoPostponing
          let e' ← Term.levelMVarToParam (← instantiateMVars e)
          Term.synthesizeSyntheticMVarsNoPostponing
          let e' ← instantiateMVars e'
          let ctx := PartialContextInfo.commandCtx {
            env := ← getEnv, fileMap := ← getFileMap, mctx := ← getMCtx, currNamespace := ← getCurrNamespace,
            openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
          }
          pure (InfoTree.context ctx (.node (Info.ofCommandInfo ⟨`Verso.Genre.Manual.docstring, (← getRef)⟩) (← getInfoState).trees), e')
        pure (← Core.getMessageLog, tree', e')
      finally
        Core.setMessageLog initMsgs
    if newMsgs.hasErrors && !ignoreElabErrors then
      for msg in newMsgs.errorsToWarnings.toArray do
        logMessage msg
      throwError m!"Didn't elaborate {stx} as term"

    let hls ← highlight stx #[] (PersistentArray.empty.push tree)
    mk hls str


declare_syntax_cat doc_metavar
scoped syntax (name := docMetavar) term ":" term : doc_metavar


open Lean Elab Term in
def tryElabCodeMetavarTermWith (mk : Highlighted → String → DocElabM α) (str : String) (ignoreElabErrors := false) : DocElabM α := do
  let loc := (← getRef).getPos?.map (← getFileMap).utf8PosToLspPos
  let src :=
    if let some ⟨line, col⟩ := loc then s!"<docstring at {← getFileName}:{line}:{col}>"
    else s!"<docstring at {← getFileName} (unknown line)>"
  match Parser.runParserCategory (← getEnv) `doc_metavar str src with
  | .error e => throw (.error (← getRef) e)
  | .ok stx => DocElabM.withFileMap (.ofString str) <| do
    if let `(doc_metavar|$pat:term : $ty:term) := stx then
      let (newMsgs, tree, e') ← show TermElabM _ from do
        let initMsgs ← Core.getMessageLog
        try
          Core.resetMessageLog
          -- TODO open decls/current namespace
          let (tree', e') ← do
            let stx' : Term ← `(($pat : $ty))
            let e ← withReader ({· with autoBoundImplicit := true}) <| elabTerm stx' none
            Term.synthesizeSyntheticMVarsNoPostponing
            let e' ← Term.levelMVarToParam (← instantiateMVars e)
            Term.synthesizeSyntheticMVarsNoPostponing
            let e' ← instantiateMVars e'
            let ctx := PartialContextInfo.commandCtx {
              env := ← getEnv, fileMap := ← getFileMap, mctx := ← getMCtx, currNamespace := ← getCurrNamespace,
              openDecls := ← getOpenDecls, options := ← getOptions, ngen := ← getNGen
            }
            pure (InfoTree.context ctx (.node (Info.ofCommandInfo ⟨`Verso.Genre.Manual.docstring, stx⟩) (← getInfoState).trees), e')
          pure (← Core.getMessageLog, tree', e')
        finally
          Core.setMessageLog initMsgs
      if newMsgs.hasErrors && !ignoreElabErrors then
        for msg in newMsgs.errorsToWarnings.toArray do
          logMessage msg
        throwError m!"Didn't elaborate {pat} : {ty} as term"

      let hls ← highlight stx #[] (PersistentArray.empty.push tree)
      mk hls str
    else
      throwError "Not a doc metavar: {stx}"

open Lean Elab Term in
def tryElabInlineCodeTerm (str : String) (ignoreElabErrors := false) (identOnly := false) : DocElabM Term :=
  tryElabCodeTermWith (ignoreElabErrors := ignoreElabErrors) (identOnly := identOnly) (fun hls str =>
    ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hls)) #[Verso.Doc.Inline.code $(quote str)]))
    str

open Lean Elab Term in
def tryElabInlineCodeMetavarTerm (str : String) (ignoreElabErrors := false) : DocElabM Term :=
  tryElabCodeMetavarTermWith (ignoreElabErrors := ignoreElabErrors) (fun hls str =>
    ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hls)) #[Verso.Doc.Inline.code $(quote str)]))
    str

open Lean Elab Term in
def tryElabBlockCodeTerm (str : String)  (ignoreElabErrors := false) : DocElabM Term :=
  tryElabCodeTermWith (ignoreElabErrors := ignoreElabErrors) (fun hls str =>
    ``(Verso.Doc.Block.other (Block.leanFromMarkdown $(quote hls)) #[Verso.Doc.Block.code $(quote str)]))
    str

open Lean Elab Term in
def tryParseInlineCodeTactic (str : String) : DocElabM Term := do
  let loc := (← getRef).getPos?.map (← getFileMap).utf8PosToLspPos
  let src :=
    if let some ⟨line, col⟩ := loc then s!"<docstring at {← getFileName}:{line}:{col}>"
    else s!"<docstring at {← getFileName} (unknown line)>"
  match Parser.runParserCategory (← getEnv) `tactic str src with
  | .error e => throw (.error (← getRef) e)
  | .ok stx => DocElabM.withFileMap (.ofString str) <| do
    -- TODO try actually running the tactic - if the parameters are simple enough, then it may work
    -- and give better highlights
    let hls ← highlight stx #[] (PersistentArray.empty)
    ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hls)) #[Verso.Doc.Inline.code $(quote str)])

open Lean Elab Term in
def tryInlineOption (str : String) : DocElabM Term := do
  let optName := str.trim.toName
  let optDecl ← getOptionDecl optName
  let hl : Highlighted := optTok optName optDecl.declName optDecl.descr
  ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hl)) #[Verso.Doc.Inline.code $(quote str)])
where
  optTok (name declName : Name) (descr : String) : Highlighted :=
    .token ⟨.option name declName descr, name.toString⟩

open Lean Elab in
def tryTacticName (tactics : Array Tactic.Doc.TacticDoc) (str : String) : DocElabM Term := do
  for t in tactics do
    if t.userName == str then
      let hl : Highlighted := tacToken t
      return ← ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hl)) #[Verso.Doc.Inline.code $(quote str)])
  throwError "Not a tactic name: {str}"
where
  tacToken (t : Lean.Elab.Tactic.Doc.TacticDoc) : Highlighted :=
    .token ⟨.keyword t.internalName none t.docString, str⟩

open Lean Elab Term in
open Lean.Parser in
def tryHighlightKeywords (extraKeywords : Array String) (str : String) : DocElabM Term := do
  let loc := (← getRef).getPos?.map (← getFileMap).utf8PosToLspPos
  let src :=
    if let some ⟨line, col⟩ := loc then s!"<docstring at {← getFileName}:{line}:{col}>"
    else s!"<docstring at {← getFileName} (unknown line)>"
  let p : Parser := {fn := simpleFn}
  match runParser extraKeywords (← getEnv) (← getOptions) p str src (prec := 0) with
  | .error e => throwError "Not keyword-highlightable"
  | .ok stx => DocElabM.withFileMap (.ofString str) <| do
    let hls ← highlight stx #[] (PersistentArray.empty)
    ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hls)) #[Verso.Doc.Inline.code $(quote str)])
where

  simpleFn := andthenFn whitespace <| nodeFn nullKind <| manyFn tokenFn

  runParser (extraKeywords : Array String) (env : Environment) (opts : Lean.Options) (p : Parser) (input : String) (fileName : String := "<example>") (prec : Nat := 0) : Except (List (Position × String)) Syntax :=
    let ictx := mkInputContext input fileName
    let p' := adaptCacheableContext ({· with prec}) p
    let tokens := extraKeywords.foldl (init := getTokenTable env) (fun x tk => x.insert tk tk)
    let s := p'.fn.run ictx { env, options := opts } tokens (mkParserState input)
    if !s.allErrors.isEmpty then
      Except.error (toErrorMsg ictx s)
    else if ictx.input.atEnd s.pos then
      Except.ok s.stxStack.back
    else
      Except.error (toErrorMsg ictx (s.mkError "end of input"))

  toErrorMsg (ctx : InputContext) (s : ParserState) : List (Position × String) := Id.run do
    let mut errs := []
    for (pos, _stk, err) in s.allErrors do
      let pos := ctx.fileMap.toPosition pos
      errs := (pos, toString err) :: errs
    errs.reverse


declare_syntax_cat braces_attr
syntax (name := plain) attr : braces_attr
syntax (name := bracketed) "[" attr "]" : braces_attr
syntax (name := atBracketed) "@[" attr "]" : braces_attr

private def getAttr : Syntax → Syntax
  | `(plain| $a)
  | `(bracketed| [ $a ] )
  | `(atBracketed| @[ $a ]) => a
  | _ => .missing

open Lean Elab Term in
def tryParseInlineCodeAttribute (validate := true) (str : String) : DocElabM Term := do
  let loc := (← getRef).getPos?.map (← getFileMap).utf8PosToLspPos
  let src :=
    if let some ⟨line, col⟩ := loc then s!"<docstring at {← getFileName}:{line}:{col}>"
    else s!"<docstring at {← getFileName} (unknown line)>"
  match Parser.runParserCategory (← getEnv) `braces_attr str src with
  | .error e => throw (.error (← getRef) e)
  | .ok stx => DocElabM.withFileMap (.ofString str) <| do
    let inner := getAttr stx
    if validate then
      let attrName ←
        match inner.getKind with
        | `Lean.Parser.Attr.simple => pure inner[0].getId
        | .str (.str (.str (.str .anonymous "Lean") "Parser") "Attr") k => pure k.toName
        | other =>
          let allAttrs := attributeExtension.getState (← getEnv) |>.map |>.toArray |>.map (·.fst) |>.qsort (·.toString < ·.toString)
          throwError "Failed to process attribute kind: {stx.getKind} {isAttribute (← getEnv) stx.getKind} {allAttrs |> repr}"
      match getAttributeImpl (← getEnv) attrName with
      | .error e => throwError e
      | .ok _ =>
        let hls ← highlight stx #[] (PersistentArray.empty)
        ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hls)) #[Verso.Doc.Inline.code $(quote str)])
    else
      let hls ← highlight stx #[] (PersistentArray.empty)
      ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hls)) #[Verso.Doc.Inline.code $(quote str)])


private def indentColumn (str : String) : Nat := Id.run do
  let mut i : Option Nat := none
  for line in str.split (· == '\n') do
    let leading := line.takeWhile (·.isWhitespace)
    if leading == line then continue
    if let some i' := i then
      if leading.length < i' then i := some leading.length
    else i := some leading.length
  return i.getD 0

/-- info: 0 -/
#guard_msgs in
#eval indentColumn ""
/-- info: 0 -/
#guard_msgs in
#eval indentColumn "abc"
/-- info: 3 -/
#guard_msgs in
#eval indentColumn "   abc"
/-- info: 3 -/
#guard_msgs in
#eval indentColumn "   abc\n\n   def"
/-- info: 2 -/
#guard_msgs in
#eval indentColumn "   abc\n\n  def"
/-- info: 2 -/
#guard_msgs in
#eval indentColumn "   abc\n\n  def\n    a"

open Lean Elab Term in
def tryElabBlockCodeCommand (str : String) (ignoreElabErrors := false) : DocElabM Term := do
    let loc := (← getRef).getPos?.map (← getFileMap).utf8PosToLspPos
    let src :=
      if let some ⟨line, col⟩ := loc then s!"<docstring at {← getFileName}:{line}:{col}>"
      else s!"<docstring at {← getFileName} (unknown line)>"

    let ictx := Parser.mkInputContext str src
    let cctx : Command.Context := { fileName := ← getFileName, fileMap := FileMap.ofString str, tacticCache? := none, snap? := none, cancelTk? := none}

    let mut cmdState : Command.State := {env := ← getEnv, maxRecDepth := ← MonadRecDepth.getMaxRecDepth, scopes := [{header := ""}]}
    let mut pstate := {pos := 0, recovering := false}
    let mut cmds := #[]

    repeat
      let scope := cmdState.scopes.head!
      let pmctx := { env := cmdState.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
      let (cmd, ps', messages) := Parser.parseCommand ictx pmctx pstate cmdState.messages
      cmds := cmds.push cmd
      pstate := ps'
      cmdState := {cmdState with messages := messages}

      cmdState ← withInfoTreeContext (mkInfoTree := pure ∘ InfoTree.node (.ofCommandInfo {elaborator := `Manual.Meta.lean, stx := cmd})) do
        match (← liftM <| EIO.toIO' <| (Command.elabCommand cmd cctx).run cmdState) with
        | Except.error e =>
          unless ignoreElabErrors do Lean.logError e.toMessageData
          return cmdState
        | Except.ok ((), s) => return s

      if Parser.isTerminalCommand cmd then break

    if cmdState.messages.hasErrors then
      throwError "Errors found in command"

    let hls ← DocElabM.withFileMap (.ofString str) do
      let mut hls := Highlighted.empty
      for cmd in cmds do
        hls := hls ++ (← highlight cmd cmdState.messages.toArray cmdState.infoState.trees)
      pure <| hls.deIndent (indentColumn str)

    ``(Verso.Doc.Block.other (Block.leanFromMarkdown $(quote hls)) #[Verso.Doc.Block.code $(quote str)])


open Lean Elab Term in
def tryElabInlineCodeName (str : String) : DocElabM Term := do
  let str := str.trim
  let x := str.toName
  if x.toString == str then
    let stx := mkIdent x
    let n ← realizeGlobalConstNoOverload stx
    let hl : Highlighted ← constTok n str
    ``(Verso.Doc.Inline.other (Inline.leanFromMarkdown $(quote hl)) #[Verso.Doc.Inline.code $(quote str)])
  else
    throwError "Not a name: '{str}'"
where
  constTok {m} [Monad m] [MonadEnv m] [MonadLiftT MetaM m] [MonadLiftT IO m]
      (name : Name) (str : String) :
      m Highlighted := do
    let docs ← findDocString? (← getEnv) name
    let sig := toString (← (PrettyPrinter.ppSignature name)).1
    pure <| .token ⟨.const name sig docs false, str⟩

open Lean Elab Term in
private def attempt (str : String) (xs : List (String → DocElabM α)) : DocElabM α := do
  match xs with
  | [] => throwError "No attempt succeeded"
  | [x] => x str
  | x::y::xs =>
    let info ← getInfoState
    try
      setInfoState {}
      x str
    catch e =>
      if isAutoBoundImplicitLocalException? e |>.isSome then
        throw e
      else attempt str (y::xs)
    finally
      setInfoState info


open Lean Elab Term in
def tryElabInlineCode (allTactics : Array Tactic.Doc.TacticDoc) (extraKeywords : Array String)
    (priorWord : Option String) (str : String) : DocElabM Term := do
  -- Don't try to show Lake commands as terms
  if "lake ".isPrefixOf str then return (← ``(Verso.Doc.Inline.code $(quote str)))
  try
    attempt str <| wordElab priorWord ++ [
      tryElabInlineCodeName,
      -- When identifiers have the same name as tactics, prefer the identifiers
      tryElabInlineCodeTerm (identOnly := true),
      tryParseInlineCodeTactic,
      tryParseInlineCodeAttribute (validate := true),
      tryInlineOption,
      tryElabInlineCodeTerm,
      tryElabInlineCodeMetavarTerm,
      tryTacticName allTactics,
      withTheReader Term.Context (fun ctx => {ctx with autoBoundImplicit := true}) ∘ tryElabInlineCodeTerm,
      tryElabInlineCodeTerm (ignoreElabErrors := true),
      tryHighlightKeywords extraKeywords
    ]
  catch
    | .error ref e =>
      logWarningAt ref e
      ``(Verso.Doc.Inline.code $(quote str))
    | e =>
      if isAutoBoundImplicitLocalException? e |>.isSome then
        throw e
      else
        logWarning m!"Internal exception uncaught: {e.toMessageData}"
        ``(Verso.Doc.Inline.code $(quote str))
where
  wordElab
    | some "attribute" => [tryParseInlineCodeAttribute (validate := false)]
    | some "tactic" => [tryParseInlineCodeTactic]
    | _ => []

open Lean Elab Term in
def tryElabBlockCode (str : String) : DocElabM Term := do
  try
    attempt str [
      tryElabBlockCodeCommand,
      tryElabBlockCodeTerm,
      tryElabBlockCodeCommand (ignoreElabErrors := true),
      withTheReader Term.Context (fun ctx => {ctx with autoBoundImplicit := true}) ∘
        tryElabBlockCodeTerm (ignoreElabErrors := true)
    ]
  catch
    | .error ref e =>
      logWarningAt ref e
      ``(Verso.Doc.Block.code $(quote str))
    | e =>
      if isAutoBoundImplicitLocalException? e |>.isSome then
        throw e
      else
        logWarning m!"Internal exception uncaught: {e.toMessageData}"
        ``(Verso.Doc.Block.code $(quote str))

open Lean Elab Term in
/--
Heuristically elaborate Lean fragments in Markdown code. The provided names are used as signatures,
from left to right, with the names bound by the signature being available in the local scope in
which the Lean fragments are elaborated.
-/
def blockFromMarkdownWithLean (names : List Name) (b : MD4Lean.Block) : DocElabM Term := do
  unless (← Docstring.getElabMarkdown) do
    return (← Markdown.blockFromMarkdown b (handleHeaders := Markdown.strongEmphHeaders))
  let tactics ← Elab.Tactic.Doc.allTacticDocs
  let keywords := tactics.map (·.userName)
  try
    match names with
    | decl :: decls =>
      -- This brings the parameters into scope, so the term elaboration version catches them!
      Meta.forallTelescopeReducing (← getConstInfo decl).type fun _ _ =>
        blockFromMarkdownWithLean decls b
    | [] =>
      -- It'd be silly for some weird edge case to block on this feature...
      let rec loop (max : Nat) (s : SavedState) : DocElabM Term := do
        match max with
        | k + 1 =>
          try
            let res ←
              Markdown.blockFromMarkdown b
                (handleHeaders := Markdown.strongEmphHeaders)
                (elabInlineCode := tryElabInlineCode tactics keywords)
                (elabBlockCode := tryElabBlockCode)
            synthesizeSyntheticMVarsUsingDefault

            discard <| addAutoBoundImplicits #[] (inlayHintPos? := none)

            return res
          catch e =>
            if let some n := isAutoBoundImplicitLocalException? e then
              s.restore (restoreInfo := true)
              Meta.withLocalDecl n .implicit (← Meta.mkFreshTypeMVar) fun x =>
                withTheReader Term.Context (fun ctx => { ctx with autoBoundImplicits := ctx.autoBoundImplicits.push x } ) do
                  loop k (← (saveState : TermElabM _))
            else throw e
        | 0 => throwError "Ran out of local name attempts"
      let s ← (saveState : TermElabM _)
      try
        loop 40 s
      finally
        (s.restore : TermElabM _)
  catch _ =>
    Markdown.blockFromMarkdown b
      (handleHeaders := Markdown.strongEmphHeaders)

@[block_role_expander docstring]
def docstring : BlockRoleExpander
  | args, #[] => do
    match args with
    | #[.anon (.name x)] =>
      let name ← Elab.realizeGlobalConstNoOverloadWithInfo x
      Doc.PointOfInterest.save (← getRef) name.toString (detail? := some "Documentation")
      let blockStx ←
        match ← Lean.findDocString? (← getEnv) name with
        | none => logWarningAt x m!"No docs found for '{x}'"; pure #[]
        | some docs =>
          let some ast := MD4Lean.parse docs
            | throwErrorAt x "Failed to parse docstring as Markdown"

          ast.blocks.mapM (blockFromMarkdownWithLean [name])

      if Lean.Linter.isDeprecated (← getEnv) name then
        logInfoAt x m!"'{x}' is deprecated"

      let declType ← Block.Docstring.DeclType.ofName name

      let ⟨fmt, infos⟩ ← withOptions (·.setBool `pp.tagAppFns true) <| Block.Docstring.ppSignature name (constantInfo := false)
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
      let extras ← getExtras name declType
      pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstring $(quote name) $(quote declType) $(quote signature)) #[$(blockStx ++ extras),*])]
    | _ => throwError "Expected exactly one positional argument that is a name"
  | _, more => throwErrorAt more[0]! "Unexpected block argument"
where
  getExtras (name : Name) (declType : Block.Docstring.DeclType) : DocElabM (Array Term) :=
    match declType with
    | .structure isClass constructor _ fieldInfo parents _ => do
      let ctorRow : Term ← do
        let header := if isClass then "Instance Constructor" else "Constructor"
        let sigDesc ←
          if let some docs := constructor.docstring? then
            let some mdAst := MD4Lean.parse docs
              | throwError "Failed to parse docstring as Markdown"
            mdAst.blocks.mapM (blockFromMarkdownWithLean [name, constructor.name])
          else pure #[]
        let sig ← `(Verso.Doc.Block.other (Verso.Genre.Manual.Block.internalSignature $(quote constructor.hlName) none) #[$sigDesc,*])
        ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$sig])
      let parentsRow : Option Term ← do
        if parents.isEmpty then pure none
        else
          let header := "Extends"
          let inh ← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.inheritance $(quote name) $(quote parents)) #[])
          some <$> ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$inh])


      let fieldsRow : Term ← do
        let header := if isClass then "Methods" else "Fields"
        let fieldInfo := fieldInfo.filter (·.subobject?.isNone)
        let fieldSigs : Array Term ← fieldInfo.mapM fun i => do
          let inheritedFrom : Option Nat :=
            i.fieldFrom.head?.bind (fun n => parents.findIdx? (·.name == n.name))
          let sigDesc : Array Term ←
            if let some docs := i.docString? then
              let some mdAst := MD4Lean.parse docs
                | throwError "Failed to parse docstring as Markdown"
              mdAst.blocks.mapM (blockFromMarkdownWithLean [name, constructor.name])
            else
              pure (#[] : Array Term)
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.fieldSignature $(quote i.fieldName) $(quote i.type) $(quote inheritedFrom) $(quote <| parents.map (·.parent))) #[$sigDesc,*])
        ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection $(quote header)) #[$fieldSigs,*])
      pure <| #[ctorRow] ++ parentsRow.toArray ++ [fieldsRow]
    | .inductive ctors .. => do
      let ctorSigs : Array Term ←
        -- Elaborate constructor docs in the type's NS
        ctors.mapM fun c => withTheReader Core.Context ({· with currNamespace := name}) do
          let sigDesc ←
            if let some docs := c.docstring? then
              let some mdAst := MD4Lean.parse docs
                | throwError "Failed to parse docstring as Markdown"
              mdAst.blocks.mapM (blockFromMarkdownWithLean [name, c.name])
            else pure (#[] : Array Term)
          ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.constructorSignature $(quote c.signature)) #[$sigDesc,*])
      pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.docstringSection "Constructors") #[$ctorSigs,*])]
    | _ => pure #[]

structure IncludeDocstringOpts where
  name : Name
  elaborate : Bool

def IncludeDocstringOpts.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m IncludeDocstringOpts :=
  IncludeDocstringOpts.mk <$> .positional `name .resolvedName <*> .namedD `elab .bool true

@[block_role_expander includeDocstring]
def includeDocstring : BlockRoleExpander
  | args, #[] => do
    let {name, elaborate} ← IncludeDocstringOpts.parse.run args

    let fromMd :=
      if elaborate then
        blockFromMarkdownWithLean [name]
      else
        Markdown.blockFromMarkdown (handleHeaders := Markdown.strongEmphHeaders)

    let blockStx ←
      match ← Lean.findDocString? (← getEnv) name with
      | none => throwError m!"No docs found for '{name}'"; pure #[]
      | some docs =>
        let some ast := MD4Lean.parse docs
          | throwError "Failed to parse docstring as Markdown"
        ast.blocks.mapM fromMd

    if Lean.Linter.isDeprecated (← getEnv) name then
      logInfo m!"'{name}' is deprecated"

    pure blockStx

  | _args, more => throwErrorAt more[0]! "Unexpected block argument"

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
    let contents ← mdAst.blocks.mapM (blockFromMarkdownWithLean [])
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
  localContentItem := fun _id info _contents => open Verso.Output.Html in do
    let .ok (name, _defaultValue) := FromJson.fromJson? (α := Name × Highlighted) info
      | failure
    pure #[{{<code>{{name.toString}}</code>}}]
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
  replace : Bool

def TacticDocsOptions.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m TacticDocsOptions :=
  TacticDocsOptions.mk <$> .positional `name strOrName <*> .named `show .string true <*> (.named `replace .bool true <&> (·.getD false))
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
    let contents ←
      if opts.replace then pure #[]
      else
        let some mdAst := tactic.docString >>= MD4Lean.parse
          | throwError "Failed to parse docstring as Markdown"
        mdAst.blocks.mapM (blockFromMarkdownWithLean [])
    let userContents ← more.mapM elabBlock
    pure #[← ``(Verso.Doc.Block.other (Block.tactic $(quote tactic) $(quote opts.show)) #[$(contents ++ userContents),*])]



def Inline.tactic : Inline where
  name := `Verso.Genre.Manual.tacticInline



open Verso.Genre.Manual.Markdown in
open Lean Elab Term Parser Tactic Doc in
@[block_extension tactic]
def tactic.descr : BlockDescr := withHighlighting {
  init st := st
    |>.setDomainTitle tacticDomain "Tactic Documentation"
    |>.setDomainDescription tacticDomain "Detailed descriptions of tactics"

  traverse id info _ := do
    let .ok (tactic, «show») := FromJson.fromJson? (α := TacticDoc × Option String) info
      | do logError "Failed to deserialize docstring data while traversing a tactic"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path <| show.getD tactic.userName
    Index.addEntry id {term := Doc.Inline.code <| show.getD tactic.userName}

    modify fun st =>
      st
        |>.saveDomainObject tacticDomain tactic.internalName.toString id
        |>.saveDomainObjectData tacticDomain tactic.internalName.toString (json%{"userName": $tactic.userName})

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
  localContentItem := fun _id info _contents => open Verso.Output.Html in do
    let .ok (tactic, «show») := FromJson.fromJson? (α := TacticDoc × Option String) info
      | failure
    pure #[{{<code class="tactic-name">{{show.getD tactic.userName}}</code>}}]
  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [docstringStyle]
}


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
    let `(inline|code( $tac:str )) := arg
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
def tacticInline.descr : InlineDescr := withHighlighting {
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [docstringStyle]
  toHtml :=
    open Verso.Output.Html Verso.Doc.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean tactic code while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.inlineHtml "examples"
}

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
        mdAst.blocks.mapM (blockFromMarkdownWithLean [])
      else pure #[]
    let userContents ← more.mapM elabBlock
    let some toShow := opts.show
      | throwError "An explicit 'show' is mandatory for conv docs (for now)"
    pure #[← ``(Verso.Doc.Block.other (Block.conv $(quote tactic.name) $(quote toShow) $(quote tactic.docs?)) #[$(contents ++ userContents),*])]

open Verso.Genre.Manual.Markdown in
open Lean Elab Term Parser Tactic Doc in
@[block_extension conv]
def conv.descr : BlockDescr := withHighlighting {
  init st := st
    |>.setDomainTitle convDomain "Conversion Tactics"
    |>.setDomainDescription convDomain "Tactics for performing targeted rewriting of subterms"

  traverse id info _ := do
    let .ok (name, «show», _docs?) := FromJson.fromJson? (α := Name × String × Option String) info
      | do logError "Failed to deserialize conv docstring data"; pure none
    let path ← (·.path) <$> read
    let _ ← Verso.Genre.Manual.externalTag id path <| name.toString
    Index.addEntry id {term := Doc.Inline.code <| «show»}

    modify fun st => st.saveDomainObject convDomain name.toString id
    modify fun st => st.saveDomainObjectData convDomain name.toString (json%{"userName": $«show»})

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
  localContentItem := fun _id info _contents => open Verso.Output.Html in do
    let .ok (_name, «show», _docs?) := FromJson.fromJson? (α := Name × String × Option String) info
      | failure
    pure #[{{<code class="tactic-name">{{«show»}}</code>}}]

  toTeX := some <| fun _goI goB _id _info contents => contents.mapM goB
  extraCss := [docstringStyle]
}
/--
A progress tracker that shows how many symbols are documented.

The parameter `present` tracks which names' docs are present in the manual, sorted by namespace. The
set of names in each namespace is encoded as a string with space separation to prevent running out
of heartbeats while quoting larger data structures.
-/
def Block.progress
    (namespaces exceptions : Array Name)
    (present : List (Name × String))
    (tactics : Array Name) :
    Block where
  name := `Verso.Genre.Manual.Block.progress
  data := toJson (namespaces, exceptions, present, tactics)

private def ignore (env : Environment) (x : Name) : Bool :=
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

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let mut names := #[]
  for (x, _) in (← getEnv).constants do
    if x matches .str .anonymous _ && !(ignore (← getEnv) x) then
      names := names.push x
  names := names.qsort (·.toString < ·.toString)
  elabCommand <| ← `(private def $(mkIdent `allRootNames) : Array Name := #[$(names.map (quote · : Name → Term)),*])

@[directive_expander progress]
def progress : DirectiveExpander
  | args, blocks => do
    if h : args.size > 0 then
      throwErrorAt args[0].syntax  "Expected 0 arguments"
    let mut namespaces : NameSet := {}
    let mut exceptions : NameSet := {}
    for block in blocks do
      match block with
      | `(block|```$nameStx:ident $argsStx* | $contents```) =>
        let contents := contents.getString
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
    let mut rootPresent : NameSet := {}

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
      if let .str .anonymous s := x then
        if let some v := present.find? `_root_ then
          present := present.insert `_root_ (v.insert x)
        else
          present := present.insert `_root_ (NameSet.empty.insert x)
      else
        let mut ns := x
        while !ns.isAnonymous && !(ns.getString!.get 0 |>.isUpper) do
          ns := ns.getPrefix
        if let some v := present.find? ns then
          present := present.insert ns (v.insert x)

    let present' := present.toList.map (fun x => (x.1, String.intercalate " " (x.2.toList.map Name.toString)))
    let allTactics : Array Name := (← Elab.Tactic.Doc.allTacticDocs).map (fun t => t.internalName)

    pure #[← ``(Verso.Doc.Block.other (Verso.Genre.Manual.Block.progress $(quote namespaces.toArray) $(quote exceptions.toArray) $(quote present') $(quote allTactics)) #[])]

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


    let .ok ((namespaces : Array Name), (exceptions : Array Name), (present : List (Name × String)), (allTactics : Array Name)) := fromJson? info
      | panic! "Can't deserialize progress bar state"

    let check : NameMap (List Name) := present.foldr (init := {}) fun (ns, names) z =>
      -- The filter is needed here because `"".splitOn " " = [""]`
      z.insert ns (names.splitOn " " |>.filter (!·.isEmpty) |>.map String.toName)
    let check := check.insert `_root_ allRootNames.toList

    let undocTactics ← allTactics.filterM fun tacticName => do
      let st ← Doc.Html.HtmlT.state (genre := Manual)
      pure <| (TraverseState.getDomainObject? st tacticDomain tacticName.toString).isNone && tacticName ∉ exceptions

    let tacticPercent := undocTactics.size.toFloat * 100.0 / allTactics.size.toFloat

    let namespaces := namespaces.qsort (·.toString ≤ ·.toString)

    return {{
      <dl>
        {{namespaces.map fun ns =>
          let wanted := check.findD ns []
          let notDocumented := wanted.filter (!ok.contains ·) |>.mergeSort (fun x y => x.toString < y.toString)
          let percentMissing :=
            if wanted.isEmpty then 0
            else notDocumented.length.toFloat * 100.0 / wanted.length.toFloat
          {{
            <dt><code>{{ns.toString}}</code></dt>
            <dd>
              <details>
                <summary>
                  <progress id=s!"prog-{ns}" value=s!"{100 - percentMissing.toUInt8.toNat}" min="0" max="100"></progress>
                  <label for=s!"prog-ns">s!"Missing {percentMissing}%"</label>
                </summary>
                {{notDocumented |>.map (·.toString) |> String.intercalate ", " }}
                <pre>
                  {{ notDocumented.map ("{docstring " ++ ·.toString ++ "}\n\n") |> String.join }}
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
