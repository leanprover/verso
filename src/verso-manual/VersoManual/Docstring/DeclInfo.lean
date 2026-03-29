module
meta import Verso.Instances.Deriving
public import Verso.Instances
import Lean.Data.Json.FromToJson.Basic
import Lean.PrivateName
import Lean.Modifiers
import Lean.Meta.Reduce
import Lean.Widget.InteractiveCode
import SubVerso.Highlighting.Highlighted
public import VersoManual.Docstring.Basic
public import VersoManual.Docstring.DocName
public import VersoManual.Docstring.PrettyPrint

open Lean
open SubVerso.Highlighting

private def renderTaggedInMeta (code : Lean.Widget.CodeWithInfos) : MetaM Highlighted := do
  let hlCtx : SubVerso.Highlighting.Context := ⟨{}, false, false, [], false, (← IO.mkRef {})⟩
  (renderTagged none code : ReaderT SubVerso.Highlighting.Context MetaM _) hlCtx


namespace Verso.Genre.Manual.Block.Docstring


public inductive Visibility where
  | «public» | «private» | «protected»
deriving Inhabited, Repr, ToJson, FromJson, DecidableEq, Ord, Quote

public def Visibility.of (env : Environment) (n : Name) : Visibility :=
  if isPrivateName n then .private else if isProtected env n then .protected else .public

public structure FieldInfo where
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
  visibility : Visibility
deriving Inhabited, Repr, ToJson, FromJson, Quote


public structure ParentInfo where
  projFn : Name
  name : Name
  parent : Highlighted
  index : Nat
deriving ToJson, FromJson, Quote

public inductive DeclType where
  /--
  A structure or class. The `constructor` field is `none` when the constructor is private.
  -/
  | structure (isClass : Bool) (constructor : Option DocName) (fieldNames : Array Name) (fieldInfo : Array FieldInfo) (parents : Array ParentInfo) (ancestors : Array Name)
  | def (safety : DefinitionSafety)
  | opaque (safety : DefinitionSafety)
  | inductive (constructors : Array DocName) (numArgs : Nat) (propOnly : Bool)
  | axiom (safety : DefinitionSafety)
  | theorem
  | ctor (ofInductive : Name) (safety : DefinitionSafety)
  | recursor (safety : DefinitionSafety)
  | quotPrim (kind : QuotKind)
  | other
deriving ToJson, FromJson, Quote

public def DeclType.label : DeclType → String
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
  | .axiom .unsafe => "axiom"
  | .axiom _ => "axiom"
  | .theorem => "theorem"
  | .ctor n _ => s!"constructor of {n}"
  | .quotPrim _ => "primitive"
  | .recursor .unsafe => "unsafe recursor"
  | .recursor _ => "recursor"
  | .other => ""


private partial def getStructurePathToBaseStructureAux (env : Environment) (baseStructName : Name) (structName : Name) (path : List Name) : Option (List Name) :=
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
public def getStructurePathToBaseStructure? (env : Environment) (baseStructName : Name) (structName : Name) : Option (List Name) :=
  getStructurePathToBaseStructureAux env baseStructName structName []


open Meta in
public def DeclType.ofName (c : Name)
    (hideFields : Bool := false)
    (hideStructureConstructor : Bool := false) :
    MetaM DeclType := do
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
                let projType ← withOptions (·.set `format.width (40 : Int) |>.setBool `pp.tagAppFns true) <| Widget.ppExprTagged type
                if let .const parentName _  := type.getAppFn then
                  pure ⟨parentProj, parentName, ← renderTaggedInMeta projType, i⟩
                else
                  pure ⟨parentProj, .anonymous, ← renderTaggedInMeta projType, i⟩
        let ancestors ← getAllParentStructures c
        let allFields := if hideFields then #[] else getStructureFieldsFlattened env c (includeSubobjectFields := true)
        let fieldInfo ←
          forallTelescopeReducing ii.type fun params _ =>
            withLocalDeclD `self (mkAppN (mkConst c (ii.levelParams.map mkLevelParam)) params) fun s =>
              allFields.filterMapM fun fieldName => do
                let proj ← mkProjection s fieldName
                let type ← inferType proj >>= instantiateMVars
                let type' ← withOptions (·.set `format.width (40 : Int) |>.setBool `pp.tagAppFns true) <| (Widget.ppExprTagged type)
                let projType ← withOptions (·.set `format.width (40 : Int) |>.setBool `pp.tagAppFns true) <| ppExpr type
                let fieldFrom? := findField? env c fieldName
                let fieldPath? := fieldFrom? >>= (getStructurePathToBaseStructure? env · c)
                let fieldFrom ← fieldPath?.getD [] |>.mapM (DocName.ofName (showUniverses := false))
                let subobject? := isSubobjectField? env (fieldFrom?.getD c) fieldName
                let fieldInfo? := getFieldInfo? env (fieldFrom?.getD c) fieldName

                let binderInfo := fieldInfo?.map (·.binderInfo) |>.getD BinderInfo.default
                let autoParam := fieldInfo?.map (·.autoParam?.isSome) |>.getD false

                if let some projFn := getProjFnForField? env c fieldName then
                  if isPrivateName projFn then
                    pure none
                  else
                    let docString? ←
                      -- Don't complain about missing docstrings for subobject projections
                      if subobject?.isSome then findDocString? env projFn
                      else getDocString? env projFn
                    let visibility := Visibility.of env projFn
                    let fieldName' := Highlighted.token ⟨.const projFn projType.pretty docString? true none, fieldName.toString⟩

                    pure <| some { fieldName := fieldName', fieldFrom, type := ← renderTaggedInMeta type', subobject?,  projFn, binderInfo, autoParam, docString?, visibility}
                else
                  let fieldName' := Highlighted.token ⟨.unknown, fieldName.toString⟩
                  pure <| some { fieldName := fieldName', fieldFrom, type := ← renderTaggedInMeta type' , subobject?,  projFn := .anonymous, binderInfo, autoParam, docString? := none, visibility := .public}

        let ctor? ←
          if hideStructureConstructor || isPrivateName ctor.name then pure none
          else some <$> DocName.ofName (showNamespace := true) (checkDocstring := false) ctor.name

        return .structure (isClass env c) ctor? info.fieldNames fieldInfo parents ancestors

      else
        let ctors ← ii.ctors.mapM (DocName.ofName (ppWidth := 60) (showNamespace := false) (openDecls := openDecls))
        let t ← inferType <| .const c (ii.levelParams.map .param)
        let t' ← reduceAll t
        return .inductive ctors.toArray (ii.numIndices + ii.numParams) (isPred t')
    | .opaqueInfo oi => return .opaque (if oi.isUnsafe then .unsafe else .safe)
    | .axiomInfo ai => return .axiom (if ai.isUnsafe then .unsafe else .safe)
    | .thmInfo _ => return .theorem
    | .recInfo ri => return .recursor (if ri.isUnsafe then .unsafe else .safe)
    | .ctorInfo ci => return .ctor ci.induct (if ci.isUnsafe then .unsafe else .safe)
    | .quotInfo qi => return .quotPrim qi.kind
  else
    return .other
where
  isPred : Expr → Bool
    | .sort u => u.isZero
    | .forallE _ _ e _ => isPred e
    | .mdata _ e => isPred e
    | .letE _ _ _ e _ => isPred e
    | _ => false

end Block.Docstring

public def Signature.forName [Monad m] [MonadWithOptions m] [MonadEnv m] [MonadMCtx m] [MonadOptions m] [MonadResolveName m] [MonadNameGenerator m] [MonadLiftT MetaM m] [MonadLiftT BaseIO m] [MonadLiftT IO m] [MonadFileMap m] [Alternative m] (name : Name) : m Signature := do
  let (⟨fmt, infos⟩ : FormatWithInfos) ← withOptions (·.setBool `pp.tagAppFns true) <| Block.Docstring.ppSignature name (constantInfo := false)

  let ctx := {
    env           := (← getEnv)
    mctx          := (← getMCtx)
    options       := (← getOptions)
    currNamespace := (← getCurrNamespace)
    openDecls     := (← getOpenDecls)
    fileMap       := default
    ngen          := (← getNGen)
  }

  let ttNarrow := Lean.Widget.TaggedText.prettyTagged (w := 42) fmt
  let sigNarrow ← Lean.Widget.tagCodeInfos ctx infos ttNarrow

  let ttWide := Lean.Widget.TaggedText.prettyTagged (w := 72) fmt
  let sigWide ← Lean.Widget.tagCodeInfos ctx infos ttWide

  return {
    wide := ← renderTaggedInMeta sigWide
    narrow := ← renderTaggedInMeta sigNarrow
  }
