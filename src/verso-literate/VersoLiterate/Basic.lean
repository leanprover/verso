import Lean.Elab.Term
import Verso
import MultiVerso
import SubVerso.Highlighting
import Std.Data.HashSet
import Std.Data.TreeSet
import Verso.BEq

open Verso Doc
open SubVerso.Highlighting
open Lean Elab Term
open Std

namespace VersoLiterate

local instance : Repr Json where
  reprPrec v _ := "json%" ++ v.render

inductive Ext where
  | highlighted : Highlighted → Ext
  | data : Json → Ext
deriving ToJson, FromJson, Repr

open Verso.BEq in
instance : BEq Ext where
  beq := ptrEqThen fun
    | .highlighted hl1, .highlighted hl2 =>
      ptrEqThen' hl1 hl2 (· == ·)
    | .data x, .data y =>
      ptrEqThen' x y (· == ·)
    | _, _ => false

def InlineToLiterate := Name → Dynamic → Array (Doc.Inline Ext) → TermElabM (Option (Doc.Inline Ext))
def BlockToLiterate := Name → Dynamic → Array (Doc.Block Ext Ext) → TermElabM (Option (Doc.Block Ext Ext))

initialize inlineToLiterateAttr : TagAttribute ← registerTagAttribute `inline_to_literate ""
initialize blockToLiterateAttr : TagAttribute ← registerTagAttribute `block_to_literate ""

namespace Builtin
def handleLocal : InlineToLiterate
  | ``Lean.Doc.Data.Local, val, content => do
    if let some { name, type, lctx, fvarId } := val.get? Lean.Doc.Data.Local then
      let (t, _) ← (Lean.Meta.ppExpr type).run {lctx := lctx} {}
      let s := match content with | #[.code s] => s | _ => name.toString
      let i := .other (.highlighted <| .token ⟨.var fvarId (toString t), s⟩) #[.code s]
      return some i
    throwError "Wrong data"
  | _, _, _ => pure none

def handleConst : InlineToLiterate
  | ``Lean.Doc.Data.Const, val, content => do
    if let some { name } := val.get? Lean.Doc.Data.Const then
      let signature ← PrettyPrinter.ppSignature name
      let docs ← findDocString? (← getEnv) name
      let k := .const name (toString signature.fmt) docs false
      let s := match content with | #[.code s] => s | _ => name.toString
      let i := .other (.highlighted <| .token ⟨k, s⟩) #[.code s]
      return some i
    throwError "Wrong data"
  | _, _, _ => pure none

def handlePostponed : InlineToLiterate
  | ``Lean.Doc.PostponedCheck, val, content => do
    if let some { .. } := val.get? Lean.Doc.PostponedCheck then
      -- TODO postponed checks need a solution here
      return some <| .concat content
    throwError "Wrong data"
  | _, _, _ => pure none

def highlightDocCode : Lean.Doc.DocCode → Highlighted
  | ⟨code⟩ => Id.run do
    let mut out : Highlighted := .empty
    for (str, info?) in code do
      if let some info := info? then
        let k :=
          match info with
          | .const x sig
          | .field x sig => .const x (sig.pretty 45) none false
          | .var _ fv ty => .var fv (ty.pretty 45)
          | .option name declName => .option name declName none
          | .literal _litKind (some type) => .withType (type.pretty 45)
          | .literal .. => .unknown
          | .keyword => .keyword none none none
        out := out ++ .token ⟨k, str⟩
      else out := out ++ .text str
    return out

def handleTerm : InlineToLiterate
  | ``Lean.Doc.Data.LeanTerm, val, content => do
    if let some { term, ..} := val.get? Lean.Doc.Data.LeanTerm then
      return some <| .other (.highlighted <| highlightDocCode term) content
    throwError "Wrong data"
  | _, _, _ => pure none

def handleOption : InlineToLiterate
  | ``Lean.Doc.Data.Option, val, content => do
    if let some { name, declName } := val.get? Lean.Doc.Data.Option then
      let str := if let #[.code s] := content then s else toString name
      return some <| .other (.highlighted <| .token ⟨.option name declName none, str⟩) content
    throwError "Wrong data"
  | _, _, _ => pure none

def handleModName : InlineToLiterate
  | ``Lean.Doc.Data.ModuleName, val, content => do
    if let some { module } := val.get? Lean.Doc.Data.ModuleName then
      return some <| .other (.highlighted <| .token ⟨.moduleName module, module.toString⟩) content
    throwError "Wrong data"
  | _, _, _ => pure none

def inline := #[handleLocal, handleConst, handlePostponed, handleTerm, handleOption, handleModName]

end Builtin

unsafe def getInlineToLiterateUnsafe [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] : m (Array InlineToLiterate) := do
  let env ← getEnv
  let mut all := #[]
  for modIdx in [0:env.header.modules.size] do
    all := all ++ inlineToLiterateAttr.ext.getModuleEntries env modIdx
  all := all ++ (inlineToLiterateAttr.ext.getState env).toArray
  return (← all.mapM (evalConstCheck InlineToLiterate ``InlineToLiterate)) ++ Builtin.inline

@[implemented_by getInlineToLiterateUnsafe]
opaque getInlineToLiterate [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] : m (Array InlineToLiterate)

unsafe def getBlockToLiterateUnsafe [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] : m (Array BlockToLiterate) := do
  let env ← getEnv
  let mut all := #[]
  for modIdx in [0:env.header.modules.size] do
    all := all ++ inlineToLiterateAttr.ext.getModuleEntries env modIdx
  all := all ++ (inlineToLiterateAttr.ext.getState env).toArray
  all.mapM (evalConstCheck BlockToLiterate ``BlockToLiterate)

@[implemented_by getBlockToLiterateUnsafe]
opaque getBlockToLiterate [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] : m (Array BlockToLiterate)

open Verso.Multi

open Std in
structure State where
  htmlIds : HashMap InternalId Slug := {}
  usedInternalIds : TreeSet InternalId := {}
  usedHtmlIds : HashSet Slug := {}
  /--
  For each module, saves the HTML IDs assigned to the module docstrings. The module doc in module
  `M`, item `i`, code element `j`, would be under keys `` `M `` and then `(i, j)`.
  -/
  modDocs : NameMap (HashMap (Nat × Nat) Slug) := {}
  moduleDomain : Domain := { title := "Modules" }
  constantDefDomain : Domain := { title := "Global constants" }

section
open Verso.BEq
variable [BEq α] [Hashable α] [Ord α]

@[inline]
private def hashMapEq [BEq β] : (x1 x2 : HashMap α β) → Bool := ptrEqThen fun l r =>
    l.size = r.size && l.fold (init := true) (· && r[·]?.isEqSome ·)

@[inline]
private def hashMapEqWith (eq : β → β → Bool) : (x1 x2 : HashMap α β) → Bool := ptrEqThen fun l r =>
    l.size = r.size && l.fold (init := true) fun soFar k v => soFar && (r[k]?.map (ptrEqThen eq v)).getD false

@[inline]
private def hashSetEq : (x1 x2 : HashSet α) → Bool := ptrEqThen fun l r =>
  l.size = r.size && l.all (· ∈ r)

@[inline]
private def treeSetEq : (x1 x2 : TreeSet α) → Bool := ptrEqThen fun l r =>
  l.size = r.size && l.all (· ∈ r)

@[inline]
private def treeMapEqWith (eq : β → β → Bool) : (x1 x2 : TreeMap α β) → Bool := ptrEqThen fun l r =>
  l.size = r.size && l.foldl (init := true) fun soFar k v => soFar && (r[k]?.map (ptrEqThen eq v)).getD false

@[inline]
private def nameMapEqWith (eq : β → β → Bool) : (x1 x2 : NameMap β) → Bool := ptrEqThen fun l r =>
  l.size = r.size && l.foldl (init := true) fun soFar k v => soFar && ((r.find? k).map (ptrEqThen eq v)).getD false


instance : BEq State where
  beq := ptrEqThen fun
    | ⟨u1, v1, w1, x1, y1, z1⟩, ⟨u2, v2, w2, x2, y2, z2⟩ =>
      hashMapEq u1 u2 &&
      treeSetEq v1 v2 &&
      hashSetEq w1 w2 &&
      nameMapEqWith (hashMapEqWith (· == ·)) x1 x2 &&
      y1 == y2 &&
      z1 == z2

end

def State.getDef (name : Name) (state : State) : Option Slug := do
  let obj ← state.constantDefDomain.get? (toString name)
  for i in obj.ids do
    if let some x := state.htmlIds[i]? then return x
  failure

def State.definitionIds (state : State) : NameMap String :=
  state.constantDefDomain.objects.foldl (init := {}) fun defIds name obj =>
    if let some htmlId := obj.ids.toArray.findSome? (state.htmlIds[·]?) |>.map (·.toString) then
      defIds.insert name.toName htmlId
    else defIds

def State.moduleLink (state : State) (mod : Name) : Option Link := do
  if let some obj := state.moduleDomain[toString mod]? then
    for i in obj.ids do
      if let some htmlId := state.htmlIds[i]? then
        return { path := mod.components.map (·.toString) |>.toArray, htmlId }
  none

def State.constLink (state : State) (c : Name) : Option Link := do
  if let some obj := state.constantDefDomain[toString c]? then
    if let .ok v := obj.data.getObjValAs? String "module" then
      if let some link := state.moduleLink v.toName then
        if let some htmlId := obj.ids.toArray.findSome? state.htmlIds.get? then
          return { link with htmlId }
  none

def State.modDocLink (state : State) (mod : Name) (item : Nat) (pos : Nat) : Option Link := do
  let link ← state.moduleLink mod
  let docIds ← state.modDocs.find? mod
  let htmlId ← docIds[(item, pos)]?
  return { link with htmlId }

def State.saveModDoc (state : State) (mod : Name) (item pos : Nat) : Slug × State :=
  if let some x := (state.modDocs.find? mod).bind (·[(item, pos)]?) then
    (x, state)
  else
    let slug := Slug.unique state.usedHtmlIds s!"mod-doc-{mod}-{item}-{pos}".sluggify
    { fst := slug,
      snd := { state with
        usedHtmlIds := state.usedHtmlIds.insert slug
        modDocs := state.modDocs.alter mod (·.getD {} |>.insert (item, pos) slug)
      }
    }

def State.moduleIds (state : State) : NameMap String :=
  state.moduleDomain.objects.foldl (init := {}) fun modIds name obj =>
    if let some htmlId := obj.ids.toArray.findSome? (state.htmlIds[·]?) |>.map (·.toString) then
      modIds.insert name.toName htmlId
    else modIds

open Verso.Multi in
def State.allLinks (state : State) : HashMap InternalId Link := Id.run do
  let mut idLinks := HashMap.emptyWithCapacity state.usedInternalIds.size
  for (name, obj) in state.moduleDomain.objects do
    if let some link := state.moduleLink name.toName then
      for id in obj.ids do
        idLinks := idLinks.insert id link
  for (_, obj) in state.constantDefDomain.objects do
      if let .ok v := obj.data.getObjValAs? String "module" then
        if let some link := state.moduleLink v.toName then
          if let some htmlId := obj.ids.toArray.findSome? state.htmlIds.get? then
            for id in obj.ids do
              idLinks := idLinks.insert id { link with htmlId }
  return idLinks


def State.linkTargets (state : State) : Code.LinkTargets ρ where
  const x _ := Id.run do
    if let some obj := state.constantDefDomain.get? x.toString then
      if let .ok v := obj.data.getObjValAs? String "module" then
        if let some link := state.moduleLink v.toName then
          return #[.mk "def" s!"Definition of `{x}`" link.link]
    return #[]
  moduleName m _ :=
    if let some link := state.moduleLink m then
      #[.mk "mod" s!"Module `{m}`" link.link]
    else #[]

structure Context where
  currentModule : Name := .anonymous

def Literate : Genre where
  PartMetadata := Empty
  Block := Ext
  Inline := Ext
  TraverseContext := Context
  TraverseState := State

instance : ToJson Literate.Block := inferInstanceAs <| ToJson Ext
instance : ToJson Literate.Inline := inferInstanceAs <| ToJson Ext

instance : TraverseBlock Literate where
instance : TraversePart Literate where

abbrev TraverseM := ReaderT Context (StateRefT State IO)

def freshId : TraverseM InternalId := do
  modifyGet fun s =>
    let (i, s') := InternalId.fresh s.usedInternalIds
    (i, { s with usedInternalIds := s' })

def freshHtmlId (name : Name) : TraverseM Slug := do
  let mut slug := (toString name).sluggify
  while (← get).usedHtmlIds.contains slug do
    slug := slug ++ next
  modify (fun st => {st with usedHtmlIds := st.usedHtmlIds.insert slug })
  return slug
where
  next := "-".sluggify

def saveDef (name : Name) : TraverseM Slug := do
  let mod := (← read).currentModule
  let data := json%{ "module": $(mod), "private": $(isPrivateName name), "userName": $(privateToUserName name) }
  let name' := toString name
  if let some obj := (← get).constantDefDomain.get? name' then
    modify (fun st => { st with constantDefDomain := st.constantDefDomain.setData name' data })
    for i in obj.ids do
      if let some x := (← get).htmlIds[i]? then return x
    -- No HTML ID is registered. Because all these internal IDs are aliases,
    -- we should stick the slug on all of them and return it.
    let x ← freshHtmlId name
    modify (fun st => { st with htmlIds := st.htmlIds.insertMany (obj.ids.toArray.map (·, x)) })
    return x
  else
    let i ← freshId
    let x ← freshHtmlId name
    modify fun st =>
      { st with
        constantDefDomain := st.constantDefDomain.insertId name' i |>.setData name' data
        htmlIds := st.htmlIds.insert i x
      }
    return x

def saveModule (name : Name) : TraverseM Slug := do
  if let some obj := (← get).moduleDomain.get? (toString name) then
    for i in obj.ids do
      if let some x := (← get).htmlIds[i]? then return x
    -- No HTML ID is registered. Because all these internal IDs are aliases,
    -- we should stick the slug on all of them and return it.
    let x ← freshHtmlId name
    modify (fun st => { st with htmlIds := st.htmlIds.insertMany (obj.ids.toArray.map (·, x)) })
    return x
  else
    let i ← freshId
    let x ← freshHtmlId name
    modify fun st =>
      { st with
        moduleDomain := st.moduleDomain.insertId (toString name) i
        htmlIds := st.htmlIds.insert i x
      }
    return x

def saveModDoc (mod : Name) (item pos : Nat) : TraverseM Slug := do
  modifyGet (·.saveModDoc mod item pos)

def getDef (name : Name) : TraverseM (Option Slug) := do
  if let some obj := (← get).constantDefDomain.get? (toString name) then
    for i in obj.ids do
      if let some x := (← get).htmlIds[i]? then return some x
    return none
  else return none

instance : Traverse Literate TraverseM where
  part _ := pure none
  block _ := pure ()
  inline _ := pure ()
  genrePart := nofun
  genreBlock _ _ := pure none
  genreInline _ _ := pure none

open Html
instance [Monad m] : GenreHtml Literate m where
  part _ := nofun
  block _goI goB ext contents :=
    match ext with
    | .highlighted hl => hl.blockHtml (g := Literate) "lean"
    | .data _ => contents.mapM goB
  inline goI ext contents :=
    match ext with
    | .highlighted hl => hl.inlineHtml (g := Literate) "lean"
    | .data _ => contents.mapM goI
