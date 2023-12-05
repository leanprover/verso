import Lean
import LeanDoc.Genre.Blog.Basic
import LeanDoc.Method

open Lean Elab
open LeanDoc.Genre

namespace LeanDoc.Genre.Highlighted

partial defmethod Highlighted.Token.Kind.priority : Highlighted.Token.Kind → Nat
  | .var .. => 2
  | .const .. => 5
  | .sort => 4
  | .keyword _ _ => 3
  | .unknown => 0

-- Find all info nodes whose canonical span matches the given syntax
def infoForSyntax (t : InfoTree) (stx : Syntax) : List Info :=
  t.collectNodesBottomUp fun _ info _ soFar =>
    if info.stx.getPos? true == stx.getPos? true &&
       info.stx.getTailPos? true == stx.getTailPos? true then
      info :: soFar
    else soFar


partial def bestD (sems : Array Highlighted.Token.Kind) (default : Highlighted.Token.Kind) : Highlighted.Token.Kind :=
  if let some m := sems.back? then
    bestD sems.pop <| if m.priority > default.priority then m else default
  else
    default

def fakeToken (meaning : Token.Kind) (tok : String) : Token where
  pre := ""
  content := tok
  post := ""
  kind := meaning

def mkToken (meaning : Token.Kind) (info : SourceInfo)  (tok : String) : Token := Id.run do
  let .original leading pos trailing endPos := info
    | panic! "Syntax not original"
  {
    pre := leading.toString,
    content := tok,
    post := trailing.toString,
    kind := meaning
  }
  -- hl.processWhitespace leading
  -- openFor hl span.1
  -- hl.start span meaning
  -- hl.emit span tok
  -- hl.stop span meaning
  -- closeFor hl <| text.toPosition ⟨endPos.byteIdx + trailing.bsize⟩
  -- hl.processWhitespace trailing


namespace UnionFind
structure State (α : Type u) where
  contents : Array (Nat ⊕ (α × Nat)) := {}
  [eq : BEq α]
  [hashable : Hashable α]
  indices : HashMap α Nat := {}

def State.init [BEq α] [Hashable α] : State α := {}

def insert [Monad m] [MonadState (State α) m] [BEq α] [Hashable α] (x : α) : m Nat := do
  if let some i := (← get).indices.find? x then
    pure i
  else
    let i := (← get).contents.size
    modify fun s => {s with
      contents := s.contents.push <| .inr (x, 1),
    }
    modify fun s => {s with
      indices := s.indices.insert x i
    }
    pure i

partial def find [Inhabited α] [Monad m] [MonadState (State α) m] [BEq α] [Hashable α] (x : α) : m (Nat × α × Nat) := do
  loop <| ← insert x
where
  loop (i : Nat) : m (Nat × α × Nat) := do
    match (← get).contents[i]! with
    | .inl j => loop j
    | .inr (v, sz) => return (i, v, sz)

def equate [Inhabited α] [Monad m] [MonadState (State α) m] [BEq α] [Hashable α] (x y : α) : m Unit := do
  let mut x' ← find x
  let mut y' ← find y
  if x'.fst == y'.fst then return
  if x'.2.2 < y'.2.2 then
    let tmp := x'
    x' := y'
    y' := tmp
  modify fun s => {s with contents := s.contents.set! y'.fst (.inl x'.fst)}
  modify fun s => {s with contents := s.contents.set! x'.fst (.inr (x'.2.1, x'.2.2 + y'.2.2))}

def testSetup : StateT (State String) Id Unit := do
  for x in [0:10] do discard <| insert (toString x)
  for x in [0:10:2] do equate "0" (toString x)

end UnionFind

def getRefs (info : Server.RefInfo) : List Lsp.RefIdent :=
  let defn := info.definition.map getNames |>.getD []
  let more := info.usages.map getNames
  more.foldl (· ++ ·) defn
where
  getNames (ref : Server.Reference) : List Lsp.RefIdent :=
    ref.ident :: ref.aliases.toList

def build (refs : Server.ModuleRefs) : HashMap Lsp.RefIdent Lsp.RefIdent := Id.run do
  let st := go refs.toList |>.run .init |>.snd
  let mut ids : HashMap _ _ := {}
  for (x, _) in st.indices.toList do
    let ((_, y, _), _) := StateT.run (m := Id) (UnionFind.find x) st
    ids := ids.insert x y
  ids
where
  go : List (Lsp.RefIdent × Server.RefInfo) → StateT (UnionFind.State Lsp.RefIdent) Id Unit
    | [] => pure ()
    | (x, info) :: more => do
      for y in getRefs info do UnionFind.equate x y
      go more


def identKind [Monad m] [MonadInfoTree m] [MonadLiftT IO m] [MonadFileMap m] [MonadEnv m] (ids : HashMap Lsp.RefIdent Lsp.RefIdent) (stx : TSyntax `ident) : m Token.Kind := do
  let trees ← getInfoTrees

  let mut kind : Token.Kind := .unknown

  for t in trees do
    for info in infoForSyntax t stx do
      match info with
      | .ofTermInfo termInfo =>
        match termInfo.expr with
        | Expr.fvar id =>
          let seen ←
            if let some y := ids.find? (.fvar id) then
              match y with
              | .fvar x => pure <| .var x
              | .const x => do
                let docs ← findDocString? (← getEnv) x
                pure (.const x docs)
            else pure (.var id)
          if seen.priority > kind.priority then kind := seen
        | Expr.const name _ => --TODO universe vars
          let docs ← findDocString? (← getEnv) name
          let seen := .const name docs
          if seen.priority > kind.priority then kind := seen
        | Expr.sort .. =>
          let seen := .sort
          if seen.priority > kind.priority then kind := seen
        | _ => continue
      | .ofFieldInfo fieldInfo =>
          let docs ← findDocString? (← getEnv) fieldInfo.projName
          let seen := .const fieldInfo.projName docs
          if seen.priority > kind.priority then kind := seen
      | .ofFieldRedeclInfo _ => continue
      | .ofCustomInfo _ => continue
      | .ofMacroExpansionInfo _ => continue
      | .ofCompletionInfo _ => continue
      | .ofFVarAliasInfo _ => continue
      | .ofOptionInfo oi =>
          let docs ← findDocString? (← getEnv) oi.declName
          let seen := .const oi.declName docs
          if seen.priority > kind.priority then kind := seen
      | .ofTacticInfo _ => continue
      | .ofUserWidgetInfo _ => continue
      | .ofCommandInfo _ => continue
  pure kind

def infoExists [Monad m] [MonadInfoTree m] [MonadLiftT IO m] (stx : Syntax) : m Bool := do
  let trees ← getInfoTrees
  for t in trees do
    for _ in infoForSyntax t stx do
      return true
  return false



partial def highlight' [Inhabited (m Highlighted)] [Monad m] [MonadFileMap m] [MonadEnv m] [MonadInfoTree m] [MonadError m] [MonadLiftT IO m]
    (ids : HashMap Lsp.RefIdent Lsp.RefIdent) (stx : Syntax) (inErr : Bool := false) (lookingAt : Option Name := none) : m Highlighted := do
  match stx with
  | `($e.%$tk$field:ident) =>
      let hl1 ← highlight' ids e inErr
      let pos := tk.getPos? true
      let endPos := tk.getTailPos? true
      let (some pos, some endPos) := (pos, endPos)
        | throwErrorAt stx "Tried to highlight syntax not from the parser {repr stx}"
      let hl2 := .token (mkToken .unknown tk.getHeadInfo <| (← getFileMap).source.extract pos endPos)
      let hl3 ← highlight' ids field inErr
      pure <| .seq #[hl1, hl2, hl3]
  | _ =>
    match stx with
    | .missing => pure .empty -- TODO emit unhighlighted string somehow?
    | stx@(.ident i _ x _) =>
        match x.eraseMacroScopes with
        | .str (.str _ _) _ =>
          match stx.identComponents (nFields? := some 1) with
          | [y, field] =>
            if (← infoExists field) then
              let hl1 ← highlight' ids y inErr
              let hl2 := .token (fakeToken .unknown ".")
              let hl3 ← highlight' ids field inErr
              pure <| .seq #[hl1, hl2, hl3]
            else
              pure <| .token (mkToken (← identKind ids ⟨stx⟩) i x.toString)
          | _ => pure <| .token (mkToken (← identKind ids ⟨stx⟩) i x.toString)
        | _ => pure <| .token (mkToken (← identKind ids ⟨stx⟩) i x.toString)
    | stx@(.atom i x) =>
      let docs ← match lookingAt with
        | none => pure none
        | some n => findDocString? (← getEnv) n
      if let .sort ← identKind ids ⟨stx⟩ then
        return .token (mkToken .sort i x)
      return (.token <| mkToken · i x) <|
        match x.get? 0 with
        | some '#' => .keyword lookingAt docs
        | some c =>
          if c.isAlpha then .keyword lookingAt docs
          else .unknown
        | _ => .unknown
    | .node _ k children =>
      .seq <$> children.mapM (highlight' ids · inErr (lookingAt := some k))


def highlight [Inhabited (m Highlighted)] [Monad m] [MonadFileMap m] [MonadEnv m] [MonadInfoTree m] [MonadError m] [MonadLiftT IO m]
    (stx : Syntax) (inErr : Bool := false) (lookingAt : Option Name := none) : m Highlighted := do
  let modrefs := Lean.Server.findModuleRefs (← getFileMap) (← getInfoTrees).toArray
  let ids := build modrefs
  highlight' ids stx inErr lookingAt
