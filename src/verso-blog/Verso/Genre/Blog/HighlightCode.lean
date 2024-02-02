import Lean
import Verso.Genre.Blog.Basic
import Verso.Method

open Lean Elab
open Verso.Genre

namespace Verso.Genre.Highlighted

partial defmethod Highlighted.Token.Kind.priority : Highlighted.Token.Kind → Nat
  | .var .. => 2
  | .const .. => 5
  | .option .. => 4
  | .sort => 4
  | .keyword _ _ => 3
  | .docComment => 1
  | .unknown => 0

-- Find all info nodes whose canonical span matches the given syntax
def infoForSyntax (t : InfoTree) (stx : Syntax) : List (ContextInfo × Info) :=
  t.collectNodesBottomUp fun ci info _ soFar =>
    if info.stx.getPos? true == stx.getPos? true &&
       info.stx.getTailPos? true == stx.getTailPos? true then
      (ci, info) :: soFar
    else soFar


partial def bestD (sems : Array Highlighted.Token.Kind) (default : Highlighted.Token.Kind) : Highlighted.Token.Kind :=
  if let some m := sems.back? then
    bestD sems.pop <| if m.priority > default.priority then m else default
  else
    default

def fakeToken (meaning : Token.Kind) (tok : String) : Token where
  content := tok
  kind := meaning


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


def identKind [Monad m] [MonadInfoTree m] [MonadLiftT IO m]  [MonadFileMap m] [MonadEnv m] [MonadMCtx m] (ids : HashMap Lsp.RefIdent Lsp.RefIdent) (stx : TSyntax `ident) : m Token.Kind := do
  let trees ← getInfoTrees
  let mut kind : Token.Kind := .unknown

  for t in trees do
    for (ci, info) in infoForSyntax t stx do
      let runMeta {α} (act : MetaM α) : m α := ci.runMetaM info.lctx act
      match info with
      | .ofTermInfo termInfo => do
        let expr ← instantiateMVars termInfo.expr
        match expr with
        | Expr.fvar id =>
          let seen ←
            if let some y := ids.find? (.fvar id) then
              match y with
              | .fvar x =>
                let ty ← instantiateMVars (← runMeta <| Meta.inferType expr)
                let tyStr := toString (← runMeta <| Meta.ppExpr ty)
                if let some localDecl := termInfo.lctx.find? x then
                  if localDecl.isAuxDecl then
                    let e ← runMeta <| Meta.ppExpr expr
                    pure (.const (toString e) tyStr none)
                  else pure (.var x tyStr)
                else pure (.var x tyStr)
              | .const x =>
                let sig := toString (← runMeta (PrettyPrinter.ppSignature x)).1
                let docs ← findDocString? (← getEnv) x
                pure (.const x sig docs)
            else
              let ty ← instantiateMVars (← runMeta <| Meta.inferType expr)
              let tyStr := toString (← runMeta <| Meta.ppExpr ty)
              pure (.var id tyStr)
          if seen.priority > kind.priority then kind := seen
        | Expr.const name _ => --TODO universe vars
          let docs ← findDocString? (← getEnv) name
          let sig := toString (← runMeta (PrettyPrinter.ppSignature name)).1
          let seen := .const name sig docs
          if seen.priority > kind.priority then kind := seen
        | Expr.sort .. =>
          let seen := .sort
          if seen.priority > kind.priority then kind := seen
        | _ => continue
      | .ofFieldInfo fieldInfo =>
        let ty ← instantiateMVars (← runMeta <| Meta.inferType fieldInfo.val)
        let tyStr := toString (← runMeta <| Meta.ppExpr ty)
        let docs ← findDocString? (← getEnv) fieldInfo.projName
        let seen := .const fieldInfo.projName tyStr docs
        if seen.priority > kind.priority then kind := seen
      | .ofFieldRedeclInfo _ => continue
      | .ofCustomInfo _ => continue
      | .ofMacroExpansionInfo _ => continue
      | .ofCompletionInfo _ => continue
      | .ofFVarAliasInfo _ => continue
      | .ofOptionInfo oi =>
        let docs ← findDocString? (← getEnv) oi.declName
        let seen := .option oi.declName docs
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


inductive Output where
  | seq (emitted : Array Highlighted)
  | span (kind : Highlighted.Span.Kind) (info : String)

def Output.add (output : List Output) (hl : Highlighted) : List Output :=
  match output with
  | [] => [.seq #[hl]]
  | .seq left :: more => .seq (left.push hl) :: more
  | .span .. :: _ => .seq #[hl] :: output

def Output.addToken (output : List Output) (token : Highlighted.Token) : List Output :=
  Output.add output (.token token)

def Output.addText (output : List Output) (str : String) : List Output :=
  Output.add output (.text str)

def Output.openSpan (output : List Output) (kind : Highlighted.Span.Kind) (info : String) : List Output :=
  .span kind info :: output

def Output.closeSpan (output : List Output) : List Output :=
  let rec go (acc : Highlighted) : List Output → List Output
    | [] => [.seq #[acc]]
    | .span kind info :: more => Output.add more (.span kind info acc)
    | .seq left :: more => go (.seq (left.push acc)) more
  go .empty output

defmethod Highlighted.fromOutput (output : List Output) : Highlighted :=
  let rec go (acc : Highlighted) : List Output → Highlighted
    | [] => acc
    | .seq left :: more => go (.seq (left.push acc)) more
    | .span kind info :: more => go (.span kind info acc) more
  go .empty output

structure HighlightState where
  /-- Messages not yet displayed -/
  messages : Array Message
  nextMessage : Option (Fin messages.size)
  /-- Output so far -/
  output : List Output
  /-- Messages being displayed -/
  inMessages : List Message
deriving Inhabited

private defmethod Lean.Position.before (pos1 pos2 : Lean.Position) : Bool :=
  pos1.line < pos2.line || (pos1.line == pos2.line && pos1.column < pos2.column)

private defmethod Lean.Position.notAfter (pos1 pos2 : Lean.Position) : Bool :=
  pos1.line < pos2.line || (pos1.line == pos2.line && pos1.column ≤ pos2.column)


def HighlightState.ofMessages [Monad m] [MonadFileMap m]
    (stx : Syntax) (messages : Array Message) : m HighlightState := do
  let msgs ← (·.qsort cmp) <$> messages.filterM (isRelevant stx)
  pure {
    messages := msgs,
    nextMessage := if h : 0 < msgs.size then some ⟨0, h⟩ else none,
    output := [],
    inMessages := [],
  }
where
  cmp (m1 m2 : Message) :=
    if m1.pos.before m2.pos then true
    else if m1.pos == m2.pos then
      match m1.endPos, m2.endPos with
      | none, none => true
      | some _, none => false
      | none, some _ => true
      | some e1, some e2 => e2.before e1
    else false

  isRelevant (stx : Syntax) (msg : Message) : m Bool := do
    let text ← getFileMap
    let (some s, some e) := (stx.getPos?.map text.toPosition , stx.getTailPos?.map text.toPosition)
      | return false
    if let some e' := msg.endPos then
      pure <| !(e'.before s) && !(e.before msg.pos)
    else
      pure <| !(msg.pos.before s) && !(e.before msg.pos)


abbrev HighlightM (α : Type) : Type := StateT HighlightState TermElabM α

instance : Inhabited (HighlightM α) where
  default := fun _ => default

def nextMessage? : HighlightM (Option Message) := do
  let st ← get
  match st.nextMessage with
  | none => pure none
  | some i => pure (some st.messages[i])

def advanceMessages : HighlightM Unit := do
  modify fun st =>
    if let some ⟨i, _⟩ := st.nextMessage then
      if h : i + 1 < st.messages.size
        then {st with nextMessage := some ⟨i + 1, h⟩}
        else {st with nextMessage := none}
    else st

def needsOpening (pos : Lean.Position) (message : Message) : Bool :=
  message.pos.notAfter pos

def needsClosing (pos : Lean.Position) (message : Message) : Bool :=
  message.endPos.map pos.notAfter |>.getD true

partial def openUntil (pos : Lean.Position) : HighlightM Unit := do
  if let some msg ← nextMessage? then
    if needsOpening pos msg then
      advanceMessages
      let kind :=
        match msg.severity with
        | .error => .error
        | .warning => .warning
        | .information => .info
      let str ← contents msg
      modify fun st => {st with
        output := Output.openSpan st.output kind str
        inMessages := msg :: st.inMessages
      }
      openUntil pos
where
  contents (message : Message) : IO String := do
    let head := if message.caption != "" then message.caption ++ ":\n" else ""
    pure <| head ++ (← message.data.toString)


partial def closeUntil (pos : Lean.Position) : HighlightM Unit := do
  let more ← modifyGet fun st =>
    match st.inMessages with
    | [] => (false, st)
    | m :: ms =>
      if needsClosing pos m then
        (true, {st with output := Output.closeSpan st.output, inMessages := ms})
      else (false, st)
  if more then closeUntil pos

def emitString (pos endPos : String.Pos) (string : String) : HighlightM Unit := do
  let text ← getFileMap
  openUntil <| text.toPosition pos
  modify fun st => {st with output := Output.addText st.output string}
  closeUntil <| text.toPosition endPos

def emitString' (string : String) : HighlightM Unit :=
  modify fun st => {st with output := Output.addText st.output string}

def emitToken (info : SourceInfo) (token : Highlighted.Token) : HighlightM Unit := do
  let .original leading pos trailing endPos := info
    | throwError "Syntax not original, can't highlight"
  emitString' leading.toString
  let text ← getFileMap
  openUntil <| text.toPosition pos
  modify fun st => {st with output := Output.addToken st.output token}
  closeUntil <| text.toPosition endPos
  emitString' trailing.toString

def emitToken' (token : Highlighted.Token) : HighlightM Unit := do
  modify fun st => {st with output := Output.addToken st.output token}

partial def highlight' (ids : HashMap Lsp.RefIdent Lsp.RefIdent) (stx : Syntax) (lookingAt : Option Name := none) : HighlightM Unit := do
  match stx with
  | `($e.%$tk$field:ident) =>
      highlight' ids e
      if let some ⟨pos, endPos⟩ := tk.getRange? then
        emitToken tk.getHeadInfo <| .mk .unknown <| (← getFileMap).source.extract pos endPos
      else
        emitString' "."
      highlight' ids field
  | _ =>
    match stx with
    | .missing => pure () -- TODO emit unhighlighted string
    | stx@(.ident i _ x _) =>
        match x.eraseMacroScopes with
        | .str (.str _ _) _ =>
          match stx.identComponents (nFields? := some 1) with
          | [y, field] =>
            if (← infoExists field) then
              highlight' ids y
              emitToken' <| fakeToken .unknown "."
              highlight' ids field
            else
              emitToken i ⟨← identKind ids ⟨stx⟩, x.toString⟩
          | _ => emitToken i ⟨← identKind ids ⟨stx⟩, x.toString⟩
        | _ => emitToken i ⟨← identKind ids ⟨stx⟩, x.toString⟩
    | stx@(.atom i x) =>
      let docs ← match lookingAt with
        | none => pure none
        | some n => findDocString? (← getEnv) n
      if let .sort ← identKind ids ⟨stx⟩ then
        emitToken i ⟨.sort, x⟩
        return
      else
        emitToken i <| (⟨ ·,  x⟩) <|
        match x.get? 0 with
        | some '#' =>
          match x.get? ((0 : String.Pos) + '#') with
          | some c =>
            if c.isAlpha then .keyword lookingAt docs
            else .unknown
          | _ => .unknown
        | some c =>
          if c.isAlpha then .keyword lookingAt docs
          else .unknown
        | _ => .unknown
    | .node _ ``Lean.Parser.Command.docComment #[.atom i1 opener, .atom i2 body] =>
      if let .original leading pos ws _ := i1 then
        if let .original ws' _ trailing endPos := i2 then
          emitToken (.original leading pos trailing endPos) ⟨.docComment, opener ++ ws.toString ++ ws'.toString ++ body⟩
          return
      emitString' (opener ++ " " ++ body ++ "\n")
    | .node _ k children =>
      for child in children do
        highlight' ids child (lookingAt := some k)

def highlight (stx : Syntax) (messages : Array Message) : TermElabM Highlighted := do
  let modrefs := Lean.Server.findModuleRefs (← getFileMap) (← getInfoTrees).toArray
  let ids := build modrefs
  let st ← HighlightState.ofMessages stx messages
  let ((), {output := output, ..}) ← StateT.run (highlight' ids stx) st
  pure <| .fromOutput output
