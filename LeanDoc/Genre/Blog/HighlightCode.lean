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


def identKind [Monad m] [MonadInfoTree m] [MonadLiftT IO m] [MonadEnv m] (stx : TSyntax `ident) : m Token.Kind := do
  let trees ← getInfoTrees
  let mut kind : Token.Kind := .unknown

  for t in trees do
    for info in infoForSyntax t stx do
      match info with
      | .ofTermInfo termInfo =>
        match termInfo.expr with
        | Expr.fvar id =>
          let seen := .var id
          if seen.priority > kind.priority then kind := seen
        | Expr.const name _ => --TODO universe vars
          let docs ← findDocString? (← getEnv) name
          let seen := .const name docs
          if seen.priority > kind.priority then kind := seen
        | Expr.sort .. =>
          let seen := .sort
          if seen.priority > kind.priority then kind := seen
        | _ => continue
      | .ofFieldInfo _ => continue
      | .ofFieldRedeclInfo _ => continue
      | .ofCustomInfo _ => continue
      | .ofMacroExpansionInfo _ => continue
      | .ofCompletionInfo _ => continue
      | .ofFVarAliasInfo _ => continue
      | .ofOptionInfo _ => continue
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


partial def highlight [Inhabited (m Highlighted)] [Monad m] [MonadEnv m] [MonadInfoTree m] [MonadError m] [MonadLiftT IO m]
    (text : FileMap) (stx : Syntax) (inErr : Bool := false) (lookingAt : Option Name := none) : m Highlighted := do
  match stx with
  | `($e.%$tk$field:ident) =>
      let hl1 ← highlight text e inErr
      let pos := tk.getPos? true
      let endPos := tk.getTailPos? true
      let (some pos, some endPos) := (pos, endPos)
        | throwErrorAt stx "Tried to highlight syntax not from the parser {repr stx}"
      let hl2 := .token (mkToken .unknown tk.getHeadInfo <| text.source.extract pos endPos)
      let hl3 ← highlight text field inErr
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
              let hl1 ← highlight text y inErr
              let hl2 := .token (fakeToken .unknown ".")
              let hl3 ← highlight text field inErr
              pure <| .seq #[hl1, hl2, hl3]
            else
              pure <| .token (mkToken (← identKind ⟨stx⟩) i x.toString)
          | _ => pure <| .token (mkToken (← identKind ⟨stx⟩) i x.toString)
        | _ => pure <| .token (mkToken (← identKind ⟨stx⟩) i x.toString)
    | stx@(.atom i x) =>
      let docs ← match lookingAt with
        | none => pure none
        | some n => findDocString? (← getEnv) n
      if let .sort ← identKind ⟨stx⟩ then
        return .token (mkToken .sort i x)
      return (.token <| mkToken · i x) <|
        match x.get? 0 with
        | some '#' => .keyword lookingAt docs
        | some c =>
          if c.isAlpha then .keyword lookingAt docs
          else .unknown
        | _ => .unknown
    | .node _ k children =>
      .seq <$> children.mapM (highlight text · inErr (lookingAt := some k))
