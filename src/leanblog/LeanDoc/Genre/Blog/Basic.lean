import Lean

import LeanDoc.Doc
import LeanDoc.Doc.Html
import LeanDoc.Method
import LeanDoc.Genre.Blog.Highlighted

open LeanDoc Doc Output Html

namespace LeanDoc.Genre

inductive Blog.BlockExt where
  | highlightedCode (contextName : Lean.Name) (highlighted : Highlighted)
  | htmlDiv (classes : String)
  | blob (html : Html)
deriving Repr

inductive Blog.InlineExt where
  | label (name : Lean.Name)
  | ref (name : Lean.Name)
  | pageref (name : Lean.Name)
  | htmlSpan (classes : String)
  | blob (html : Html)

structure Blog.Info.Target where
  path : List String
  htmlId : String
deriving BEq

open Lean (Name Syntax)

structure Blog.Info.Ref where
  sourceModule : Name
  sourceSyntax : Syntax
  resolved : Bool
deriving BEq

namespace Blog

structure Date where
  year : Int
  month : Nat
  day : Nat
deriving Inhabited

def defaultPostName (date : Date) (title : String) : String :=
  s!"{date.year}-{date.month}-{date.day}-{slugify title}"
where
  slugify str := Id.run do
    let mut slug := ""
    for c in str.toList do
      if c == ' ' then slug := slug.push '-'
      else if c.isAlpha || c.isDigit then slug := slug.push c.toLower
      else continue
    pure slug

structure Config where
  destination : System.FilePath := "./_site"
  showDrafts : Bool := false
  postName : Date → String → String := defaultPostName
  logError : String → IO Unit
deriving Inhabited

class MonadConfig (m : Type → Type u) where
  currentConfig : m Config

export MonadConfig (currentConfig)

def logError [Monad m] [MonadConfig m] [MonadLift IO m] (message : String) : m Unit := do
  (← currentConfig).logError message

structure TraverseContext where
  path : List String := {}
  config : Config

end Blog


deriving instance Ord for List -- TODO - upstream?

structure Blog.TraverseState where
  usedIds : Lean.RBMap (List String) (Lean.HashSet String) compare := {}
  targets : Lean.NameMap Blog.Info.Target := {}
  refs : Lean.NameMap Blog.Info.Ref := {}
  pageIds : Lean.NameMap (List String) := {}


def Blog : Genre where
  PartMetadata := Empty
  Block := Blog.BlockExt
  Inline := Blog.InlineExt
  TraverseContext := Blog.TraverseContext
  TraverseState := Blog.TraverseState

namespace Blog

structure Post where
  date : Date
  authors : List String
  content : Doc Blog
  draft : Bool
deriving TypeName, Inhabited

partial def TraverseState.freshId (state : Blog.TraverseState) (path : List String) (hint : Lean.Name) : String := Id.run do
  let mut idStr := mangle (toString hint)
  match state.usedIds.find? path with
  | none => return idStr
  | some used =>
    while used.contains idStr do
      idStr := next idStr
    return idStr
where
  next (idStr : String) : String :=
    match idStr.takeRightWhile (·.isDigit) with
    | "" => idStr ++ "1"
    | more =>
      if let some n := more.toNat? then
        idStr.dropRight (more.length) ++ toString (n + 1)
      else
        idStr.dropRight (more.length) ++ "1"
  mangle (idStr : String) : String := Id.run do
    let mut state := false -- found valid leading char?
    let mut out := ""
    for c in idStr.toList do
      if state == false then
        if c.isAlpha then
          state := true
          out := out.push c
      else
        if c.isAlphanum || c ∈ [':', '-', ':', '.'] then
          out := out.push c
        else
          out := out ++ s!"--{c.toNat}--"
    pure out



instance : BEq TraverseState where
  beq
    | ⟨u1, t1, r1, p1⟩, ⟨u2, t2, r2, p2⟩ =>
      u1.toList.map (fun p => {p with snd := p.snd.toList}) == u2.toList.map (fun p => {p with snd := p.snd.toList}) &&
      t1.toList == t2.toList &&
      r1.toList == r2.toList &&
      p1.toList == p2.toList


namespace Traverse

open Doc

@[reducible]
defmethod Blog.TraverseM := ReaderT Blog.TraverseContext (StateT Blog.TraverseState IO)

instance : Traverse Blog Blog.TraverseM where
  part _ := pure ()
  block _ := pure ()
  inline _ := pure ()
  genrePart _ _ := pure none
  genreBlock _ _ := pure none
  genreInline
    | .label x, _contents => do
      -- Add as target if not already present
      if let none := (← get).targets.find? x then
        let path := (← read).path
        let htmlId := (← get).freshId path x
        modify (fun st => {st with targets := st.targets.insert x ⟨path, htmlId⟩})
      pure none
    | .ref _x, _contents =>
      -- TODO backreference
      pure none
    | .pageref _x, _contents =>
      -- TODO backreference
      pure none
    | .htmlSpan .., _ | .blob .., _ => pure none
end Traverse
