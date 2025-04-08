/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Data.HashMap
import Std.Data.HashSet

import SubVerso.Highlighting

import Verso.Doc
import Verso.Doc.Html
import Verso.Method
import VersoBlog.LexedText
import Verso.Code

open Std (HashSet HashMap)

open Verso Doc Output Html Code Highlighted.WebAssets
open SubVerso.Highlighting

namespace Verso.Genre

namespace Blog
inductive BlockExt where
  | highlightedCode (contextName : Lean.Name) (highlighted : Highlighted)
  | lexedText (content : LexedText)
  | htmlDiv (classes : String)
  | htmlWrapper (tag : String) (attributes : Array (String × String))
  | htmlDetails (classes : String) (summary : Html)
  | blob (html : Html)
deriving Repr

inductive InlineExt where
  | highlightedCode (contextName : Lean.Name) (highlighted : Highlighted)
  | customHighlight (highlighted : Highlighted)
  | label (name : Lean.Name)
  | ref (name : Lean.Name)
  | pageref (name : Lean.Name)
  | htmlSpan (classes : String)
  | blob (html : Html)
deriving Repr

namespace Post

structure Category where
  name : String
  slug : String
deriving BEq, Hashable, DecidableEq, Repr, TypeName

/-- Wrapper around `Array Category` that allows a `TypeName` instance and provides link targets -/
structure Categories where
  categories : Array (String × Post.Category)
deriving TypeName, Repr

end Post

namespace Info

structure Target where
  path : List String
  htmlId : String
deriving BEq

open Lean (Name Syntax)

structure Ref where
  sourceModule : Name
  sourceSyntax : Syntax
  resolved : Bool
deriving BEq

structure ArchivesMeta where
  /-- The categories used by posts in these archives -/
  categories : HashMap Post.Category (HashSet Name) := {}
deriving Repr

instance [BEq α] [Hashable α] : BEq (HashSet α) where
  beq xs ys := xs.size == ys.size && ys.fold (fun pre y => pre && xs.contains y) true

instance [BEq α] [Hashable α] [BEq β] : BEq (HashMap α β) where
  beq xs ys := xs.size == ys.size && ys.fold (fun pre k v => pre && xs[k]? == some v) true

instance : BEq ArchivesMeta where
  beq xs ys := xs.categories == ys.categories

structure PageMeta where
  path : List String
  title : String
deriving BEq, Hashable, TypeName, Repr

end Info

structure Date where
  year : Int
  month : Nat
  day : Nat
deriving Inhabited, Repr

-- FIXME replace this primitive implementation with proper ISO 8601
-- date formatting when available
def Date.toIso8601String (date : Date) : String :=
  s!"{date.year}-{pad date.month}-{pad date.day}"
where
  pad (n : Nat) : String :=
    (if n ≤ 9 then "0" else "") ++ toString n

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

structure TraverseState where
  usedIds : Lean.RBMap (List String) (HashSet String) compare := {}
  targets : Lean.NameMap Blog.Info.Target := {}
  blogs : Lean.NameMap Blog.Info.ArchivesMeta := {}
  refs : Lean.NameMap Blog.Info.Ref := {}
  pageIds : Lean.NameMap Blog.Info.PageMeta := {}
  scripts : HashSet String := {}
  stylesheets : HashSet String := {}
  jsFiles : Array (String × String) := #[]
  cssFiles : Array (String × String) := #[]
  errors : HashSet String := {}

def TraverseState.addJsFile (st : TraverseState) (name content : String) :=
  if st.jsFiles.all (·.1 != name) then
    {st with jsFiles := st.jsFiles.push (name, content)}
  else st

def TraverseState.addCssFile (st : TraverseState) (name content : String) :=
  if st.cssFiles.all (·.1 != name) then
    {st with cssFiles := st.cssFiles.push (name, content)}
  else st

structure Page.Meta where
  /-- Whether to hide this page/part from navigation entries -/
  showInNav : Bool := true
deriving Repr

def Page : Genre where
  PartMetadata := Page.Meta
  Block := Blog.BlockExt
  Inline := Blog.InlineExt
  TraverseContext := Blog.TraverseContext
  TraverseState := Blog.TraverseState

instance : Repr Page.PartMetadata := inferInstanceAs (Repr Page.Meta)
instance : Repr Page.Block := inferInstanceAs (Repr Blog.BlockExt)
instance : Repr Page.Inline := inferInstanceAs (Repr Blog.InlineExt)

structure Post.Meta where
  date : Blog.Date
  authors : List String
  categories : List Post.Category := []
  draft : Bool := false
deriving TypeName, Repr

def Post : Genre where
  PartMetadata := Post.Meta
  Block := Blog.BlockExt
  Inline := Blog.InlineExt
  TraverseContext := Blog.TraverseContext
  TraverseState := Blog.TraverseState

instance : Repr Post.PartMetadata := inferInstanceAs (Repr Post.Meta)
instance : Repr Post.Block := inferInstanceAs (Repr Blog.BlockExt)
instance : Repr Post.Inline := inferInstanceAs (Repr Blog.InlineExt)

instance : TypeName Post.PartMetadata := inferInstanceAs (TypeName Post.Meta)

structure BlogPost where
  id : Lean.Name
  contents : Part Post
deriving TypeName, Repr

class BlogGenre (genre : Genre) where
  traverseContextEq : genre.TraverseContext = Blog.TraverseContext := by rfl
  traverseStateEq : genre.TraverseState = Blog.TraverseState := by rfl

instance : BlogGenre Post where

instance : BlogGenre Page where


defmethod Part.postName [Monad m] [MonadConfig m] [MonadState TraverseState m]
    (post : Part Post) : m String := do
  let date ←
    match post.metadata with
    | none =>
      modify fun st => { st with errors := st.errors.insert s!"Missing metadata block in post \"{post.titleString}\""}
      pure {year := 1900, month := 1, day := 1}
    | some {date, ..} =>
      pure date
  pure <| (← currentConfig).postName date post.titleString

defmethod Part.postName' [Monad m] [MonadConfig m]
    (post : Part Post) : m String := do
  let date : Date :=
    match post.metadata with
    | none =>
      {year := 1900, month := 1, day := 1}
    | some {date, ..}=>
      date
  pure <| (← currentConfig).postName date post.titleString

defmethod BlogPost.postName [Monad m] [MonadConfig m] [MonadState TraverseState m]
    (post : BlogPost) : m String :=
  post.contents.postName

defmethod BlogPost.postName' [Monad m] [MonadConfig m] (post : BlogPost) : m String :=
  post.contents.postName'

private def sumArrayWith (f : α → Nat) (arr : Array α) : Nat := Id.run do
  let mut sum := 0
  for x in arr do
    sum := sum + f x
  sum

/-- An approximate word count for summary length limits -/
partial defmethod Inline.wordCount : Inline genre → Nat
  | .code str
  | .text str => str.split (Char.isWhitespace) |>.filter (!·.isEmpty) |>.length
  | .emph content
  | .link content ..
  | .concat content
  | .other _ content
  | .footnote _ (content : Array (Inline genre))
  | .bold content => sumArrayWith wordCount content
  | .math .. => 1
  | .linebreak .. => 0
  | .image _ _ => 1

partial defmethod Block.wordCount : Block genre → Nat
    | .para contents => sumArrayWith (·.wordCount) contents
    | .ul items
    | .ol _ items => sumArrayWith (fun ⟨bs⟩ => sumArrayWith wordCount bs) items
    | .dl items => sumArrayWith (fun ⟨is, bs⟩ => sumArrayWith (·.wordCount) is + sumArrayWith wordCount bs) items
    | .blockquote items
    | .concat items => sumArrayWith wordCount items
    | .other _ content => sumArrayWith wordCount content
    | .code str => str.split (Char.isWhitespace) |>.filter (!·.isEmpty) |>.length

defmethod BlogPost.summary (post : BlogPost) : Array (Block Post) := Id.run do
  let mut out := #[]
  let mut words := 100
  for b in post.contents.content do
    let wc := b.wordCount
    if out.isEmpty || wc < words then
      out := out.push b
      words := words - wc
    else break
  out

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
    | ⟨u1, t1, b1, r1, p1, s1, s1', js1, css1, err1⟩, ⟨u2, t2, b2, r2, p2, s2, s2', js2, css2, err2⟩ =>
      u1.toList.map (fun p => {p with snd := p.snd.toList}) == u2.toList.map (fun p => {p with snd := p.snd.toList}) &&
      t1.toList == t2.toList &&
      b1.toList == b2.toList &&
      r1.toList == r2.toList &&
      p1.toList == p2.toList &&
      s1.toList == s2.toList &&
      s1'.toList == s2'.toList &&
      js1.size == js2.size &&
      js1.all (js2.contains ·) &&
      css1.size == css2.size &&
      css1.all (css2.contains ·) &&
      err1.toList == err2.toList

abbrev TraverseM := ReaderT Blog.TraverseContext (StateT Blog.TraverseState IO)

instance : MonadConfig TraverseM where
  currentConfig := do pure (← read).config

namespace Traverse

open Doc

def renderMathJs : String :=
"document.addEventListener(\"DOMContentLoaded\", () => {
    for (const m of document.querySelectorAll(\".math.inline\")) {
        katex.render(m.textContent, m, {throwOnError: false, displayMode: false});
    }
    for (const m of document.querySelectorAll(\".math.display\")) {
        katex.render(m.textContent, m, {throwOnError: false, displayMode: true});
    }
});"

def genreBlock (g : Genre) : Blog.BlockExt → Array (Block g) → Blog.TraverseM (Option (Block g))
    | .highlightedCode .., _contents => do
      modify fun st => {st with
        stylesheets := st.stylesheets.insert highlightingStyle,
        scripts := st.scripts.insert highlightingJs
      } |>.addJsFile "popper.js" popper |>.addJsFile "tippy.js" tippy |>.addCssFile "tippy-border.css" tippy.border.css
      pure none
    | _, _ => pure none

def genreInline (g : Genre) : Blog.InlineExt → Array (Inline g) → Blog.TraverseM (Option (Inline g))
    | .highlightedCode .., _contents | .customHighlight .., _contents => do
      modify fun st => {st with
        stylesheets := st.stylesheets.insert highlightingStyle,
        scripts := st.scripts.insert highlightingJs
      } |>.addJsFile "popper.js" popper |>.addJsFile "tippy.js" tippy |>.addCssFile "tippy-border.css" tippy.border.css
      pure none
    | .label x, _contents => do
      -- Add as target if not already present
      if let none := (← get).targets.find? x then
        let path := (← read).path
        let htmlId := (← get).freshId path x
        modify fun st => {st with targets := st.targets.insert x ⟨path, htmlId⟩}
      pure none
    | .ref _x, _contents =>
      -- TODO backreference
      pure none
    | .pageref _x, _contents =>
      -- TODO backreference
      pure none
    | .htmlSpan .., _ | .blob .., _ => pure none

def traverser (g : Genre) (block : g.Block = Blog.BlockExt) (inline : g.Inline = Blog.InlineExt) : Traverse g Blog.TraverseM where
  part _ := pure none
  block _ := pure ()
  inline _ := pure ()
  genrePart _ _ := pure none
  genreBlock := block ▸ genreBlock g
  genreInline := inline ▸ genreInline g

instance : TraversePart Page := {}

instance : Traverse Page Blog.TraverseM := traverser Page rfl rfl

instance : TraversePart Post := {}

instance : Traverse Post Blog.TraverseM := traverser Post rfl rfl

end Traverse
