/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Data.HashMap
import Std.Data.HashSet

import SubVerso.Highlighting


import Verso.Code
import Verso.Doc
import Verso.Doc.Html
import Verso.Method
import MultiVerso


import VersoBlog.LexedText

open Std (HashSet HashMap)
open Lean (Json)

open Verso Doc Output Html Code
open Verso.Multi
open SubVerso.Highlighting

namespace Verso.Genre

namespace Blog

structure CodeOpts where
  contextName : Lean.Name
  showProofStates : Bool := true
deriving Repr

/--
The additional blocks available in pages and posts.
-/
inductive BlockExt where
  /--
  Highlighted Lean code.
  -/
  | highlightedCode (opts : CodeOpts) (highlighted : Highlighted)
  /--
  Highlighted Lean messages.
  -/
  | message (summarize : Bool) (msg : Highlighted.Message) (expandTraces : List Lean.Name)
  /--
  Lexed text, to be displayed with highlighted syntax.
  -/
  | lexedText (content : LexedText)
  /--
  When rendered, the content is wrapped in a `<div>` with the given classes.
  -/
  | htmlDiv (classes : String)
  /--
  When rendered, the content is wrapped in the specified HTML tag.
  -/
  | htmlWrapper (tag : String) (attributes : Array (String × String))
  /--
  When rendered, the content is wrapped in a `<details>` tag with the given summary.
  -/
  | htmlDetails (classes : String) (summary : Html)
  /--
  A blob of HTML. The contents are discarded.
  -/
  | blob (html : Html)
  /--
  A reference to a component.
  -/
  | component (name : Lean.Name) (data : Json)
  /--
  A Lean docstring that was indented `indent` spaces in the original source.
  -/
  | docstring (indent : Nat) (declName? : Option Lean.Name)
  /--
  A section in a Lean docstring.

  Lean docstrings may contain nested headers, but they are not sections of the document as a whole.
  The contents of a docstring section are expected to be a paragraph that contains the section's
  title, followed by the actual content.
  -/
  | docstringSection (level : Nat)

/--
The additional inline elements available in pages and posts.
-/
inductive InlineExt where
  /--
  Highlighted Lean code.
  -/
  | highlightedCode (opts : CodeOpts) (highlighted : Highlighted)
  /--
  Highlighted Lean messages.
  -/
  | message (msg : Highlighted.Message) (expandTraces : List Lean.Name)
  /--
  Lexed text, to be displayed with highlighted syntax.
  -/
  | lexedText (content : LexedText)
  /--
  Highlighted code that is not necessarily from Lean.
  -/
  | customHighlight (highlighted : Highlighted)
  /--
  A label to serve as a cross-reference target.
  -/
  | label (name : Lean.Name)
  /--
  A reference to a label.
  -/
  | ref (name : Lean.Name)
  /--
  A reference to a page or post's internal name as a Lean value, to be shown as a link.
  If `id?` is `some X`, then the link is suffixed with `#X`.
  -/
  | pageref (name : Lean.Name) (id? : Option String)
  /--
  An HTML span element with the given classes.
  -/
  | htmlSpan (classes : String)
  /--
  A blob of HTML. The contents are discarded.
  -/
  | blob (html : Html)
  /--
  A reference to a component.
  -/
  | component (name : Lean.Name) (data : Json)

section
local instance : Repr Json where
  reprPrec v := Repr.addAppParen <| "json%" ++ v.render

deriving instance Repr for BlockExt
deriving instance Repr for InlineExt
end

namespace Post

/--
A category of blog posts.
-/
structure Category where
  /-- The name to show in the user interface -/
  name : String
  /-- A URL component for a category index page -/
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
  remoteInfoConfigPath : Option System.FilePath := none
  verbose : Bool := false
deriving Inhabited

class MonadConfig (m : Type → Type u) where
  currentConfig : m Config

export MonadConfig (currentConfig)

def logError [Monad m] [MonadConfig m] [MonadLiftT IO m] (message : String) : m Unit := do
  (← currentConfig).logError message

structure Components where
  /--
  Implementations of all block-level components.

  These will always be of type `BlockComponent`; the use of `Dynamic` breaks a cycle here.
  -/
  blocks : Lean.NameMap Dynamic := {}
  /--
  Implementations of all inline-level components.

  These will always be of type `InlineComponent`; the use of `Dynamic` breaks a cycle here.
  -/
  inlines : Lean.NameMap Dynamic := {}
deriving Inhabited


structure TraverseContext where
  path : List String := {}
  config : Config
  components : Components

structure TraverseState where
  usedIds : Std.HashMap (List String) (HashSet String) := {}
  targets : Lean.NameMap Blog.Info.Target := {}
  blogs : Lean.NameMap Blog.Info.ArchivesMeta := {}
  refs : Lean.NameMap Blog.Info.Ref := {}
  pageIds : Lean.NameMap Blog.Info.PageMeta := {}
  scripts : HashSet String := {}
  stylesheets : HashSet String := {}
  jsFiles : Array (String × String) := #[]
  cssFiles : Array (String × String) := #[]
  errors : HashSet String := {}
  remoteContent : AllRemotes

def TraverseState.addJsFile (st : TraverseState) (name content : String) :=
  if st.jsFiles.all (·.1 != name) then
    {st with jsFiles := st.jsFiles.push (name, content)}
  else st

def TraverseState.addCssFile (st : TraverseState) (name content : String) :=
  if st.cssFiles.all (·.1 != name) then
    {st with cssFiles := st.cssFiles.push (name, content)}
  else st

/-- The metadata used for non-blog-post pages -/
structure Page.Meta where
  /-- Whether to hide this page/part from navigation entries -/
  showInNav : Bool := true
  /-- The HTML ID to assign to the header -/
  htmlId : Option String := none
deriving Repr

/--
An ordinary web page that is not a blog post.
-/
def Page : Genre where
  PartMetadata := Page.Meta
  Block := Blog.BlockExt
  Inline := Blog.InlineExt
  TraverseContext := Blog.TraverseContext
  TraverseState := Blog.TraverseState

instance : Repr Page.PartMetadata := inferInstanceAs (Repr Page.Meta)
instance : Repr Page.Block := inferInstanceAs (Repr Blog.BlockExt)
instance : Repr Page.Inline := inferInstanceAs (Repr Blog.InlineExt)

/-- The metadata used for blog posts -/
structure Post.Meta where
  /-- The post's date. By default, this is used in the URL as well as included in the content. -/
  date : Blog.Date
  /-- The authors of the post -/
  authors : List String
  /-- The categories in which to include the post -/
  categories : List Post.Category := []
  /-- If `true`, the post is not rendered by default -/
  draft : Bool := false
  /-- The HTML ID to assign to the header -/
  htmlId : Option String := none
deriving TypeName, Repr

/--
A blog post.
-/
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

-- This needs to be `Type` because otherwise the code generator starts running into applications of
-- its `casesOn`
class BlogGenre (genre : Genre) : Type where
  context_eq : genre.TraverseContext = Blog.TraverseContext := by rfl
  state_eq : genre.TraverseState = Blog.TraverseState := by rfl
  block_eq : genre.Block = Blog.BlockExt := by rfl
  inline_eq : genre.Inline = Blog.InlineExt := by rfl

instance : BlogGenre Post where

instance : BlogGenre Page where

def BlogGenre.blockComponent [bg : BlogGenre g] (name : Lean.Name) (json : Json) (content : Array (Block g)) : Block g :=
  Block.other (bg.block_eq ▸ BlockExt.component name json) content

def BlogGenre.inlineComponent [bg : BlogGenre g] (name : Lean.Name) (json : Json) (content : Array (Inline g)) : Inline g :=
  Inline.other (bg.inline_eq ▸ InlineExt.component name json) content


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
  match state.usedIds[path]? with
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
    | ⟨u1, t1, b1, r1, p1, s1, s1', js1, css1, err1, rem1⟩,
      ⟨u2, t2, b2, r2, p2, s2, s2', js2, css2, err2, rem2⟩ =>
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
      err1.toList == err2.toList &&
      rem1 == rem2

abbrev TraverseM := ReaderT Blog.TraverseContext (StateT Blog.TraverseState IO)

instance : MonadConfig TraverseM where
  currentConfig := do pure (← read).config
