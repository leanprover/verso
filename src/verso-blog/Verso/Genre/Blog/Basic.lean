import Lean

import Verso.Doc
import Verso.Doc.Html
import Verso.Method
import Verso.Genre.Blog.Highlighted
import Verso.Genre.Blog.LexedText

open Verso Doc Output Html

namespace Verso.Genre

namespace Blog
inductive BlockExt where
  | highlightedCode (contextName : Lean.Name) (highlighted : Highlighted)
  | lexedText (content : LexedText)
  | htmlDiv (classes : String)
  | htmlDetails (classes : String) (summary : Html)
  | blob (html : Html)
deriving Repr

inductive InlineExt where
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

open Lean (Name Syntax HashSet HashMap)

structure Ref where
  sourceModule : Name
  sourceSyntax : Syntax
  resolved : Bool
deriving BEq

instance [BEq α] [Hashable α] [Repr α] [Repr β] : Repr (HashMap α β) where
  reprPrec hm p :=
    Repr.addAppParen (.group <| .nest 2 <| "HashMap.fromList" ++ .line ++ contents hm) p
where contents hm := repr hm.toList

instance [BEq α] [Hashable α] [Repr α] : Repr (HashSet α) where
  reprPrec hs p :=
    Repr.addAppParen (.group <| .nest 2 <| "HashSet.fromList" ++ .line ++ contents hs) p
where contents hs := repr hs.toList

structure ArchivesMeta where
  /-- The categories used by posts in these archives -/
  categories : HashMap Post.Category (HashSet Name) := .empty
deriving Repr

instance [BEq α] [Hashable α] : BEq (HashSet α) where
  beq xs ys := xs.size == ys.size && ys.fold (fun pre y => pre && xs.contains y) true

instance [BEq α] [Hashable α] [BEq β] : BEq (HashMap α β) where
  beq xs ys := xs.size == ys.size && ys.fold (fun pre k v => pre && xs.findEntry? k == some (k, v)) true

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


deriving instance Ord for List -- TODO - upstream?

structure TraverseState where
  usedIds : Lean.RBMap (List String) (Lean.HashSet String) compare := {}
  targets : Lean.NameMap Blog.Info.Target := {}
  blogs : Lean.NameMap Blog.Info.ArchivesMeta := {}
  refs : Lean.NameMap Blog.Info.Ref := {}
  pageIds : Lean.NameMap Blog.Info.PageMeta := {}
  scripts : Lean.HashSet String := {}
  stylesheets : Lean.HashSet String := {}
  errors : Lean.HashSet String := {}

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
    | .ol _ items => sumArrayWith (fun ⟨_, bs⟩ => sumArrayWith wordCount bs) items
    | .dl items => sumArrayWith (fun ⟨is, bs⟩ => sumArrayWith (·.wordCount) is + sumArrayWith wordCount bs) items
    | .blockquote items
    | .concat items => sumArrayWith wordCount items
    | .other _ content => sumArrayWith wordCount content
    | .code _ _ _ str => str.split (Char.isWhitespace) |>.filter (!·.isEmpty) |>.length

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
    | ⟨u1, t1, b1, r1, p1, s1, s1', err1⟩, ⟨u2, t2, b2, r2, p2, s2, s2', err2⟩ =>
      u1.toList.map (fun p => {p with snd := p.snd.toList}) == u2.toList.map (fun p => {p with snd := p.snd.toList}) &&
      t1.toList == t2.toList &&
      b1.toList == b2.toList &&
      r1.toList == r2.toList &&
      p1.toList == p2.toList &&
      s1.toList == s2.toList &&
      s1'.toList == s2'.toList &&
      err1.toList == err2.toList

abbrev TraverseM := ReaderT Blog.TraverseContext (StateT Blog.TraverseState IO)

instance : MonadConfig TraverseM where
  currentConfig := do pure (← read).config

namespace Traverse

open Doc


-- TODO CSS variables, and document it
def highlightingStyle : String := "

.hl.lean .keyword {
  font-weight : bold;
}

.hl.lean .var {
  font-style: italic;
  position: relative;
}

.hover-container {
    width: 0;
    height: 0;
    position: relative;
    display: inline;
}

.hl.lean .token .hover-info {
  display: none;
  position: absolute;
  background-color: #e5e5e5;
  border: 1px solid black;
  padding: 0.5em;
  z-index: 300;
  font-size: inherit;
}

.hl.lean .has-info:hover > .hover-container > .hover-info:not(.tactic *),
.hl.lean .tactic:has(> .tactic-toggle:checked) .has-info:hover > .hover-container > .hover-info,
.hl.lean .token:hover > .hover-container > .hover-info:not(.has-info *):not(.tactic *),
.hl.lean .tactic:has(> .tactic-toggle:checked) .token:hover > .hover-container > .hover-info:not(.has-info *) {
  display: inline-block;
  position: absolute;
  top: 1em;
  font-weight: normal;
  font-style: normal;
}


.hl.lean .token {
  transition: all 0.25s; /* Slight fade for highlights */
}

.hl.lean .token.binding-hl, .hl.lean .literal.string:hover {
  background-color: #eee;
  border-radius: 2px;
  transition: none;
}


.hl.lean .has-info {
  text-decoration-style: wavy;
  text-decoration-line: underline;
  text-decoration-thickness: 0.1rem;
}

.hl.lean .has-info .hover-info {
  display: none;
  position: absolute;
  transform: translate(0.25rem, 0.3rem);
  border: 1px solid black;
  padding: 0.5em;
  z-index: 400;
  text-align: left;
}

.hl.lean .has-info.error {
  text-decoration-color: red;
}

.hl.lean .has-info.error:hover {
  background-color: #ffb3b3;
}

.hl.lean .has-info.error > .hover-container > .hover-info {
  background-color: #ffb3b3;
}

.error pre {
    color: red;
}

.hl.lean .has-info.warning {
  text-decoration-color: yellow;
}

.hl.lean .has-info.warning .hover-info {
  background-color: yellow;
}

.hl.lean .has-info.info {
  text-decoration-color: blue;
}

.hl.lean .has-info.info .hover-info {
  background-color: #4777ff;
}

.hl.lean div.docstring {
  font-family: sans-serif;
  white-space: normal;
  width: 40em;
}

.hl.lean code {
  font-family: monospace;
}

.hl.lean .tactic-state {
  display: none;
  position: relative;
  left: 2em;
  width: fit-content;
  border: 1px solid #888888;
  border-radius: 0.1em;
  padding: 0.5em;
  font-family: sans-serif;
  background-color: #ffffff;
  z-index: 200;
}

.hl.lean .tactic {
  position: relative;
}

.hl.lean .tactic-toggle:checked ~ .tactic-state {
  display: block;
}

.hl.lean .tactic:hover > .tactic-toggle:not(:checked) ~ .tactic-state {
  display: block;
  position: absolute;
  left: 0;
  transform: translate(0.25rem, 0);
  z-index: 250;
}

.hl.lean .tactic > label {
  position: relative;
  transition: all 0.5s;
}

.hl.lean .tactic > label:hover {
  border-bottom: 1px dotted #bbbbbb;
}

.hl.lean .tactic-toggle {
  position: absolute;
  top: 0;
  left: 0;
  opacity: 0;
}

.hl.lean .tactic > label::after {
  content: \"\";
  border: 1px solid #bbbbbb;
  border-radius: 1em;
  height: 0.25em;
  vertical-align: middle;
  width: 0.6em;
  margin-left: 0.1em;
  margin-right: 0.1em;
  display: inline-block;
  transition: all 0.5s;
}

.hl.lean .tactic > label:hover::after {
  border: 1px solid #aaaaaa;
  background-color: #aaaaaa;
  transition: all 0.5s;
}

.hl.lean .tactic > label:has(+ .tactic-toggle:checked)::after {
  border: 1px solid #999999;
  background-color: #999999;
  transition: all 0.5s;
}

.hl.lean .tactic-state .goal + .goal {
  margin-top: 1.5em;
}

.hl.lean .tactic-state summary {
  margin-left: -0.5em;
}

.hl.lean .tactic-state details {
  padding-left: 0.5em;
}

.hl.lean .tactic-state .goal-name::before {
  font-style: normal;
  content: \"case \";
}

.hl.lean .tactic-state .goal-name {
  font-style: italic;
  font-family: monospace;
}

.hl.lean .tactic-state .hypotheses td.colon {
  text-align: center;
  min-width: 1em;
}

.hl.lean .tactic-state .hypotheses td.name {
  text-align: right;
}

.hl.lean .tactic-state .hypotheses td.name,
.hl.lean .tactic-state .hypotheses td.type,
.hl.lean .tactic-state .conclusion .type {
  font-family: monospace;
}

"

def highlightingJs : String :=
"window.onload = () => {
    for (const c of document.querySelectorAll(\".hl.lean .token\")) {
        if (c.dataset.binding != \"\") {
            c.addEventListener(\"mouseover\", (event) => {
                const context = c.closest(\".hl.lean\").dataset.leanContext;
                for (const example of document.querySelectorAll(\".hl.lean\")) {
                    if (example.dataset.leanContext == context) {
                        for (const tok of example.querySelectorAll(\".token\")) {
                            if (c.dataset.binding == tok.dataset.binding) {
                                tok.classList.add(\"binding-hl\");
                            }
                        }
                    }
                }
            });
        }
        c.addEventListener(\"mouseout\", (event) => {
            for (const tok of document.querySelectorAll(\".hl.lean .token\")) {
                tok.classList.remove(\"binding-hl\");
            }
        });
    }
    /* Render docstrings */
    for (const d of document.querySelectorAll(\"pre.docstring\")) {
        const str = d.innerText;
        const html = marked.parse(str);
        const rendered = document.createElement(\"div\");
        rendered.classList.add(\"docstring\");
        rendered.innerHTML = html;
        d.parentNode.replaceChild(rendered, d);
    }
}
"

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
      }
      pure none
    | _, _ => pure none

def genreInline (g : Genre) : Blog.InlineExt → Array (Inline g) → Blog.TraverseM (Option (Inline g))
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
  part _ := pure ()
  block _ := pure ()
  inline _ := pure ()
  genrePart _ _ := pure none
  genreBlock := block ▸ genreBlock g
  genreInline := inline ▸ genreInline g

instance : Traverse Page Blog.TraverseM := traverser Page rfl rfl

instance : Traverse Post Blog.TraverseM := traverser Post rfl rfl

end Traverse
