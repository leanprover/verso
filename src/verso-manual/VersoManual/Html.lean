/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Std.Data.HashSet

import Verso.Output.Html
import MultiVerso.Path

import VersoManual.Basic
import VersoManual.Html.Style

namespace Verso.Genre.Manual.Html
open Std (HashSet)
open Verso.Output Html Multi

structure Toc.Meta where
  title : Html
  shortTitle : Option Html := none
  path : Path
  id : Option String
  sectionNum : Option (Array Numbering)
deriving Repr

structure Toc extends Toc.Meta where
  entry ::
  children : List Toc
deriving Repr

namespace Toc

/--
Remove all ToC elements that don't have their own paths.
-/
partial def onlyPages (toc : Toc) : Toc :=
  {toc with
    children := toc.children.filter (·.path.size > toc.path.size) |>.map onlyPages
  }

/--
Specification for the preorder traversal implemented by the local navigation buttons.

Use this for testing!
-/
def preorder (toc : Toc) : List Toc :=
  toc :: toc.children.attach.flatMap fun ⟨t, h⟩ =>
    have := List.sizeOf_lt_of_mem h
    have : sizeOf toc.children < sizeOf toc := by
      cases toc
      simp +arith
    preorder t
termination_by toc

structure Zipper.ContextFrame extends Toc.Meta where
  /-- The nodes to the left, reversed -/
  left : List Toc
  /-- The nodes to the right, in order -/
  right : List Toc
deriving Repr

def Zipper.ContextFrame.ofToc (toc : Toc) (left right : List Toc) : Zipper.ContextFrame where
  left := left
  right := right
  title := toc.title
  path := toc.path
  id := toc.id
  sectionNum := toc.sectionNum

structure Zipper where
  context : List Zipper.ContextFrame
  focus : Toc
deriving Repr

namespace Zipper

/--
Focuses a zipper on the most specific page that corresponds to the provided path.
-/
def followPath (toc : Toc) (path : Path) : Option Zipper := Id.run do
  let mut here : Zipper := {context := [], focus := toc}
  let mut currentPath := #[]
  for lvl in path do
    currentPath := currentPath.push lvl
    let mut left := []
    for c in here.focus.children do
      if currentPath.isPrefixOf c.path then
        here := {
          focus := c,
          context :=
            .ofToc here.focus left (here.focus.children.drop (left.length + 1)) :: here.context
        }
        if here.focus.path == path then
          return (some here)
        break
      else
        left := c :: left
  if here.focus.path == path then
    return (some here)
  else
    return none

def up (self : Zipper) (hasParent : self.context ≠ []) : Zipper :=
  match h : self.context with
  | {title, path, id, sectionNum, left, right, ..} :: more =>
    let children := left.reverse ++ self.focus :: right
    { context := more,
      focus := {title, path, id, sectionNum, children}
    }
  | [] => False.elim (by contradiction)

def up? (self : Zipper) : Option Zipper :=
  if h : !self.context.isEmpty then
    have : self.context ≠ [] := by
      intro h'
      rw [h'] at h
      simp [List.isEmpty] at h
    some (self.up this)
  else none

def left? (self : Zipper) : Option Zipper :=
  match self.context with
  | [] => none
  | parent :: ancestors =>
    match parent.left with
    | [] => none
    | l :: ls => some {
      context := {parent with left := ls, right := self.focus :: parent.right} :: ancestors,
      focus := l
    }

def right? (self : Zipper) : Option Zipper :=
  match self.context with
  | [] => none
  | parent :: ancestors =>
    match parent.right with
    | [] => none
    | r :: rs => some {
      context := {parent with left := self.focus :: parent.left, right := rs} :: ancestors,
      focus := r
    }

/-- Enters the first child node if one exists -/
def down? (self : Zipper) : Option Zipper :=
  match self.focus.children with
  | [] => none
  | c :: cs => some {
    context := .ofToc self.focus [] cs :: self.context,
    focus := c
  }

@[simp]
theorem up_smaller_context (z : Zipper) {p : z.context ≠ []} : sizeOf (z.up p).context < sizeOf z.context := by
  simp only [up]
  split
  . simp_all +arith
  . contradiction

/-- Reconstructs the ToC that corresponds to a zipper by repeatedly moving upwards. -/
def rebuild (self : Zipper) : Toc :=
  match h : self.context with
  | f :: more =>
    have : sizeOf more < sizeOf self.context := by simp_all; omega
    rebuild <| self.up (by simp_all)
  | [] => self.focus
termination_by self.context

partial def upUntilRight? (self : Zipper) : Option Zipper := do
  let parent ← self.up?
  match parent.context with
  | [] => upUntilRight? parent
  | frame :: ctxt =>
    match frame.right with
    | [] => upUntilRight? parent
    | r :: rs =>
      return {
        context := {frame with left := parent.focus :: frame.left, right := rs} :: ctxt,
        focus := r
      }

/--
Compute the next focus in a preorder traversal, if one exists.

The traversal covers only ToC elements that have their own HTML pages.
-/
partial def next (self : Zipper) : Option Zipper :=
  -- Take the first child, if possible.
  -- Failing that, go to the sibling to the right.
  -- If there's no right sibling, go up until there is.
  self.down? <|> self.right? <|> self.upUntilRight?


/-- Find the rightmost descendent of the current focus with its own HTML page. -/
partial def last (self : Zipper) : Zipper :=
  if let some (left, c) := getLast self.focus.children then {
      context := .ofToc self.focus left [] :: self.context,
      focus := c
      : Zipper
    }.last
  else self
where
  getLast {α} (lst : List α) : Option (List α × α) :=
    if let (x :: xs) := lst then
      some (getLast' [] x xs)
    else none
  getLast' {α} (acc : List α) (x : α) : List α → List α × α
    | [] => (acc, x)
    | y :: ys => getLast' (x :: acc) y ys

/-- Compute the previous focus in a preorder traversal, if one exists -/
def prev (self : Zipper) : Option Zipper := do
  self.left?.map (·.last) <|> self.up?

end Zipper

end Toc

section
open Toc Zipper

private def testToc : Toc where
  title := "ROOT"
  path := #[]
  id := none
  sectionNum := none
  children := [
    {title := "A", path := #["A"], id := none, sectionNum := none, children := []},
    { title := "B", path := #["B"], id := none, sectionNum := none,
      children := [
        {title := "B1", path := #["B", "1"], id := none, sectionNum := none, children := []},
        { title := "B2", path := #["B", "2"], id := none, sectionNum := none, children := [
            {title := "B2a", path := #["B", "2", "a"], id := none, sectionNum := none, children := []}
          ]
        }
      ]
    },
    {title := "C", path := #["C"], id := none, sectionNum := none, children := [
        {title := "C1", path := #["C", "1"], id := none, sectionNum := none, children := []},
        {title := "C2", path := #["C", "2"], id := none, sectionNum := none, children := []}
      ]
    },
    {title := "D", path := #["D"], id := none, sectionNum := none, children := []},
  ]


/--
info: Expected #[], seeing #[]
	Prev: none
	Up: none
	Next: (some #[A])
Expected #[A], seeing #[A]
	Prev: (some #[])
	Up: (some #[])
	Next: (some #[B])
Expected #[B], seeing #[B]
	Prev: (some #[A])
	Up: (some #[])
	Next: (some #[B, 1])
Expected #[B, 1], seeing #[B, 1]
	Prev: (some #[B])
	Up: (some #[B])
	Next: (some #[B, 2])
Expected #[B, 2], seeing #[B, 2]
	Prev: (some #[B, 1])
	Up: (some #[B])
	Next: (some #[B, 2, a])
Expected #[B, 2, a], seeing #[B, 2, a]
	Prev: (some #[B, 2])
	Up: (some #[B, 2])
	Next: (some #[C])
Expected #[C], seeing #[C]
	Prev: (some #[B, 2, a])
	Up: (some #[])
	Next: (some #[C, 1])
Expected #[C, 1], seeing #[C, 1]
	Prev: (some #[C])
	Up: (some #[C])
	Next: (some #[C, 2])
Expected #[C, 2], seeing #[C, 2]
	Prev: (some #[C, 1])
	Up: (some #[C])
	Next: (some #[D])
Expected #[D], seeing #[D]
	Prev: (some #[C, 2])
	Up: (some #[])
	Next: none
Done
-/
#guard_msgs in
#eval do
  let mut here : Zipper := ⟨[], testToc⟩
  let spec := testToc.preorder

  for s in spec do
    IO.println s!"Expected {s.path}, seeing {here.focus.path}"
    IO.println s!"\tPrev: {here.prev |>.map (fun (z : Zipper) => z.focus.path)}"
    IO.println s!"\tUp: {here.up? |>.map (fun (z : Zipper) => z.focus.path)}"
    IO.println s!"\tNext: {here.next |>.map (fun (z : Zipper) => z.focus.path)}"
    if let some n := here.next then
      here := n
    else
      IO.println "Done"
      break

end

/--
Convert a `Toc` to `HTML`.

The `depth` is a limit for the tree depth of the generated HTML (`none` for no limit).
-/
partial def Toc.html (depth : Option Nat) : Toc → Html
  | {title, shortTitle := _, path, id, sectionNum, children} =>
    if depth = some 0 then .empty
    else
      let page :=
        if path.isEmpty then "/"
        else path.link id
      let sectionNum :=
        match sectionNum with
        | none => {{<span class="unnumbered"></span>}}
        | some ns => {{<span class="number">{{sectionNumberString ns}}</span>" "}}
      {{
        <li>
          <a href={{page}}>{{sectionNum}}{{title}}</a>
          {{if children.isEmpty || depth == some 1 then .empty
            else {{<ol> {{children.map (·.html (depth.map Nat.pred))}} </ol>}} }}
        </li>
      }}

def Toc.navButtons (path : Path) (toc : Toc) : Html :=
  let z := Zipper.followPath toc.onlyPages path
  let prev := z.bind Zipper.prev |>.map (·.focus)
  let next := z.bind Zipper.next |>.map (·.focus)
  {{
    <nav class="prev-next-buttons">
      {{if let some somePrev := prev
          then button prev {{<span class="arrow">"←"</span><span class="where">{{getTitle somePrev |>.getD ""}}</span>}} "prev"
          else {{<div></div>}}}}
      {{if let some someNext := next
          then button next {{<span class="where">{{getTitle someNext |>.getD "Next"}}</span><span class="arrow">"→"</span>}} "next"
          else {{<div></div>}}}}
    </nav>
  }}

where
  button (toc : Option Toc) (label : Html) (rel : Option String := none) : Html :=
    if let some dest := toc then
      let relAttr := rel.map (fun r => #[("rel", r)]) |>.getD #[]
      let titleAttr := toc.bind getTitle |>.map (fun t => #[("title", t)]) |>.getD #[]
      {{
        <a class="local-button active" href={{dest.path.link dest.id}} {{relAttr ++ titleAttr}}>
          {{label}}
        </a>
      }}
    else
      {{<span class="local-button inactive">{{label}}</span>}}

  getTitle (toc : Toc) : Option String := do
    let n := toc.sectionNum.map (sectionNumberString · ++ " ") |>.getD ""
    return s!"{n}{← getHtmlTitle toc.title}"

  safeTags := ["code", "span", "a"]

  getHtmlTitle : Html → Option String
  | .text _e s => some s
  | .seq es => (String.join ∘ (·.toList)) <$> es.mapM getHtmlTitle
  | .tag t _ e =>
    if t ∈ safeTags then
      getHtmlTitle e
    else none

def Toc.titleInToc (toc : Toc) : Html := toc.shortTitle.getD toc.title

def Toc.localHtml (path : Path) (toc : Toc) (localItems : Array Html) : Html := Id.run do
  -- We want the last two levels of ToC to be open, so it's possible to navigate both in the local page and see your location in the chapter.
  let mut toc := toc
  let mut fallbackId : Nat := 0
  let rootId := "----bookRoot"
  let mut out : Html := splitTocElem true (path.size ≤ 1) path.isEmpty rootId .empty (linkify #[] none (toc.titleInToc)) toc.children
  let mut currentPath := #[]
  for lvl in path do
    currentPath := currentPath.push lvl
    if let some nextStep := toc.children.find? (·.path == currentPath) then
      toc := nextStep
      let entryId ←
        if let some i := toc.id then pure i
        else
          fallbackId := fallbackId + 1
          pure s!"----header{fallbackId}"
      -- In the last position, when `path == currentPath`, the ToC should default to open and show local items if possible
      if path == currentPath then
        if localItems.isEmpty then
          out := out ++ splitTocElem false true true entryId (sectionNum toc.sectionNum) (linkify currentPath toc.id toc.titleInToc) toc.children
        else
          out := out ++ splitTocLocalElem false true entryId (sectionNum toc.sectionNum) (linkify currentPath toc.id toc.titleInToc) localItems
      else
        out := out ++ splitTocElem false (path.size - currentPath.size == 1) false entryId (sectionNum toc.sectionNum) (linkify currentPath toc.id toc.titleInToc) toc.children
    else break
  {{<div class="split-tocs">{{out}}</div>}}
where
  splitTocWrapper (isTop isOpen thisPage : Bool) (chapterId : String) («section» : Html) (title : Html) (children : Option Html) :=
    let toggleId := s!"--verso-manual-toc-{chapterId}"
    let «class» := if isTop then "split-toc book" else "split-toc"
    let checked := if isOpen then #[("checked", "checked")] else #[]
    {{
      <div class={{«class»}}>
        <div class="title">
          {{if children.isNone then {{
              <span class="no-toggle"/>
            }}
            else {{
              <label for={{toggleId}} class="toggle-split-toc">
                <input
                  type="checkbox"
                  class="toggle-split-toc"
                  id={{toggleId}}
                  {{checked}}/>
              </label>
            }}
          }}
          {{«section»}}
          <span class={{if thisPage && !isTop then "current" else ""}}>
            {{if isTop then "Table of Contents" else title}}
          </span>
        </div>
        {{if let some children := children then children
          else .empty
        }}
      </div>
    }}
  splitTocElem (isTop isOpen thisPage : Bool) (chapterId : String) («section» : Html) (title : Html) (children : List Toc) :=
    let children :=
      if children.isEmpty then none
      else some {{
        <table>
          {{children.map fun c =>
            let classes := String.intercalate " " <|
              (if c.path.isPrefixOf path && !thisPage then
                ["current"]
               else []) ++
              (if c.sectionNum.isSome then
                ["numbered"]
               else ["unnumbered"])

            {{<tr class={{classes}}>
                <td class="num">
                  {{if let some ns := c.sectionNum then sectionNumberString ns
                    else .empty}}
                </td>
                <td>
                  {{linkify c.path c.id c.titleInToc}}
                </td>
              </tr>}}
          }}
        </table>
      }}

    splitTocWrapper isTop isOpen thisPage chapterId «section» title children

  splitTocLocalElem (isTop isOpen : Bool) (chapterId : String) («section» : Html) (title : Html) (children : Array Html) :=
    let children :=
      if children.isEmpty then none
      else some {{
        <ol>
          {{children.map ({{<li>{{·}}</li>}})}}
        </ol>
      }}

    splitTocWrapper isTop isOpen true chapterId «section» title children


  linkify (path : Path) (id : Option String) (html : Html) :=
    match html with
    | .tag "a" _ _ => html
    | other => {{<a href={{path.link id}}>{{other}}</a>}}
  sectionNum num :=
      match num with
      | none => {{<span class="unnumbered"></span>}}
      | some ns => {{<span class="number">{{sectionNumberString ns}}</span>" "}}

def titlePage (title : Html) (authors : List String) (authorshipNote : Option String) (intro : Html) : Html := {{
  <div class="titlepage">
    <h1>{{title}}</h1>
    <div class="authors">
      {{authors.toArray.map ({{ <span class="author">{{Coe.coe ·}}</span> }})}}
      {{if let some note := authorshipNote then {{<p class="note">{{note}}</p>}} else .empty }}
    </div>
    {{intro}}
  </div>
}}

/--
If the current address has no trailing slash, then add it. Otherwise, relative URLs don't work right
on servers that don't do this step.

This is a hack - it only helps clients with JS enabled, and should really be fixed in the server
configuration. But not all hosts allow this to happen, and most clients have JS enabled.
-/
def addSlashJs : String :=
r#"(function(){
  const {protocol:proto, host:hostName, pathname:path, search:srch, hash:hsh} = window.location;
  if (!(path.endsWith("/") || path.endsWith(".html"))) {
    window.location.replace(`${proto}//${hostName}${path}/${srch}${hsh}`);
  }
})()"#

def page
    (toc : Toc) (path : Path)
    (textTitle : String)
    (bookTitle : Html)
    (contents : Html)
    (extraCss : HashSet String)
    (extraJs : HashSet String)
    (localItems : Array Html)
    (extraHead : Array Html := #[])
    (extraContents : Array Html := #[])
    (showNavButtons : Bool := true)
    (logo : Option String := none)
    (logoLink : Option String := none)
    (repoLink : Option String := none)
    (issueLink : Option String := none)
    (extraStylesheets : List String := [])
    (extraJsFiles : Array (String × Bool) := #[]) : Html :=
  let relativeRoot := String.join <| "./" :: path.toList.map (fun _ => "../")
  let defer := #[("defer", "defer")]
  {{
    <html>
      <head>
        <script>
          {{addSlashJs}}
        </script>
        <base href={{relativeRoot}}/>
        <meta charset="utf-8"/>
        <meta name="viewport" content="height=device-height, width=device-width, initial-scale=1, minimum-scale=1, maximum-scale=1"/>
        <title>{{textTitle}}</title>
        <link rel="stylesheet" href="/book.css" />
        <script>s!"const __versoSiteRoot = document.baseURI;"</script>
        <script src="https://cdn.jsdelivr.net/npm/marked@11.1.1/marked.min.js" integrity="sha384-zbcZAIxlvJtNE3Dp5nxLXdXtXyxwOdnILY1TDPVmKFhl4r4nSUG1r8bcFXGVa4Te" crossorigin="anonymous"></script>
        <script src="-verso-search/fuzzysort.js"></script>
        <script type="module" src="-verso-search/search-init.js"></script>
        <link rel="stylesheet" href="-verso-search/search-box.css"/>
        <link rel="stylesheet" href="-verso-search/search-highlight.css"/>
        {{extraJsFiles.map fun f => ({{<script src=s!"{f.1}" {{if f.2 then defer else #[]}}></script>}})}}
        {{extraStylesheets.map (fun url => {{<link rel="stylesheet" href={{url}}/> }})}}
        {{extraCss.toArray.map ({{<style>{{Html.text false ·}}</style>}})}}
        {{extraJs.toArray.map ({{<script>{{Html.text false ·}}</script>}})}}
        {{extraHead}}
        <script src="-verso-search/search-highlight.js" defer="defer"></script>
      </head>
      <body>
        <header>
          <div class="header-logo-wrapper">
            {{if let some url := logo then
                let logoHtml := {{<img src={{url}}/>}}
                let logoDest :=
                  if let some root := logoLink then root
                  else "/"
                {{<a href={{logoDest}} id="logo">{{logoHtml}}</a>}}
              else .empty }}
          </div>
          <div class="header-title-wrapper">
            <a href={{if let some dest := logoLink then dest else "/"}} class="header-title"><h1>{{bookTitle}}</h1></a>
          </div>
        </header>
        <label for="toggle-toc" id="toggle-toc-click">
          <span class="line line1"/>
          <span class="line line2"/>
          <span class="line line3"/>
        </label>
        <div class="with-toc">
          <div class="toc-backdrop" onclick="document.getElementById('toggle-toc-click')?.click()"></div>
          <nav id="toc">
            <input type="checkbox" id="toggle-toc" />
            <div class="first">
              <a href={{if let some dest := logoLink then dest else "/"}} class="toc-title"><h1>{{bookTitle}}</h1></a>
              {{toc.localHtml path localItems}}
            </div>
            <div class="last">
              {{ if repoLink.isSome || issueLink.isSome then {{
                <ul id="meta-links">
                  {{if let some url := repoLink then
                    {{ <li><a href={{url}}>"Source Code"</a></li> }}
                    else .empty}}
                  {{if let some url := issueLink then
                    {{ <li><a href={{url}}>"Report Issues"</a></li> }}
                    else .empty}}
                </ul>
                }} else .empty }}
            </div>
          </nav>
          <main>
            <div class="content-wrapper">
              {{if showNavButtons then toc.navButtons path else .empty}}
              {{contents}}
              {{extraContents}}
              {{if showNavButtons then toc.navButtons path else .empty}}
            </div>
          </main>
        </div>
      </body>
    </html>
  }}



def relativize (path : Path) (html : Html) : Html :=
  html.visitM (m := ReaderT Path Id) (tag := rwTag) |>.run path
where
  urlAttr (name : String) : Bool := name ∈ ["href", "src", "data", "poster"]
  rwAttr (attr : String × String) : ReaderT Path Id (String × String) := do
    if urlAttr attr.fst && "/".isPrefixOf attr.snd then
      let path := (← read)
      pure { attr with
        snd := path.relativize attr.snd
      }
    else
      pure attr
  rwTag (tag : String) (attrs : Array (String × String)) (content : Html) : ReaderT Path Id (Option Html) := do
    if tag == "base" then pure none
    else pure <| some <| .tag tag (← attrs.mapM rwAttr) content
