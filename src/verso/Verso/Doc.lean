/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.ToExpr
import Verso.Doc.Name

namespace Verso

namespace Doc

open Std (Format)
open Lean (Name Json ToJson FromJson ToExpr)
open Lean.Json (getObj?)

structure Genre : Type 1 where
  PartMetadata : Type
  Block : Type
  Inline : Type
  TraverseContext : Type
  TraverseState : Type

def Genre.none : Genre := ⟨Empty, Empty, Empty, Unit, Unit⟩

instance : Repr Genre.none.Block where
  reprPrec e _ := nomatch e

instance : Repr Genre.none.Inline where
  reprPrec e _ := nomatch e

instance : Repr Genre.none.PartMetadata where
  reprPrec e _ := nomatch e

inductive MathMode where | inline | display
deriving Repr, BEq, Hashable, Ord, ToJson, FromJson, ToExpr

private def arrayEq (eq : α → α → Bool) (xs ys : Array α) : Bool := Id.run do
    if h : xs.size = ys.size then
      for h' : i in [0:xs.size] do
        have : i < ys.size := by
          have : i < xs.size := by get_elem_tactic
          rw [← h]
          assumption
        if !(eq xs[i] ys[i]) then return false
      return true
    else return false


inductive Inline (genre : Genre) : Type where
  | text (string : String)
  | emph (content : Array (Inline genre))
  | bold (content : Array (Inline genre))
  | code (string : String)
  /-- Embedded blobs of TeX math -/
  | math (mode : MathMode) (string : String)
  | linebreak (string : String)
  | link (content : Array (Inline genre)) (url : String)
  | footnote (name : String) (content : Array (Inline genre))
  | image (alt : String) (url : String)
  | concat (content : Array (Inline genre))
  | other (container : genre.Inline) (content : Array (Inline genre))
deriving Inhabited

instance : Append (Inline genre) where
  append
    | .concat #[], x => x
    | x, .concat #[] => x
    | .concat xs, .concat ys => .concat (xs ++ ys)
    | .concat xs, x => .concat (xs.push x)
    | x, .concat xs => .concat (#[x] ++ xs)
    | x, y => .concat #[x, y]

def Inline.empty : Inline genre := .concat #[]

private partial def Inline.toJson [ToJson genre.Inline] : Inline genre → Json
  | .text str => json% {"text": $str}
  | .emph content => json% {"emph": $(content.map toJson)}
  | .bold content => json% {"bold": $(content.map toJson)}
  | .code str => json% {"code": $str}
  | .math mode str => json% {"math": {"mode": $mode, "str": $str}}
  | .linebreak str => json% {"linebreak": $str}
  | .link content url => json% {"link": {"content" : $(content.map toJson), "url": $url}}
  | .footnote name content => json% {"footnote": { "name": $name, "content" : $(content.map toJson)}}
  | .image alt url => json% {"image":{"alt": $alt, "url": $url}}
  | .concat content => json% {"concat": $(content.map toJson)}
  | .other container content => json%{"other": {"container": $container, "content": $(content.map toJson)}}

instance [ToJson genre.Inline] : ToJson (Inline genre) where
  toJson := Inline.toJson

private partial def Inline.fromJson? [FromJson genre.Inline] (json : Json) : Except String (Inline genre) := do
  let obj ← json.getObj?
  if let #[⟨k, v⟩] := obj.toArray then
    match k with
    | "text" => text <$> FromJson.fromJson? v
    | "emph" =>
      let arr : Array Json ← FromJson.fromJson? v
      emph <$> arr.mapM fromJson?
    | "bold" =>
      let arr : Array Json ← FromJson.fromJson? v
      bold <$> arr.mapM fromJson?
    | "code" => code <$> FromJson.fromJson? v
    | "math" => math <$> FromJson.fromJson? (← v.getObjVal? "mode") <*> FromJson.fromJson? (← v.getObjVal? "str")
    | "linebreak" => linebreak <$> FromJson.fromJson? v
    | "link" =>
      let arr : Array Json ← v.getObjValAs? (Array Json) "content"
      link <$> arr.mapM fromJson? <*> FromJson.fromJson? (← v.getObjVal? "url")
    | "footnote" =>
      let arr : Array Json ← v.getObjValAs? (Array Json) "content"
      footnote <$> FromJson.fromJson? (← v.getObjVal? "name") <*> arr.mapM fromJson?
    | "image" => image <$> FromJson.fromJson? (← v.getObjVal? "alt") <*> FromJson.fromJson? (← v.getObjVal? "url")
    | "concat" =>
      let arr : Array Json ← FromJson.fromJson? v
      concat <$> arr.mapM fromJson?
    | "other" =>
      let arr : Array Json ← v.getObjValAs? (Array Json) "content"
      other <$> FromJson.fromJson? (← v.getObjVal? "container") <*> arr.mapM fromJson?
    | nonKey => throw s!"Expected a key that's a constructor name of 'Inline', got '{nonKey}'"
  else
    throw "Expected a one-field object"

instance [FromJson genre.Inline] : FromJson (Inline genre) where
  fromJson? := Inline.fromJson?

partial def Inline.beq [BEq genre.Inline] : Inline genre → Inline genre → Bool
  | .text str1, .text str2
  | .code str1, .code str2
  | .linebreak str1, .linebreak str2=> str1 == str2
  | .emph c1, .emph c2
  | .bold c1, .bold c2 => arrayEq beq c1 c2
  | .math m1 str1, .math m2 str2 => m1 == m2 && str1 == str2
  | .link txt1 url1, .link txt2 url2 => arrayEq beq txt1 txt2 && url1 == url2
  | .footnote name1 content1, .footnote name2 content2 => name1 == name2 && arrayEq beq content1 content2
  | .image alt1 url1, .image alt2 url2 => alt1 == alt2 && url1 == url2
  | .concat c1, .concat c2 => arrayEq beq c1 c2
  | .other container1 content1, .other container2 content2 => container1 == container2 && arrayEq beq content1 content2
  | _, _ => false

instance [BEq genre.Inline] : BEq (Inline genre) := ⟨Inline.beq⟩

private partial def Inline.hashCode [Hashable genre.Inline] : Inline genre → UInt64
  | .text str => mixHash 11 <| hash str
  | .code str => mixHash 13 <| hash str
  | .linebreak str => mixHash 17 <| hash str
  | .emph c => mixHash 19 <| hash (c.map hashCode)
  | .bold c => mixHash 23 <| hash (c.map hashCode)
  | .math m str => mixHash 29 <| mixHash (hash m) (hash str)
  | .link txt url => mixHash 31 <| mixHash (hash <| txt.map hashCode) (hash url)
  | .footnote name c => mixHash 37 <| mixHash (hash name) (hash <| c.map hashCode)
  | .image alt url => mixHash 41 <| mixHash (hash alt) (hash url)
  | .concat c => mixHash 43 <| hash (c.map hashCode)
  | .other container content => mixHash 47 <| mixHash (hash container) (hash <| content.map hashCode)

instance [Hashable genre.Inline] : Hashable (Inline genre) where
  hash := Inline.hashCode

private def Inline.compare [Ord genre.Inline] : (i1 i2 : Inline genre) → Ordering
  | .text str1, .text str2 => Ord.compare str1 str2
  | .text _, _ => .lt
  | _, .text _ => .gt
  | .code str1, .code str2 => Ord.compare str1 str2
  | .code _, _ => .lt
  | _, .code _ => .gt
  | .linebreak str1, .linebreak str2 => Ord.compare str1 str2
  | .linebreak _, _ => .lt
  | _, .linebreak _ => .gt
  | .emph c1, .emph c2 => arr c1 c2
  | .emph _, _ => .lt
  | _, .emph _ => .gt
  | .bold c1, .bold c2 => arr c1 c2
  | .bold _, _ => .lt
  | _, .bold _ => .gt
  | .math m1 c1, .math m2 c2 =>
    Ord.compare m1 m2 |>.then (Ord.compare c1 c2)
  | .math .., _ => .lt
  | _, .math .. => .gt
  | .link txt1 url1, .link txt2 url2 =>
    arr txt1 txt2 |>.then (Ord.compare url1 url2)
  | .link .., _ => .lt
  | _, .link .. => .gt
  | .footnote name1 c1, .footnote name2 c2 =>
    arr c1 c2 |>.then (Ord.compare name1 name2)
  | .footnote .., _ => .lt
  | _, .footnote .. => .gt
  | .image alt1 url1, .image alt2 url2 =>
    Ord.compare alt1 alt2 |>.then (Ord.compare url1 url2)
  | .image .., _ => .lt
  | _, .image .. => .gt
  | .concat c1, .concat c2 => arr c1 c2
  | .concat _, _ => .lt
  | _, .concat _ => .gt
  | .other o1 c1, .other o2 c2 =>
    Ord.compare o1 o2 |>.then (arr c1 c2)
where
  arr xs ys :=
    match Ord.compare xs.size ys.size with
      | .eq => Id.run do
        for ⟨x, _⟩ in xs.attach, ⟨y, _⟩ in ys.attach do
          let o := compare x y
          if o != .eq then return o
        return .eq
      | .lt => .lt
      | .gt => .gt

instance [Ord genre.Inline] : Ord (Inline genre) where
  compare := Inline.compare

private def reprArray (r : α → Nat → Format) (arr : Array α) : Format :=
  .bracket "#[" (.joinSep (arr.toList.map (r · max_prec)) ("," ++ .line)) "]"

private def reprList (r : α → Nat → Format) (xs : List α) : Format :=
  .bracket "[" (.joinSep (xs.map (r · max_prec)) ("," ++ .line)) "]"

private def reprPair (x : α → Nat → Format) (y : β → Nat → Format) (v : α × β) : Format :=
  .bracket "(" (x v.fst max_prec ++ ("," ++.line) ++ y v.snd max_prec) ")"

private def reprCtor (c : Name) (args : List Format) : Format :=
  .nest 2 <| .group (.joinSep (.text s!"{c}" :: args) .line)

partial def Inline.reprPrec [Repr g.Inline] (inline : Inline g) (prec : Nat) : Std.Format :=
    open Repr Std.Format in
    let rec go i p :=
      (addAppParen · p) <|
        match i with
        | .text str => reprCtor ``Inline.text [reprArg str]
        | .emph content => reprCtor ``Inline.emph [reprArray go content]
        | .bold content => reprCtor ``Inline.bold [reprArray go content]
        | .code str => reprCtor ``Inline.code [reprArg str]
        | .math mode str => reprCtor ``Inline.math [reprArg mode, reprArg str]
        | .linebreak str => reprCtor ``Inline.linebreak [reprArg str]
        | .link content dest => reprCtor ``Inline.link [
            reprArray go content,
            reprArg dest
          ]
        | .footnote name content => reprCtor ``Inline.footnote [reprArg name, reprArray go content]
        | .image content dest => reprCtor ``Inline.image [
            reprArg content,
            reprArg dest
          ]
        | .concat content => reprCtor ``Inline.concat [reprArray go content]
        | .other container content => reprCtor ``Inline.other [reprArg container, reprArray go content]
    go inline prec


instance [Repr g.Inline] : Repr (Inline g) where
  reprPrec := Inline.reprPrec

def Inline.cast (inlines_eq : g1.Inline = g2.Inline) : Inline g1 → Inline g2
  | .other i xs => .other (inlines_eq ▸ i) (xs.map (cast inlines_eq))
  | .concat xs => .concat (xs.map (cast inlines_eq))
  | .bold xs => .bold (xs.map (cast inlines_eq))
  | .emph xs => .emph (xs.map (cast inlines_eq))
  | .link xs href => .link (xs.map (cast inlines_eq)) href
  | .footnote ref xs => .footnote ref (xs.map (cast inlines_eq))
  | .image x y => .image x y
  | .code x => .code x
  | .text x => .text x
  | .linebreak x => .linebreak x
  | .math x y => .math x y

open Lean in
inductive ArgVal where
  | name (x : Ident)
  | str (text : StrLit)
  | num (n : NumLit)
deriving Repr, Inhabited, BEq

def ArgVal.syntax (argVal : ArgVal) : Lean.Syntax :=
  match argVal with
  | .name x => x
  | .str txt => txt
  | .num n => n

open Lean in
inductive Arg where
  | anon (value : ArgVal)
  | named (stx : Syntax) (name : Ident) (value : ArgVal)
deriving Repr, Inhabited, BEq

open Lean in
def Arg.syntax : Arg → Syntax
  | .anon v => v.syntax
  | .named stx _ _ => stx

structure ListItem (α : Type u) where
  contents : Array α
deriving Repr, BEq, Inhabited

private def ListItem.toJson (blockToJson : ToJson α) : ListItem α → Json
  | ⟨xs⟩ => json% {"contents": $(xs.map blockToJson.toJson)}

instance [inst : ToJson α] : ToJson (ListItem α) := ⟨ListItem.toJson inst⟩

def ListItem.reprPrec [Repr α] : ListItem α → Nat → Std.Format := Repr.reprPrec

structure DescItem (α : Type u) (β : Type v) where
  term : Array α
  desc : Array β
deriving Repr, BEq, Inhabited

private def DescItem.toJson (inlineToJson : ToJson α) (blockToJson : ToJson β) : DescItem α β → Json
  | ⟨term, desc⟩ => json% {"term": $(term.map inlineToJson.toJson), "contents": $(desc.map blockToJson.toJson)}

instance [inst : ToJson α] : ToJson (ListItem α) := ⟨ListItem.toJson inst⟩


def DescItem.reprPrec [Repr α] [Repr β] : DescItem α β → Nat → Std.Format := Repr.reprPrec

inductive Block (genre : Genre) : Type where
  | para (contents : Array (Inline genre))
  | code (content : String)
  | ul (items : Array (ListItem (Block genre)))
  | ol (start : Int) (items : Array (ListItem (Block genre)))
  | dl (items : Array (DescItem (Inline genre) (Block genre)))
  | blockquote (items : Array (Block genre))
  | concat (content : Array (Block genre))
  | other (container : genre.Block) (content : Array (Block genre))
deriving Inhabited

instance : Append (Block genre) where
  append
    | .concat #[], x => x
    | x, .concat #[] => x
    | .concat xs, .concat ys => .concat (xs ++ ys)
    | .concat xs, x => .concat (xs.push x)
    | x, .concat xs => .concat (#[x] ++ xs)
    | x, y => .concat #[x, y]

def Block.empty : Block genre := .concat #[]

private partial def Block.toJson [ToJson genre.Inline] [ToJson genre.Block] : Block genre → Json
  | .para contents => json% {"para": $contents}
  | .code content => json%{"code": $content}
  | .ul items => json% {"ul": $(items.map (ListItem.toJson ⟨Block.toJson⟩))}
  | .ol start items => json% {"ol": {"start": $start, "items": $(items.map (ListItem.toJson ⟨Block.toJson⟩))}}
  | .dl items => json% {"dl": $(items.map (DescItem.toJson ⟨Inline.toJson⟩ ⟨Block.toJson⟩))}
  | .blockquote content => json% {"blockquote": $(content.map toJson)}
  | .concat content => json% {"concat": $(content.map toJson)}
  | .other container content => json% {"other": {"container": $container, "content": $(content.map toJson)}}

instance [ToJson genre.Inline] [ToJson genre.Block] : ToJson (Block genre) := ⟨Block.toJson⟩

partial def Block.beq [BEq genre.Inline] [BEq genre.Block] : Block genre → Block genre → Bool
  | .para c1, .para c2 => c1 == c2
  | .code c1, .code c2 => c1 == c2
  | .ul i1, .ul i2 => arrayEq (fun | ⟨c1⟩, ⟨c2⟩ => arrayEq beq c1 c2) i1 i2
  | .ol n1 i1, .ol n2 i2 => n1 == n2 && arrayEq (fun | ⟨c1⟩, ⟨c2⟩ => arrayEq beq c1 c2) i1 i2
  | .dl i1, .dl i2 =>
    arrayEq (fun | ⟨t1, d1⟩, ⟨t2, d2⟩ => t1 == t2 && arrayEq beq d1 d2) i1 i2
  | .blockquote i1, .blockquote i2 => arrayEq beq i1 i2
  | .concat c1, .concat c2 => arrayEq beq c1 c2
  | .other b1 c1, .other b2 c2 => b1 == b2 && arrayEq beq c1 c2
  | _, _ => false

instance [BEq genre.Inline] [BEq genre.Block] : BEq (Block genre) := ⟨Block.beq⟩

partial def Block.reprPrec [Repr g.Inline] [Repr g.Block] (inline : Block g) (prec : Nat) : Std.Format :=
    open Repr Std.Format in
    let rec go i p :=
      (addAppParen · p) <|
        match i with
        | para contents => reprCtor ``Block.para [reprArg contents]
        | code content => reprCtor ``Block.code [reprArg content]
        | ul items => reprCtor ``Block.ul [reprArray (@ListItem.reprPrec _ ⟨go⟩) items]
        | ol start items => reprCtor ``Block.ol [reprArg start, reprArray (@ListItem.reprPrec _ ⟨go⟩) items]
        | dl items => reprCtor ``Block.dl [reprArray (@DescItem.reprPrec _ _ _ ⟨go⟩) items]
        | blockquote items => reprCtor ``Block.blockquote [reprArray go items]
        | concat content => reprCtor ``Block.concat [reprArray go content]
        | other container content => reprCtor ``Block.other [reprArg container, reprArray go content]
    go inline prec

instance [Repr g.Inline] [Repr g.Block] : Repr (Block g) where
  reprPrec b p := Block.reprPrec b p

partial def Block.cast (inlines_eq : g1.Inline = g2.Inline) (blocks_eq : g1.Block = g2.Block) : Block g1 → Block g2
  | .para xs => .para (xs.map (Inline.cast inlines_eq))
  | .code x => .code x
  | .ul xs => .ul (xs.map fun ⟨ys⟩ => ⟨ys.map (Block.cast inlines_eq blocks_eq)⟩)
  | .ol n xs => .ol n (xs.map fun ⟨ys⟩ => ⟨ys.map (Block.cast inlines_eq blocks_eq)⟩)
  | .dl xs => .dl (xs.map fun ⟨dt, dd⟩ => ⟨dt.map (Inline.cast inlines_eq), dd.map (Block.cast inlines_eq blocks_eq)⟩)
  | .blockquote x => .blockquote (x.map (cast inlines_eq blocks_eq))
  | .concat xs => .concat (xs.map (cast inlines_eq blocks_eq))
  | .other x xs => .other (blocks_eq ▸ x) (xs.map (cast inlines_eq blocks_eq))


inductive Part (genre : Genre) : Type where
  | mk (title : Array (Inline genre)) (titleString : String) (metadata : Option genre.PartMetadata) (content : Array (Block genre)) (subParts : Array (Part genre))
deriving Inhabited

partial def Part.beq [BEq genre.Inline] [BEq genre.Block] [BEq genre.PartMetadata] : Part genre → Part genre → Bool
  | .mk t1 ts1 m1 c1 s1, .mk t2 ts2 m2 c2 s2 =>
    t1 == t2 && ts1 == ts2 && m1 == m2 && c1 == c2 && arrayEq beq s1 s2

instance [BEq genre.Inline] [BEq genre.Block] [BEq genre.PartMetadata] : BEq (Part genre) := ⟨Part.beq⟩

def Part.title : Part genre → Array (Inline genre)
  | .mk title .. => title
def Part.titleString : Part genre → String
  | .mk _ titleString .. => titleString
def Part.metadata : Part genre → Option genre.PartMetadata
  | .mk _ _ metadata .. => metadata
def Part.content  : Part genre → Array (Block genre)
  | .mk _ _ _ content .. => content
def Part.subParts : Part genre → Array (Part genre)
  | .mk _ _ _ _ subParts => subParts

def Part.withoutSubparts : Part genre → Part genre
  | .mk title titleString meta content _ => .mk title titleString meta content #[]

def Part.withSubparts : Part genre → Array (Part genre) → Part genre
  | .mk title titleString meta content _, newSubs => .mk title titleString meta content newSubs

def Part.withoutMetadata : Part genre → Part genre
  | .mk title titleString _ content subParts => .mk title titleString none content subParts

def Part.withMetadata (part : Part genre) (newMeta : genre.PartMetadata) : Part genre :=
  match part with
  | .mk title titleString _ content subParts => .mk title titleString (some newMeta) content subParts


partial def Part.reprPrec [Repr g.Inline] [Repr g.Block] [Repr g.PartMetadata] (part : Part g) (_prec : Nat) : Std.Format :=
  open Std.Format in
  reprCtor ``Part.mk [
      reprArg part.title,
      reprArg part.titleString,
      reprArg part.metadata,
      reprArg part.content,
      reprArray Part.reprPrec part.subParts
    ]

instance [Repr g.Inline] [Repr g.Block] [Repr g.PartMetadata] : Repr (Part g) := ⟨Part.reprPrec⟩

class TraversePart (g : Genre) where
  /--
  How to modify the context while traversing the contents a given part.
  This is applied after `part` and `genrePart` have rewritten the text, if applicable.

  It is also used during HTML generation.
  -/
  inPart : Part g → g.TraverseContext → g.TraverseContext := fun _ => id

instance : TraversePart .none := {}

/--
Genre-specific traversal.

The traversal pass is where cross-references are resolved. The traversal pass repeatedly applies a
genre-specific stateful computation until a fixed point is reached, both with respect to the state
and the document. Traversal may update the state or rewrite parts of the document.

The methods `part`, `block`, and `inline` provide effects to be carried out before traversing the
given level of the AST, and `part` allows the part's metadata to be updated.

`genrePart` is carried out after `part`. It allows genre-specific rewriting of the entire part based
on genre-specific metadata. This is typically used to construct a table of contents or permalinks,
but it can in principle arbitrarily rewrite the part. `inPart` is used to locally transform the
genre's traversal context along the lines of `withReader`, and can be used to keep track of e.g. the
current position in the table of contents.

`genreBlock` and `genreInline` are invoked when traversal encounters `Block.other` and
`Inline.other`. It may rewrite them, or have state effects.

-/
class Traverse (g : Genre) (m : outParam (Type → Type)) where
  part [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : Part g → m (Option g.PartMetadata)
  block [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : Block g → m Unit
  inline [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : Inline g → m Unit
  genrePart [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : g.PartMetadata → Part g → m (Option (Part g))
  genreBlock [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : g.Block → Array (Block g) → m (Option (Block g))
  genreInline [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : g.Inline → Array (Inline g) → m (Option (Inline g))



partial def Genre.traverse (g : Genre)
    [Traverse g m] [TraversePart g] [Monad m]
    [MonadReader g.TraverseContext m] [MonadWithReader g.TraverseContext m]
    [MonadState g.TraverseState m]
    (top : Part g) : m (Part g) :=
  part top

where
  inline (i : Doc.Inline g) : m (Doc.Inline g) := do
    Traverse.inline i
    match i with
    | .emph content => .emph <$> content.mapM inline
    | .bold content => .bold <$> content.mapM inline
    | .link content ref => (.link · ref) <$> content.mapM inline
    | .footnote name content => .footnote name <$> content.mapM inline
    | .image alt ref => pure <| .image alt ref
    | .concat content => .concat <$> content.mapM inline
    | .other container content => do
      match ← Traverse.genreInline container content with
      | .none => .other container <$> content.mapM inline
      | .some i' => inline i'
    | .text .. | .linebreak .. | .code .. | .math .. => pure i

  block (b : Doc.Block g) : m (Doc.Block g) := do
    Traverse.block b
    match b with
    | .para contents => .para <$> contents.mapM inline
    | .ul items => .ul <$> items.mapM fun
      | ListItem.mk contents => ListItem.mk <$> contents.mapM block
    | .ol start items => .ol start <$> items.mapM fun
      | ListItem.mk contents => ListItem.mk <$> contents.mapM block
    | .dl items => .dl <$> items.mapM fun
      | DescItem.mk t d => DescItem.mk <$> t.mapM inline <*> d.mapM block
    | .blockquote items => .blockquote <$> items.mapM block
    | .concat items => .concat <$> items.mapM block
    | .other container content =>
      match ← Traverse.genreBlock container content with
      | .none => .other container <$> content.mapM block
      | .some b' => block b'
    | .code .. => pure b

  part (p : Doc.Part g) : m (Doc.Part g) := do
    let meta' ← Traverse.part p
    let mut p := meta'.map p.withMetadata |>.getD p
    if let some md := p.metadata then
      if let some p' ← Traverse.genrePart md p then
        p := p'
    let .mk title titleString meta content subParts := p
    let (content', subParts') ← withReader (TraversePart.inPart p) <|
      (·,·) <$> content.mapM block <*> subParts.mapM part
    pure <| .mk (← title.mapM inline) titleString meta content' subParts'
