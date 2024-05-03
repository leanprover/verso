/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json

namespace Verso

namespace Doc

open Std (Format)
open Lean (Name Json ToJson FromJson)
open Lean.Json (getObj?)

def docName (moduleName : Name) : Name :=
  id <| .str moduleName "the canonical document object name"
where
  absolutize : Name → Name
    | .anonymous => .anonymous
    | .num ns i => .num (absolutize ns) i
    | n@(.str .anonymous "_root_") => n
    | .str .anonymous other => .str (.str .anonymous "_root_") other
    | .str ns n => .str (absolutize ns) n

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
deriving Repr, BEq, Hashable, ToJson, FromJson

private def arrayEq (eq : α → α → Bool) (xs ys : Array α) : Bool := Id.run do
    if h : xs.size = ys.size then
      for h' : i in [0:xs.size] do
        have : i < ys.size := by
          let ⟨_, h''⟩ := h'
          simp [*] at h''; assumption
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
  | .math m1 str1, .math m2 str2 => m1 == m1 && str1 == str2
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

structure ListItem (α : Type u) where
  indent : Nat
  contents : Array α
deriving Repr, BEq

private def ListItem.toJson (blockToJson : ToJson α) : ListItem α → Json
  | ⟨i, xs⟩ => json% {"indent": $i, "contents": $(xs.map blockToJson.toJson)}

instance [inst : ToJson α] : ToJson (ListItem α) := ⟨ListItem.toJson inst⟩

def ListItem.reprPrec [Repr α] : ListItem α → Nat → Std.Format := Repr.reprPrec

structure DescItem (α : Type u) (β : Type v) where
  term : Array α
  desc : Array β
deriving Repr, BEq

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
  | .ul i1, .ul i2 => arrayEq (fun | ⟨indent1, c1⟩, ⟨indent2, c2⟩ => indent1 == indent2 && arrayEq beq c1 c2) i1 i2
  | .ol n1 i1, .ol n2 i2 => n1 == n2 && arrayEq (fun | ⟨indent1, c1⟩, ⟨indent2, c2⟩ => indent1 == indent2 && arrayEq beq c1 c2) i1 i2
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

def Part.withoutMetadata : Part genre → Part genre
  | .mk title titleString _ content subParts => .mk title titleString none content subParts

def Part.withMetadata (part : Part genre) (newMeta : genre.PartMetadata) : Part genre :=
  match part with
  | .mk title titleString _ content subParts => .mk title titleString (some newMeta) content subParts


partial def Part.reprPrec [Repr g.Inline] [Repr g.Block] [Repr g.PartMetadata] (part : Part g) (prec : Nat) : Std.Format :=
  open Std.Format in
  reprCtor ``Part.mk [
      reprArg part.title,
      reprArg part.titleString,
      reprArg part.metadata,
      reprArg part.content,
      reprArray Part.reprPrec part.subParts
    ]

instance [Repr g.Inline] [Repr g.Block] [Repr g.PartMetadata] : Repr (Part g) := ⟨Part.reprPrec⟩

class Traverse (g : Genre) (m : outParam (Type → Type)) where
  part [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : Part g → m (Option g.PartMetadata)
  block [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : Block g → m Unit
  inline [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : Inline g → m Unit
  genrePart [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : g.PartMetadata → Part g → m (Option (Part g))
  genreBlock [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : g.Block → Array (Block g) → m (Option (Block g))
  genreInline [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : g.Inline → Array (Inline g) → m (Option (Inline g))



partial def Genre.traverse (g : Genre)
    [Traverse g m] [Monad m] [MonadReader g.TraverseContext m] [MonadState g.TraverseState m]
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
      | ListItem.mk n contents => ListItem.mk n <$> contents.mapM block
    | .ol start items => .ol start <$> items.mapM fun
      | ListItem.mk n contents => ListItem.mk n <$> contents.mapM block
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
    pure <| .mk (← title.mapM inline) titleString meta (← content.mapM block) (← subParts.mapM part)
