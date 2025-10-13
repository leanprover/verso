/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean.Data.Json
import Lean.DocString.Types
import Verso.Doc.Name

namespace Verso

namespace Doc

open Std (Format)
open Lean (Name Json ToJson FromJson)
open Lean.Json (getObj?)

/--
A genre is a kind of document that can be written with Verso.

A genre is primarily defined by its extensions to the Verso framework, provided in this type.
Additionally, each genre should provide a `main` function that is responsible for the traversal pass
and for generating output.
-/
structure Genre : Type 1 where
  /--
  The metadata that may be associated with each `Part` (e.g. author, publication date,
  cross-referencing identifier).
  -/
  PartMetadata : Type
  /--
  Additional block-level values for documents written in the genre.
  -/
  Block : Type
  /--
  Additional inline-level values for documents written in the genre.
  -/
  Inline : Type
  /--
  The reader-style data used in the genre's traversal pass. Instances of `TraversePart` and
  `TraverseBlock` for a genre specify how this is updated while traversing parts and blocks,
  respectively.
  -/
  TraverseContext : Type
  /--
  The mutable state used in the genre's traversal pass.
  -/
  TraverseState : Type

def Genre.none : Genre := ⟨Empty, Empty, Empty, Unit, Unit⟩

instance : BEq Genre.none.Block where
  beq e _ := nomatch e

instance : BEq Genre.none.PartMetadata where
  beq e _ := nomatch e

instance : BEq Genre.none.Inline where
  beq e _ := nomatch e

instance : Repr Genre.none.Block where
  reprPrec e _ := nomatch e

instance : Repr Genre.none.Inline where
  reprPrec e _ := nomatch e

instance : Repr Genre.none.PartMetadata where
  reprPrec e _ := nomatch e

export Lean.Doc (MathMode MathMode.inline MathMode.display)

deriving instance ToJson, FromJson for MathMode

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

@[inherit_doc Lean.Doc.Inline]
abbrev Inline (genre : Genre) :=
  Lean.Doc.Inline genre.Inline

@[inherit_doc Lean.Doc.Inline.text, match_pattern]
def Inline.text (string : String) : Inline genre :=
  Lean.Doc.Inline.text (string : String)

@[inherit_doc Lean.Doc.Inline.emph, match_pattern]
def Inline.emph (content : Array (Inline genre)) : Inline genre :=
  Lean.Doc.Inline.emph (content : Array (Inline genre))

@[inherit_doc Lean.Doc.Inline.bold, match_pattern]
def Inline.bold (content : Array (Inline genre)) : Inline genre :=
  Lean.Doc.Inline.bold (content : Array (Inline genre))

@[inherit_doc Lean.Doc.Inline.code, match_pattern]
def Inline.code (string : String) : Inline genre :=
  Lean.Doc.Inline.code (string : String)

@[inherit_doc Lean.Doc.Inline.math, match_pattern]
def Inline.math (mode : MathMode) (string : String) : Inline genre :=
  Lean.Doc.Inline.math (mode : MathMode) (string : String)

@[inherit_doc Lean.Doc.Inline.linebreak, match_pattern]
def Inline.linebreak (string : String) : Inline genre :=
  Lean.Doc.Inline.linebreak (string : String)

@[inherit_doc Lean.Doc.Inline.link, match_pattern]
def Inline.link (content : Array (Inline genre)) (url : String) : Inline genre :=
  Lean.Doc.Inline.link (content : Array (Inline genre)) (url : String)

@[inherit_doc Lean.Doc.Inline.footnote, match_pattern]
def Inline.footnote (name : String) (content : Array (Inline genre)) : Inline genre :=
  Lean.Doc.Inline.footnote (name : String) (content : Array (Inline genre))

@[inherit_doc Lean.Doc.Inline.image, match_pattern]
def Inline.image (alt : String) (url : String) : Inline genre :=
  Lean.Doc.Inline.image (alt : String) (url : String)

@[inherit_doc Lean.Doc.Inline.concat, match_pattern]
def Inline.concat (content : Array (Inline genre)) : Inline genre :=
  Lean.Doc.Inline.concat (content : Array (Inline genre))

@[inherit_doc Lean.Doc.Inline.other, match_pattern]
def Inline.other (container : genre.Inline) (content : Array (Inline genre)) : Inline genre :=
  Lean.Doc.Inline.other (container : genre.Inline) (content : Array (Inline genre))


def Inline.empty : Inline genre := .concat #[]

private partial def Inline.toJson [ToJson i] : Lean.Doc.Inline i → Json
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

instance instToJsonLeanInline [ToJson i] : ToJson (Lean.Doc.Inline i) where
  toJson := Inline.toJson

@[instance] abbrev instToJsonInline [ToJson genre.Inline] : ToJson (Inline genre) := instToJsonLeanInline

private partial def Inline.fromJson? [inst : FromJson i] (json : Json) : Except String (Lean.Doc.Inline i) := do
  let obj ← json.getObj?
  if let #[⟨k, v⟩] := obj.toArray then
    match k with
    | "text" => .text <$> FromJson.fromJson? v
    | "emph" =>
      let arr : Array Json ← FromJson.fromJson? v
      .emph <$> arr.mapM fromJson?
    | "bold" =>
      let arr : Array Json ← FromJson.fromJson? v
      .bold <$> arr.mapM fromJson?
    | "code" => .code <$> FromJson.fromJson? v
    | "math" => .math <$> FromJson.fromJson? (← v.getObjVal? "mode") <*> FromJson.fromJson? (← v.getObjVal? "str")
    | "linebreak" => .linebreak <$> FromJson.fromJson? v
    | "link" =>
      let arr : Array Json ← v.getObjValAs? (Array Json) "content"
      .link <$> arr.mapM fromJson? <*> FromJson.fromJson? (← v.getObjVal? "url")
    | "footnote" =>
      let arr : Array Json ← v.getObjValAs? (Array Json) "content"
      .footnote <$> FromJson.fromJson? (← v.getObjVal? "name") <*> arr.mapM fromJson?
    | "image" =>
      .image <$> FromJson.fromJson? (← v.getObjVal? "alt") <*> FromJson.fromJson? (← v.getObjVal? "url")
    | "concat" =>
      let arr : Array Json ← FromJson.fromJson? v
      .concat <$> arr.mapM fromJson?
    | "other" =>
      let arr : Array Json ← v.getObjValAs? (Array Json) "content"
      .other <$> inst.fromJson? (← v.getObjVal? "container") <*> arr.mapM fromJson?
    | nonKey => throw s!"Expected a key that's a constructor name of 'Inline', got '{nonKey}'"
  else
    throw "Expected a one-field object"

instance instFromJsonLeanInline [FromJson i] : FromJson (Lean.Doc.Inline i) where
  fromJson? := Inline.fromJson?

@[instance] abbrev instFromJsonInline [FromJson genre.Inline] : FromJson (Inline genre) := instFromJsonLeanInline

partial def Inline.beq [BEq i] : Lean.Doc.Inline i → Lean.Doc.Inline i → Bool
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

instance instBEqLeanInline [BEq i] : BEq (Lean.Doc.Inline i) := ⟨Inline.beq⟩

@[instance] abbrev instBEqInline [BEq genre.Inline] : BEq (Inline genre) := instBEqLeanInline

private partial def Inline.hashCode [Hashable i] : Lean.Doc.Inline i → UInt64
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

instance instHashableLeanInline [Hashable i] : Hashable (Lean.Doc.Inline i) where
  hash := Inline.hashCode

@[instance] abbrev instHashableInline [Hashable genre.Inline] : Hashable (Inline genre) :=
  instHashableLeanInline

@[instance] abbrev instOrdInline [Ord genre.Inline] : Ord (Inline genre) :=
  inferInstanceAs (Ord (Lean.Doc.Inline genre.Inline))

private def reprArray (r : α → Nat → Format) (arr : Array α) : Format :=
  .bracket "#[" (.joinSep (arr.toList.map (r · max_prec)) ("," ++ .line)) "]"

private def reprList (r : α → Nat → Format) (xs : List α) : Format :=
  .bracket "[" (.joinSep (xs.map (r · max_prec)) ("," ++ .line)) "]"

private def reprPair (x : α → Nat → Format) (y : β → Nat → Format) (v : α × β) : Format :=
  .bracket "(" (x v.fst max_prec ++ ("," ++.line) ++ y v.snd max_prec) ")"

private def reprCtor (c : Name) (args : List Format) : Format :=
  .nest 2 <| .group (.joinSep (.text s!"{c}" :: args) .line)

-- The Lean instance exists, but shows the Lean constructor names instead of the Verso ones
partial def Inline.reprPrec [Repr genre.Inline] (inline : Inline genre) (prec : Nat) : Std.Format :=
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

instance [Repr g.Inline] : Repr (Inline g) := ⟨Inline.reprPrec⟩


def Inline.cast (inlines_eq : g1.Inline = g2.Inline) : Inline g1 → Inline g2 :=
  Lean.Doc.Inline.cast inlines_eq

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
  | flag (stx : Syntax) (name : Ident) (value : Bool)
deriving Repr, Inhabited, BEq

open Lean in
def Arg.syntax : Arg → Syntax
  | .anon v => v.syntax
  | .named stx .. | .flag stx .. => stx


export Lean.Doc (ListItem ListItem.mk)

private def ListItem.toJson (blockToJson : ToJson α) : ListItem α → Json
  | ⟨xs⟩ => json% {"contents": $(xs.map blockToJson.toJson)}

instance [inst : ToJson α] : ToJson (ListItem α) := ⟨ListItem.toJson inst⟩

def ListItem.reprPrec [Repr α] : ListItem α → Nat → Std.Format := Repr.reprPrec

export Lean.Doc (DescItem DescItem.mk)

private def DescItem.toJson (inlineToJson : ToJson α) (blockToJson : ToJson β) : DescItem α β → Json
  | ⟨term, desc⟩ => json% {"term": $(term.map inlineToJson.toJson), "contents": $(desc.map blockToJson.toJson)}

instance [inst : ToJson α] : ToJson (ListItem α) := ⟨ListItem.toJson inst⟩

def DescItem.reprPrec [Repr α] [Repr β] : DescItem α β → Nat → Std.Format := Repr.reprPrec

@[inherit_doc Lean.Doc.Block]
abbrev Block (genre : Genre) : Type :=
  Lean.Doc.Block genre.Inline genre.Block

@[inherit_doc Lean.Doc.Block.para, match_pattern]
def Block.para (contents : Array (Inline genre)) : Block genre :=
  Lean.Doc.Block.para (contents : Array (Inline genre))

@[inherit_doc Lean.Doc.Block.code, match_pattern]
def Block.code (content : String) : Block genre :=
  Lean.Doc.Block.code (content : String)

@[inherit_doc Lean.Doc.Block.ul, match_pattern]
def Block.ul (items : Array (ListItem (Block genre))) : Block genre :=
  Lean.Doc.Block.ul (items : Array (ListItem (Block genre)))

@[inherit_doc Lean.Doc.Block.ol, match_pattern]
def Block.ol (start : Int) (items : Array (ListItem (Block genre))) : Block genre :=
  Lean.Doc.Block.ol (start : Int) (items : Array (ListItem (Block genre)))

@[inherit_doc Lean.Doc.Block.dl, match_pattern]
def Block.dl (items : Array (DescItem (Inline genre) (Block genre))) : Block genre :=
  Lean.Doc.Block.dl (items : Array (DescItem (Inline genre) (Block genre)))

@[inherit_doc Lean.Doc.Block.blockquote, match_pattern]
def Block.blockquote (items : Array (Block genre)) : Block genre :=
  Lean.Doc.Block.blockquote (items : Array (Block genre))

@[inherit_doc Lean.Doc.Block.concat, match_pattern]
def Block.concat (content : Array (Block genre)) : Block genre :=
  Lean.Doc.Block.concat (content : Array (Block genre))

@[inherit_doc Lean.Doc.Block.other, match_pattern]
def Block.other (container : genre.Block) (content : Array (Block genre)) : Block genre :=
  Lean.Doc.Block.other (container : genre.Block) (content : Array (Block genre))

instance : Append (Lean.Doc.Block i b) where
  append
    | .concat #[], x => x
    | x, .concat #[] => x
    | .concat xs, .concat ys => .concat (xs ++ ys)
    | .concat xs, x => .concat (xs.push x)
    | x, .concat xs => .concat (#[x] ++ xs)
    | x, y => .concat #[x, y]

@[instance] abbrev instAppendBlock : Append (Block genre) :=
  inferInstanceAs (Append (Lean.Doc.Block genre.Inline genre.Block))

def Block.empty : Block genre := .concat #[]

private partial def Block.toJson [ToJson i] [ToJson b] : Lean.Doc.Block i b → Json
  | .para contents => json% {"para": $contents}
  | .code content => json%{"code": $content}
  | .ul items => json% {"ul": $(items.map (ListItem.toJson ⟨Block.toJson⟩))}
  | .ol start items => json% {"ol": {"start": $start, "items": $(items.map (ListItem.toJson ⟨Block.toJson⟩))}}
  | .dl items => json% {"dl": $(items.map (DescItem.toJson ⟨Inline.toJson⟩ ⟨Block.toJson⟩))}
  | .blockquote content => json% {"blockquote": $(content.map toJson)}
  | .concat content => json% {"concat": $(content.map toJson)}
  | .other container content => json% {"other": {"container": $container, "content": $(content.map toJson)}}

instance instToJsonLeanBlock [ToJson i] [ToJson b] : ToJson (Lean.Doc.Block i b) := ⟨Block.toJson⟩

@[instance] abbrev instToJsonBLock [ToJson genre.Inline] [ToJson genre.Block] : ToJson (Block genre) :=
  instToJsonLeanBlock

partial def Block.beq [BEq i] [BEq b] : Lean.Doc.Block i b → Lean.Doc.Block i b → Bool
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

instance instBEqLeanBlock [BEq genre.Inline] [BEq genre.Block] : BEq (Block genre) := ⟨Block.beq⟩

@[instance] abbrev instBEqBlock [BEq genre.Inline] [BEq genre.Block] : BEq (Block genre) := instBEqLeanBlock

-- Upstream has an instance, but the constructor names are the Lean ones rather than the Verso ones
partial def Block.reprPrec [Repr genre.Inline] [Repr genre.Block] (inline : Block genre) (prec : Nat) : Std.Format :=
    open Repr Std.Format in
    open Lean.Doc in
    let rec go i p :=
      (addAppParen · p) <|
        match i with
        | .para contents => reprCtor ``Block.para [reprArg contents]
        | .code content => reprCtor ``Block.code [reprArg content]
        | .ul items => reprCtor ``Block.ul [reprArray (@ListItem.reprPrec _ ⟨go⟩) items]
        | .ol start items => reprCtor ``Block.ol [reprArg start, reprArray (@ListItem.reprPrec _ ⟨go⟩) items]
        | .dl items => reprCtor ``Block.dl [reprArray (@DescItem.reprPrec _ _ _ ⟨go⟩) items]
        | .blockquote items => reprCtor ``Block.blockquote [reprArray go items]
        | .concat content => reprCtor ``Block.concat [reprArray go content]
        | .other container content => reprCtor ``Block.other [reprArg container, reprArray go content]
    go inline prec

instance [Repr g.Inline] [Repr g.Block] : Repr (Block g) where
  reprPrec b p := Block.reprPrec b p


def Block.cast (inlines_eq : g1.Inline = g2.Inline) (blocks_eq : g1.Block = g2.Block) : Block g1 → Block g2 :=
  Lean.Doc.Block.cast inlines_eq blocks_eq

@[inherit_doc Lean.Doc.Part]
abbrev Part (genre : Genre) := Lean.Doc.Part genre.Inline genre.Block genre.PartMetadata

@[match_pattern]
def Part.mk
    (title : Array (Inline genre))
    (titleString : String)
    (metadata : Option genre.PartMetadata)
    (content : Array (Block genre))
    (subParts : Array (Part genre)) : Part genre :=
  Lean.Doc.Part.mk title titleString metadata content subParts

@[inherit_doc Lean.Doc.Part.title]
abbrev Part.title : Part genre → Array (Inline genre) := Lean.Doc.Part.title

@[inherit_doc Lean.Doc.Part.titleString]
abbrev Part.titleString : Part genre → String := Lean.Doc.Part.titleString

@[inherit_doc Lean.Doc.Part.metadata]
abbrev Part.metadata : Part genre → Option genre.PartMetadata := Lean.Doc.Part.metadata

@[inherit_doc Lean.Doc.Part.content]
abbrev Part.content : Part genre → Array (Block genre) := Lean.Doc.Part.content

@[inherit_doc Lean.Doc.Part.subParts]
abbrev Part.subParts : Part genre → Array (Part genre) := Lean.Doc.Part.subParts


@[instance]
abbrev instBEqPart [BEq genre.Inline] [BEq genre.Block] [BEq genre.PartMetadata] : BEq (Part genre) :=
  inferInstanceAs (BEq (Lean.Doc.Part genre.Inline genre.Block genre.PartMetadata))

def Part.withoutSubparts (p : Part genre) : Part genre := { p with subParts := #[] }

def Part.withoutMetadata (p : Part genre) : Part genre := { p with metadata := none }

partial def Part.reprPrec [Repr genre.Inline] [Repr genre.Block] [Repr genre.PartMetadata] (part : Part genre) (_prec : Nat) : Std.Format :=
  open Std.Format in
  reprCtor ``Part.mk [
      reprArg (part.title : Array (Inline genre)),
      reprArg part.titleString,
      reprArg (part.metadata : Option genre.PartMetadata),
      reprArg (part.content : Array (Block genre)),
      reprArray Part.reprPrec (part.subParts : Array (Part genre))
    ]

instance [Repr g.Inline] [Repr g.Block] [Repr g.PartMetadata] : Repr (Part g) := ⟨Part.reprPrec⟩

/--
Specifies how to modify the context while traversing the contents of a given part.
-/
class TraversePart (g : Genre) where
  /--
  How to modify the context while traversing the contents of a given part. This is applied after
  `part` and `genrePart` have rewritten the text, if applicable.

  It is also used during HTML generation.
  -/
  inPart : Part g → g.TraverseContext → g.TraverseContext := fun _ => id

/--
Specifies how to modify the context while traversing the contents of a given block.
-/
class TraverseBlock (g : Genre) where
  /--
  How to modify the context while traversing a given block.

  It is also used during HTML generation.
  -/
  inBlock : Block g → g.TraverseContext → g.TraverseContext := fun _ => id


instance : TraversePart .none := {}

instance : TraverseBlock .none := {}

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
  /--
  The effects carried out before traversing a `Part`.
  -/
  part [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : Part g → m (Option g.PartMetadata)
  /--
  The effects carried out before traversing a `Block`.
  -/
  block [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : Block g → m Unit
  /--
  The effects carried out before traversing an `Inline`.
  -/
  inline [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : Inline g → m Unit
  /--
  Operations carried out after `part`, when a part has metadata. It allows genre-specific rewriting
  of the entire part based on genre-specific metadata. This is typically used to construct a table
  of contents or permalinks, but it can in principle arbitrarily rewrite the part. If it returns
  `none`, then no rewrite is performed.
  -/
  genrePart [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : g.PartMetadata → Part g → m (Option (Part g))
  /--
  The traversal of genre-specific block values. If it returns `none`, then no rewrite is performed.
  -/
  genreBlock [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : g.Block → Array (Block g) → m (Option (Block g))
  /--
  The traversal of genre-specific inline values. If it returns `none`, then no rewrite is performed.
  -/
  genreInline [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : g.Inline → Array (Inline g) → m (Option (Inline g))



partial def Genre.traverse (g : Genre)
    [Traverse g m] [TraversePart g] [TraverseBlock g] [Monad m]
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
    withReader (TraverseBlock.inBlock b) <|
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
      | .other container content => do
        match ← Traverse.genreBlock container content with
        | .none => .other container <$> content.mapM block
        | .some b' => block b'
      | .code .. => pure b

  part (p : Doc.Part g) : m (Doc.Part g) := do
    let meta' ← Traverse.part p
    let mut p := meta'.map ({ p with metadata := ·}) |>.getD p
    if let some md := p.metadata then
      if let some p' ← Traverse.genrePart md p then
        p := p'
    let .mk title titleString metadata content subParts := p
    let (content', subParts') ← withReader (TraversePart.inPart p) <|
      (·,·) <$> content.mapM block <*> subParts.mapM part
    pure <| .mk (← title.mapM inline) titleString metadata content' subParts'
