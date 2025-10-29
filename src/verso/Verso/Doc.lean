/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Data.Json
public import Lean.DocString.Types
import Verso.Doc.Name

set_option doc.verso true
set_option pp.rawOnError true

/--
Identify function; this is a temporary compatibility shim to introduce a new type,
VersoDoc, that will have a nontrival toPart method.
-/
@[deprecated "remove or use VersoDoc.toPart" (since := "2025-11-01")]
public def Lean.Doc.Part.toPart (p : Lean.Doc.Part i b p) := p

namespace Verso

namespace Doc

open Std (Format)
open Lean (Name Json ToJson FromJson)
open Lean.Json (getObj?)

/--
A genre is a kind of document that can be written with Verso.

A genre is primarily defined by its extensions to the Verso framework, provided in this type.
Additionally, each genre should provide a {lit}`main` function that is responsible for the traversal pass
and for generating output.
-/
public structure Genre : Type 1 where
  /--
  {open Verso.Doc}

  The metadata that may be associated with each {name scope:="Verso.Doc"}`Part` (e.g. author, publication date,
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
  {open Verso.Doc}

  The reader-style data used in the genre's traversal pass. Instances of {name scope:="Verso.Doc"}`TraversePart` and
  {name scope:="Verso.Doc"}`TraverseBlock` for a genre specify how this is updated while traversing parts and blocks,
  respectively.
  -/
  TraverseContext : Type
  /--
  The mutable state used in the genre's traversal pass.
  -/
  TraverseState : Type

@[expose]
public def Genre.none : Genre := ⟨Empty, Empty, Empty, Unit, Unit⟩

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

deriving instance ToJson, FromJson for Lean.Doc.MathMode

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
public abbrev Inline (genre : Genre) :=
  Lean.Doc.Inline genre.Inline

@[inherit_doc Lean.Doc.Inline.text, expose, match_pattern]
public def Inline.text (string : String) : Inline genre :=
  Lean.Doc.Inline.text (string : String)

@[inherit_doc Lean.Doc.Inline.emph, expose, match_pattern]
public def Inline.emph (content : Array (Inline genre)) : Inline genre :=
  Lean.Doc.Inline.emph (content : Array (Inline genre))

@[inherit_doc Lean.Doc.Inline.bold, expose, match_pattern]
public def Inline.bold (content : Array (Inline genre)) : Inline genre :=
  Lean.Doc.Inline.bold (content : Array (Inline genre))

@[inherit_doc Lean.Doc.Inline.code, expose, match_pattern]
public def Inline.code (string : String) : Inline genre :=
  Lean.Doc.Inline.code (string : String)

@[inherit_doc Lean.Doc.Inline.math, expose, match_pattern]
public def Inline.math (mode : MathMode) (string : String) : Inline genre :=
  Lean.Doc.Inline.math (mode : MathMode) (string : String)

@[inherit_doc Lean.Doc.Inline.linebreak, expose, match_pattern]
public def Inline.linebreak (string : String) : Inline genre :=
  Lean.Doc.Inline.linebreak (string : String)

@[inherit_doc Lean.Doc.Inline.link, expose, match_pattern]
public def Inline.link (content : Array (Inline genre)) (url : String) : Inline genre :=
  Lean.Doc.Inline.link (content : Array (Inline genre)) (url : String)

@[inherit_doc Lean.Doc.Inline.footnote, expose, match_pattern]
public def Inline.footnote (name : String) (content : Array (Inline genre)) : Inline genre :=
  Lean.Doc.Inline.footnote (name : String) (content : Array (Inline genre))

@[inherit_doc Lean.Doc.Inline.image, expose, match_pattern]
public def Inline.image (alt : String) (url : String) : Inline genre :=
  Lean.Doc.Inline.image (alt : String) (url : String)

@[inherit_doc Lean.Doc.Inline.concat, expose, match_pattern]
public def Inline.concat (content : Array (Inline genre)) : Inline genre :=
  Lean.Doc.Inline.concat (content : Array (Inline genre))

@[inherit_doc Lean.Doc.Inline.other, expose, match_pattern]
public def Inline.other (container : genre.Inline) (content : Array (Inline genre)) : Inline genre :=
  Lean.Doc.Inline.other (container : genre.Inline) (content : Array (Inline genre))

public def Inline.empty : Inline genre := .concat #[]

public partial def Inline.rewriteOtherM [Monad m]
    (onInline :
      (Inline genre1 → m (Inline genre2)) →
      genre1.Inline → Array (Inline genre1) →
      m (Inline genre2)) :
    Inline genre1 → m (Inline genre2)
  | .text str => pure <| .text str
  | .linebreak str => pure <| .linebreak str
  | .image alt url => pure <| .image alt url
  | .code s => pure <| .code s
  | .math m s => pure <| .math m s
  | .emph content => .emph <$> content.mapM (rewriteOtherM onInline)
  | .bold content => .bold <$> content.mapM (rewriteOtherM onInline)
  | .concat content => .concat <$> content.mapM (rewriteOtherM onInline)
  | .footnote name content => .footnote name <$> content.mapM (rewriteOtherM onInline)
  | .link content url => (.link · url) <$> content.mapM (rewriteOtherM onInline)
  | .other container content =>
    onInline (rewriteOtherM onInline) container content

public partial def Inline.rewriteOther
    (onInline :
      (Inline genre1 → Inline genre2) →
      genre1.Inline → Array (Inline genre1) →
      Inline genre2) :
    Inline genre1 → Inline genre2 :=
  Inline.rewriteOtherM (m := Id) onInline

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

public instance instToJsonLeanInline [ToJson i] : ToJson (Lean.Doc.Inline i) where
  toJson := private Inline.toJson

@[instance] public abbrev instToJsonInline [ToJson genre.Inline] : ToJson (Inline genre) := instToJsonLeanInline

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

public instance instFromJsonLeanInline [FromJson i] : FromJson (Lean.Doc.Inline i) where
  fromJson? := private Inline.fromJson?

@[instance] abbrev instFromJsonInline [FromJson genre.Inline] : FromJson (Inline genre) := instFromJsonLeanInline

private partial def Inline.beq [BEq i] : Lean.Doc.Inline i → Lean.Doc.Inline i → Bool
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

public instance instBEqLeanInline [BEq i] : BEq (Lean.Doc.Inline i) where
  beq := private Inline.beq

@[instance] public abbrev instBEqInline [BEq genre.Inline] : BEq (Inline genre) := instBEqLeanInline

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

public instance instHashableLeanInline [Hashable i] : Hashable (Lean.Doc.Inline i) where
  hash := private Inline.hashCode

@[instance] public abbrev instHashableInline [Hashable genre.Inline] : Hashable (Inline genre) :=
  instHashableLeanInline

@[instance] public abbrev instOrdInline [Ord genre.Inline] : Ord (Inline genre) :=
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
public partial def Inline.reprPrec [Repr genre.Inline] (inline : Inline genre) (prec : Nat) : Std.Format :=
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

public instance [Repr g.Inline] : Repr (Inline g) := ⟨Inline.reprPrec⟩


public def Inline.cast (inlines_eq : g1.Inline = g2.Inline) : Inline g1 → Inline g2 :=
  Lean.Doc.Inline.cast inlines_eq

open Lean in
public inductive ArgVal where
  | name (x : Ident)
  | str (text : StrLit)
  | num (n : NumLit)
deriving Repr, Inhabited, BEq

public def ArgVal.syntax (argVal : ArgVal) : Lean.Syntax :=
  match argVal with
  | .name x => x
  | .str txt => txt
  | .num n => n

open Lean in
public inductive Arg where
  | anon (value : ArgVal)
  | named (stx : Syntax) (name : Ident) (value : ArgVal)
  | flag (stx : Syntax) (name : Ident) (value : Bool)
deriving Repr, Inhabited, BEq

open Lean in
public def Arg.syntax : Arg → Syntax
  | .anon v => v.syntax
  | .named stx .. | .flag stx .. => stx

export Lean.Doc (ListItem ListItem.mk)

private def ListItem.toJson (blockToJson : ToJson α) : ListItem α → Json
  | ⟨xs⟩ => json% {"contents": $(xs.map blockToJson.toJson)}

public instance [inst : ToJson α] : ToJson (ListItem α) where
  toJson := private ListItem.toJson inst

private def ListItem.fromJson? [FromJson α] (json : Json) : Except String (ListItem α) := do
  let v ← json.getObjVal? "contents"
  .mk <$> FromJson.fromJson? v

private def ListItem.reprPrec [Repr α] : ListItem α → Nat → Std.Format := Repr.reprPrec

public instance [Repr α] : Repr (ListItem α) where
  reprPrec := private ListItem.reprPrec

export Lean.Doc (DescItem DescItem.mk)

private def DescItem.reprPrec [Repr α] [Repr β] : DescItem α β → Nat → Std.Format := Repr.reprPrec

public instance [Repr α] [Repr β] : Repr (DescItem α β) where
  reprPrec := private DescItem.reprPrec


private def DescItem.toJson (inlineToJson : ToJson α) (blockToJson : ToJson β) : DescItem α β → Json
  | ⟨term, desc⟩ => json% {"term": $(term.map inlineToJson.toJson), "contents": $(desc.map blockToJson.toJson)}

private def DescItem.fromJson? [FromJson α] [FromJson β] (json : Json) : Except String (DescItem α β) := do
  let term ← json.getObjVal? "term" >>= (·.getArr?)
  let contents ← json.getObjVal? "contents" >>= (·.getArr?)
  let term ← term.mapM FromJson.fromJson?
  let contents ← contents.mapM FromJson.fromJson?
  return ⟨term, contents⟩

public instance [FromJson α] [FromJson β] : FromJson (DescItem α β) where
  fromJson? := private DescItem.fromJson?

@[inherit_doc Lean.Doc.Block]
public abbrev Block (genre : Genre) : Type :=
  Lean.Doc.Block genre.Inline genre.Block

@[inherit_doc Lean.Doc.Block.para, expose, match_pattern]
public def Block.para (contents : Array (Inline genre)) : Block genre :=
  Lean.Doc.Block.para (contents : Array (Inline genre))

@[inherit_doc Lean.Doc.Block.code, expose, match_pattern]
public def Block.code (content : String) : Block genre :=
  Lean.Doc.Block.code (content : String)

@[inherit_doc Lean.Doc.Block.ul, expose, match_pattern]
public def Block.ul (items : Array (ListItem (Block genre))) : Block genre :=
  Lean.Doc.Block.ul (items : Array (ListItem (Block genre)))

@[inherit_doc Lean.Doc.Block.ol, expose, match_pattern]
public def Block.ol (start : Int) (items : Array (ListItem (Block genre))) : Block genre :=
  Lean.Doc.Block.ol (start : Int) (items : Array (ListItem (Block genre)))

@[inherit_doc Lean.Doc.Block.dl, expose, match_pattern]
public def Block.dl (items : Array (DescItem (Inline genre) (Block genre))) : Block genre :=
  Lean.Doc.Block.dl (items : Array (DescItem (Inline genre) (Block genre)))

@[inherit_doc Lean.Doc.Block.blockquote, expose, match_pattern]
public def Block.blockquote (items : Array (Block genre)) : Block genre :=
  Lean.Doc.Block.blockquote (items : Array (Block genre))

@[inherit_doc Lean.Doc.Block.concat, expose, match_pattern]
public def Block.concat (content : Array (Block genre)) : Block genre :=
  Lean.Doc.Block.concat (content : Array (Block genre))

@[inherit_doc Lean.Doc.Block.other, expose, match_pattern]
public def Block.other (container : genre.Block) (content : Array (Block genre)) : Block genre :=
  Lean.Doc.Block.other (container : genre.Block) (content : Array (Block genre))

public instance : Append (Lean.Doc.Block i b) where
  append
    | .concat #[], x => x
    | x, .concat #[] => x
    | .concat xs, .concat ys => .concat (xs ++ ys)
    | .concat xs, x => .concat (xs.push x)
    | x, .concat xs => .concat (#[x] ++ xs)
    | x, y => .concat #[x, y]

@[instance] public abbrev instAppendBlock : Append (Block genre) :=
  inferInstanceAs (Append (Lean.Doc.Block genre.Inline genre.Block))

public def Block.empty : Block genre := .concat #[]

public partial def Block.rewriteOtherM [Monad m]
    (onInline :
      (Inline genre1 → m (Inline genre2)) →
      genre1.Inline → Array (Inline genre1) → m (Inline genre2))
    (onBlock :
      (Inline genre1 → m (Inline genre2)) →
      (Block genre1 → m (Block genre2)) →
      genre1.Block → Array (Block genre1) → m (Block genre2)) :
    Block genre1 → m (Block genre2)
  | .code s => pure <| .code s
  | .para content => .para <$> content.mapM (·.rewriteOtherM onInline)
  | .blockquote content => .blockquote <$> content.mapM (·.rewriteOtherM onInline onBlock)
  | .concat content => .concat <$> content.mapM (·.rewriteOtherM onInline onBlock)
  | .ol n items => .ol n <$> items.mapM fun ⟨content⟩ => (⟨·⟩) <$> content.mapM (·.rewriteOtherM onInline onBlock)
  | .ul items => .ul <$> items.mapM fun ⟨content⟩ => (⟨·⟩) <$> content.mapM (·.rewriteOtherM onInline onBlock)
  | .dl items => .dl <$> items.mapM fun ⟨term, desc⟩ => (⟨·, ·⟩) <$> term.mapM (·.rewriteOtherM onInline) <*> desc.mapM (·.rewriteOtherM onInline onBlock)
  | .other container content =>
    onBlock (Inline.rewriteOtherM onInline) (Block.rewriteOtherM onInline onBlock) container content

public partial def Block.rewriteOther
    (onInline :
      (Inline genre1 → Inline genre2) →
      genre1.Inline → Array (Inline genre1) → Inline genre2)
    (onBlock :
      (Inline genre1 → Inline genre2) →
      (Block genre1 → Block genre2) →
      genre1.Block → Array (Block genre1) → Block genre2) :
    Block genre1 → Block genre2 :=
  Block.rewriteOtherM (m := Id) onInline onBlock

private partial def Block.toJson [ToJson i] [ToJson b] : Lean.Doc.Block i b → Json
  | .para contents => json% {"para": $contents}
  | .code content => json%{"code": $content}
  | .ul items => json% {"ul": $(items.map (ListItem.toJson ⟨Block.toJson⟩))}
  | .ol start items => json% {"ol": {"start": $start, "items": $(items.map (ListItem.toJson ⟨Block.toJson⟩))}}
  | .dl items => json% {"dl": $(items.map (DescItem.toJson ⟨Inline.toJson⟩ ⟨Block.toJson⟩))}
  | .blockquote content => json% {"blockquote": $(content.map toJson)}
  | .concat content => json% {"concat": $(content.map toJson)}
  | .other container content => json% {"other": {"container": $container, "content": $(content.map toJson)}}

public instance instToJsonLeanBlock [ToJson i] [ToJson b] : ToJson (Lean.Doc.Block i b) where
  toJson := private Block.toJson

@[instance] public abbrev instToJsonBLock [ToJson genre.Inline] [ToJson genre.Block] : ToJson (Block genre) :=
  instToJsonLeanBlock

private partial def Block.fromJson? [FromJson i] [FromJson b] (json : Json) : Except String (Lean.Doc.Block i b) := do
  let vals ← json.getObj?
  if let some v := vals["para"]? then
    .para <$> FromJson.fromJson? v
  else if let some v := vals["code"]? then
    .code <$> FromJson.fromJson? v
  else if let some v := vals["ul"]? then
    let items ← v.getArr?
    have : FromJson (Lean.Doc.Block i b) := ⟨Block.fromJson?⟩
    .ul <$> items.mapM (ListItem.fromJson?)
  else if let some v := vals["ol"]? then
    let start ← v.getObjValAs? _ "start"
    let items ← v.getObjVal? "items" >>= (·.getArr?)
    have : FromJson (Lean.Doc.Block i b) := ⟨Block.fromJson?⟩
    .ol start <$> items.mapM (ListItem.fromJson?)
  else if let some v := vals["dl"]? then
    have : FromJson (Lean.Doc.Block i b) := ⟨Block.fromJson?⟩
    .dl <$> FromJson.fromJson? v
  else if let some v := vals["blockquote"]? then
    let v ← v.getArr?
    .blockquote <$> v.mapM Block.fromJson?
  else if let some v := vals["concat"]? then
    let v ← v.getArr?
    .concat <$> v.mapM Block.fromJson?
  else if let some v := vals["other"]? then
    let container ← v.getObjVal? "container"
    let content ← v.getObjVal? "content" >>= (·.getArr?)
    .other <$> FromJson.fromJson? container <*> content.mapM fromJson?
  else throw s!"Expected an object containing a block constructor name as a key, but got {json.compress}"

public instance instFromJsonLeanBlock [FromJson i] [FromJson b] : FromJson (Lean.Doc.Block i b) where
  fromJson? := private Block.fromJson?

@[instance] public abbrev instFromJsonBlock [FromJson genre.Inline] [FromJson genre.Block] : FromJson (Block genre) :=
  instFromJsonLeanBlock

private partial def Block.beq [BEq i] [BEq b] : Lean.Doc.Block i b → Lean.Doc.Block i b → Bool
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

public instance instBEqLeanBlock [BEq genre.Inline] [BEq genre.Block] : BEq (Block genre) where
  beq := private Block.beq

@[instance] public abbrev instBEqBlock [BEq genre.Inline] [BEq genre.Block] : BEq (Block genre) := instBEqLeanBlock

-- Upstream has an instance, but the constructor names are the Lean ones rather than the Verso ones
private partial def Block.reprPrec [Repr genre.Inline] [Repr genre.Block] (inline : Block genre) (prec : Nat) : Std.Format :=
    open Repr Std.Format in
    open Lean.Doc in
    let rec go i p :=
      (addAppParen · p) <|
        match i with
        | .para contents => reprCtor ``Block.para [reprArg contents]
        | .code content => reprCtor ``Block.code [reprArg content]
        | .ul items => reprCtor ``Block.ul [reprArray (@ListItem.reprPrec _ ⟨go⟩) items]
        | .ol start items => reprCtor ``Block.ol [reprArg start, reprArray (@ListItem.reprPrec _ ⟨go⟩) items]
        | .dl items => reprCtor ``Block.dl [reprArray (@DescItem.reprPrec _ _ ⟨Inline.reprPrec⟩ ⟨go⟩) items]
        | .blockquote items => reprCtor ``Block.blockquote [reprArray go items]
        | .concat content => reprCtor ``Block.concat [reprArray go content]
        | .other container content => reprCtor ``Block.other [reprArg container, reprArray go content]
    go inline prec

public instance [Repr g.Inline] [Repr g.Block] : Repr (Block g) where
  reprPrec b p := private Block.reprPrec b p


public def Block.cast (inlines_eq : g1.Inline = g2.Inline) (blocks_eq : g1.Block = g2.Block) : Block g1 → Block g2 :=
  Lean.Doc.Block.cast inlines_eq blocks_eq

@[inherit_doc Lean.Doc.Part]
public abbrev Part (genre : Genre) := Lean.Doc.Part genre.Inline genre.Block genre.PartMetadata

private partial def Part.toJson [ToJson i] [ToJson b] [ToJson p] (p : Lean.Doc.Part i b p) := json% {
    "title" : $(p.title),
    "titleString" : $(p.titleString),
    "metadata" : $(p.metadata),
    "content": $(p.content),
    "subParts": $(p.subParts.map Part.toJson)
  }

public instance instToJsonLeanPart [ToJson i] [ToJson b] [ToJson p] : ToJson (Lean.Doc.Part i b p) where
  toJson := private Part.toJson

@[instance] public abbrev instToJsonPart
    [ToJson genre.Inline] [ToJson genre.Block] [ToJson genre.PartMetadata] :
    ToJson (Part genre) :=
  instToJsonLeanPart

private partial def Part.fromJson? [FromJson i] [FromJson b] [FromJson p]
    (json : Json) : Except String (Lean.Doc.Part i b p) := do
  have : FromJson (Lean.Doc.Part i b p) := ⟨Part.fromJson?⟩
  .mk <$> json.getObjValAs? _ "title"
    <*> json.getObjValAs? _ "titleString"
    <*> json.getObjValAs? _ "metadata"
    <*> json.getObjValAs? _ "content"
    <*> json.getObjValAs? _ "subParts"

public instance instFromJsonLeanPart [FromJson i] [FromJson b] [FromJson p] : FromJson (Lean.Doc.Part i b p) where
  fromJson? := private Part.fromJson?

@[instance] public abbrev instFromJsonPart
    [FromJson genre.Inline] [FromJson genre.Block] [FromJson genre.PartMetadata] :
    FromJson (Part genre) :=
  instFromJsonLeanPart

@[expose, match_pattern]
public def Part.mk
    (title : Array (Inline genre))
    (titleString : String)
    (metadata : Option genre.PartMetadata)
    (content : Array (Block genre))
    (subParts : Array (Part genre)) : Part genre :=
  Lean.Doc.Part.mk title titleString metadata content subParts

@[inherit_doc Lean.Doc.Part.title]
public abbrev Part.title : Part genre → Array (Inline genre) := Lean.Doc.Part.title

@[inherit_doc Lean.Doc.Part.titleString]
public abbrev Part.titleString : Part genre → String := Lean.Doc.Part.titleString

@[inherit_doc Lean.Doc.Part.metadata]
public abbrev Part.metadata : Part genre → Option genre.PartMetadata := Lean.Doc.Part.metadata

@[inherit_doc Lean.Doc.Part.content]
public abbrev Part.content : Part genre → Array (Block genre) := Lean.Doc.Part.content

@[inherit_doc Lean.Doc.Part.subParts]
public abbrev Part.subParts : Part genre → Array (Part genre) := Lean.Doc.Part.subParts

@[instance]
public abbrev instBEqPart [BEq genre.Inline] [BEq genre.Block] [BEq genre.PartMetadata] : BEq (Part genre) :=
  inferInstanceAs (BEq (Lean.Doc.Part genre.Inline genre.Block genre.PartMetadata))

public def Part.withoutSubparts (p : Part genre) : Part genre := { p with subParts := #[] }

public def Part.withoutMetadata (p : Part genre) : Part genre := { p with metadata := none }

public def Part.cast
    (inlines_eq : g1.Inline = g2.Inline)
    (blocks_eq : g1.Block = g2.Block)
    (metadata_eq : g1.PartMetadata = g2.PartMetadata)
    (p : Part g1) : Part g2 :=
  show Lean.Doc.Part g2.Inline g2.Block g2.PartMetadata from
  inlines_eq ▸ blocks_eq ▸ metadata_eq ▸ (p : Lean.Doc.Part g1.Inline g1.Block g1.PartMetadata)


private partial def Part.reprPrec [Repr genre.Inline] [Repr genre.Block] [Repr genre.PartMetadata] (part : Part genre) (_prec : Nat) : Std.Format :=
  open Std.Format in
  reprCtor ``Part.mk [
      reprArg (part.title : Array (Inline genre)),
      reprArg part.titleString,
      reprArg (part.metadata : Option genre.PartMetadata),
      reprArg (part.content : Array (Block genre)),
      reprArray Part.reprPrec (part.subParts : Array (Part genre))
    ]

public instance [Repr g.Inline] [Repr g.Block] [Repr g.PartMetadata] : Repr (Part g) where
  reprPrec := private Part.reprPrec

/--
The result type of values created by Verso's `#doc` and `#docs` commands. A value of type
{lean}`VersoDoc` represents a not-fully-evaluated document of type {lean}`Part` that can be turned
into a value by invoking the `VersoDoc.toPart` method. The actual structure of a {lean}`VersoDoc`
should not be relied on.
-/
public structure VersoDoc (genre : Genre) where
  construct : Unit → Part genre

instance : Inhabited (VersoDoc genre) where
  default := VersoDoc.mk fun () => Inhabited.default

/--
A {lean}`VersoDoc` represents a potentially-not-fully-evaluated {lean}`Part`. Calling {lean}`VersoDoc.toPart` forces
evaluation of the {lean}`VersoDoc` to a {lean}`Part`.
-/
public def VersoDoc.toPart: VersoDoc genre → Part genre
  | .mk construct => construct ()

/--
Replace the metadata in a VersoDoc.

This is something of a hack used as a workaround in LiterateModuleDocs.
-/
public def VersoDoc.withMetadata (metadata? : Option genre.PartMetadata)  : VersoDoc genre → VersoDoc genre
  | .mk construct => .mk fun () => { construct () with metadata := metadata? }

/--
Identify function; this is a temporary compatibility shim to introduce a new type,
VersoDoc, that will have a nontrival toPart method.
-/
@[deprecated "remove or use VersoDoc.toPart" (since := "2025-11-01")]
public def Part.toPart (p : Part genre) := p

/--
Specifies how to modify the context while traversing the contents of a given part.
-/
public class TraversePart (g : Genre) where
  /--
  How to modify the context while traversing the contents of a given part. This is applied after
  {lit}`part` and {lit}`genrePart` have rewritten the text, if applicable.

  It is also used during HTML generation.
  -/
  inPart : Part g → g.TraverseContext → g.TraverseContext := fun _ => id

/--
Specifies how to modify the context while traversing the contents of a given block.
-/
public class TraverseBlock (g : Genre) where
  /--
  How to modify the context while traversing a given block.

  It is also used during HTML generation.
  -/
  inBlock : Block g → g.TraverseContext → g.TraverseContext := fun _ => id


public instance : TraversePart .none := {}

public instance : TraverseBlock .none := {}

/--
Genre-specific traversal.

The traversal pass is where cross-references are resolved. The traversal pass repeatedly applies a
genre-specific stateful computation until a fixed point is reached, both with respect to the state
and the document. Traversal may update the state or rewrite parts of the document.

{open Traverse}
{open TraversePart}

The methods {name}`part`, {name}`block`, and {name full:=Verso.Doc.Traverse.inline}`inline` provide effects to be carried out before traversing the
given level of the AST, and {name}`part` allows the part's metadata to be updated.

{name}`genrePart` is carried out after {name}`part`. It allows genre-specific rewriting of the entire part based
on genre-specific metadata. This is typically used to construct a table of contents or permalinks,
but it can in principle arbitrarily rewrite the part. {name}`inPart` is used to locally transform the
genre's traversal context along the lines of {name}`withReader`, and can be used to keep track of e.g. the
current position in the table of contents.

{name}`genreBlock` and {name}`genreInline` are invoked when traversal encounters {name}`Block.other` and
{name}`Inline.other`. It may rewrite them, or have state effects.

-/
public class Traverse (g : Genre) (m : outParam (Type → Type)) where
  /--
  The effects carried out before traversing a {name}`Part`.
  -/
  part [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : Part g → m (Option g.PartMetadata)
  /--
  The effects carried out before traversing a {name}`Block`.
  -/
  block [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : Block g → m Unit
  /--
  The effects carried out before traversing an {name}`Inline`.
  -/
  inline [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : Inline g → m Unit
  /--
  {open Traverse}

  Operations carried out after {name}`part`, when a part has metadata. It allows genre-specific rewriting
  of the entire part based on genre-specific metadata. This is typically used to construct a table
  of contents or permalinks, but it can in principle arbitrarily rewrite the part. If it returns
  {name}`none`, then no rewrite is performed.
  -/
  genrePart [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : g.PartMetadata → Part g → m (Option (Part g))
  /--
  The traversal of genre-specific block values. If it returns {name}`none`, then no rewrite is performed.
  -/
  genreBlock [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : g.Block → Array (Block g) → m (Option (Block g))
  /--
  The traversal of genre-specific inline values. If it returns {name}`none`, then no rewrite is performed.
  -/
  genreInline [MonadReader g.TraverseContext m] [MonadState g.TraverseState m] : g.Inline → Array (Inline g) → m (Option (Inline g))

section
variable (g : Genre) [Traverse g m] [TraversePart g] [TraverseBlock g] [Monad m]
variable [MonadReader g.TraverseContext m] [MonadWithReader g.TraverseContext m]
variable [MonadState g.TraverseState m]


public partial def Genre.traverseInline (i : Doc.Inline g) : m (Doc.Inline g) := do
  Traverse.inline i
  match i with
  | .emph content => .emph <$> content.mapM traverseInline
  | .bold content => .bold <$> content.mapM traverseInline
  | .link content ref => (.link · ref) <$> content.mapM traverseInline
  | .footnote name content => .footnote name <$> content.mapM traverseInline
  | .image alt ref => pure <| .image alt ref
  | .concat content => .concat <$> content.mapM traverseInline
  | .other container content => do
    match ← Traverse.genreInline container content with
    | .none => .other container <$> content.mapM traverseInline
    | .some i' => traverseInline i'
  | .text .. | .linebreak .. | .code .. | .math .. => pure i

public partial def Genre.traverseBlock (b : Doc.Block g) : m (Doc.Block g) := do
  Traverse.block b
  withReader (TraverseBlock.inBlock b) <|
    match b with
    | .para contents => .para <$> contents.mapM g.traverseInline
    | .ul items => .ul <$> items.mapM fun
      | ListItem.mk contents => ListItem.mk <$> contents.mapM traverseBlock
    | .ol start items => .ol start <$> items.mapM fun
      | ListItem.mk contents => ListItem.mk <$> contents.mapM traverseBlock
    | .dl items => .dl <$> items.mapM fun
      | DescItem.mk t d => DescItem.mk <$> t.mapM g.traverseInline <*> d.mapM traverseBlock
    | .blockquote items => .blockquote <$> items.mapM traverseBlock
    | .concat items => .concat <$> items.mapM traverseBlock
    | .other container content => do
      match ← Traverse.genreBlock container content with
      | .none => .other container <$> content.mapM traverseBlock
      | .some b' => traverseBlock b'
    | .code .. => pure b

public partial def Genre.traversePart (p : Doc.Part g) : m (Doc.Part g) := do
    let meta' ← Traverse.part p
    let mut p := meta'.map ({ p with metadata := ·}) |>.getD p
    if let some md := p.metadata then
      if let some p' ← Traverse.genrePart md p then
        p := p'
    let .mk title titleString metadata content subParts := p
    let (content', subParts') ← withReader (TraversePart.inPart p) <|
      (·,·) <$> content.mapM g.traverseBlock <*> subParts.mapM traversePart
    pure <| .mk (← title.mapM g.traverseInline) titleString metadata content' subParts'

public partial def Genre.traverse (top : Part g) : m (Part g) :=
  g.traversePart top
