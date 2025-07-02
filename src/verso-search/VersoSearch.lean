import Std.Data.TreeMap
import Std.Data.TreeMap.Lemmas
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF
import Std.Data.HashSet

import Lean.Data.Json

import Verso.Doc

import VersoSearch.PorterStemmer

open Std
open Lean

namespace Verso.Search


/--
How should multiple search terms be combined?
-/
inductive SearchBool where
  /-- Requires all terms to be present. -/
  | and
  /-- Requires at least one term to be present. -/
  | or

structure FieldOptions where
  boost : Option UInt8 := none
  bool : Option SearchBool := none
  expand : Option Bool := false

structure Options where
  bool : SearchBool := .and -- Different from elasticlunr, but this is basically always correct for Verso docs
  expand : Bool := false
  fields : TreeMap String FieldOptions

abbrev Doc := TreeMap String String

structure DocumentStore where
  save : Bool
  docs : TreeMap String Doc
  docInfo : TreeMap String (TreeMap String USize)
  length : USize

namespace DocumentStore

def toJson (self: DocumentStore) : Json :=
  json%{
    "save": $self.save,
    "docs": $(self.docs.foldr (init := Json.mkObj []) fun k v json => json.setObjVal! k (v.foldr (init := Json.mkObj []) fun k v js => js.setObjVal! k (Json.str v))),
    "docInfo": $(self.docInfo.foldr (init := Json.mkObj []) (fun k v js => js.setObjVal! k (v.foldr (init := Json.mkObj []) (fun k v js => js.setObjVal! k v.toNat)))),
    "length" : $self.length
  }

def hasDoc (self : DocumentStore) (ref : String) : Bool := self.docs.contains ref

def isEmpty (self : DocumentStore) : Bool := self.length == 0

def addDoc (self : DocumentStore) (ref : String) (doc : Doc) : DocumentStore :=
  { self with
    length := if self.hasDoc ref then self.length else self.length + 1,
    docs := self.docs.insert ref <| if self.save then doc else {} }

def get? (self : DocumentStore) (ref : String) : Option Doc := self.docs[ref]?

instance : GetElem? DocumentStore String Doc (fun store ref => ref ∈ store.docs) where
  getElem store ref ok := store.docs[ref]'ok
  getElem? store ref := store.docs[ref]?

def erase (self : DocumentStore) (ref : String) : DocumentStore :=
  { self with
    length := if self.hasDoc ref then self.length - 1 else self.length,
    docs := self.docs.erase ref }

def addFieldLength (self : DocumentStore) (ref : String) (field : String) (length : USize) : DocumentStore :=
  { self with
    docInfo := self.docInfo.alter ref fun v => some (v.getD {} |>.insert field length) }

def getFieldLength (self : DocumentStore) (ref : String) (field : String) : USize :=
  (self.docInfo[ref]? >>= fun i => i[field]?).getD 0

-- TODO port tests

end DocumentStore

structure TermFrequency where
  -- TODO rename field to tf in json - check json output
  termFreq : Float

def TermFrequency.toJson (freq : TermFrequency) : Json := json%{"tf": $freq.termFreq}

structure IndexItem.Raw where
  docs : TreeMap String TermFrequency := {}
  -- TODO field name df
  docFreq : Int64 := 0
  -- TODO serialization
  children : TreeMap.Raw Char IndexItem.Raw := {}

inductive IndexItem.Raw.WF : IndexItem.Raw → Prop where
  | mk
    {docs : TreeMap String TermFrequency} {docFreq : Int64}
    {children : TreeMap.Raw Char IndexItem.Raw} :
    (∀ (c : Char) v, children[c]? = some v → IndexItem.Raw.WF v) →
    children.WF →
    IndexItem.Raw.WF { docs, docFreq, children }

namespace IndexItem

namespace Raw

def empty : IndexItem.Raw := {}

def addToken (self : IndexItem.Raw) (ref : String) (token : String) (termFreq : Float) : IndexItem.Raw :=
  if token.isEmpty then self
  else loop self token.iter
where
  loop (item : IndexItem.Raw) (iter : String.Iterator) : IndexItem.Raw :=
    if h : iter.hasNext then --while loop
      let c := iter.curr' h
      have : c = iter.curr' h := rfl
      let item' := item.children[c]?.getD {}
      let item' := loop item' (iter.next' h)
      { item with children := item.children.insert c item' }
    else
      let item := if item.docs.contains ref then item else { item with docFreq := item.docFreq + 1 }
      { item with docs := item.docs.insert ref ⟨termFreq⟩ }
  termination_by iter.s.endPos.byteIdx - iter.i.byteIdx
  decreasing_by
    have : iter.s.endPos.byteIdx > iter.i.byteIdx := by
      simp [String.Iterator.hasNext] at h
      omega
    simp [String.Iterator.next', String.next, Char.utf8Size]
    repeat (split; omega)
    omega

def getNode? (self : IndexItem.Raw) (token : String) : Option IndexItem.Raw :=
  loop self token.iter
where
  loop (item : IndexItem.Raw) (iter : String.Iterator) : Option IndexItem.Raw := do
    if h : iter.hasNext then
      let item ← item.children[iter.curr' h]?
      loop item (iter.next' h)
    else
      pure item
  termination_by iter.s.endPos.byteIdx - iter.i.byteIdx
  decreasing_by
    have : iter.s.endPos.byteIdx > iter.i.byteIdx := by
      simp [String.Iterator.hasNext] at h
      omega
    simp [String.Iterator.next', String.next, Char.utf8Size]
    repeat (split; omega)
    omega

def removeToken (self : IndexItem.Raw) (ref token : String) : IndexItem.Raw :=
  loop self token.iter
where
  loop (item : IndexItem.Raw) (iter : String.Iterator) : IndexItem.Raw :=
    if h : iter.hasNext then
      let ch := iter.curr' h
      let iter := iter.next' h
      if _ : iter.hasNext then
        { item with
          children := item.children.alter ch fun
            | some item' => some <| loop item' iter
            | none => none
        }
      else if item.docs.contains ref then
        { item with
          docs := item.docs.erase ref
          docFreq := item.docFreq - 1 }
      else item
    else
      item
  termination_by iter.s.endPos.byteIdx - iter.i.byteIdx
  decreasing_by
    simp [iter] at *
    clear iter
    have : iter.s.endPos.byteIdx > iter.i.byteIdx := by
      simp_all [String.Iterator.hasNext, String.Iterator.next', String.next]
      omega
    simp [String.Iterator.next', String.next, Char.utf8Size]
    repeat (split; omega)
    omega


end Raw

namespace WF

theorem empty : Raw.empty.WF := by
  constructor
  . intro c v h
    have : (∅ : TreeMap.Raw Char IndexItem.Raw)[c]? = none := by rfl
    simp_all
  . exact TreeMap.Raw.WF.empty

where


end WF

end IndexItem

structure IndexItem where
  raw : IndexItem.Raw := {}
  -- TODO WF



namespace IndexItem
def docs (item : IndexItem) : TreeMap String TermFrequency := item.raw.docs
def docFreq (item : IndexItem) : Int64 := item.raw.docFreq
def empty : IndexItem := {}
def addToken (self : IndexItem) (ref : String) (token : String) (termFreq : Float) : IndexItem :=
  ⟨self.raw.addToken ref token termFreq⟩
def getNode? (self : IndexItem) (token : String) : Option IndexItem :=
  (⟨·⟩) <$> self.raw.getNode? token
def removeToken (self : IndexItem) (ref token : String) : IndexItem :=
  ⟨self.raw.removeToken ref token⟩

partial def Raw.toJson (self: IndexItem.Raw) : Json :=
  let metadata := json%{
    "docs": $(self.docs.foldr (init := Json.mkObj []) (fun f freq json => json.setObjVal! f freq.toJson)),
    "df": $self.docFreq.toInt
  }
  self.children.foldr (init := metadata) fun c ch json => json.setObjVal! c.toString (Raw.toJson ch)

def toJson (self : IndexItem) : Json := self.raw.toJson

end IndexItem

structure InvertedIndex where
  root : IndexItem := {}

instance : EmptyCollection InvertedIndex := ⟨{root := {}}⟩

namespace InvertedIndex

def addToken (self : InvertedIndex) (ref token : String) (freq : Float) : InvertedIndex :=
  { self with root := self.root.addToken ref token freq }

def hasToken (self : InvertedIndex) (token : String) : Bool :=
  self.root.getNode? token |>.isSome

def removeToken (self : InvertedIndex) (ref token : String) : InvertedIndex :=
  {self with root := self.root.removeToken ref token }

def getDocs (self : InvertedIndex) (token : String) : Option (TreeMap String Float) :=
  self.root.getNode? token |>.map fun node =>
    node.docs.map fun _ v => v.termFreq

def getTermFrequency (self : InvertedIndex) (ref token : String) : Float :=
  self.root.getNode? token |>.bind (·.docs[ref]?) |>.map (·.termFreq) |>.getD 0.0

def toJson (self : InvertedIndex) : Json :=
  json%{
    "root": $self.root.toJson
  }
end InvertedIndex

structure PipelineFn where
  name : String
  filter (token : String) : Option String

-- Replaces StopWordFilter in Rust version
def stopWordFilter (name : String) (stopWords : HashSet String) : PipelineFn where
  name := name
  filter tok := if stopWords.contains tok then none else some tok


-- Replaces RegexTrimmer in Rust version
def predicateTrimmer (name : String) (wordChars : Char → Bool) : PipelineFn where
  name := name
  filter tok :=
    let tok := tok.dropWhile wordChars |>.dropRightWhile wordChars
    if tok.isEmpty then none
    else some tok


open Verso.Search.Stemmer.Porter in
def porterStemmerFilter (name : String) : PipelineFn where
  name := name
  filter tok :=
    let res := porterStem tok
    if res.isEmpty then none else some res


structure Pipeline where
  queue : Array PipelineFn

def Pipeline.run (self : Pipeline) (tokens : Array String) : Array String :=
  tokens.filterMap fun tok =>
    self.queue.foldl (init := some tok) fun s f => s.bind f.filter

def Pipeline.toJson (self : Pipeline) : Json := .arr <| self.queue.map (Json.str ·.name)

-- TODO tests
structure Language where
  name : String
  code : String
  tokenize : String → Array String
  pipeline : Pipeline

def english : Language where
  name := "English"
  code := "en"
  tokenize := tokenizeWhitespace
  pipeline := .mk #[
    .mk "trimmer" trimmer,
    stopWordFilter "stopWordFilter" <| HashSet.ofArray words,
    porterStemmerFilter "stemmer"
  ]
where
  trimmer (tok : String) : Option String := tok.dropWhile badChar |>.dropRightWhile badChar
  badChar c := !(c.isAlphanum || c == '_')
  words := #["", "a", "able", "about", "across", "after", "all", "almost", "also", "am", "among", "an",
    "and", "any", "are", "as", "at", "be", "because", "been", "but", "by", "can", "cannot",
    "could", "dear", "did", "do", "does", "either", "else", "ever", "every", "for", "from", "get",
    "got", "had", "has", "have", "he", "her", "hers", "him", "his", "how", "however", "i", "if",
    "in", "into", "is", "it", "its", "just", "least", "let", "like", "likely", "may", "me",
    "might", "most", "must", "my", "neither", "no", "nor", "not", "of", "off", "often", "on",
    "only", "or", "other", "our", "own", "rather", "said", "say", "says", "she", "should", "since",
    "so", "some", "than", "that", "the", "their", "them", "then", "there", "these", "they", "this",
    "tis", "to", "too", "twas", "us", "wants", "was", "we", "were", "what", "when", "where",
    "which", "while", "who", "whom", "why", "will", "with", "would", "yet", "you", "your"]
  tokenizeWhitespace (str : String) :=
    str.split (fun c => c.isWhitespace || c == '-') |>.toArray |>.filter (!·.isEmpty) |>.map (·.trim.toLower)

abbrev Tokenizer := Option (String → Array String)

structure IndexBuilder where
  save : Bool := true
  fields : Array String := #[]
  fieldTokenizers : Array Tokenizer := #[]
  refField : String := "id"
  pipeline : Option Pipeline := none
  language : Language := english

instance : Inhabited IndexBuilder where
  default := ⟨true, #[], #[], "id", none, english⟩

namespace IndexBuilder
def addField (self : IndexBuilder) (field : String) : IndexBuilder :=
  if self.fields.contains field then panic! s!"Duplicate field '{field}'"
  else
    { self with
      fields := self.fields.push field,
      fieldTokenizers := self.fieldTokenizers.push none
      }

def addFieldWithTokenizer (self : IndexBuilder) (field : String) (tokenizer : Tokenizer) : IndexBuilder :=
  if self.fields.contains field then panic! s!"Duplicate field '{field}'"
  else
    { self with
      fields := self.fields.push field,
      fieldTokenizers := self.fieldTokenizers.push tokenizer
      }

def setRef (self : IndexBuilder) (refField : String) : IndexBuilder := { self with refField }
end IndexBuilder

structure Index where
  fields : Array String
  fieldTokenizers : Array Tokenizer
  pipeline : Pipeline
  refField : String
  version : String
  index : TreeMap String InvertedIndex
  documentStore : DocumentStore
  language : Language

namespace IndexBuilder
def build (self : IndexBuilder) : Index :=
  let {save, fields, fieldTokenizers, refField, pipeline, language} := self
  let index := TreeMap.ofArray <| fields.map fun f => (f, {})
  { self with
      pipeline := self.pipeline.getD language.pipeline,
      version := "0.9.5",
      documentStore := {save, docs := {}, docInfo := {}, length := 0}
      index
  }
end IndexBuilder

namespace Index

def addDoc (self : Index) (ref : String) (data : Array String) : Index := Id.run do
  let mut self := self
  let mut doc : TreeMap String String := ∅
  doc := doc.insert self.refField ref
  let mut tokenFreq : TreeMap String Float := ∅
  for field in self.fields, tokenizer? in self.fieldTokenizers, value in data do
    doc := doc.insert field value

    if field == ref then continue

    let rawTokens := tokenizer?.getD self.language.tokenize <| value
    let tokens := self.pipeline.run rawTokens

    self := { self with documentStore := self.documentStore.addFieldLength ref field tokens.usize }

    for token in tokens do
      tokenFreq := tokenFreq.alter token fun f => some (f.getD 0.0 + 1.0)

    for (token, count) in tokenFreq do
      let freq := count.sqrt
      self :=
        { self with index := self.index.alter field fun
          | none => panic! s!"Inverted index does not exist for field '{field}'"
          | some i => some <| i.addToken ref token freq
        }
  { self with documentStore := self.documentStore.addDoc ref doc }

def indexJson (self : Index) : Json :=
  self.index.foldr (init := Json.mkObj []) fun f i json => json.setObjVal! f i.toJson

def toJson (self : Index) : Json :=

  json%{
    "version": $self.version,
    "fields": $self.fields,
    "ref": $self.refField,
    "documentStore": $self.documentStore.toJson,
    "index" : $self.indexJson,
    "pipeline": $self.pipeline.toJson

  }

end Index

open Verso Doc

structure IndexDoc where
  /-- A globally unique identifier for the document -/
  id : String
  /-- The string content to search for this document -/
  content : String

abbrev IndexM := EStateM String (HashMap String IndexDoc)

def IndexM.save (doc : IndexDoc) : IndexM Unit := do
  if (← get).contains doc.id then
    throw "Duplicate document ID: {doc.id}"
  else
    modify (·.insert doc.id doc)

class Indexable (genre : Genre) where
  /-- The identifier for a part -/
  partId : genre.PartMetadata → Option String
  /--
  How to index block extensions.

  Return `none` to fall back to the content of the contained blocks.
  -/
  block : genre.Block → Option ((Inline genre → IndexM String) → (Block genre → IndexM String) → Array (Block genre) → IndexM IndexDoc)
  /--
  How to index inline extensions.

  Return `none` to fall back to the content of the contained inlines.
  -/
  inline : genre.Inline → Option ((Inline genre → IndexM String) → Array (Inline genre) → IndexM IndexDoc)

partial def inlineText [Indexable g] (i : Inline g) : IndexM String :=
  match i with
  | .text s | .math _ s | .linebreak s | .code s => pure s
  | .link inls _ | .concat inls | .bold inls | .emph inls | .footnote _ inls =>
    inls.foldlM (init := "") (fun s i => do return s ++ (← inlineText i))
  | .image .. => pure " " -- TODO figure out if alt text can be searchable
  | .other i inls =>
    match Indexable.inline i with
    | some go => do
      let doc ← go inlineText inls
      IndexM.save doc
      pure " "
    | none =>
      inls.foldlM (init := "") (fun s i => do return s ++ (← inlineText i))

partial def blockText [Indexable g] (b : Block g) : IndexM String :=
  match b with
  | .para inls =>
    inls.foldlM (init := "") (fun s i => do return s ++ (← inlineText i))
  | .concat bs | .blockquote bs =>
    bs.foldlM (init := "") (fun s i => do return s ++ (← blockText i))
  | .code s => pure s
  | .dl items => do
    let mut out := ""
    for i in items do
      out ← i.term.foldlM (init := out) (fun s i => do return s ++ (← inlineText i))
      out := out ++ "\n\n"
      out ← i.desc.foldlM (init := out) (fun s b => do return s ++ (← blockText b))
      out := out ++ "\n\n"
    return out
  | .ol start items => do
    let mut out := ""
    let mut n := start
    for i in items do
      out := out ++ s!"{n}. "
      n := n + 1
      out ← i.contents.foldlM (init := out) (fun s b => do return s ++ (← blockText b))
    return out
  | .ul items => do
    let mut out := ""
    for i in items do
      out := out ++ s!"* "
      out ← i.contents.foldlM (init := out) (fun s b => do return s ++ (← blockText b))
    return out
  | .other b bs =>
    match Indexable.block b with
    | none => bs.foldlM (init := "") (fun s i => do return s ++ (← blockText i))
    | some go => do
      let doc ← go inlineText blockText bs
      IndexM.save doc
      pure " "

partial def partText [idx : Indexable g] (p : Part g) : IndexM String := do
  let content := p.titleString ++ "\n\n"
  let content ← p.content.foldlM (init := content) fun s b => do return s ++ (← blockText b) ++ "\n\n"
  let content ← p.subParts.foldlM (init := content) fun s p' => do return s ++ (← partText p') ++ "\n\n"

  match p.metadata >>= idx.partId with
  | none => return content
  | some id =>
    IndexM.save {id, content}
    return ""

def mkIndexDocs [idx : Indexable g] (p : Part g) : Except String (Array IndexDoc) := do
  if p.metadata.bind idx.partId |>.isNone then
    throw "No ID for root part"
  else
    match partText p {} with
    | .error e _ => throw e
    | .ok _ docs => return docs.fold (init := #[]) fun xs _ x => xs.push x

def mkIndex [idx : Indexable g] (p : Part g) : Except String Index := do
  if p.metadata.bind idx.partId |>.isNone then
    throw "No ID for root part"
  else
    match partText p {} with
    | .error e _ => throw e
    | .ok _ docs =>
      let mut index : Index := { refField := "id" : IndexBuilder } |>.addField "id" |>.addField "contents" |>.build
      for (_, doc) in docs do
        index := index.addDoc doc.id #[doc.id, doc.content]
      return index


-- #eval { refField := "id" : IndexBuilder } |>.addField "id" |>.addField "contents" |>.build |>.addDoc "a" #["a", "dog cat"] |>.addDoc "b" #["b", "dog rat"] |>.indexJson |>.compress |> IO.println
