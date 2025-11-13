/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Std.Data.TreeMap
import Std.Data.TreeMap.Lemmas
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.TreeMap.Raw.WF
public import Std.Data.HashSet

import Lean.Data.Json
public import Lean.Data.Json.Basic
public import Lean.Data.Json.FromToJson.Basic

public import Verso.Doc

import VersoSearch.PorterStemmer
import VersoSearch.DomainSearch

set_option linter.missingDocs true
set_option doc.verso true

open Std
open Lean



namespace Verso.Search

/-!
This module contains code to construct an index that's compatible with elasticlunr.js.
-/

/--
How should multiple search terms be combined?
-/
public inductive SearchBool where
  /-- Requires all terms to be present. -/
  | and
  /-- Requires at least one term to be present. -/
  | or

/-- Generates an elasticlunr.js-compatible encoding of a Boolean term combination model. -/
public protected def SearchBool.toJson : SearchBool → Json
  | .and => .str "AND"
  | .or => .str "OR"

/-- Parses the elasticlunr.js encoding of a term combination model. -/
public protected def SearchBool.fromJson? : Json → Except String SearchBool
  | .str "AND" => pure .and
  | .str "OR" => pure .or
  | other => throw s!"Expected \"AND\" or \"OR\" but got {other.compress}"

public instance : ToJson SearchBool := ⟨SearchBool.toJson⟩
public instance : FromJson SearchBool := ⟨SearchBool.fromJson?⟩

/--
A version of `elasticlunr.js`'s field options, used at query time.

This exists to facilitate the construction of queries and is not used during indexing.
-/
public structure FieldOptions where
  /-- The relative weight to give the matches in the field. -/
  boost : Option UInt8 := none
  /-- How should terms be combined in this field? Overrides the model used for the whole query. -/
  bool : Option SearchBool := none
  /-- Whether to search for substrings, e.g. by expanding 'micro' to 'microwave' and 'microscope' -/
  expand : Option Bool := false

/-- Converts query field options to the right JSON encoding for elasticlunr.js. -/
protected def FieldOptions.toJson : FieldOptions → Json
  | {boost, bool, expand} =>
    Json.mkObj <|
      (boost.map fun x => [("boost", toJson x.toNat)]).getD [] ++
      (bool.map fun x => [("bool", x.toJson)]).getD [] ++
      (expand.map fun x => [("expand", toJson x)]).getD []

instance : ToJson FieldOptions where
  toJson := FieldOptions.toJson

/-- Overall query options for elasticlunr.js. -/
public structure Options where
  /-- How should terms be combined in this index? May be overridden on a per-field basis. -/
  bool : SearchBool := .or
  /-- Whether to search for substrings, e.g. by expanding 'micro' to 'microwave' and 'microscope' -/
  expand : Bool := false
  /-- Options for each field. -/
  fields : TreeMap String FieldOptions

/-- A document is a map from field names to field values. -/
public abbrev Doc := TreeMap String String

/--
The number of characters in the document.
-/
public def Doc.size (doc : Doc) : Nat :=
  doc.foldl (init := 0) fun s k v => s + k.length + v.length

/--
A collection of indexed documents, represented so as to be compatible with elasticlunr.js.
-/
public structure DocumentStore where
  /-- Whether to save the contents of documents, or just their inverted index entries. -/
  save : Bool
  /-- The saved documents. -/
  docs : TreeMap String Doc
  /-- The size of each field in the document. -/
  docInfo : TreeMap String (TreeMap String USize)
  /-- The total size of the document store. -/
  length : USize

namespace DocumentStore

/-- Converts a document store to an elasticlunr.js-compatible representation. -/
public protected def toJson (self: DocumentStore) : Json :=
  json%{
    "save": $self.save,
    "docs": $(self.docs.foldr (init := Json.mkObj []) fun k v json => json.setObjVal! k (v.foldr (init := Json.mkObj []) fun k v js => js.setObjVal! k (Json.str v))),
    "docInfo": $(self.docInfo.foldr (init := Json.mkObj []) (fun k v js => js.setObjVal! k (v.foldr (init := Json.mkObj []) (fun k v js => js.setObjVal! k v.toNat)))),
    "length" : $self.length
  }

/-- Checks whether the store contains a document with the given value for its reference field. -/
public def hasDoc (self : DocumentStore) (ref : String) : Bool := self.docs.contains ref

/-- Checks whether the store contains no data -/
public def isEmpty (self : DocumentStore) : Bool := self.length == 0

/--
Adds a document to the store.

If {lean}`self.save` is {name}`false`, then only the length is incremented and the contents are discarded.
-/
public def addDoc (self : DocumentStore) (ref : String) (doc : Doc) : DocumentStore :=
  { self with
    length := if self.hasDoc ref then self.length else self.length + 1,
    docs := self.docs.insert ref <| if self.save then doc else {} }

/--
Removes the documents from the store, setting {lean}`self.save` to {name}`false`.
-/
public def extractDocs (self : DocumentStore) : DocumentStore × TreeMap String Doc :=
  let docs := self.docs
  let noDocs := docs.map (fun _ _ => {})
  ({ self with docs := noDocs, save := false }, docs)

/--
Gets a document if it is present in the store.
-/
public protected def get? (self : DocumentStore) (ref : String) : Option Doc := self.docs[ref]?

public instance : GetElem? DocumentStore String Doc (fun store ref => ref ∈ store.docs) where
  getElem store ref ok := store.docs[ref]'ok
  getElem? store ref := store.docs[ref]?

/--
Removes a document with the given value in its reference field from the store.
-/
public def erase (self : DocumentStore) (ref : String) : DocumentStore :=
  { self with
    length := if self.hasDoc ref then self.length - 1 else self.length,
    docs := self.docs.erase ref }

/--
Adds the length of the given field to the store.
-/
public def addFieldLength (self : DocumentStore) (ref : String) (field : String) (length : USize) : DocumentStore :=
  { self with
    docInfo := self.docInfo.alter ref fun v => some (v.getD {} |>.insert field length) }

/--
Gets the length of the given field from the store for the given document.
-/
public def getFieldLength (self : DocumentStore) (ref : String) (field : String) : USize :=
  (self.docInfo[ref]? >>= fun i => i[field]?).getD 0

end DocumentStore

/--
The frequency of a term.

Stored in a wrapper to trigger appropriate serialization for elasticlunr.js.
-/
public structure TermFrequency where
  /-- The frequency value. -/
  termFreq : Float

/--
Serializes a term frequency to an elasticlunr-compatible representation.
-/
protected def TermFrequency.toJson (freq : TermFrequency) : Json := json%{"tf": $freq.termFreq}

private structure IndexItem.Raw where
  docs : TreeMap String TermFrequency := {}
  docFreq : Int64 := 0
  children : TreeMap.Raw Char IndexItem.Raw := {}

private inductive IndexItem.Raw.WF : IndexItem.Raw → Prop where
  | mk
    {docs : TreeMap String TermFrequency} {docFreq : Int64}
    {children : TreeMap.Raw Char IndexItem.Raw} :
    (∀ (c : Char) v, children[c]? = some v → IndexItem.Raw.WF v) →
    children.WF →
    IndexItem.Raw.WF { docs, docFreq, children }

namespace IndexItem

namespace Raw

private def empty : IndexItem.Raw := {}

private def addToken (self : IndexItem.Raw) (ref : String) (token : String) (termFreq : Float) : IndexItem.Raw :=
  if token.isEmpty then self
  else loop self token.startValidPos
where
  loop (item : IndexItem.Raw) (iter : String.ValidPos token) : IndexItem.Raw :=
    if h : iter ≠ token.endValidPos then --while loop
      let c := iter.get h
      let item' := item.children[c]?.getD {}
      let item' := loop item' (iter.next h)
      { item with children := item.children.insert c item' }
    else
      let item := if item.docs.contains ref then item else { item with docFreq := item.docFreq + 1 }
      { item with docs := item.docs.insert ref ⟨termFreq⟩ }
  termination_by token.endValidPos.offset.byteIdx - iter.offset.byteIdx
  decreasing_by
    have := iter.isValid.le_endPos
    apply Nat.sub_lt_sub_left
    . rw [String.Pos.Raw.le_iff] at this
      have : iter.offset.byteIdx ≠ token.endValidPos.offset.byteIdx := by
        intro h
        have : iter = token.endValidPos := by
          ext; assumption
        contradiction
      apply Nat.lt_of_le_of_ne <;> trivial
    . simp [Char.utf8Size_pos]

private def getNode? (self : IndexItem.Raw) (token : String) : Option IndexItem.Raw :=
  loop self token.startValidPos
where
  loop (item : IndexItem.Raw) (iter : String.ValidPos token) : Option IndexItem.Raw := do
    if h : iter ≠ token.endValidPos then
      let item ← item.children[iter.get h]?
      loop item (iter.next h)
    else
      pure item
  termination_by token.endValidPos.offset.byteIdx - iter.offset.byteIdx
  decreasing_by
    have := iter.isValid.le_endPos
    simp only [String.offset_endValidPos, String.byteIdx_endPos, String.ValidPos.offset_next,
      String.Pos.Raw.byteIdx_add_char, gt_iff_lt]
    apply Nat.sub_lt_sub_left
    . apply Nat.lt_of_le_of_ne this
      . intro h'
        have : iter = token.endValidPos := by ext <;> assumption
        contradiction
    . simp [Char.utf8Size_pos]

private def removeToken (self : IndexItem.Raw) (ref token : String) : IndexItem.Raw :=
  loop self token.startValidPos
where
  loop (item : IndexItem.Raw) (iter : token.ValidPos) : IndexItem.Raw :=
    if h : iter ≠ token.endValidPos then
      let ch := iter.get h
      let iter := iter.next h
      if _ : iter ≠ token.endValidPos then
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
  termination_by token.endValidPos.offset.byteIdx - iter.offset.byteIdx
  decreasing_by
    rename_i iter' _
    have := iter.isValid.le_endPos
    have := iter'.isValid.le_endPos
    apply Nat.sub_lt_sub_left
    . apply Nat.lt_of_le_of_ne this
      . intro h'
        have : iter' = token.endValidPos := by ext <;> assumption
        contradiction
    . simp [Char.utf8Size_pos]
end Raw

namespace WF

private theorem empty : Raw.empty.WF := by
  constructor
  . intro c v h
    have : (∅ : TreeMap.Raw Char IndexItem.Raw)[c]? = none := by rfl
    simp_all
  . exact TreeMap.Raw.WF.empty

end WF

end IndexItem

/--
An item in the inverted index.
-/
public structure IndexItem where
  private mk ::
  private raw : IndexItem.Raw := {}
  -- TODO WF

public instance : EmptyCollection IndexItem where
  emptyCollection := private {}

namespace IndexItem
/-- The term frequency for each document. -/
public def docs (item : IndexItem) : TreeMap String TermFrequency := item.raw.docs
/-- The frequency for each document (field {lit}`df` in the serialized index) -/
public def docFreq (item : IndexItem) : Int64 := item.raw.docFreq
/-- The empty inverted index. -/
public def empty : IndexItem := .mk {}
/-- Adds a token to the index for the given frequency. -/
public def addToken (self : IndexItem) (ref : String) (token : String) (termFreq : Float) : IndexItem :=
  ⟨self.raw.addToken ref token termFreq⟩
/-- Gets a node for the given token if it exists. -/
public def getNode? (self : IndexItem) (token : String) : Option IndexItem :=
  (⟨·⟩) <$> self.raw.getNode? token
/-- Removes the given token if it exists. -/
public def removeToken (self : IndexItem) (ref token : String) : IndexItem :=
  ⟨self.raw.removeToken ref token⟩

private partial def Raw.toJson (self: IndexItem.Raw) : Json :=
  let metadata := json%{
    "docs": $(self.docs.foldr (init := Json.mkObj []) (fun f freq json => json.setObjVal! f freq.toJson)),
    "df": $self.docFreq.toInt
  }
  self.children.foldr (init := metadata) fun c ch json => json.setObjVal! c.toString (Raw.toJson ch)

/-- Converts an index item into the elasticlunr.js JSON format. -/
protected def toJson (self : IndexItem) : Json := self.raw.toJson

end IndexItem

/-- An inverted index consists of a root in the trie. -/
public structure InvertedIndex where
  /-- The root item. -/
  root : IndexItem := {}

public instance : EmptyCollection InvertedIndex := ⟨{root := {}}⟩

namespace InvertedIndex

@[inherit_doc IndexItem.addToken]
public def addToken (self : InvertedIndex) (ref token : String) (freq : Float) : InvertedIndex :=
  { self with root := self.root.addToken ref token freq }

/-- Checks whether the given token is present in the index. -/
public def hasToken (self : InvertedIndex) (token : String) : Bool :=
  self.root.getNode? token |>.isSome

@[inherit_doc IndexItem.removeToken]
public def removeToken (self : InvertedIndex) (ref token : String) : InvertedIndex :=
  {self with root := self.root.removeToken ref token }

/--
Gets the term frequency for each document for the given token. Documents are identified by their
reference field.
-/
public def getDocs (self : InvertedIndex) (token : String) : Option (TreeMap String Float) :=
  self.root.getNode? token |>.map fun node =>
    node.docs.map fun _ v => v.termFreq

/--
Gets the term frequency for a document with the given reference field value for the given token.
-/
public def getTermFrequency (self : InvertedIndex) (ref token : String) : Float :=
  self.root.getNode? token |>.bind (·.docs[ref]?) |>.map (·.termFreq) |>.getD 0.0

/-- Serializes an inverted index into the format expected by elasticlunr.js. -/
public protected def toJson (self : InvertedIndex) : Json :=
  json%{
    "root": $self.root.toJson
  }
end InvertedIndex

/--
A named function in a pipeline.

elasticlunr.js uses an array of names, each of which is mapped to a registered string processing
function. The names and implementations must match for correctness.
-/
public structure PipelineFn where
  /-- The name used to identify the elasticlunr equivalent of the function. -/
  name : String
  /-- The implementation, which should match the corresponding elasticlunr function -/
  filter (token : String) : Option String

/-- A pipeline function that eliminates the words in {name}`stopWords`. -/
public def stopWordFilter (name : String) (stopWords : HashSet String) : PipelineFn where
  name := name
  filter tok := if stopWords.contains tok then none else some tok

/-- A pipeline function that trims the prefix and suffix that match {name}`wordChars`. -/
public def predicateTrimmer (name : String) (wordChars : Char → Bool) : PipelineFn where
  name := name
  filter tok :=
    let tok := tok.dropWhile wordChars |>.dropRightWhile wordChars
    if tok.isEmpty then none
    else some tok

open Verso.Search.Stemmer.Porter in
/--
A Porter stemmer, used to find the stems of English words.
-/
public def porterStemmerFilter (name : String) : PipelineFn where
  name := name
  filter tok :=
    let res := porterStem tok
    if res.isEmpty then none else some res

/--
A pipeline, which arranges functions from left to right. This configuration should match the one
used in elasticlunr.js.
-/
public structure Pipeline where
  /-- The functions in the pipeline.-/
  queue : Array PipelineFn

/-- Applies the functions in the pipeline from left to right. -/
public def Pipeline.run (self : Pipeline) (tokens : Array String) : Array String :=
  tokens.filterMap fun tok =>
    self.queue.foldl (init := some tok) fun s f => s.bind f.filter

/-- Serializes a pipeline for use with elasticlunr.js. -/
public protected def Pipeline.toJson (self : Pipeline) : Json := .arr <| self.queue.map (Json.str ·.name)

/--
A natural language for use with indexing.
-/
public structure Language where
  /-- The name of the language, e.g. {lean}`"English"`.-/
  name : String
  /-- The ISO code for the language, e.g. {lean}`"en"`.-/
  code : String
  /--
  A tokenization function that splits a text into words. Each word is further transformed or
  eliminated by the pipeline.
  -/
  tokenize : String → Array String
  /-- Further filters and transformations on the words, such as trimming them or stemming them. -/
  pipeline : Pipeline

/-- The English language, with a fairly simple Porter stemmer. -/
public def english : Language where
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
    str.splitToList (fun c => c.isWhitespace || c == '-') |>.toArray |>.filter (!·.isEmpty) |>.map (·.trim.toLower)

/--
A tokenizer maps an input string to an array of search tokens (normally words).

{name}`none` means to use the language's tokenizer.
-/
public abbrev TokenizerOverride := Option (String → Array String)

/--
An initial configuration for an index.
-/
public structure IndexBuilder where
  /-- Whether to save document contents, or just the index. -/
  save : Bool := true
  /--
  The fields present in documents. The reference field {name full:=IndexBuilder.refField}`refField`
  should be among them.
  -/
  fields : Array String := #[]
  /--
  Custom tokenizers for fields, associated with the fields in {name full:=IndexBuilder.fields}`fields` by position.
  -/
  fieldTokenizers : Array TokenizerOverride := #[]
  /-- The field used to identify a document. -/
  refField : String := "id"
  /-- A custom token filtering/transformation pipeline that overrides the one in the language -/
  pipeline : Option Pipeline := none
  /-- Which language are documents written in? -/
  language : Language := english

public instance : Inhabited IndexBuilder where
  default := ⟨true, #[], #[], "id", none, english⟩

namespace IndexBuilder
/-- Adds a field to an index configuration with the default tokenizer. -/
public def addField (self : IndexBuilder) (field : String) : IndexBuilder :=
  if self.fields.contains field then panic! s!"Duplicate field '{field}'"
  else
    { self with
      fields := self.fields.push field,
      fieldTokenizers := self.fieldTokenizers.push none
      }

/-- Adds a field to an index configuration, simultaneously specifying a different tokenizer. -/
public def addFieldWithTokenizer (self : IndexBuilder) (field : String) (tokenizer : TokenizerOverride) : IndexBuilder :=
  if self.fields.contains field then panic! s!"Duplicate field '{field}'"
  else
    { self with
      fields := self.fields.push field,
      fieldTokenizers := self.fieldTokenizers.push tokenizer
      }

end IndexBuilder

/--
An index suitable for elasticlunr.js.
-/
public structure Index where
  /-- Which fields exist in the provided documents? -/
  fields : Array String
  /--
  Fields that should be specially tokenized should have none-{name}`none` tokenizers in the
  corresponding position.
  -/
  fieldTokenizers : Array TokenizerOverride
  /--
  A pipeline. This Lean code must match the code used in the JavaScript configuration exactly - the
  names, orders, and behaviors of the steps must be identical.
  -/
  pipeline : Pipeline
  /--
  {open Index}
  The field used to identify documents. Should be present in {name}`fields`.
  -/
  refField : String
  /-- The version of `elasticlunr.js` that the index is designed to work with. -/
  version : String
  /-- An inverted index for each field. -/
  index : TreeMap String InvertedIndex
  /-- The indexed documents. -/
  documentStore : DocumentStore
  /-- The language used for the index. -/
  language : Language

namespace IndexBuilder
/--
Constructs an empty index with the current settings.
-/
public def build (self : IndexBuilder) : Index :=
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

/--
Adds a document to the index.

The document should be an array with one element for each field that's configured for the index,
matched elementwise in order of addition.
-/
public def addDoc (self : Index) (ref : String) (data : Array String) : Index := Id.run do
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

/--
Removes the documents from the index's store, setting {lean}`self.documentStore.save` to
{name}`false`.
-/
public def extractDocs (self : Index) : Index × TreeMap String Doc :=
  let (store, docs) := self.documentStore.extractDocs
  ({ self with documentStore := store }, docs)

/--
Converts the context of an index into JSON.
-/
private def indexJson (self : Index) : Json :=
  self.index.foldr (init := Json.mkObj []) fun f i json => json.setObjVal! f i.toJson

/--
Converts an index into a form suitable for loading in `elasticlunr.js` using
`elasticlunr.Index.load(...)`.
-/
public protected def toJson (self : Index) : Json :=
  json%{
    "version": $self.version,
    "fields": $self.fields,
    "ref": $self.refField,
    "documentStore": $self.documentStore.toJson,
    "index" : $self.indexJson,
    "pipeline": $self.pipeline.toJson

  }

end Index

open Verso

/--
A document to be indexed.

These are documents in the sense of elasticlunr.js, not necessarily Verso. Search occurs within a
document, so making them too fine-grained can make it hard to find results with multiple search
terms.
-/
public structure IndexDoc where
  /-- A globally unique identifier for the document -/
  id : String
  /-- A header to show in search results -/
  header : String
  /-- An indication of the context in the document, to be shown as breadcrumbs -/
  context : Array String
  /-- The string content to search for this document -/
  content : String

/-- A monad for indexing documents. -/
public abbrev IndexM (genre : Verso.Doc.Genre) :=
  ReaderT (Array String × genre.TraverseContext) (EStateM String (HashMap String IndexDoc))

/--
Gets the traversal context for the current point.
-/
public def IndexM.traverseContext : IndexM g g.TraverseContext := read <&> (·.2)

/--
Saves an indexable document to the store.
-/
public def IndexM.save (doc : IndexDoc) : IndexM g Unit := do
  if (← get).contains doc.id then
    throw s!"Duplicate document ID: {doc.id}"
  else
    modify (·.insert doc.id doc)

/--
Returns the stack of headers within which indexing is occurring.
-/
public def IndexM.currentContext : IndexM g (Array String) := read <&> (·.1)

/--
Runs an indexing computation and constructs the resulting index.
-/
public def IndexM.finalize (traverseContext : g.TraverseContext) (act : IndexM g Unit) : Except String Index := do
  match act (#[], traverseContext) {} with
  | .error e _ => throw e
  | .ok _ docs =>
    let mut index : Index := { refField := "id" : IndexBuilder } |>.addField "id" |>.addField "header" |>.addField "contents" |>.addField "context" |>.build
    for (_, doc) in docs do
      let context := "\t".intercalate doc.context.toList
      index := index.addDoc doc.id #[doc.id, doc.header, doc.content, context]
    return index

/--
A genre is indexable if there are instructions for constructing an index for use with elasticlunr.js.
-/
public class Indexable (genre : Verso.Doc.Genre) where
  /--
  The identifier for a part. A frontend must be able to map this to a URL (but not necessarily a
  whole HTML file, as {lit}`#id`s may be used).
  -/
  partId : genre.PartMetadata → Option String

  /--
  Computes the indexed header for a part. On {name}`none`, falls back to a default implementation.
  -/
  partHeader : Verso.Doc.Part genre → IndexM genre (Option String) := fun _ => pure none

  /--
  Computes a potentially abbreviated header name to show in contexts (e.g. an initialism for a long
  book title). Falls back to the chapter title.
  -/
  partShortContextName : Verso.Doc.Part genre → IndexM genre (Option String) := fun _ => pure none

  /--
  How to index block extensions.

  Return {name}`none` to fall back to the content of the contained blocks.
  -/
  block : genre.Block → Option ((Verso.Doc.Inline genre → IndexM genre String) → (Verso.Doc.Block genre → IndexM genre String) → Array (Verso.Doc.Block genre) → IndexM genre IndexDoc)

  /--
  How to index inline extensions.

  Return {name}`none` to fall back to the content of the contained inlines.
  -/
  inline : genre.Inline → Option ((Verso.Doc.Inline genre → IndexM genre String) → Array (Verso.Doc.Inline genre) → IndexM genre IndexDoc)

section
variable [idx : Indexable g] [traversePart : Verso.Doc.TraversePart g]

/--
Adds a header to the current context and updates the traversal context.
-/
public def IndexM.inPart (part : Verso.Doc.Part g) (act : IndexM g α) : IndexM g α := do
  let ctxHeader := (← idx.partShortContextName part).getD part.titleString
  withReader (fun ρ => (ρ.1.push ctxHeader, traversePart.inPart part ρ.2)) act

/--
Finds the index-ready text for the given inline. May add sub-items to the index as a side effect.
-/
public partial def inlineText (i : Verso.Doc.Inline g) : IndexM g String :=
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

/--
Finds the index-ready text for the given bock. May add sub-items to the index as a side effect.
-/
public partial def blockText (b : Verso.Doc.Block g) : IndexM g String :=
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

/--
Finds the index-ready text for the given part. May add sub-items to the index as a side effect.
-/
public partial def partText (p : Verso.Doc.Part g) : IndexM g String := do
  let header := (← idx.partHeader p).getD p.titleString

  let context ← IndexM.currentContext
  let content ← IndexM.inPart p do
    let content ← p.content.foldlM (init := "") fun s b => do return s ++ (← blockText b) ++ "\n\n"
    p.subParts.foldlM (init := content) fun s p' => do return s ++ (← partText p') ++ "\n\n"

  match p.metadata >>= idx.partId with
  | none => return header ++ "\n\n" ++ content
  | some id =>
    IndexM.save {id, header, context, content}
    return ""

/--
Constructs a set of documents that can be used with elasticlunr.js by emitting JavaScript arrays and
code to construct the index. Primarily useful for testing.
-/
public def mkIndexDocs (p : Verso.Doc.Part g) (ctx : g.TraverseContext) : Except String (Array IndexDoc) := do
  if p.metadata.bind idx.partId |>.isNone then
    throw "mkIndexDocs: No ID for root part"
  else
    match partText p (#[], ctx) {} with
    | .error e _ => throw e
    | .ok _ docs => return docs.fold (init := #[]) fun xs _ x => xs.push x

/--
Constructs an elasticlunr.js-compatible reverse index for the provided document.
-/
public def mkIndex (p : Verso.Doc.Part g) (ctx : g.TraverseContext) : Except String Index := do
  if p.metadata.bind idx.partId |>.isNone then
    throw "No ID for root part"
  else
   partText p |> discard |>.finalize ctx

end
