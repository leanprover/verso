/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Random.Lorem
public import VersoGen.Doc.Basic

set_option doc.verso true

/-!
Genre profiles say what generated documents may use from their genre and which surface documents
are valid for the genre. The generator and the edits keep to a profile, so that every generated
document and every edited document elaborates without errors.
-/

namespace VersoGen.Genre

open VersoGen.Doc.SurfaceDoc VersoGen.Random

open Lean

/-- The parameters of document generation. -/
public structure Params where
  topLevelBlocks : Nat := 12
  /-- The deepest nesting of directives. -/
  directiveDepth : Nat := 2
  /-- The relative weights of the kinds of surface document blocks for top-level blocks. -/
  topLevelMix : List (BlockKind × Nat) :=
    [(.para, 10), (.ul, 2), (.ol, 1), (.dl, 1), (.blockquote, 1), (.directive, 3), (.command, 1)]
  /-- The relative weights of the kinds of surface document blocks for blocks inside others. -/
  nestedMix : List (BlockKind × Nat) := [(.para, 10), (.ul, 1), (.directive, 1)]
  /-- The chance, in percent, that each block is a code block, where the genre allows one there. -/
  codeBlockChance : Nat := 15
  /-- How long each proof in generated Lean code sleeps, in milliseconds. -/
  proofWeight : Nat := 0
  /-- The number of parts below the document. -/
  parts : Nat := 3
  /-- The deepest nesting of parts below the document. -/
  partDepth : Nat := 2
  /-- The chance, in percent, that each part, the document included, has a metadata block. -/
  metadataChance : Nat := 30
  /-- The largest number of sentences in a paragraph. -/
  paragraphLength : Nat := 3
  /-- The chance, in percent, that a sentence has an inline element other than text. -/
  inlineChance : Nat := 30
  /--
  The chance, in percent, that each inline element is a link or footnote use with a new definition,
  where the genre has link or footnote definitions.
  -/
  referenceChance : Nat := 20
deriving ToJson, FromJson, Repr, Inhabited

/-- A replacement of some lines of a code block's contents. -/
public structure LineEdit where
  /-- What the edit does, for people reading edit scripts. -/
  label : String
  /-- The first replaced line. -/
  start : Nat
  /-- The number of replaced lines. -/
  count : Nat
  lines : Array String
deriving ToJson, FromJson, BEq, Repr, Inhabited

/--
The generator of a kind of code block's contents, as lines of text, and the edits that keep the
contents valid.
-/
public structure CodeBlockContent where
  generate : Params → LoremGen (Array String)
  /--
  The edits that are valid for some contents. Each edit is a generator that runs when the edit is
  chosen, and it gives {name}`none` when the edit doesn't fit the contents.
  -/
  edits : Params → Array String → List (LoremGen (Option LineEdit))
deriving Inhabited

/-- A directive that generated documents may use. -/
public structure DirectiveSpec where
  name : String
  /-- A generator of valid arguments. -/
  args : LoremGen String := pure ""
  /-- The kinds of surface document blocks that the directive may contain. -/
  contains : List BlockKind
  /-- Whether the directive may occur inside another directive. -/
  mayNest : Bool := true
deriving Inhabited

/-- A code block that generated documents may use. -/
public structure CodeBlockSpec where
  name : String
  /-- A generator of valid arguments. -/
  args : LoremGen String := pure ""
  content : CodeBlockContent
deriving Inhabited

/-- A block command that generated documents may use. -/
public structure CommandSpec where
  name : String
  /-- A generator of valid arguments. -/
  args : LoremGen String := pure ""
deriving Inhabited

/-- A role that generated documents may use. -/
public structure RoleSpec where
  name : String
  /-- A generator of valid arguments. -/
  args : LoremGen String := pure ""
  /-- Whether the role has inline content. A role without it has inline code. -/
  inlineContent : Bool := true
  /-- A generator of the role's inline code, for a role without inline content. -/
  code : LoremGen String := pure "x"
deriving Inhabited

/-- A metadata field that a part may set. -/
public structure MetadataField where
  name : String
  /-- A generator of valid values, as Lean source. -/
  value : LoremGen String
deriving Inhabited

/--
The generator's configuration for a genre: the imports, options and genre of generated documents.
It also lists the directives, code blocks, block commands, roles and metadata that they may use.
-/
public structure GenreProfile where
  /-- The profile's name, which edit scripts use to refer to it. -/
  name : String
  imports : List String
  opens : List String := []
  /-- The genre, as Lean source. -/
  genre : String
  /-- Options set before the document, as names and values in Lean source. -/
  options : List (String × String) := []
  directives : List DirectiveSpec := []
  codeBlocks : List CodeBlockSpec := []
  commands : List CommandSpec := []
  roles : List RoleSpec := []
  metadata : List MetadataField := []
  linkDefs : Bool := true
  footnoteDefs : Bool := true
deriving Inhabited

/-- The text before a document's `#doc` command. -/
public def GenreProfile.header (p : GenreProfile) : Array String :=
  let imports := p.imports.toArray.map ("import " ++ ·)
  let opens := if p.opens.isEmpty then #[] else #["open " ++ " ".intercalate p.opens]
  let options := p.options.toArray.map fun (o, v) => s!"set_option {o} {v}"
  imports ++ #[""] ++ (if opens.isEmpty && options.isEmpty then #[] else opens ++ options ++ #[""])

/-- The line of a document's `#doc` command, for a document with the given title. -/
public def GenreProfile.docLine (p : GenreProfile) (title : String) : String :=
  s!"#doc ({p.genre}) {title.quote} =>"

/-- Quotes the strings that a generator gives, for string-valued arguments and metadata. -/
public def quoted (g : LoremGen String) : LoremGen String := do return (← g).quote

/-- Whether a string contains any of the characters of another. -/
def hasAnyOf (s chars : String) : Bool := s.any fun (c : Char) => chars.contains c

namespace GenreProfile

variable (p : GenreProfile)

def directive? (name : String) : Option DirectiveSpec := p.directives.find? (·.name == name)

public def codeBlock? (name : String) : Option CodeBlockSpec := p.codeBlocks.find? (·.name == name)

public def command? (name : String) : Option CommandSpec := p.commands.find? (·.name == name)

def role? (name : String) : Option RoleSpec := p.roles.find? (·.name == name)

/--
Whether an inline is valid. Links and roles contain only text, emphasis, bold and inline code, and
emphasis and bold don't nest in themselves.
-/
partial def validInline (inEmph inBold inSpan : Bool) : Inline → Bool
  | .text s => !s.isEmpty && !s.startsWith " " && !s.endsWith " "
  | .emph c => !inEmph && !c.isEmpty && c.all (validInline true inBold inSpan)
  | .bold c => !inBold && !c.isEmpty && c.all (validInline inEmph true inSpan)
  | .link c t =>
    !inSpan && !c.isEmpty && c.all (validInline inEmph inBold true) &&
    match t with
    | .url u => !u.isEmpty && !hasAnyOf u " )\n"
    | .ref n => !n.isEmpty
  | .role name _ c =>
    !inSpan &&
    match p.role? name with
    | none => false
    | some spec =>
      if spec.inlineContent then !c.isEmpty && c.all (validInline inEmph inBold true)
      else c matches #[.code _] && c.all (validInline inEmph inBold true)
  | .image alt url => !inSpan && !hasAnyOf alt " []\n" && !url.isEmpty
  | .code s =>
    !s.isEmpty && !s.startsWith " " && !s.endsWith " " && !s.any (· == '`') && !s.any (· == '\n')
  | .footnote n => !inSpan && !n.isEmpty

/-- Whether some inlines are valid as a paragraph's contents. -/
def validInlines (xs : Array Inline) : Bool :=
  !xs.isEmpty && xs.all (p.validInline false false false)

/--
Whether no two neighboring blocks are description lists, which would be concretized as one
description list.
-/
def nonAdjacentDescriptionLists (bs : Array Block) : Bool :=
  (bs.zip (bs.extract 1)).all fun (a, b) => !(a matches .dl .. && b matches .dl ..)

/-- Whether a block is a valid link or footnote definition. -/
def validDef : Block → Bool
  | .linkDef name url =>
    p.linkDefs && !name.isEmpty && !name.startsWith "^" && !hasAnyOf name " []\n" &&
    !url.isEmpty && !url.any (· == '\n')
  | .footnoteDef name c =>
    p.footnoteDefs && !name.isEmpty && !hasAnyOf name " []\n" && p.validInlines c
  | _ => false

/-- Whether a block is valid. {lit}`inDirective` says whether it is inside a directive. -/
public partial def validBlock (inDirective : Bool) (b : Block) : Bool :=
  let blocks (cs : Array Block) :=
    !cs.isEmpty && cs.all (validBlock inDirective) && nonAdjacentDescriptionLists cs
  match b with
  | .para c => p.validInlines c
  | .ul items | .ol items => !items.isEmpty && items.all blocks
  | .dl items => !items.isEmpty && items.all fun (term, bs) => p.validInlines term && blocks bs
  | .blockquote bs => blocks bs
  | .directive name _ bs =>
    match p.directive? name with
    | none => false
    | some spec =>
      (!inDirective || spec.mayNest) && !bs.isEmpty && bs.all (spec.contains.contains ·.kind) &&
      bs.all (validBlock true) && nonAdjacentDescriptionLists bs
  | .code name _ lines => (p.codeBlock? name).isSome && !lines.isEmpty
  | .command name _ => (p.command? name).isSome
  | .linkDef .. | .footnoteDef .. => false

/-- Whether a part is valid. Link and footnote definitions occur only among parts' blocks. -/
partial def validPart (part : Part) : Bool :=
  let fields := part.metadata.map (·.1)
  !part.title.isEmpty && !part.title.any (· == '\n') &&
  fields.all (fun f => p.metadata.any (·.name == f)) &&
  fields.all (fun f => (fields.filter (· == f)).size == 1) &&
  part.blocks.all (fun b => p.validDef b || p.validBlock false b) &&
  nonAdjacentDescriptionLists part.blocks &&
  part.subParts.all validPart

/--
Whether a document is valid: its parts and blocks are valid, every label that is used has a
definition, and no two definitions have the same label.
-/
public def valid (doc : Part) : Bool :=
  let refs := doc.refs
  let defs := doc.defs
  p.validPart doc &&
  refs.links.all defs.links.contains && refs.footnotes.all defs.footnotes.contains &&
  defs.links.allDiff && defs.footnotes.allDiff
