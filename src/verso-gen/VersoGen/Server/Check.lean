/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Server.Basic
public import VersoGen.Server.Expectations
import VersoGen.Random.Basic

set_option doc.verso true

/-!
Checks of the language server's answers for a generated document against the expectations that its
surface document gives. Besides the checks' results, the report records answers that the checks
allow but that differ from the surface document, so that a change in them is seen.
-/

namespace VersoGen.Server

open Lean Lean.Lsp

open VersoGen.Doc VersoGen.Doc.SurfaceDoc VersoGen.Genre VersoGen.Random

/-- A document symbol, as the server sends it. -/
structure DocSymbol where
  name : String
  kind : SymbolKind
  detail : String
  range : Lsp.Range
  selection : Lsp.Range
  children : Array DocSymbol
deriving Inhabited

-- `children` is looked up by name, which gives no proof that it is smaller than `j`.
partial def DocSymbol.ofJson (j : Json) : Except String DocSymbol := do
  let children ← match j.getObjVal? "children" with
    | .ok (.arr cs) => cs.mapM DocSymbol.ofJson
    | _ => pure #[]
  return {
    name := ← j.getObjValAs? String "name", kind := ← j.getObjValAs? SymbolKind "kind",
    detail := (j.getObjValAs? String "detail").toOption.getD "",
    range := ← j.getObjValAs? Lsp.Range "range",
    selection := ← j.getObjValAs? Lsp.Range "selectionRange",
    children
  }

/--
The part tree that document symbols give. Symbols of kind {lit}`String` are parts, and the others
describe blocks in them.
-/
def DocSymbol.partTree : DocSymbol → PartTree
  | { name, children, .. } => {
    title := name
    code := (children.filter (·.kind != .string)).map fun c =>
      { name := c.name, detail := c.detail.trimAscii.copy }
    subParts := (children.filter (·.kind == .string)).map DocSymbol.partTree
  }

def rangeContains (outer inner : Lsp.Range) : Bool :=
  outer.start ≤ inner.start && inner.«end» ≤ outer.«end»

/--
The problems with the ranges of symbols: a selection outside its range, or a child outside its
parent.
-/
def DocSymbol.rangeProblems : DocSymbol → Array String
  | { name, range, selection, children, .. } =>
    (if rangeContains range selection then #[]
     else #[s!"the selection of {name.quote} is outside its range"]) ++
    children.flatMap fun c =>
      (if rangeContains range c.range then #[]
       else #[s!"{c.name.quote} is outside {name.quote}"]) ++ c.rangeProblems

/-- A position as {lit}`line:character`, counted from 0. -/
def showPos (p : Lsp.Position) : String := s!"{p.line}:{p.character}"

/-- A range as {lit}`line:character-line:character`, counted from 0. -/
def showRange (r : Lsp.Range) : String := s!"{showPos r.start}-{showPos r.«end»}"

/-- The position of the second character of a range in a text. -/
def secondCharacter (fileMap : FileMap) (r : Lsp.Range) : Lsp.Position :=
  fileMap.utf8PosToLspPos ((fileMap.lspPosToUtf8Pos r.start).next fileMap.source)

/-- A number between {name}`lo` and {name}`hi`, or {name}`lo` if {name}`hi` is smaller. -/
def between (lo hi : Nat) : Plausible.Gen Nat :=
  return (← Plausible.Gen.choose Nat lo (max lo hi) (Nat.le_max_left ..)).val

/--
Positions at the starts of at most {name}`count` words in the lines from {name}`first`, chosen at
random.
-/
def wordStarts (fileMap : FileMap) (lines : Array String.Slice) (first count : Nat) :
    Plausible.Gen (Array Lsp.Position) := do
  let mut out := #[]
  let mut tries := 0
  while out.size < count && tries < 10 * count do
    tries := tries + 1
    let line := lines[← between first (lines.size - 1)]!
    let mut starts := #[]
    let mut pos := line.startInclusive.offset
    let mut prev := ' '
    for c in line.chars do
      if c != ' ' && prev == ' ' then starts := starts.push pos
      pos := pos + c
      prev := c
    if starts.isEmpty then continue
    out := out.push (fileMap.utf8PosToLspPos starts[← between 0 (starts.size - 1)]!)
  return out

/--
Five ranges of between one and ten whole lines, which start in the lines from {name}`first` and end
at the start of a line of the text, chosen at random.
-/
def lineRanges (lines : Array String.Slice) (first : Nat) : Plausible.Gen (Array Lsp.Range) := do
  let mut out := #[]
  for _ in [0:5] do
    let start ← between first (lines.size - 2)
    let stop := min (start + (← between 1 10)) (lines.size - 1)
    out := out.push ⟨⟨start, 0⟩, ⟨stop, 0⟩⟩
  return out

/-- Whether a range lies in a text's lines. -/
def inText (fileMap : FileMap) (lines : Array String.Slice) (r : Lsp.Range) : Bool :=
  let lineLength (line : String.Slice) :=
    (fileMap.utf8PosToLspPos line.endExclusive.offset).character
  r.start ≤ r.«end» && r.«end».line < lines.size &&
  r.start.character ≤ (lines[r.start.line]?.map lineLength).getD 0 &&
  r.«end».character ≤ (lines[r.«end».line]?.map lineLength).getD 0

def highlightRanges (j : Json) : Array Lsp.Range :=
  match j with
  | .arr xs => xs.filterMap fun x => (x.getObjValAs? Lsp.Range "range").toOption
  | _ => #[]

/-- Whether two arrays have the same ranges, in any order. -/
def sameRanges (a b : Array Lsp.Range) : Bool :=
  a.all b.contains && b.all a.contains && a.size == b.size

/--
The data of a response to a {lit}`textDocument/semanticTokens/range` request, five numbers for each
token. A {lit}`null` response has no tokens. Any other response that doesn't decode as
{name}`SemanticTokens`, or whose data length isn't a multiple of five, is an error that gives the
reason.
-/
public def semanticTokenData (j : Json) : Except String (Array Nat) := do
  if j.isNull then return #[]
  let tokens : SemanticTokens ← fromJson? j
  unless tokens.data.size % 5 == 0 do
    throw s!"the data has {tokens.data.size} numbers, which isn't a multiple of five"
  return tokens.data

/--
The pairs of crossing ranges among the folding ranges {name}`actual`, given as kind, start line and
end line. Two ranges cross when they overlap and neither contains the other.
-/
public def foldCrossings (actual : Array (Option String × Nat × Nat)) :
    Array ((Option String × Nat × Nat) × (Option String × Nat × Nat)) := Id.run do
  let mut crossing := #[]
  for (a, i) in actual.zipIdx do
    for b in actual.extract (i + 1) do
      let (_, s1, e1) := a
      let (_, s2, e2) := b
      let nested := (s1 ≤ s2 && e2 ≤ e1) || (s2 ≤ s1 && e1 ≤ e2)
      let disjoint := e1 < s2 || e2 < s1
      unless nested || disjoint do
        crossing := crossing.push (a, b)
  return crossing

/--
Checks the answers of the language server for the document {name}`surfaceDoc` of the genre profile
{name}`p`, whose concretized text is open as {name}`doc`. It returns a report and whether every
check passed. Each check that fails gives a line of the report that starts with {lit}`FAIL`.
* Document symbols: the part tree of the symbols is the surface document's, with the same parts and
  the same {lit}`lean` code blocks and {lit}`docstring` commands, and every selection and child lies
  in its symbol's range.
* Folding ranges: the ranges are exactly those that the surface document gives, none lies outside
  the document, and no two ranges cross.
* Links and footnotes: highlighting at a definition gives the definition and every use. The report
  records each distinct answer that go to definition and highlighting give at a use.
* Hover: at 20 word starts drawn from a seed that is the hash of {name}`name`, no request fails and
  every range lies in the document.
* Semantic tokens: for 5 line ranges drawn from the next seed, every response decodes as
  {name}`semanticTokenData` requires, and every token lies in the document. The report says whether
  some tokens lie outside the requested range or start where the previous one starts.
Besides the failures, the report records only these answers, with no positions or counts.
-/
def checkOpenDoc (doc : OpenDoc) (p : GenreProfile) (surfaceDoc : Part) (text name : String) :
    Ipc.IpcM (String × Bool) := do
  let server := doc.server
  let lines := (text.split '\n').toArray
  let fileMap := FileMap.ofString text
  let report ← IO.mkRef s!"document {name}\n"
  let ok ← IO.mkRef true
  let say (line : String) : IO Unit := report.modify (· ++ line ++ "\n")
  let fail (msg : String) : IO Unit := do
    ok.set false
    say s!"  FAIL {msg}"
  -- Document symbols
  let textDocument : TextDocumentIdentifier := { uri := doc.uri }
  match ← server.request? "textDocument/documentSymbol" ({ textDocument } : DocumentSymbolParams)
    with
  | .error e => fail s!"document symbols: {e}"
  | .ok (.arr xs) =>
    match xs.mapM DocSymbol.ofJson with
    | .error e => fail s!"document symbols: {e}"
    | .ok syms =>
      let expected := partTree surfaceDoc
      let actual := syms.map DocSymbol.partTree
      let problems := syms.flatMap DocSymbol.rangeProblems
      if actual != #[expected] then
        fail s!"document symbols: the part tree differs from the surface document's\n    \
          expected {repr expected}\n    actual {repr actual}"
      for pr in problems do fail s!"document symbols: {pr}"
  | .ok _ => fail "document symbols: not an array"
  -- Folding ranges
  match ← server.request? "textDocument/foldingRange" ({ textDocument } : FoldingRangeParams) with
  | .error e => fail s!"folding ranges: {e}"
  | .ok j =>
    let actual : Array (Option String × Nat × Nat) := match j with
      | .arr xs => xs.filterMap fun x => do
        return ((x.getObjValAs? String "kind").toOption,
          ← (x.getObjValAs? Nat "startLine").toOption, ← (x.getObjValAs? Nat "endLine").toOption)
      | _ => #[]
    let expected := expectedFolds p surfaceDoc
    let key (f : Fold) := (f.kind?, f.startLine, f.endLine)
    let mut missing := expected.map key
    let mut extra := #[]
    for a in actual do
      if missing.contains a then missing := missing.erase a else extra := extra.push a
    let showF (f : Option String × Nat × Nat) := s!"{f.2.1}-{f.2.2}{(f.1.map (" " ++ ·)).getD ""}"
    unless missing.isEmpty && extra.isEmpty do
      fail s!"folding ranges: missing {missing.map showF}, unexpected {extra.map showF}"
    let eof := lines.size - 1
    let outside := actual.filter fun (_, s, e) => s > e || e > eof
    unless outside.isEmpty do
      fail s!"folding ranges outside the document: {outside.map showF}"
    let crossing := foldCrossings actual
    unless crossing.isEmpty do
      fail s!"folding ranges cross: {crossing.map fun (a, b) => (showF a, showF b)}"
  -- Links and footnotes
  let mut atUses := #[]
  for r in labelRanges p surfaceDoc do
    let params : DocumentHighlightParams :=
      { textDocument, position := secondCharacter fileMap r.definition }
    match ← server.request? "textDocument/documentHighlight" params with
    | .error e => fail s!"highlight at the definition of {r.label}: {e}"
    | .ok j =>
      let expected := #[r.definition] ++ r.uses
      unless sameRanges (highlightRanges j) expected do
        fail s!"highlight at the definition of {r.label}: expected {expected.map showRange}, \
          got {(highlightRanges j).map showRange}"
    for u in r.uses do
      let atUse := secondCharacter fileMap u
      let params : TextDocumentPositionParams := { textDocument, position := atUse }
      let goto ← match ← server.request? "textDocument/definition" params with
        | .error e => pure s!"fails: {e}"
        | .ok (.arr xs) =>
          let here := xs.filter fun x =>
            (x.getObjValAs? String "targetUri").toOption == some doc.uri
          let targets := here.filterMap fun x => (x.getObjValAs? Lsp.Range "targetRange").toOption
          if targets.isEmpty then pure "finds nothing in this document"
          else if targets.all (· == r.definition) then pure "finds the definition"
          else pure "finds other ranges"
        | .ok _ => pure "finds nothing in this document"
      let params : DocumentHighlightParams := { textDocument, position := atUse }
      let hl ← match ← server.request? "textDocument/documentHighlight" params with
        | .error e => pure s!"fails: {e}"
        | .ok j =>
          let got := highlightRanges j
          if sameRanges got #[u] then pure "only this use"
          else if sameRanges got (#[r.definition] ++ r.uses) then
            pure "the definition and all uses"
          else pure "other ranges"
      let atUse := s!"  at a use: go to definition {goto}; highlight {hl}"
      unless atUses.contains atUse do atUses := atUses.push atUse
  for atUse in atUses do say atUse
  -- Hover
  -- The body starts at the first line range after that of the `#doc` line.
  let bodyStart := ((layout p surfaceDoc)[1]?.map (·.first)).getD lines.size
  let seed := (hash name).toNat
  let positions := runWithSeed (wordStarts fileMap lines bodyStart 20) seed
  for pos in positions do
    match ← server.request? "textDocument/hover" ({ textDocument, position := pos } : HoverParams)
      with
    | .error e => fail s!"hover at {showPos pos}: {e}"
    | .ok .null => pure ()
    | .ok j =>
      if let .ok r := j.getObjValAs? Lsp.Range "range" then
        unless inText fileMap lines r do
          fail s!"hover at {showPos pos}: range {showRange r} outside the document"
  -- Semantic tokens
  let mut outsideRange := false
  let mut sameStart := false
  for range in runWithSeed (lineRanges lines bodyStart) (seed + 1) do
    let params : SemanticTokensRangeParams := { textDocument, range }
    match ← server.request? "textDocument/semanticTokens/range" params with
    | .error e => fail s!"semantic tokens: {showRange range}: {e}"
    | .ok j =>
      match semanticTokenData j with
      | .error e => fail s!"semantic tokens: {showRange range}: {e}"
      | .ok data =>
        let mut line := 0
        let mut char := 0
        let mut prevStart : Option Lsp.Position := none
        for i in [0:data.size / 5] do
          let dl := data[5 * i]!
          let ds := data[5 * i + 1]!
          let len := data[5 * i + 2]!
          line := line + dl
          char := if dl == 0 then char + ds else ds
          let tok : Lsp.Range := ⟨⟨line, char⟩, ⟨line, char + len⟩⟩
          unless inText fileMap lines tok do
            fail s!"semantic tokens: token {showRange tok} outside the document"
          unless rangeContains range tok do outsideRange := true
          if prevStart == some tok.start then sameStart := true
          prevStart := some tok.start
  if outsideRange then say "  semantic tokens: some outside the requested range"
  if sameStart then say "  semantic tokens: some start where the previous one starts"
  return (← report.get, ← ok.get)

/--
Checks the language server's answers for a generated document, which is the surface document
{name}`surfaceDoc` of the genre profile {name}`p` concretized and written to {name}`path`. The
server runs in the Lake workspace at {name}`root`. The result is a report and whether every check
passed. {name}`name` identifies the document in the report and determines the positions of the hover
and semantic token requests.
-/
public def checkAnswers (root path : System.FilePath) (p : GenreProfile) (surfaceDoc : Part)
    (name : String) : IO (String × Bool) :=
  withServer root #[] fun server => do
    let text := concretizeDocument p surfaceDoc
    let doc ← server.openDoc path text
    doc.wait
    checkOpenDoc doc p surfaceDoc text name
