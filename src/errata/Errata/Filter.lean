/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Filters over the inventory: the predicates `name(…)`, `file(…)`, `exe(…)`, and `tag(…)`, the
constants `all()` and `none()`, `default()` for the profile's default filter, and the operators
`|`, `&`, `\`, and `!`. Filters are parsed in three layers: the expression, the text of each
predicate's matcher with its escapes, and, for a glob matcher, the glob. Every node of a parsed filter has its span in the filter's text.
-/
module

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace Errata.Filter

/-- Where a filter's text came from, for messages that name a place in it. -/
inductive Source where
  /-- A command-line argument, named by a label such as {lit}`--filter`. -/
  | argument (label : String)
  /--
  A string in a file. {name}`line` and {name}`col` are the position of the string's opening
  delimiter, with lines counted from one and columns from zero. {name}`positions` holds the line and
  column of each character of the filter's text, then of the closing delimiter, and is empty when
  the string's characters have no known positions.
  -/
  | file (path : String) (line col : Nat) (positions : Array (Nat × Nat))
deriving Repr, Inhabited, DecidableEq

/--
The place {name}`offset` characters into the filter's text, as a message's prefix. In a file, it is
the line and column of that character, or the string's own position and the offset when the
characters have no known positions.
-/
def Source.at (s : Source) (offset : Nat) : String :=
  match s with
  | .argument label => s!"{label}:{offset}"
  | .file path line col positions =>
    match positions[offset]? <|> positions.back? with
    | some (l, c) => s!"{path}:{l}:{c}"
    | none => s!"{path}:{line}:{col}: at offset {offset} in the filter"

/--
A span of a filter's text: the offsets, in characters, of its first character and past its last.
-/
structure Span where
  /-- The offset of the first character. -/
  start : Nat := 0
  /-- The offset past the last character. -/
  stop : Nat := 0
deriving Repr, Inhabited, DecidableEq

/-- An error in a filter's text, at an offset into it. -/
structure ParseError where
  /-- The offset, in characters, where the error was found. -/
  offset : Nat
  /-- What is wrong. -/
  message : String
deriving Repr, Inhabited, DecidableEq

/-- The error as a message that names its place in the filter's source. -/
def ParseError.render (e : ParseError) (source : Source) : String :=
  s!"{source.at e.offset}: {e.message}"

/-! # Globs -/

/-- One step of a glob pattern after alternation is expanded. -/
inductive GlobPart where
  /-- A character, matched literally. -/
  | lit (c : Char)
  /-- Any one character. -/
  | any
  /-- One character in the ranges, or not in them when {name}`negated`. -/
  | cls (negated : Bool) (ranges : Array (Char × Char))
  /-- Any sequence of characters, possibly empty. -/
  | star
deriving Repr, Inhabited, DecidableEq

/-- Whether a class step accepts a character. -/
def GlobPart.classAccepts (negated : Bool) (ranges : Array (Char × Char)) (c : Char) : Bool :=
  ranges.any (fun (lo, hi) => lo ≤ c && c ≤ hi) != negated

/--
A glob, as the patterns that its alternation expands to. Strings match the glob when they match one
of the patterns, each of which holds only literals, {lit}`?`, classes, and {lit}`*`.
-/
structure Glob where
  /-- The expanded patterns. -/
  patterns : Array (Array GlobPart) := #[]
deriving Repr, Inhabited, DecidableEq

/-- How many patterns the alternation of one glob may expand to. -/
def maxAlternatives : Nat := 10000

/-- How many steps, summed over its expanded patterns, the alternation of one glob may expand to. -/
def maxExpandedSize : Nat := 1000000

/-- How deeply braces may nest in a glob, and parentheses and {lit}`!` in a filter. -/
def maxDepth : Nat := 100

/-- A glob before its alternation is expanded. -/
private inductive GlobNode where
  | part (p : GlobPart)
  | alt (alternatives : Array (Array GlobNode))
deriving Inhabited

/-- The state of the glob parser: the characters, the source offset of each, and the position. -/
private structure GlobInput where
  chars : Array Char
  offsets : Array Nat
  /-- The source offset just past the text, for an error at the end. -/
  endOffset : Nat

private def GlobInput.offsetAt (g : GlobInput) (i : Nat) : Nat :=
  g.offsets[i]?.getD g.endOffset

/--
Parses a sequence of glob parts starting at {name}`i`, up to the end or, inside braces, up to the
{lit}`,` or {lit}`}` that ends an alternative. The result is the parts and the position after them.
-/
private partial def parseGlobSeq (g : GlobInput) (i : Nat) (depth : Nat) (inBraces : Bool) :
    Except ParseError (Array GlobNode × Nat) := do
  let mut i := i
  let mut out : Array GlobNode := #[]
  let mut lastStar := false
  while h : i < g.chars.size do
    let c := g.chars[i]
    if inBraces && (c == ',' || c == '}') then break
    match c with
    | '*' =>
      if lastStar then
        throw { offset := g.offsetAt i,
                message := "two '*' in a row; one '*' already matches any sequence of characters" }
      out := out.push (.part .star)
      lastStar := true
      i := i + 1
    | '?' =>
      out := out.push (.part .any)
      lastStar := false
      i := i + 1
    | '[' =>
      let start := i
      i := i + 1
      let mut negated := false
      if let some n := g.chars[i]? then
        if n == '!' || n == '^' then
          negated := true
          i := i + 1
      let mut ranges : Array (Char × Char) := #[]
      let mut first := true
      let mut closed := false
      while h' : i < g.chars.size do
        let lo := g.chars[i]
        if lo == ']' && !first then
          closed := true
          i := i + 1
          break
        first := false
        match g.chars[i + 1]?, g.chars[i + 2]? with
        | some '-', some hi =>
          if hi == ']' then
            ranges := ranges.push (lo, lo)
            i := i + 1
          else
            if hi < lo then
              throw { offset := g.offsetAt i, message := s!"the range '{lo}-{hi}' is empty" }
            ranges := ranges.push (lo, hi)
            i := i + 3
        | _, _ =>
          ranges := ranges.push (lo, lo)
          i := i + 1
      unless closed do
        throw { offset := g.offsetAt start, message := "'[' is not closed by ']'" }
      out := out.push (.part (.cls negated ranges))
      lastStar := false
    | '{' =>
      if depth ≥ maxDepth then
        throw { offset := g.offsetAt i, message := s!"braces nest more than {maxDepth} deep" }
      let start := i
      i := i + 1
      let mut alternatives : Array (Array GlobNode) := #[]
      let mut closed := false
      repeat
        let (alt, next) ← parseGlobSeq g i (depth + 1) true
        alternatives := alternatives.push alt
        i := next
        match g.chars[i]? with
        | some ',' => i := i + 1
        | some '}' =>
          i := i + 1
          closed := true
          break
        | _ => break
      unless closed do
        throw { offset := g.offsetAt start, message := "'{' is not closed by '}'" }
      out := out.push (.alt alternatives)
      lastStar := false
    | c =>
      out := out.push (.part (.lit c))
      lastStar := false
      i := i + 1
  return (out, i)

/-- Appends a part to a pattern, merging a {lit}`*` into a {lit}`*` that precedes it. -/
private def pushPart (p : Array GlobPart) (x : GlobPart) : Array GlobPart :=
  if x == .star && p.back? == some .star then p else p.push x

/-- The number of steps in all of the patterns. -/
private def expandedSize (patterns : Array (Array GlobPart)) : Nat :=
  patterns.foldl (· + ·.size) 0

/--
The patterns that a sequence of glob nodes expands to, each appended to every pattern in
{name}`prefixes`. Fails once the patterns number more than {name}`maxAlternatives`, or their steps
more than {name}`maxExpandedSize`, checking each bound before the patterns that exceed it are made.
-/
private partial def expandGlob (prefixes : Array (Array GlobPart)) (nodes : Array GlobNode) :
    Except String (Array (Array GlobPart)) := do
  let tooLarge := s!"the glob's alternatives expand to more than {maxExpandedSize} characters"
  let mut acc := prefixes
  let mut size := expandedSize prefixes
  for n in nodes do
    match n with
    | .part p =>
      -- Each pattern grows by one step at most.
      if size + acc.size > maxExpandedSize then throw tooLarge
      acc := acc.map (pushPart · p)
      size := expandedSize acc
    | .alt alternatives =>
      let mut next := #[]
      let mut nextSize := 0
      for a in alternatives do
        let expanded ← expandGlob acc a
        next := next ++ expanded
        nextSize := nextSize + expandedSize expanded
        if next.size > maxAlternatives then
          throw s!"the glob's alternatives expand to more than {maxAlternatives} patterns"
        if nextSize > maxExpandedSize then throw tooLarge
      acc := next
      size := nextSize
  return acc

/--
Parses a glob from its characters. {name}`offsets` gives the source offset of each character, and
{name}`endOffset` the offset past the last, so that an error names its place in the filter's text.
-/
def Glob.parse (chars : Array Char) (offsets : Array Nat) (endOffset : Nat) :
    Except ParseError Glob := do
  let g : GlobInput := { chars, offsets, endOffset }
  let (nodes, _) ← parseGlobSeq g 0 0 false
  match expandGlob #[#[]] nodes with
  | .ok patterns => return { patterns }
  | .error message => throw { offset := g.offsetAt 0, message }

/-- Parses a glob from a string, with offsets counted from the string's start. -/
def Glob.ofString (s : String) : Except ParseError Glob :=
  let chars := s.toList.toArray
  Glob.parse chars (Array.range chars.size) chars.size

/--
Whether the pattern matches the whole string. The walk keeps one place to resume: the most recent
{lit}`*` and the position in the string after the characters it has taken so far. On a mismatch the
walk resumes there, with that {lit}`*` taking one more character, so no earlier {lit}`*` is revisited
and nothing recurses over the string.
-/
def matchPattern (p : Array GlobPart) (s : Array Char) : Bool := Id.run do
  let mut px := 0
  let mut sx := 0
  -- The resume point: the pattern position after the latest `*`, and the string position that the
  -- next attempt starts from. `sx` stays at or above `restartSx - 1`, and `restartSx` grows by one at
  -- each restart, so the loop ends.
  let mut restartPx := 0
  let mut restartSx := 0
  while px < p.size || sx < s.size do
    if h : px < p.size then
      match p[px] with
      | .star =>
        restartPx := px + 1
        restartSx := sx + 1
        px := px + 1
        continue
      | .any =>
        if sx < s.size then
          px := px + 1
          sx := sx + 1
          continue
      | .lit c =>
        if h' : sx < s.size then
          if s[sx] == c then
            px := px + 1
            sx := sx + 1
            continue
      | .cls negated ranges =>
        if h' : sx < s.size then
          if GlobPart.classAccepts negated ranges s[sx] then
            px := px + 1
            sx := sx + 1
            continue
    if 0 < restartSx && restartSx ≤ s.size then
      px := restartPx
      sx := restartSx
      restartSx := restartSx + 1
      continue
    return false
  return true

/-- Whether the glob matches the whole string. -/
def Glob.matches (g : Glob) (s : String) : Bool :=
  let chars := s.toList.toArray
  g.patterns.any (matchPattern · chars)

/-! # Filters -/

/-- The predicates of a filter. -/
inductive Predicate where
  /-- The test's name. -/
  | name
  /-- The file that the inventory records for the test. -/
  | file
  /-- The test executable's name. -/
  | exe
  /-- One of the test's tags. -/
  | tag
deriving Repr, Inhabited, DecidableEq

/-- The predicate's keyword. -/
def Predicate.keyword : Predicate → String
  | .name => "name"
  | .file => "file"
  | .exe => "exe"
  | .tag => "tag"

/-- How a matcher compares its text. -/
inductive Mode where
  /-- The text is equal to the whole string. -/
  | equal
  /-- The text is contained in the string. -/
  | contains
  /-- The whole string matches the glob that the text denotes. -/
  | glob
deriving Repr, Inhabited, DecidableEq

/--
The mode of a matcher with no prefix: containment for names, a glob for files and executables, and
equality for tags.
-/
def Predicate.defaultMode : Predicate → Mode
  | .name => .contains
  | .file | .exe => .glob
  | .tag => .equal

/-- The prefix character that selects a mode. -/
def Mode.prefix : Mode → Char
  | .equal => '='
  | .contains => '~'
  | .glob => '#'

/--
A predicate's argument: the mode, the text after its escapes are read, and the glob it denotes.
-/
structure Matcher where
  /-- How the text is compared. -/
  mode : Mode
  /-- The text, with its escapes read. -/
  text : String
  /-- The glob that the text denotes, for the glob mode. -/
  glob : Glob := {}
deriving Repr, Inhabited, DecidableEq

/-- Whether the matcher accepts a string. -/
def Matcher.matches (m : Matcher) (s : String) : Bool :=
  match m.mode with
  | .equal => s == m.text
  | .contains => (s.find? m.text).isSome
  | .glob => m.glob.matches s

/-- A parsed filter. Every node has its span in the filter's text. -/
inductive Expr where
  /-- A predicate applied to a matcher. -/
  | atom (predicate : Predicate) (matcher : Matcher) (span : Span)
  /-- Every test. -/
  | all (span : Span)
  /-- No test. -/
  | none (span : Span)
  /-- The tests that the profile's default filter selects. -/
  | default (span : Span)
  /-- The tests that the operand leaves out. -/
  | not (e : Expr) (span : Span)
  /-- The tests that both operands select. -/
  | and (a b : Expr) (span : Span)
  /-- The tests that the left operand selects and the right does not. -/
  | diff (a b : Expr) (span : Span)
  /-- The tests that either operand selects. -/
  | or (a b : Expr) (span : Span)
deriving Repr, Inhabited, DecidableEq

/-- The span of a filter node. -/
def Expr.span : Expr → Span
  | .atom _ _ s | .all s | .none s | .default s | .not _ s | .and _ _ s | .diff _ _ s
  | .or _ _ s => s

/-- The filter with every span replaced by the empty span at zero, for comparing structure alone. -/
def Expr.forgetSpans : Expr → Expr
  | .atom p m _ => .atom p m {}
  | .all _ => .all {}
  | .none _ => .none {}
  | .default _ => .default {}
  | .not e _ => .not e.forgetSpans {}
  | .and a b _ => .and a.forgetSpans b.forgetSpans {}
  | .diff a b _ => .diff a.forgetSpans b.forgetSpans {}
  | .or a b _ => .or a.forgetSpans b.forgetSpans {}

/-- What a filter is evaluated against: one test of the inventory. -/
structure Record where
  /-- The test's name. -/
  name : String
  /-- The file that the inventory records for the test, or the empty string. -/
  file : String := ""
  /-- The test executable's name. -/
  exe : String
  /-- The test's tags. -/
  tags : Array String := #[]
deriving Repr, Inhabited

/--
Whether the filter selects the test. {name}`dflt` is whether the default filter selects it, which is
what {lit}`default()` stands for.
-/
def Expr.eval (e : Expr) (r : Record) (dflt : Bool := true) : Bool :=
  match e with
  | .atom .name m _ => m.matches r.name
  | .atom .file m _ => m.matches r.file
  | .atom .exe m _ => m.matches r.exe
  | .atom .tag m _ => r.tags.any m.matches
  | .all _ => true
  | .none _ => false
  | .default _ => dflt
  | .not e _ => !e.eval r dflt
  | .and a b _ => a.eval r dflt && b.eval r dflt
  | .diff a b _ => a.eval r dflt && !b.eval r dflt
  | .or a b _ => a.eval r dflt || b.eval r dflt

/--
Whether the filter can select a test of the executable named {name}`exe`, when only the executable's
name is known: {lean}`some true` when it selects every test of the executable, {lean}`some false`
when it selects none, and {lean}`none` when that depends on the tests. {name}`dflt` is the same
answer for the default filter.
-/
def Expr.evalExe (e : Expr) (exe : String) (dflt : Option Bool := some true) : Option Bool :=
  match e with
  | .atom .exe m _ => some (m.matches exe)
  | .atom _ _ _ => Option.none
  | .all _ => some true
  | .none _ => some false
  | .default _ => dflt
  | .not e _ => (e.evalExe exe dflt).map (!·)
  | .and a b _ => and3 (a.evalExe exe dflt) (b.evalExe exe dflt)
  | .diff a b _ => and3 (a.evalExe exe dflt) ((b.evalExe exe dflt).map (!·))
  | .or a b _ => (and3 ((a.evalExe exe dflt).map (!·)) ((b.evalExe exe dflt).map (!·))).map (!·)
where
  /-- Conjunction of two answers that may be unknown: false when either is false. -/
  and3 : Option Bool → Option Bool → Option Bool
    | some false, _ | _, some false => some false
    | some true, some true => some true
    | _, _ => Option.none

/-- The span of the first {lit}`default()` in the filter, if it has one. -/
def Expr.defaultSpan? : Expr → Option Span
  | .default s => some s
  | .atom .. | .all _ | .none _ => Option.none
  | .not e _ => e.defaultSpan?
  | .and a b _ | .diff a b _ | .or a b _ => a.defaultSpan? <|> b.defaultSpan?

/-- Every atom of the filter, in the order of the text. -/
def Expr.atoms : Expr → Array (Predicate × Matcher × Span)
  | .atom p m s => #[(p, m, s)]
  | .all _ | .none _ | .default _ => #[]
  | .not e _ => e.atoms
  | .and a b _ | .diff a b _ | .or a b _ => a.atoms ++ b.atoms

/-! # Parsing -/

/-- The filter parser: the characters of the text, and the position in them. -/
private abbrev P := ReaderT (Array Char) (StateT Nat (Except ParseError))

private def fail (offset : Nat) (message : String) : P α :=
  throw { offset, message }

private def peek : P (Option Char) := do
  return (← read)[← get]?

private def skipWs : P Unit := do
  while (← peek).any (·.isWhitespace) do modify (· + 1)

/-- A character as a message shows it. -/
private def showChar (c : Char) : String :=
  if c.toNat < 0x20 then s!"U+{String.ofList (Nat.toDigits 16 c.toNat)}" else s!"'{c}'"

private def expect (c : Char) : P Unit := do
  match ← peek with
  | some d => if d == c then modify (· + 1) else fail (← get) s!"expected '{c}', found {showChar d}"
  | none => fail (← get) s!"expected '{c}'"

/--
Reads the hexadecimal digits and the {lit}`}` of a {lit}`\u{…}` escape, whose {lit}`\` is at
{name}`start`.
-/
private def unicodeEscape (start : Nat) : P Char := do
  expect '{'
  let mut value := 0
  let mut digits := 0
  repeat
    match ← peek with
    | some '}' =>
      modify (· + 1)
      break
    | some c =>
      let d? : Option Nat :=
        if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
        else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
        else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
        else none
      let some d := d? | fail (← get) ("expected a hexadecimal digit or '}', found " ++ showChar c)
      value := value * 16 + d
      digits := digits + 1
      if digits > 6 then fail start "a '\\u{…}' escape has at most six hexadecimal digits"
      modify (· + 1)
    | none => fail (← get) "expected '}' to end the '\\u{…}' escape"
  if digits == 0 then fail start "a '\\u{…}' escape needs at least one hexadecimal digit"
  unless value.isValidChar do fail start ("'\\u{…}' names no character: " ++ toString value)
  return Char.ofNat value

/--
Reads the text of a matcher, up to the {lit}`)` that ends the atom, reading its escapes. The result
is the characters and the source offset of each.
-/
private def matcherText : P (Array Char × Array Nat) := do
  let mut chars := #[]
  let mut offsets := #[]
  repeat
    let pos ← get
    match ← peek with
    | none => fail pos "expected ')' to end the matcher"
    | some ')' => break
    | some ',' => fail pos "a ',' in a matcher is written '\\,'"
    | some '\\' =>
      modify (· + 1)
      let escaped ← peek
      modify (· + 1)
      let c ← match escaped with
        | some 'n' => pure '\n'
        | some 't' => pure '\t'
        | some 'r' => pure '\r'
        | some '\\' => pure '\\'
        | some ')' => pure ')'
        | some ',' => pure ','
        | some 'u' => unicodeEscape pos
        | some c =>
          fail pos ("unknown escape '\\" ++ c.toString ++
            "'; the escapes are \\n, \\t, \\r, \\\\, \\), \\, and \\u{…}")
        | none => fail pos "a '\\' at the end of the filter"
      chars := chars.push c
      offsets := offsets.push pos
    | some c =>
      modify (· + 1)
      chars := chars.push c
      offsets := offsets.push pos
  return (chars, offsets)

/-- Reads a predicate's matcher, after its {lit}`(`, and the {lit}`)` after it. -/
private def matcher (pred : Predicate) : P Matcher := do
  let mode ← match ← peek with
    | some '=' => modify (· + 1); pure Mode.equal
    | some '~' => modify (· + 1); pure Mode.contains
    | some '#' => modify (· + 1); pure Mode.glob
    | _ => pure pred.defaultMode
  let (chars, offsets) ← matcherText
  let endOffset ← get
  expect ')'
  let text := String.ofList chars.toList
  match mode with
  | .glob =>
    match Glob.parse chars offsets endOffset with
    | .ok glob => return { mode, text, glob }
    | .error e => throw e
  | _ => return { mode, text }

/-- Reads a word of letters, for a predicate or a constant. -/
private def word : P String := do
  let mut w := ""
  while (← peek).any (·.isAlpha) do
    w := w.push (← peek).get!
    modify (· + 1)
  return w

mutual
  /-- Reads an atom: a predicate, a constant, or a parenthesized filter. -/
  private partial def atom (depth : Nat) : P Expr := do
    skipWs
    let start ← get
    if (← peek) == some '(' then
      if depth ≥ maxDepth then fail start s!"parentheses nest more than {maxDepth} deep"
      modify (· + 1)
      let e ← union (depth + 1)
      skipWs
      expect ')'
      return e
    let w ← word
    let pred? : Option Predicate := match w with
      | "name" => some .name
      | "file" => some .file
      | "exe" => some .exe
      | "tag" => some .tag
      | _ => none
    if let some pred := pred? then
      skipWs
      expect '('
      let m ← matcher pred
      return .atom pred m { start, stop := ← get }
    if w == "all" || w == "none" || w == "default" then
      skipWs
      expect '('
      expect ')'
      let span := { start, stop := ← get }
      return if w == "all" then .all span else if w == "none" then .none span else .default span
    if w.isEmpty then
      match ← peek with
      | some c =>
        fail start s!"expected a filter, such as name(…), tag(…), all(), or '(', and found {showChar c}"
      | none => fail start "expected a filter, such as name(…), tag(…), all(), or '('"
    fail start s!"unknown predicate '{w}'; the predicates are name, file, exe, and tag, and the \
      constants are all(), none(), and default()"

  /-- Reads a complement, or an atom. -/
  private partial def unary (depth : Nat) : P Expr := do
    skipWs
    let start ← get
    if (← peek) == some '!' then
      if depth ≥ maxDepth then fail start s!"'!' nests more than {maxDepth} deep"
      modify (· + 1)
      let e ← unary (depth + 1)
      return .not e { start, stop := e.span.stop }
    atom depth

  /-- Reads intersections and differences, which associate to the left. -/
  private partial def inter (depth : Nat) : P Expr := do
    let mut e ← unary depth
    repeat
      skipWs
      match ← peek with
      | some '&' =>
        modify (· + 1)
        let r ← unary depth
        e := .and e r { start := e.span.start, stop := r.span.stop }
      | some '\\' =>
        modify (· + 1)
        let r ← unary depth
        e := .diff e r { start := e.span.start, stop := r.span.stop }
      | _ => break
    return e

  /-- Reads unions, which associate to the left. -/
  private partial def union (depth : Nat) : P Expr := do
    let mut e ← inter depth
    repeat
      skipWs
      if (← peek) == some '|' then
        modify (· + 1)
        let r ← inter depth
        e := .or e r { start := e.span.start, stop := r.span.stop }
      else break
    return e
end

/-- Parses a filter from its text. -/
def parse (text : String) : Except ParseError Expr := do
  let chars := text.toList.toArray
  let p : P Expr := do
    let e ← union 0
    skipWs
    if let some c ← peek then
      fail (← get) s!"expected '|', '&', '\\', or the end of the filter, and found {showChar c}"
    return e
  let (e, _) ← (p.run chars).run 0
  return e

/-! # Printing -/

/-- A matcher's text written with the escapes that make it read back as the same text. -/
def escapeText (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | ')' => acc ++ "\\)"
    | ',' => acc ++ "\\,"
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\t' => acc ++ "\\t"
    | '\r' => acc ++ "\\r"
    | c =>
      if c.toNat < 0x20 || c.toNat == 0x7f then
        acc ++ "\\u{" ++ String.ofList (Nat.toDigits 16 c.toNat) ++ "}"
      else acc.push c

/-- A matcher as the argument of the predicate {name}`pred`. -/
def Matcher.print (pred : Predicate) (m : Matcher) : String :=
  let needsPrefix := m.mode != pred.defaultMode ||
    (m.text.front? |>.any fun c => c == '=' || c == '~' || c == '#')
  (if needsPrefix then m.mode.prefix.toString else "") ++ escapeText m.text

/--
The filter as text that parses back to the same filter, with parentheses where the precedence of the
operators calls for them.
-/
def Expr.print (e : Expr) : String :=
  printAt e 0
where
  /--
  The filter at a place that needs the given level: 0 for a union, 1 for an intersection or a
  difference, and 2 for a complement or an atom.
  -/
  printAt (e : Expr) (level : Nat) : String :=
    let (own, text) : Nat × String := match e with
      | .atom p m _ => (2, s!"{p.keyword}({m.print p})")
      | .all _ => (2, "all()")
      | .none _ => (2, "none()")
      | .default _ => (2, "default()")
      | .not e _ => (2, "!" ++ printAt e 2)
      | .and a b _ => (1, s!"{printAt a 1} & {printAt b 2}")
      | .diff a b _ => (1, s!"{printAt a 1} \\ {printAt b 2}")
      | .or a b _ => (0, s!"{printAt a 0} | {printAt b 1}")
    if own < level then s!"({text})" else text

/-- Several filters as one, joined by union. The union of no filters selects every test. -/
def unionOf (filters : Array Expr) : Expr :=
  match filters[0]? with
  | none => .all {}
  | some first => filters.extract 1 filters.size |>.foldl (init := first) fun acc f => .or acc f {}

end Errata.Filter
