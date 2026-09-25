/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
Tests of the filter language: the parser's precedence, associativity, escapes, and errors, the
printer, evaluation, and glob matching, including its time on patterns with many `*` against long
strings that almost match.
-/
module

public import Errata

open Errata
open Errata.Filter

public section

namespace ErrataTests.Filter

/-- A name atom that contains the text. -/
def nm (text : String) : Expr := .atom .name { mode := .contains, text } {}

/-- A tag atom equal to the text. -/
def tg (text : String) : Expr := .atom .tag { mode := .equal, text } {}

/-- The filter that a text parses to, without its spans. -/
def parsed (text : String) : Option Expr :=
  (Filter.parse text).toOption.map (·.forgetSpans)

/--
`!` binds tighter than `&` and `\`, which bind tighter than `|`, and the binary operators associate
to the left.
-/
@[test]
def filterPrecedence : Test := do
  let cases : List (String × Expr) := [
    ("name(a) | name(b) & name(c)", .or (nm "a") (.and (nm "b") (nm "c") {}) {}),
    ("name(a) & name(b) | name(c)", .or (.and (nm "a") (nm "b") {}) (nm "c") {}),
    ("!name(a) & name(b)", .and (.not (nm "a") {}) (nm "b") {}),
    ("name(a) \\ name(b) | name(c)", .or (.diff (nm "a") (nm "b") {}) (nm "c") {}),
    ("name(a) | name(b) \\ name(c)", .or (nm "a") (.diff (nm "b") (nm "c") {}) {}),
    ("name(a) & name(b) \\ name(c)", .diff (.and (nm "a") (nm "b") {}) (nm "c") {}),
    ("name(a) \\ name(b) & name(c)", .and (.diff (nm "a") (nm "b") {}) (nm "c") {}),
    ("name(a) | name(b) | name(c)", .or (.or (nm "a") (nm "b") {}) (nm "c") {}),
    ("name(a) \\ name(b) \\ name(c)", .diff (.diff (nm "a") (nm "b") {}) (nm "c") {}),
    ("!!name(a)", .not (.not (nm "a") {}) {}),
    ("!(name(a) | name(b))", .not (.or (nm "a") (nm "b") {}) {}),
    ("name(a) & (name(b) | name(c))", .and (nm "a") (.or (nm "b") (nm "c") {}) {}),
    ("  tag(x)\t&\n all () ", .and (tg "x") (.all {}) {}),
    ("all() \\ tag(browser)", .diff (.all {}) (tg "browser") {}),
    ("none()", .none {}),
    ("default() | tag(x)", .or (.default {}) (tg "x") {})]
  for (text, expected) in cases do
    result text.quote do
      assertBEq (some expected) (parsed text)

/--
`default()` selects what the default filter selects, and prints back as itself. Judged from an
executable's name alone, filters select every test of the executable, none of them, or an unknown
part, which `default()` takes from the default filter's answer.
-/
@[test]
def filterDefaultAndExecutables : Test := do
  let r : Record := { name := "A.alpha", exe := "Lib" }
  let some e := (Filter.parse "default() & name(A.)").toOption | fail "does not parse"
  assertBEq true (e.eval r true)
  assertBEq false (e.eval r false)
  assertBEq "default() & name(A.)" e.print
  let exe (text name : String) (dflt : Option Bool := some true) : Option (Option Bool) :=
    (Filter.parse text).toOption.map (·.evalExe name dflt)
  assertBEq (some (some true)) (exe "exe(Lib)" "Lib")
  assertBEq (some (some false)) (exe "exe(Lib)" "Other")
  assertBEq (some none) (exe "name(x)" "Lib")
  assertBEq (some (some false)) (exe "exe(Lib) & name(x)" "Other")
  assertBEq (some none) (exe "exe(Lib) & name(x)" "Lib")
  assertBEq (some (some true)) (exe "exe(Lib) | name(x)" "Lib")
  assertBEq (some none) (exe "exe(Lib) | name(x)" "Other")
  assertBEq (some (some false)) (exe "all() \\ exe(Lib)" "Lib")
  assertBEq (some none) (exe "!tag(x)" "Lib")
  assertBEq (some (some false)) (exe "default()" "Lib" (some false))
  assertBEq (some none) (exe "default() | exe(Other)" "Lib" none)

/-- A small inventory for evaluating filters. -/
def records : Array Record := #[
  { name := "A.alpha", file := "src/a.lean", exe := "Lib", tags := #["slow"] },
  { name := "A.beta", file := "src/b.lean", exe := "Lib", tags := #[] },
  { name := "B.gamma", file := "test/c.py", exe := "browser", tags := #["slow", "browser"] },
  { name := "B.delta", file := "", exe := "browser", tags := #["browser"] }]

/-- The names of the records that a filter selects. -/
def selects (text : String) : Option (Array String) :=
  (Filter.parse text).toOption.map fun e => (records.filter e.eval).map (·.name)

/-- `A \ B` selects the same tests as `A & !B`, and the constants select everything and nothing. -/
@[test]
def filterEvaluation : Test := do
  let atoms := ["name(A.)", "tag(slow)", "exe(browser)", "file(src/*)", "all()", "none()",
    "name(=B.delta)", "name(#*a)", "tag(~row)"]
  for a in atoms do
    for b in atoms do
      assertBEq (selects s!"{a} & !{b}") (selects s!"{a} \\ {b}")
  assertBEq (some (records.map (·.name))) (selects "all()")
  assertBEq (some #[]) (selects "none()")
  assertBEq (some #["A.alpha", "A.beta"]) (selects "all() \\ tag(browser)")
  assertBEq (some #["A.alpha", "B.gamma"]) (selects "tag(slow)")
  assertBEq (some #["B.gamma", "B.delta"]) (selects "exe(brow*)")
  assertBEq (some #[]) (selects "exe(brow)")
  assertBEq (some #["A.beta", "B.delta"]) (selects "!tag(slow)")
  assertBEq (some #["B.delta"]) (selects "file(=)")

/-- The escapes of a matcher's text, each read as the character it stands for. -/
@[test]
def filterEscapes : Test := do
  let text (filter : String) : Option String :=
    match Filter.parse filter with
    | .ok (.atom _ m _) => some m.text
    | _ => none
  assertBEq (some "a)b") (text "name(a\\)b)")
  assertBEq (some "a,b") (text "name(a\\,b)")
  assertBEq (some "a\\b") (text "name(a\\\\b)")
  assertBEq (some "a\nb\tc\rd") (text "name(a\\nb\\tc\\rd)")
  assertBEq (some "A") (text "name(\\u{41})")
  assertBEq (some "😀") (text "name(\\u{1F600})")
  assertBEq (some " x y ") (text "name( x y )")
  assertBEq (some "=x") (text "name(==x)")
  assertBEq (some "") (text "name()")

/-- Every parse error, with the column that it names. -/
@[test]
def filterParseErrors : Test := do
  let cases : List (String × Nat × String) := [
    ("name(x", 6, "expected ')' to end the matcher"),
    ("name(a,b)", 6, "a ',' in a matcher is written '\\,'"),
    ("name(a\\q)", 6, "unknown escape '\\q'"),
    ("name(\\", 5, "a '\\' at the end of the filter"),
    ("foo(x)", 0, "unknown predicate 'foo'"),
    ("", 0, "expected a filter"),
    ("name(x) &", 9, "expected a filter"),
    ("!", 1, "expected a filter"),
    ("| name(x)", 0, "expected a filter, such as name(…), tag(…), all(), or '(', and found '|'"),
    ("(name(x)", 8, "expected ')'"),
    ("name(x) name(y)", 8, "expected '|', '&', '\\', or the end of the filter, and found 'n'"),
    ("name x", 5, "expected '(', found 'x'"),
    ("all(x)", 4, "expected ')', found 'x'"),
    ("all( )", 4, "expected ')', found ' '"),
    ("name(\\u{})", 5, "a '\\u{…}' escape needs at least one hexadecimal digit"),
    ("name(\\u41)", 7, "expected '{', found '4'"),
    ("name(\\u{12", 10, "expected '}' to end the '\\u{…}' escape"),
    ("name(\\u{1g})", 9, "expected a hexadecimal digit or '}', found 'g'"),
    ("name(\\u{1234567})", 5, "a '\\u{…}' escape has at most six hexadecimal digits"),
    ("name(\\u{110000})", 5, "'\\u{…}' names no character: 1114112"),
    ("file(a**)", 7, "two '*' in a row"),
    ("name(#**)", 7, "two '*' in a row"),
    ("exe([ab)", 4, "'[' is not closed by ']'"),
    ("exe(x{a)", 5, "'{' is not closed by '}'"),
    ("exe([z-a])", 5, "the range 'z-a' is empty"),
    ("exe(\\,\\,[)", 8, "'[' is not closed by ']'")]
  for (text, offset, message) in cases do
    result text do
      match Filter.parse text with
      | .ok e => fail s!"expected an error, got {repr e}"
      | .error err =>
        assertBEq offset err.offset
        assertContains message err.message

/-- Parse errors name their places in their sources. -/
@[test]
def filterErrorLocations : Test := do
  let text := "tag(x) & (name(y)"
  let .error e := Filter.parse text | fail "expected an error"
  assertBEq "--filter:17: expected ')'" (e.render (.argument "--filter"))
  let positions := (Array.range (text.length + 1)).map ((12, 11 + ·))
  assertBEq "errata.toml:12:28: expected ')'" (e.render (.file "errata.toml" 12 10 positions))
  result "a string whose characters have no known positions" do
    assertBEq "errata.toml:12:10: at offset 17 in the filter: expected ')'"
      (e.render (.file "errata.toml" 12 10 #[]))

/--
Parsing a filter and printing it gives the same text, for filters written in their shortest form.
-/
@[test]
def filterPrintsAsWritten : Test := do
  for text in ["name(a) | tag(b) & !exe(c)", "(name(a) | tag(b)) & file(src/*)", "all() \\ tag(slow)",
      "!(name(a) & tag(b))", "name(a\\)b\\,c\\\\d)", "name(=x) | exe(~y) | tag(#z*)", "name(~=a)"] do
    match Filter.parse text with
    | .ok e => assertBEq text e.print
    | .error e => fail s!"{text}: {e.message}"

/-- Characters that a generated matcher's text is made of, the special ones included. -/
def textChars : List Char :=
  ['a', 'b', ' ', '(', ')', ',', '\\', '=', '~', '#', '\n', '\t', 'é', '|', '&', '!', '*', '?', '[',
   ']', '{', '}', '\x01', '😀']

open Plausible in
/-- A matcher's text of any characters. -/
def genText : Gen String := do
  let n := (← Gen.choose Nat 0 6 (by omega)).val
  let mut s := ""
  for _ in [0 : n] do
    s := s.push (← Gen.elements textChars (by decide))
  return s

open Plausible in
/-- The text of a glob, with two `*` never in a row. -/
def genGlobText : Gen String := do
  let n := (← Gen.choose Nat 0 5 (by omega)).val
  let mut s := ""
  for _ in [0 : n] do
    let t ← Gen.elements ["a", "b", ".", "*", "?", "[ab]", "[!a]", "[^a-c]", "{a,b}", "{x,}", "[*]",
      "[{]", "{a,{b,c}}", ")", ","] (by decide)
    unless t == "*" && s.endsWith "*" do s := s ++ t
  return s

open Plausible in
/-- A matcher in any mode. -/
def genMatcher : Gen Matcher := do
  let mode ← Gen.elements [Mode.equal, .contains, .glob] (by decide)
  match mode with
  | .glob =>
    let text ← genGlobText
    match Glob.ofString text with
    | .ok glob => return { mode, text, glob }
    | .error _ => return { mode := .equal, text }
  | _ => return { mode, text := ← genText }

open Plausible in
/-- A filter with at most the given depth of operators. -/
def genExpr : Nat → Gen Expr
  | 0 => do
    match (← Gen.choose Nat 0 5 (by omega)).val with
    | 0 => return .all {}
    | 1 => return .none {}
    | n =>
      let pred := [Predicate.name, .file, .exe, .tag][n - 2]!
      return .atom pred (← genMatcher) {}
  | d + 1 => do
    match (← Gen.choose Nat 0 5 (by omega)).val with
    | 0 => return .not (← genExpr d) {}
    | 1 => return .and (← genExpr d) (← genExpr d) {}
    | 2 => return .diff (← genExpr d) (← genExpr d) {}
    | 3 => return .or (← genExpr d) (← genExpr d) {}
    | _ => genExpr 0

/-- A generated filter, for the round-trip property. -/
structure FilterCase where
  /-- The filter. -/
  expr : Expr
deriving Repr

instance : Plausible.Shrinkable FilterCase where
  shrink _ := []

instance : Plausible.Arbitrary FilterCase where
  arbitrary := do return ⟨← genExpr 4⟩

/-- Printing a filter and parsing the text gives back the filter. -/
@[test]
def filterPrintParses : seed → Test :=
  property (∀ c : FilterCase, parsed c.expr.print = some c.expr)

/-- Whether a glob, read from its text, matches a string. -/
def globMatches (glob s : String) : Option Bool :=
  (Glob.ofString glob).toOption.map (·.matches s)

/--
Globs match whole strings, `*` and `?` cross every character, classes accept or reject one
character, alternation expands, and a metacharacter in brackets is literal. The cases include the
examples in the documentation of Rust's `globset`, restricted to what Errata's globs have.
-/
@[test]
def globCases : Test := do
  let cases : List (String × String × Bool) := [
    ("*.rs", "foo.rs", true), ("*.rs", "foo/bar.rs", true), ("*.rs", "foo.rs.bak", false),
    ("*.rs", ".rs", true), ("{*.rs,*.toml}", "Cargo.toml", true), ("{*.rs,*.toml}", "a.md", false),
    ("?", "a", true), ("?", "", false), ("?", "ab", false), ("a?c", "abc", true), ("a?c", "ac", false),
    ("a?c", "a/c", true),
    ("[ab]", "a", true), ("[ab]", "c", false), ("[!ab]", "c", true), ("[!ab]", "a", false),
    ("[^ab]", "c", true), ("[^ab]", "b", false), ("[a-c]x", "bx", true), ("[a-c]x", "dx", false),
    ("[!a-c]x", "dx", true), ("[a-cx-z]", "y", true), ("[a-]", "-", true), ("[]]", "]", true),
    ("[!]]", "a", true), ("[!]]", "]", false),
    ("{exe,}", "exe", true), ("{exe,}", "", true), ("{exe,}", "ex", false),
    ("[*]", "*", true), ("[*]", "a", false), ("[?]", "?", true), ("[?]", "a", false),
    ("[[]", "[", true), ("[{]", "{", true), ("}", "}", true), (",", ",", true),
    ("*", "", true), ("*", "anything/at:all.", true), ("a*b*c", "abc", true),
    ("a*b*c", "aXbYc", true), ("a*b*c", "acb", false), ("*a", "ba", true), ("*a", "ab", false),
    ("{a,b}{c,d}", "bd", true), ("{a,b}{c,d}", "ab", false), ("{a,{b,c}}x", "cx", true),
    ("a*{*b,c}", "aXXb", true), ("", "", true), ("", "a", false), ("é?", "éü", true)]
  for (glob, s, expected) in cases do
    result s!"{glob} {s}" do
      assertBEq (some expected) (globMatches glob s)
  for glob in ["**", "a**b", "[", "[a", "{a", "{a,{b}", "[b-a]"] do
    result s!"{glob} is an error" do
      assertBEq none (globMatches glob "")

/--
Globs match in time bounded by the product of the pattern's length and the string's, and linear in
the string for a given pattern, so patterns with many `*` against long strings that almost match
finish at once.
-/
@[test]
def globMatchingIsLinear : Test := do
  let long := "".pushn 'a' 5000
  let cases : List (String × String × Bool) := [
    ("a*a*a*a*a*a*a*a*a*a*b", long, false),
    ("a*a*a*a*a*a*a*a*a*a*b", long ++ "b", true),
    ("{a*a*a*a*a*a*a*a*a*a*b,x*y}", long, false),
    ("[a]*[a]*[a]*[a]*[a]*[a]*[a]*[a]*[a]*[a]*[b]", long, false),
    ("*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*a*b", long, false)]
  for (glob, s, expected) in cases do
    result glob do
      let start ← IO.monoMsNow
      assertBEq (some expected) (globMatches glob s)
      let elapsed := (← IO.monoMsNow) - start
      assertTrue (elapsed < 200) s!"matching took {elapsed}ms"

/-- Globs whose alternations expand to more patterns than the limit are errors. -/
@[test]
def globAlternationIsBounded : Test := do
  let many := String.join (List.replicate 20 "{a,b}")
  match Glob.ofString many with
  | .ok _ => fail "expected an error"
  | .error e => assertContains "expand to more than 10000 patterns" e.message
  result "a large expansion of few patterns" do
    -- 5,000 alternatives followed by 100,000 characters would copy the characters into every pattern.
    let alternatives := ",".intercalate ((List.range 5000).map toString)
    let glob := "{" ++ alternatives ++ "}" ++ "".pushn 'x' 100000
    let start ← IO.monoMsNow
    match Glob.ofString glob with
    | .ok _ => fail "expected an error"
    | .error e =>
      assertContains "expand to more than 1000000 characters" e.message
      assertBEq 0 e.offset
    let elapsed := (← IO.monoMsNow) - start
    assertTrue (elapsed < 2000) s!"parsing took {elapsed}ms"

end ErrataTests.Filter
