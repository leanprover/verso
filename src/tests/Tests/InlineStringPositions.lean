/-
Copyright (c) 2023-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso
import Verso.Doc.Concrete.InlineString

open Lean
open Verso.Doc
open Verso.SyntaxUtils

set_option pp.rawOnError true

/--
info: Inline.concat #[Inline.text "Hello, ", Inline.emph #[Inline.bold #[Inline.text "emph"]]] : Inline Genre.none
-/
#guard_msgs in
#check (inlines!"Hello, _*emph*_" : Inline .none)

/--
info: Block.concat #[Block.para #[Inline.text "Hello, ", Inline.emph #[Inline.bold #[Inline.text "emph"]]]] : Block Genre.none
-/
#guard_msgs in
#check (blocks!"Hello, _*emph*_" : Block .none)

/--
Decodes `src` with `decode` (over the whole string) and checks the decoded contents, then that each
`(lo, hi, text)` span re-extracts from the source to `text`. Comparing extracted *source* text keeps
the checks independent of where the test sits in the file: each decoded byte range `[lo, hi)` must
map back to the bytes that produced it.
-/
def checkDecode
    (decode : String → String.Pos.Raw → String.Pos.Raw → String × Std.TreeMap String.Pos.Raw String.Pos.Raw)
    (src expected : String) (spans : List (Nat × Nat × String)) : Bool :=
  let (decoded, m) := decode src ⟨0⟩ src.rawEndPos
  decoded == expected &&
  spans.all fun ⟨lo, hi, text⟩ =>
    (mapDecodedPos m ⟨lo⟩).extract src (mapDecodedPos m ⟨hi⟩) == text

-- A markup delimiter after an escape maps past the multi-byte source of the escape, not by a
-- constant shift: in `"a\n*b*"` the `*` is decoded byte 2 but source byte 4.
#guard checkDecode decodeStrLitWithMap "\"a\\n*b*\"" "a\n*b*" [(1, 2, "\\n"), (2, 3, "*")]

-- A unicode escape decodes to a multi-byte character whose source span is the whole `\uHHHH`.
#guard checkDecode decodeStrLitWithMap "\"\\u00e9x\"" "éx" [(0, 2, "\\u00e9"), (2, 3, "x")]

-- A string gap decodes to nothing; the character after it maps past the whole gap to source byte 6.
#guard checkDecode decodeStrLitWithMap "\"a\\\n  b\"" "ab" [(1, 2, "b")]

-- Raw string literals are not escape-decoded: `\n` stays two characters.
#guard checkDecode decodeStrLitWithMap "r\"a\\n*\"" "a\\n*" [(3, 4, "*")]

-- Every character a unicode escape: each decoded character maps to its whole six-byte `\uHHHH`.
#guard checkDecode decodeStrLitWithMap "\"\\u002A\\u0062\\u002A\"" "*b*"
  [(0, 1, "\\u002A"), (1, 2, "\\u0062"), (2, 3, "\\u002A")]

-- A bare content region (no surrounding quotes) decodes the same way; this drives re-parsing escaped
-- code spans as Lean.
#guard checkDecode decodeContentWithMap "\\u004E\\u0061\\u0074" "Nat"
  [(0, 1, "\\u004E"), (1, 2, "\\u0061"), (2, 3, "\\u0074")]

-- Remapping reanchors a token's leading and trailing whitespace into the source string, so the
-- syntax round-trips, and the token's positions become absolute.
#guard
  let src := "\"a\\n*b*\""
  let (_, m) := decodeStrLitWithMap src ⟨0⟩ src.rawEndPos
  let leading : Substring.Raw := { str := "a\n*b*", startPos := ⟨2⟩, stopPos := ⟨2⟩ }
  let trailing : Substring.Raw := { str := "a\n*b*", startPos := ⟨3⟩, stopPos := ⟨3⟩ }
  let remapped := remapSyntaxPos src (mapDecodedPos m) (Syntax.atom (.original leading ⟨2⟩ trailing ⟨3⟩) "*")
  remapped.getPos? == some ⟨4⟩ &&
  remapped.getTailPos? == some ⟨5⟩ &&
  (remapped.getHeadInfo.getTrailing?.map (·.str)) == some src

/--
info: Inline.concat
  #[Inline.text "a", Inline.linebreak "\n", Inline.text "b ",
    Inline.emph #[Inline.bold #[Inline.text "c"]]] : Inline Genre.none
-/
#guard_msgs in
#check (inlines!"a\nb _*c*_" : Inline .none)
