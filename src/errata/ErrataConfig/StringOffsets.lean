/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The decoding of a TOML string token with the place in the token of each decoded character, so that
a message about a filter can name the line and column in the file of the character it concerns.
-/
module

public section

set_option linter.missingDocs true
set_option doc.verso true

namespace ErrataConfig

/--
Decodes a TOML string token by TOML's string rules, with the byte offset in the token where each
decoded character starts, then the offset of the closing delimiter. Literal strings, {lit}`'…'` and
{lit}`'''…'''`, hold their characters as written. Basic strings, {lit}`"…"` and {lit}`"""…"""`,
decode the escapes {lit}`\b`, {lit}`\t`, {lit}`\n`, {lit}`\f`, {lit}`\r`, {lit}`\"`, {lit}`\\`,
{lit}`\uXXXX`, and {lit}`\UXXXXXXXX`. Multi-line strings drop a newline right after their opening
delimiter, and in multi-line basic strings a backslash followed by whitespace drops that whitespace
and the newlines within it.
-/
def stringOffsets? (token : String) : Option (String × Array Nat) := Id.run do
  let cs := token.toList.toArray
  let bytes : Array Nat := cs.foldl (fun acc c => acc.push (acc.back! + c.utf8Size)) #[0]
  let delim := if token.startsWith "'''" || token.startsWith "\"\"\"" then 3 else 1
  let basic := token.startsWith "\""
  if cs.size < 2 * delim then return none
  let stop := cs.size - delim
  let mut i := delim
  if delim == 3 then
    if cs[i]? == some '\n' then i := i + 1
    else if cs[i]? == some '\r' && cs[i + 1]? == some '\n' then i := i + 2
  let mut out := ""
  let mut offsets : Array Nat := #[]
  while i < stop do
    let c := cs[i]!
    if !basic || c != '\\' then
      out := out.push c
      offsets := offsets.push bytes[i]!
      i := i + 1
      continue
    let some e := cs[i + 1]? | return none
    let simple := [('b', '\x08'), ('t', '\t'), ('n', '\n'), ('f', '\x0C'), ('r', '\r'), ('"', '"'),
      ('\\', '\\')]
    if let some (_, d) := simple.find? (·.1 == e) then
      out := out.push d
      offsets := offsets.push bytes[i]!
      i := i + 2
    else if e == 'u' || e == 'U' then
      let hex := cs.extract (i + 2) (i + 2 + if e == 'u' then 4 else 8)
      unless hex.size == (if e == 'u' then 4 else 8) && hex.all Char.isHexDigit do return none
      let digit (h : Char) :=
        if h.isDigit then h.toNat - '0'.toNat else h.toLower.toNat - 'a'.toNat + 10
      out := out.push (Char.ofNat (hex.foldl (fun n h => n * 16 + digit h) 0))
      offsets := offsets.push bytes[i]!
      i := i + 2 + hex.size
    else if delim == 3 && e.isWhitespace then
      i := i + 1
      while i < stop && cs[i]!.isWhitespace do i := i + 1
    else return none
  return some (out, offsets.push bytes[stop]!)

end ErrataConfig
