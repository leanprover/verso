/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso.Parser

namespace Verso.Parser

open Lean.Parser
/-!
This module contains unit tests for the Verso parser that are either somewhat unique, utility
parsers, or just unlikely to change.
-/

/--
info: Success! Final stack:
 • "b"
 • "a"
 • "b"
 • "a"
 • "b"
 • "a"

Remaining:
"aab"
-/
#guard_msgs in
#eval repFn 3 (chFn 'b' >> chFn 'a') |>.test! "bababaaab"


/--
info: Success! Final stack:
  []
All input consumed.
-/
#guard_msgs in
#eval atMostFn 3 (chFn 'a') "small A" |>.test! ""

/--
info: Success! Final stack:
  ["a"]
Remaining:
"bc"
-/
#guard_msgs in
#eval atMostFn 3 (chFn 'a') "small A" |>.test! "abc"

/--
info: Success! Final stack:
  ["a" "a" "a"]
All input consumed.
-/
#guard_msgs in
#eval atMostFn 3 (chFn 'a') "small A" |>.test! "aaa"

/--
info: Failure @3 (⟨1, 3⟩): unexpected small A
Final stack:
  ["a" "a" "a" <missing>]
Remaining: "a"
-/
#guard_msgs in
#eval atMostFn 3 (chFn 'a') "small A" |>.test! "aaaa"

/--
info: Failure @0 (⟨1, 0⟩): unexpected end of input
Final stack:
  [<missing>]
Remaining: ""
-/
#guard_msgs in
#eval atLeastFn 3 (chFn 'a') |>.test! ""

/--
info: Failure @2 (⟨1, 2⟩): unexpected end of input
Final stack:
  ["a" "a" <missing>]
Remaining: ""
-/
#guard_msgs in
#eval atLeastFn 3 (chFn 'a') |>.test! "aa"

/--
info: Success! Final stack:
  ["a" "a" "a"]
All input consumed.
-/
#guard_msgs in
#eval atLeastFn 3 (chFn 'a') |>.test! "aaa"

/--
info: Success! Final stack:
  ["a" "a" "a" "a" "a" "a"]
All input consumed.
-/
#guard_msgs in
#eval atLeastFn 3 (chFn 'a') |>.test! "aaaaaa"


/--
info: Success! Final stack:
 empty
Remaining:
"bc"
-/
#guard_msgs in
#eval satisfyEscFn Char.isAlpha |>.test! "abc"
/--
info: Failure @0 (⟨1, 0⟩): unexpected character
Final stack:
  <missing>
Remaining: "0abc"
-/
#guard_msgs in
#eval satisfyEscFn Char.isAlpha |>.test! "0abc"
/--
info: Success! Final stack:
 empty
Remaining:
"abc"
-/
#guard_msgs in
#eval satisfyEscFn Char.isAlpha |>.test! "\\0abc"


/--
info: Success! Final stack:
 empty
Remaining:
"c  c"
-/
#guard_msgs in
#eval takeUntilEscFn Char.isAlpha |>.test! "    c  c"

/--
info: Success! Final stack:
 empty
Remaining:
"c"
-/
#guard_msgs in
#eval takeUntilEscFn Char.isAlpha |>.test! "    \\c  c"


/--
info: Success! Final stack:
 empty
All input consumed.
-/
#guard_msgs in
#eval nl.test! "\n"

/--
info: Success! Final stack:
 empty
Remaining:
" "
-/
#guard_msgs in
#eval nl.test! "\n "


/--
info: Success! Final stack:
  "**"
Remaining:
"*"
-/
#guard_msgs in
#eval asStringFn (transform := unescapeStr) (many1Fn inlineTextChar) |>.test! "\\*\\**"



/--
info: Success! Final stack:
  ">"
All input consumed.
-/
#guard_msgs in
#eval asStringFn (transform := unescapeStr) (many1Fn inlineTextChar) |>.test! "\\>"

/--
info: Success! Final stack:
 empty
Remaining:
"\nhijk\n\n\n\nabc"
-/
#guard_msgs in
#eval (ignoreFn skipToNewline).test! "abcdeg\nhijk\n\n\n\nabc"

/--
info: Success! Final stack:
  ["\n"]
Remaining:
"\n\n\n\nabc"
-/
#guard_msgs in
#eval (ignoreFn skipToNewline >> manyFn (atomicFn skipBlock.nonEmptyLine)).test! "abcdeg\nhijk\n\n\n\nabc"

/--
info: Success! Final stack:
 empty
Remaining:
"abc"
-/
#guard_msgs in
#eval (ignoreFn skipBlock).test! "abcdeg\nhijk\n\n\n\nabc"

/--
info: Failure @4 (⟨1, 4⟩): unterminated string literal; expected identifier or numeral
Final stack:
  (Verso.Syntax.arg_str <missing>)
Remaining: ""
-/
#guard_msgs in
#eval (recoverLine val).test! "\"foo"


/--
info: Success! Final stack:
  `x
Remaining:
"\n"
-/
#guard_msgs in
#eval docIdentFn.test! "x\n"


/--
info: Failure @0 (⟨1, 0⟩): expected character other than backtick ('`')
Final stack:
  [<missing>]
Remaining: "`a"
-/
#guard_msgs in
#eval (asStringFn <| many1Fn <| code.codeContentsFn 0).test! "`a"

/--
info: Success! Final stack:
  "`"
Remaining:
"a"
-/
#guard_msgs in
#eval (asStringFn <| code.codeContentsFn 1).test! "`a"

/--
info: Success! Final stack:
  "a"
All input consumed.
-/
#guard_msgs in
#eval (asStringFn <| code.codeContentsFn 1).test! "a"

/--
info: Success! Final stack:
  "`a"
All input consumed.
-/
#guard_msgs in
#eval (asStringFn <| many1Fn <| code.codeContentsFn 1).test! "`a"

/--
info: Success! Final stack:
  "aaa`b``c"
Remaining:
"```de````"
-/
#guard_msgs in
#eval (asStringFn <| many1Fn <| code.codeContentsFn 2).test! "aaa`b``c```de````"

/--
info: Success! Final stack:
  "aaa`\nb``c"
Remaining:
"```de````"
-/
#guard_msgs in
#eval (asStringFn <| many1Fn <| code.codeContentsFn 2).test! "aaa`\nb``c```de````"

/--
info: Success! Final stack:
  "aaa`\\nb``c"
Remaining:
"```de````"
-/
#guard_msgs in
#eval (asStringFn <| many1Fn <| code.codeContentsFn 2).test! "aaa`\\nb``c```de````"

/--
info: Success! Final stack:
  (Verso.Syntax.li
   "*"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text (str "\"foo\""))]
     "}")])
Remaining:
"* bar\n"
-/
#guard_msgs in
#eval listItem {inLists:=[⟨0, .inr .asterisk⟩]} |>.test! "* foo\n* bar\n"


/--
info: Success! Final stack:
 empty
Remaining:
"\n"
-/
#guard_msgs in
#eval nameArgWhitespace none |>.test! " \n"


/--
info: Success! Final stack:
  (Verso.Syntax.text (str "\"abc \""))
All input consumed.
-/
#guard_msgs in
#eval text.test! "abc "

/--
info: Success! Final stack:
  (Verso.Syntax.bold
   "**"
   [(Verso.Syntax.text (str "\"aa\""))]
   "**")
All input consumed.
-/
#guard_msgs in
#eval bold {} |>.test! "**aa**"

/--
info: Success! Final stack:
  (Verso.Syntax.footnote "[^" (str "\"1\"") "]")
All input consumed.
-/
#guard_msgs in
#eval footnote {} |>.test! "[^1]"


section
-- Test that the antiquotes match the parser's output
open Lean Elab Command

set_option pp.rawOnError true

/--
info: "This is a paragraph."
---
info: line!"\n"
---
info: "Two lines."
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString "This is a paragraph.\nTwo lines."⟩
  if let `(block|para[$txt*]) := stx then
    for t in txt do logInfo t
  else logError m!"Didn't match {stx}"

/--
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.li "*" [(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"One\""))] "}")])
---
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.li
 "*"
 [(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"Two\""))] "}")
  (Verso.Syntax.ul
   "ul{"
   [(Verso.Syntax.li "*" [(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"A\""))] "}")])]
   "}")])
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString "* One\n* Two\n  * A"⟩
  if let `(block|ul{$items*}) := stx then
    for t in items do logInfo t
  else logError m!"Didn't match {stx}"

/--
info: 1
---
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.li "1." [(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"One\""))] "}")])
---
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.li
 "2."
 [(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"Two\""))] "}")
  (Verso.Syntax.ol
   "ol("
   (num "1")
   ")"
   "{"
   [(Verso.Syntax.li "1)" [(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"A\""))] "}")])]
   "}")])
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString "1. One\n2. Two\n  1) A"⟩
  if let `(block|ol($n){$items*}) := stx then
    logInfo n
    for t in items do logInfo t
  else logError m!"Didn't match {stx}"

/--
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.desc
 ":"
 [(Verso.Syntax.text (str "\" One\""))]
 "=>"
 [(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"En\""))] "}")])
---
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.desc
 ":"
 [(Verso.Syntax.text (str "\" Two\""))]
 "=>"
 [(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"To\""))] "}")])
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString ": One\n\n En\n\n: Two\n\n  To"⟩
  if let `(block|dl{$items*}) := stx then
    for t in items do logInfo t
  else logError m!"Didn't match {stx}"

/-- info: "Code\n" -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString "```\nCode\n```\n"⟩
  if let `(block|``` | $s ```) := stx then
    logInfo s
  else logError m!"Didn't match {stx}"

/--
info: lean
---
info: (hasArg := true)
---
info: "Code\n"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString "```lean (hasArg := true)\nCode\n```\n"⟩
  if let `(block|``` $n $args* | $s ```) := stx then
    logInfo n
    for a in args do logInfo a
    logInfo s
  else logError m!"Didn't match {stx}"

/--
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.ul
 "ul{"
 [(Verso.Syntax.li "*" [(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"Abc\""))] "}")])]
 "}")
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString "> * Abc"⟩
  if let `(block|> $blks*) := stx then
    for b in blks do logInfo b
  else logError m!"Didn't match {stx}"

/--
info: "lean"
---
info: "https://lean-lang.org"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString "[lean]: https://lean-lang.org"⟩
  if let `(block|[$x]: $url) := stx then
    logInfo x
    logInfo url
  else logError m!"Didn't match {stx}"

/--
info: "lean"
---
info: "see "
---
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.link
 "["
 [(Verso.Syntax.text (str "\"the website\""))]
 "]"
 (Verso.Syntax.url "(" (str "\"https://lean-lang.org\"") ")"))
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString "[^lean]: see [the website](https://lean-lang.org)"⟩
  if let `(block|[^$name]: $txt*) := stx then
    logInfo name
    for t in txt do logInfo t
  else logError m!"Didn't match {stx}"

/--
info: paragraph
---
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"blah blah:\""))] "}")
---
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.ul
 "ul{"
 [(Verso.Syntax.li
   "*"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text (str "\"List\""))
      (Verso.Syntax.linebreak "line!" (str "\"\\n\""))
      (Verso.Syntax.text (str "\"More\""))]
     "}")])]
 "}")
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString ":::paragraph\nblah blah:\n * List\nMore\n:::"⟩
  if let `(block|:::$x $args* {$bs*}) := stx then
    logInfo x
    for a in args do logInfo a
    for b in bs do logInfo b
  else logError m!"Didn't match {stx}"

/--
info: 1
---
info: "Header!"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString "## Header!\n"⟩
  if let `(block|header($n){$inlines}) := stx then
    logInfo n
    logInfo inlines
  else logError "Didn't match"

-- Inlines

/-- info: "abc" -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "abc"⟩
  if let `(inline|$s:str) := stx then
    logInfo s
  else logError m!"Didn't match {stx}"

/-- info: "abc" -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "_abc_"⟩
  if let `(inline|_[$i*]) := stx then
    for x in i do logInfo x
  else logError m!"Didn't match {stx}"

/-- info: "abc" -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "*abc*"⟩
  if let `(inline|*[$i*]) := stx then
    for x in i do logInfo x
  else logError m!"Didn't match {stx}"

/--
info: "abc"
---
info: "http://lean-lang.org"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "[abc](http://lean-lang.org)"⟩
  if let `(inline|link[$i*]($url)) := stx then
    for x in i do logInfo x
    logInfo url
  else logError m!"Didn't match {stx}"

/--
info: "abc"
---
info: "lean"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "[abc][lean]"⟩
  if let `(inline|link[$i*][$ref]) := stx then
    for x in i do logInfo x
    logInfo ref
  else logError m!"Didn't match {stx}"

/-- info: "note" -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "[^note]"⟩
  if let `(inline|footnote($ref)) := stx then
    logInfo ref
  else logError m!"Didn't match {stx}"

/-- info: "\n" -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "\n"⟩
  if let `(inline|line! $s) := stx then
    logInfo s
  else logError m!"Didn't match {stx}"

/-- info: "abc" -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "`abc`"⟩
  if let `(inline|code($s)) := stx then
    logInfo s
  else logError m!"Didn't match {stx}"

/--
info: role
---
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.code "`" (str "\"abc\"") "`")
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "{role}`abc`"⟩
  if let `(inline|role{$x $args*}[$is*]) := stx then
    logInfo x
    for arg in args do logInfo arg
    for i in is do logInfo i
  else logError m!"Didn't match {stx}"

/--
info: role
---
info: 1
---
info: 2
---
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.emph "_" [(Verso.Syntax.text (str "\"abc\""))] "_")
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "{role 1 2}_abc_"⟩
  if let `(inline|role{$x $args*}[$is*]) := stx then
    logInfo x
    for arg in args do logInfo arg
    for i in is do logInfo i
  else logError m!"Didn't match {stx}"

/--
info: role
---
info: "abc "
---
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.link "[" [(Verso.Syntax.text (str "\"abc\""))] "]" (Verso.Syntax.url "(" (str "\"url\"") ")"))
---
info: " abc"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "{role}[abc [abc](url) abc]"⟩
  if let `(inline|role{$x $args*}[$is*]) := stx then
    logInfo x
    for arg in args do logInfo arg
    for i in is do logInfo i
  else logError m!"Didn't match {stx}"

/-- info: "2+s" -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "$`2+s`"⟩
  if let `(inline|\math code($s)) := stx then
    logInfo s
  else logError m!"Didn't match {stx}"

/-- info: "2+s" -/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← inline {} |>.parseString "$$`2+s`"⟩
  if let `(inline|\displaymath code($s)) := stx then
    logInfo s
  else logError m!"Didn't match {stx}"

-- List items
/--
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"A\""))] "}")
---
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"B\""))] "}")
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString "* A\n* B"⟩
  if let `(block|ul{ * $as* * $bs*}) := stx then
    for x in as do logInfo x
    for x in bs do logInfo x
  else logError m!"Didn't match {stx}"

/--
info: " A"
---
info: [Error pretty printing syntax: format: uncaught backtrack exception. Falling back to raw printer.]
(Verso.Syntax.para "para{" [(Verso.Syntax.text (str "\"B\""))] "}")
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let stx : TSyntax `block := ⟨← block {} |>.parseString ": A\n\n B"⟩
  if let `(block|dl{ : $as* => $bs*}) := stx then
    for x in as do logInfo x
    for x in bs do logInfo x
  else logError m!"Didn't match {stx}"

end
