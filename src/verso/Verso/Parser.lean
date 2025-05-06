/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Parser

import Verso.Parser.Lean
import Verso.SyntaxUtils
import Verso.Syntax

set_option guard_msgs.diff true

namespace Verso.Parser


open Verso.SyntaxUtils
open Verso.Syntax
open Lean Parser


scoped instance : Coe Char ParserFn where
  coe := chFn

instance : AndThen ParserFn where
  andThen p1 p2 := andthenFn p1 (p2 ())

instance : OrElse ParserFn where
  orElse p1 p2 := orelseFn p1 (p2 ())

partial def atLeastAux (n : Nat) (p : ParserFn) : ParserFn := fun c s => Id.run do
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let mut s  := p c s
  if s.hasError then
    return if iniPos == s.pos && n == 0 then s.restore iniSz iniPos else s
  if iniPos == s.pos then
    return s.mkUnexpectedError "invalid 'atLeast' parser combinator application, parser did not consume anything"
  if s.stackSize > iniSz + 1 then
    s := s.mkNode nullKind iniSz
  atLeastAux (n - 1) p c s

def atLeastFn (n : Nat) (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let s := atLeastAux n p c s
  s.mkNode nullKind iniSz

def skipFn : ParserFn := fun _ s => s

def eatSpaces := takeWhileFn (· == ' ')

def repFn : Nat → ParserFn → ParserFn
  | 0, _ => skipFn
  | n+1, p => p >> repFn n p

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

/-- Like `satisfyFn`, but no special handling of EOI -/
partial def satisfyFn' (p : Char → Bool) (errorMsg : String := "unexpected character") : ParserFn := fun c s =>
  let i := s.pos
  if h : c.input.atEnd i then s.mkUnexpectedError errorMsg
  else if p (c.input.get' i h) then s.next' c.input i h
  else s.mkUnexpectedError errorMsg


partial def atMostAux (n : Nat) (p : ParserFn) (msg : String) : ParserFn := fun c s => Id.run do
  let iniSz  := s.stackSize
  let iniPos := s.pos
  if n == 0 then return notFollowedByFn p msg c s
  let mut s := p c s
  if s.hasError then
    return if iniPos == s.pos then s.restore iniSz iniPos else s
  if iniPos == s.pos then
    return s.mkUnexpectedError "invalid 'atMost' parser combinator application, parser did not consume anything"
  if s.stackSize > iniSz + 1 then
    s := s.mkNode nullKind iniSz
  atMostAux (n - 1) p msg c s

def atMostFn (n : Nat) (p : ParserFn) (msg : String) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let s := atMostAux n p msg c s
  s.mkNode nullKind iniSz

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

/-- Like `satisfyFn`, but allows any escape sequence through -/
partial def satisfyEscFn (p : Char → Bool) (errorMsg : String := "unexpected character") : ParserFn := fun c s =>
  let i := s.pos
  if h : c.input.atEnd i then s.mkEOIError
  else if c.input.get' i h == '\\' then
    let s := s.next' c.input i h
    let i := s.pos
    if h : c.input.atEnd i then s.mkEOIError
    else s.next' c.input i h
  else if p (c.input.get' i h) then s.next' c.input i h
  else s.mkUnexpectedError errorMsg

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

partial def takeUntilEscFn (p : Char → Bool) : ParserFn := fun c s =>
  let i := s.pos
  if h : c.input.atEnd i then s
  else if c.input.get' i h == '\\' then
    let s := s.next' c.input i h
    let i := s.pos
    if h : c.input.atEnd i then s.mkEOIError
    else takeUntilEscFn p c (s.next' c.input i h)
  else if p (c.input.get' i h) then s
  else takeUntilEscFn p c (s.next' c.input i h)

partial def takeWhileEscFn (p : Char → Bool) : ParserFn := takeUntilEscFn (not ∘ p)

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

def ignoreFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stxStack.size
  let s' := p c s
  s'.shrinkStack iniSz

def withInfoSyntaxFn (p : ParserFn) (infoP : SourceInfo → ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stxStack.size
  let startPos := s.pos
  let s := p c s
  let input    := c.input
  let stopPos  := s.pos
  let leading  := mkEmptySubstringAt input startPos
  let trailing := mkEmptySubstringAt input stopPos
  let info     := SourceInfo.original leading startPos trailing stopPos
  infoP info c (s.shrinkStack iniSz)

private def unescapeStr (str : String) : String := Id.run do
  let mut out := ""
  let mut iter := str.iter
  while !iter.atEnd do
    let c := iter.curr
    iter := iter.next
    if c == '\\' then
      if !iter.atEnd then
        out := out.push iter.curr
        iter := iter.next
    else
      out := out.push c
  out

private def asStringAux (quoted : Bool) (startPos : String.Pos) (transform : String → String) : ParserFn := fun c s =>
  let input    := c.input
  let stopPos  := s.pos
  let leading  := mkEmptySubstringAt input startPos
  let val      := input.extract startPos stopPos
  let val      := transform val
  let trailing := mkEmptySubstringAt input stopPos
  let atom     :=
    mkAtom (SourceInfo.original leading startPos trailing stopPos) <|
      if quoted then val.quote else val
  s.pushSyntax atom

/-- Match an arbitrary Parser and return the consumed String in a `Syntax.atom`. -/
def asStringFn (p : ParserFn) (quoted := false) (transform : String → String := id ) : ParserFn := fun c s =>
  let startPos := s.pos
  let iniSz := s.stxStack.size
  let s := p c s
  if s.hasError then s
  else asStringAux quoted startPos transform c (s.shrinkStack iniSz)

def checkCol0Fn (errorMsg : String) : ParserFn := fun c s =>
  let pos      := c.fileMap.toPosition s.pos
  if pos.column = 1 then s
  else s.mkError errorMsg

def _root_.Lean.Parser.ParserContext.currentColumn (c : ParserContext) (s : ParserState) : Nat :=
  c.fileMap.toPosition s.pos |>.column

def pushColumn : ParserFn := fun c s =>
  let col := c.fileMap.toPosition s.pos |>.column
  s.pushSyntax <| Syntax.mkLit `column (toString col) (SourceInfo.synthetic s.pos s.pos)

def guardColumn (p : Nat → Bool) (message : String) : ParserFn := fun c s =>
  if p (c.currentColumn s) then s else s.mkErrorAt message s.pos

def guardMinColumn (min : Nat) : ParserFn := guardColumn (· ≥ min) s!"expected column at least {min}"

def withCurrentColumn (p : Nat → ParserFn) : ParserFn := fun c s =>
  p (c.currentColumn s) c s

def bol : ParserFn := fun c s =>
  let position := c.fileMap.toPosition s.pos
  let col := position |>.column
  if col == 0 then s else s.mkErrorAt s!"beginning of line at {position}" s.pos

def bolThen (p : ParserFn) (description : String) : ParserFn := fun c s =>
  let position := c.fileMap.toPosition s.pos
  let col := position |>.column
  if col == 0 then
    let s := p c s
    if s.hasError then
      s.mkErrorAt description s.pos
    else s
  else s.mkErrorAt description s.pos

/--
We can only start a nestable block if we're immediately after a newline followed by a sequence of nestable block openers
-/
def onlyBlockOpeners : ParserFn := fun c s =>
  let position := c.fileMap.toPosition s.pos
  let lineStart := c.fileMap.lineStart position.line
  let ok : Bool := Id.run do
    let mut iter := {c.input.iter with i := lineStart}
    while iter.i < s.pos && iter.hasNext do
      if iter.curr.isDigit then
        while iter.curr.isDigit && iter.i < s.pos && iter.hasNext do
          iter := iter.next
        if !iter.hasNext then return false
        else if iter.curr == '.' || iter.curr == ')' then iter := iter.next
      else if iter.curr == ' ' then iter := iter.next
      else if iter.curr == '>' then iter := iter.next
      else if iter.curr == '*' then iter := iter.next
      else if iter.curr == '+' then iter := iter.next
      else if iter.curr == '-' then iter := iter.next
      else return false
    true

  if ok then s
  else s.mkErrorAt s!"beginning of line or sequence of nestable block openers at {position}" s.pos


def nl := satisfyFn (· == '\n') "newline"

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

def fakeAtom (str : String) (info : SourceInfo := SourceInfo.none) : ParserFn := fun _c s =>
  let atom := mkAtom info str
  s.pushSyntax atom

def pushMissing : ParserFn := fun _c s =>
  s.pushSyntax .missing


def strFn (str : String) : ParserFn := asStringFn <| fun c s =>
  let rec go (iter : String.Iterator) (s : ParserState) :=
    if iter.atEnd then s
    else
      let ch := iter.curr
      go iter.next <| satisfyFn (· == ch) ch.toString c s
  let iniPos := s.pos
  let iniSz := s.stxStack.size
  let s := go str.iter s
  if s.hasError then s.mkErrorAt s!"'{str}'" iniPos (some iniSz) else s


inductive OrderedListType where
   /-- Items like 1. -/
  | numDot
   /-- Items like 1) -/
  | parenAfter
deriving Repr, BEq, Ord, DecidableEq

def OrderedListType.all : List OrderedListType :=
  [.numDot, .parenAfter]

theorem OrderedListType.all_complete : ∀ x : OrderedListType, x ∈ all := by
  unfold all; intro x; cases x <;> repeat constructor


inductive UnorderedListType where
   /-- Items like * -/
  | asterisk
   /-- Items like - -/
  | dash
   /-- Items like + -/
  | plus
deriving Repr, BEq, Ord, DecidableEq

def UnorderedListType.all : List UnorderedListType :=
  [.asterisk, .dash, .plus]

theorem UnorderedListType.all_complete : ∀ x : UnorderedListType, x ∈ all := by
  unfold all; intro x; cases x <;> repeat constructor

def unorderedListIndicator (type : UnorderedListType) : ParserFn :=
  asStringFn <|
    match type with
    | .asterisk => chFn '*'
    | .dash => chFn '-'
    | .plus => chFn '+'

def orderedListIndicator (type : OrderedListType) : ParserFn :=
  asStringFn <|
    takeWhile1Fn (·.isDigit) "digits" >>
    match type with
    | .numDot => chFn '.'
    | .parenAfter => chFn ')'


def blankLine : ParserFn := nodeFn `blankLine <| atomicFn <| asStringFn <| takeWhileFn (· == ' ') >> nl

def bullet := atomicFn (go UnorderedListType.all)
where
  go
    | [] => fun _ s => s.mkError "no list type"
    | [x] => atomicFn (unorderedListIndicator x)
    | x :: xs => atomicFn (unorderedListIndicator x) <|> go xs

def numbering := atomicFn (go OrderedListType.all)
where
  go
    | [] => fun _ s => s.mkError "no list type"
    | [x] => atomicFn (orderedListIndicator x)
    | x :: xs => atomicFn (orderedListIndicator x) <|> go xs


def inlineTextChar : ParserFn := fun c s =>
  let i := s.pos
  if h : c.input.atEnd i then s.mkEOIError
  else
    let curr := c.input.get' i h
    match curr with
    | '\\' =>
      let s := s.next' c.input i h
      let i := s.pos
      if h : c.input.atEnd i then s.mkEOIError
      else s.next' c.input i h
    | '*' | '_' | '\n' | '[' | ']' | '{' | '}' | '`' => s.mkUnexpectedErrorAt s!"'{curr}'" i
    | '!' =>
      let s := s.next' c.input i h
      let i' := s.pos
      if h : c.input.atEnd i' then s
      else if c.input.get' i' h == '['
      then s.mkUnexpectedErrorAt "![" i
      else s
    | '$' =>
      let s := s.next' c.input i h
      let i' := s.pos
      if h : c.input.atEnd i' then
        s
      else if c.input.get' i' h == '`' then
        s.mkUnexpectedErrorAt "$`" i
      else if c.input.get' i' h == '$' then
        let s := s.next' c.input i' h
        let i' := s.pos
        if h : c.input.atEnd i' then
          s
        else if c.input.get' i' h == '`' then
          s.mkUnexpectedErrorAt "$$`" i
        else s
      else s
    | _ => s.next' c.input i h

/-- Return some inline text up to the next inline opener or the end of
the line, whichever is first. Always consumes at least one
logical character on success, taking escaping into account. -/
def inlineText : ParserFn := asStringFn (transform := unescapeStr) <| atomicFn inlineTextChar >> manyFn inlineTextChar

/--
info: Failure @0 (⟨1, 0⟩): unexpected end of input
Final stack:
  <missing>
Remaining: ""
-/
#guard_msgs in
#eval inlineTextChar |>.test! ""


/--
info: Success! Final stack:
 empty
All input consumed.
-/
#guard_msgs in
#eval inlineTextChar |>.test! "a"

/--
info: Success! Final stack:
 empty
Remaining:
"bc"
-/
#guard_msgs in
#eval inlineTextChar |>.test! "abc"

/--
info: Failure @0 (⟨1, 0⟩): '['
Final stack:
  <missing>
Remaining: "[abc"
-/
#guard_msgs in
#eval inlineTextChar |>.test! "[abc"

/--
info: Success! Final stack:
 empty
Remaining:
"abc"
-/
#guard_msgs in
#eval inlineTextChar |>.test! "!abc"

/--
info: Success! Final stack:
  "!!"
Remaining:
"![abc"
-/
#guard_msgs in
#eval asStringFn (many1Fn inlineTextChar) |>.test! "!!![abc"

/--
info: Failure @0 (⟨1, 0⟩): '*'
Final stack:
  [<missing>]
Remaining: "*"
-/
#guard_msgs in
#eval asStringFn (many1Fn inlineTextChar) |>.test! "*"

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
  "!!!\\[abc"
Remaining:
"]"
-/
#guard_msgs in
#eval asStringFn (many1Fn inlineTextChar) |>.test! "!!!\\[abc]"

/--
info: Success! Final stack:
  ">"
All input consumed.
-/
#guard_msgs in
#eval asStringFn (transform := unescapeStr) (many1Fn inlineTextChar) |>.test! "\\>"


/-- Block opener prefixes -/
def blockOpener := atomicFn <|
  takeWhileEscFn (· == ' ') >>
  (atomicFn ((bullet >> chFn ' ')) <|>
   atomicFn ((numbering >> chFn ' ')) <|>
   atomicFn (strFn ": ") <|>
   atomicFn (atLeastFn 3 (chFn ':')) <|>
   atomicFn (atLeastFn 3 (chFn '`')) <|>
   atomicFn (strFn "%%%") <|>
   atomicFn (chFn '>'))

/--
info: Success! Final stack:
 empty
Remaining:
"abc"
-/
#guard_msgs in
#eval ignoreFn blockOpener |>.test! "+ abc"
/--
info: Success! Final stack:
 empty
Remaining:
"abc"
-/
#guard_msgs in
#eval ignoreFn blockOpener |>.test! "* abc"
/--
info: Success! Final stack:
 empty
Remaining:
"abc"
-/
#guard_msgs in
#eval ignoreFn blockOpener |>.test! " + abc"

def val : ParserFn :=
    nodeFn ``arg_num docNumLitFn <|>
    nodeFn ``arg_ident docIdentFn <|>
    nodeFn ``arg_str docStrLitFn

/--
info: Success! Final stack:
  (Verso.Syntax.arg_num (num "1"))
All input consumed.
-/
#guard_msgs in
  #eval val.test! "1"
/--
info: Success! Final stack:
  (Verso.Syntax.arg_num (num "3"))
All input consumed.
-/
#guard_msgs in
  #eval val.test! "3"
/--
info: Failure @0 (⟨1, 0⟩): unexpected end of input; expected identifier, numeral or string literal
Final stack:
  (Verso.Syntax.arg_str <missing>)
Remaining: ""
-/
#guard_msgs in
  #eval val.test! ""

/--
info: Success! Final stack:
  (Verso.Syntax.arg_str (str "\"a b c\t d\""))
All input consumed.
-/
#guard_msgs in
  #eval val.test! "\"a b c\t d\""

/--
info: Success! Final stack:
  (Verso.Syntax.arg_str (str "\"a b c\t d\""))
Remaining:
"\n"
-/
#guard_msgs in
  #eval val.test! "\"a b c\t d\"\n"

/--
info: Success! Final stack:
  (Verso.Syntax.arg_num (num "43"))
Remaining:
"\n\"foo\""
-/
#guard_msgs in
#eval val.test! "43\n\"foo\""

def withCurrentStackSize (p : Nat → ParserFn) : ParserFn := fun c s =>
  p s.stxStack.size c s

/-- Match the character indicated, pushing nothing to the stack in case of success -/
def skipChFn (c : Char) : ParserFn :=
  satisfyFn (· == c) c.toString

def skipToNewline : ParserFn :=
    takeUntilFn (· == '\n')

def skipToSpace : ParserFn :=
    takeUntilFn (· == ' ')

def skipRestOfLine : ParserFn :=
    skipToNewline >> (eoiFn <|> nl)

def skipBlock : ParserFn :=
  skipToNewline >> manyFn nonEmptyLine >> takeWhileFn (· == '\n')
where
  nonEmptyLine : ParserFn :=
    chFn '\n' >>
    takeWhileFn (fun c => c.isWhitespace && c != '\n') >>
    satisfyFn (!·.isWhitespace) "non-whitespace" >> skipToNewline

def recoverBlock (p : ParserFn) (final : ParserFn := skipFn) : ParserFn := recoverFn p fun _ => ignoreFn skipBlock >> final
def recoverBlockWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    ignoreFn skipBlock >>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.shrinkStack rctx.initialSize) (·.pushSyntax ·)
def recoverLine (p : ParserFn) : ParserFn := recoverFn p fun _ => ignoreFn <| skipRestOfLine
def recoverWs (p : ParserFn) : ParserFn := recoverFn p fun _ => ignoreFn <| takeUntilFn (fun c =>  c == ' ' || c == '\n')
def recoverEol (p : ParserFn) : ParserFn := recoverFn p fun _ => ignoreFn <| skipToNewline
def recoverEolWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    ignoreFn skipToNewline >>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.shrinkStack rctx.initialSize) (·.pushSyntax ·)
def recoverSkip (p : ParserFn) : ParserFn := recoverFn p fun _ => skipFn
def recoverSkipWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.shrinkStack rctx.initialSize) (·.pushSyntax ·)
def recoverHereWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.restore rctx.initialSize rctx.initialPos) (·.pushSyntax ·)


def arg : ParserFn :=
    withCurrentStackSize fun iniSz =>
      withParens iniSz <|> potentiallyNamed iniSz <|> (val >> mkAnon iniSz)
where
  mkNamed (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Verso.Syntax.named iniSz
  mkAnon (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Verso.Syntax.anon iniSz
  mkIdent (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Verso.Syntax.arg_ident iniSz
  potentiallyNamed iniSz :=
      atomicFn docIdentFn >> eatSpaces >>
       ((atomicFn (strFn ":=") >> eatSpaces >> val >> eatSpaces >> mkNamed iniSz) <|> (mkIdent iniSz >> mkAnon iniSz))
  withParens iniSz :=
    atomicFn (ignoreFn (strFn "(")) >> eatSpaces >>
    recoverWs (docIdentFn (reportAs := "argument name"))  >> eatSpaces >>
    recoverWs (strFn ":=") >> eatSpaces >>
    recoverWs val >> eatSpaces >>
    recoverEol (ignoreFn (strFn ")")) >> eatSpaces >>
    mkNamed iniSz

/--
info: Success! Final stack:
  (Verso.Syntax.anon (Verso.Syntax.arg_ident `x))
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "x"


/--
info: Success! Final stack:
  (Verso.Syntax.named
   `x
   ":="
   (Verso.Syntax.arg_num (num "1")))
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "x:=1"

/--
info: Success! Final stack:
  (Verso.Syntax.named
   `x
   ":="
   (Verso.Syntax.arg_num (num "1")))
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "(x:=1)"

/--
info: Failure @0 (⟨1, 0⟩): '
'; expected '(', identifier or numeral
Final stack:
  (Verso.Syntax.arg_str <missing>)
Remaining: "\n(x:=1)"
-/
#guard_msgs in
  #eval arg.test! "\n(x:=1)"

/--
info: Success! Final stack:
  (Verso.Syntax.named
   `x
   ":="
   (Verso.Syntax.arg_num (num "1")))
Remaining:
"\n"
-/
#guard_msgs in
  #eval arg.test! "(x:=1)\n"

/--
info: Success! Final stack:
  (Verso.Syntax.named
   `x
   ":="
   (Verso.Syntax.arg_ident `y))
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "x:=y"

/--
info: Success! Final stack:
  (Verso.Syntax.named
   `x
   ":="
   (Verso.Syntax.arg_ident `y))
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "(x:=y)"

/--
info: Success! Final stack:
  (Verso.Syntax.named
   `x
   ":="
   (Verso.Syntax.arg_str (str "\"y\"")))
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "x:=\"y\""

/--
info: Failure @3 (⟨1, 3⟩): unterminated string literal; expected identifier or numeral
Final stack:
 • `x
 • ":="
 • (Verso.Syntax.arg_str <missing>)

Remaining: "\"y"
-/
#guard_msgs in
  #eval arg.test! "x:=\"y"

/--
info: 2 failures:
  @7 (⟨1, 7⟩): expected ')'
    ""
  @7 (⟨1, 7⟩): unterminated string literal; expected identifier or numeral
    ""

Final stack:
  (Verso.Syntax.named
   `x
   ":="
   (Verso.Syntax.arg_str <missing>))
-/
#guard_msgs in
  #eval arg.test! "(x:=\"y)"


/--
info: Success! Final stack:
  (Verso.Syntax.anon
   (Verso.Syntax.arg_num (num "42")))
All input consumed.
-/
#guard_msgs in
#eval arg.test! "42"

/--
info: 4 failures:
  @4 (⟨1, 4⟩): expected ')'
    ""
  @4 (⟨1, 4⟩): expected ':='
    ""
  @4 (⟨1, 4⟩): expected argument name
    ""
  @4 (⟨1, 4⟩): unexpected end of input; expected identifier, numeral or string literal
    ""

Final stack:
  (Verso.Syntax.named
   <missing>
   <missing>
   (Verso.Syntax.arg_str <missing>))
-/
#guard_msgs in
#eval arg.test! "(42)"

/--
info: 3 failures:
  @6 (⟨1, 6⟩): expected ')'
    ""
  @6 (⟨1, 6⟩): expected ':='
    ""
  @6 (⟨1, 6⟩): unexpected end of input; expected identifier, numeral or string literal
    ""

Final stack:
  (Verso.Syntax.named
   `x
   <missing>
   (Verso.Syntax.arg_str <missing>))
-/
#guard_msgs in
#eval arg.test! "(x 42)"

/--
info: Failure @8 (⟨1, 8⟩): expected ')'
Final stack:
  (Verso.Syntax.named
   `x
   ":="
   (Verso.Syntax.arg_num (num "42")))
Remaining: "\n)"
-/
#guard_msgs in
#eval arg.test! "(x := 42\n)"

/--
info: Failure @8 (⟨1, 8⟩): expected ')'
Final stack:
  (Verso.Syntax.named
   `x
   ":="
   (Verso.Syntax.arg_num (num "42")))
Remaining: "\na"
-/
#guard_msgs in
#eval arg.test! "(x := 42\na"

/--
info: Success! Final stack:
  `x
Remaining:
"\n"
-/
#guard_msgs in
#eval docIdentFn.test! "x\n"

/--

Skip whitespace for name and arguments. If the argument is `none`,
it's in a single-line context and whitespace may only be the space
character. If it's `some N`, then newlines are allowed, but `N` is the
minimum indentation column.
-/
def nameArgWhitespace : (multiline : Option Nat) → ParserFn
  | none => eatSpaces
  | some n => takeWhileFn (fun c => c == ' ' || c == '\n') >> guardMinColumn n


/--
info: Success! Final stack:
 empty
Remaining:
"\n"
-/
#guard_msgs in
#eval nameArgWhitespace none |>.test! " \n"


def args (multiline : Option Nat := none) : ParserFn :=
  sepByFn true arg (nameArgWhitespace multiline)

def nameAndArgs (multiline : Option Nat := none) (reportNameAs : String := "identifier") : ParserFn :=
  nameArgWhitespace multiline >> docIdentFn (reportAs := reportNameAs) >>
  nameArgWhitespace multiline >> args (multiline := multiline)

/--
info: Success! Final stack:
 • `leanExample
 • [(Verso.Syntax.named
      `context
      ":="
      (Verso.Syntax.arg_num (num "2")))]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context := 2"

/--
info: Success! Final stack:
 • `scheme
 • [(Verso.Syntax.named
      `dialect
      ":="
      (Verso.Syntax.arg_str (str "\"chicken\"")))
     (Verso.Syntax.anon
      (Verso.Syntax.arg_num (num "43")))]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "scheme dialect:=\"chicken\" 43"


/--
info: Success! Final stack:
  [(Verso.Syntax.anon
    (Verso.Syntax.arg_num (num "43")))]
Remaining:
"\n\"foo\""
-/
#guard_msgs in
#eval args.test! "43\n\"foo\""

/--
info: Success! Final stack:
  [(Verso.Syntax.named
    `dialect
    ":="
    (Verso.Syntax.arg_str (str "\"chicken\"")))
   (Verso.Syntax.anon
    (Verso.Syntax.arg_num (num "43")))]
Remaining:
"\nfoo"
-/
#guard_msgs in
#eval args.test! "dialect:=\"chicken\" 43\nfoo"

/--
info: Success! Final stack:
  [(Verso.Syntax.named
    `dialect
    ":="
    (Verso.Syntax.arg_str (str "\"chicken\"")))
   (Verso.Syntax.anon
    (Verso.Syntax.arg_num (num "43")))]
Remaining:
"\n(foo)"
-/
#guard_msgs in
#eval args.test! "dialect:=\"chicken\" 43\n(foo)"

/--
info: Success! Final stack:
 • `scheme
 • [(Verso.Syntax.named
      `dialect
      ":="
      (Verso.Syntax.arg_str (str "\"chicken\"")))
     (Verso.Syntax.anon
      (Verso.Syntax.arg_num (num "43")))]

Remaining:
"\n(foo)"
-/
#guard_msgs in
#eval nameAndArgs.test! "scheme dialect:=\"chicken\" 43\n(foo)"

/--
info: Success! Final stack:
 • `leanExample
 • [(Verso.Syntax.anon
      (Verso.Syntax.arg_ident `context))]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context"
/--
info: Success! Final stack:
 • `leanExample
 • [(Verso.Syntax.anon
      (Verso.Syntax.arg_ident `context))
     (Verso.Syntax.anon
      (Verso.Syntax.arg_ident `more))]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context more"
/--
info: Success! Final stack:
 • `leanExample
 • [(Verso.Syntax.anon
      (Verso.Syntax.arg_ident `context))
     (Verso.Syntax.named
      `more
      ":="
      (Verso.Syntax.arg_str (str "\"stuff\"")))]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context more:=\"stuff\""


/--
info: Success! Final stack:
 • `leanExample
 • [(Verso.Syntax.anon
      (Verso.Syntax.arg_ident `context))
     (Verso.Syntax.named
      `more
      ":="
      (Verso.Syntax.arg_str (str "\"stuff\"")))]

Remaining:
"\n\nabc"
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context more:=\"stuff\"\n\nabc"

structure InlineCtxt where
  allowNewlines := true
  -- The minimum indentation of a continuation line for the current paragraph
  minIndent : Nat := 0
  -- How many asterisks introduced the current level of boldness? `none` means no bold here.
  boldDepth : Option Nat := none
  -- How many underscores introduced the current level of emphasis? `none` means no emphasis here.
  emphDepth : Option Nat := none

  -- Are we in a link?
  inLink : Bool := false

deriving Inhabited


/- Parsing inlines:
 * Inline parsers may not consume trailing whitespace, and must be robust in the face of leading whitespace
-/

/--
A linebreak that isn't a block break (that is, there's non-space content on the next line)
-/
def linebreak (ctxt : InlineCtxt) :=
  if ctxt.allowNewlines then
    nodeFn ``linebreak <|
      andthenFn (fakeAtom "line!") <|
        nodeFn strLitKind <|
        asStringFn (quoted := true) <|
          atomicFn (chFn '\n' >> lookaheadFn (manyFn (chFn ' ') >> notFollowedByFn (chFn '\n' <|> blockOpener) "newline"))
  else
    errorFn "Newlines not allowed here"

mutual
  partial def emphLike (name : SyntaxNodeKind) (char : Char) (what plural : String) (getter : InlineCtxt → Option Nat) (setter : InlineCtxt → Option Nat → InlineCtxt) (ctxt : InlineCtxt) : ParserFn :=
    nodeFn name <|
    withCurrentColumn fun c =>
      atomicFn (asStringFn (asStringFn (opener ctxt) >> notFollowedByFn (chFn ' ' false <|> chFn '\n' false) "space or newline after opener")) >>
      (recoverSkip <|
        withCurrentColumn fun c' =>
          let count := c' - c
          manyFn (inline (setter ctxt (some count))) >>
          asStringFn (atomicFn (noSpaceBefore >> repFn count (satisfyFn (· == char) s!"'{tok count}'"))))

  where
    tok (count : Nat) : String := ⟨List.replicate count char⟩
    opener (ctxt : InlineCtxt) : ParserFn :=
      match getter ctxt with
      | none => many1Fn (satisfyFn (· == char) s!"any number of {char}s")
      | some 1 | some 0 => fun _ s => s.mkError s!"Can't {what} here"
      | some d => atMostFn (d - 1) (satisfyFn (· == char) s!"{char}") s!"at most {d} {plural}"
    noSpaceBefore : ParserFn := fun c s =>
      if s.pos == 0 then s
      else
        let prior := c.input.get (c.input.prev s.pos)
        if prior.isWhitespace then
          s.mkError s!"'{char}' without preceding space"
        else s

  partial def emph := emphLike ``emph '_' "emphasize" "underscores" (·.emphDepth) ({· with emphDepth := ·})
  partial def bold := emphLike ``bold '*' "bold" "asterisks" (·.boldDepth) ({· with boldDepth := ·})

  partial def code : ParserFn :=
    nodeFn ``code <|
    withCurrentColumn fun c =>
      atomicFn opener >>
      (recoverHereWith #[.missing, .missing] <| atomicFn <|
        withCurrentColumn fun c' =>
          let count := c' - c
          nodeFn strLitKind
            (asStringFn (many1Fn <| codeContentsFn (count - 1)) (quoted := true) >>
             normFn) >>
          closer count)
  where
    opener : ParserFn := asStringFn (many1Fn (satisfyFn (· == '`') s!"any number of backticks"))
    closer (count : Nat) : ParserFn :=
      asStringFn (atomicFn (repFn count (satisfyFn' (· == '`') s!"expected '{String.mk (.replicate count '`')}' to close inline code"))) >>
      notFollowedByFn (satisfyFn (· == '`') "`") "backtick"
    takeBackticksFn : Nat → ParserFn
      | 0 => satisfyFn (fun _ => false)
      | n+1 => optionalFn (chFn '`' >> takeBackticksFn n)
    codeContentsFn (maxCount : Nat) : ParserFn :=
      atomicFn (asStringFn (satisfyFn (maxCount > 0 && · == '`') >> atMostFn (maxCount - 1) (chFn '`') s!"at most {maxCount} backticks")) <|>
      satisfyFn (· != '`') "expected character other than backtick ('`')"
    normFn : ParserFn := fun _c s => Id.run <| do
      let str := s.stxStack.back
      if let .atom info str := str then
        if str.startsWith "\" " && str.endsWith " \"" then
          let str := "\"" ++ (str.drop 2 |>.dropRight 2) ++ "\""
          if str.any (· != ' ') then
            let info : SourceInfo :=
              match info with
              | .none => .none
              | .synthetic start stop c => .synthetic (start + ⟨1⟩) (stop - ⟨1⟩) c
              | .original leading start trailing stop =>
                .original
                  {leading with stopPos := leading.stopPos + ⟨1⟩} (start + ⟨1⟩)
                  {trailing with startPos := trailing.startPos - ⟨1⟩} (stop - ⟨1⟩)
            return s.popSyntax.pushSyntax (.atom info str)
      return s

    takeContentsFn (maxCount : Nat) : ParserFn := fun c s =>
      let i := s.pos
      if h : c.input.atEnd i then s.mkEOIError
      else
        let ch := c.input.get' i h
        let s := s.next' c.input i h
        let i := s.pos
        if ch == '\\' then
          if h : c.input.atEnd i then s.mkEOIError
          else
            let ch := c.input.get' i h
            let s := s.next' c.input i h
            if ch ∈ ['`', '\\'] then takeContentsFn maxCount c s
            else
              s.mkError "expected 'n', '\\', or '`'"
        else if ch == '`' then
          optionalFn (atomicFn (takeBackticksFn maxCount) >> takeContentsFn maxCount) c s
        else if ch == '\n' then
          s.mkError "unexpected newline"
        else takeContentsFn maxCount c s

  partial def math : ParserFn :=
    atomicFn (nodeFn ``display_math <| strFn "$$" >> code) <|>
    atomicFn (nodeFn ``inline_math <| strFn "$" >> code)

  -- Read a prefix of a line of text, stopping at a text-mode special character
  partial def text :=
    nodeFn ``text <|
      nodeFn strLitKind <|
        asStringFn (transform := unescapeStr) (quoted := true) <|
          many1Fn inlineTextChar

  partial def link (ctxt : InlineCtxt) :=
    nodeFn ``link <|
      (atomicFn (notInLink ctxt >> strFn "[" >> notFollowedByFn (chFn '^') "'^'" )) >>
      (recoverEol <|
        many1Fn (inline {ctxt with inLink := true}) >>
        strFn "]" >> linkTarget)

  partial def footnote (ctxt : InlineCtxt) :=
    nodeFn ``footnote <|
      (atomicFn (notInLink ctxt >> strFn "[^" )) >>
      (recoverLine <|
        nodeFn `str (asStringFn (quoted := true) (many1Fn (satisfyEscFn (fun c => c != ']' && c != '\n') "other than ']' or newline"))) >>
        strFn "]")

  partial def linkTarget := ref <|> url
  where
    notUrlEnd := satisfyEscFn (· ∉ ")\n".toList) "not ')' or newline" >> takeUntilEscFn (· ∈ ")\n".toList)
    notRefEnd := satisfyEscFn (· ∉ "]\n".toList) "not ']' or newline" >> takeUntilEscFn (· ∈ "]\n".toList)
    ref : ParserFn :=
      nodeFn ``Verso.Syntax.ref <|
        (atomicFn <| strFn "[") >>
        recoverEol (nodeFn strLitKind (asStringFn notRefEnd (quoted := true)) >> strFn "]")
    url : ParserFn :=
      nodeFn ``Verso.Syntax.url <|
        (atomicFn <| strFn "(") >>
        recoverEol (nodeFn strLitKind (asStringFn notUrlEnd (quoted := true)) >> strFn ")")

  partial def notInLink (ctxt : InlineCtxt) : ParserFn := fun _ s =>
      if ctxt.inLink then s.mkError "Already in a link" else s

  partial def image : ParserFn :=
    nodeFn ``image <|
      atomicFn (strFn "![") >>
      (recoverSkip <|
        nodeFn strLitKind (asStringFn (takeUntilEscFn (· ∈ "]\n".toList)) (quoted := true)) >>
        strFn "]" >>
        linkTarget)

  partial def role (ctxt : InlineCtxt) : ParserFn :=
    nodeFn ``role <|
      intro >> (bracketed <|> atomicFn nonBracketed)
  where
    intro := atomicFn (chFn '{') >> recoverBlock (eatSpaces >> nameAndArgs >> eatSpaces >> chFn '}')
    bracketed := atomicFn (chFn '[') >> recoverBlock (manyFn (inline ctxt) >> chFn ']')
    fakeOpen := mkAtom SourceInfo.none "["
    fakeClose := mkAtom SourceInfo.none "]"
    nonBracketed : ParserFn := fun c s =>
      let s := s.pushSyntax fakeOpen
      let s := nodeFn nullKind (delimitedInline ctxt) c s
      s.pushSyntax fakeClose


  partial def delimitedInline (ctxt : InlineCtxt) : ParserFn := emph ctxt <|> bold ctxt <|> code <|> math <|> role ctxt <|> image <|> link ctxt <|> footnote ctxt

  partial def inline (ctxt : InlineCtxt) : ParserFn :=
    text <|> linebreak ctxt <|> delimitedInline ctxt
end


def textLine (allowNewlines := true) : ParserFn := many1Fn (inline { allowNewlines })

/--
info: Success! Final stack:
  (Verso.Syntax.text (str "\"abc \""))
All input consumed.
-/
#guard_msgs in
  #eval text.test! "abc "

/--
info: Success! Final stack:
  (Verso.Syntax.emph
   "_"
   [(Verso.Syntax.text (str "\"aa\""))]
   "_")
All input consumed.
-/
#guard_msgs in
  #eval emph {} |>.test! "_aa_"

/--
info: Failure @4 (⟨1, 4⟩): expected '_' without preceding space
Final stack:
  (Verso.Syntax.emph
   "_"
   [(Verso.Syntax.text (str "\"aa \""))]
   <missing>)
Remaining: "_"
-/
#guard_msgs in
  #eval emph {} |>.test! "_aa _"

/--
info: Failure @0 (⟨1, 0⟩): unexpected space or newline after opener
Final stack:
  (Verso.Syntax.emph "_" <missing>)
Remaining: "_ aa_"
-/
#guard_msgs in
  #eval emph {} |>.test! "_ aa_"


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
  (Verso.Syntax.code
   "``"
   (str "\"foo bar\"")
   "``")
All input consumed.
-/
#guard_msgs in
  #eval code.test! "``foo bar``"

/--
info: Success! Final stack:
  (Verso.Syntax.code
   "``"
   (str "\"foo `stuff` bar\"")
   "``")
All input consumed.
-/
#guard_msgs in
  #eval code.test! "``foo `stuff` bar``"

/--
info: Failure @1 (⟨1, 1⟩): expected '`' to close inline code
Final stack:
  (Verso.Syntax.code "`" <missing> <missing>)
Remaining: "foo"
-/
#guard_msgs in
  #eval code.test! "`foo"

/--
info: Success! Final stack:
  (Verso.Syntax.code "`" (str "\" foo\"") "`")
All input consumed.
-/
#guard_msgs in
  #eval code.test! "` foo`"

/--
info: Success! Final stack:
  (Verso.Syntax.code "`" (str "\"foo\"") "`")
All input consumed.
-/
#guard_msgs in
  #eval code.test! "` foo `"

/--
info: Success! Final stack:
  (Verso.Syntax.code "`" (str "\"fo\\no\"") "`")
All input consumed.
-/
#guard_msgs in
  #eval code.test! "` fo\no `"

/--
info: Success! Final stack:
  (Verso.Syntax.code "``" (str "\"`x\"") "``")
All input consumed.
-/
#guard_msgs in
#eval code.test! "`` `x ``"

/--
info: Success! Final stack:
  (Verso.Syntax.code
   "``"
   (str "\"foo bar\"")
   "``")
All input consumed.
-/
#guard_msgs in
  #eval (inline {}).test! "``foo bar``"

/--
info: Success! Final stack:
  (Verso.Syntax.code
   "``"
   (str "\"foo `stuff` bar\"")
   "``")
All input consumed.
-/
#guard_msgs in
  #eval (inline {}).test! "``foo `stuff` bar``"

/--
info: Failure @1 (⟨1, 1⟩): expected '`' to close inline code
Final stack:
  (Verso.Syntax.code "`" <missing> <missing>)
Remaining: "foo"
-/
#guard_msgs in
  #eval (inline {}).test! "`foo"

/--
info: Success! Final stack:
  (Verso.Syntax.code "`" (str "\" foo\"") "`")
All input consumed.
-/
#guard_msgs in
  #eval (inline {}).test! "` foo`"

/--
info: Success! Final stack:
  (Verso.Syntax.code "`" (str "\"foo\"") "`")
All input consumed.
-/
#guard_msgs in
  #eval (inline {}).test! "` foo `"

/--
info: Success! Final stack:
  (Verso.Syntax.code "`" (str "\"fo\\no\"") "`")
All input consumed.
-/
#guard_msgs in
  #eval (inline {}).test! "` fo\no `"

/--
info: Failure @2 (⟨1, 2⟩): expected '``' to close inline code
Final stack:
  (Verso.Syntax.code "``" <missing> <missing>)
Remaining: " fo\no `"
-/
#guard_msgs in
  #eval (inline {}).test! "`` fo\no `"


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
  (Verso.Syntax.bold
   "**"
   [(Verso.Syntax.text (str "\"aa\""))
    (Verso.Syntax.linebreak
     "line!"
     (str "\"\\n\""))
    (Verso.Syntax.text (str "\"bb\""))]
   "**")
All input consumed.
-/
#guard_msgs in
  #eval inline {} |>.test! "**aa\nbb**"

/--
info: Success! Final stack:
  (Verso.Syntax.text (str "\"a \""))
Remaining:
"* b"
-/
#guard_msgs in
  #eval inline {} |>.test! "a * b"

/--
info: Success! Final stack:
  (Verso.Syntax.link
   "["
   [(Verso.Syntax.text (str "\"Wikipedia\""))]
   "]"
   (Verso.Syntax.url
    "("
    (str "\"https://en.wikipedia.org\"")
    ")"))
All input consumed.
-/
#guard_msgs in
  #eval inline {} |>.test! "[Wikipedia](https://en.wikipedia.org)"

/--
info: Success! Final stack:
  (Verso.Syntax.image
   "!["
   (str "\"\"")
   "]"
   (Verso.Syntax.url
    "("
    (str "\"logo.png\"")
    ")"))
All input consumed.
-/
#guard_msgs in
  #eval inline {} |>.test! "![](logo.png)"

/--
info: Failure @12 (⟨1, 12⟩): expected ')'
Final stack:
  (Verso.Syntax.image
   "!["
   (str "\"\"")
   "]"
   (Verso.Syntax.url
    "("
    (str "\"logo.png\"")
    <missing>))
Remaining: "\nabc"
-/
#guard_msgs in
  #eval inline {} |>.test! "![](logo.png\nabc"

/--
info: Failure @5 (⟨1, 5⟩): expected ']'
Final stack:
  (Verso.Syntax.image
   "!["
   (str "\"abc\"")
   <missing>)
Remaining: "\n123"
-/
#guard_msgs in
  #eval inline {} |>.test! "![abc\n123"


/--
info: Success! Final stack:
  (Verso.Syntax.image
   "!["
   (str "\"alt text is good\"")
   "]"
   (Verso.Syntax.url
    "("
    (str "\"logo.png\"")
    ")"))
All input consumed.
-/
#guard_msgs in
  #eval inline {} |>.test! "![alt text is good](logo.png)"

/--
info: Failure @19 (⟨1, 19⟩): expected '(' or '['
Final stack:
  (Verso.Syntax.image
   "!["
   (str "\"alt text is good\"")
   "]"
   (Verso.Syntax.url <missing>))
Remaining: "](logo.png)"
-/
#guard_msgs in
  #eval inline {} |>.test! "![alt text is good]](logo.png)"

/--
info: Success! Final stack:
  (Verso.Syntax.role
   "{"
   `hello
   []
   "}"
   "["
   [(Verso.Syntax.bold
     "*"
     [(Verso.Syntax.text (str "\"there\""))]
     "*")]
   "]")
All input consumed.
-/
#guard_msgs in
#eval role {} |>.test! "{hello}*there*"

/--
info: Success! Final stack:
  (Verso.Syntax.role
   "{"
   `hello
   []
   "}"
   "["
   [(Verso.Syntax.text (str "\"there\""))]
   "]")
All input consumed.
-/
#guard_msgs in
#eval role {} |>.test! "{hello}[there]"

/--
info: Success! Final stack:
  (Verso.Syntax.role
   "{"
   `ref
   [(Verso.Syntax.anon
     (Verso.Syntax.arg_ident `other))]
   "}"
   "["
   [(Verso.Syntax.role
     "{"
     `leanKw
     []
     "}"
     "["
     [(Verso.Syntax.code "`" (str "\"cmd\"") "`")]
     "]")
    (Verso.Syntax.text (str "\" is great\""))]
   "]")
All input consumed.
-/
#guard_msgs in
#eval role {} |>.test! "{ref other}[{leanKw}`cmd` is great]"

/--
info: Success! Final stack:
  (Verso.Syntax.role
   "{"
   `hello
   [(Verso.Syntax.named
     `world
     ":="
     (Verso.Syntax.arg_ident `gaia))]
   "}"
   "["
   [(Verso.Syntax.text (str "\"there\""))]
   "]")
All input consumed.
-/
#guard_msgs in
#eval role {} |>.test! "{hello world:=gaia}[there]"

/--
info: Success! Final stack:
  (Verso.Syntax.role
   "{"
   `hello
   [(Verso.Syntax.named
     `world
     ":="
     (Verso.Syntax.arg_ident `gaia))]
   "}"
   "["
   [(Verso.Syntax.text (str "\"there \""))
    (Verso.Syntax.bold
     "*"
     [(Verso.Syntax.text (str "\"is\""))]
     "*")
    (Verso.Syntax.text (str "\" \""))
    (Verso.Syntax.emph
     "_"
     [(Verso.Syntax.text (str "\"a meaning!\""))]
     "_")
    (Verso.Syntax.text (str "\" \""))]
   "]")
All input consumed.
-/
#guard_msgs in
#eval role {} |>.test! "{hello world:=gaia}[there *is* _a meaning!_ ]"

/--
info: Success! Final stack:
  (Verso.Syntax.footnote "[^" (str "\"1\"") "]")
All input consumed.
-/
#guard_msgs in
#eval footnote {} |>.test! "[^1]"

/--
info: Success! Final stack:
  (Verso.Syntax.footnote "[^" (str "\"1\"") "]")
All input consumed.
-/
#guard_msgs in
#eval inline {} |>.test! "[^1]"

/--
info: Success! Final stack:
  (Verso.Syntax.inline_math
   "$"
   (Verso.Syntax.code
    "`"
    (str "\"\\\\frac{x}{4}\"")
    "`"))
All input consumed.
-/
#guard_msgs in
#eval inline {} |>.test! "$`\\frac{x}{4}`"

/--
info: Success! Final stack:
  (Verso.Syntax.inline_math
   "$"
   (Verso.Syntax.code
    "`"
    (str "\"\\\\frac{\\n  x\\n}{\\n  4\\n}\\n\"")
    "`"))
All input consumed.
-/
#guard_msgs in
#eval inline {} |>.test! "$`\\frac{
  x
}{
  4
}
`"


/--
info: Success! Final stack:
  (Verso.Syntax.display_math
   "$$"
   (Verso.Syntax.code
    "`"
    (str "\"\\\\frac{x}{4}\"")
    "`"))
All input consumed.
-/
#guard_msgs in
#eval inline {} |>.test! "$$`\\frac{x}{4}`"

/--
info: Success! Final stack:
  (Verso.Syntax.text (str "\"$35.23\""))
All input consumed.
-/
#guard_msgs in
#eval inline {} |>.test! "$35.23"

/--
info: Success! Final stack:
  (Verso.Syntax.text (str "\"$\""))
Remaining:
"`code`"
-/
#guard_msgs in
#eval inline {} |>.test! "\\$`code`"

/--
info: Success! Final stack:
  (Verso.Syntax.text (str "\"$$$\""))
All input consumed.
-/
#guard_msgs in
#eval inline {} |>.test! "$$$"

open Lean.Parser.Term in
def metadataBlock : ParserFn :=
  nodeFn ``metadata_block <|
    opener >>
    metadataContents.fn >>
    takeWhileFn (·.isWhitespace) >>
    closer
where
  opener := atomicFn (bolThen (eatSpaces >> strFn "%%%") "%%% (at line beginning)") >> eatSpaces >> ignoreFn (chFn '\n')
  closer := bolThen (eatSpaces >> strFn "%%%") "%%% (at line beginning)" >> eatSpaces >> ignoreFn (chFn '\n' <|> eoiFn)


/--
info: Success! Final stack:
  (Verso.Syntax.metadata_block
   "%%%"
   (Term.structInstFields [])
   "%%%")
All input consumed.
-/
#guard_msgs in
#eval metadataBlock |>.test! "%%%\n%%%\n"

/--
info: Success! Final stack:
  (Verso.Syntax.metadata_block
   "%%%"
   (Term.structInstFields
    [(Term.structInstField
      (Term.structInstLVal `foo [])
      [[] [] (Term.structInstFieldDef ":=" `bar)])
     []])
   "%%%")
All input consumed.
-/
#guard_msgs in
#eval metadataBlock |>.test! "%%%\nfoo := bar\n\n%%%\n"

/--
info: Success! Final stack:
  (Verso.Syntax.metadata_block
   "%%%"
   (Term.structInstFields
    [(Term.structInstField
      (Term.structInstLVal `foo [])
      [[] [] (Term.structInstFieldDef ":=" `bar)])
     []
     (Term.structInstField
      (Term.structInstLVal `x [])
      [])
     []])
   "%%%")
All input consumed.
-/
#guard_msgs in
#eval metadataBlock |>.test! "%%%\nfoo := bar\nx\n%%%\n"


structure InList where
  indentation : Nat
  type : OrderedListType ⊕ UnorderedListType
deriving Repr

structure BlockCtxt where
  minIndent : Nat := 0
  maxDirective : Option Nat := none
  inLists : List InList := []
deriving Inhabited, Repr

def lookaheadOrderedListIndicator (ctxt : BlockCtxt) (p : OrderedListType → Int → ParserFn) : ParserFn := fun c s =>
    let iniPos := s.pos
    let iniSz := s.stxStack.size
    let s := (onlyBlockOpeners >> takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent) c s
    if s.hasError then s.setPos iniPos |>.shrinkStack iniSz
    else
    let numPos := s.pos
    let s := ignoreFn (takeWhile1Fn (·.isDigit) "digits") c s
    if s.hasError then {s with pos := iniPos}.shrinkStack iniSz else
    let digits := c.input.extract numPos s.pos
    match digits.toNat? with
    | none => {s.mkError s!"digits, got '{digits}'" with pos := iniPos}
    | some n =>
      let i := s.pos
      if h : c.input.atEnd i then {s.mkEOIError with pos := iniPos}
      else
        let (s, next, type) := match c.input.get' i h with
          | '.' => (s.next' c.input i h, chFn ' ', OrderedListType.numDot)
          | ')' => (s.next' c.input i h, chFn ' ', OrderedListType.parenAfter)
          | other => (s.setError {unexpected := s!"unexpected '{other}'", expected := ["'.'", "')'"]}, skipFn, .numDot)
        if s.hasError then {s with pos := iniPos}
        else
          let s := next c s
          if s.hasError then {s with pos := iniPos}
          else
            let leading := mkEmptySubstringAt c.input numPos
            let trailing := mkEmptySubstringAt c.input i
            let num := Syntax.mkNumLit digits (info := .original leading numPos trailing i)
            p type n c (s.shrinkStack iniSz |>.setPos numPos |>.pushSyntax num)
/--
info: Success! Final stack:
 • (num "1")
 • "Verso.Parser.OrderedListType.numDot 1"

Remaining:
"1. "
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "1. "
/--
info: Success! Final stack:
 • (num "2")
 • "Verso.Parser.OrderedListType.numDot 2"

Remaining:
"2. "
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "2. "
/--
info: Failure @0 (⟨1, 0⟩): unexpected end of input
Final stack:
  <missing>
Remaining: "2."
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "2."
/--
info: Success! Final stack:
 • (num "2")
 • "Verso.Parser.OrderedListType.parenAfter 2"

Remaining:
"2) "
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "2) "
/--
info: Failure @0 (⟨1, 0⟩): digits
Final stack:
 empty
Remaining: "-23) "
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "-23) "
/--
info: Failure @0 (⟨1, 0⟩): digits
Final stack:
 empty
Remaining: "a-23) "
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "a-23) "
/--
info: Failure @0 (⟨1, 0⟩): unexpected ' '; expected ')' or '.'
Final stack:
 empty
Remaining: "23 ) "
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "23 ) "

def lookaheadUnorderedListIndicator (ctxt : BlockCtxt) (p : UnorderedListType → ParserFn) : ParserFn := fun c s =>
  let iniPos := s.pos
  let iniSz := s.stxStack.size
  let s := (onlyBlockOpeners >> takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent) c s
  let bulletPos := s.pos
  if s.hasError then s.setPos iniPos |>.shrinkStack iniSz
  else if h : c.input.atEnd s.pos then s.mkEOIError.setPos iniPos |>.shrinkStack iniSz
  else let (s, type) : (_ × UnorderedListType) := match c.input.get' s.pos h with
    | '*' => (s.next' c.input s.pos h, .asterisk)
    | '-' => (s.next' c.input s.pos h, .dash)
    | '+' => (s.next' c.input s.pos h, .plus)
    | other => (s.setError {expected := ["*", "-", "+"], unexpected := s!"'{other}'"}, .plus)
  if s.hasError then s.setPos iniPos
  else
    let s := (chFn ' ') c s
    if s.hasError then s.setPos iniPos
    else p type c (s.shrinkStack iniSz |>.setPos bulletPos)

/--
info: Success! Final stack:
  "Verso.Parser.UnorderedListType.asterisk"
Remaining:
"* "
-/
#guard_msgs in
#eval lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}") |>.test! "* "
/--
info: Success! Final stack:
  "Verso.Parser.UnorderedListType.dash"
Remaining:
"- "
-/
#guard_msgs in
#eval lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}") |>.test! "- "
/--
info: Success! Final stack:
  "Verso.Parser.UnorderedListType.plus"
Remaining:
"+ "
-/
#guard_msgs in
#eval lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}") |>.test! "+ "
/--
info: Success! Final stack:
  "Verso.Parser.UnorderedListType.asterisk"
Remaining:
"* "
-/
#guard_msgs in
#eval lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}") |>.test! " * "

/--
info: Failure @0 (⟨1, 0⟩): unexpected end of input
Final stack:
  <missing>
Remaining: " *"
-/
#guard_msgs in
#eval lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}") |>.test! " *"
/--
info: Failure @0 (⟨1, 0⟩): ' '
Final stack:
  <missing>
Remaining: "** "
-/
#guard_msgs in
#eval lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}") |>.test! "** "


def skipUntilDedent (indent : Nat) : ParserFn :=
  skipRestOfLine >>
  manyFn (chFn ' ' >> takeWhileFn (· == ' ') >> guardColumn (· ≥ indent) s!"indentation at {indent}" >> skipRestOfLine)

def recoverUnindent (indent : Nat) (p : ParserFn) (finish : ParserFn := skipFn) : ParserFn := recoverFn p (fun _ => ignoreFn (skipUntilDedent indent) >> finish)

mutual
  partial def listItem (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``li (bulletFn >> withCurrentColumn fun c => blocks {ctxt with minIndent := c})
  where
    bulletFn :=
      match ctxt.inLists.head? with
      | none => fun _ s => s.mkError "not in a list"
      | some ⟨col, .inr type⟩ =>
        atomicFn <|
          takeWhileFn (· == ' ') >>
          guardColumn (· == col) s!"indentation at {col}" >>
          unorderedListIndicator type >> ignoreFn (lookaheadFn (chFn ' '))
      | some ⟨col, .inl type⟩ =>
        atomicFn <|
          takeWhileFn (· == ' ') >>
          guardColumn (· == col) s!"indentation at {col}" >>
          orderedListIndicator type >> ignoreFn (lookaheadFn (chFn ' '))


  partial def descItem (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``desc <|
      colonFn >>
      withCurrentColumn fun c => textLine >> ignoreFn (manyFn blankLine) >>
      fakeAtom "=>" >>
      takeWhileFn (· == ' ') >>
      recoverSkip (guardColumn (· ≥ c) s!"indentation at least {c}" >>
        blocks1 { ctxt with minIndent := c}) >>
      ignoreFn (manyFn blankLine)
  where
    colonFn := atomicFn <|
      takeWhileFn (· == ' ') >>
      guardColumn (· == ctxt.minIndent) s!"indentation at {ctxt.minIndent}" >>
      asStringFn (chFn ':' false) >> ignoreFn (lookaheadFn (chFn ' '))

  partial def blockquote (ctxt : BlockCtxt) : ParserFn :=
    atomicFn <| nodeFn ``blockquote <|
      takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent >> chFn '>' >>
      withCurrentColumn fun c => blocks { ctxt with minIndent := c }

  partial def unorderedList (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``ul <|
      lookaheadUnorderedListIndicator ctxt fun type =>
        withCurrentColumn fun c =>
          fakeAtom "ul{" >>
          many1Fn (listItem {ctxt with minIndent := c + 1 , inLists := ⟨c, .inr type⟩  :: ctxt.inLists}) >>
          fakeAtom "}"

  partial def orderedList (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``ol <|
      fakeAtom "ol(" >>
      lookaheadOrderedListIndicator ctxt fun type _start => -- TODO? Validate list numbering?
        withCurrentColumn fun c =>
          fakeAtom ")" >> fakeAtom "{" >>
          many1Fn (listItem {ctxt with minIndent := c + 1 , inLists := ⟨c, .inl type⟩  :: ctxt.inLists}) >>
          fakeAtom "}"


  partial def definitionList (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``dl <|
      atomicFn (onlyBlockOpeners >> takeWhileFn (· == ' ') >> ignoreFn (lookaheadFn (chFn ':' >> chFn ' ')) >> guardMinColumn ctxt.minIndent) >>
      withInfoSyntaxFn skip.fn (fun info => fakeAtom "ul{" info) >>
      withCurrentColumn (fun c => many1Fn (descItem {ctxt with minIndent := c})) >>
      withInfoSyntaxFn skip.fn (fun info => fakeAtom "}" info)

  partial def para (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``para <|
      atomicFn (takeWhileFn (· == ' ') >> notFollowedByFn blockOpener "block opener" >> guardMinColumn ctxt.minIndent) >>
      withInfoSyntaxFn skip.fn (fun info => fakeAtom "para{" (info := info)) >>
      textLine >>
      withInfoSyntaxFn skip.fn (fun info => fakeAtom "}" (info := info))

  partial def header (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``header <|
      guardMinColumn ctxt.minIndent >>
      atomicFn (bol >>
        withCurrentColumn fun c =>
          withInfoSyntaxFn (many1Fn (skipChFn '#')) (fun info => fakeAtom "header(" (info := info)) >>
          withCurrentColumn fun c' =>
            skipChFn ' ' >> takeWhileFn (· == ' ') >> lookaheadFn (satisfyFn (· != '\n') "non-newline") >>
            (show ParserFn from fun _ s => s.pushSyntax <| Syntax.mkNumLit (toString <| c' - c - 1)) >>
            fakeAtom ")") >>
      fakeAtom "{" >>
      textLine (allowNewlines := false) >>
      fakeAtom "}"




  partial def codeBlock (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``codeblock <|
      -- Opener - leaves indent info and open token on the stack
      atomicFn (takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent >> pushColumn >> asStringFn (atLeastFn 3 (skipChFn '`'))) >>
        withIndentColumn fun c =>
          recoverUnindent c <|
            withCurrentColumn fun c' =>
              let fenceWidth := c' - c
              takeWhileFn (· == ' ') >>
              optionalFn nameAndArgs >>
              asStringFn (satisfyFn (· == '\n') "newline") >>
              nodeFn strLitKind (asStringFn (manyFn (atomicFn blankLine <|> codeFrom c fenceWidth)) (transform := deIndent c) (quoted := true)) >>
              closeFence c fenceWidth
  where
    withIndentColumn (p : Nat → ParserFn) : ParserFn := fun c s =>
      let colStx := s.stxStack.get! (s.stxStack.size - 2)
      match colStx with
      | .node _ `column #[.atom _ col] =>
        if let some colNat := col.toNat? then
          let opener := s.stxStack.get! (s.stxStack.size - 1)
          p colNat c (s.popSyntax.popSyntax.pushSyntax opener)
        else
          s.mkError s!"Internal error - not a Nat {col}"
      | other => s.mkError s!"Internal error - not a column node {other}"

    deIndent (n : Nat) (str : String) : String := Id.run do
      let str := if str != "" && str.back == '\n' then str.dropRight 1 else str
      let mut out := ""
      for line in str.splitOn "\n" do
        out := out ++ line.drop n ++ "\n"
      out

    codeFrom (col width : Nat) :=
      atomicFn (bol >> takeWhileFn (· == ' ') >> guardMinColumn col >>
        notFollowedByFn (atLeastFn width (skipChFn '`')) "ending fence") >>
      manyFn (satisfyFn (· != '\n') "non-newline") >> satisfyFn (· == '\n') "newline"

    closeFence (col width : Nat) :=
      bol >> takeWhileFn (· == ' ') >> guardColumn (· == col) s!"column {col}" >>
      atomicFn (asStringFn (repFn width (skipChFn '`'))) >>
      notFollowedByFn (skipChFn '`') "extra `" >>
      takeWhileFn (· == ' ') >> (satisfyFn (· == '\n') "newline" <|> eoiFn)

  partial def directive (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``directive <|
      -- Opener - leaves indent info and open token on the stack
      atomicFn
        (eatSpaces >> guardMinColumn ctxt.minIndent >>
          asStringFn (atLeastFn 3 (skipChFn ':')) >>
         guardOpenerSize >>
         eatSpaces >>
         recoverEolWith #[.missing, .node .none nullKind #[]] (nameAndArgs (reportNameAs := "directive name (identifier)") >>
         satisfyFn (· == '\n') "newline")) >>
       fakeAtom "\n" >>
       ignoreFn (manyFn blankLine) >>
        (withFencePos 3 fun ⟨l, col⟩ =>
          withFenceSize 3 fun fenceWidth =>
            blocks {ctxt with minIndent := col, maxDirective := fenceWidth} >>
            recoverHereWith #[.missing]
              (closeFence l fenceWidth >>
               withFence 0 fun info _ c s =>
                if (c.fileMap.toPosition info.getPos!).column != col then
                  s.mkErrorAt s!"closing '{String.mk <| List.replicate fenceWidth ':'}' from directive on line {l} at column {col}, but it's at column {(c.fileMap.toPosition info.getPos!).column}" info.getPos!
                else
                  s))

  where
    withFence (atDepth : Nat) (p : SourceInfo → String → ParserFn) : ParserFn := fun c s =>
        match s.stxStack.get! (s.stxStack.size - (atDepth + 1)) with
        | .atom info str =>
          if str.all (· == ':') then
            p info str c s
          else
            s.mkError s!"Internal error - index {atDepth} wasn't the directive fence - it was the atom {str}"
        | .missing => s.pushSyntax .missing
        | stx =>
          s.mkError s!"Internal error - index {atDepth} wasn't the directive fence - it was {stx}"

    withFenceSize (atDepth : Nat) (p : Nat → ParserFn) : ParserFn :=
      withFence atDepth fun _ str => p str.length

    withFencePos (atDepth : Nat) (p : Position → ParserFn) : ParserFn :=
      withFence atDepth fun info _ c s => p (c.fileMap.toPosition info.getPos!) c s

    withIndentColumn (atDepth : Nat) (p : Nat → ParserFn) : ParserFn :=
      withFence atDepth fun info _ c s =>
        let col := c.fileMap.toPosition info.getPos! |>.column
        p col c s

    guardOpenerSize : ParserFn := withFenceSize 0 fun x =>
        if let some m := ctxt.maxDirective then
          if x < m then skipFn else fun _ s => s.mkError "Too many ':'s here"
        else skipFn

    closeFence (line width : Nat) :=
      let str := String.mk (.replicate width ':')
      bolThen (description := s!"closing '{str}' for directive from line {line}")
        (eatSpaces >>
         asStringFn (strFn str) >> notFollowedByFn (chFn ':') "':'" >>
         eatSpaces >>
         (ignoreFn <| atomicFn (satisfyFn (· == '\n') "newline") <|> eoiFn))


  -- This low-level definition is to get exactly the right amount of lookahead
  -- together with column tracking
  partial def block_role (ctxt : BlockCtxt) : ParserFn := fun c s =>
    let iniPos := s.pos
    let iniSz := s.stxStack.size
    let restorePosOnErr : ParserState → ParserState
      | ⟨stack, lhsPrec, _, cache, some msg, errs⟩ => ⟨stack, lhsPrec, iniPos, cache, some msg, errs⟩
      | other => other
    let s := eatSpaces c s
    if s.hasError then restorePosOnErr s
    else
      let col := c.currentColumn s
      let s := (intro >> eatSpaces >> ignoreFn (satisfyFn (· == '\n') "newline" <|> eoiFn)) c s
      if s.hasError then restorePosOnErr s
      else
        let s := (nodeFn nullKind <| atomicFn (ignoreFn (eatSpaces >> (satisfyFn (· == '\n') "newline" <|> eoiFn))) <|> block {ctxt with minIndent := col}) c s
        s.mkNode ``block_role iniSz
  where
    eatSpaces := takeWhileFn (· == ' ')
    intro := guardMinColumn (ctxt.minIndent) >> withCurrentColumn fun c => atomicFn (chFn '{') >> withCurrentColumn fun c' => nameAndArgs (some c') >> nameArgWhitespace (some c)  >> chFn '}'

  partial def linkRef (c : BlockCtxt) : ParserFn :=
    nodeFn ``link_ref <|
      atomicFn (ignoreFn (bol >> eatSpaces >> guardMinColumn c.minIndent) >> chFn '[' >> nodeFn strLitKind (asStringFn (quoted := true) (nameStart >> manyFn (satisfyEscFn (· != ']') "not ']'"))) >> strFn "]:") >>
      eatSpaces >>
      nodeFn strLitKind (asStringFn (quoted := true) (takeWhileFn (· != '\n'))) >>
      ignoreFn (satisfyFn (· == '\n') "newline" <|> eoiFn)
  where nameStart := satisfyEscFn (fun c => c != ']' && c != '^') "not ']' or '^'"

  partial def footnoteRef (c : BlockCtxt) : ParserFn :=
    nodeFn ``footnote_ref <|
      atomicFn (ignoreFn (bol >> eatSpaces >> guardMinColumn c.minIndent) >> strFn "[^" >> nodeFn strLitKind (asStringFn (quoted := true) (many1Fn (satisfyEscFn (· != ']') "not ']'"))) >> strFn "]:") >>
      eatSpaces >>
      notFollowedByFn blockOpener "block opener" >> guardMinColumn c.minIndent >> textLine

  partial def block (c : BlockCtxt) : ParserFn :=
    block_role c <|> unorderedList c <|> orderedList c <|> definitionList c <|> header c <|> codeBlock c <|> directive c <|> blockquote c <|> linkRef c <|> footnoteRef c <|> para c <|> metadataBlock

  partial def blocks (c : BlockCtxt) : ParserFn := sepByFn true (block c) (ignoreFn (manyFn blankLine))

  partial def blocks1 (c : BlockCtxt) : ParserFn := sepBy1Fn true (block c) (ignoreFn (manyFn blankLine))

  partial def document (blockContext : BlockCtxt := {}) : ParserFn := ignoreFn (manyFn blankLine) >> blocks blockContext
end

/--
info: Success! Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text
      (str
       "\"This is just some textual content. How is it?\""))]
    "}")
   (Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text (str "\"More?\""))]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "This is just some textual content. How is it?\n\nMore?"

/--
info: Success! Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text
      (str "\"Newlines are preserved\""))
     (Verso.Syntax.linebreak
      "line!"
      (str "\"\\n\""))
     (Verso.Syntax.text
      (str "\"in paragraphs.\""))]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "Newlines are preserved\nin paragraphs."

/--
info: Success! Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text
      (str
       "\"I can describe lists like this one:\""))]
    "}")
   (Verso.Syntax.ul
    "ul{"
    [(Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"a\""))]
        "}")])
     (Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"b\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "I can describe lists like this one:\n\n* a\n* b"


/--
info: Success! Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.image
      "!["
      (str "\"Lean logo\"")
      "]"
      (Verso.Syntax.url
       "("
       (str "\"/static/lean_logo.svg\"")
       ")"))]
    "}")
   (Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text
      (str
       "\"This is an example website/blog, for testing purposes.\""))]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval document |>.test! "\n![Lean logo](/static/lean_logo.svg)\n\nThis is an example website/blog, for testing purposes."



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
  [(Verso.Syntax.ul
    "ul{"
    [(Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"foo\""))]
        "}")])
     (Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"bar\""))
         (Verso.Syntax.linebreak
          "line!"
          (str "\"\\n\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "* foo\n* bar\n"

/--
info: Success! Final stack:
  [(Verso.Syntax.blockquote
    ">"
    [(Verso.Syntax.ul
      "ul{"
      [(Verso.Syntax.li
        "*"
        [(Verso.Syntax.para
          "para{"
          [(Verso.Syntax.text (str "\"foo\""))]
          "}")])]
      "}")])]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> * foo"

/--
info: Success! Final stack:
  [(Verso.Syntax.blockquote
    ">"
    [(Verso.Syntax.ol
      "ol("
      (num "1")
      ")"
      "{"
      [(Verso.Syntax.li
        "1."
        [(Verso.Syntax.para
          "para{"
          [(Verso.Syntax.text (str "\"foo\""))]
          "}")])]
      "}")])]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> 1. foo"


/--
info: Success! Final stack:
  [(Verso.Syntax.blockquote
    ">"
    [(Verso.Syntax.ul
      "ul{"
      [(Verso.Syntax.li
        "*"
        [(Verso.Syntax.para
          "para{"
          [(Verso.Syntax.text (str "\"foo\""))]
          "}")])]
      "}")
     (Verso.Syntax.ul
      "ul{"
      [(Verso.Syntax.li
        "*"
        [(Verso.Syntax.para
          "para{"
          [(Verso.Syntax.text (str "\"foo\""))]
          "}")])]
      "}")])]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> * foo\n\n\n * foo"

/--
info: Success! Final stack:
  [(Verso.Syntax.blockquote
    ">"
    [(Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text
        (str "\"I like quotes\""))]
      "}")
     (Verso.Syntax.ul
      "ul{"
      [(Verso.Syntax.li
        "*"
        [(Verso.Syntax.para
          "para{"
          [(Verso.Syntax.text
            (str "\"Also with lists in them\""))]
          "}")])]
      "}")])
   (Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text (str "\"Abc\""))]
    "}")]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> I like quotes\n  * Also with lists in them\n\nAbc"

/--
info: Success! Final stack:
  [(Verso.Syntax.blockquote
    ">"
    [(Verso.Syntax.ul
      "ul{"
      [(Verso.Syntax.li
        "*"
        [(Verso.Syntax.para
          "para{"
          [(Verso.Syntax.text (str "\"foo\""))]
          "}")])
       (Verso.Syntax.li
        "*"
        [(Verso.Syntax.para
          "para{"
          [(Verso.Syntax.text (str "\"foo\""))]
          "}")])]
      "}")])]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> * foo\n\n\n  * foo"

/--
info: Success! Final stack:
  [(Verso.Syntax.blockquote
    ">"
    [(Verso.Syntax.blockquote
      ">"
      [(Verso.Syntax.ul
        "ul{"
        [(Verso.Syntax.li
          "*"
          [(Verso.Syntax.para
            "para{"
            [(Verso.Syntax.text (str "\"foo\""))]
            "}")])]
        "}")])
     (Verso.Syntax.ul
      "ul{"
      [(Verso.Syntax.li
        "*"
        [(Verso.Syntax.para
          "para{"
          [(Verso.Syntax.text (str "\"foo\""))]
          "}")])]
      "}")])]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> > * foo\n\n\n * foo"

/--
info: Success! Final stack:
  [(Verso.Syntax.blockquote
    ">"
    [(Verso.Syntax.ul
      "ul{"
      [(Verso.Syntax.li
        "*"
        [(Verso.Syntax.para
          "para{"
          [(Verso.Syntax.text (str "\"foo\""))]
          "}")])]
      "}")])
   (Verso.Syntax.ul
    "ul{"
    [(Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"foo\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> * foo\n\n\n* foo"

/--
info: Success! Final stack:
  [(Verso.Syntax.ul
    "ul{"
    [(Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"foo\""))
         (Verso.Syntax.linebreak
          "line!"
          (str "\"\\n\""))
         (Verso.Syntax.text (str "\"  thing\""))]
        "}")])]
    "}")]
Remaining:
"* bar\n"
-/
#guard_msgs in
  #eval blocks {} |>.test! "* foo\n  thing* bar\n"

/--
info: Success! Final stack:
  [(Verso.Syntax.ul
    "ul{"
    [(Verso.Syntax.li
      "+"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"foo\""))]
        "}")])
     (Verso.Syntax.li
      "+"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"bar\""))
         (Verso.Syntax.linebreak
          "line!"
          (str "\"\\n\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "+ foo\n+ bar\n"


/--
info: Success! Final stack:
  [(Verso.Syntax.ul
    "ul{"
    [(Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"foo\""))]
        "}")])
     (Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"bar\""))
         (Verso.Syntax.linebreak
          "line!"
          (str "\"\\n\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "* foo\n\n* bar\n"

/--
info: Success! Final stack:
  [(Verso.Syntax.ul
    "ul{"
    [(Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"foo\""))
         (Verso.Syntax.linebreak
          "line!"
          (str "\"\\n\""))
         (Verso.Syntax.text (str "\"  stuff\""))]
        "}")
       (Verso.Syntax.blockquote
        ">"
        [(Verso.Syntax.para
          "para{"
          [(Verso.Syntax.text (str "\"more \""))]
          "}")])
       (Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"abc\""))]
        "}")])
     (Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"bar\""))
         (Verso.Syntax.linebreak
          "line!"
          (str "\"\\n\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "* foo\n  stuff\n\n > more \n\n abc\n\n\n* bar\n"

/--
info: Success! Final stack:
  [(Verso.Syntax.ul
    "ul{"
    [(Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"foo\""))]
        "}")
       (Verso.Syntax.ul
        "ul{"
        [(Verso.Syntax.li
          "*"
          [(Verso.Syntax.para
            "para{"
            [(Verso.Syntax.text (str "\"bar\""))]
            "}")])]
        "}")])
     (Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text
          (str "\"more outer\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "* foo\n  * bar\n* more outer"

/--
info: Failure @35 (⟨2, 15⟩): unexpected end of input; expected %%% (at line beginning), '![', '$$', '$', '[', '[^', beginning of line at ⟨2, 15⟩ or beginning of line or sequence of nestable block openers at ⟨2, 15⟩
Final stack:
  [(Verso.Syntax.dl
    "ul{"
    [(Verso.Syntax.desc
      ":"
      [(Verso.Syntax.text
        (str "\" an excellent idea\""))
       (Verso.Syntax.linebreak
        "line!"
        (str "\"\\n\""))
       (Verso.Syntax.text
        (str "\"Let's say more!\""))]
      "=>"
      [(Verso.Syntax.metadata_block <missing>)
       <missing>])]
    "}")]
Remaining: ""
-/
#guard_msgs in
  #eval blocks {} |>.test! ": an excellent idea\nLet's say more!"

/--
info: Success! Final stack:
  [(Verso.Syntax.dl
    "ul{"
    [(Verso.Syntax.desc
      ":"
      [(Verso.Syntax.text
        (str "\" an excellent idea\""))]
      "=>"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text
          (str "\"Let's say more!\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! ": an excellent idea\n\n    Let's say more!"

/--
info: Failure @47 (⟨7, 0⟩): expected indentation at least 1
Final stack:
  [(Verso.Syntax.dl
    "ul{"
    [(Verso.Syntax.desc
      ":"
      [(Verso.Syntax.text
        (str "\" an excellent idea\""))]
      "=>"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text
          (str "\"Let's say more!\""))]
        "}")])
     (Verso.Syntax.desc
      ":"
      [(Verso.Syntax.text (str "\" more\""))]
      "=>"
      <missing>)]
    "}")]
Remaining: ""
-/
#guard_msgs in
  #eval blocks {} |>.test! ": an excellent idea\n\n Let's say more!\n\n: more\n\n"

/--
info: Success! Final stack:
  [(Verso.Syntax.dl
    "ul{"
    [(Verso.Syntax.desc
      ":"
      [(Verso.Syntax.text
        (str "\" an excellent idea\""))]
      "=>"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text
          (str "\"Let's say more!\""))]
        "}")])
     (Verso.Syntax.desc
      ":"
      [(Verso.Syntax.text (str "\" more\""))]
      "=>"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text
          (str "\"even more!\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! ": an excellent idea\n\n Let's say more!\n\n\n\n\n: more\n\n even more!"


/--
info: Success! Final stack:
  [(Verso.Syntax.dl
    "ul{"
    [(Verso.Syntax.desc
      ":"
      [(Verso.Syntax.text
        (str "\" an excellent idea\""))]
      "=>"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text
          (str "\"Let's say more!\""))]
        "}")])
     (Verso.Syntax.desc
      ":"
      [(Verso.Syntax.text (str "\" more\""))]
      "=>"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"stuff\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! ": an excellent idea\n\n Let's say more!\n\n: more\n\n stuff"

/--
info: Failure @21 (⟨3, 0⟩): expected indentation at least 1
Final stack:
  [(Verso.Syntax.dl
    "ul{"
    [(Verso.Syntax.desc
      ":"
      [(Verso.Syntax.text
        (str "\" an excellent idea\""))]
      "=>"
      <missing>)]
    "}")
   (Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text
      (str "\"Let's say more!\""))]
    "}")
   (Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text (str "\"hello\""))]
    "}")]
Remaining: "Let's say more!\n\nhello"
-/
#guard_msgs in
  #eval blocks {} |>.test! ": an excellent idea\n\nLet's say more!\n\nhello"

/--
info: Success! Final stack:
  [(Verso.Syntax.ol
    "ol("
    (num "1")
    ")"
    "{"
    [(Verso.Syntax.li
      "1."
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"Hello\""))]
        "}")])
     (Verso.Syntax.li
      "2."
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"World\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
 #eval blocks {} |>.test! "1. Hello\n\n2. World"

/--
info: Success! Final stack:
  [(Verso.Syntax.ol
    "ol("
    (num "1")
    ")"
    "{"
    [(Verso.Syntax.li
      "1."
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"Hello\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
 #eval blocks {} |>.test! " 1. Hello"

/--
info: Success! Final stack:
  [(Verso.Syntax.ol
    "ol("
    (num "1")
    ")"
    "{"
    [(Verso.Syntax.li
      "1."
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"Hello\""))]
        "}")])]
    "}")
   (Verso.Syntax.ol
    "ol("
    (num "2")
    ")"
    "{"
    [(Verso.Syntax.li
      "2."
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"World\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
 #eval blocks {} |>.test! "1. Hello\n\n 2. World"

/--
info: Success! Final stack:
  [(Verso.Syntax.ol
    "ol("
    (num "1")
    ")"
    "{"
    [(Verso.Syntax.li
      "1."
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"Hello\""))]
        "}")])
     (Verso.Syntax.li
      "2."
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"World\""))]
        "}")])]
    "}")]
All input consumed.
-/
#guard_msgs in
 #eval blocks {} |>.test! " 1. Hello\n\n 2. World"

/--
info: Success! Final stack:
  [(Verso.Syntax.blockquote
    ">"
    [(Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text (str "\"hey\""))
       (Verso.Syntax.linebreak
        "line!"
        (str "\"\\n\""))]
      "}")])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "> hey\n"

/--
info: Success! Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text (str "\"n*k \""))]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "n\\*k "

-- Unlike Djot, we don't have precedence - these must be well-nested
/--
info: Failure @16 (⟨1, 16⟩): '_'
Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.bold
      "*"
      [(Verso.Syntax.text (str "\"This is \""))
       (Verso.Syntax.emph
        "_"
        [(Verso.Syntax.text (str "\"strong\""))]
        <missing>)]
      "*")
     (Verso.Syntax.text (str "\" not regular\""))]
    "}")]
Remaining: "* not regular_ emphasis"
-/
#guard_msgs in
  #eval blocks {} |>.test! "*This is _strong* not regular_ emphasis"


/--
info: Success! Final stack:
  (Verso.Syntax.header
   "header("
   (num "0")
   ")"
   "{"
   [(Verso.Syntax.text (str "\"Header!\""))]
   "}")
All input consumed.
-/
#guard_msgs in
  #eval header {} |>.test! "# Header!"

/--
info: Success! Final stack:
  [(Verso.Syntax.header
    "header("
    (num "0")
    ")"
    "{"
    [(Verso.Syntax.text (str "\"Header!\""))]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "# Header!\n"

/--
info: Success! Final stack:
  [(Verso.Syntax.header
    "header("
    (num "1")
    ")"
    "{"
    [(Verso.Syntax.text (str "\"Header!\""))]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "## Header!\n"

/--
info: Success! Final stack:
  [(Verso.Syntax.blockquote
    ">"
    [(Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text (str "\"Quotation\""))
       (Verso.Syntax.linebreak
        "line!"
        (str "\"\\n\""))
       (Verso.Syntax.text
        (str "\"and contained\""))]
      "}")])]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> Quotation\nand contained"

/--
info: Failure @54 (⟨3, 42⟩): expected '`' to close inline code
Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text (str "\"Attention:\""))]
    "}")
   (Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text
      (str
       "\"Here is a paragraph with an unterminated \""))
     (Verso.Syntax.code "`" <missing> <missing>)
     (Verso.Syntax.text (str "\"code block\""))
     (Verso.Syntax.linebreak
      "line!"
      (str "\"\\n\""))
     (Verso.Syntax.text
      (str
       "\"that would be super annoying without error recovery in the\""))
     (Verso.Syntax.linebreak
      "line!"
      (str "\"\\n\""))
     (Verso.Syntax.text (str "\"parser.\""))]
    "}")
   (Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text (str "\"Yep.\""))]
    "}")]
Remaining: "code block\nthat would be super annoying without error recovery in the\nparser.\n\nYep."
-/
#guard_msgs in
#eval blocks {} |>.test!
  "Attention:

Here is a paragraph with an unterminated `code block
that would be super annoying without error recovery in the
parser.

Yep."

/--
info: 3 failures:
  @73 (⟨9, 3⟩): expected directive name (identifier)
    "\n"
  @74 (⟨10, 0⟩): expected closing ':::' for directive from line 9
    ""
  @74 (⟨10, 0⟩): expected closing '::::' for directive from line 3
    ""

Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text
      (str
       "\"Here's some error recovery for directives.\""))]
    "}")
   (Verso.Syntax.directive
    "::::"
    `foo
    []
    "\n"
    [(Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text (str "\"Indeed.\""))]
      "}")
     (Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text (str "\"It is.\""))]
      "}")
     (Verso.Syntax.directive
      ":::"
      <missing>
      []
      "\n"
      []
      <missing>)]
    <missing>)]
-/
#guard_msgs in
#eval blocks {} |>.test!
  "Here's some error recovery for directives.

::::foo

Indeed.

It is.

:::
"

/--
info: 3 failures:
  @68 (⟨8, 0⟩): expected closing ':::' from directive on line 3 at column 0, but it's at column 1
    " :::\n"
  @72 (⟨8, 4⟩): expected directive name (identifier)
    "\n"
  @73 (⟨9, 0⟩): expected closing ':::' for directive from line 8
    ""

Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text
      (str
       "\"Here's some error recovery for directives.\""))]
    "}")
   (Verso.Syntax.directive
    ":::"
    `foo
    []
    "\n"
    [(Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text (str "\"Indeed.\""))]
      "}")
     (Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text (str "\"It is.\""))]
      "}")]
    <missing>)
   (Verso.Syntax.directive
    ":::"
    <missing>
    []
    "\n"
    []
    <missing>)]
-/
#guard_msgs in
#eval blocks {} |>.test!
  "Here's some error recovery for directives.

:::foo

Indeed.

It is.
 :::
"

/--
info: 2 failures:
  @71 (⟨8, 0⟩): expected closing '::::' for directive from line 3
    ":::: a\n\nx\n"
  @81 (⟨11, 0⟩): expected closing '::::' for directive from line 8
    ""

Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text
      (str
       "\"Here's some error recovery for directives.\""))]
    "}")
   (Verso.Syntax.directive
    "::::"
    `foo
    [(Verso.Syntax.anon
      (Verso.Syntax.arg_num (num "5")))]
    "\n"
    [(Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text (str "\"Indeed.\""))]
      "}")
     (Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text (str "\"It is.\""))]
      "}")]
    <missing>)
   (Verso.Syntax.directive
    "::::"
    `a
    []
    "\n"
    [(Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text (str "\"x\""))
       (Verso.Syntax.linebreak
        "line!"
        (str "\"\\n\""))]
      "}")]
    <missing>)]
-/
#guard_msgs in
#eval blocks {} |>.test!
  "Here's some error recovery for directives.

::::foo 5

Indeed.

It is.
:::: a

x
"

/--
info: Success! Final stack:
  [(Verso.Syntax.blockquote
    ">"
    [(Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text (str "\"Quotation\""))]
      "}")
     (Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text
        (str "\"and contained\""))]
      "}")])]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> Quotation\n\n and contained"

/--
info: Success! Final stack:
  [(Verso.Syntax.blockquote
    ">"
    [(Verso.Syntax.para
      "para{"
      [(Verso.Syntax.text (str "\"Quotation\""))]
      "}")])
   (Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text
      (str "\"and not contained\""))]
    "}")]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> Quotation\n\nand not contained"



/--
info: Success! Final stack:
  (Verso.Syntax.codeblock
   "```"
   [`scheme []]
   "\n"
   (str "\"(define x 4)\\nx\\n\"")
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ``` scheme\n (define x 4)\n x\n ```"

/--
info: Success! Final stack:
  (Verso.Syntax.codeblock
   "```"
   [`scheme []]
   "\n"
   (str "\" (define x 4)\\n x\\n\"")
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme\n (define x 4)\n x\n```"


/--
info: Success! Final stack:
  (Verso.Syntax.codeblock
   "```"
   []
   "\n"
   (str "\"(define x 4)\\nx\\n\"")
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ``` \n (define x 4)\n x\n ```"

/--
info: Success! Final stack:
  (Verso.Syntax.codeblock
   "```"
   []
   "\n"
   (str "\"(define x 4)\\nx\\n\"")
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ```\n (define x 4)\n x\n ```"


/--
info: Success! Final stack:
  (Verso.Syntax.codeblock
   "```"
   [`scheme []]
   "\n"
   (str "\" (define x 4)\\n x\\n\"")
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme\n (define x 4)\n x\n```\n"

/--
info: Success! Final stack:
  (Verso.Syntax.codeblock
   "```"
   [`scheme []]
   "\n"
   (str "\"(define x 4)\\nx\\n\"")
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme\n(define x 4)\nx\n```"


/--
info: Failure @32 (⟨5, 0⟩): expected column 0
Final stack:
  (Verso.Syntax.codeblock
   "```"
   [`scheme []]
   "\n"
   (str "\"(define x 4)\\nx\\n\"")
   <missing>)
Remaining: "more"
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme\n(define x 4)\nx\n ````\nmore"

/--
info: Success! Final stack:
  (Verso.Syntax.codeblock
   "```"
   [`scheme
    [(Verso.Syntax.named
      `dialect
      ":="
      (Verso.Syntax.arg_str (str "\"chicken\"")))
     (Verso.Syntax.anon
      (Verso.Syntax.arg_num (num "43")))]]
   "\n"
   (str "\"(define x 4)\\nx\\n\"")
   "```")
All input consumed.
-/
#guard_msgs in
#eval codeBlock {} |>.test!
"``` scheme dialect:=\"chicken\" 43
(define x 4)
x
```"

/--
info: Success! Final stack:
  (Verso.Syntax.codeblock
   "```"
   [`scheme
    [(Verso.Syntax.named
      `dialect
      ":="
      (Verso.Syntax.arg_str
       (str "\"chicken\"")))]]
   "\n"
   (str "\"(define x 4)\\nx\\n\"")
   "```")
All input consumed.
-/
#guard_msgs in
#eval codeBlock {} |>.test!
"``` scheme (dialect:=\"chicken\")
(define x 4)
x
```"

/--
info: Failure @30 (⟨1, 30⟩): expected ')'
Final stack:
  (Verso.Syntax.codeblock
   "```"
   [`scheme
    [(Verso.Syntax.named
      `dialect
      ":="
      (Verso.Syntax.arg_str
       (str "\"chicken\"")))]]
   "\n"
   (str "\"(define x 4)\\nx\\n\"")
   "```")
Remaining: "\n(define x 4)\nx\n```"
-/
#guard_msgs in
#eval codeBlock {} |>.test!
"``` scheme (dialect:=\"chicken\"
(define x 4)
x
```"

/--
info: Failure @25 (⟨3, 0⟩): expected column 1
Final stack:
  (Verso.Syntax.codeblock
   "```"
   [`scheme []]
   "\n"
   (str "\"\\n\"")
   <missing>)
Remaining: "x\n```"
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ``` scheme\n(define x 4)\nx\n```"

/--
info: Failure @32 (⟨4, 3⟩): expected column 1
Final stack:
  (Verso.Syntax.codeblock
   "```"
   [`scheme []]
   "\n"
   (str "\"(define x 4)\\nx\\n\"")
   <missing>)
Remaining: ""
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ``` scheme\n (define x 4)\n x\n```"

/--
info: Failure @25 (⟨4, 3⟩): expected column 1
Final stack:
  (Verso.Syntax.codeblock
   "```"
   []
   "\n"
   (str "\"(define x 4)\\nx\\n\"")
   <missing>)
Remaining: ""
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ```\n (define x 4)\n x\n```"

/--
info: Failure @28 (⟨4, 3⟩): expected column 1
Final stack:
  (Verso.Syntax.codeblock
   "```"
   []
   "\n"
   (str "\"(define x 4)\\nx\\n\"")
   <missing>)
Remaining: ""
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ```   \n (define x 4)\n x\n```"

/--
info: Success! Final stack:
  (Verso.Syntax.ul
   "ul{"
   [(Verso.Syntax.li
     "*"
     [(Verso.Syntax.para
       "para{"
       [(Verso.Syntax.text
         (str "\"Here's a bullet\""))]
       "}")])
    (Verso.Syntax.li
     "*"
     [(Verso.Syntax.para
       "para{"
       [(Verso.Syntax.text
         (str
          "\"and another with some code in it\""))]
       "}")
      (Verso.Syntax.codeblock
       "````"
       [`lean []]
       "\n"
       (str "\"hey\\n\\nthere\\n\"")
       "````")])
    (Verso.Syntax.li
     "*"
     [(Verso.Syntax.para
       "para{"
       [(Verso.Syntax.text
         (str "\"and another one\""))
        (Verso.Syntax.linebreak
         "line!"
         (str "\"\\n\""))]
       "}")])]
   "}")
All input consumed.
-/
#guard_msgs in
#eval block {} |>.test!
  " * Here's a bullet
 * and another with some code in it
    ````lean
    hey

    there
    ````
 * and another one
"

/--
info: Success! Final stack:
  (Verso.Syntax.ul
   "ul{"
   [(Verso.Syntax.li
     "*"
     [(Verso.Syntax.para
       "para{"
       [(Verso.Syntax.code
         "`"
         (str "\"structure\"")
         "`")
        (Verso.Syntax.text (str "\" and \""))
        (Verso.Syntax.code
         "`"
         (str "\"inductive\"")
         "`")
        (Verso.Syntax.text (str "\" commands\""))]
       "}")
      (Verso.Syntax.ul
       "ul{"
       [(Verso.Syntax.li
         "*"
         [(Verso.Syntax.para
           "para{"
           [(Verso.Syntax.link
             "["
             [(Verso.Syntax.text
               (str "\"#5842\""))]
             "]"
             (Verso.Syntax.url
              "("
              (str
               "\"https://github.com/leanprover/lean4/pull/5842\"")
              ")"))
            (Verso.Syntax.text (str "\" and \""))
            (Verso.Syntax.link
             "["
             [(Verso.Syntax.text
               (str "\"#5783\""))]
             "]"
             (Verso.Syntax.url
              "("
              (str
               "\"https://github.com/leanprover/lean4/pull/5783\"")
              ")"))
            (Verso.Syntax.text
             (str
              "\" implement a feature where the \""))
            (Verso.Syntax.code
             "`"
             (str "\"structure\"")
             "`")
            (Verso.Syntax.text
             (str
              "\" command can now define recursive inductive types:\""))]
           "}")
          (Verso.Syntax.codeblock
           "```"
           [`lean []]
           "\n"
           (str
            "\"structure Tree where\\n  n : Nat\\n  children : Fin n → Tree\\n\\ndef Tree.size : Tree → Nat\\n  | {n, children} => Id.run do\\n    let mut s := 0\\n    for h : i in [0 : n] do\\n      s := s + (children ⟨i, h.2⟩).size\\n    pure s\\n\"")
           "```")])
        (Verso.Syntax.li
         "*"
         [(Verso.Syntax.para
           "para{"
           [(Verso.Syntax.link
             "["
             [(Verso.Syntax.text
               (str "\"#5814\""))]
             "]"
             (Verso.Syntax.url
              "("
              (str
               "\"https://github.com/leanprover/lean4/pull/5814\"")
              ")"))
            (Verso.Syntax.text (str "\" \""))]
           "}")])]
       "}")])]
   "}")
All input consumed.
-/
#guard_msgs in
#eval block {} |>.test!
r##"* `structure` and `inductive` commands
  * [#5842](https://github.com/leanprover/lean4/pull/5842) and [#5783](https://github.com/leanprover/lean4/pull/5783) implement a feature where the `structure` command can now define recursive inductive types:
    ```lean
    structure Tree where
      n : Nat
      children : Fin n → Tree

    def Tree.size : Tree → Nat
      | {n, children} => Id.run do
        let mut s := 0
        for h : i in [0 : n] do
          s := s + (children ⟨i, h.2⟩).size
        pure s
    ```
  * [#5814](https://github.com/leanprover/lean4/pull/5814) "##

/--
info: Success! Final stack:
  (Verso.Syntax.block_role
   "{"
   `test
   []
   "}"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text
       (str "\"Here's a modified paragraph.\""))]
     "}")])
All input consumed.
-/
#guard_msgs in
#eval block {} |>.test! "{test}\nHere's a modified paragraph."
/--
info: Success! Final stack:
  (Verso.Syntax.block_role
   "{"
   `test
   []
   "}"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text
       (str "\"Here's a modified paragraph.\""))]
     "}")])
All input consumed.
-/
#guard_msgs in
#eval block {} |>.test! "{test}\n Here's a modified paragraph."
/--
info: Success! Final stack:
  (Verso.Syntax.block_role
   "{"
   `test
   []
   "}"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text
       (str "\"Here's a modified paragraph.\""))]
     "}")])
All input consumed.
-/
#guard_msgs in
#eval block {} |>.test! " {test}\n Here's a modified paragraph."
/--
info: Failure @8 (⟨2, 0⟩): ':'; expected %%% (at line beginning), expected column at least 1 or expected end of file
Final stack:
  (Verso.Syntax.block_role
   "{"
   `test
   []
   "}"
   [(Verso.Syntax.metadata_block
     <missing>
     <missing>)])
Remaining: "Here's a modified paragraph."
-/
#guard_msgs in
#eval block {} |>.test! " {test}\nHere's a modified paragraph."

/--
info: Success! Final stack:
  (Verso.Syntax.block_role
   "{"
   `test
   []
   "}"
   [(Verso.Syntax.blockquote
     ">"
     [(Verso.Syntax.para
       "para{"
       [(Verso.Syntax.text
         (str
          "\"Here's a modified blockquote\""))]
       "}")
      (Verso.Syntax.para
       "para{"
       [(Verso.Syntax.text
         (str "\"with multiple paras\""))]
       "}")])])
Remaining:
"that ends"
-/
#guard_msgs in
#eval block {} |>.test! "{test}\n> Here's a modified blockquote\n\n with multiple paras\n\nthat ends"

/--
info: 2 failures:
  @36 (⟨3, 28⟩): expected identifier
    ""
  @36 (⟨3, 28⟩): unexpected end of input; expected '![', '$$', '$', '[' or '[^'
    ""

Final stack:
  (Verso.Syntax.para
   "para{"
   [(Verso.Syntax.role
     "{"
     <missing>
     "["
     [(Verso.Syntax.footnote <missing>)]
     "]")])
-/
#guard_msgs in
#eval block {} |>.test! "{\ntest}\nHere's a modified paragraph."

/--
info: Success! Final stack:
  (Verso.Syntax.block_role
   "{"
   `test
   []
   "}"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text
       (str "\"Here's a modified paragraph.\""))]
     "}")])
All input consumed.
-/
#guard_msgs in
#eval block {} |>.test! "{\n test}\nHere's a modified paragraph."

/--
info: 2 failures:
  @44 (⟨4, 28⟩): expected identifier
    ""
  @44 (⟨4, 28⟩): unexpected end of input; expected '![', '$$', '$', '[' or '[^'
    ""

Final stack:
  (Verso.Syntax.para
   "para{"
   [(Verso.Syntax.role
     "{"
     <missing>
     "["
     [(Verso.Syntax.footnote <missing>)]
     "]")])
-/
#guard_msgs in
#eval block {} |>.test! "{\n    test\narg}\nHere's a modified paragraph."

/--
info: Success! Final stack:
  (Verso.Syntax.block_role
   "{"
   `test
   [(Verso.Syntax.anon
     (Verso.Syntax.arg_ident `arg))]
   "}"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text
       (str "\"Here's a modified paragraph.\""))]
     "}")])
All input consumed.
-/
#guard_msgs in
#eval block {} |>.test! "{\n    test\n arg}\nHere's a modified paragraph."
/--
info: Success! Final stack:
  (Verso.Syntax.block_role
   "{"
   `test
   [(Verso.Syntax.anon
     (Verso.Syntax.arg_ident `arg))]
   "}"
   [])
Remaining:
"\nHere's a non-modified paragraph."
-/
#guard_msgs in
#eval block {} |>.test! "{\n    test\n arg}\n\n\nHere's a non-modified paragraph."

/--
info: Success! Final stack:
  [(Verso.Syntax.metadata_block
    "%%%"
    (Term.structInstFields
     [(Term.structInstField
       (Term.structInstLVal `foo [])
       [[]
        []
        (Term.structInstFieldDef
         ":="
         (num "53"))])
      []])
    "%%%")
   (Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text
      (str "\"Text/paragraph!\""))]
    "}")]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "%%%\nfoo := 53\n%%%\nText/paragraph!"

/--
info: Success! Final stack:
  (Verso.Syntax.directive
   "::::"
   `multiPara
   []
   "\n"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text (str "\"foo\""))]
     "}")]
   "::::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! ":::: multiPara\nfoo\n::::"

/--
info: Success! Final stack:
  (Verso.Syntax.directive
   "::::"
   `multiPara
   []
   "\n"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text (str "\"foo\""))]
     "}")]
   "::::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! ":::: multiPara\n\n\nfoo\n::::"

/--
info: Success! Final stack:
  (Verso.Syntax.directive
   ":::"
   `multiPara
   [(Verso.Syntax.named
     `greatness
     ":="
     (Verso.Syntax.arg_str (str "\"amazing!\"")))]
   "\n"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text (str "\"foo\""))]
     "}")]
   ":::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! " ::: multiPara greatness:=\"amazing!\"\n foo\n :::"


/--
info: Success! Final stack:
  (Verso.Syntax.directive
   ":::"
   `multiPara
   []
   "\n"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text (str "\"foo\""))]
     "}")
    (Verso.Syntax.ul
     "ul{"
     [(Verso.Syntax.li
       "*"
       [(Verso.Syntax.para
         "para{"
         [(Verso.Syntax.text
           (str "\"List item \""))]
         "}")])]
     "}")]
   ":::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! " ::: multiPara\n foo\n \n \n \n  * List item \n :::"

/--
info: Success! Final stack:
  (Verso.Syntax.directive
   ":::"
   `multiPara
   [(Verso.Syntax.anon
     (Verso.Syntax.arg_ident `thing))]
   "\n"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text (str "\"foo\""))]
     "}")
    (Verso.Syntax.ul
     "ul{"
     [(Verso.Syntax.li
       "*"
       [(Verso.Syntax.para
         "para{"
         [(Verso.Syntax.text
           (str "\"List item \""))]
         "}")])]
     "}")]
   ":::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! " ::: multiPara thing\n foo\n \n \n \n  * List item \n :::"

/--
info: Success! Final stack:
  (Verso.Syntax.directive
   ":::"
   `multiPara
   []
   "\n"
   [(Verso.Syntax.para
     "para{"
     [(Verso.Syntax.text (str "\"foo\""))]
     "}")
    (Verso.Syntax.ul
     "ul{"
     [(Verso.Syntax.li
       "*"
       [(Verso.Syntax.para
         "para{"
         [(Verso.Syntax.text
           (str "\"List item \""))]
         "}")])]
     "}")]
   ":::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! " ::: multiPara\n foo\n\n * List item \n :::"

/--
info: Success! Final stack:
  (Verso.Syntax.text (str "\" \""))
Remaining:
"[\\[link\\]](https://link.com)"
-/
#guard_msgs in
  #eval text |>.test! " [\\[link\\]](https://link.com)"

/--
info: Success! Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.link
      "["
      [(Verso.Syntax.text (str "\"[link A]\""))]
      "]"
      (Verso.Syntax.url
       "("
       (str "\"https://example.com\"")
       ")"))
     (Verso.Syntax.text (str "\" \""))
     (Verso.Syntax.link
      "["
      [(Verso.Syntax.text (str "\"[link B]\""))]
      "]"
      (Verso.Syntax.url
       "("
       (str "\"https://more.example.com\"")
       ")"))]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "[\\[link A\\]](https://example.com) [\\[link B\\]](https://more.example.com)"


/--
info: Success! Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.link
      "["
      [(Verso.Syntax.text (str "\"My link\""))]
      "]"
      (Verso.Syntax.ref
       "["
       (str "\"lean\"")
       "]"))]
    "}")
   (Verso.Syntax.link_ref
    "["
    (str "\"lean\"")
    "]:"
    (str "\"https://lean-lang.org\""))]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "[My link][lean]\n\n[lean]: https://lean-lang.org"

/--
info: Failure @45 (⟨2, 29⟩): expected '(' or '['
Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.link
      "["
      [(Verso.Syntax.text (str "\"My link\""))]
      "]"
      (Verso.Syntax.ref "[" (str "\"lean\"") "]"))
     (Verso.Syntax.linebreak
      "line!"
      (str "\"\\n\""))
     (Verso.Syntax.link
      "["
      [(Verso.Syntax.text (str "\"lean\""))]
      "]"
      (Verso.Syntax.url <missing>))]
    "}")]
Remaining: ""
-/
#guard_msgs in
  #eval blocks {} |>.test! "[My link][lean]\n[lean]: https://lean-lang.org"

/--
info: Success! Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.link
      "["
      [(Verso.Syntax.text (str "\"My link\""))]
      "]"
      (Verso.Syntax.ref
       "["
       (str "\"lean\"")
       "]"))]
    "}")
   (Verso.Syntax.link_ref
    "["
    (str "\"lean\"")
    "]:"
    (str "\"https://lean-lang.org\""))
   (Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text (str "\"hello\""))]
    "}")]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "[My link][lean]\n\n[lean]: https://lean-lang.org\nhello"

/--
info: Success! Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text (str "\"Blah blah\""))
     (Verso.Syntax.footnote
      "[^"
      (str "\"1\"")
      "]")]
    "}")
   (Verso.Syntax.footnote_ref
    "[^"
    (str "\"1\"")
    "]:"
    [(Verso.Syntax.text
      (str "\"More can be said\""))])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "Blah blah[^1]\n\n[^1]: More can be said"


-- A big test of error recovery

/--
info: 10 failures:
  @38 (⟨4, 14⟩): expected ']'
    "\n\n* [busted\n   link\n\n* [busted\n   _italics\n   link\n\n\n* [busted destination](hey\n\n* ![busted image alt text\n\n* ![busted image link](image.png\n\n* a *bold choice\n\n* very _italic *and bold, onto many\n   lines is OK* but don't forget...\n\na paragraph with [a bad link syntax](http://example.com\nis OK. The rest *works*.\n"
  @57 (⟨7, 7⟩): expected ']'
    "\n\n* [busted\n   _italics\n   link\n\n\n* [busted destination](hey\n\n* ![busted image alt text\n\n* ![busted image link](image.png\n\n* a *bold choice\n\n* very _italic *and bold, onto many\n   lines is OK* but don't forget...\n\na paragraph with [a bad link syntax](http://example.com\nis OK. The rest *works*.\n"
  @88 (⟨11, 7⟩): '_'
    "\n\n\n* [busted destination](hey\n\n* ![busted image alt text\n\n* ![busted image link](image.png\n\n* a *bold choice\n\n* very _italic *and bold, onto many\n   lines is OK* but don't forget...\n\na paragraph with [a bad link syntax](http://example.com\nis OK. The rest *works*.\n"
  @88 (⟨11, 7⟩): expected ']'
    "\n\n\n* [busted destination](hey\n\n* ![busted image alt text\n\n* ![busted image link](image.png\n\n* a *bold choice\n\n* very _italic *and bold, onto many\n   lines is OK* but don't forget...\n\na paragraph with [a bad link syntax](http://example.com\nis OK. The rest *works*.\n"
  @117 (⟨14, 26⟩): expected ')'
    "\n\n* ![busted image alt text\n\n* ![busted image link](image.png\n\n* a *bold choice\n\n* very _italic *and bold, onto many\n   lines is OK* but don't forget...\n\na paragraph with [a bad link syntax](http://example.com\nis OK. The rest *works*.\n"
  @144 (⟨16, 25⟩): expected ']'
    "\n\n* ![busted image link](image.png\n\n* a *bold choice\n\n* very _italic *and bold, onto many\n   lines is OK* but don't forget...\n\na paragraph with [a bad link syntax](http://example.com\nis OK. The rest *works*.\n"
  @178 (⟨18, 32⟩): expected ')'
    "\n\n* a *bold choice\n\n* very _italic *and bold, onto many\n   lines is OK* but don't forget...\n\na paragraph with [a bad link syntax](http://example.com\nis OK. The rest *works*.\n"
  @196 (⟨20, 16⟩): '*'
    "\n\n* very _italic *and bold, onto many\n   lines is OK* but don't forget...\n\na paragraph with [a bad link syntax](http://example.com\nis OK. The rest *works*.\n"
  @269 (⟨23, 35⟩): '_'
    "\n\na paragraph with [a bad link syntax](http://example.com\nis OK. The rest *works*.\n"
  @326 (⟨25, 55⟩): expected ')'
    "\nis OK. The rest *works*.\n"

Final stack:
  [(Verso.Syntax.para
    "para{"
    [(Verso.Syntax.linebreak
      "line!"
      (str "\"\\n\""))
     (Verso.Syntax.text
      (str "\"Error recovery tests:\""))]
    "}")
   (Verso.Syntax.ul
    "ul{"
    [(Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.link
          "["
          [(Verso.Syntax.text
            (str "\"busted link\""))]
          <missing>)]
        "}")])
     (Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.link
          "["
          [(Verso.Syntax.text (str "\"busted\""))
           (Verso.Syntax.linebreak
            "line!"
            (str "\"\\n\""))
           (Verso.Syntax.text
            (str "\"   link\""))]
          <missing>)]
        "}")])
     (Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.link
          "["
          [(Verso.Syntax.text (str "\"busted\""))
           (Verso.Syntax.linebreak
            "line!"
            (str "\"\\n\""))
           (Verso.Syntax.text (str "\"   \""))
           (Verso.Syntax.emph
            "_"
            [(Verso.Syntax.text
              (str "\"italics\""))
             (Verso.Syntax.linebreak
              "line!"
              (str "\"\\n\""))
             (Verso.Syntax.text
              (str "\"   link\""))]
            <missing>)]
          <missing>)]
        "}")])
     (Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.link
          "["
          [(Verso.Syntax.text
            (str "\"busted destination\""))]
          "]"
          (Verso.Syntax.url
           "("
           (str "\"hey\"")
           <missing>))]
        "}")])
     (Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.image
          "!["
          (str "\"busted image alt text\"")
          <missing>)]
        "}")])
     (Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.image
          "!["
          (str "\"busted image link\"")
          "]"
          (Verso.Syntax.url
           "("
           (str "\"image.png\"")
           <missing>))]
        "}")])
     (Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"a \""))
         (Verso.Syntax.bold
          "*"
          [(Verso.Syntax.text
            (str "\"bold choice\""))]
          <missing>)]
        "}")])
     (Verso.Syntax.li
      "*"
      [(Verso.Syntax.para
        "para{"
        [(Verso.Syntax.text (str "\"very \""))
         (Verso.Syntax.emph
          "_"
          [(Verso.Syntax.text (str "\"italic \""))
           (Verso.Syntax.bold
            "*"
            [(Verso.Syntax.text
              (str "\"and bold, onto many\""))
             (Verso.Syntax.linebreak
              "line!"
              (str "\"\\n\""))
             (Verso.Syntax.text
              (str "\"   lines is OK\""))]
            "*")
           (Verso.Syntax.text
            (str "\" but don't forget...\""))]
          <missing>)]
        "}")])]
    "}")
   (Verso.Syntax.para
    "para{"
    [(Verso.Syntax.text
      (str "\"a paragraph with \""))
     (Verso.Syntax.link
      "["
      [(Verso.Syntax.text
        (str "\"a bad link syntax\""))]
      "]"
      (Verso.Syntax.url
       "("
       (str "\"http://example.com\"")
       <missing>))
     (Verso.Syntax.linebreak
      "line!"
      (str "\"\\n\""))
     (Verso.Syntax.text
      (str "\"is OK. The rest \""))
     (Verso.Syntax.bold
      "*"
      [(Verso.Syntax.text (str "\"works\""))]
      "*")
     (Verso.Syntax.text (str "\".\""))
     (Verso.Syntax.linebreak
      "line!"
      (str "\"\\n\""))]
    "}")]
-/
#guard_msgs in
#eval blocks {} |>.test!
r#"
Error recovery tests:

* [busted link

* [busted
   link

* [busted
   _italics
   link


* [busted destination](hey

* ![busted image alt text

* ![busted image link](image.png

* a *bold choice

* very _italic *and bold, onto many
   lines is OK* but don't forget...

a paragraph with [a bad link syntax](http://example.com
is OK. The rest *works*.
"#

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
info: hasArg:=true
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
