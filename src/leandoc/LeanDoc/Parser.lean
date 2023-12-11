/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Lean
import Std.Tactic.GuardMsgs

import LeanDoc.Parser.Lean
import LeanDoc.SyntaxUtils
import LeanDoc.Syntax

namespace LeanDoc.Parser


open LeanDoc.SyntaxUtils
open LeanDoc.Syntax
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
info: Failure: unexpected small A
Final stack:
  ["a" "a" "a" <missing>]
Remaining: "a"
-/
#guard_msgs in
  #eval atMostFn 3 (chFn 'a') "small A" |>.test! "aaaa"

/--
info: Failure: unexpected end of input
Final stack:
  [<missing>]
Remaining: ""
-/
#guard_msgs in
  #eval atLeastFn 3 (chFn 'a') |>.test! ""

/--
info: Failure: unexpected end of input
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
info: Failure: unexpected character
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
    mkAtom (SourceInfo.original leading startPos trailing (startPos + val)) <|
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
  s.pushSyntax <| Syntax.mkLit `column (toString col) SourceInfo.none

def guardColumn (p : Nat → Bool) (message : String) : ParserFn := fun c s =>
  if p (c.currentColumn s) then s else s.mkErrorAt message s.pos

def guardMinColumn (min : Nat) : ParserFn := guardColumn (· ≥ min) s!"expected column at least {min}"

def withCurrentColumn (p : Nat → ParserFn) : ParserFn := fun c s =>
  p (c.currentColumn s) c s

def bol : ParserFn := fun c s =>
  let position := c.fileMap.toPosition s.pos
  let col := position |>.column
  if col == 0 then s else s.mkErrorAt s!"expected beginning of line at {position}" s.pos


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

def strFn (str : String) : ParserFn := asStringFn <| fun c s =>
  let rec go (iter : String.Iterator) (s : ParserState) :=
    if iter.atEnd then s
    else
      let ch := iter.curr
      go iter.next <| satisfyFn (· == ch) ch.toString c s
  let iniPos := s.pos
  let iniSz := s.stxStack.size
  let s := go str.iter s
  if s.hasError then s.mkErrorAt str iniPos (some iniSz) else s


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
    | _ => s.next' c.input i h

/-- Return some inline text up to the next inline opener or the end of
the line, whichever is first. Always consumes at least one
logical character on success, taking escaping into account. -/
def inlineText : ParserFn := asStringFn (transform := unescapeStr) <| atomicFn inlineTextChar >> manyFn inlineTextChar

/--
info: Failure: unexpected end of input
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
info: Failure: '['
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
info: Failure: '*'
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

def val : ParserFn := docNumLitFn <|> docIdentFn <|> docStrLitFn

/--
info: Success! Final stack:
  (num "1")
All input consumed.
-/
#guard_msgs in
  #eval val.test! "1"
/--
info: Success! Final stack:
  (num "3")
All input consumed.
-/
#guard_msgs in
  #eval val.test! "3"
/--
info: Failure: unexpected end of input; expected identifier, numeral or string literal
Final stack:
  <missing>
Remaining: ""
-/
#guard_msgs in
  #eval val.test! ""

/--
info: Success! Final stack:
  (str "\"a b c\t d\"")
All input consumed.
-/
#guard_msgs in
  #eval val.test! "\"a b c\t d\""

/--
info: Success! Final stack:
  (str "\"a b c\t d\"")
Remaining:
"\n"
-/
#guard_msgs in
  #eval val.test! "\"a b c\t d\"\n"


def withCurrentStackSize (p : Nat → ParserFn) : ParserFn := fun c s =>
  p s.stxStack.size c s

/-- Match the character indicated, pushing nothing to the stack in case of success -/
def skipChFn (c : Char) : ParserFn :=
  satisfyFn (· == c) c.toString

def arg : ParserFn :=
    withCurrentStackSize fun iniSz =>
      potentiallyNamed iniSz <|> ((docStrLitFn <|> docNumLitFn) >> mkAnon iniSz)

where
  mkNamed (iniSz : Nat) : ParserFn := fun _ s => s.mkNode `arg.named iniSz
  mkAnon (iniSz : Nat) : ParserFn := fun _ s => s.mkNode `arg.anon iniSz
  eatSpaces := takeWhileFn (· == ' ')
  potentiallyNamed iniSz :=
      atomicFn docIdentFn >> eatSpaces >>
       ((atomicFn (strFn ":=") >> eatSpaces >> val >> eatSpaces >> mkNamed iniSz) <|> mkAnon iniSz)
/--
info: Success! Final stack:
  (arg.anon `x)
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "x"

/--
info: Success! Final stack:
  (arg.named `x ":=" (num "1"))
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "x:=1"

/--
info: Success! Final stack:
  (arg.named `x ":=" `y)
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "x:=y"

/--
info: Success! Final stack:
  (arg.named `x ":=" (str "\"y\""))
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "x:=\"y\""

/--
info: Failure: unterminated string literal; expected identifier or numeral
Final stack:
 • `x
 • ":="
 • <missing>

Remaining: "\"y"
-/
#guard_msgs in
  #eval arg.test! "x:=\"y"

/--
info: Success! Final stack:
  (arg.anon (num "42"))
All input consumed.
-/
#guard_msgs in
#eval arg.test! "42"


/--
info: Success! Final stack:
  `x
Remaining:
"\n"
-/
#guard_msgs in
#eval docIdentFn.test! "x\n"

def eatSpaces := takeWhileFn (· == ' ')

/--

Skip whitespace for name and arguments. If the argument is `none`,
it's in a single-line context and whitespace may only be the space
character. If it's `some N`, then newlines are allowed, but `N` is the
minimum indentation column.
-/
def nameArgWhitespace : (multiline : Option Nat) → ParserFn
  | none => eatSpaces
  | some n => takeWhileFn (fun c => c == ' ' || c == '\n') >> guardMinColumn n

def args (multiline : Option Nat := none) : ParserFn :=
  sepByFn true arg <| nameArgWhitespace multiline

def nameAndArgs (multiline : Option Nat := none) : ParserFn :=
  nameArgWhitespace multiline >> docIdentFn >>
  nameArgWhitespace multiline >> args (multiline := multiline)


/--
info: Success! Final stack:
 • `leanExample
 • [(arg.named `context ":=" (num "2"))]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context := 2"
/--
info: Success! Final stack:
 • `leanExample
 • [(arg.anon `context)]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context"
/--
info: Success! Final stack:
 • `leanExample
 • [(arg.anon `context) (arg.anon `more)]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context more"
/--
info: Success! Final stack:
 • `leanExample
 • [(arg.anon `context)
     (arg.named `more ":=" (str "\"stuff\""))]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context more:=\"stuff\""


/--
info: Success! Final stack:
 • `leanExample
 • [(arg.anon `context)
     (arg.named `more ":=" (str "\"stuff\""))]

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
    nodeFn ``linebreak <| asStringFn <| atomicFn (chFn '\n' >> lookaheadFn (manyFn (chFn ' ') >> notFollowedByFn (chFn '\n' <|> blockOpener) "newline"))
  else
    errorFn "Newlines not allowed here"

mutual
  partial def emphLike (name : SyntaxNodeKind) (char : Char) (what plural : String) (getter : InlineCtxt → Option Nat) (setter : InlineCtxt → Option Nat → InlineCtxt) (ctxt : InlineCtxt) : ParserFn :=
    nodeFn name <|
    withCurrentColumn fun c =>
      atomicFn (asStringFn (asStringFn (opener ctxt) >> notFollowedByFn (chFn ' ' false <|> chFn '\n' false) "space or newline after opener")) >>
      withCurrentColumn fun c' =>
        let count := c' - c
        manyFn (inline (setter ctxt (some count))) >>

        asStringFn (atomicFn (noSpaceBefore >> repFn count (satisfyFn (· == char) s!"{count} {plural}")))

  where
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
          s.mkError "closer without preceding space"
        else s

  partial def emph := emphLike ``emph '_' "emphasize" "underscores" (·.emphDepth) ({· with emphDepth := ·})
  partial def bold := emphLike ``bold '*' "bold" "asterisks" (·.boldDepth) ({· with boldDepth := ·})

  partial def code : ParserFn :=
    nodeFn ``code <|
    withCurrentColumn fun c =>
      atomicFn opener >>
      withCurrentColumn fun c' =>
        let count := c' - c
        nodeFn strLitKind (asStringFn (takeContentsFn (count - 1)) (quoted := true)) >>
        asStringFn (atomicFn (repFn count (satisfyFn (· == '`') s!"{count} backticks"))) >>
        notFollowedByFn (satisfyFn (· == '`') "`") "backtick"

  where
    opener : ParserFn := asStringFn (many1Fn (satisfyFn (· == '`') s!"any number of backticks"))
    takeBackticksFn : Nat → ParserFn
      | 0 => satisfyFn (· != '`') "expected non-backtick"
      | n+1 => fun c s =>
        let i := s.pos
        if h : c.input.atEnd i then s.mkEOIError
        else
          if c.input.get' i h == '`' then
            takeBackticksFn n c (s.next' c.input i h)
          else s.next' c.input i h
    takeContentsFn (maxCount : Nat) : ParserFn := fun c s =>
      let i := s.pos
      if h : c.input.atEnd i then s.mkEOIError
      else
        let ch := c.input.get' i h
        if ch == '`' then
          optionalFn (atomicFn (takeBackticksFn maxCount) >> takeContentsFn maxCount) c s
        else if ch == '\n' then s.mkUnexpectedError "newline"
        else takeContentsFn maxCount c (s.next' c.input i h)


  -- Read a prefix of a line of text, stopping at a text-mode special character
  partial def text :=
    nodeFn ``text <|
      nodeFn strLitKind <|
        asStringFn (transform := unescapeStr) (quoted := true) <|
          many1Fn inlineTextChar

  partial def link (ctxt : InlineCtxt) :=
    nodeFn ``link <|
      (atomicFn (notInLink ctxt >> strFn "[" >> notFollowedByFn (chFn '^') "'^'" )) >>
      many1Fn (inline {ctxt with inLink := true}) >>
      strFn "]" >>
      linkTarget

  partial def footnote (ctxt : InlineCtxt) :=
    nodeFn ``footnote <|
      (atomicFn (notInLink ctxt >> strFn "[^" )) >>
      nodeFn `str (asStringFn (quoted := true) (many1Fn (satisfyEscFn (· != ']')))) >>
      strFn "]"

  partial def linkTarget := ref <|> url
  where
    notUrlEnd := satisfyEscFn (· ∉ ")\n".toList) >> takeUntilEscFn (· ∈ ")\n".toList)
    notRefEnd := satisfyEscFn (· ∉ "]\n".toList) >> takeUntilEscFn (· ∈ "]\n".toList)
    ref : ParserFn := nodeFn ``LeanDoc.Syntax.ref ((atomicFn <| strFn "[") >> nodeFn strLitKind (asStringFn notRefEnd (quoted := true)) >> strFn "]")
    url : ParserFn := nodeFn ``LeanDoc.Syntax.url ((atomicFn <| strFn "(") >> nodeFn strLitKind (asStringFn notUrlEnd (quoted := true)) >> strFn ")")

  partial def notInLink (ctxt : InlineCtxt) : ParserFn := fun _ s =>
      if ctxt.inLink then s.mkError "Already in a link" else s

  partial def image : ParserFn :=
    nodeFn ``image <|
      atomicFn (strFn "![") >>
      asStringFn (takeUntilEscFn (· ∈ "]\n".toList))>>
      strFn "]" >>
      linkTarget

  partial def role (ctxt : InlineCtxt) : ParserFn :=
    nodeFn ``role <|
      intro >> (atomicFn nonBracketed <|> bracketed)
  where
    eatSpaces := takeWhileFn (· == ' ')
    intro := atomicFn (chFn '{') >> eatSpaces >> nameAndArgs >> eatSpaces >> chFn '}'
    bracketed := atomicFn (chFn '[') >> manyFn (inline ctxt >> eatSpaces) >> chFn ']'
    fakeOpen := mkAtom SourceInfo.none "["
    fakeClose := mkAtom SourceInfo.none "]"
    nonBracketed : ParserFn := fun c s =>
      let s := s.pushSyntax fakeOpen
      let s := nodeFn nullKind (delimitedInline ctxt) c s
      s.pushSyntax fakeClose


  partial def delimitedInline (ctxt : InlineCtxt) : ParserFn := emph ctxt <|> bold ctxt <|> code <|> role ctxt <|> image <|> link ctxt <|> footnote ctxt

  partial def inline (ctxt : InlineCtxt) : ParserFn :=
    text <|> linebreak ctxt <|> delimitedInline ctxt
end


def textLine (allowNewlines := true) : ParserFn := many1Fn (inline { allowNewlines })

/--
info: Success! Final stack:
  (LeanDoc.Syntax.text (str "\"abc \""))
All input consumed.
-/
#guard_msgs in
  #eval text.test! "abc "

/--
info: Success! Final stack:
  (LeanDoc.Syntax.emph
   "_"
   [(LeanDoc.Syntax.text (str "\"aa\""))]
   "_")
All input consumed.
-/
#guard_msgs in
  #eval emph {} |>.test! "_aa_"

/--
info: Failure: expected closer without preceding space
Final stack:
  (LeanDoc.Syntax.emph
   "_"
   [(LeanDoc.Syntax.text (str "\"aa \""))]
   <missing>)
Remaining: "_"
-/
#guard_msgs in
  #eval emph {} |>.test! "_aa _"

/--
info: Failure: unexpected space or newline after opener
Final stack:
  (LeanDoc.Syntax.emph "_" <missing>)
Remaining: "_ aa_"
-/
#guard_msgs in
  #eval emph {} |>.test! "_ aa_"



/--
info: Success! Final stack:
  (LeanDoc.Syntax.code
   "``"
   (str "\"foo bar\"")
   "``")
All input consumed.
-/
#guard_msgs in
  #eval code.test! "``foo bar``"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.code
   "``"
   (str "\"foo `stuff` bar\"")
   "``")
All input consumed.
-/
#guard_msgs in
  #eval code.test! "``foo `stuff` bar``"

/--
info: Failure: unexpected end of input
Final stack:
  (LeanDoc.Syntax.code "`" (str <missing>))
Remaining: ""
-/
#guard_msgs in
  #eval code.test! "`foo"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.code "`" (str "\" foo\"") "`")
All input consumed.
-/
#guard_msgs in
  #eval code.test! "` foo`"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.code "`" (str "\" foo \"") "`")
All input consumed.
-/
#guard_msgs in
  #eval code.test! "` foo `"

/--
info: Failure: newline
Final stack:
  (LeanDoc.Syntax.code "`" (str <missing>))
Remaining: "\no `"
-/
#guard_msgs in
  #eval code.test! "` fo\no `"


/--
info: Success! Final stack:
  (LeanDoc.Syntax.code
   "``"
   (str "\"foo bar\"")
   "``")
All input consumed.
-/
#guard_msgs in
  #eval (inline {}).test! "``foo bar``"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.code
   "``"
   (str "\"foo `stuff` bar\"")
   "``")
All input consumed.
-/
#guard_msgs in
  #eval (inline {}).test! "``foo `stuff` bar``"

/--
info: Failure: unexpected end of input
Final stack:
  (LeanDoc.Syntax.code "`" (str <missing>))
Remaining: ""
-/
#guard_msgs in
  #eval (inline {}).test! "`foo"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.code "`" (str "\" foo\"") "`")
All input consumed.
-/
#guard_msgs in
  #eval (inline {}).test! "` foo`"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.code "`" (str "\" foo \"") "`")
All input consumed.
-/
#guard_msgs in
  #eval (inline {}).test! "` foo `"

/--
info: Failure: newline
Final stack:
  (LeanDoc.Syntax.code "`" (str <missing>))
Remaining: "\no `"
-/
#guard_msgs in
  #eval (inline {}).test! "` fo\no `"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.bold
   "**"
   [(LeanDoc.Syntax.text (str "\"aa\""))]
   "**")
All input consumed.
-/
#guard_msgs in
  #eval bold {} |>.test! "**aa**"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.bold
   "**"
   [(LeanDoc.Syntax.text (str "\"aa\""))
    (LeanDoc.Syntax.linebreak "\n")
    (LeanDoc.Syntax.text (str "\"bb\""))]
   "**")
All input consumed.
-/
#guard_msgs in
  #eval inline {} |>.test! "**aa\nbb**"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.text (str "\"a \""))
Remaining:
"* b"
-/
#guard_msgs in
  #eval inline {} |>.test! "a * b"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.link
   "["
   [(LeanDoc.Syntax.text (str "\"Wikipedia\""))]
   "]"
   (LeanDoc.Syntax.url
    "("
    (str "\"https://en.wikipedia.org\"")
    ")"))
All input consumed.
-/
#guard_msgs in
  #eval inline {} |>.test! "[Wikipedia](https://en.wikipedia.org)"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.image
   "!["
   ""
   "]"
   (LeanDoc.Syntax.url
    "("
    (str "\"logo.png\"")
    ")"))
All input consumed.
-/
#guard_msgs in
  #eval inline {} |>.test! "![](logo.png)"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.image
   "!["
   "alt text is good"
   "]"
   (LeanDoc.Syntax.url
    "("
    (str "\"logo.png\"")
    ")"))
All input consumed.
-/
#guard_msgs in
  #eval inline {} |>.test! "![alt text is good](logo.png)"

/--
info: Failure: expected ( or [
Final stack:
  (LeanDoc.Syntax.image
   "!["
   "alt text is good"
   "]"
   (LeanDoc.Syntax.url <missing>))
Remaining: "](logo.png)"
-/
#guard_msgs in
  #eval inline {} |>.test! "![alt text is good]](logo.png)"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.role
   "{"
   `hello
   []
   "}"
   "["
   [(LeanDoc.Syntax.bold
     "*"
     [(LeanDoc.Syntax.text (str "\"there\""))]
     "*")]
   "]")
All input consumed.
-/
#guard_msgs in
#eval role {} |>.test! "{hello}*there*"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.role
   "{"
   `hello
   []
   "}"
   "["
   [(LeanDoc.Syntax.text (str "\"there\""))]
   "]")
All input consumed.
-/
#guard_msgs in
#eval role {} |>.test! "{hello}[there]"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.role
   "{"
   `hello
   [(arg.named `world ":=" `gaia)]
   "}"
   "["
   [(LeanDoc.Syntax.text (str "\"there\""))]
   "]")
All input consumed.
-/
#guard_msgs in
#eval role {} |>.test! "{hello world:=gaia}[there]"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.role
   "{"
   `hello
   [(arg.named `world ":=" `gaia)]
   "}"
   "["
   [(LeanDoc.Syntax.text (str "\"there \""))
    (LeanDoc.Syntax.bold
     "*"
     [(LeanDoc.Syntax.text (str "\"is\""))]
     "*")
    (LeanDoc.Syntax.emph
     "_"
     [(LeanDoc.Syntax.text
       (str "\"a meaning!\""))]
     "_")]
   "]")
All input consumed.
-/
#guard_msgs in
#eval role {} |>.test! "{hello world:=gaia}[there *is* _a meaning!_ ]"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.footnote "[^" (str "\"1\"") "]")
All input consumed.
-/
#guard_msgs in
#eval footnote {} |>.test! "[^1]"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.footnote "[^" (str "\"1\"") "]")
All input consumed.
-/
#guard_msgs in
#eval inline {} |>.test! "[^1]"

structure InList where
  indentation : Nat
  type : OrderedListType ⊕ UnorderedListType
deriving Repr

structure BlockCtxt where
  minIndent : Nat := 0
  maxDirective : Option Nat := none
  inLists : List InList := []
deriving Inhabited, Repr

def fakeAtom (str : String) : ParserFn := fun _c s =>
  let atom := mkAtom SourceInfo.none str
  s.pushSyntax atom

def lookaheadOrderedListIndicator (ctxt : BlockCtxt) (p : OrderedListType → Int → ParserFn) : ParserFn := fun c s =>
    let iniPos := s.pos
    let iniSz := s.stxStack.size
    let s := (bol >> takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent) c s
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
 • "LeanDoc.Parser.OrderedListType.numDot 1"

Remaining:
"1. "
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "1. "
/--
info: Success! Final stack:
 • (num "2")
 • "LeanDoc.Parser.OrderedListType.numDot 2"

Remaining:
"2. "
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "2. "
/--
info: Failure: unexpected end of input
Final stack:
  <missing>
Remaining: "2."
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "2."
/--
info: Success! Final stack:
 • (num "2")
 • "LeanDoc.Parser.OrderedListType.parenAfter 2"

Remaining:
"2) "
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "2) "
/--
info: Failure: digits
Final stack:
 empty
Remaining: "-23) "
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "-23) "
/--
info: Failure: digits
Final stack:
 empty
Remaining: "a-23) "
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "a-23) "
/--
info: Failure: unexpected ' '; expected ')' or '.'
Final stack:
 empty
Remaining: "23 ) "
-/
#guard_msgs in
#eval lookaheadOrderedListIndicator {} (fun type i => fakeAtom s!"{repr type} {i}") |>.test! "23 ) "


def lookaheadUnorderedListIndicator (ctxt : BlockCtxt) (p : UnorderedListType → ParserFn) : ParserFn := fun c s =>
  let iniPos := s.pos
  let iniSz := s.stxStack.size
  let s := (bol >> takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent) c s
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
  "LeanDoc.Parser.UnorderedListType.asterisk"
Remaining:
"* "
-/
#guard_msgs in
#eval lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}") |>.test! "* "
/--
info: Success! Final stack:
  "LeanDoc.Parser.UnorderedListType.dash"
Remaining:
"- "
-/
#guard_msgs in
#eval lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}") |>.test! "- "
/--
info: Success! Final stack:
  "LeanDoc.Parser.UnorderedListType.plus"
Remaining:
"+ "
-/
#guard_msgs in
#eval lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}") |>.test! "+ "
/--
info: Success! Final stack:
  "LeanDoc.Parser.UnorderedListType.asterisk"
Remaining:
"* "
-/
#guard_msgs in
#eval lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}") |>.test! " * "

/--
info: Failure: unexpected end of input
Final stack:
  <missing>
Remaining: " *"
-/
#guard_msgs in
#eval lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}") |>.test! " *"
/--
info: Failure: ' '
Final stack:
  <missing>
Remaining: "** "
-/
#guard_msgs in
#eval lookaheadUnorderedListIndicator {} (fun type => fakeAtom s! "{repr type}") |>.test! "** "

mutual
  partial def listItem (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``li (bulletFn >> withCurrentColumn fun c => blocks {ctxt with minIndent := c})
  where
    bulletFn :=
      match ctxt.inLists.head? with
      | none => fun _ s => s.mkError "not in a list"
      | some ⟨col, .inr type⟩ =>
        atomicFn <| nodeFn `bullet <|
          takeWhileFn (· == ' ') >>
          pushColumn >>
          guardColumn (· == col) s!"indentation at {col}" >>
          unorderedListIndicator type >> ignoreFn (lookaheadFn (chFn ' '))
      | some ⟨col, .inl type⟩ =>
        atomicFn <| nodeFn `bullet <|
          takeWhileFn (· == ' ') >>
          pushColumn >>
          guardColumn (· == col) s!"indentation at {col}" >>
          orderedListIndicator type >> ignoreFn (lookaheadFn (chFn ' '))


  partial def descItem (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``desc <|
      colonFn >>
      withCurrentColumn fun c => textLine >> ignoreFn (manyFn blankLine) >>
      fakeAtom "=>" >>
      blocks1 { ctxt with minIndent := c}
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
      lookaheadUnorderedListIndicator ctxt (fun type => withCurrentColumn (fun c => many1Fn (listItem {ctxt with minIndent := c + 1 , inLists := ⟨c, .inr type⟩  :: ctxt.inLists})))

  partial def orderedList (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``ol <|
      lookaheadOrderedListIndicator ctxt fun type _start => -- TODO? Validate list numbering?
        withCurrentColumn fun c =>
          many1Fn (listItem {ctxt with minIndent := c + 1 , inLists := ⟨c, .inl type⟩  :: ctxt.inLists})


  partial def definitionList (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``dl <|
      atomicFn (bol >> takeWhileFn (· == ' ') >> ignoreFn (lookaheadFn (chFn ':' >> chFn ' ')) >> guardMinColumn ctxt.minIndent) >>
      withCurrentColumn (fun c => many1Fn (descItem {ctxt with minIndent := c}))

  partial def para (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``para <| atomicFn (takeWhileFn (· == ' ') >> notFollowedByFn blockOpener "block opener" >> guardMinColumn ctxt.minIndent) >> textLine

  partial def header (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``header <|
      guardMinColumn ctxt.minIndent >>
      atomicFn (bol >> asStringFn (many1Fn (skipChFn '#')) >> skipChFn ' ' >> takeWhileFn (· == ' ') >> lookaheadFn (satisfyFn (· != '\n'))) >>
      textLine (allowNewlines := false)



  partial def codeBlock (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``codeblock <|
      -- Opener - leaves indent info and open token on the stack
      atomicFn (takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent >> pushColumn >> asStringFn (atLeastFn 3 (skipChFn '`'))) >>
      withIndentColumn fun c =>
        withCurrentColumn fun c' =>
          let fenceWidth := c' - c
          takeWhileFn (· == ' ') >>
          optionalFn nameAndArgs >>
          satisfyFn (· == '\n') "newline" >>
          asStringFn (manyFn (codeFrom c fenceWidth)) (transform := deIndent c) >>
          closeFence c fenceWidth

  where
    withIndentColumn (p : Nat → ParserFn) : ParserFn := fun c s =>
      let colStx := s.stxStack.get! (s.stxStack.size - 2)
      match colStx with
      | .node _ `column #[.atom _ col] =>
        if let some colNat := col.toNat? then p colNat c s else s.mkError s!"Internal error - not a Nat {col}"
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
        (takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent >> pushColumn >> asStringFn (atLeastFn 3 (skipChFn ':')) >>
         guardOpenerSize) >>
      withIndentColumn fun c =>
        withCurrentColumn fun c' =>
          let fenceWidth := c' - c
          dropIndentColumn >> -- TODO kludge
          takeWhileFn (· == ' ') >>
          nameAndArgs >>
          satisfyFn (· == '\n') "newline" >>
          fakeAtom "\n" >>
          fakeAtom "\n" >>
          blocks {ctxt with minIndent := c, maxDirective := fenceWidth} >>
          closeFence c fenceWidth

  where
    withIndentColumn (p : Nat → ParserFn) : ParserFn := fun c s =>
      let colStx := s.stxStack.get! (s.stxStack.size - 2)
      match colStx with
      | .node _ `column #[.atom _ col] =>
        if let some colNat := col.toNat? then p colNat c s else s.mkError s!"Internal error - not a Nat {col}"
      | other => s.mkError s!"Internal error - not a column node {other}"

    dropIndentColumn : ParserFn := fun _ s =>
      let top := s.stxStack.get! (s.stxStack.size - 1)
      let s := {s with stxStack := s.stxStack.pop.pop}
      s.pushSyntax top

    guardOpenerSize : ParserFn := withIndentColumn fun c => withCurrentColumn fun c' =>
      match ctxt.maxDirective with
      | none => skipFn
      | some m => if c' - c < m then skipFn else fun _ s => s.mkError "Too many ':'s here"

    closeFence (col width : Nat) :=
      atomicFn
        (bol >> takeWhileFn (· == ' ') >> (withCurrentColumn fun c'=> guardColumn (· == col) s!"column {col} (got {c'})") >>
         asStringFn (repFn width (skipChFn ':'))) >>
      notFollowedByFn (skipChFn ':') "extra :" >>
      takeWhileFn (· == ' ') >> (satisfyFn (· == '\n') "newline" <|> eoiFn)

  partial def block_role (ctxt : BlockCtxt) : ParserFn := fun c s =>
    let iniPos := s.pos
    let iniSz := s.stxStack.size
    let restorePosOnErr : ParserState → ParserState
      | ⟨stack, lhsPrec, _, cache, some msg⟩ => ⟨stack, lhsPrec, iniPos, cache, some msg⟩
      | other => other
    let s := eatSpaces c s
    if s.hasError then restorePosOnErr s
    else
      let col := c.currentColumn s
      let s := (intro >> eatSpaces >> ignoreFn (satisfyFn (· == '\n') "newline" <|> eoiFn)) c s
      if s.hasError then restorePosOnErr s
      else
        let s := block {ctxt with minIndent := col} c s
        s.mkNode ``block_role iniSz
  where
    eatSpaces := takeWhileFn (· == ' ')
    intro := guardMinColumn (ctxt.minIndent) >> withCurrentColumn fun c => atomicFn (chFn '{') >> withCurrentColumn fun c' => nameAndArgs (some c') >> nameArgWhitespace (some c)  >> chFn '}'

  partial def linkRef (c : BlockCtxt) : ParserFn :=
    nodeFn ``link_ref <|
      atomicFn (ignoreFn (bol >> eatSpaces >> guardMinColumn c.minIndent) >> chFn '[' >> nodeFn strLitKind (asStringFn (quoted := true) (satisfyEscFn nameStart >> manyFn (satisfyEscFn (· != ']')))) >> strFn "]:") >>
      eatSpaces >>
      nodeFn strLitKind (asStringFn (quoted := true) (takeWhileFn (· != '\n'))) >>
      ignoreFn (satisfyFn (· == '\n') "newline" <|> eoiFn)
  where nameStart c := c != ']' && c != '^'

  partial def footnoteRef (c : BlockCtxt) : ParserFn :=
    nodeFn ``footnote_ref <|
      atomicFn (ignoreFn (bol >> eatSpaces >> guardMinColumn c.minIndent) >> strFn "[^" >> nodeFn strLitKind (asStringFn (quoted := true) (many1Fn (satisfyEscFn (· != ']')))) >> strFn "]:") >>
      eatSpaces >>
      notFollowedByFn blockOpener "block opener" >> guardMinColumn c.minIndent >> textLine

  partial def block (c : BlockCtxt) : ParserFn :=
    block_role c <|> unorderedList c <|> orderedList c <|> definitionList c <|> header c <|> codeBlock c <|> directive c <|> blockquote c <|> linkRef c <|> footnoteRef c <|> para c

  partial def blocks (c : BlockCtxt) : ParserFn := sepByFn true (block c) (ignoreFn (manyFn blankLine))

  partial def blocks1 (c : BlockCtxt) : ParserFn := sepBy1Fn true (block c) (ignoreFn (manyFn blankLine))

  partial def document (blockContext : BlockCtxt := {}) : ParserFn := ignoreFn (manyFn blankLine) >> blocks blockContext
end

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text
      (str
       "\"This is just some textual content. How is it?\""))])
   (LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text (str "\"More?\""))])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "This is just some textual content. How is it?\n\nMore?"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text
      (str
       "\"I can describe lists like this one:\""))])
   (LeanDoc.Syntax.ul
    [(LeanDoc.Syntax.li
      (bullet (column "0") "*")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text (str "\"a\""))])])
     (LeanDoc.Syntax.li
      (bullet (column "0") "*")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"b\""))])])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "I can describe lists like this one:\n\n* a\n* b"


/--
info: Success! Final stack:
  [(LeanDoc.Syntax.para
    [(LeanDoc.Syntax.image
      "!["
      "Lean logo"
      "]"
      (LeanDoc.Syntax.url
       "("
       (str "\"/static/lean_logo.svg\"")
       ")"))])
   (LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text
      (str
       "\"This is an example website/blog, for testing purposes.\""))])]
All input consumed.
-/
#guard_msgs in
  #eval document |>.test! "\n![Lean logo](/static/lean_logo.svg)\n\nThis is an example website/blog, for testing purposes."



/--
info: Success! Final stack:
  (LeanDoc.Syntax.li
   (bullet (column "0") "*")
   [(LeanDoc.Syntax.para
     [(LeanDoc.Syntax.text (str "\"foo\""))])])
Remaining:
"* bar\n"
-/
#guard_msgs in
  #eval listItem {inLists:=[⟨0, .inr .asterisk⟩]} |>.test! "* foo\n* bar\n"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.ul
    [(LeanDoc.Syntax.li
      (bullet (column "0") "*")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text (str "\"foo\""))])])
     (LeanDoc.Syntax.li
      (bullet (column "0") "*")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text (str "\"bar\""))
         (LeanDoc.Syntax.linebreak "\n")])])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "* foo\n* bar\n"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.ul
    [(LeanDoc.Syntax.li
      (bullet (column "0") "*")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text (str "\"foo\""))
         (LeanDoc.Syntax.linebreak "\n")
         (LeanDoc.Syntax.text
          (str "\"  thing\""))])])])]
Remaining:
"* bar\n"
-/
#guard_msgs in
  #eval blocks {} |>.test! "* foo\n  thing* bar\n"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.ul
    [(LeanDoc.Syntax.li
      (bullet (column "0") "+")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text (str "\"foo\""))])])
     (LeanDoc.Syntax.li
      (bullet (column "0") "+")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text (str "\"bar\""))
         (LeanDoc.Syntax.linebreak "\n")])])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "+ foo\n+ bar\n"


/--
info: Success! Final stack:
  [(LeanDoc.Syntax.ul
    [(LeanDoc.Syntax.li
      (bullet (column "0") "*")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text (str "\"foo\""))])])
     (LeanDoc.Syntax.li
      (bullet (column "0") "*")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text (str "\"bar\""))
         (LeanDoc.Syntax.linebreak "\n")])])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "* foo\n\n* bar\n"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.ul
    [(LeanDoc.Syntax.li
      (bullet (column "0") "*")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text (str "\"foo\""))
         (LeanDoc.Syntax.linebreak "\n")
         (LeanDoc.Syntax.text
          (str "\"  stuff\""))])
       (LeanDoc.Syntax.blockquote
        ">"
        [(LeanDoc.Syntax.para
          [(LeanDoc.Syntax.text
            (str "\"more \""))])])
       (LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text (str "\"abc\""))])])
     (LeanDoc.Syntax.li
      (bullet (column "0") "*")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text (str "\"bar\""))
         (LeanDoc.Syntax.linebreak "\n")])])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "* foo\n  stuff\n\n > more \n\n abc\n\n\n* bar\n"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.ul
    [(LeanDoc.Syntax.li
      (bullet (column "0") "*")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text (str "\"foo\""))])
       (LeanDoc.Syntax.ul
        [(LeanDoc.Syntax.li
          (bullet (column "2") "*")
          [(LeanDoc.Syntax.para
            [(LeanDoc.Syntax.text
              (str "\"bar\""))])])])])
     (LeanDoc.Syntax.li
      (bullet (column "0") "*")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"more outer\""))])])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "* foo\n  * bar\n* more outer"

/--
info: Failure: unexpected end of input; expected ![, [, [^ or expected beginning of line at ⟨2, 15⟩
Final stack:
  [(LeanDoc.Syntax.dl
    [(LeanDoc.Syntax.desc
      ":"
      [(LeanDoc.Syntax.text
        (str "\" an excellent idea\""))
       (LeanDoc.Syntax.linebreak "\n")
       (LeanDoc.Syntax.text
        (str "\"Let's say more!\""))]
      "=>"
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.footnote <missing>)])
       <missing>])])]
Remaining: ""
-/
#guard_msgs in
  #eval blocks {} |>.test! ": an excellent idea\nLet's say more!"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.dl
    [(LeanDoc.Syntax.desc
      ":"
      [(LeanDoc.Syntax.text
        (str "\" an excellent idea\""))]
      "=>"
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"Let's say more!\""))])])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! ": an excellent idea\n\n    Let's say more!"

/--
info: Failure: unexpected end of input; expected expected column at least 1
Final stack:
  [(LeanDoc.Syntax.dl
    [(LeanDoc.Syntax.desc
      ":"
      [(LeanDoc.Syntax.text
        (str "\" an excellent idea\""))]
      "=>"
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"Let's say more!\""))])])
     (LeanDoc.Syntax.desc
      ":"
      [(LeanDoc.Syntax.text (str "\" more\""))]
      "=>"
      [(LeanDoc.Syntax.para <missing>)
       <missing>])])]
Remaining: ""
-/
#guard_msgs in
  #eval blocks {} |>.test! ": an excellent idea\n\n Let's say more!\n\n: more\n\n"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.dl
    [(LeanDoc.Syntax.desc
      ":"
      [(LeanDoc.Syntax.text
        (str "\" an excellent idea\""))]
      "=>"
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"Let's say more!\""))])])
     (LeanDoc.Syntax.desc
      ":"
      [(LeanDoc.Syntax.text (str "\" more\""))]
      "=>"
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"stuff\""))])])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! ": an excellent idea\n\n Let's say more!\n\n: more\n\n stuff"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.ol
    (num "1")
    [(LeanDoc.Syntax.li
      (bullet (column "0") "1.")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"Hello\""))])])
     (LeanDoc.Syntax.li
      (bullet (column "0") "2.")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"World\""))])])])]
All input consumed.
-/
#guard_msgs in
 #eval blocks {} |>.test! "1. Hello\n\n2. World"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.ol
    (num "1")
    [(LeanDoc.Syntax.li
      (bullet (column "1") "1.")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"Hello\""))])])])]
All input consumed.
-/
#guard_msgs in
 #eval blocks {} |>.test! " 1. Hello"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.ol
    (num "1")
    [(LeanDoc.Syntax.li
      (bullet (column "0") "1.")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"Hello\""))])])])
   (LeanDoc.Syntax.ol
    (num "2")
    [(LeanDoc.Syntax.li
      (bullet (column "1") "2.")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"World\""))])])])]
All input consumed.
-/
#guard_msgs in
 #eval blocks {} |>.test! "1. Hello\n\n 2. World"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.ol
    (num "1")
    [(LeanDoc.Syntax.li
      (bullet (column "1") "1.")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"Hello\""))])])
     (LeanDoc.Syntax.li
      (bullet (column "1") "2.")
      [(LeanDoc.Syntax.para
        [(LeanDoc.Syntax.text
          (str "\"World\""))])])])]
All input consumed.
-/
#guard_msgs in
 #eval blocks {} |>.test! " 1. Hello\n\n 2. World"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.blockquote
    ">"
    [(LeanDoc.Syntax.para
      [(LeanDoc.Syntax.text (str "\"hey\""))
       (LeanDoc.Syntax.linebreak "\n")])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "> hey\n"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text (str "\"n*k \""))])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "n\\*k "

-- Unlike Djot, we don't have precedence - these must be well-nested
/--
info: Failure: 1 underscores
Final stack:
  [(LeanDoc.Syntax.para
    [(LeanDoc.Syntax.bold
      "*"
      [(LeanDoc.Syntax.text (str "\"This is \""))
       (LeanDoc.Syntax.emph
        "_"
        [(LeanDoc.Syntax.text (str "\"strong\""))]
        <missing>)])])]
Remaining: "* not regular_ emphasis"
-/
#guard_msgs in
  #eval blocks {} |>.test! "*This is _strong* not regular_ emphasis"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.header
   "#"
   [(LeanDoc.Syntax.text (str "\"Header!\""))])
All input consumed.
-/
#guard_msgs in
  #eval header {} |>.test! "# Header!"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.header
    "#"
    [(LeanDoc.Syntax.text (str "\"Header!\""))])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "# Header!\n"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.blockquote
    ">"
    [(LeanDoc.Syntax.para
      [(LeanDoc.Syntax.text (str "\"Quotation\""))
       (LeanDoc.Syntax.linebreak "\n")
       (LeanDoc.Syntax.text
        (str "\"and contained\""))])])]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> Quotation\nand contained"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.blockquote
    ">"
    [(LeanDoc.Syntax.para
      [(LeanDoc.Syntax.text
        (str "\"Quotation\""))])
     (LeanDoc.Syntax.para
      [(LeanDoc.Syntax.text
        (str "\"and contained\""))])])]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> Quotation\n\n and contained"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.blockquote
    ">"
    [(LeanDoc.Syntax.para
      [(LeanDoc.Syntax.text
        (str "\"Quotation\""))])])
   (LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text
      (str "\"and not contained\""))])]
All input consumed.
-/
#guard_msgs in
#eval blocks {} |>.test! "> Quotation\n\nand not contained"



/--
info: Success! Final stack:
  (LeanDoc.Syntax.codeblock
   (column "1")
   "```"
   [`scheme []]
   "(define x 4)\nx\n"
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ``` scheme\n (define x 4)\n x\n ```"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.codeblock
   (column "0")
   "```"
   [`scheme []]
   " (define x 4)\n x\n"
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme\n (define x 4)\n x\n```"


/--
info: Success! Final stack:
  (LeanDoc.Syntax.codeblock
   (column "1")
   "```"
   []
   "(define x 4)\nx\n"
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ``` \n (define x 4)\n x\n ```"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.codeblock
   (column "1")
   "```"
   []
   "(define x 4)\nx\n"
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ```\n (define x 4)\n x\n ```"


/--
info: Success! Final stack:
  (LeanDoc.Syntax.codeblock
   (column "0")
   "```"
   [`scheme []]
   " (define x 4)\n x\n"
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme\n (define x 4)\n x\n```\n"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.codeblock
   (column "0")
   "```"
   [`scheme []]
   "(define x 4)\nx\n"
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme\n(define x 4)\nx\n```"


/--
info: Failure: expected column 0
Final stack:
  (LeanDoc.Syntax.codeblock
   (column "0")
   "```"
   [`scheme []]
   "(define x 4)\nx\n"
   <missing>)
Remaining: "````"
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme\n(define x 4)\nx\n ````"

/--
info: Failure: newline
Final stack:
  (LeanDoc.Syntax.codeblock
   (column "0")
   "```"
   [`scheme
    [(arg.named `dialect ":=" (str "\"chicken\""))
     (arg.anon (num "43"))]]
   <missing>)
Remaining: "(define x 4)\nx\n```"
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme dialect:=\"chicken\" 43\n(define x 4)\nx\n```"

/--
info: Failure: expected column 1
Final stack:
  (LeanDoc.Syntax.codeblock
   (column "1")
   "```"
   [`scheme []]
   "\n"
   <missing>)
Remaining: "(define x 4)\nx\n```"
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ``` scheme\n(define x 4)\nx\n```"

/--
info: Failure: expected column 1
Final stack:
  (LeanDoc.Syntax.codeblock
   (column "1")
   "```"
   [`scheme []]
   "(define x 4)\nx\n"
   <missing>)
Remaining: "```"
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ``` scheme\n (define x 4)\n x\n```"

/--
info: Failure: expected column 1
Final stack:
  (LeanDoc.Syntax.codeblock
   (column "1")
   "```"
   []
   "(define x 4)\nx\n"
   <missing>)
Remaining: "```"
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ```\n (define x 4)\n x\n```"

/--
info: Failure: expected column 1
Final stack:
  (LeanDoc.Syntax.codeblock
   (column "1")
   "```"
   []
   "(define x 4)\nx\n"
   <missing>)
Remaining: "```"
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ```   \n (define x 4)\n x\n```"


/--
info: Success! Final stack:
  (LeanDoc.Syntax.block_role
   "{"
   `test
   []
   "}"
   (LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text
      (str "\"Here's a modified paragraph.\""))]))
All input consumed.
-/
#guard_msgs in
#eval block {} |>.test! "{test}\nHere's a modified paragraph."
/--
info: Success! Final stack:
  (LeanDoc.Syntax.block_role
   "{"
   `test
   []
   "}"
   (LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text
      (str "\"Here's a modified paragraph.\""))]))
All input consumed.
-/
#guard_msgs in
#eval block {} |>.test! "{test}\n Here's a modified paragraph."
/--
info: Success! Final stack:
  (LeanDoc.Syntax.block_role
   "{"
   `test
   []
   "}"
   (LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text
      (str "\"Here's a modified paragraph.\""))]))
All input consumed.
-/
#guard_msgs in
#eval block {} |>.test! " {test}\n Here's a modified paragraph."
/--
info: Failure: ':'; expected expected column at least 1
Final stack:
  (LeanDoc.Syntax.block_role
   "{"
   `test
   []
   "}"
   (LeanDoc.Syntax.para <missing>))
Remaining: "Here's a modified paragraph."
-/
#guard_msgs in
#eval block {} |>.test! " {test}\nHere's a modified paragraph."
/--
info: Success! Final stack:
  (LeanDoc.Syntax.block_role
   "{"
   `test
   []
   "}"
   (LeanDoc.Syntax.blockquote
    ">"
    [(LeanDoc.Syntax.para
      [(LeanDoc.Syntax.text
        (str
         "\"Here's a modified blockquote\""))])
     (LeanDoc.Syntax.para
      [(LeanDoc.Syntax.text
        (str "\"with multiple paras\""))])]))
Remaining:
"that ends"
-/
#guard_msgs in
#eval block {} |>.test! "{test}\n> Here's a modified blockquote\n\n with multiple paras\n\nthat ends"
/--
info: Failure: expected identifier
Final stack:
  (LeanDoc.Syntax.para
   [(LeanDoc.Syntax.role "{" <missing>)])
Remaining: "\ntest}\nHere's a modified paragraph."
-/
#guard_msgs in
#eval block {} |>.test! "{\ntest}\nHere's a modified paragraph."
/--
info: Success! Final stack:
  (LeanDoc.Syntax.block_role
   "{"
   `test
   []
   "}"
   (LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text
      (str "\"Here's a modified paragraph.\""))]))
All input consumed.
-/
#guard_msgs in
#eval block {} |>.test! "{\n test}\nHere's a modified paragraph."
/--
info: Failure: expected identifier
Final stack:
  (LeanDoc.Syntax.para
   [(LeanDoc.Syntax.role "{" <missing>)])
Remaining: "\n    test\narg}\nHere's a modified paragraph."
-/
#guard_msgs in
#eval block {} |>.test! "{\n    test\narg}\nHere's a modified paragraph."
/--
info: Success! Final stack:
  (LeanDoc.Syntax.block_role
   "{"
   `test
   [(arg.anon `arg)]
   "}"
   (LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text
      (str "\"Here's a modified paragraph.\""))]))
All input consumed.
-/
#guard_msgs in
#eval block {} |>.test! "{\n    test\n arg}\nHere's a modified paragraph."
/--
info: Failure: '{'; expected ![, *, +, -, [ or [^
Final stack:
  (LeanDoc.Syntax.block_role
   "{"
   `test
   [(arg.anon `arg)]
   "}"
   (LeanDoc.Syntax.para
    [(LeanDoc.Syntax.footnote <missing>)]))
Remaining: "\n\nHere's a modified paragraph."
-/
#guard_msgs in
#eval block {} |>.test! "{\n    test\n arg}\n\n\nHere's a modified paragraph."


/--
info: Success! Final stack:
  (LeanDoc.Syntax.directive
   "::::"
   `multiPara
   []
   "\n"
   "\n"
   [(LeanDoc.Syntax.para
     [(LeanDoc.Syntax.text (str "\"foo\""))])]
   "::::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! ":::: multiPara\nfoo\n::::"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.directive
   ":::"
   `multiPara
   [(arg.named
     `greatness
     ":="
     (str "\"amazing!\""))]
   "\n"
   "\n"
   [(LeanDoc.Syntax.para
     [(LeanDoc.Syntax.text (str "\"foo\""))])]
   ":::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! " ::: multiPara greatness:=\"amazing!\"\n foo\n :::"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.directive
   ":::"
   `multiPara
   []
   "\n"
   "\n"
   [(LeanDoc.Syntax.para
     [(LeanDoc.Syntax.text (str "\"foo\""))])
    (LeanDoc.Syntax.ul
     [(LeanDoc.Syntax.li
       (bullet (column "2") "*")
       [(LeanDoc.Syntax.para
         [(LeanDoc.Syntax.text
           (str "\"List item \""))])])])]
   ":::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! " ::: multiPara\n foo\n \n \n \n  * List item \n :::"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.directive
   ":::"
   `multiPara
   []
   "\n"
   "\n"
   [(LeanDoc.Syntax.para
     [(LeanDoc.Syntax.text (str "\"foo\""))])
    (LeanDoc.Syntax.ul
     [(LeanDoc.Syntax.li
       (bullet (column "1") "*")
       [(LeanDoc.Syntax.para
         [(LeanDoc.Syntax.text
           (str "\"List item \""))])])])]
   ":::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! " ::: multiPara\n foo\n\n * List item \n :::"

/--
info: Success! Final stack:
  (LeanDoc.Syntax.text (str "\" \""))
Remaining:
"[\\[link\\]](https://link.com)"
-/
#guard_msgs in
  #eval text |>.test! " [\\[link\\]](https://link.com)"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.para
    [(LeanDoc.Syntax.link
      "["
      [(LeanDoc.Syntax.text (str "\"[link A]\""))]
      "]"
      (LeanDoc.Syntax.url
       "("
       (str "\"https://example.com\"")
       ")"))
     (LeanDoc.Syntax.text (str "\" \""))
     (LeanDoc.Syntax.link
      "["
      [(LeanDoc.Syntax.text (str "\"[link B]\""))]
      "]"
      (LeanDoc.Syntax.url
       "("
       (str "\"https://more.example.com\"")
       ")"))])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "[\\[link A\\]](https://example.com) [\\[link B\\]](https://more.example.com)"


/--
info: Success! Final stack:
  [(LeanDoc.Syntax.para
    [(LeanDoc.Syntax.link
      "["
      [(LeanDoc.Syntax.text (str "\"My link\""))]
      "]"
      (LeanDoc.Syntax.ref
       "["
       (str "\"lean\"")
       "]"))])
   (LeanDoc.Syntax.link_ref
    "["
    (str "\"lean\"")
    "]:"
    (str "\"https://lean-lang.org\""))]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "[My link][lean]\n\n[lean]: https://lean-lang.org"

/--
info: Failure: expected ( or [
Final stack:
  [(LeanDoc.Syntax.para
    [(LeanDoc.Syntax.link
      "["
      [(LeanDoc.Syntax.text (str "\"My link\""))]
      "]"
      (LeanDoc.Syntax.ref
       "["
       (str "\"lean\"")
       "]"))
     (LeanDoc.Syntax.linebreak "\n")
     (LeanDoc.Syntax.link
      "["
      [(LeanDoc.Syntax.text (str "\"lean\""))]
      "]"
      (LeanDoc.Syntax.url <missing>))])]
Remaining: ": https://lean-lang.org"
-/
-- NB this is correct - blank lines are required here
#guard_msgs in
  #eval blocks {} |>.test! "[My link][lean]\n[lean]: https://lean-lang.org"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.para
    [(LeanDoc.Syntax.link
      "["
      [(LeanDoc.Syntax.text (str "\"My link\""))]
      "]"
      (LeanDoc.Syntax.ref
       "["
       (str "\"lean\"")
       "]"))])
   (LeanDoc.Syntax.link_ref
    "["
    (str "\"lean\"")
    "]:"
    (str "\"https://lean-lang.org\""))
   (LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text (str "\"hello\""))])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "[My link][lean]\n\n[lean]: https://lean-lang.org\nhello"

/--
info: Success! Final stack:
  [(LeanDoc.Syntax.para
    [(LeanDoc.Syntax.text (str "\"Blah blah\""))
     (LeanDoc.Syntax.footnote
      "[^"
      (str "\"1\"")
      "]")])
   (LeanDoc.Syntax.footnote_ref
    "[^"
    (str "\"1\"")
    "]:"
    [(LeanDoc.Syntax.text
      (str "\"More can be said\""))])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "Blah blah[^1]\n\n[^1]: More can be said"
