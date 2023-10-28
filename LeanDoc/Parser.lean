import Lean
import Std.Tactic.GuardMsgs

import LeanDoc.SyntaxUtils

namespace LeanDoc.Parser


open LeanDoc.SyntaxUtils
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

private def asStringAux  (startPos : String.Pos) : ParserFn := fun c s =>
  let input   := c.input
  let stopPos := s.pos
  let leading := mkEmptySubstringAt input startPos
  let val     := input.extract startPos stopPos
  let trailing := mkEmptySubstringAt input stopPos
  let atom     := mkAtom (SourceInfo.original leading startPos trailing (startPos + val)) val
  s.pushSyntax atom

/-- Match an arbitrary Parser and return the consumed String in a `Syntax.atom`. -/
def asStringFn (p : ParserFn) : ParserFn := fun c s =>
  let startPos := s.pos
  let iniSz := s.stxStack.size
  let s := p c s
  if s.hasError then s
  else asStringAux startPos c (s.shrinkStack iniSz)

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

def blankLine : ParserFn := nodeFn `blankLine <| atomicFn <| asStringFn <| takeWhileFn (· == ' ') >> nl

def bullet := satisfyFn (· == '*') "bullet (*)"

/-- Characters with a special meaning during a line (we already know we're reading inlines) -/
def specialChars := "*\n[]".toList

def isSpecial (c : Char) : Bool := c ∈ specialChars

def notSpecial := satisfyEscFn (not ∘ isSpecial)

/-- Block opener prefixes -/
def blockOpener := atomicFn <|
  takeWhileEscFn (· == ' ') >>
  (atomicFn ((bullet >> chFn ' ')) <|>
   atomicFn (atLeastFn 3 (chFn ':')) <|>
   atomicFn (atLeastFn 3 (chFn '`')) <|>
   atomicFn (chFn '>'))


/--
info: Success! Final stack:
 empty
All input consumed.
-/
#guard_msgs in
  #eval notSpecial.test! "a"

/--
info: Success! Final stack:
 empty
All input consumed.
-/
#guard_msgs in
  #eval notSpecial.test! "b"

/--
info: Success! Final stack:
 empty
All input consumed.
-/
#guard_msgs in
  #eval notSpecial.test! "\\*"

/--
info: Success! Final stack:
 empty
All input consumed.
-/
#guard_msgs in
  #eval notSpecial.test! "\\>"

structure InlineCtxt where
  -- The minimum indentation of a continuation line for the current paragraph
  minIndent : Nat := 0
  -- How many asterisks introduced the current level of emphasis? `none` means no emphasis here.
  emphDepth : Option Nat := none
  -- Are we in a link?
  inLink : Bool := false

deriving Inhabited


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

/- Parsing inlines:
 * Inline parsers may not consume trailing whitespace, and must be robust in the face of leading whitespace
-/

/--
A linebreak that isn't a block break (that is, there's non-space content on the next line)
-/
def linebreak := nodeFn `linebreak <| asStringFn <| atomicFn (chFn '\n' >> lookaheadFn (manyFn (chFn ' ') >> notFollowedByFn (chFn '\n' <|> atLeastFn 3 (chFn ':')) "newline"))

mutual
  partial def emph (ctxt : InlineCtxt) : ParserFn :=
    nodeFn `emph <|
    withCurrentColumn fun c =>
      atomicFn (asStringFn (asStringFn (opener ctxt) >> notFollowedByFn (chFn ' ' false <|> chFn '\n' false) "space or newline after opener")) >>
      withCurrentColumn fun c' =>
        let count := c' - c
        manyFn (inline {ctxt with emphDepth := some count}) >>

        asStringFn (atomicFn (noSpaceBefore >> repFn count (satisfyFn (· == '*') s!"{count} asterisks")))

  where
    opener (ctxt : InlineCtxt) : ParserFn :=
      match ctxt.emphDepth with
      | none => many1Fn (satisfyFn (· == '*') s!"any number of *s")
      | some 1 | some 0 => fun _ s => s.mkError "Can't emphasize here"
      | some d => atMostFn (d - 1) (satisfyFn (· == '*') "*") s!"at most {d} *s"
    noSpaceBefore : ParserFn := fun c s =>
      if s.pos == 0 then s
      else
        let prior := c.input.get (c.input.prev s.pos)
        if prior.isWhitespace then
          s.mkError "closer without preceding space"
        else s


  -- Read a prefix of a line of text, stopping at a text-mode special character
  partial def text :=
    nodeFn `text (asStringFn (atomicFn (manyFn (chFn ' ') >> notSpecial) >> takeUntilEscFn isSpecial))

  partial def link (ctxt : InlineCtxt) :=
    nodeFn `link <|
      (atomicFn (notInLink >> strFn "[" )) >>
      many1Fn (inline {ctxt with inLink := true}) >>
      strFn "]" >>
      (ref <|> url)
  where
    notUrlEnd := satisfyEscFn (· ∉ ")\n".toList) >> takeUntilEscFn (· ∈ ")\n".toList)
    notRefEnd := satisfyEscFn (· ∉ "]\n".toList) >> takeUntilEscFn (· ∈ "]\n".toList)
    notInLink : ParserFn := fun _ s =>
      if ctxt.inLink then s.mkError "Already in a link" else s
    ref : ParserFn := nodeFn `ref ((atomicFn <| strFn "[") >> asStringFn notRefEnd >> strFn "]")
    url : ParserFn := nodeFn `url ((atomicFn <| strFn "(") >> asStringFn notUrlEnd >> strFn ")")



  partial def inline (ctxt : InlineCtxt) : ParserFn :=
    text <|> emph ctxt <|> linebreak <|> link ctxt
end

def textLine : ParserFn := many1Fn (inline {})

/--
info: Success! Final stack:
  (text "abc ")
All input consumed.
-/
#guard_msgs in
  #eval text.test! "abc "

/--
info: Success! Final stack:
  (emph "*" [(text "aa")] "*")
All input consumed.
-/
#guard_msgs in
  #eval emph {} |>.test! "*aa*"

/--
info: Failure: expected closer without preceding space
Final stack:
  (emph "*" [(text "aa ")] <missing>)
Remaining: "*"
-/
#guard_msgs in
  #eval emph {} |>.test! "*aa *"

/--
info: Failure: unexpected space or newline after opener
Final stack:
  (emph "*" <missing>)
Remaining: "* aa*"
-/
#guard_msgs in
  #eval emph {} |>.test! "* aa*"

/--
info: Success! Final stack:
  (emph "**" [(text "aa")] "**")
All input consumed.
-/
#guard_msgs in
  #eval emph {} |>.test! "**aa**"

/--
info: Success! Final stack:
  (emph
   "**"
   [(text "aa") (linebreak "\n") (text "bb")]
   "**")
All input consumed.
-/
#guard_msgs in
  #eval inline {} |>.test! "**aa\nbb**"


/--
info: Success! Final stack:
  (link
   "["
   [(text "Wikipedia")]
   "]"
   (url "(" "https://en.wikipedia.org" ")"))
All input consumed.
-/
#guard_msgs in
  #eval inline {} |>.test! "[Wikipedia](https://en.wikipedia.org)"


def name : ParserFn := asStringFn <| satisfyFn (·.isAlpha) >> takeWhileFn (fun ch => ch.isAlpha || ch.isDigit || ch ∈ "_'".toList)

def val : ParserFn := num <|> nameArg <|> str
where
  num := nodeFn `num <| asStringFn <| atomicFn (takeWhile1Fn (·.isDigit) "digits")
  nameArg := nodeFn `name <| name
  strContents := asStringFn <| takeUntilEscFn (· ∈ "\"\n".toList)
  str := nodeFn `string <| asStringFn <| atomicFn (chFn '\"') >> strContents >> chFn '\"'

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
info: Failure: unexpected end of input
Final stack:
  (string <missing>)
Remaining: ""
-/
#guard_msgs in
  #eval val.test! ""

/--
info: Success! Final stack:
  (string "\"a b c\\ d\"")
All input consumed.
-/
#guard_msgs in
  #eval val.test! "\"a b c\\ d\""

def withCurrentStackSize (p : Nat → ParserFn) : ParserFn := fun c s =>
  p s.stxStack.size c s

/-- Match the character indicated, pushing nothing to the stack in case of success -/
def skipChFn (c : Char) : ParserFn :=
  satisfyFn (· == c) c.toString

def arg : ParserFn :=
  withCurrentStackSize fun iniSz =>
    atomicFn name >> eatSpaces >>
    ((atomicFn (skipChFn '=') >> eatSpaces >> val >> eatSpaces >> mkNamed iniSz) <|> mkAnon iniSz)

where
  mkNamed (iniSz : Nat) : ParserFn := fun _ s => s.mkNode `arg.named iniSz
  mkAnon (iniSz : Nat) : ParserFn := fun _ s => s.mkNode `arg.anon iniSz
  eatSpaces := takeWhileFn (· == ' ')

/--
info: Success! Final stack:
  (arg.anon "x")
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "x"

/--
info: Success! Final stack:
  (arg.named "x" (num "1"))
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "x=1"

/--
info: Success! Final stack:
  (arg.named "x" (name "y"))
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "x=y"

/--
info: Success! Final stack:
  (arg.named "x" (string "\"y\""))
All input consumed.
-/
#guard_msgs in
  #eval arg.test! "x=\"y\""

/--
info: Failure: unexpected end of input
Final stack:
 • "x"
 • (string "\"" "y" <missing>)

Remaining: ""
-/
#guard_msgs in
  #eval arg.test! "x=\"y"

def nameAndArgs : ParserFn := eatSpaces >> name >> eatSpaces >> manyFn arg
where
  eatSpaces := takeWhileFn (· == ' ')

/--
info: Success! Final stack:
 • "leanExample"
 • [(arg.named "context" (num "2"))]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context=2"
/--
info: Success! Final stack:
 • "leanExample"
 • [(arg.anon "context")]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context"
/--
info: Success! Final stack:
 • "leanExample"
 • [(arg.anon "context") (arg.anon "more")]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context more"
/--
info: Success! Final stack:
 • "leanExample"
 • [(arg.anon "context")
     (arg.named "more" (string "\"stuff\""))]

All input consumed.
-/
#guard_msgs in
#eval nameAndArgs.test! "leanExample context more=\"stuff\""

structure BlockCtxt where
  minIndent : Nat := 0
  maxDirective : Option Nat := none
deriving Inhabited, Repr

mutual
  partial def listItem (ctxt : BlockCtxt) : ParserFn :=
    nodeFn `li (bulletFn >> withCurrentColumn fun c => manyFn (block {ctxt with minIndent := c}))
  where
    bulletFn := atomicFn <| nodeFn `bullet <|
      takeWhileFn (· == ' ') >>
      pushColumn >>
      -- The outer list block recognizer sets up the minimum indent to be the precise indent of its items
      guardColumn (· == ctxt.minIndent) s!"indentation at {ctxt.minIndent}" >>
      asStringFn (chFn '*' false)

  partial def blockquote (ctxt : BlockCtxt) : ParserFn :=
    atomicFn <| nodeFn `blockquote <|
      takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent >> chFn '>' >>
      withCurrentColumn fun c => many1Fn (block { ctxt with minIndent := c })

  partial def list (ctxt : BlockCtxt) : ParserFn :=
    nodeFn `ul <|
      atomicFn (bol >> takeWhileFn (· == ' ') >> ignoreFn (lookaheadFn (chFn '*' >> chFn ' ')) >> guardMinColumn ctxt.minIndent >> pushColumn) >>
      withCurrentColumn (fun c => many1Fn (listItem {ctxt with minIndent := c} ))

  partial def para (ctxt : BlockCtxt) : ParserFn :=
    nodeFn `para <| atomicFn (takeWhileFn (· == ' ') >> notFollowedByFn blockOpener "block opener" >> guardMinColumn ctxt.minIndent) >> textLine

  partial def header : ParserFn :=
    nodeFn `header <|
      atomicFn (bol >> asStringFn (many1Fn (skipChFn '#')) >> skipChFn ' ' >> takeWhileFn (· == ' ') >> lookaheadFn (satisfyFn (· != '\n'))) >>
      textLine

  partial def codeBlock (ctxt : BlockCtxt) : ParserFn :=
    nodeFn `code <|
      -- Opener - leaves indent info and open token on the stack
      atomicFn (takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent >> pushColumn >> asStringFn (atLeastFn 3 (skipChFn '`'))) >>
      withIndentColumn fun c =>
        withCurrentColumn fun c' =>
          let fenceWidth := c' - c
          takeWhileFn (· == ' ') >>
          nameAndArgs >>
          satisfyFn (· == '\n') "newline" >>
          asStringFn (manyFn (codeFrom c fenceWidth)) >>
          closeFence c fenceWidth

  where
    withIndentColumn (p : Nat → ParserFn) : ParserFn := fun c s =>
      let colStx := s.stxStack.get! (s.stxStack.size - 2)
      match colStx with
      | .node _ `column #[.atom _ col] =>
        if let some colNat := col.toNat? then p colNat c s else s.mkError s!"Internal error - not a Nat {col}"
      | other => s.mkError s!"Internal error - not a column node {other}"

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
    nodeFn `directive <|
      -- Opener - leaves indent info and open token on the stack
      atomicFn
        (takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent >> pushColumn >> asStringFn (atLeastFn 3 (skipChFn ':')) >>
         guardOpenerSize) >>
      withIndentColumn fun c =>
        withCurrentColumn fun c' =>
          let fenceWidth := c' - c
          takeWhileFn (· == ' ') >>
          nameAndArgs >>
          satisfyFn (· == '\n') "newline" >>
          blocks {ctxt with minIndent := c, maxDirective := fenceWidth} >>
          closeFence c fenceWidth

  where
    withIndentColumn (p : Nat → ParserFn) : ParserFn := fun c s =>
      let colStx := s.stxStack.get! (s.stxStack.size - 2)
      match colStx with
      | .node _ `column #[.atom _ col] =>
        if let some colNat := col.toNat? then p colNat c s else s.mkError s!"Internal error - not a Nat {col}"
      | other => s.mkError s!"Internal error - not a column node {other}"

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

  partial def block (c : BlockCtxt) := list c <|> header <|> codeBlock c <|> directive c <|> blockquote c <|> para c

  partial def blocks c := sepByFn true (block c) (ignoreFn (many1Fn blankLine))
end

/--
info: Success! Final stack:
  [(para
    [(text
      "This is just some textual content. How is it?")])
   (para [(text "More?")])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "This is just some textual content. How is it?\n\nMore?"

/--
info: Success! Final stack:
  [(para
    [(text
      "I can describe lists like this one:")])
   (ul
    (column "0")
    [(li
      (bullet (column "0") "*")
      [(para [(text "a") (linebreak "\n")])])
     (li
      (bullet (column "0") "*")
      [(para [(text "b")])])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "I can describe lists like this one:\n\n* a\n* b"

/--
info: Success! Final stack:
  (li
   (bullet (column "0") "*")
   [(para [(text "foo") (linebreak "\n")])])
Remaining:
"* bar\n"
-/
#guard_msgs in
  #eval listItem {} |>.test! "* foo\n* bar\n"

/--
info: Success! Final stack:
  [(ul
    (column "0")
    [(li
      (bullet (column "0") "*")
      [(para [(text "foo") (linebreak "\n")])])
     (li
      (bullet (column "0") "*")
      [(para [(text "bar") (linebreak "\n")])])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "* foo\n* bar\n"

/--
info: Success! Final stack:
  [(ul
    (column "0")
    [(li
      (bullet (column "0") "*")
      [(para [(text "foo") (linebreak "\n")])
       (ul
        (column "2")
        [(li
          (bullet (column "2") "*")
          [(para
            [(text "bar") (linebreak "\n")])])])])
     (li
      (bullet (column "0") "*")
      [(para [(text "more outer")])])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "* foo\n  * bar\n* more outer"

/--
info: Success! Final stack:
  [(blockquote
    ">"
    [(para [(text "hey") (linebreak "\n")])])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "> hey\n"

/--
info: Success! Final stack:
  [(para [(text "n\\*k ")])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "n\\*k "

/--
info: Success! Final stack:
  (header "#" [(text "Header!")])
All input consumed.
-/
#guard_msgs in
  #eval header |>.test! "# Header!"

/--
info: Success! Final stack:
  [(header
    "#"
    [(text "Header!") (linebreak "\n")])]
All input consumed.
-/
#guard_msgs in
  #eval blocks {} |>.test! "# Header!\n"

/--
info: Success! Final stack:
  (code
   (column "1")
   "```"
   "scheme"
   []
   " (define x 4)\n x\n"
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ``` scheme\n (define x 4)\n x\n ```"

/--
info: Success! Final stack:
  (code
   (column "0")
   "```"
   "scheme"
   []
   " (define x 4)\n x\n"
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme\n (define x 4)\n x\n```\n"

/--
info: Success! Final stack:
  (code
   (column "0")
   "```"
   "scheme"
   []
   "(define x 4)\nx\n"
   "```")
All input consumed.
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme\n(define x 4)\nx\n```"


/--
info: Failure: expected column 0
Final stack:
  (code
   (column "0")
   "```"
   "scheme"
   []
   "(define x 4)\nx\n"
   <missing>)
Remaining: "````"
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme\n(define x 4)\nx\n ````"

/--
info: Failure: newline
Final stack:
  (code
   (column "0")
   "```"
   "scheme"
   [(arg.named "dialect" (string "\"chicken\""))]
   <missing>)
Remaining: "43\n(define x 4)\nx\n```"
-/
#guard_msgs in
  #eval codeBlock {} |>.test! "``` scheme dialect=\"chicken\" 43\n(define x 4)\nx\n```"

/--
info: Failure: expected column 1
Final stack:
  (code
   (column "1")
   "```"
   "scheme"
   []
   ""
   <missing>)
Remaining: "(define x 4)\nx\n```"
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ``` scheme\n(define x 4)\nx\n```"

/--
info: Failure: expected column 1
Final stack:
  (code
   (column "1")
   "```"
   "scheme"
   []
   " (define x 4)\n x\n"
   <missing>)
Remaining: "```"
-/
#guard_msgs in
  #eval codeBlock {} |>.test! " ``` scheme\n (define x 4)\n x\n```"


/--
info: Success! Final stack:
  (directive
   (column "0")
   "::::"
   "multiPara"
   []
   [(para [(text "foo")])]
   "::::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! ":::: multiPara\nfoo\n::::"

/--
info: Success! Final stack:
  (directive
   (column "1")
   ":::"
   "multiPara"
   [(arg.named
     "greatness"
     (string "\"amazing!\""))]
   [(para [(text "foo")])]
   ":::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! " ::: multiPara greatness=\"amazing!\"\n foo\n :::"

/--
info: Success! Final stack:
  (directive
   (column "1")
   ":::"
   "multiPara"
   []
   [(para [(text "foo")])
    (ul
     (column "2")
     [(li
       (bullet (column "2") "*")
       [(para [(text "List item ")])])])]
   ":::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! " ::: multiPara\n foo\n \n \n \n  * List item \n :::"

/--
info: Success! Final stack:
  (directive
   (column "1")
   ":::"
   "multiPara"
   []
   [(para [(text "foo")])
    (ul
     (column "1")
     [(li
       (bullet (column "1") "*")
       [(para [(text "List item ")])])])]
   ":::")
All input consumed.
-/
#guard_msgs in
  #eval directive {} |>.test! " ::: multiPara\n foo\n\n * List item \n :::"
