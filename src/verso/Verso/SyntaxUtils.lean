/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Parser.Types
public meta import Verso.Instances
import Verso.Instances
import Verso.Method

namespace Verso.Parser
-- TODO: make public upstream and delete these

open Lean Doc Parser


public def textLine (allowNewlines := true) : ParserFn := many1Fn (inline { allowNewlines })

public def nl := satisfyFn (· == '\n') "newline"

/--
Parses a line that contains only spaces.
-/
public def blankLine : ParserFn :=
  nodeFn `blankLine <| atomicFn <| asStringFn <| takeWhileFn (· == ' ') >> nl

private def skipToNewline : ParserFn :=
    takeUntilFn (· == '\n')

private def skipRestOfLine : ParserFn :=
    skipToNewline >> (eoiFn <|> nl)

/--
Consumes the rest of the current line and any subsequent non-empty lines in order to reach the
end of the block.
-/
public def skipBlock : ParserFn :=
  skipToNewline >> manyFn nonEmptyLine >> takeWhileFn (· == '\n')
where
  nonEmptyLine : ParserFn :=
    atomicFn <|
      chFn '\n' >>
      takeWhileFn (fun c => c.isWhitespace && c != '\n') >>
      satisfyFn (!·.isWhitespace) "non-whitespace" >> skipToNewline


/--
Recovers from a parse error by skipping input until one or more complete blank lines has been
skipped.

The provided `stxs` are pushed to the stack upon recovery.
-/
public def recoverBlockWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    ignoreFn skipBlock >>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.shrinkStack rctx.initialSize) (·.pushSyntax ·)


end Verso.Parser

namespace Verso.SyntaxUtils

open Lean Parser
open Std.Format


public defmethod Syntax.getPos! (stx : Syntax) : String.Pos.Raw :=
  if let some pos := stx.getPos? then pos else panic! s!"No position for {stx}"

public defmethod SourceInfo.getPos! (info : SourceInfo) : String.Pos.Raw :=
  if let some pos := info.getPos? then pos else panic! s!"No position for {repr info}"

public def ppSyntax (stx : Syntax) : Std.Format := .nest 2 <| stx.formatStx (some 50) false

public def ppStack (elts : Array Syntax) (number : Bool := false) : Std.Format := Id.run do
  let mut stk : Format := .nil
  if h : elts.size = 0 then
    stk := " empty"
  else if elts.size = 1 then
    stk := "  " ++ ppSyntax elts[0]
  else
    for h : i in [0:elts.size] do
      let tm := ppSyntax (elts[i])
      let num := if number then .text s!"[{i}] " else .nil
      stk := stk ++ .group (" • " ++ num ++ nest 2 (.group tm)) ++ line
  pure stk

public defmethod ParserFn.test (p : ParserFn) (input : String) : IO String := do
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let pmctx : ParserModuleContext := {env := env, options := {}}
  let s' := p.run ictx pmctx (getTokenTable env) (mkParserState input)
  let stk := ppStack <| s'.stxStack.extract 0 s'.stxStack.size

  let remaining : String :=
    if s'.pos ≥ input.rawEndPos then "All input consumed."
    else s!"Remaining:\n{repr (s'.pos.extract input input.rawEndPos)}"

  if s'.allErrors.isEmpty then
    return s!"Success! Final stack:\n{stk.pretty 50}\n{remaining}"
  else if let #[(p, _, err)] := s'.allErrors then
    return s!"Failure @{p} ({ictx.fileMap.toPosition p}): {toString err}\nFinal stack:\n{stk.pretty 50}\nRemaining: {repr $ p.extract input input.rawEndPos}"
  else
    let mut errors := ""
    for (p, _, e) in s'.allErrors.qsort (fun x y => x.1 < y.1 || x.1 == y.1 && toString x.2.2 < toString y.2.2)  do
      errors := errors ++ s!"  @{p} ({ictx.fileMap.toPosition p}): {toString e}\n    {repr <| p.extract input input.rawEndPos}\n"
    return s!"{s'.allErrors.size} failures:\n{errors}\nFinal stack:\n{stk.pretty 50}"

public defmethod ParserFn.test! (p : ParserFn) (input : String) : IO Unit :=
  p.test input >>= IO.println

public section
/-- A more convenient concrete syntax for low-level syntax objects,
without needing to involve the Lean parser. Useful when working at the
ParserFn level.-/
declare_syntax_cat lowStx
syntax str : lowStx
syntax "[" lowStx* "]" : lowStx
syntax "(" ident lowStx* ")" : lowStx
/-- Embed a term into syntax -/
syntax "~" term:100 : lowStx
/-- Embed a string atom into syntax -/
syntax "~~" term:100 : lowStx

/-- Embedded low-level syntax -/
syntax "`<low|" lowStx ">" : term
macro_rules
  | `( `<low| $s:str > ) => ``(Syntax.atom $(quote s.raw.getHeadInfo) $(quote s.getString))
  | `( `<low| [ $stx* ] > ) => ``(Syntax.node SourceInfo.none nullKind #[ $[`<low| $stx > ],* ] )
  | `( `<low| ( $id $stx* ) > ) => ``(Syntax.node SourceInfo.none $(quote id.getId) #[ $[`<low| $stx > ],* ] )
  | `( `<low| ~$e > ) => ``(($e : Syntax))
  | `( `<low| ~~$e > ) => ``(Syntax.atom _ $e)
end

/--
Given a string literal, constructs a Lean string that can be parsed by the Lean parser, yielding
correct source positions for items in the string literal.
-/
public def parserInputString [Monad m] [MonadFileMap m]
    (str : TSyntax `str) :
    m String := do
  let text ← getFileMap
  let preString := (0 : String.Pos.Raw).extract text.source (str.raw.getPos?.getD 0)
  let mut code := ""
  let mut iter := preString.startPos
  while h : iter ≠ preString.endPos do
    let c := iter.get h
    iter := iter.next h
    if c == '\n' then
      code := code.push '\n'
    else
      for _ in [0:c.utf8Size] do
        code := code.push ' '
  let strOriginal? : Option String := do
    let ⟨start, stop⟩ ← str.raw.getRange?
    start.extract text.source stop
  code := code ++ strOriginal?.getD str.getString
  return code


public structure SyntaxError where
  pos : Position
  endPos : Position
  text : String
deriving ToJson, FromJson, BEq, Repr, Quote



-- Based on mkErrorMessage used in Lean upstream - keep them in synch for best UX
open Lean.Parser in
private partial def mkSyntaxError (c : InputContext) (pos : String.Pos.Raw) (stk : SyntaxStack) (e : Parser.Error) : SyntaxError := Id.run do
  let mut pos := pos
  let mut endPos? := none
  let mut e := e
  unless e.unexpectedTk.isMissing do
    -- calculate error parts too costly to do eagerly
    if let some r := e.unexpectedTk.getRange? then
      pos := r.start
      endPos? := some r.stop
    let unexpected := match e.unexpectedTk with
      | .ident .. => "unexpected identifier"
      | .atom _ v => s!"unexpected token '{v}'"
      | _         => "unexpected token"  -- TODO: categorize (custom?) literals as well?
    e := { e with unexpected }
    -- if there is an unexpected token, include preceding whitespace as well as the expected token could
    -- be inserted at any of these places to fix the error; see tests/lean/1971.lean
    if let some trailing := lastTrailing stk then
      if trailing.stopPos == pos then
        pos := trailing.startPos
  return {
    pos := c.fileMap.toPosition pos
    endPos := (c.fileMap.toPosition <$> endPos?).getD (c.fileMap.toPosition (pos + c.get pos))
    text := toString e
  }
where
  -- Error recovery might lead to there being some "junk" on the stack
  lastTrailing (s : SyntaxStack) : Option Substring.Raw :=
    s.toSubarray.findSomeRevM? (m := Id) fun stx =>
      if let .original (trailing := trailing) .. := stx.getTailInfo then pure (some trailing)
        else none

public defmethod ParserFn.parseString [Monad m] [MonadError m] [MonadEnv m] (p : ParserFn) (input : String) : m Syntax := do
  let ictx := mkInputContext input "<input>"
  let env ← getEnv
  let pmctx : ParserModuleContext := {env := env, options := {}}
  let s' := p.run ictx pmctx (getTokenTable env) (mkParserState input)
  let stk := s'.stxStack.extract 0 s'.stxStack.size
  if let some err := s'.errorMsg then
    throwError err.toString
  if s'.recoveredErrors.size > 0 then
    throwError String.intercalate "\n" <| Std.HashSet.toList <| Std.HashSet.ofArray <|
      s'.recoveredErrors.map fun (p, s, e) =>
        let err := mkSyntaxError ictx p s e
        err.text
  if h : stk.size ≠ 1 then
    throwError "Expected single item in parser stack, got {ppStack stk}"
  else
    pure stk[0]


open Lean.Parser in
/--
Runs a parser category, returning any errors encountered as a list of position-string pairs.
-/
public def runParserCategory
    (env : Environment) (opts : Lean.Options) (catName : Name)
    (input : String) (fileName : String := "<example>") :
    Except (List (Position × String)) Syntax :=
  let p := andthenFn whitespace (categoryParserFnImpl catName)
  let ictx := mkInputContext input fileName
  let s := p.run ictx { env, options := opts } (getTokenTable env) (mkParserState input)
  if !s.allErrors.isEmpty then
    Except.error (toErrorMsg ictx s)
  else if ictx.atEnd s.pos then
    Except.ok s.stxStack.back
  else
    Except.error (toErrorMsg ictx (s.mkError "end of input"))
where
  toErrorMsg (ctx : InputContext) (s : ParserState) : List (Position × String) := Id.run do
    let mut errs := []
    for (pos, _stk, err) in s.allErrors do
      let pos := ctx.fileMap.toPosition pos
      errs := (pos, toString err) :: errs
    errs.reverse

open Lean.Parser in
/--
Runs a parser category, returning any errors encountered as `SyntaxError`s, with the source spans
computed the way Lean does.
-/
public def runParserCategory' (env : Environment) (opts : Lean.Options) (catName : Name) (input : String) (fileName : String := "<example>") : Except (Array SyntaxError) Syntax :=
    let p := andthenFn whitespace (categoryParserFnImpl catName)
    let ictx := mkInputContext input fileName
    let s := p.run ictx { env, options := opts } (getTokenTable env) (mkParserState input)
    if !s.allErrors.isEmpty then
      Except.error <| toSyntaxErrors ictx s
    else if ictx.atEnd s.pos then
      Except.ok s.stxStack.back
    else
      Except.error (toSyntaxErrors ictx (s.mkError "end of input"))
where
  toSyntaxErrors (ictx : InputContext) (s : ParserState) : Array SyntaxError :=
    s.allErrors.map fun (pos, stk, e) => (mkSyntaxError ictx pos stk e)

end Verso.SyntaxUtils
