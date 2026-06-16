/-
Copyright (c) 2023 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Parser.Types
public import Std.Data.TreeMap
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
Returns an `InputContext` and start position for parsing the contents of a string literal that was
part of the original source file.

Throws an error if the string literal has no source position (e.g. because it was created by a
macro or quotation rather than parsed from the source). The end position is clamped to the end of
the source.
-/
public def strLitInputContext [Monad m] [MonadFileMap m] [MonadError m] (str : Syntax) (fileName : String) : m (InputContext × String.Pos.Raw) := do
  let some startPos := str.getPos?
    | throwErrorAt str "Expected an original string literal with source positions, but it has none"
  let endPos := str.getTailPos?.getD startPos
  let text ← getFileMap
  let endPos := if endPos > text.source.rawEndPos then text.source.rawEndPos else endPos
  let ictx := Parser.mkInputContext text.source fileName (endPos := endPos) (endPos_valid := by grind)
  return (ictx, startPos)

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

open Lean.Syntax in
/--
Decodes the region of `source` between `startPos` and `stopPos`, which holds the bare contents of a
string literal (no surrounding quotes), applying escape sequences. Returns the decoded string and a
map from decoded byte positions to absolute source positions.

The map records, for each decoded character, the position where its source representation begins,
followed by a final entry pairing the end of the decoded string with `stopPos`.
-/
public def decodeContentWithMap (source : String) (startPos stopPos : String.Pos.Raw) :
    String × Std.TreeMap String.Pos.Raw String.Pos.Raw := Id.run do
  let mut i := startPos
  let mut decoded := ""
  let mut map : Std.TreeMap String.Pos.Raw String.Pos.Raw := {}
  while i.byteIdx < stopPos.byteIdx do
    let c := i.get source
    if c == '\\' then
      if let some (ch, i') := decodeQuotedChar source (i.next source) then
        map := map.insert decoded.rawEndPos i
        decoded := decoded.push ch
        i := i'
      else if let some i' := decodeStringGap source (i.next source) then
        i := i'
      else
        break
    else
      map := map.insert decoded.rawEndPos i
      decoded := decoded.push c
      i := i.next source
  return (decoded, map.insert decoded.rawEndPos i)

/--
Decodes the contents of a string literal, returning the decoded string together with a map from byte
positions in the decoded string to absolute byte positions in `source`. `startPos` and `stopPos`
delimit the literal, including its quotes, within `source`.
-/
public def decodeStrLitWithMap (source : String) (startPos stopPos : String.Pos.Raw) :
    String × Std.TreeMap String.Pos.Raw String.Pos.Raw :=
  if startPos.get source == 'r' then Id.run do
    -- Raw string literals are not escape-decoded.
    let mut i := startPos.next source
    let mut num := 0
    while i.get source == '#' do
      num := num + 1
      i := i.next source
    let contentStart := i.next source
    let contentClose : String.Pos.Raw := ⟨stopPos.byteIdx - (num + 1)⟩
    let decoded := contentStart.extract source contentClose
    return (decoded, Std.TreeMap.empty.insert ⟨0⟩ contentStart |>.insert decoded.rawEndPos contentClose)
  else
    -- The contents lie between the opening and closing quotes.
    decodeContentWithMap source (startPos.next source) ⟨stopPos.byteIdx - 1⟩

/--
Maps a byte position in a decoded string to the corresponding absolute source position, using a map
produced by `decodeStrLitWithMap`.
-/
public def mapDecodedPos (map : Std.TreeMap String.Pos.Raw String.Pos.Raw) (p : String.Pos.Raw) :
    String.Pos.Raw :=
  match map.getEntryLE? p with
  | some (decodedPos, sourcePos) => ⟨sourcePos.byteIdx + (p.byteIdx - decodedPos.byteIdx)⟩
  | none => p

private def remapSubstring (source : String) (mapPos : String.Pos.Raw → String.Pos.Raw)
    (w : Substring.Raw) : Substring.Raw :=
  { str := source, startPos := mapPos w.startPos, stopPos := mapPos w.stopPos }

private def remapSourceInfo (source : String) (mapPos : String.Pos.Raw → String.Pos.Raw) :
    SourceInfo → SourceInfo
  | .original leading pos trailing endPos =>
    .original
      (remapSubstring source mapPos leading) (mapPos pos)
      (remapSubstring source mapPos trailing) (mapPos endPos)
  | .synthetic pos endPos canonical =>
    .synthetic (mapPos pos) (mapPos endPos) canonical
  | .none => .none

/--
Rewrites every source position in `stx`, mapping positions in a decoded string back to absolute
positions in `source`. The leading and trailing whitespace of original tokens is reanchored to
`source`, so the syntax round-trips back to the original text.
-/
public partial def remapSyntaxPos (source : String) (mapPos : String.Pos.Raw → String.Pos.Raw) :
    Syntax → Syntax
  | .node info kind args =>
    .node (remapSourceInfo source mapPos info) kind (args.map (remapSyntaxPos source mapPos))
  | .atom info val =>
    .atom (remapSourceInfo source mapPos info) val
  | .ident info rawVal val preresolved =>
    .ident (remapSourceInfo source mapPos info) rawVal val preresolved
  | .missing => .missing

/--
Parses an original string literal.

The provided string literal is used only for source positions; the `FileMap` is used to acquire the
actual string contents. When the literal's source text differs from its contents because of escape
sequences, the decoded contents are parsed and the resulting positions are mapped back to the
source.
-/
public def parseStrLitWith [Monad m] [MonadLog m] [MonadEnv m] [MonadOptions m] [MonadError m] [AddMessageContext m] (p : ParserFn) (input : StrLit) : m Syntax := do
  let text ← getFileMap
  if let some startPos := input.raw.getPos? then
    let endPos := input.raw.getTailPos?.getD startPos
    let stopPos := if endPos > text.source.rawEndPos then text.source.rawEndPos else endPos
    if startPos.extract text.source stopPos != input.getString then
      let (decoded, posMap) := decodeContentWithMap text.source startPos stopPos
      if decoded == input.getString then
        return ← parseDecoded p decoded (mapDecodedPos posMap) text
  -- The contents appear verbatim in the source: parse it directly for exact source positions.
  let (ictx, startPos) ← strLitInputContext input.raw (← getFileName)
  let s := { mkParserState text.source with pos := startPos }
  let env ← getEnv
  let s := p.run ictx { env, options := ← getOptions } (getTokenTable env) s
  if !s.allErrors.isEmpty then
    for (pos, stk, err) in s.allErrors do
      let err := mkSyntaxError ictx pos stk err
      let start := text.ofPosition err.pos
      let stop := text.ofPosition err.endPos
      let blame := Syntax.mkStrLit (start.extract text.source stop)
      logErrorAt blame err.text
    return .missing
  else if ictx.atEnd s.pos then
    return s.stxStack.back
  else
    throwErrorAt input "Unparsed input: `{s.pos.extract text.source ictx.endPos}`"
where
  parseDecoded (p : ParserFn) (decoded : String) (mapPos : String.Pos.Raw → String.Pos.Raw) (text : FileMap) : m Syntax := do
    let env ← getEnv
    let ictx := mkInputContext decoded (← getFileName)
    let s := p.run ictx { env, options := ← getOptions } (getTokenTable env) (mkParserState decoded)
    if !s.allErrors.isEmpty then
      for (pos, stk, err) in s.allErrors do
        let serr := mkSyntaxError ictx pos stk err
        logErrorAt (Syntax.atom (.synthetic (mapPos pos) (mapPos pos)) "") serr.text
      return .missing
    else if ictx.atEnd s.pos then
      return remapSyntaxPos text.source mapPos s.stxStack.back
    else
      throwErrorAt input "Unparsed input: `{s.pos.extract decoded ictx.endPos}`"

/--
Parses an original string literal as part of a syntax category.

The provided string literal is used only for source positions; the `FileMap` is used to acquire the
actual string contents.
-/
public def parseStrLitAsCategory [Monad m] [MonadLog m] [MonadEnv m] [MonadOptions m] [MonadError m] [AddMessageContext m] (catName : Name) (input : StrLit) : m Syntax :=
  parseStrLitWith (andthenFn whitespace (categoryParserFnImpl catName)) input

/--
Parses the contents of a string literal as Verso markup using `p`, producing syntax whose source
positions are absolute positions in the enclosing file. Escape sequences are decoded before parsing,
and the resulting positions are mapped back to the original source.

When the literal has no source position (for example, one synthesized by a macro), the contents are
parsed directly and positions refer to the decoded string.
-/
public def parseMarkupStrLit [Monad m] [MonadFileMap m] [MonadEnv m] [MonadError m]
    (p : ParserFn) (s : StrLit) : m Syntax := do
  let text ← getFileMap
  let env ← getEnv
  let pmctx : ParserModuleContext := { env, options := {} }
  let (input, mapPos, remap) :=
    match s.raw.getPos?, s.raw.getTailPos? with
    | some startPos, some stopPos =>
      let (input, posMap) := decodeStrLitWithMap text.source startPos stopPos
      if input == s.getString then
        let mapPos := mapDecodedPos posMap
        (input, mapPos, remapSyntaxPos text.source mapPos)
      else
        (s.getString, id, id)
    | _, _ => (s.getString, id, id)
  let st := p.run (mkInputContext input "<string literal>") pmctx (getTokenTable env) (mkParserState input)
  if st.allErrors.isEmpty then
    if st.stxStack.size = 1 then
      return remap st.stxStack.back
    else
      throwError "Unexpected syntax from Verso parser: expected a single node, got {st.stxStack.size}"
  else
    let mut msg := "Failed to parse Verso markup:"
    for (errPos, _, e) in st.allErrors do
      let pos := text.toPosition (mapPos errPos)
      msg := msg ++ s!"\n  {pos.line}:{pos.column}: {toString e}"
    let blamePos := mapPos (((st.allErrors[0]?).map (·.1)).getD ⟨0⟩)
    throwErrorAt (Syntax.atom (.synthetic blamePos blamePos) "") msg

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
