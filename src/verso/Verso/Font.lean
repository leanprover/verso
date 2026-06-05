/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public meta import Lean.Elab.Command
public import VersoUtil.BinFiles

set_option linter.missingDocs true
set_option doc.verso true

namespace Verso

/-- Whether a font is upright or italic. -/
public inductive FontStyle where
  | normal
  | italic
deriving DecidableEq, Repr, Hashable

/-- The CSS {lit}`font-style` declaration for a style. -/
public def FontStyle.toCss (s : FontStyle) : String :=
  "font-style: " ++
  match s with
  | .normal => "normal;"
  | .italic => "italic;"

/--
A font weight in the CSS range 1–1000 (e.g. 400 for regular, 700 for bold).
-/
public structure Weight where
  /-- The numeric weight, between 1 and 1000 inclusive. -/
  val : Nat
  /-- The weight is at least 1. -/
  lo : 1 ≤ val := by grind
  /-- The weight is at most 1000. -/
  hi : val ≤ 1000 := by grind

/--
Numeric literals can be use for weights.

They are clamped into the valid 1–1000 range, so a weight can be written as a plain number with no
proof at the call site.
-/
public instance (n : Nat) : OfNat Weight n where
  ofNat.val := max 1 (min 1000 n)

namespace Weight

/-- Thin (100). -/
public abbrev thin : Weight := 100
/-- Extra light (200). -/
public abbrev extraLight : Weight := 200
/-- Light (300). -/
public abbrev light : Weight := 300
/-- Regular (400). -/
public abbrev regular : Weight := 400
/-- Medium (500). -/
public abbrev medium : Weight := 500
/-- Semibold (600). -/
public abbrev semibold : Weight := 600
/-- Bold (700). -/
public abbrev bold : Weight := 700
/-- Extra bold (800). -/
public abbrev extraBold : Weight := 800
/-- Black (900). -/
public abbrev black : Weight := 900

end Weight

/-- A font file format. -/
public inductive FontFormat where
  | woff2
  | woff
  | otf
  | ttf
deriving DecidableEq, Repr

/--
The format hint for this file kind: the string written inside CSS {lit}`format("...")` in the
{lit}`src` entry of a {lit}`@font-face` rule (for example, {lit}`"woff2"` or {lit}`"opentype"`).
-/
public def FontFormat.css : FontFormat → String
  | .woff2 => "woff2"
  | .woff => "woff"
  | .otf => "opentype"
  | .ttf => "truetype"

/--
The weight or weights provided by a single font file: one fixed weight, or a variable-font range
carrying a proof that the low weight does not exceed the high weight.
-/
public inductive FaceWeights where
  | fixed (weight : Weight)
  | variable (lo hi : Weight) (le : lo.val ≤ hi.val := by grind)

/-- One font file: the weights and style it provides, its format, and its embedded bytes. -/
public structure FontFace where
  /-- The weight or weight range this file provides. -/
  weights : FaceWeights := .fixed .regular
  /-- The style (upright or italic) this file provides. -/
  style : FontStyle := .normal
  /-- The file's format. -/
  format : FontFormat
  /-- The file's contents, embedded at compile time. -/
  bytes : ByteArray

/--
{open Typeface}

A concrete font for theme text. The {name}`sans`, {name}`serif`, and {name}`mono` constructors refer
to some arbitrary built-in family that may vary from system to system, while {name}`files` is used
to refer to specific files.
-/
public inductive Typeface where
  /-- Some sans-serif font -/
  | sans
  /-- Some serif font -/
  | serif
  /-- Some monospace font -/
  | mono
  /-- A specific font, provided as files -/
  | files (family : String) (faces : Array FontFace)

/-- Quotes a CSS string, escaping backslashes and double quotes so the name cannot break out. -/
public def cssQuote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"") ++ "\""

/--
The CSS {lit}`font-family` value for a typeface.
-/
public def Typeface.cssFamily : Typeface → String
  | .sans => "ui-sans-serif, system-ui, sans-serif"
  | .serif => "ui-serif, Georgia, Cambria, serif"
  | .mono => "ui-monospace, SFMono-Regular, Menlo, Consolas, monospace"
  | .files family _ => cssQuote family

/--
The fontspec family name that LuaLaTeX should pick for a typeface. The built-in
{name (full := Verso.Typeface.sans)}`sans`/{name (full := Verso.Typeface.serif)}`serif`/{name (full := Verso.Typeface.mono)}`mono`
typefaces fall back to a system family known to ship with TeXLive's LuaLaTeX bundle; a
{name (full := Verso.Typeface.files)}`files` typeface uses its declared family name directly so
the corresponding fontspec files loaded elsewhere in the preamble resolve.
-/
public def Typeface.texFamily : Typeface → String
  | .sans => "DejaVu Sans"
  | .serif => "DejaVu Serif"
  | .mono => "DejaVu Sans Mono"
  | .files family _ => family

/-! # Defining font faces -/

/--
Defines a {name}`FontFace` whose {name}`FontFace.bytes` are embedded from a file at compile time.

The fields, in any order: {lit}`format` (required), {lit}`file` (required, a string literal path
relative to the current source file), {lit}`weights` (defaults to {lean}`(.fixed .regular : FaceWeights)`),
{lit}`weight` (sugar: {lit}`weight := w` is rewritten to a fixed-weight value), and {lit}`style`
(defaults to {lean}`(.normal : FontStyle)`). For example:

```
define_font_face sourceSansVariable where
  weights := .variable .thin .black
  format := .ttf
  file := "fonts/SourceSans3-VF.ttf"
```
-/
syntax (name := defineFontFace) "define_font_face " ident " where" manyIndent(group(withPosition(ident " := " colGt term))) : command

open Lean Elab Command in
/-- Elaborates a {kw (of := Verso.defineFontFace)}`define_font_face` command into a {name}`FontFace` definition. -/
@[command_elab defineFontFace]
public meta def elabDefineFontFace : CommandElab := fun stx => do
  let nameIdent := stx[1]
  let mut weights? : Option Term := none
  let mut style? : Option Term := none
  let mut format? : Option Term := none
  let mut file? : Option (TSyntax `str) := none
  for f in stx[3].getArgs do
    let key := f[0].getId
    let val : Term := ⟨f[2]⟩
    match key with
    | `weights => weights? := some val
    | `weight => weights? := some (← `(Verso.FaceWeights.fixed $val))
    | `style => style? := some val
    | `format => format? := some val
    | `file =>
      if f[2].isStrLit?.isSome then file? := some ⟨f[2]⟩
      else throwErrorAt f[2] "the `file` field must be a string literal"
    | other => throwErrorAt f[0] s!"unknown field `{other}`; expected weights, weight, style, format, or file"
  let some format := format?
    | throwError "`define_font_face` requires a `format` field"
  let some file := file?
    | throwError "`define_font_face` requires a `file` field"
  let weights ←
    match weights? with
    | some w => pure w
    | none => ``(Verso.FaceWeights.fixed Verso.Weight.regular)
  let style ←
    match style? with
    | some s => pure s
    | none => ``(Verso.FontStyle.normal)
  let name : Ident := ⟨nameIdent⟩
  elabCommand <| ←
    `(public def $name : Verso.FontFace :=
        { weights := $weights, style := $style, format := $format, bytes := include_bin $file })
