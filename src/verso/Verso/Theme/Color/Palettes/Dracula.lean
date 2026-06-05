/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The Dracula and Alucard hex constants below are reproduced from the official Dracula spec at
<https://draculatheme.com/spec>. The Dracula spec is distributed under the MIT license. The
notice is reproduced here verbatim per the license's attribution clause; the manual genre
also includes it in the attribution page of any generated manual that includes a Dracula or
Alucard theme.

  The MIT License (MIT)

  Copyright (c) 2020 Dracula Theme

  Permission is hereby granted, free of charge, to any person obtaining a copy of this
  software and associated documentation files (the "Software"), to deal in the Software
  without restriction, including without limitation the rights to use, copy, modify, merge,
  publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons
  to whom the Software is furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all copies or
  substantial portions of the Software.

  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
  INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR
  PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE
  FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
  OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
  DEALINGS IN THE SOFTWARE.
-/
module

public import Verso.Theme.Color.Basic
public import Verso.Theme.Color.Syntax
public import Verso.Theme.SourceLink

set_option linter.missingDocs true
set_option doc.verso true

/-!
{open Verso.Theme}

The *Dracula* and *Alucard* palettes from the [official Dracula spec](https://draculatheme.com/spec)
as named {name}`Color` constants. The Dracula Classic palette is the canonical dark theme
(Dracula); Alucard Classic is its light-substrate counterpart (named after the *Castlevania*
character, Dracula spelled backwards).

Both palettes share twelve color slots with documented semantic intent. The hex values are
the canonical ones from <https://draculatheme.com/spec>.
-/

namespace Verso.Theme.Color.Palettes

/-! # Dracula Classic — the canonical dark palette -/

namespace DraculaClassic

/-- The palette's display name, suitable as a prefix when naming themes built on it. -/
public def name : String := "Dracula"

/-- The official Dracula spec page, shown in the picker for themes that use this palette. -/
public def sourceLink : SourceLink :=
  { url := "https://draculatheme.com/spec", text := "draculatheme.com/spec" }

/-- Dracula Background ({lit}`#282A36`). Documented role: main background. -/
public def background : Color := color%#282A36
/--
Dracula Current Line ({lit}`#6272A4`). Documented role: semantic current-line highlight
(the active line indicator in editors).
-/
public def currentLine : Color := color%#6272A4
/-- Dracula Selection ({lit}`#44475A`). Documented role: text selection. -/
public def selection : Color := color%#44475A
/-- Dracula Foreground ({lit}`#F8F8F2`). Documented role: default text. -/
public def foreground : Color := color%#F8F8F2
/-- Dracula Comment ({lit}`#6272A4`). Documented role: comments and disabled code. -/
public def comment : Color := color%#6272A4
/-- Dracula Red ({lit}`#FF5555`). Documented role: errors, warnings, deletions. -/
public def red : Color := color%#FF5555
/-- Dracula Orange ({lit}`#FFB86C`). Documented role: numbers, constants, booleans. -/
public def orange : Color := color%#FFB86C
/-- Dracula Yellow ({lit}`#F1FA8C`). Documented role: strings and text content. -/
public def yellow : Color := color%#F1FA8C
/--
Dracula Green ({lit}`#50FA7B`). Documented role: functions, methods, inherited classes.
-/
public def green : Color := color%#50FA7B
/--
Dracula Cyan ({lit}`#8BE9FD`). Documented role: classes, types, support, regular
expressions.
-/
public def cyan : Color := color%#8BE9FD
/--
Dracula Purple ({lit}`#BD93F9`). Documented role: instance reserved words and constants.
-/
public def purple : Color := color%#BD93F9
/-- Dracula Pink ({lit}`#FF79C6`). Documented role: keywords and storage types. -/
public def pink : Color := color%#FF79C6

end DraculaClassic

/-! # Alucard Classic — the canonical light counterpart -/

namespace AlucardClassic

/-- The palette's display name, suitable as a prefix when naming themes built on it. -/
public def name : String := "Alucard"

/-- The official Dracula spec page, shown in the picker for themes that use this palette. -/
public def sourceLink : SourceLink :=
  { url := "https://draculatheme.com/spec", text := "draculatheme.com/spec" }

/-- Alucard Background ({lit}`#FFFBEB`). Documented role: main background. -/
public def background : Color := color%#FFFBEB
/--
Alucard Current Line ({lit}`#6C664B`). Documented role: semantic current-line highlight.
-/
public def currentLine : Color := color%#6C664B
/-- Alucard Selection ({lit}`#CFCFDE`). Documented role: text selection. -/
public def selection : Color := color%#CFCFDE
/-- Alucard Foreground ({lit}`#1F1F1F`). Documented role: default text. -/
public def foreground : Color := color%#1F1F1F
/-- Alucard Comment ({lit}`#6C664B`). Documented role: comments and disabled code. -/
public def comment : Color := color%#6C664B
/-- Alucard Red ({lit}`#CB3A2A`). Documented role: errors, warnings, deletions. -/
public def red : Color := color%#CB3A2A
/-- Alucard Orange ({lit}`#A34D14`). Documented role: numbers, constants, booleans. -/
public def orange : Color := color%#A34D14
/-- Alucard Yellow ({lit}`#846E15`). Documented role: strings and text content. -/
public def yellow : Color := color%#846E15
/--
Alucard Green ({lit}`#14710A`). Documented role: functions, methods, inherited classes.
-/
public def green : Color := color%#14710A
/--
Alucard Cyan ({lit}`#036A96`). Documented role: classes, types, support, regular
expressions.
-/
public def cyan : Color := color%#036A96
/--
Alucard Purple ({lit}`#644AC9`). Documented role: instance reserved words and constants.
-/
public def purple : Color := color%#644AC9
/-- Alucard Pink ({lit}`#A3144D`). Documented role: keywords and storage types. -/
public def pink : Color := color%#A3144D

end AlucardClassic

end Verso.Theme.Color.Palettes
