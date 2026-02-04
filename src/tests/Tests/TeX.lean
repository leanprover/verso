/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Verso.Doc.TeX
import Verso.Output.TeX

namespace Verso.Tests.TeX

open Verso.Doc.TeX
open Verso.Output.TeX

/-! ## Tests for escapeForVerbatim -/

/-- info: "\\symbol{123}\\symbol{124}\\symbol{125}\\symbol{92}" -/
#guard_msgs in
#eval escapeForVerbatim "{|}\\"

-- Tests for lineBreaks functionality
/-- info: "Nat.\\allowbreak{}add\\-One" -/
#guard_msgs in
#eval escapeForVerbatim "Nat.addOne" (lineBreaks := true)

/-- info: "List.\\allowbreak{}map2\\-Fun" -/
#guard_msgs in
#eval escapeForVerbatim "List.map2Fun" (lineBreaks := true)

/-- info: "x2\\-y" -/
#guard_msgs in
#eval escapeForVerbatim "x2y" (lineBreaks := true)

/-- info: "Foo123" -/
#guard_msgs in
#eval escapeForVerbatim "Foo123" (lineBreaks := true)  -- no break before digits

/-- info: "a..\\allowbreak{}b" -/
#guard_msgs in
#eval escapeForVerbatim "a..b" (lineBreaks := true)  -- only one break after dot sequence

/-- info: "\\symbol{123}foo\\-Bar" -/
#guard_msgs in
#eval escapeForVerbatim "{fooBar" (lineBreaks := true)  -- escaping + line breaks

/-- info: "plain" -/
#guard_msgs in
#eval escapeForVerbatim "plain" (lineBreaks := true)  -- no transitions

/-- info: "Nat.addOne" -/
#guard_msgs in
#eval escapeForVerbatim "Nat.addOne"  -- lineBreaks := false (default), no breaks

end Verso.Tests.TeX

/-! ## Tests for TeX syntax macros -/

open scoped Verso.Output.TeX

/-- info: Verso.Output.TeX.seq #[] -/
#guard_msgs in
#eval IO.println <| (repr <| \TeX{}).pretty 80

/-- info: Verso.Output.TeX.text "Hello, world!" -/
#guard_msgs in
#eval IO.println <| (repr <| \TeX{"Hello, world!"}).pretty 80

/--
info: Verso.Output.TeX.command
  "hyperlink"
  #[]
  #[Verso.Output.TeX.raw "foo", Verso.Output.TeX.text ""]
-/
#guard_msgs in
#eval IO.println <| (repr<| \TeX{\hyperlink{\Lean{.raw "foo" }}{\Lean{""}}}).pretty 80

/--
info: Verso.Output.TeX.seq
  #[Verso.Output.TeX.text "Hello, ",
    Verso.Output.TeX.command "textbf" #[] #[Verso.Output.TeX.text "world"]]
-/
#guard_msgs in
#eval IO.println <| (repr <| \TeX{"Hello, " \textbf{"world"}}).pretty 80

/--
info: Verso.Output.TeX.environment
  "Verbatim"
  #[]
  #[Verso.Output.TeX.raw "commandChars=\\\\"]
  #[Verso.Output.TeX.text "Hello, ",
    Verso.Output.TeX.command "textbf" #[] #[Verso.Output.TeX.text "world"]]
-/
#guard_msgs in
#eval IO.println <| (repr <| \TeX{\begin{Verbatim}{s!"commandChars=\\\\"}"Hello, " \textbf{"world"}\end{Verbatim}}).pretty 80
