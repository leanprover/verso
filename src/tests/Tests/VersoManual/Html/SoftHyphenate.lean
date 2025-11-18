/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoManual.Html.SoftHyphenate
open Verso.Genre.Manual

/-- info: "blahNotCode<code><a>foo&shy;Bar&shy;Baz</a></code>" -/
#guard_msgs in
open Verso.Output Html in
#eval softHyphenateIdentifiers {{"blahNotCode"<code><a>"fooBarBaz"</a></code>}} |>.asString

/-- info: "<code>abc.<wbr>def.<wbr>ghi.<wbr>jkl</code>" -/
#guard_msgs in
open Verso.Output Html in
#eval softHyphenateIdentifiers {{<code>"abc.def.ghi.jkl"</code>}} |>.asString

/-- info: "<code>ABC.<wbr>DEF</code>" -/
#guard_msgs in
open Verso.Output Html in
#eval softHyphenateIdentifiers {{<code>"ABC.DEF"</code>}} |>.asString

/-- info: "blahNotCode<code><a>fooBa.<wbr>rBaz.<wbr>ab&shy;CD</a></code>" -/
#guard_msgs in
open Verso.Output Html in
#eval softHyphenateIdentifiers {{"blahNotCode"<code><a>"fooBa.rBaz.abCD"</a></code>}} |>.asString

/-- info: "blahNotCode<code><a>fooBa...<wbr>rBaz.<wbr>ab&shy;CD</a></code>" -/
#guard_msgs in
open Verso.Output Html in
#eval softHyphenateIdentifiers {{"blahNotCode"<code><a>"fooBa...rBaz.abCD"</a></code>}} |>.asString
