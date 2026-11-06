/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import VersoGen.Text
public import VersoGen.Random
public import VersoGen.Genre
public import VersoGen.Doc
public import VersoGen.TextEdit
public import VersoGen.Edit
public import VersoGen.Server

set_option doc.verso true

/-!
A generator of Verso documents and edit scripts, for testing and benchmarking Verso's elaboration
and language server support. The generator makes a surface document from a genre profile,
parameters and a seed, concretizes it as a Lean module, and records edits of the surface document as
an edit script. A client of the Lean language server replays the resulting edit sequences in a
server session, measures what the server reuses and checks its answers to requests.
-/
