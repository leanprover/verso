/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

set_option linter.missingDocs true
set_option doc.verso true

namespace Verso.CLI

/--
Result type for extracting a required filename from command-line arguments.

This indexed type captures the validation result along with a proof that relates the result to the
original argument list. The type index allows termination proofs to go through easily.
-/
public inductive RequiredFilename : (args : List String) → Type where
  /--
  The validation succeeded. Contains the extracted filename {lit}`name`, the remaining arguments
  {lit}`more`, and a proof that the filename does not start with {lit}`-`.
  -/
  | ok (name : String) (more : List String) : ¬ name.startsWith "-" → RequiredFilename (name :: more)
  /--
  The validation failed with an error message.
  -/
  | error (msgs : String) : RequiredFilename args

/--
Validates and extracts a filename argument from a command-line argument list.

This helper function is used when parsing command-line options that require a filename parameter. It
ensures that:
1. A filename argument is present after the option name.
2. The filename does not start with {lit}`-`. This would indicate that it's another option, not a
   filename.
-/
public def requireFilename (optionName : String) (args : List String) : RequiredFilename args :=
  match args with
  | [] => .error s!"Missing filename for {optionName}"
  | file :: more =>
    if h : file.startsWith "-" then
      .error s!"Expected filename after {optionName}, got option {file}"
    else
      .ok file more h
