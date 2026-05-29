/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

set_option linter.missingDocs true
set_option doc.verso true

namespace Verso

-- This is an inductive with a single `rgba` constructor rather than a structure so that other color
-- models (such as wide-gamut `oklch`) can be added later. The byte channels give a canonical
-- `DecidableEq`, so colors round-trip through hex exactly and themes, fonts, and assets deduplicate
-- by value.
/--
A color in sRGB with an alpha channel, each channel a byte.
-/
public inductive Color where
  | rgba (red green blue alpha : UInt8)
deriving DecidableEq, Repr, Inhabited
