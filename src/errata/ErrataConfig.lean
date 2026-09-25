/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

/-
The processing of `errata.toml`: reading and validating it with positions, applying the profiles'
inheritance, and writing the elaborated file that the driver and the runner read.
-/
module

public import ErrataConfig.Basic
public import ErrataConfig.Duration
public import ErrataConfig.StringOffsets
public import ErrataConfig.Read
public import ErrataConfig.Json
