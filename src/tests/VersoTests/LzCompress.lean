/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import VersoUtil.LzCompress
import Errata

open Verso.LzCompress Errata

/-- The LZ compressor produces the expected encoding for a sample Lean snippet. -/
@[test]
def compresses : Test := do
  let actual := lzCompress r#"import Mathlib.Logic.Basic -- basic facts in logic
-- theorems in Lean's mathematics library

-- Let P and Q be true-false statements
variable (P Q : Prop)

-- The following is a basic result in logic
example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  -- its proof is already in Lean's mathematics library
  exact not_and_or

-- Here is another basic result in logic
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  apply? -- we can search for the proof in the library
  -- we can also replace `apply?` with its output
"#
  let expected :=
    "JYWwDg9gTgLgBAWQIYwBYBtgCMB0AZCAc2AGMcAhJAZ1LgFo64traAzJEmKuYAOznRFSAKAZw0AU2gSQ3" ++
    "PnDwSkvAOTcQKVDJSlumLFCRQAnsNGNF8AApxlAEzgBFJhPFQArhLrt0VV1RgUGQleLmEANyNgJCx0VwA" ++
    "KG2cALjgrKAgwAEozMQAVLThWCHRBAHc+Qh5uJCYWEjgoCSp3dHh5QWISYQkADyRwOLhUgBq4RLhAciIn" ++
    "LLhAFMI4MZtACiJFp2GAXiZTOHpGYC44MAyIVmrbdCakO2MefkVlNTgNSRfdAWxDE2Fdvo54XgQGAAfXs" ++
    "wOguUYAAkJE1zsogVooHUaA0mi02ncBEJun9Bq5RuMVjN5msbNMxiktlgdrYwGB0MYAPx7OBlVwkZRwPx" ++
    "GEioIrQcSFY4QU5YyQfAxGWlidlwTn8JC+CCNCQMjiuAAGSHpjKZmrZB35B24EHcMDA5uEQA"
  assertEq expected actual
