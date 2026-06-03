import LitConfig.Core
import LitConfig.NoDocstrings
import Verso

/-!
# LitConfig: A Test Module

This module demonstrates the literate website generation.
It has module docstrings that should appear as prose.
-/

/-!
## Overview

The {module -checked}`LitConfig` module serves as the root of a small test project.
Below is a simple definition.
-/

/-- A greeting message. -/
def hello : String := "Hello, literate world!"

/--
Given {lean}`n : Nat`, compute {name}`double` of {name}`n`.
-/
def doubleIt (n : Nat) : Nat := double n

/--
Given {lean}`n : Nat`, {name}`double` returns {lean}`n * 2`.
-/
theorem double_spec {n : Nat} : double n = n * 2 := rfl

/--
A variant: {name}`double` is the same as adding {lean}`n` to itself.
-/
theorem double_spec' {n : Nat} : double n = n + n := by grind [double]

/--
A rewrite sequence. Each rewrite step gets its own intermediate proof state, nested inside the
whole-invocation region, whose own final state closes all goals.
-/
theorem rw_chain {a b c d : Nat} (h1 : a = b) (h2 : b = c) (h3 : c = d) : a = d := by
  rw [h1, h2, h3]

/-!
We can also have inline code references like {name}`hello`.

Here is a diagram:
![Test diagram](images/test-diagram.png)
-/

#check hello
