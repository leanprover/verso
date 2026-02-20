import LitConfig.Core
import LitConfig.NoDocstrings
import Verso

set_option doc.verso true

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

/-!
We can also have inline code references like {name}`hello`.
-/

#check hello
