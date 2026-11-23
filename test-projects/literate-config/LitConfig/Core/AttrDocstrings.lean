import LitConfig.Core.AttrDefinedConstant

set_option doc.verso false

/-!
# Docstrings and Attributes

A declaration keeps its docstring when one of its attributes defines a further constant.
-/

/-- The docstring of the first declaration. -/
@[also_as AttrDocstrings.firstAlias]
def AttrDocstrings.first : Nat := 1

/-- The docstring of the second declaration. -/
@[also_as AttrDocstrings.secondAlias /-- The docstring of the constant defined in the second attribute. -/]
def AttrDocstrings.second : Nat := 2

/-- The docstring of the third declaration. -/
@[also_as AttrDocstrings.thirdOuter
    (attr := also_as AttrDocstrings.thirdInner /-- The docstring of the inner constant. -/)
    /-- The docstring of the outer constant. -/]
def AttrDocstrings.third : Nat := 3
