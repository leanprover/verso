/-!
# Guarded Messages

{lit}`#guard_msgs` takes the messages that it expects as a doc comment. That comment documents
nothing, so the declaration in the guarded command keeps its own docstring, and only that.
-/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- A theorem whose proof is left open. -/
theorem guarded : 1 + 1 = 2 := sorry
