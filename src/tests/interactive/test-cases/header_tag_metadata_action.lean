import VersoManual

/-!
Tests that Lean's own code action provider offers the header tag linter's quick fixes with their
short titles in a metadata block without a `tag` field.
-/

set_option linter.verso.manual.headerTags true

#doc (Verso.Genre.Manual) "Trees" =>

# Leaves

%%%
shortTitle := "Leaves"
%%%
--^ codeAction

Leaves fall from the trees in autumn.
