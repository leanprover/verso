import VersoManual
--^ collectDiagnostics

/-!
Tests that the correct quick fix warnings are added for the missing tags linter.
-/

set_option linter.verso.manual.headerTags true

#doc (Verso.Genre.Manual) "Trees" =>

%%%
tag := "trees"
%%%

# Leaves
--^ codeAction
