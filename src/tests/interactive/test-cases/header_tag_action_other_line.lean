import VersoManual
--^ collectDiagnostics

/-!
Tests that `headerTagActions` doesn't offer quick fixes for a request on a line other than the
header's, including the quick fixes of a hint about the requested line. The paragraph's command logs
the header tag linter's hint about the header and a hint about the paragraph.
-/

set_option linter.verso.manual.headerTags true

#doc (Verso.Genre.Manual) "Trees" =>

%%%
tag := "trees"
%%%

# Leaves

__Maple__ leaves turn red in the fall.
--⬑ codeAction
