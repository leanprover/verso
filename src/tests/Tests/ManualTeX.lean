import Verso
import VersoManual

namespace Verso.ManualTexTest

open Verso Genre Manual

--------------------

/-- This is a docstring.

Here's some more text with a `code inline` in it.
Here's when a `code inline`
occurs right before a line break.

And then here's a paragraph break.
-/
def sample_constant := Unit

#docs (Manual) sample_part "Title of the Doc" :=
:::::::

%%%
shortTitle := "ShortTitle"
authors := ["Harry Q. Bovik"]
%%%

{docstring sample_constant}

:::::::

def run : IO String := open Verso Genre Manual in do
 let logError (msg : String) := IO.eprintln msg
 let cfg : Config := { }
 ReaderT.run (makeTeX logError cfg sample_part) extension_impls%

end Verso.ManualTexTest
