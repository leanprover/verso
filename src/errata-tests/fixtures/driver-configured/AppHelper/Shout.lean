module

public import Errata

open Errata

public section

namespace AppHelper

/-- Writes each argument on a line of its own to standard output, and exits with 7. -/
@[test_helper]
def shout (args : List String) : IO UInt32 := do
  for a in args do IO.println a
  return 7

end AppHelper
