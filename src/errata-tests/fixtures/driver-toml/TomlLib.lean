module

public import Errata

open Errata

public section

namespace TomlLib

/-- The file that the fixture's `stamp` target builds. -/
@[setting, expose]
def stampFile : Setting where
  type := System.FilePath
  fromString s := some s

/-- The target's result reaches the test as the value of the setting that needs it. -/
@[test]
def readsStamp (stamp : stampFile) : Test := do
  assertTrue (← stamp.pathExists) s!"{stamp} does not exist"
  assertContains "stamp" (← IO.FS.readFile stamp)

end TomlLib
