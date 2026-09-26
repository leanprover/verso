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

/-- The `stamp` need's value reaches the test as the value of the setting that refers to it. -/
@[test]
def readsStamp (stamp : stampFile) : Test := do
  assertTrue (← stamp.pathExists) s!"{stamp} does not exist"
  assertContains "stamp" (← IO.FS.readFile stamp)

/-- The file that the fixture's `marker` target writes. -/
@[setting, expose]
def markerFile : Setting where
  type := System.FilePath
  fromString s := some s

/-- The `marker` need's value reaches the test as the value of the setting that refers to it. -/
@[test]
def readsMarker (marker : markerFile) : Test := do
  assertTrue (← marker.pathExists) s!"{marker} does not exist"

end TomlLib
