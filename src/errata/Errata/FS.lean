/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module
set_option linter.missingDocs true
set_option doc.verso true

/-!
This module contains file system helpers shared by Errata's own modules that aren't really suitable
as the API to a test framework due to not being germane to testing. They are private, so they stay
out of the library's public API. The modules that use them use `import all` to see them.
-/


namespace Errata

/-- Writes a file, creating all parent directories if necessary. -/
private def writeFile (path : System.FilePath) (contents : String) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeFile path contents

/-- Writes a binary file, creating all parent directories if necessary. -/
private def writeBinFile (path : System.FilePath) (contents : ByteArray) : IO Unit := do
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.writeBinFile path contents

end Errata
