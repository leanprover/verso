import Lake
open Lake DSL

-- A package with a configuration file for Verso's Errata driver, whose setting needs a target of
-- this lakefile.
package tomlapp where
  testDriver := "verso/Errata.run"
  -- Verso's clones of the git dependencies serve this workspace too, so that the modules built from
  -- the shared Verso checkout see the same dependency paths from both.
  packagesDir := "../../../../.lake/packages"

require verso from "../../../.."

-- A test that reads the file that the `stamp` target builds.
lean_lib TomlLib

-- Copies `stamp-input.txt` into the build directory. The test's setting needs it.
target stamp pkg : System.FilePath := do
  let input ← inputTextFile (pkg.dir / "stamp-input.txt")
  input.mapM fun src => do
    let out := pkg.buildDir / "stamp.txt"
    buildFileUnlessUpToDate' (text := true) out do
      IO.FS.createDirAll pkg.buildDir
      IO.FS.writeFile out (← IO.FS.readFile src)
    return out
