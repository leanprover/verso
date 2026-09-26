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

-- Tests that read the files that the `stamp` and `marker` targets build.
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

-- Writes a marker file into the build directory, so that a test can tell whether it was built. The
-- test that reads it needs it.
target marker pkg : System.FilePath := do
  let input ← inputTextFile (pkg.dir / "stamp-input.txt")
  input.mapM fun _ => do
    let out := pkg.buildDir / "marker.txt"
    buildFileUnlessUpToDate' (text := true) out do
      IO.FS.createDirAll pkg.buildDir
      IO.FS.writeFile out "marker\n"
    return out

-- A target whose build fails, for a need of `variants/broken-need.toml`.
target broken pkg : System.FilePath := do
  let input ← inputTextFile (pkg.dir / "stamp-input.txt")
  input.mapM fun _ => do
    error "the target fails to build on purpose"

-- Copies `stamp-input.txt` as `stamp` does, after ten seconds, on every build, for a need of
-- `variants/slow-need.toml`.
target slowStamp pkg : System.FilePath := do
  let input ← inputTextFile (pkg.dir / "stamp-input.txt")
  input.mapM fun src => do
    IO.sleep 10000
    let out := pkg.buildDir / "stamp.txt"
    IO.FS.createDirAll pkg.buildDir
    IO.FS.writeFile out (← IO.FS.readFile src)
    return out
