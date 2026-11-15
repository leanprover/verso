/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Verso.Code.External.Files
import Errata

open Lean Errata Verso.Code.External

namespace VersoTests.ExternalCode

private def load (project : System.FilePath) : IO (String × String) := do
  let options := ({} : Lean.Options).setBool `trace.Elab.Verso.Code.External.loadModule true
  let (items, state) ← (loadModuleContent' ⟨Syntax.mkStrLit project.toString⟩
    "AnchorExamples.Basic" [] : CoreM _).toIO
      { fileName := "<external-code-test>", fileMap := default, options }
      { env := ← mkEmptyEnvironment }
  let traces ← state.traceState.traces.toArray.mapM (·.msg.toString)
  return (String.join (items.toList.map (·.code.toString)), String.intercalate "\n" traces.toList)

private def checkCommand (trace : String) : Test := do
  assertContains "lake build +AnchorExamples.Basic:highlighted" trace
  assertNotContains "building extractor" trace
  assertBEq 1 ((trace.splitOn "building highlighted example").length - 1)

private def checkProject (currentToolchain : Bool) : Test := IO.FS.withTempDir fun project => do
  let source : System.FilePath := "test-projects/anchor-examples"
  IO.FS.createDirAll (project / "AnchorExamples")
  for file in ["lakefile.lean", "lake-manifest.json", "lean-toolchain",
      "AnchorExamples.lean", "AnchorExamples/Basic.lean"] do
    IO.FS.writeFile (project / file) (← IO.FS.readFile (source / file))
  if currentToolchain then
    IO.FS.writeFile (project / "lean-toolchain") (← IO.FS.readFile "lean-toolchain")
    let manifest ← IO.ofExcept <| Json.parse (← IO.FS.readFile "lake-manifest.json")
    let packages ← IO.ofExcept <| manifest.getObjValAs? (Array Json) "packages"
    let some subverso := packages.find? fun package =>
      (package.getObjValAs? String "name").toOption == some "subverso"
      | fail "root manifest has no SubVerso dependency"
    let manifest := Json.mkObj [("version", toJson "1.3.0"),
      ("packagesDir", toJson ".lake/packages"), ("packages", toJson #[subverso]),
      ("name", toJson "examples"), ("lakeDir", toJson ".lake")]
    IO.FS.writeFile (project / "lake-manifest.json") manifest.pretty

  -- Start without an extractor, local oleans or highlighted output.
  assertTrue (!(← (project / ".lake").pathExists))
  let (cold, trace) ← load project
  checkCommand trace
  assertContains "def Tree.flip" cold
  assertFileExists (project / ".lake/build/highlighted/AnchorExamples/Basic.json")
  let (warm, trace) ← load project
  checkCommand trace
  assertBEq cold warm

  let file := project / "AnchorExamples/Basic.lean"
  let original ← IO.FS.readFile file
  let changed := original ++ "\ndef externalCodeFresh : Nat := 137\n"
  IO.FS.writeFile file changed
  let (fresh, trace) ← load project
  checkCommand trace
  assertContains "def externalCodeFresh : Nat := 137" fresh
  assertNotContains "externalCodeFresh" cold

  IO.FS.writeFile file (changed ++ "\ndef externalCodeBroken : Nat := unknownExternalCodeName\n")
  assertThrowsIO (load project) fun error =>
    decide (((toString error).splitOn "unknownExternalCodeName").length > 1)
  IO.FS.writeFile file changed
  let (recovered, trace) ← load project
  checkCommand trace
  assertBEq fresh recovered

/-- A current-toolchain external project builds and refreshes with one Lake command per load. -/
@[test]
def current : Test := checkProject true

/-- The older anchor-example toolchain also builds its extractor through the highlighted facet. -/
@[test]
def older : Test := checkProject false
