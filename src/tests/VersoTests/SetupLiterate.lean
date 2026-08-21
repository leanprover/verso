/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

Tests for `verso setup-literate`, which scaffolds the GitHub Pages workflow in a downstream project.
-/
module

import Errata

open Errata

/-- The `verso-literate-pages.yml` workflow path within a project. -/
private def workflowPath (root : System.FilePath) : System.FilePath :=
  root / ".github" / "workflows" / "verso-literate-pages.yml"

/--
`verso setup-literate` generates the Pages workflow on a fresh project, reports that it is up to
date on a second run, and backs up a hand-edited workflow before rewriting it.
-/
@[test]
def setupLiterate : Test := do
  let versoRoot ← IO.FS.realPath "."
  IO.FS.withTempDir fun tmpDir => do
    let setupLiterate : TestM IO.Process.Output := do
      let out ← IO.Process.output {
        cmd := "lake", args := #["exe", "verso", "setup-literate"], cwd := some tmpDir.toString }
      pure out

    -- A project that depends on the Verso under test.
    assertExitCode 0 (← IO.Process.output {
      cmd := "git", args := #["init", "-q"], cwd := some tmpDir.toString })
    IO.FS.writeFile (tmpDir / "lean-toolchain") (← IO.FS.readFile "lean-toolchain")
    IO.FS.writeFile (tmpDir / "lakefile.toml")
      s!"name = \"test-project\"\n\n[[require]]\nname = \"verso\"\npath = \"{versoRoot}\"\n"

    -- Fresh generation writes a workflow with the expected steps.
    let fresh ← setupLiterate
    assertExitCode 0 fresh
    assertFileExists (workflowPath tmpDir)
    let content ← IO.FS.readFile (workflowPath tmpDir)
    for needle in ["lake query :literateHtml", "deploy-pages@v", "upload-pages-artifact@v", "lean-action@v"] do
      assertContains needle content

    -- A second run changes nothing.
    let again ← setupLiterate
    assertContains "up to date" again.stdout

    -- Editing the workflow makes the next run back up the old content.
    IO.FS.writeFile (workflowPath tmpDir) "modified content\n"
    let updated ← setupLiterate
    assertExitCode 0 updated
    let backup := (workflowPath tmpDir).toString ++ ".bak"
    assertFileExists backup
    assertContains "modified content" (← IO.FS.readFile backup)
