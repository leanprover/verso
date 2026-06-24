/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen

Golden tests for manual-genre TeX generation. This is a non-`module` file because `VersoManual`
and the integration document fixtures are not part of the module system; the Errata runner imports
it through its non-module main.
-/
import VersoManual
import Tests.Integration.SampleDoc
import Tests.Integration.InheritanceDoc
import Tests.Integration.CodeContent
import Tests.Integration.ExtraFilesDoc
import Tests.Integration.FrontMatter
import Tests.Integration.DiagramDoc
import Errata

open Verso Genre Manual
open Verso.Integration
open Errata

/--
Renders `doc` to TeX under `integration/<dir>/output`, checks the produced tree against the golden
`expected` tree, and, under `--check-tex`, confirms `lualatex` builds the result. The extra-file
lists place additional assets alongside the output, matching the document's expectations.
-/
def texGolden (dir : System.FilePath) (doc : Verso.Doc.VersoDoc Manual)
    (extraFiles extraFilesTeX : List (System.FilePath × String) := []) : Test := do
  let base : System.FilePath := "src/tests/integration" / dir
  let output := base / "output"
  if ← output.pathExists then IO.FS.removeDirAll output
  let config : Manual.Config :=
    { destination := output, emitTeX := true, emitHtmlMulti := .no, extraFiles, extraFilesTeX }
  let logger ← Verso.Logger.new
  emitTeX config doc.toPart |>.run extension_impls% |>.run logger
  goldenDir (base / "expected") output
  if ← flag "check-tex" then
    -- `-shell-escape` lets the `svg` package call Inkscape to rasterize `diagram` attachments.
    let out ← IO.Process.output {
      cwd := output / "tex"
      cmd := "lualatex"
      args := #["-shell-escape", "-halt-on-error", "-interaction=nonstopmode", "main.tex"]
    }
    unless out.exitCode == 0 do
      failHere s!"lualatex exited with code {out.exitCode}"
        (detail? := some (out.stdout ++ out.stderr))

/-- The sample document renders to its golden TeX. -/
@[test]
def sampleDoc : Test := texGolden "sample-doc" SampleDoc.doc

/-- A document using inheritance renders to its golden TeX. -/
@[test]
def inheritanceDoc : Test := texGolden "inheritance-doc" InheritanceDoc.doc

/-- A document exercising code content renders to its golden TeX. -/
@[test]
def codeContentDoc : Test := texGolden "code-content-doc" CodeContent.doc

/-- A document with extra bundled files renders to its golden TeX. -/
@[test]
def extraFilesDoc : Test :=
  texGolden "extra-files-doc" ExtraFilesDoc.doc
    (extraFiles := [("src/tests/integration/extra-files-doc/test-data/shared", "shared")])
    (extraFilesTeX := [("src/tests/integration/extra-files-doc/test-data/TeX-only", "TeX-only")])

/-- A document with front matter renders to its golden TeX. -/
@[test]
def frontMatterDoc : Test := texGolden "front-matter-doc" FrontMatter.doc

/-- A document with diagrams renders to its golden TeX. -/
@[test]
def diagramDoc : Test := texGolden "diagram-doc" DiagramDoc.doc
