namespace Tests.ManualHtmlMulti

private def hasSubstring (s : String) (sub : String) : Bool :=
  s.find? sub |>.isSome

private def assertContains (label : String) (haystack needle : String) : IO Unit := do
  unless hasSubstring haystack needle do
    throw <| IO.userError s!"{label}: expected output to contain {repr needle}, got:\n{haystack}"

def testManualHtmlMultiLinks : IO Unit := do
  IO.println "Running manual multi-page HTML link tests..."
  IO.FS.withTempDir fun tmpDir => do
    let result ← IO.Process.output {
      cmd := "lake"
      args := #["--quiet", "exe", "demotextbook", "--output", tmpDir.toString]
    }
    unless result.exitCode == 0 do
      throw <| IO.userError s!"demotextbook failed with exit code {result.exitCode}:\n{result.stderr}"

    let rootHtml ← IO.FS.readFile (tmpDir / "html-multi" / "index.html")
    let chapterHtml ← IO.FS.readFile (tmpDir / "html-multi" / "Lean-Code" / "index.html")

    assertContains
      "root contents link"
      rootHtml
      "href=\"Lean-Code/index.html#A-Textbook--Lean-Code\""
    assertContains
      "root next button"
      rootHtml
      "href=\"Lean-Code/index.html#A-Textbook--Lean-Code\" rel=\"next\""
    assertContains
      "chapter child-page link"
      chapterHtml
      "href=\"Lean-Code/Saved-Lean-Code/index.html#A-Textbook--Lean-Code--Saved-Lean-Code\""
    assertContains
      "chapter previous button"
      chapterHtml
      "href=\"index.html\" rel=\"prev\""
    assertContains
      "same-page chapter anchor"
      chapterHtml
      "href=\"#A-Textbook--Lean-Code\">Lean Code</a>"
