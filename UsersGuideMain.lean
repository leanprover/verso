import VersoManual

import UsersGuide

open Verso.Genre.Manual

def config : Config := {
  sourceLink := some "https://github.com/leanprover/verso",
  issueLink := some "https://github.com/leanprover/verso/issues"
  -- The user's guide ships every theme as a live example, including ones with documented
  -- accessibility trade-offs — most notably the canonical Solarized palette, whose token
  -- colors are below WCAG AA's 4.5:1 contrast threshold for normal text by design. The
  -- coverage and default-accessibility checks still fire (the default theme pair must be
  -- accessible, and the registered set must offer an accessible choice on both
  -- appearances), and per-theme warnings still surface the individual issues; the per-theme
  -- warnings are silenced here to keep the build log readable.
  warnPerThemeAccessibility := false
}

def main := manualMain (%doc UsersGuide.Basic) (config := { config with : RenderConfig })
