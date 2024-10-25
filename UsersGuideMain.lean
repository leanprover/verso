import VersoManual

import UsersGuide

open Verso.Genre.Manual

def config : Config := {
  sourceLink := some "https://github.com/leanprover/verso",
  issueLink := some "https://github.com/leanprover/verso/issues"
}

def main := manualMain (%doc UsersGuide.Basic) (config := config)
