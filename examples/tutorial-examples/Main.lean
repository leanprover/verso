import VersoTutorial
import TutorialExample

open Verso.Genre Tutorial

open Verso.Doc.Concrete in
def content : Tutorials where
  content :=
    verso (.none) "Example Tutorial Site"
    ::::
    Here are some examples of the tutorials feature.
    ::::

  topics := #[
    { title := "Data",
      description := #[blocks!"These tutorials describe the use of data in Lean."]
      tutorials := #[%doc TutorialExample.Data, %doc TutorialExample.HashMap, literate_part⟨"." TutorialExample.Lit "Literately-Produced Tutorial" {slug := "literate", summary := "checks that we can load them"} : Tutorial⟩]
    },
    { title := "Tactics",
      description := #[]
      tutorials := #[%doc TutorialExample.RCases]
    }

  ]

-- TODO cmdline for output dir
def main := tutorialsMain content (config := { destination := "_out/tut" : Verso.Genre.Manual.Config} |>.addKaTeX)
