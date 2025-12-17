/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoTutorial
import TutorialExample

open Verso.Genre Tutorial

open Verso.Doc.Concrete in
def content : Tutorials where
  content :=
    (verso (Blog.Page) "Example Tutorial Site"
    ::::
    Here are some examples of the tutorials feature.
    ::::).toPart

  topics := #[
    { title := #[inlines!"Data"],
      titleString := "Data",
      description := #[blocks!"These tutorials describe the use of data in Lean."]
      tutorials := #[
        %doc TutorialExample.Data,
        %doc TutorialExample.HashMap,
        literate_part⟨"." TutorialExample.Lit "Literately-Produced Tutorial" {slug := "literate", summary := "checks that we can load them", exampleStyle := .inlineLean `Lit} : Tutorial⟩ |>.toPart]
    },
    { title := #[inlines!"Tactics"],
      titleString := "Tactics",
      description := #[]
      tutorials := #[%doc TutorialExample.RCases]
    }

  ]

def main := tutorialsMain content (config := { destination := "_out/tut" })
