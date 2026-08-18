/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import VersoTutorial
import TutorialExample.Site

open Verso.Genre Tutorial

def main := tutorialsRenderedHtmlMain content (config := { destination := "_out/tutorial-content/v1" })
