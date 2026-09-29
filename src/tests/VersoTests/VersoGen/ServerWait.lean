/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

import Errata
import VersoGen.Server.Basic

set_option doc.verso true

/-!
Tests of how the language server client counts the time of a wait on a server. The time limits of
the client's waits bound slow servers, so a wait must count the time during which the machine was
awake, and not the time during which it slept. A failure means that a wait in progress fails when a
machine wakes up, or that a slow machine's waits last longer than their limits.
-/

open Errata VersoGen.Server

namespace Verso.Tests.VersoGen.ServerWait

/--
A wait counts the time between two polls in full when it is at most {name}`pollStepCap`, and counts
a longer time, such as a sleep of the machine, as {name}`pollStepCap`.
-/
@[test]
def pollSteps : Test := do
  assertBEq 260 (countPollStep 10 250)
  assertBEq (10 + pollStepCap) (countPollStep 10 pollStepCap)
  assertBEq (10 + pollStepCap) (countPollStep 10 (10 * 60 * 1000))
