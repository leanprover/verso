/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import Lean.Log

open Lean

namespace Verso.Log

variable [Monad m] [MonadOptions m] [MonadLog m] [AddMessageContext m] [MonadRef m]

/--
Logs a message silently with the given severity at the given location.

Silent messages are only shown in the InfoView when the cursor is on their region, and they are not
emitted as side effects when building code at the command line.
-/
def logSilentAt (ref : Syntax) (severity : MessageSeverity) (message : MessageData) : m Unit :=
  logAt ref message (severity := severity) (isSilent := true)

/--
Logs a message silently with the given severity at the current reference location.

Silent messages are only shown in the InfoView when the cursor is on their region, and they are not
emitted as side effects when building code at the command line.
-/
def logSilent (severity : MessageSeverity) (message : MessageData) : m Unit := do
  logSilentAt (← getRef) severity message

/--
Logs an informational message silently at the given location.

Silent messages are only shown in the InfoView when the cursor is on their region, and they are not
emitted as side effects when building code at the command line.
-/
def logSilentInfoAt  (ref : Syntax) (message : MessageData) : m Unit :=
  logSilentAt ref .information message

/--
Logs an informational message silently at the current reference location.

Silent messages are only shown in the InfoView when the cursor is on their region, and they are not
emitted as side effects when building code at the command line.
-/
def logSilentInfo (message : MessageData) : m Unit := do
  logSilent .information message
