/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import UsersGuide.Releases.Entry

open Verso.Genre Manual InlineLean UsersGuide.Releases

release_note
  version := ⟨4, 34, 0⟩
  breaking := true
  tag := "css-color-vars"
  prs := [954]

#doc (Manual) "Color Customization" =>

All colors in rendered Lean code are now controlled by CSS variables, and the message text color variables have new names.

All colors in Verso's rendering of Lean code are controlled by CSS custom properties, documented in `verso-vars.css`.
Each message severity (info, warning, error) has four configurations (here exemplified for the `error` severity, but also present for `warning` and `info`):

* variables for the affected code itself, via the `--verso-code-error-color`, `--verso-code-error-bg-color`, and `--verso-code-error-hover-color` and `--verso-code-error-hover-bg-color` families, plus `--verso-error-indicator-color` for the wavy underline,
* a variable for the text of the message, via `--verso-message-error-color`,
* variables for the tooltip that displays the message, via `--verso-tooltip-error-color`, `--verso-tooltip-error-bg-color`, and `--verso-tooltip-error-border-color`, and
* a variable for the marker bar on output blocks, via `--verso-output-error-color`,


Tooltips share a generic palette (`--verso-tooltip-color`, `--verso-tooltip-bg-color`, `--verso-tooltip-border-color`, and `--verso-tooltip-separator-color`) that the severity-specific tooltip colors default to.
Proof states are styled by the `--verso-tactic-state-` and `--verso-tactic-toggle-` variable families, and the hover highlight on interactive code by `--verso-code-hover-bg-color`.

Breaking change: the variables `--verso-error-color`, `--verso-warning-color`, and `--verso-info-color` no longer exist.
Sites that override them to recolor diagnostics should set `--verso-message-error-color`, `--verso-message-warning-color`, and `--verso-message-info-color` instead.
