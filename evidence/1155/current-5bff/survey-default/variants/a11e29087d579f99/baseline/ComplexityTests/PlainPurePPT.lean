/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.PPT

/-! Plain deterministic certificates lift through ordinary imports, with full typed context. -/

open Turing.MultiTapeTM Cslib.Probability

example {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β}
    (h : ComputableInPolyTime f input output) :
    IsPPTOn input output (fun a => pure (f a)) :=
  ComputableInPolyTime.isPPTOn h

example {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool} {f : α → β}
    (h : ComputableInPolyTime f input output) :
    IsPPTOn input output (fun a => pure (f a)) := by
  fail_if_success (clear h; fun_prop)
  fun_prop
