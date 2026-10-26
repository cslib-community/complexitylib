/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.PPT.Composition

/-! Ordinary preprocessing retains complete input, intermediate and output encodings. -/

open Turing.MultiTapeTM Cslib.Probability

example {α β γ : Type} {input : α ↪ List Bool} {middle : β ↪ List Bool}
    {output : γ ↪ List Bool} {program : β → Cslib.ProbComp γ} {prepare : α → β}
    (hprogram : IsPPTOn middle output program)
    (hprepare : ComputableInPolyTime prepare input middle) :
    IsPPTOn input output (fun a => program (prepare a)) :=
  hprogram.preprocess hprepare

example {α β γ : Type} {input : α ↪ List Bool} {middle : β ↪ List Bool}
    {output : γ ↪ List Bool} {program : β → Cslib.ProbComp γ} {prepare : α → β}
    (hprogram : IsPPTOn middle output program)
    (hprepare : ComputableInPolyTime prepare input middle) :
    IsPPTOn input output (fun a => program (prepare a)) := by
  fail_if_success (clear hprepare; fun_prop)
  fail_if_success (clear hprogram; fun_prop)
  fun_prop
