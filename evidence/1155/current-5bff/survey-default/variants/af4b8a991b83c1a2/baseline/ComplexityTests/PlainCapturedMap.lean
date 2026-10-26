/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Tactic.PPT

/-!
# Plain deterministic callbacks with captured probabilistic input

The callback is certified on the entire framed pair of caller input and sampled value. It uses
one uniform machine, with no separate premise about the sampled value's length or distribution.
-/

open Cslib Cslib.Probability Turing.MultiTapeTM

example {α β γ : Type} {input : α ↪ List Bool} {sample : β ↪ List Bool}
    {output : γ ↪ List Bool} {program : α → ProbComp β} {callback : α → β → γ}
    (hp : IsPPTOn input sample program)
    (hf : ComputableInPolyTime (fun p => callback p.1 p.2) (encPair input sample) output) :
    IsPPTOn input output (fun a => callback a <$> program a) := by
  fail_if_success (clear hf; ppt)
  exact hp.map_with hf

-- A raw construction certificate can still be explicitly forgotten inside an existing proof.
example {α β γ : Type} {input : α ↪ List Bool} {sample : β ↪ List Bool}
    {output : γ ↪ List Bool} {program : α → ProbComp β} {callback : α → β → γ}
    (hp : IsPPTOn input sample program)
    (hf : ComputableTidilyInPolyTime (fun p => callback p.1 p.2) (encPair input sample) output) :
    IsPPTOn input output (fun a => callback a <$> program a) :=
  hp.map_with (.of_tidy hf)

-- The output retains an actual captured word as well as the sampled word.
example {source : ℕ × List Bool → ProbComp (List Bool)}
    (hs : IsPPTOn (encPair encUnary encBits) encBits source) :
    IsPPTOn (encPair encUnary encBits) encBits
      (fun a => (fun word => a.2 ++ word) <$> source a) := by
  apply hs.map_with
  fun_prop
