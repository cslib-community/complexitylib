/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString
public import CslibFrontier.Computability.Probabilistic.Sampling

/-!
# Uniform fixed-width bit strings in strict polynomial time

A uniform `BitString k`, written as its bit list `encBitString k`, is sampled exactly by `k` fair
coins (`BitString.sampleList`). So the typed sampler `ProbComp.uniform (BitString (k a))` is
uniform strict PPT whenever the width `k a` is computable in polynomial time in unary.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.uniformBitString`: the typed uniform sampler of
  `BitString (k a)` is uniform strict PPT.
-/

public section

open Cslib Cslib.Probability

/-- **Uniform fixed-width bit strings are strict PPT**: for a width `k a` computable in polynomial
time in unary, sampling a uniform `BitString (k a)` and writing its bit list is uniform strict
PPT. -/
theorem Turing.MultiTapeTM.ComputableInPolyTime.uniformBitString {α : Type}
    {input : α ↪ List Bool} {k : α → ℕ} (hk : ComputableInPolyTime k input encUnary) :
    IsPPTOn input encBits fun a => encBitString (k a) <$> ProbComp.uniform (BitString (k a)) :=
  hk.sampleList.congr fun a => by
    rw [BitString.eval_sampleList, ProbComp.eval_map, ProbComp.eval_uniform]
    rfl
