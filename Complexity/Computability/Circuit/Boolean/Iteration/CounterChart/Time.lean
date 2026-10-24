/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Iteration.CounterChart.Circuit

import Mathlib.Tactic.Linarith

/-! # Advancing sparse orbit coordinates with one streamed input-time remainder 
## Main definitions

* `advanceCycleLabel`: advance a phase by an input bit-string time.

## Main results

* `advanceCycleLabel_spec`: advancing the label agrees with iteration.
* `synthesis_advanceCycleLabel`: one streamed remainder, linear in time width.

## References

* Adapted from lean/Proofs/CounterChartTime.lean at revision `c4cfa198` of
  [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

attribute [local instance] counterChartWordOrder



open Cslib.FunctionalGraph

variable {n m a : ℕ}

/-- Keep the cycle representative and length, advancing its phase by the input time. -/
def advanceCycleLabel (r : BitString (n + (chartWidth n + chartWidth n)))
    (bits : Fin m → Bool) :
    BitString (n + (chartWidth n + chartWidth n)) :=
  labelBits (labelRepresentative r) (labelLength r)
    (addResidue (labelLength r) (labelPhase r)
      (streamRemainder (labelLength r) bits))

/-- Advancing the cycle label of `x` by `bits` yields the cycle label of
`f^[(word bits).toNat] x`. -/
theorem advanceCycleLabel_spec (f : BitVec n → BitVec n) (x : BitVec n) (bits : Fin m → Bool) :
    advanceCycleLabel (wordCycleLabel f x) bits = wordCycleLabel f (f^[(word bits).toNat] x) := by
  let ell := BitVec.ofNat (chartWidth n) (cycleLength f x)
  let p := BitVec.ofNat (chartWidth n) (phase f x)
  have hel : ell.toNat = cycleLength f x := chart_ofNat_toNat (cycleLength_le_words f x)
  have hp : p.toNat = phase f x := chart_ofNat_toNat
    ((phase_lt f x).le.trans (cycleLength_le_words f x))
  have hpos : 0 < ell.toNat := by rw [hel]; exact cycleLength_pos f x
  have hwide : 2 * ell.toNat ≤ 2 ^ chartWidth n := by
    rw [hel]
    have := cycleLength_le_words f x
    simp only [chartWidth, Nat.pow_succ]
    lia
  have hrem := toNat_streamRemainder ell bits hpos hwide
  have hphase : addResidue ell p (streamRemainder ell bits) =
      BitVec.ofNat (chartWidth n) (phase f (f^[(word bits).toNat] x)) := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_addResidue _ _ _ (by rw [hp, hel]; exact phase_lt f x)
      (by rw [hrem]; exact Nat.mod_lt _ hpos), hrem, hp, hel]
    rw [chart_ofNat_toNat ((phase_lt f _).le.trans (cycleLength_le_words f _)),
      phase_iterate, Nat.add_mod_mod]
  simp only [advanceCycleLabel, wordCycleLabel, labelRepresentative_labelBits,
    labelLength_labelBits, labelPhase_labelBits, canonicalCycle_iterate, cycleLength_iterate]
  exact congrArg (labelBits (fun i => (canonicalCycle f x).getLsbD i.val) ell) hphase

/-- Streaming is performed once after the input's cycle length is selected. -/
theorem synthesis_advanceCycleLabel (s : Set (BitString a → Bool))
    (r : BitString a → BitString (n + (chartWidth n + chartWidth n)))
    (bits : BitString a → Fin m → Bool) (hr : wires r ⊆ s)
    (hb : ∀ j, (fun z => bits z j) ∈ s) (hz : (fun _ => false) ∈ s) :
    Synthesis Boolean.interpretation s (wires fun z => advanceCycleLabel (r z) (bits z))
      (200 * (n + 3) * (m + 1)) := by
  let ell := fun z => labelLength (r z)
  let p := fun z => labelPhase (r z)
  let rem := fun z => streamRemainder (ell z) (bits z)
  have he : wordWires ell ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [ell, labelLength, getLsbD_word] using hr ⟨_, rfl⟩
  have hp : wordWires p ⊆ s := by
    rintro _ ⟨i, rfl⟩
    simpa only [p, labelPhase, getLsbD_word] using hr ⟨_, rfl⟩
  have hrem := synthesis_streamRemainder s ell bits (fun i => he ⟨i, rfl⟩) hb hz
  let src := s ∪ wordWires rem
  have hadd := synthesis_addResidue src ell p rem
    (fun _ h => Or.inl (he h)) (fun _ h => Or.inl (hp h)) (fun _ h => Or.inr h)
  let newPhase := fun z => addResidue (ell z) (p z) (rem z)
  have hout := labelBits_wires_subset (src ∪ wordWires newPhase)
    (fun z => labelRepresentative (r z)) ell newPhase
    (by rintro _ ⟨i, rfl⟩; exact Or.inl (Or.inl (hr ⟨_, rfl⟩)))
    (fun _ h => Or.inl (Or.inl (he h))) (fun _ h => Or.inr h)
  exact (hrem.trans (hadd.trans (Synthesis.of_subset hout))).mono
    Set.Subset.rfl Set.Subset.rfl (by dsimp [chartWidth]; nlinarith [Nat.zero_le (n * m)])

end Cslib.Circuits.Boolean.Iteration
