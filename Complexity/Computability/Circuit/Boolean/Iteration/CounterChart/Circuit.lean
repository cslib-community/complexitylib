/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Iteration.CounterChart.Decode

/-!
# Native Boolean circuits for sparse orbit charts

Constants are supplied by the caller and charged once there. Both chart
directions use linear arithmetic per interval and a shared-flag selector.
No exponent-dependent circuit is duplicated across the interval table.

## Main definitions

* The encode and decode maps are defined in the imported chart modules.

## Main results

* `CounterIntervalChart.synthesis_encode`, `CounterIntervalChart.synthesis_decode`:
  linear gate counts in the number of intervals and word width.

## References

* Adapted from lean/Proofs/CounterChartCircuits.lean at revision `c4cfa198` of
  [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration.CounterIntervalChart

attribute [local instance] counterChartWordOrder



open Cslib.FunctionalGraph

variable {n R a : ℕ} {f : BitVec n → BitVec n} (chart : CounterIntervalChart f R)

/-- Synthesize the interval-chart encoding `chart.encode` using at most `R * (220 * (n + 3))`
gates. -/
theorem synthesis_encode (s : Set (BitString a → Bool)) (x : BitString a → BitVec n)
    (hx : wordWires x ⊆ s) (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s) :
    Synthesis Boolean.interpretation s (wires fun z => chart.encode (x z))
      (R * (220 * (n + 3))) := by
  let wide := fun z => (x z).setWidth (chartWidth n)
  have hw := wordWires_setWidth_subset (v := chartWidth n) (s := s) (value := x) hx (hc false)
  have hrow (j : Fin R) : Synthesis Boolean.interpretation s
      ({fun z => chart.contains j (x z)} ∪ wires (fun z => chart.encodedRow j (x z)))
      (200 * (n + 3)) := by
    have hlo := Synthesis.word_ult (s := s) wide
      (fun _ => BitVec.ofNat (chartWidth n) (chart.start j))
      (fun i => hw ⟨i, rfl⟩) (fun _ => hc _)
    have hhi := Synthesis.word_ult (s := s) wide
      (fun _ => BitVec.ofNat (chartWidth n) (chart.stop j))
      (fun i => hw ⟨i, rfl⟩) (fun _ => hc _)
    have hflag := hlo.not.and hhi
    have hoff := Synthesis.word_sub (s := s) wide
      (fun _ => BitVec.ofNat (chartWidth n) (chart.start j)) (fun i => hw ⟨i, rfl⟩) (fun _ => hc _)
    let s1 := s ∪ wordWires (fun z => chart.offset j (x z))
    have hmod := synthesis_addResidue s1
      (fun _ => chart.period j) (fun _ => chart.initialPhase j) (fun z => chart.offset j (x z))
      (by rintro _ ⟨i, rfl⟩; exact Or.inl (hc _))
      (by rintro _ ⟨i, rfl⟩; exact Or.inl (hc _)) (fun _ h => Or.inr h)
    let phase := fun z => addResidue (chart.period j) (chart.initialPhase j)
      (chart.offset j (x z))
    have hout := labelBits_wires_subset (n := n) (s1 ∪ wordWires phase)
      (fun _ i => (canonicalCycle f (chart.first j)).getLsbD i.val) (fun _ => chart.period j) phase
      (by rintro _ ⟨i, rfl⟩; exact Or.inl (Or.inl (hc _)))
      (by rintro _ ⟨i, rfl⟩; exact Or.inl (Or.inl (hc _))) (fun _ h => Or.inr h)
    have hrecord := hoff.trans (hmod.trans (Synthesis.of_subset hout))
    exact (hflag.union hrecord).mono Set.Subset.rfl Set.Subset.rfl (by dsimp [chartWidth]; lia)
  have h := synthesis_flaggedRecords s (fun j z => chart.contains j (x z))
    (fun j z => chart.encodedRow j (x z)) (200 * (n + 3)) (hc false) hrow
  exact h.mono Set.Subset.rfl Set.Subset.rfl
    (Nat.mul_le_mul_left R (by dsimp [chartWidth]; lia))

/-- Synthesize the interval-chart decoding `chart.decode` using at most `R * (150 * (n + 3))`
gates. -/
theorem synthesis_decode (s : Set (BitString a → Bool))
    (rep : BitString a → BitVec n) (p : BitString a → BitVec (chartWidth n))
    (hr : wordWires rep ⊆ s) (hp : wordWires p ⊆ s)
    (hc : ∀ b : Bool, (fun _ : BitString a => b) ∈ s) :
    Synthesis Boolean.interpretation s (wires fun z => chart.decode (rep z) (p z))
      (R * (150 * (n + 3))) := by
  have hrow (j : Fin R) : Synthesis Boolean.interpretation s
      ({fun z => chart.decodeFlag j (rep z) (p z)} ∪
        wordWires (fun z => chart.decodedRow j (p z))) (140 * (n + 3)) := by
    let dist := fun z => chart.phaseDistance j (p z)
    have hd := synthesis_addResidue s (fun _ => chart.period j) p
      (fun _ => chart.negativePhase j) (by rintro _ ⟨i, rfl⟩; exact hc _) hp
      (by rintro _ ⟨i, rfl⟩; exact hc _)
    let src := s ∪ wordWires dist
    have hrep := Synthesis.word_eq_const (s := src) rep
      (fun i => Or.inl (hr ⟨i, rfl⟩)) (canonicalCycle f (chart.first j))
    have hlt := Synthesis.word_ult (s := src) dist (fun _ => chart.length j)
      (fun i => Or.inr ⟨i, rfl⟩) (fun _ => Or.inl (hc _))
    have hflag := hrep.and hlt
    have hn := wordWires_setWidth_subset (v := n) (s := src) (value := dist)
      (fun _ h => Or.inr h) (Or.inl (hc false))
    have hv := Synthesis.word_add (s := src) (fun _ => BitVec.ofNat n (chart.start j))
      (fun z => (dist z).setWidth n) (fun _ => Or.inl (hc _)) (fun i => hn ⟨i, rfl⟩)
    exact (hd.trans (hflag.union hv)).mono Set.Subset.rfl Set.Subset.rfl
      (by dsimp [chartWidth]; lia)
  have h := synthesis_flaggedRecords s (fun j z => chart.decodeFlag j (rep z) (p z))
    (fun j z i => (chart.decodedRow j (p z)).getLsbD i.val) (140 * (n + 3)) (hc false) hrow
  exact h.mono Set.Subset.rfl Set.Subset.rfl
    (Nat.mul_le_mul_left R (by lia))

end Cslib.Circuits.Boolean.Iteration.CounterIntervalChart
