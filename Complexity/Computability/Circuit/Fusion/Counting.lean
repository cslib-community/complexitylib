/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Basic
public import Mathlib.Algebra.Order.Floor.Div
import Complexity.Computability.Circuit.Simulation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting failures in a fusion cover

Every witness in a finite sample fails at some atom of a cover. The union bound therefore
turns per-atom failure estimates into circuit-cost lower bounds. The witness type need not be
finite, and the estimates are required only on the actual extracted atoms. In particular,
restricted circuit clients may use their local degree, width or liveness hypotheses.

Witnesses may carry natural-number masses. Clearing denominators represents any finite
nonnegative rational weighting this way. Unit masses recover the cardinality bounds. This is
weighted union counting; it does not remove the fixed-distribution barrier for bounds over all
Boolean gate pairs proved in `Complexity/Computability/Circuit/Fusion/Sampling.lean`.

## Main definitions

* `Cslib.Circuits.Fusion.Atom.failures`: sampled witnesses at which preservation fails.

## Main results

* `Cslib.Circuits.Fusion.Cover.sum_le_mul_cost`: weighted finite witness counting for a cover.
* `Cslib.Circuits.Fusion.sum_le_mul_program_cost`: local bounds on evaluated gates suffice.
* `Cslib.Circuits.Fusion.ceilDiv_sum_le_circuit_cost`: the bound for positive capacity.
* `Cslib.Circuits.Fusion.Cover.card_le_mul_cost`,
  `Cslib.Circuits.Fusion.card_le_mul_program_cost`,
  `Cslib.Circuits.Fusion.ceilDiv_card_le_circuit_cost`: the unit-mass specializations.

## References

* Adapted from LowerBound/Fusion/Counting.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

universe u v w

variable {σ : Signature.{u}} {U : Type v} {W : Type w} {n g m k : ℕ}
  {I : Interpretation σ U} {P : W → U → Prop}

/-- Witnesses in `samples` at which the atom fails to preserve the candidate invariant. -/
noncomputable def Atom.failures (a : Atom σ U) (I : Interpretation σ U)
    (P : W → U → Prop) (samples : Finset W) : Finset W :=
  @Finset.filter W (fun t => ¬ a.Preserves I (P t)) (Classical.decPred _) samples

/-- A witness `t` belongs to `a.failures I P samples` if and only if `t ∈ samples` and `a` does
not preserve `P t` under `I`. -/
@[simp] theorem Atom.mem_failures {a : Atom σ U} {samples : Finset W} {t : W} :
    t ∈ a.failures I P samples ↔ t ∈ samples ∧ ¬ a.Preserves I (P t) := by
  simp only [failures, Finset.mem_filter]

/-- Each witness's mass occurs in at least one atom's failure sum. -/
private theorem sum_le_sum_failures (atoms : Fin k → Atom σ U) (samples : Finset W)
    (mass : W → ℕ)
    (hcover : ∀ t ∈ samples, ¬ ∀ i, (atoms i).Preserves I (P t)) :
    ∑ t ∈ samples, mass t ≤ ∑ i, ∑ t ∈ (atoms i).failures I P samples, mass t := by
  classical
  calc
    ∑ t ∈ samples, mass t ≤
        ∑ t ∈ samples, ∑ i, if ¬ (atoms i).Preserves I (P t) then mass t else 0 := by
      refine Finset.sum_le_sum fun t ht => ?_
      obtain ⟨i, hi⟩ := not_forall.mp (hcover t ht)
      have h := Finset.single_le_sum (f := fun i : Fin k =>
        if ¬ (atoms i).Preserves I (P t) then mass t else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      simpa only [ite_eq_left hi] using h
    _ = ∑ i, ∑ t ∈ (atoms i).failures I P samples, mass t := by
      rw [Finset.sum_comm]
      simp only [Atom.failures, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => ?_
      by_cases ht : (atoms i).Preserves I (P t) <;> simp [ht]

/-- Local failure-mass estimates bound the total mass of any finite sample of witnesses.
Operation costs and witness masses are independent; capacity zero and zero masses are allowed. -/
theorem Cover.sum_le_mul_cost (c : Cover I P) (samples : Finset W) (mass : W → ℕ)
    (weight : σ.Op → ℕ) (capacity : ℕ)
    (hbound : ∀ i, ∑ t ∈ (c.atoms i).failures I P samples, mass t ≤
      capacity * weight (c.atoms i).op) :
    ∑ t ∈ samples, mass t ≤ capacity * c.cost weight := by
  calc
    ∑ t ∈ samples, mass t ≤ ∑ i, ∑ t ∈ (c.atoms i).failures I P samples, mass t :=
      sum_le_sum_failures c.atoms samples mass (fun t _ => c.isCover t)
    _ ≤ ∑ i, capacity * weight (c.atoms i).op := Finset.sum_le_sum fun i _ => hbound i
    _ = capacity * c.cost weight := (Finset.mul_sum ..).symm

/-- Local failure estimates on a cover bound any finite sample of its witnesses.
This multiplicative form also applies when capacity is zero. -/
theorem Cover.card_le_mul_cost (c : Cover I P) (samples : Finset W) (weight : σ.Op → ℕ)
    (capacity : ℕ) (hbound : ∀ i, ((c.atoms i).failures I P samples).card ≤
      capacity * weight (c.atoms i).op) :
    samples.card ≤ capacity * c.cost weight := by
  simpa using c.sum_le_mul_cost samples (fun _ => 1) weight capacity (by simpa using hbound)

/-- Count weighted failures using only the actual evaluated gates. No estimate for other
semantic configurations is required, and supplied inputs must satisfy every sampled invariant. -/
theorem sum_le_mul_program_cost (p : Program σ n g) (I : Interpretation σ U)
    (P : W → U → Prop) (samples : Finset W) (mass : W → ℕ) (input : Fin n → U)
    (hin : ∀ t ∈ samples, ∀ i, P t (input i))
    (hfail : ∀ t ∈ samples, ∃ w, ¬ P t (p.trace I input w))
    (weight : σ.Op → ℕ) (capacity : ℕ)
    (hbound : ∀ k, ∑ t ∈ (programAtoms p I input k).failures I P samples, mass t ≤
      capacity * weight (p.lines k).op) :
    ∑ t ∈ samples, mass t ≤ capacity * p.cost weight := by
  have hcover := programAtoms_isCover p I (fun t : ↥samples => P t) input
    (fun t => hin t t.property) (fun t => hfail t t.property)
  calc
    ∑ t ∈ samples, mass t ≤ ∑ k, ∑ t ∈ (programAtoms p I input k).failures I P samples,
        mass t :=
      sum_le_sum_failures _ samples mass (fun t ht => hcover ⟨t, ht⟩)
    _ ≤ ∑ k, capacity * weight (p.lines k).op := Finset.sum_le_sum fun k _ => hbound k
    _ = capacity * p.cost weight := by rw [p.cost_eq_sum, Finset.mul_sum]

/-- Count a finite sample of failed invariants using bounds on the actual evaluated gates.
No estimate for other semantic configurations is required. -/
theorem card_le_mul_program_cost (p : Program σ n g) (I : Interpretation σ U)
    (P : W → U → Prop) (samples : Finset W) (input : Fin n → U)
    (hin : ∀ t ∈ samples, ∀ i, P t (input i))
    (hfail : ∀ t ∈ samples, ∃ w, ¬ P t (p.trace I input w))
    (weight : σ.Op → ℕ) (capacity : ℕ)
    (hbound : ∀ k, ((programAtoms p I input k).failures I P samples).card ≤
      capacity * weight (p.lines k).op) :
    samples.card ≤ capacity * p.cost weight := by
  simpa using sum_le_mul_program_cost p I P samples (fun _ => 1) input hin hfail
    weight capacity (by simpa using hbound)

/-- Divide total witness mass by a positive failure capacity and round up. Each witness may
fail at a different designated output, and shared gates are charged once. -/
theorem ceilDiv_sum_le_circuit_cost (c : Circuit σ n m) (I : Interpretation σ U)
    (P : W → U → Prop) (samples : Finset W) (mass : W → ℕ) (input : Fin n → U)
    (hin : ∀ t ∈ samples, ∀ i, P t (input i))
    (hfail : ∀ t ∈ samples, ∃ o, ¬ P t (c.eval I input o))
    (weight : σ.Op → ℕ) {capacity : ℕ} (hpos : 0 < capacity)
    (hbound : ∀ k, ∑ t ∈ (programAtoms c.program I input k).failures I P samples, mass t ≤
      capacity * weight (c.program.lines k).op) :
    (∑ t ∈ samples, mass t) ⌈/⌉ capacity ≤ c.program.cost weight :=
  (ceilDiv_le_iff_le_mul hpos).mpr (sum_le_mul_program_cost c.program I P samples mass input
    hin (fun t ht => (hfail t ht).elim fun o ho => ⟨c.outputs o, ho⟩) weight capacity hbound)

/-- A positive capacity converts the local counting bound into a rounded-up cost bound.
Each witness may fail at a different output, and shared gates are charged once. -/
theorem ceilDiv_card_le_circuit_cost (c : Circuit σ n m) (I : Interpretation σ U)
    (P : W → U → Prop) (samples : Finset W) (input : Fin n → U)
    (hin : ∀ t ∈ samples, ∀ i, P t (input i))
    (hfail : ∀ t ∈ samples, ∃ o, ¬ P t (c.eval I input o))
    (weight : σ.Op → ℕ) {capacity : ℕ} (hpos : 0 < capacity)
    (hbound : ∀ k, ((programAtoms c.program I input k).failures I P samples).card ≤
      capacity * weight (c.program.lines k).op) :
    samples.card ⌈/⌉ capacity ≤ c.program.cost weight := by
  simpa using ceilDiv_sum_le_circuit_cost c I P samples (fun _ => 1) input hin hfail
    weight hpos (by simpa using hbound)

end Cslib.Circuits.Fusion
