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

## Main definitions

* `Cslib.Circuits.Fusion.Atom.failures`: sampled witnesses at which preservation fails.

## Main results

* `Cslib.Circuits.Fusion.Cover.card_le_mul_cost`: finite witness counting for a cover.
* `Cslib.Circuits.Fusion.card_le_mul_program_cost`: local bounds on evaluated gates suffice.
* `Cslib.Circuits.Fusion.ceilDiv_card_le_circuit_cost`: the bound for positive capacity.

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

@[simp] theorem Atom.mem_failures {a : Atom σ U} {samples : Finset W} {t : W} :
    t ∈ a.failures I P samples ↔ t ∈ samples ∧ ¬ a.Preserves I (P t) := by
  simp only [failures, Finset.mem_filter]

/-- The sampled witnesses are covered by the union of the atoms' failures. -/
private theorem card_le_sum_failures (atoms : Fin k → Atom σ U) (samples : Finset W)
    (hcover : ∀ t ∈ samples, ¬ ∀ i, (atoms i).Preserves I (P t)) :
    samples.card ≤ ∑ i, ((atoms i).failures I P samples).card := by
  classical
  refine (Finset.card_le_card (t := Finset.univ.biUnion
    (fun i => (atoms i).failures I P samples)) ?_).trans Finset.card_biUnion_le
  intro t ht
  obtain ⟨i, hi⟩ := not_forall.mp (hcover t ht)
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Atom.mem_failures.mpr ⟨ht, hi⟩⟩

/-- Local failure estimates on a cover bound any finite sample of its witnesses.
This multiplicative form also applies when capacity is zero. -/
theorem Cover.card_le_mul_cost (c : Cover I P) (samples : Finset W) (weight : σ.Op → ℕ)
    (capacity : ℕ) (hbound : ∀ i, ((c.atoms i).failures I P samples).card ≤
      capacity * weight (c.atoms i).op) :
    samples.card ≤ capacity * c.cost weight := by
  calc
    samples.card ≤ ∑ i, ((c.atoms i).failures I P samples).card :=
      card_le_sum_failures c.atoms samples (fun t _ => c.isCover t)
    _ ≤ ∑ i, capacity * weight (c.atoms i).op := Finset.sum_le_sum fun i _ => hbound i
    _ = capacity * c.cost weight := (Finset.mul_sum ..).symm

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
  have hcover := programAtoms_isCover p I (fun t : ↥samples => P t) input
    (fun t => hin t t.property) (fun t => hfail t t.property)
  calc
    samples.card ≤ ∑ k, ((programAtoms p I input k).failures I P samples).card :=
      card_le_sum_failures _ samples (fun t ht => hcover ⟨t, ht⟩)
    _ ≤ ∑ k, capacity * weight (p.lines k).op := Finset.sum_le_sum fun k _ => hbound k
    _ = capacity * p.cost weight := by rw [p.cost_eq_sum, Finset.mul_sum]

/-- A positive capacity converts the local counting bound into a rounded-up cost bound.
Each witness may fail at a different output, and shared gates are charged once. -/
theorem ceilDiv_card_le_circuit_cost (c : Circuit σ n m) (I : Interpretation σ U)
    (P : W → U → Prop) (samples : Finset W) (input : Fin n → U)
    (hin : ∀ t ∈ samples, ∀ i, P t (input i))
    (hfail : ∀ t ∈ samples, ∃ o, ¬ P t (c.eval I input o))
    (weight : σ.Op → ℕ) {capacity : ℕ} (hpos : 0 < capacity)
    (hbound : ∀ k, ((programAtoms c.program I input k).failures I P samples).card ≤
      capacity * weight (c.program.lines k).op) :
    samples.card ⌈/⌉ capacity ≤ c.program.cost weight :=
  (ceilDiv_le_iff_le_mul hpos).mpr (card_le_mul_program_cost c.program I P samples input hin
    (fun t ht => (hfail t ht).elim fun o ho => ⟨c.outputs o, ho⟩) weight capacity hbound)

end Cslib.Circuits.Fusion
