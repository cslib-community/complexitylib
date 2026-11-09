/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Composition
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Superquadratic sensitivity separation: or

The OR `orBits` of finitely many bits and the disjunction `orCopies f` of `Fintype.card K` disjoint
copies of a Boolean function `f`. Passing to `orCopies f` multiplies the sensitivity bound on
rejected inputs and the block sensitivity at the all-false input by `Fintype.card K`, while the
bound on accepted inputs is unchanged; this balances the zero and one sensitivities of the terminal
predicate.

## Main definitions

* `orBits`: disjunction of a finite family of bits.
* `orCopies`: disjunction of independent copies of a Boolean function, `compose orBits f`.

## Main results

* `sensitivity_orCopies_le`: if `f` has sensitivity at most `S₀` on rejected and at most `S₁` on
  accepted inputs, then `orCopies f` has sensitivity at most `max (Fintype.card K * S₀) S₁`.
* `card_le_blockSensitivityAt_orBits_zero`: `orBits` has block sensitivity at least `Fintype.card K`
  at the all-false input.
* `blockSensitivityAt_orCopies_zero`: the block sensitivity of `orCopies f` at the all-false input
  is at least `Fintype.card K` times that of `f`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/Or.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

variable {I K : Type} [Fintype K]

/-- Disjunction of a finite family of Boolean values. -/
def orBits (x : K → Bool) : Bool := decide (∃ k, x k = true)

/-- `orBits x` is true iff some coordinate of `x` is true. -/
@[simp] theorem orBits_eq_true (x : K → Bool) : orBits x = true ↔ ∃ k, x k = true := by
  simp [orBits]

/-- `orBits x` is false iff every coordinate of `x` is false. -/
@[simp] theorem orBits_eq_false (x : K → Bool) : orBits x = false ↔ ∀ k, x k = false := by
  simp [orBits]

/-- The OR of the all-false vector is `false`. -/
@[simp] theorem orBits_zero : orBits (fun _ : K => false) = false := by
  simp [orBits]

open scoped Classical in
/-- If some coordinate `j ≠ i` of `x` is true, then flipping coordinate `i` does not change
`orBits x`. -/
private theorem orBits_flip_of_witness (x : K → Bool) {i j : K}
    (hji : j ≠ i) (hj : x j = true) : orBits (BitString.flipOn {i} x) = orBits x := by
  have h₁ : orBits x = true := (orBits_eq_true x).mpr ⟨j, hj⟩
  have h₂ : orBits (BitString.flipOn {i} x) = true :=
    (orBits_eq_true _).mpr ⟨j, by rw [BitString.flipOn_singleton_of_ne hji x, hj]⟩
  exact h₂.trans h₁.symm

/-- Disjunction of independent copies of a Boolean function. -/
def orCopies (f : (I → Bool) → Bool) : (K × I → Bool) → Bool := compose orBits f

/-- If `f` rejects the all-false input, then so does `orCopies f`. -/
theorem orCopies_zero (f : (I → Bool) → Bool) (hf : f (fun _ => false) = false) :
    orCopies (K := K) f (fun _ => false) = false := by
  rw [orCopies, compose_zero _ _ hf, orBits_zero]

variable [Fintype I]

/-- If `f` has sensitivity at most `S₀` at every rejected input and at most `S₁` at every accepted
input, then `sensitivity (orCopies f) ≤ max (Fintype.card K * S₀) S₁`. -/
theorem sensitivity_orCopies_le (f : (I → Bool) → Bool) (S₀ S₁ : ℕ)
    (h₀ : ∀ x, f x = false → sensitivityAt f x ≤ S₀)
    (h₁ : ∀ x, f x = true → sensitivityAt f x ≤ S₁) :
    sensitivity (orCopies (K := K) f) ≤ max (Fintype.card K * S₀) S₁ := by
  classical
  apply sensitivity_le
  intro x
  change sensitivityAt (compose orBits f) x ≤ _
  rw [sensitivityAt_compose]
  let y : K → Bool := fun k => f (fun a => x (k, a))
  let s : Finset K := Finset.univ.filter fun i => orBits (BitString.flipOn {i} y) ≠ orBits y
  change (∑ i ∈ s, sensitivityAt f (fun a => x (i, a))) ≤ _
  by_cases hy : orBits y = false
  · have hall := (orBits_eq_false y).mp hy
    calc
      _ ≤ ∑ _i ∈ s, S₀ := Finset.sum_le_sum fun i _ => h₀ _ (hall i)
      _ = s.card * S₀ := by simp
      _ ≤ Fintype.card K * S₀ := Nat.mul_le_mul_right _ (Finset.card_le_univ _)
      _ ≤ max (Fintype.card K * S₀) S₁ := le_max_left _ _
  · have htrue : orBits y = true := by cases h : orBits y <;> simp_all
    obtain ⟨i, hi⟩ := (orBits_eq_true y).mp htrue
    have hs : s ⊆ {i} := by
      intro j hj
      have hc := (Finset.mem_filter.mp hj).2
      by_contra hji
      have hij : i ≠ j := Ne.symm (by simpa only [Finset.mem_singleton] using hji)
      exact hc (orBits_flip_of_witness y hij hi)
    calc
      _ ≤ ∑ j ∈ ({i} : Finset K), sensitivityAt f (fun a => x (j, a)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hs (by intros; exact Nat.zero_le _)
      _ = sensitivityAt f (fun a => x (i, a)) := by simp
      _ ≤ S₁ := h₁ _ hi
      _ ≤ max (Fintype.card K * S₀) S₁ := le_max_right _ _

/-- The block sensitivity of `orBits` at the all-false input is at least `Fintype.card K`. -/
theorem card_le_blockSensitivityAt_orBits_zero :
    Fintype.card K ≤ blockSensitivityAt (orBits (K := K)) (fun _ => false) := by
  classical
  apply le_blockSensitivityAt_of_family orBits (fun _ => false) (fun k : K => {k})
  · intro k
    simp
  · intro k l hkl
    simpa using hkl
  · intro k
    have h : orBits (BitString.flipOn {k} (fun _ : K => false)) = true :=
      (orBits_eq_true _).mpr ⟨k, by simp⟩
    simp [h]

/-- If `f` rejects the all-false input, then `Fintype.card K` times the block sensitivity of `f` at
the all-false input is at most the block sensitivity of `orCopies f` there. -/
theorem blockSensitivityAt_orCopies_zero (f : (I → Bool) → Bool)
    (hf : f (fun _ => false) = false) :
    Fintype.card K * blockSensitivityAt f (fun _ => false) ≤
      blockSensitivityAt (orCopies (K := K) f) (fun _ => false) := by
  exact (Nat.mul_le_mul_right _ card_le_blockSensitivityAt_orBits_zero).trans
    (blockSensitivityAt_compose_zero_le orBits f hf)

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
