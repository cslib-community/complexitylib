/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Basic
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Superquadratic sensitivity separation: composition

Disjoint Boolean composition `compose f g` on the coordinate type `I × J`: the inner function `g` is
evaluated on each row `fun j => x (i, j)`, and the outer function `f` on the resulting vector of row
values, so each child keeps its own raw coordinates. Sensitivity is submultiplicative under
composition, while block sensitivity at the all-false input is supermultiplicative when `g` rejects
the all-false input.

## Main definitions

* `compose`: block composition `x ↦ f (fun i => g (fun j => x (i, j)))`.

## Main results

* `compose_flip_sensitive_iff`: coordinate `(i, j)` is sensitive for `compose f g` iff `j` is
  sensitive for `g` on row `i` and `i` is sensitive for `f` on the row values.
* `sensitivityAt_compose`: the sensitivity of `compose f g` at `x` is the sum of the inner
  sensitivities over the rows that are sensitive for `f`.
* `sensitivity_compose_le`: `sensitivity (compose f g) ≤ sensitivity f * sensitivity g`.
* `blockSensitivityAt_compose_zero_le`: block sensitivities at the all-false input are
  supermultiplicative under composition, provided `g` rejects the all-false input.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/Composition.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

variable {I J : Type}

/-- Block composition: evaluate the inner function in each row, then the outer function. -/
def compose (f : (I → Bool) → Bool) (g : (J → Bool) → Bool) :
    (I × J → Bool) → Bool :=
  fun x => f (fun i => g (fun j => x (i, j)))

open scoped Classical in
/-- Flipping coordinate `(i, j)` changes `compose f g x` iff flipping `j` changes the value of `g`
on row `i` of `x`, and flipping `i` changes the value of `f` on the vector of row values
`fun k => g (fun a => x (k, a))`. -/
theorem compose_flip_sensitive_iff [DecidableEq (I × J)]
    (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (x : I × J → Bool) (i : I) (j : J) :
    compose f g (BitString.flipOn {(i, j)} x) ≠ compose f g x ↔
      g (BitString.flipOn {j} (fun a => x (i, a))) ≠ g (fun a => x (i, a)) ∧
      f (BitString.flipOn {i} (fun k => g (fun a => x (k, a)))) ≠
        f (fun k => g (fun a => x (k, a))) := by
  by_cases hg : g (BitString.flipOn {j} (fun a => x (i, a))) = g (fun a => x (i, a))
  · have he : (fun k => g (fun a => BitString.flipOn {(i, j)} x (k, a))) =
        fun k => g (fun a => x (k, a)) := by
      funext k
      by_cases hk : k = i
      · subst k
        rw [BitString.flipOn_prod_same, hg]
      · rw [BitString.flipOn_prod_of_ne x j hk]
    simp only [compose, he, ne_eq, not_true_eq_false, hg, false_and]
  · have hn : g (BitString.flipOn {j} (fun a => x (i, a))) = !(g (fun a => x (i, a))) := by
      cases h₁ : g (BitString.flipOn {j} (fun a => x (i, a))) <;>
        cases h₂ : g (fun a => x (i, a)) <;> simp_all
    have he : (fun k => g (fun a => BitString.flipOn {(i, j)} x (k, a))) =
        BitString.flipOn {i} (fun k => g (fun a => x (k, a))) := by
      funext k
      by_cases hk : k = i
      · subst k
        rw [BitString.flipOn_prod_same, BitString.flipOn_singleton_self, hn]
      · rw [BitString.flipOn_prod_of_ne x j hk, BitString.flipOn_singleton_of_ne hk]
    simp only [compose, he, ne_eq, hg, not_false_eq_true, true_and]

/-- If `g` rejects the all-false input, then `compose f g` and `f` take the same value on the
all-false input. -/
theorem compose_zero (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (hg : g (fun _ => false) = false) :
    compose f g (fun _ => false) = f (fun _ => false) := by
  simp [compose, hg]

open scoped Classical in
/-- If `g` rejects the all-false input and flipping the block `D` changes its value there, then
flipping the product block `C ×ˢ D` in the all-false input of `compose f g` gives the value of `f`
on the all-false input with `C` flipped. -/
private theorem compose_flip_product_zero [DecidableEq (I × J)]
    (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (C : Finset I) (D : Finset J) (hg : g (fun _ => false) = false)
    (hD : g (BitString.flipOn D (fun _ => false)) ≠ g (fun _ => false)) :
    compose f g (BitString.flipOn (C ×ˢ D) (fun _ => false)) =
      f (BitString.flipOn C (fun _ => false)) := by
  have hD' : g (BitString.flipOn D (fun _ => false)) = true := by
    cases he : g (BitString.flipOn D (fun _ => false)) <;> simp_all
  apply congrArg f
  funext i
  by_cases hi : i ∈ C
  · have he : (fun j => BitString.flipOn (C ×ˢ D) (fun _ => false) (i, j)) =
        BitString.flipOn D (fun _ => false) := by
      funext j
      simp [BitString.flipOn_apply, hi]
    rw [he, hD']
    simp [BitString.flipOn_apply, hi]
  · have he : (fun j => BitString.flipOn (C ×ˢ D) (fun _ => false) (i, j)) =
        fun _ => false := by
      funext j
      simp [BitString.flipOn_apply, hi]
    rw [he, hg]
    simp [BitString.flipOn_apply, hi]

section Finite
variable [Fintype I] [Fintype J]

open scoped Classical in
/-- The sensitivity of `compose f g` at `x` equals the sum, over the rows `i` that are sensitive for
`f` at the vector of row values, of the sensitivity of `g` at row `i` of `x`. -/
theorem sensitivityAt_compose (f : (I → Bool) → Bool) (g : (J → Bool) → Bool)
    (x : I × J → Bool) :
    sensitivityAt (compose f g) x =
      ∑ i ∈ Finset.univ.filter (fun i =>
        f (BitString.flipOn {i} (fun k => g (fun a => x (k, a)))) ≠
          f (fun k => g (fun a => x (k, a)))),
        sensitivityAt g (fun a => x (i, a)) := by
  simp only [sensitivityAt, Finset.card_eq_sum_ones, Finset.sum_filter,
    compose_flip_sensitive_iff, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : f (BitString.flipOn {i} (fun k => g (fun a => x (k, a)))) ≠
      f (fun k => g (fun a => x (k, a)))
  · simp [hi]
  · simp [hi]

/-- Sensitivity is submultiplicative under composition:
`sensitivity (compose f g) ≤ sensitivity f * sensitivity g`. -/
theorem sensitivity_compose_le (f : (I → Bool) → Bool) (g : (J → Bool) → Bool) :
    sensitivity (compose f g) ≤ sensitivity f * sensitivity g := by
  classical
  apply sensitivity_le
  intro x
  rw [sensitivityAt_compose]
  calc
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        f (BitString.flipOn {i} (fun k => g (fun a => x (k, a)))) ≠
          f (fun k => g (fun a => x (k, a)))), sensitivity g :=
      Finset.sum_le_sum fun i _ => sensitivityAt_le_sensitivity g _
    _ = sensitivityAt f (fun k => g (fun a => x (k, a))) * sensitivity g := by
      simp [sensitivityAt]
    _ ≤ sensitivity f * sensitivity g :=
      Nat.mul_le_mul_right _ (sensitivityAt_le_sensitivity f _)

/-- If `g` rejects the all-false input, then the product of the block sensitivities of `f` and `g`
at the all-false input is at most the block sensitivity of `compose f g` there. -/
theorem blockSensitivityAt_compose_zero_le (f : (I → Bool) → Bool)
    (g : (J → Bool) → Bool) (hg : g (fun _ => false) = false) :
    blockSensitivityAt f (fun _ => false) * blockSensitivityAt g (fun _ => false) ≤
      blockSensitivityAt (compose f g) (fun _ => false) := by
  classical
  obtain ⟨S, hS, hdS, hbS⟩ := exists_blockSensitivityAt_family f (fun _ => false)
  obtain ⟨T, hT, hdT, hbT⟩ := exists_blockSensitivityAt_family g (fun _ => false)
  have h := le_blockSensitivityAt_of_family (compose f g) (fun _ => false)
    (fun p : S × T => p.1.val ×ˢ p.2.val)
    (by
      intro p
      obtain ⟨i, hi⟩ := (hbS p.1.val p.1.property).1
      obtain ⟨j, hj⟩ := (hbT p.2.val p.2.property).1
      exact ⟨(i, j), Finset.mem_product.mpr ⟨hi, hj⟩⟩)
    (by
      intro p q hpq
      apply Finset.disjoint_left.mpr
      intro a ha hq
      obtain ⟨ha₁, ha₂⟩ := Finset.mem_product.mp ha
      obtain ⟨hq₁, hq₂⟩ := Finset.mem_product.mp hq
      by_cases hs : p.1 = q.1
      · have ht : p.2.val ≠ q.2.val := by
          intro h
          exact hpq (Prod.ext hs (Subtype.ext h))
        exact Finset.disjoint_left.mp (hdT _ p.2.property _ q.2.property ht) ha₂ hq₂
      · have hs' : p.1.val ≠ q.1.val := fun h => hs (Subtype.ext h)
        exact Finset.disjoint_left.mp (hdS _ p.1.property _ q.1.property hs') ha₁ hq₁)
    (by
      intro p
      rw [BitString.flipOn_congr_decidableEq,
        compose_flip_product_zero f g _ _ hg (hbT p.2.val p.2.property).2,
        compose_zero f g hg]
      exact (hbS p.1.val p.1.property).2)
  simpa only [Fintype.card_prod, Fintype.card_coe, hS, hT] using h

end Finite
end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
