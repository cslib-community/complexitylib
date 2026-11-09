/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Parity

/-!
# Interpolating two table entries by a parity

The values of a Boolean table `f` with `f 0 = false` at any two points of the cube agree with
some parity. The zero point and repeated points impose the only consistency conditions on two
answers. The parity can be chosen on finitely many coordinates even when the coordinate type
is infinite. This elementary interpolation lemma is proved by choosing separating coordinates.

## Main results

* `Cslib.BitString.exists_parityOn_agrees_pair`: a normalized table agrees with a parity at two
  specified points.

## References

The interpolation argument in this module is elementary and original to this formalization.
-/

public section

namespace Cslib.BitString

variable {ι : Type*}

private theorem exists_true_of_ne_zero {x : ι → Bool} (hx : x ≠ 0) : ∃ i, x i = true := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ false := by
    by_contra! h
    exact hx (funext h)
  exact ⟨i, Bool.eq_true_of_not_eq_false hi⟩

private theorem exists_parityOn_true_false {x y : ι → Bool} (hx : x ≠ 0) (hxy : x ≠ y) :
    ∃ S : Finset ι, parityOn S x = true ∧ parityOn S y = false := by
  classical
  obtain ⟨i, hi⟩ := exists_true_of_ne_zero hx
  by_cases hyi : y i = false
  · exact ⟨{i}, by simpa only [parityOn_singleton] using hi,
      by simpa only [parityOn_singleton] using hyi⟩
  have hyi : y i = true := Bool.eq_true_of_not_eq_false hyi
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
    by_contra! h
    exact hxy (funext h)
  by_cases hxj : x j = true
  · have hyj : y j = false := by
      cases hy : y j
      · rfl
      · exact (hj (hxj.trans hy.symm)).elim
    exact ⟨{j}, by simpa only [parityOn_singleton] using hxj,
      by simpa only [parityOn_singleton] using hyj⟩
  · have hxj : x j = false := Bool.eq_false_of_not_eq_true hxj
    have hyj : y j = true := by
      cases hy : y j
      · exact (hj (hxj.trans hy.symm)).elim
      · rfl
    have hij : i ≠ j := by
      intro h
      subst j
      rw [hi] at hxj
      contradiction
    refine ⟨{i, j}, ?_, ?_⟩
    · simp [parityOn_insert, hij, hi, hxj]
    · simp [parityOn_insert, hij, hyi, hyj]

/-- Any two answers of a table that is false at zero extend to a parity. The two points may
coincide or be zero; no finiteness assumption on the coordinate type is needed. -/
theorem exists_parityOn_agrees_pair {f : (ι → Bool) → Bool} (hf : f 0 = false)
    (x y : ι → Bool) : ∃ S : Finset ι, parityOn S x = f x ∧ parityOn S y = f y := by
  cases hfx : f x <;> cases hfy : f y
  · exact ⟨∅, parityOn_empty x, parityOn_empty y⟩
  · have hy : y ≠ 0 := by
      intro h
      rw [h, hf] at hfy
      contradiction
    have hyx : y ≠ x := by
      intro h
      rw [h, hfx] at hfy
      contradiction
    obtain ⟨S, hSy, hSx⟩ := exists_parityOn_true_false hy hyx
    exact ⟨S, hSx, hSy⟩
  · have hx : x ≠ 0 := by
      intro h
      rw [h, hf] at hfx
      contradiction
    have hxy : x ≠ y := by
      intro h
      rw [h, hfy] at hfx
      contradiction
    obtain ⟨S, hSx, hSy⟩ := exists_parityOn_true_false hx hxy
    exact ⟨S, hSx, hSy⟩
  · have hx : x ≠ 0 := by
      intro h
      rw [h, hf] at hfx
      contradiction
    have hy : y ≠ 0 := by
      intro h
      rw [h, hf] at hfy
      contradiction
    have hxy : x ≠ x + y := by
      intro h
      apply hy
      exact (add_left_cancel ((add_zero x).trans h)).symm
    obtain ⟨S, hSx, hSsum⟩ := exists_parityOn_true_false hx hxy
    refine ⟨S, hSx, ?_⟩
    have hadd := parityOn_add S x y
    rw [hSsum, hSx] at hadd
    cases hSy : parityOn S y
    · rw [hSy] at hadd
      cases hadd
    · rfl

end Cslib.BitString
