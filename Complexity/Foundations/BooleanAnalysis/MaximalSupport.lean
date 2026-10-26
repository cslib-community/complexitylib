/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Degree
import Complexity.Foundations.BooleanAnalysis.Influence

/-!
# Maximal Fourier supports on faces of the Boolean cube

If `S` has a nonzero Fourier coefficient and every strict superset has coefficient zero, then
every face obtained by fixing the coordinates outside `S` contains a nonzero value. If `S` is
nonempty, the function is nonconstant on each such face. Differentiating in a coordinate of `S`
reduces both claims to a smaller support.

The nonconstant-face statement is the Fourier form of the maximal-monomial observation in
[Midrijanis2004], Lemma 3. A support of maximum cardinality is also maximal under inclusion, so
this supplies the sensitive block used in the decision tree bound `D(f) ≤ deg(f) bs(f)`.

## Main results

* `Cslib.BitString.exists_ne_zero_on_face_of_fourierCoeff_maximal`: every face parallel to a
  maximal Fourier support contains a nonzero value.
* `Cslib.BitString.exists_ne_on_face_of_fourierCoeff_maximal`: a nonempty maximal Fourier
  support makes every parallel face nonconstant.

## References

* [G. Midrijanis, *Exact quantum query complexity for total Boolean functions*][Midrijanis2004]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A maximal nonzero Fourier coefficient forces a nonzero value on every face obtained by
fixing the coordinates outside its support. -/
theorem exists_ne_zero_on_face_of_fourierCoeff_maximal (S : Finset ι) :
    ∀ f : (ι → Bool) → ℝ, fourierCoeff f S ≠ 0 →
      (∀ T, S ⊂ T → fourierCoeff f T = 0) → ∀ x : ι → Bool,
      ∃ y, (∀ i, i ∉ S → y i = x i) ∧ f y ≠ 0 := by
  induction S using Finset.induction_on with
  | empty =>
    intro f hS hT x
    refine ⟨x, fun _ _ => rfl, ?_⟩
    have hconst : f x = fourierCoeff f ∅ := by
      rw [← sum_fourierCoeff_mul_chi f x, sum_eq_single (∅ : Finset ι)]
      · rw [chi_empty, mul_one]
      · intro T _ hT0
        rw [hT T (empty_ssubset.2 (nonempty_iff_ne_empty.2 hT0)), zero_mul]
      · exact fun h => absurd (mem_univ _) h
    rwa [hconst]
  | insert i S hi ih =>
    intro f hS hT x
    have h₁ : fourierCoeff (derivative i f) S ≠ 0 := by
      rwa [fourierCoeff_derivative, ite_eq_right hi]
    have h₂ (T : Finset ι) (hST : S ⊂ T) : fourierCoeff (derivative i f) T = 0 := by
      rw [fourierCoeff_derivative]
      split_ifs with hiT
      · rfl
      · refine hT _ (Finset.ssubset_iff_subset_ne.2
          ⟨insert_subset_insert i hST.1, fun heq => hST.ne ?_⟩)
        rw [← erase_insert hi, heq, erase_insert hiT]
    obtain ⟨y, hy, hfy⟩ := ih (derivative i f) h₁ h₂ x
    have hvalue : f (update y i false) ≠ 0 ∨ f (update y i true) ≠ 0 := by
      by_contra h
      push Not at h
      exact hfy (by simp [derivative, h.1, h.2])
    rcases hvalue with hvalue | hvalue
    all_goals
      refine ⟨_, ?_, hvalue⟩
      intro j hj
      have hji : j ≠ i := fun h => hj (by simp [h])
      rw [update_of_ne hji]
      exact hy j (notMem_subset (subset_insert i S) hj)

/-- A nonempty maximal Fourier support makes every parallel face nonconstant. This is the
Fourier form of [Midrijanis2004], Lemma 3. -/
theorem exists_ne_on_face_of_fourierCoeff_maximal {S : Finset ι} (hS : S.Nonempty)
    {f : (ι → Bool) → ℝ} (hf : fourierCoeff f S ≠ 0)
    (hmax : ∀ T, S ⊂ T → fourierCoeff f T = 0) (x : ι → Bool) :
    ∃ y, (∀ i, i ∉ S → y i = x i) ∧ f y ≠ f x := by
  have hcoeff : fourierCoeff (fun y => f y - f x) S ≠ 0 := by
    simpa [fourierCoeff_sub, fourierCoeff_const, hS.ne_empty] using hf
  have hsup (T : Finset ι) (hST : S ⊂ T) :
      fourierCoeff (fun y => f y - f x) T = 0 := by
    rw [fourierCoeff_sub, fourierCoeff_const, ite_eq_right (hS.mono hST.1).ne_empty, sub_zero]
    exact hmax T hST
  obtain ⟨y, hy, hfy⟩ := exists_ne_zero_on_face_of_fourierCoeff_maximal S _ hcoeff hsup x
  exact ⟨y, hy, sub_ne_zero.1 hfy⟩

end Cslib.BitString
