/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Mobius
public import CslibFrontier.Foundations.BooleanAnalysis.MultilinearExtension
public import Mathlib.Data.ZMod.Basic

/-!
# The degree of OR over a ring

A polynomial `p` over a nontrivial commutative ring `R`, multilinear or not, that agrees with
`OR` on the cube `{0, 1}ⁿ` has total degree at least `n` (`card_le_totalDegree_of_eval_eq_or`).
If its degree `D` were smaller, its values on the cube would lie in the span of the monomials of
at most `D` coordinates (`lowDegree_eq_map_restrictTotalDegree`), so their subset Möbius transform
would vanish on the set of all coordinates (`subsetMobius_eq_zero_of_mem_lowDegree`). For `OR`
that transform is `-(-1)ⁿ ≠ 0`: `OR = 1 - [x = 0]`, the constant contributes nothing at a nonempty
set, and the indicator of the zero point contributes `(-1)ⁿ`. The bound is attained by
`1 - ∏ᵢ (1 - xᵢ)` (`orPoly`, `totalDegree_orPoly`).

Over `GF(q) = ZMod q`, `q` prime, this is Exercise 6 of Chapter 13 of
[Arora and Barak, draft of 2007-01-08][AroraBarak07] (`le_totalDegree_of_eval_eq_or_zmod`).
The proof uses no property of the ring beyond `0 ≠ 1`.

## Main definitions

* `Cslib.BitString.orPoly`: the polynomial `1 - ∏ᵢ (1 - Xᵢ)`.

## Main results

* `Cslib.BitString.card_le_totalDegree_of_eval_eq_or`: a polynomial agreeing with `OR` on the cube
  has total degree at least the number of variables.
* `Cslib.BitString.eval_orPoly`, `Cslib.BitString.totalDegree_orPoly`: `1 - ∏ᵢ (1 - Xᵢ)` agrees
  with `OR` on the cube and has total degree exactly the number of variables.
* `Cslib.BitString.le_totalDegree_of_eval_eq_or_zmod`: the statement over `GF(q)` on `n`
  variables.

## References

* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, draft of
  2007-01-08][AroraBarak07]
-/

public section

namespace Cslib.BitString

open MvPolynomial Finset

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- The subset Möbius transform of `OR` on the set of all coordinates is `-(-1)ⁿ`. -/
private theorem subsetMobius_or_univ [DecidableEq ι] [Nonempty ι] :
    subsetMobius (fun T : Finset ι => bitVal R (decide (∃ i, decide (i ∈ T) = true))) univ =
      -(-1 : R) ^ Fintype.card ι := by
  have hconst := subsetMobius_monomial (R := R) (∅ : Finset ι) univ
  rw [ite_eq_right_iff.2 fun h => absurd h Finset.univ_nonempty.ne_empty.symm] at hconst
  have hor : ∀ T : Finset ι, bitVal R (decide (∃ i, decide (i ∈ T) = true)) =
      monomial R ∅ (fun i => decide (i ∈ T)) - if T = ∅ then 1 else 0 := by
    intro T
    rcases T.eq_empty_or_nonempty with rfl | ⟨i, hi⟩
    · simp [monomial]
    · have hT : T ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨i, hi⟩
      have hex : ∃ j, j ∈ T := ⟨i, hi⟩
      simp [monomial, hT, hex]
  simp only [subsetMobius] at hconst ⊢
  simp_rw [hor, smul_sub, Finset.sum_sub_distrib, hconst, smul_ite, smul_zero,
    Finset.sum_ite_eq' _ (∅ : Finset ι), Finset.empty_mem_powerset, ite_true, card_empty,
    Nat.sub_zero, card_univ, zsmul_eq_mul, mul_one, Int.cast_pow, Int.cast_neg, Int.cast_one,
    zero_sub]

/-- **OR has degree `n` on the cube** [AroraBarak07, Chapter 13, Exercise 6]: over a nontrivial
commutative ring, every polynomial, multilinear or not, that agrees with `OR` on `{0, 1}ⁿ` has
total degree at least `n`. -/
theorem card_le_totalDegree_of_eval_eq_or [Nontrivial R] {p : MvPolynomial ι R}
    (hp : ∀ x : ι → Bool, eval (bitPoint x) p = bitVal R (decide (∃ i, x i = true))) :
    Fintype.card ι ≤ p.totalDegree := by
  classical
  by_contra! h
  have : Nonempty ι := Fintype.card_pos_iff.1 (Nat.zero_lt_of_lt h)
  have hmem : (fun x : ι → Bool => bitVal R (decide (∃ i, x i = true))) ∈
      lowDegree R ι p.totalDegree := by
    simpa only [← hp] using eval_mem_lowDegree p le_rfl
  have h0 := subsetMobius_eq_zero_of_mem_lowDegree hmem (S := univ) (by simpa using h)
  rw [subsetMobius_or_univ, neg_eq_zero] at h0
  exact (isUnit_one.neg.pow _).ne_zero h0

variable (ι R) in
/-- The polynomial `1 - ∏ᵢ (1 - Xᵢ)`, which computes `OR` on the cube. -/
noncomputable def orPoly : MvPolynomial ι R :=
  1 - ∏ i, (1 - X i)

/-- `1 - ∏ᵢ (1 - Xᵢ)` agrees with `OR` on the cube. -/
theorem eval_orPoly (x : ι → Bool) :
    eval (bitPoint x) (orPoly ι R) = bitVal R (decide (∃ i, x i = true)) := by
  classical
  by_cases h : ∃ i, x i = true
  · obtain ⟨i, hi⟩ := h
    rw [decide_eq_true ⟨i, hi⟩, orPoly, map_sub, map_one, map_prod,
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [bitPoint, hi])]
    simp
  · push Not at h
    rw [decide_eq_false (by simpa using h), orPoly, map_sub, map_one, map_prod]
    simp [bitPoint, h]

/-- `1 - ∏ᵢ (1 - Xᵢ)` has total degree at most the number of variables. -/
theorem totalDegree_orPoly_le : (orPoly ι R).totalDegree ≤ Fintype.card ι := by
  refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i, (1 - X i : MvPolynomial ι R).totalDegree ≤ ∑ _i : ι, 1 :=
        Finset.sum_le_sum fun i _ => (totalDegree_sub _ _).trans
          (max_le (by simp) ((totalDegree_monomial_le _ _).trans (by simp)))
    _ = Fintype.card ι := by simp

/-- **The bound is attained**: over a nontrivial commutative ring, `1 - ∏ᵢ (1 - Xᵢ)` has total
degree exactly the number of variables. -/
theorem totalDegree_orPoly [Nontrivial R] : (orPoly ι R).totalDegree = Fintype.card ι :=
  le_antisymm totalDegree_orPoly_le (card_le_totalDegree_of_eval_eq_or eval_orPoly)

/-- **OR over `GF(q)`** [AroraBarak07, Chapter 13, Exercise 6]: for a prime `q`, every polynomial
over `ZMod q` in `n` variables, not necessarily multilinear, that agrees with `OR` on `{0, 1}ⁿ`
has total degree at least `n`; `orPoly` attains `n` (`totalDegree_orPoly`). -/
theorem le_totalDegree_of_eval_eq_or_zmod {q n : ℕ} [Fact q.Prime]
    {p : MvPolynomial (Fin n) (ZMod q)}
    (hp : ∀ x : Fin n → Bool, eval (bitPoint x) p = bitVal (ZMod q) (decide (∃ i, x i = true))) :
    n ≤ p.totalDegree := by
  convert card_le_totalDegree_of_eval_eq_or (ι := Fin n) fun x => by rw [hp x]; congr
  simp

end Cslib.BitString
