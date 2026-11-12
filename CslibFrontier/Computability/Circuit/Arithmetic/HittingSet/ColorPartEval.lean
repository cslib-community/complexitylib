/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ColorPart
public import CslibFrontier.Foundations.Data.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Evaluating the colour part of a polynomial

The colour part `colorPart c G` of a polynomial `G` (the sum of its monomials with exactly one
variable of each colour, to the first power) is not zero as soon as `G` has one such monomial
(`colorPart_ne_zero`), and its values are reached from values of `G` itself: if
`colorPart c G` does not vanish at a point `b`, then `G` does not vanish at one of the points
obtained from `b` by setting the variables of some colours to zero and scaling the others by an
element `t` of a set with more than `G.totalDegree` elements
(`exists_eval_ne_zero_of_eval_colorPart_ne_zero`).

The second statement is an interpolation. Scaling the variables of colour `j` by a new variable
`yⱼ` turns `G` into a polynomial in `y` whose coefficients are the values at `b` of the weighted
homogeneous components of `G` (`MvPolynomial.coeff_aeval_monomial`). The coefficient of
`y₁ ⋯ yᵣ` is then the coefficient of `z ^ r` in the alternating sum, over the sets `J` of
colours, of the polynomials obtained by substituting `0` for `yⱼ`, `j ∈ J`, and `z` for the
other `yⱼ`, as in Ryser's formula for the permanent.

## Main results

* `colorPart_ne_zero`: [Shpilka2026, Lemma 3.1].
* `exists_eval_ne_zero_of_eval_colorPart_ne_zero`: [Shpilka2026, Lemma 3.2].

## References

* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], §3, Lemmas 3.1 and 3.2, pp. 6–7 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

variable {σ τ F : Type*} {r : ℕ}

/-- [Shpilka2026, Lemma 3.1]: the colour part of a polynomial is not zero if the polynomial has
a multilinear monomial of degree `r` whose variables have distinct colours. -/
theorem colorPart_ne_zero [CommSemiring F] (c : σ → Fin r) {G : MvPolynomial σ F}
    {m : σ →₀ ℕ} (hm : m ∈ G.support) (hmul : ∀ v, m v ≤ 1) (hc : Set.InjOn c m.support)
    (hcard : m.support.card = r) : colorPart c G ≠ 0 := by
  classical
  have hw : Finsupp.weight (colorWeight c) m = colorOnes r := by
    ext j
    have himg : m.support.image c = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [Finset.card_image_of_injOn hc, hcard, Fintype.card_fin])
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (himg ▸ Finset.mem_univ j)
    have hv1 : m v = 1 := le_antisymm (hmul v) (Finsupp.mem_support_iff.1 hv).bot_lt
    rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.finsetSum_apply,
      Finset.sum_eq_single_of_mem v hv fun u hu huv => ?_]
    · simp [colorWeight, colorOnes, hv1]
    · simpa [colorWeight, Finsupp.single_apply] using fun h => absurd (hc hu hv h) huv
  intro h
  have hcoeff : (colorPart c G).coeff m = G.coeff m := by
    simp only [colorPart, coeff_weightedHomogeneousComponent, hw, ↓reduceIte]
  exact mem_support_iff.1 hm (by rw [← hcoeff, h]; rfl)

private theorem eq_colorOnes_iff (e : Fin r →₀ ℕ) :
    e = colorOnes r ↔ e.support = Finset.univ ∧ ∑ j ∈ e.support, e j = r := by
  have hs : (colorOnes r).support = Finset.univ := by ext j; simp [colorOnes]
  refine ⟨?_, fun ⟨h, hd⟩ => ?_⟩
  · rintro rfl
    exact ⟨hs, by rw [hs]; simp [colorOnes]⟩
  · have h1 : ∀ j ∈ Finset.univ, (colorOnes r) j ≤ e j := fun j _ => by
      have : e j ≠ 0 := Finsupp.mem_support_iff.1 (h ▸ Finset.mem_univ j)
      simpa [colorOnes] using Nat.one_le_iff_ne_zero.2 this
    ext j
    refine ((Finset.sum_eq_sum_iff_of_le h1).1 ?_ j (Finset.mem_univ j)).symm
    rw [← h, hd, h]
    simp [colorOnes]

/-- Inclusion–exclusion for the coefficient of `y₁ ⋯ yᵣ`, as in Ryser's formula: it is the
coefficient of `z ^ r` in the alternating sum, over the sets `J` of variables, of the
substitutions of `0` for the variables in `J` and `z` for the others. -/
private theorem coeff_sum_neg_one_pow_card_smul_aeval [CommRing F]
    (T : MvPolynomial (Fin r) F) :
    (∑ J : Finset (Fin r), (-1 : ℤ) ^ J.card •
      aeval (fun j => if j ∈ J then 0 else (Polynomial.X : Polynomial F)) T).coeff r =
      T.coeff (colorOnes r) := by
  classical
  induction T using MvPolynomial.induction_on' with
  | monomial e a =>
    have hJ (J : Finset (Fin r)) :
        aeval (fun j => if j ∈ J then 0 else (Polynomial.X : Polynomial F)) (monomial e a) =
          if J ∈ e.supportᶜ.powerset then
            Polynomial.C a * Polynomial.X ^ ∑ j ∈ e.support, e j else 0 := by
      rw [aeval_monomial, Finsupp.prod]
      simp only [Finset.mem_powerset]
      split_ifs with h
      · rw [← Finset.prod_pow_eq_pow_sum]
        refine congrArg _ (Finset.prod_congr rfl fun j hj => ?_)
        have : j ∉ J := fun hjJ => Finset.mem_compl.1 (h hjJ) hj
        simp only [this, ↓reduceIte]
      · obtain ⟨j, hjJ, hj⟩ := Finset.not_subset.1 h
        rw [Finset.prod_eq_zero (i := j) (by simpa using hj), mul_zero]
        simp only [hjJ, ↓reduceIte]
        exact zero_pow (by simpa using hj)
    simp only [hJ, smul_ite, smul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_smul,
      Finset.sum_powerset_neg_one_pow_card, coeff_monomial]
    simp only [eq_colorOnes_iff]
    by_cases h : e.support = Finset.univ
    · simp [h, Polynomial.coeff_X_pow, eq_comm]
    · simp [h]
  | add p q hp hq =>
    simp only [map_add, smul_add, Finset.sum_add_distrib, Polynomial.coeff_add, hp, hq]
    rfl

/-- [Shpilka2026, Lemma 3.2]: if the colour part of `G` does not vanish at `b`, then `G` does not
vanish at one of the points obtained from `b` by setting the variables with colour in a set `J`
to zero and scaling the others by an element `t` of `Λ`, a set with more than `G.totalDegree`
elements. -/
theorem exists_eval_ne_zero_of_eval_colorPart_ne_zero [CommRing F] [IsDomain F]
    (c : σ → Fin r) {G : MvPolynomial σ F} {b : σ → F} {Λ : Finset F}
    (hΛ : G.totalDegree < Λ.card) (hb : MvPolynomial.eval b (colorPart c G) ≠ 0) :
    ∃ t ∈ Λ, ∃ J : Finset (Fin r),
      MvPolynomial.eval (fun v => if c v ∈ J then 0 else t * b v) G ≠ 0 := by
  classical
  by_contra! h
  let P (J : Finset (Fin r)) : Polynomial F :=
    aeval (fun v => if c v ∈ J then 0 else Polynomial.C (b v) * Polynomial.X) G
  have hP (J : Finset (Fin r)) : P J = aeval (fun j => if j ∈ J then 0 else Polynomial.X)
      (aeval (fun v => monomial (colorWeight c v) (b v)) G) := by
    rw [← AlgHom.comp_apply, comp_aeval]
    refine congrArg (fun f => aeval f G) (funext fun v => ?_)
    simp [colorWeight, aeval_monomial]
  have heval (J : Finset (Fin r)) (t : F) :
      (P J).eval t = eval (fun v => if c v ∈ J then 0 else t * b v) G := by
    rw [← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval]
    refine congrArg (fun f => eval f G) (funext fun v => ?_)
    by_cases hv : c v ∈ J
    · simp only [hv, ↓reduceIte, map_zero]
    · simp only [hv, ↓reduceIte, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      exact mul_comm _ _
  have hQ : ∑ J : Finset (Fin r), (-1 : ℤ) ^ J.card • P J = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Λ (fun t ht => ?_)
      (lt_of_le_of_lt ?_ hΛ)
    · rw [Polynomial.eval_finsetSum]
      refine Finset.sum_eq_zero fun J _ => ?_
      rw [Polynomial.eval_smul, heval, h t ht J, smul_zero]
    · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun J _ =>
        (Polynomial.natDegree_smul_le _ _).trans ?_
      simpa using aeval_natDegree_le (n := 1) G le_rfl _ fun v => by
        split_ifs
        · simp
        · exact Polynomial.natDegree_C_mul_le _ _ |>.trans Polynomial.natDegree_X_le
  refine hb ?_
  rw [colorPart, ← coeff_aeval_monomial, ← coeff_sum_neg_one_pow_card_smul_aeval]
  simp only [← hP, hQ, Polynomial.coeff_zero]

end Cslib.Circuits.Arithmetic
