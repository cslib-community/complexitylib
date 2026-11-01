/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.SparseEquations

/-!
# Cube degrees of sparse equations and their parity factors

An equation `P` with monomials of at most `k` variables has a lift `monomialSum R P` of degree at
most `k` on the cube (`Cslib.BitString.lowDegree`). The `V ^ j` coefficient of its parity factor
`Polynomial.parityFactor ℓ (monomialSum ℤ P x)` is `e_j(y) h(y) ^ j` at `y = monomialSum ℤ P x`,
with `deg e_j ≤ 1` and `h(Y) = Y (Y - 1)`, so it has degree at most `k (1 + 2 j)`. This is the
per-factor degree bound in the proof of Lemma D.2 of [OpenAI2026ETH] (p. 55).

## Main results

* `Cslib.BitString.monomialSum_mem_lowDegree`: the lift of an equation with monomials of at most
  `k` variables has degree at most `k`.
* `Cslib.BitString.coeff_parityFactor_mem_lowDegree`: the `V ^ j` coefficient of its parity factor
  has degree at most `k (1 + 2 j)`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma 5.1 (p. 36) and the
  proof of Lemma D.2 (p. 55).
-/

public section

namespace Cslib.BitString

open Finset Polynomial

variable {ι R : Type*} [CommRing R]

/-- **The lift of an equation is low-degree**: if every monomial of `P` has at most `k` variables,
then `monomialSum R P` has degree at most `k` on the cube. -/
theorem monomialSum_mem_lowDegree {P : Finset (Finset ι)} {k : ℕ} (hk : ∀ M ∈ P, #M ≤ k) :
    monomialSum R P ∈ lowDegree R ι k := by
  have h : monomialSum R P = ∑ M ∈ P, monomial R M := by
    funext x
    simp only [monomialSum, Finset.sum_apply]
  rw [h]
  exact sum_mem_lowDegree P fun M hM => monomial_mem_lowDegree (hk M hM)

/-- **The parity-factor coefficients of an equation are low-degree**: if every monomial of `P` has
at most `k` variables, then the `V ^ j` coefficient of the parity factor of its integer lift has
degree at most `k (1 + 2 j)` on the cube. -/
theorem coeff_parityFactor_mem_lowDegree (ℓ : ℕ) {P : Finset (Finset ι)} {k : ℕ}
    (hk : ∀ M ∈ P, #M ≤ k) (j : ℕ) :
    (fun x => (parityFactor ℓ (monomialSum ℤ P x)).coeff j) ∈ lowDegree ℤ ι (k * (1 + 2 * j)) := by
  set y : (ι → Bool) → ℤ := monomialSum ℤ P
  have hy : y ∈ lowDegree ℤ ι k := monomialSum_mem_lowDegree hk
  by_cases hj : j < ℓ
  · have he : (fun x => evalInt (y x) (parityBaseDigit ℓ j)) ∈ lowDegree ℤ ι k := by
      have hfun : (fun x => evalInt (y x) (parityBaseDigit ℓ j)) =
          (fun _ => (parityBaseDigit ℓ j).coeff 0) + (parityBaseDigit ℓ j).coeff 1 • y := by
        funext x
        have h := congrArg (eval (y x)) (parityBaseDigit_eq_C_add_C_mul_X ℓ j)
        simp only [eval_add, eval_mul, eval_C, eval_X] at h
        rw [evalInt_int, h]
        rfl
      rw [hfun]
      exact Submodule.add_mem _ (const_mem_lowDegree k _) (Submodule.smul_mem _ _ hy)
    have hh : (fun x => evalInt (y x) hPoly) ∈ lowDegree ℤ ι (2 * k) := by
      have hfun : (fun x => evalInt (y x) hPoly) = y ^ 2 - y := by
        funext x
        simp only [evalInt_hPoly, Pi.sub_apply, Pi.pow_apply]
      rw [hfun]
      exact Submodule.sub_mem _ (pow_mem_lowDegree hy 2) (lowDegree_mono (by omega) hy)
    have hfun : (fun x => (parityFactor ℓ (y x)).coeff j) =
        (fun x => evalInt (y x) (parityBaseDigit ℓ j)) * (fun x => evalInt (y x) hPoly) ^ j := by
      funext x
      simp only [coeff_parityFactor, hj, ↓reduceIte, Pi.mul_apply, Pi.pow_apply]
    rw [hfun]
    refine lowDegree_mono (le_of_eq ?_) (mul_mem_lowDegree he (pow_mem_lowDegree hh j))
    ring
  · have hfun : (fun x => (parityFactor ℓ (y x)).coeff j) = 0 := by
      funext x
      simp only [coeff_parityFactor, hj, ↓reduceIte, Pi.zero_apply]
    rw [hfun]
    exact Submodule.zero_mem _

end Cslib.BitString
