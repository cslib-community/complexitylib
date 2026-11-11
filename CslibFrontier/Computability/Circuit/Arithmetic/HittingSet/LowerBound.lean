/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Hitting sets give lower bounds

Over a field, a set `H` of points imposes `H.card` linear conditions on the coefficients of a
polynomial. So for every finite set `T` of monomials with `H.card < T.card` there is a nonzero
polynomial with monomials in `T` that vanishes on `H` (`exists_ne_zero_forall_eval_eq_zero`). If
`H` is a hitting set for a class `𝒞`, this polynomial is not in `𝒞`
(`IsHittingSet.exists_notMem`): a small hitting set for a class certifies that some polynomial
with few monomials lies outside it.

This is the observation of Heintz and Schnorr [HeintzSchnorr1980] that turns hitting sets into
lower bounds, in the form used by Agrawal [Agrawal2005]. The polynomial is obtained by solving a
linear system, which is what makes it explicit in the applications; that complexity statement is
not formalized here.

## Main results

* `exists_ne_zero_forall_eval_eq_zero`: more monomials than points give a nonzero polynomial
  vanishing at the points.
* `IsHittingSet.exists_notMem`: a hitting set smaller than a set of monomials yields a nonzero
  polynomial on those monomials outside the class.

## References

* [J. Heintz, C.-P. Schnorr, *Testing polynomials which are easy to compute*][HeintzSchnorr1980]
* [M. Agrawal, *Proving lower bounds via pseudo-random generators*][Agrawal2005]
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable {F σ : Type*} [Field F]

/-- For a set `T` of monomials larger than a set `H` of points, some nonzero polynomial with
monomials in `T` vanishes on `H`. -/
theorem exists_ne_zero_forall_eval_eq_zero (H : Finset (σ → F)) (T : Finset (σ →₀ ℕ))
    (h : H.card < T.card) :
    ∃ f : MvPolynomial σ F, f ≠ 0 ∧ f.support ⊆ T ∧ ∀ a ∈ H, eval a f = 0 := by
  classical
  -- the polynomial with given coefficients on `T`, and its values on `H`
  let ι : (T → F) →ₗ[F] MvPolynomial σ F :=
    Fintype.linearCombination F fun m : T => monomial (m : σ →₀ ℕ) (1 : F)
  let E : MvPolynomial σ F →ₗ[F] (H → F) :=
    LinearMap.pi fun a => (aeval (a : σ → F) : MvPolynomial σ F →ₐ[F] F).toLinearMap
  have hι (c : T → F) : ι c = ∑ m : T, monomial (m : σ →₀ ℕ) (c m) := by
    simp only [ι, Fintype.linearCombination_apply, smul_monomial, smul_eq_mul, mul_one]
  have hcoeff (c : T → F) (m : T) : (ι c).coeff (m : σ →₀ ℕ) = c m := by
    rw [hι, coeff_sum, Fintype.sum_eq_single m]
    · simp
    · intro m' hm'
      rw [coeff_monomial, ite_eq_right fun h => hm' (Subtype.ext h)]
  have hker : LinearMap.ker (E ∘ₗ ι) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by
      rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
        Fintype.card_coe, Fintype.card_coe])
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).1 hker
  refine ⟨ι c, fun h0 => hc0 (funext fun m => ?_), fun d hd => ?_, fun a ha => ?_⟩
  · rw [← hcoeff c m, h0]; simp
  · by_contra hdT
    refine mem_support_iff.1 hd ?_
    rw [hι, coeff_sum]
    exact sum_eq_zero fun m _ => by
      rw [coeff_monomial, ite_eq_right fun h : (m : σ →₀ ℕ) = d => hdT (h ▸ m.2)]
  · have := congrFun (LinearMap.mem_ker.1 hc) ⟨a, ha⟩
    simpa [E, aeval_eq_eval] using this

/-- **Hitting sets give lower bounds.** If `H` is a hitting set for the class `𝒞` and `T` is a
set of monomials larger than `H`, some nonzero polynomial with monomials in `T` is not in `𝒞`. -/
theorem IsHittingSet.exists_notMem {H : Finset (σ → F)} {𝒞 : Set (MvPolynomial σ F)}
    (hH : IsHittingSet H 𝒞) (T : Finset (σ →₀ ℕ)) (h : H.card < T.card) :
    ∃ f : MvPolynomial σ F, f ≠ 0 ∧ f.support ⊆ T ∧ f ∉ 𝒞 := by
  obtain ⟨f, hf0, hfT, hzero⟩ := exists_ne_zero_forall_eval_eq_zero H T h
  refine ⟨f, hf0, hfT, fun hmem => ?_⟩
  obtain ⟨a, ha, hne⟩ := hH f hmem hf0
  exact hne (hzero a ha)

end Cslib.Circuits.Arithmetic
