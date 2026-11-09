/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.SmallBias
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.FieldTheory.Finite.Subfield
import Mathlib.Algebra.Polynomial.Roots

/-!
# The powering construction of small-bias spaces

Let `F` be a field with `2 ^ m` elements, written as `m`-bit strings by an additive bijection
`bits : F ≃+ BitString m`. The *powering sample space* of Alon, Goldreich, Håstad and Peralta
[Alon, Goldreich, Håstad and Peralta, Section 3][AlonGoldreichHastadPeralta1992] maps a seed
`(x, y) ∈ F × F`, which is `2 m` bits, to the `n` bits `⟨bits (x ^ i), bits y⟩`, `i < n`, where
`⟨u, v⟩ = u ⬝ᵥ v` is the inner product of bit strings modulo two
(`Cslib.BitString.powering`).

The parity of the bits in a set `S` is `⟨bits (p_S x), bits y⟩` for the polynomial
`p_S = ∑_{i ∈ S} X ^ i`. For a fixed `x` with `p_S x ≠ 0` this is an unbiased bit over the
uniform `y`, and with `p_S x = 0` it is constantly zero, so the bias at `S` is the fraction of roots
of `p_S` in `F` (`Cslib.BitString.bias_powering`). A nonempty `S` gives a nonzero `p_S` of degree
less than `n`, so the powering space is `((n - 1) / 2 ^ m)`-biased
(`Cslib.BitString.isSmallBias_powering`).
Fields with `2 ^ m` elements exist for every `m ≠ 0`, so `2 m` uniform bits can be stretched to
`n` bits with bias at most `(n - 1) / 2 ^ m`
(`Cslib.BitString.exists_isSmallBias_uniformOfFintype_map`).

These are statements about distributions; computing the sample space efficiently needs arithmetic
in `F`, which is not certified here.

## Main definitions

* `Cslib.BitString.powering`: the powering sample space.

## Main results

* `Cslib.BitString.bias_powering`: the bias of the powering space at `S` is the fraction of roots
  of `∑_{i ∈ S} X ^ i`.
* `Cslib.BitString.isSmallBias_powering`: the powering space is `((n - 1) / |F|)`-biased.
* `Cslib.BitString.exists_isSmallBias_uniformOfFintype_map`: `2 m` uniform bits stretch to `n` bits
  with bias at most `(n - 1) / 2 ^ m`.

## References

* [N. Alon, O. Goldreich, J. Håstad, R. Peralta, *Simple constructions of almost `k`-wise
  independent random variables*][AlonGoldreichHastadPeralta1992]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Probability
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] {m : ℕ}

/-- The *powering sample space* of Alon, Goldreich, Håstad and Peralta
[Alon, Goldreich, Håstad and Peralta, Section 3][AlonGoldreichHastadPeralta1992]: the seed
`(x, y) ∈ F × F` gives the `n` bits `⟨bits (x ^ i), bits y⟩`, `i < n`, inner products of bit
strings modulo two. -/
def powering (bits : F ≃+ BitString m) (n : ℕ) (s : F × F) : BitString n :=
  fun i => bits (s.1 ^ (i : ℕ)) ⬝ᵥ bits s.2

variable (bits : F ≃+ BitString m) {n : ℕ}

omit [Fintype F] in
/-- The character of `S` at a point of the powering space is the sign of the inner product of
`bits (∑_{i ∈ S} x ^ i)` with `bits y`. -/
private theorem chi_powering (S : Finset (Fin n)) (s : F × F) :
    chi ℝ S (powering bits n s) = signVal (bits (∑ i ∈ S, s.1 ^ (i : ℕ)) ⬝ᵥ bits s.2) := by
  rw [chi_eq_signVal_parityOn, parityOn_eq_sum, map_sum, sum_dotProduct]
  rfl

/-- The inner product of `bits a` with the bits of a uniformly random field element is unbiased
unless `a = 0`. -/
theorem expect_signVal_dotProduct [DecidableEq F] (a : F) :
    𝔼 y, signVal (bits a ⬝ᵥ bits y) = if a = 0 then 1 else 0 := by
  rw [Fintype.expect_equiv bits.toEquiv (fun y => signVal (bits a ⬝ᵥ bits y))
    (fun v => signVal (bits a ⬝ᵥ v)) fun _ => rfl]
  simp only [signVal_dotProduct, expect_chi]
  congr 1
  rw [eq_iff_iff, filter_eq_empty_iff, ← map_eq_zero_iff bits bits.injective, funext_iff]
  simp only [mem_univ, true_implies, Bool.not_eq_true, Pi.zero_apply]
  rfl

/-- The bias of the powering space at `S` is the fraction of the roots of `∑_{i ∈ S} X ^ i` in
`F`. -/
theorem bias_powering [DecidableEq F] (S : Finset (Fin n)) :
    bias ((PMF.uniformOfFintype (F × F)).map (powering bits n)) S =
      dens {x : F | ∑ i ∈ S, x ^ (i : ℕ) = 0} := by
  rw [bias_uniformOfFintype_map, Fintype.expect_prod_type]
  simp only [chi_powering, expect_signVal_dotProduct]
  exact Fintype.expect_boole _

/-- A nonempty sum of distinct powers `x ^ i`, `i < n`, vanishes at fewer than `n` points of a
field. -/
theorem card_filter_sum_pow_eq_zero_le [DecidableEq F] {S : Finset (Fin n)}
    (hS : S.Nonempty) :
    #{x : F | ∑ i ∈ S, x ^ (i : ℕ) = 0} ≤ n - 1 := by
  classical
  set P : Polynomial F := ∑ i ∈ S, Polynomial.X ^ (i : ℕ)
  have hP : P ≠ 0 := by
    obtain ⟨i₀, hi₀⟩ := hS
    intro h
    have hcoeff := congrArg (Polynomial.coeff · (i₀ : ℕ)) h
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, Fin.val_inj,
      Polynomial.coeff_zero] at hcoeff
    rw [sum_ite_eq, ite_eq_left hi₀] at hcoeff
    exact one_ne_zero hcoeff
  have hdeg : P.natDegree ≤ n - 1 :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ =>
      (Polynomial.natDegree_X_pow_le _).trans (by omega)
  refine le_trans (Polynomial.card_le_degree_of_subset_roots fun x hx => ?_) hdeg
  rw [Polynomial.mem_roots hP, Polynomial.IsRoot.def]
  simpa [P, Polynomial.eval_finsetSum] using hx

/-- **The powering space has small bias** [Alon, Goldreich, Håstad and Peralta, Section
3][AlonGoldreichHastadPeralta1992]: it is `((n - 1) / |F|)`-biased. -/
theorem isSmallBias_powering :
    IsSmallBias ((n - 1 : ℕ) / Fintype.card F : ℝ)
      ((PMF.uniformOfFintype (F × F)).map (powering bits n)) := fun S hS => by
  classical
  rw [bias_powering, abs_of_nonneg (by positivity), dens, NNRat.cast_div, NNRat.cast_natCast,
    NNRat.cast_natCast]
  gcongr
  exact_mod_cast card_filter_sum_pow_eq_zero_le (F := F) hS

/-- **Small-bias spaces from the powering construction**: for every `m ≠ 0` there is a map from
`2 m` bits to `n` bits whose image of the uniform distribution is `((n - 1) / 2 ^ m)`-biased. -/
theorem exists_isSmallBias_uniformOfFintype_map (n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    ∃ g : BitString (2 * m) → BitString n,
      IsSmallBias ((n - 1 : ℕ) / 2 ^ m : ℝ) ((PMF.uniformOfFintype _).map g) := by
  obtain ⟨F, _, _, _, hF⟩ := exists_field_card_eq_two_pow hm
  classical
  obtain ⟨bits⟩ := nonempty_addEquiv_bitString hF
  let e : BitString (2 * m) ≃ F × F :=
    ((Equiv.arrowCongr (finCongr (two_mul m)) (Equiv.refl Bool)).trans
      ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
        (Equiv.sumArrowEquivProdArrow _ _ _))).trans
      (Equiv.prodCongr bits.toEquiv.symm bits.toEquiv.symm)
  refine ⟨powering bits n ∘ e, fun S hS => ?_⟩
  have h := isSmallBias_powering bits (n := n) S hS
  rw [bias_uniformOfFintype_map, hF] at h
  push_cast at h
  rwa [bias_uniformOfFintype_map, Fintype.expect_equiv e
    (fun s => chi ℝ S ((powering bits n ∘ e) s)) (fun s => chi ℝ S (powering bits n s))
    fun _ => rfl]

end Cslib.BitString
