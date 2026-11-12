/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Analysis/Polynomial/MahlerMeasure.lean`)
-- Hadamard's determinant inequality fits `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`.

public import CslibFrontier.Init
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

import CslibFrontier.Foundations.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# Root Magnitude and Separation Bounds

This module proves Hadamard's determinant inequality over `ℂ`, connects Cauchy's root magnitude
bound to explicit rational coefficient bounds on `ℚ[X]`, relates polynomial discriminants to
squared Vandermonde determinants, and establishes Mignotte-type root-separation lower bounds for
squarefree integer and rational polynomials.

## Main definitions

* `Polynomial.coeffSqNorm`: the sum of squares of the integer coefficients of `p : ℤ[X]`.

## Main results

* `Matrix.hadamard_det_sq_le`: Hadamard's inequality `‖A.det‖ ^ 2 ≤ ∏ i, ∑ j, ‖A i j‖ ^ 2` for a
  complex square matrix `A`.
* `Polynomial.norm_lt_cauchyBound_of_forall_coeff_le` and
  `Polynomial.abs_lt_cauchyBound_of_forall_coeff_le`: rational Cauchy root-magnitude bounds for
  complex and real roots of `p : ℚ[X]`.
* `Polynomial.discr_eq_leadingCoeff_pow_mul_det_vandermonde_sq`: discriminant expressed via the
  leading coefficient and squared Vandermonde determinant over any field where `p` splits.
* `Polynomial.mignotte_sep_mahler_complex`, `Polynomial.mignotte_sep_sqNorm_complex`,
  `Polynomial.mignotte_sep_sqNorm_real`, and `Polynomial.mignotte_sep_sqNorm_rat`: Mignotte-type
  root-separation lower bounds via Mahler's measure and Landau's coefficient `ℓ²` inequality.

## References

* [Mahler1964], pp. 257–262 (Hadamard's determinant inequality and root-separation lower bound via
  discriminant and Mahler's measure; internal lemma/theorem numbers unverified).
* [Mignotte1982], pp. 259–263 (coefficient `ℓ²` root-separation specialization via Landau's
  inequality; internal theorem number unverified).
* [BasuPollackRoy2006] (locator unverified; `Polynomial.mignotte_sep_sqNorm_rat` packages the
  cleared-denominator rational `ℓ²` form for this library).
-/

public section

open scoped Matrix

namespace Matrix

/-- Hadamard's determinant inequality for a complex square matrix `A`: the squared modulus of
`A.det` is bounded by the product of the squared Euclidean norms of the rows of `A`. -/
theorem hadamard_det_sq_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ ^ 2 ≤ ∏ i : Fin n, ∑ j : Fin n, ‖A i j‖ ^ 2 := by
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (A i)
  have hgram : Matrix.gram ℂ v = (A * Aᴴ)ᵀ := by
    ext i j
    simp only [Matrix.gram_apply, PiLp.inner_apply, RCLike.inner_apply, Matrix.transpose_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply]
    rfl
  have hdet_eq : (Matrix.gram ℂ v).det = ((‖A.det‖ ^ 2 : ℝ) : ℂ) := by
    rw [hgram, Matrix.det_transpose, Matrix.det_mul, Matrix.det_conjTranspose]
    change A.det * (starRingEnd ℂ) A.det = _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hgs := InnerProductSpace.det_gram_eq_prod_norm_gramSchmidt_sq (𝕜 := ℂ) v
  rw [hdet_eq] at hgs
  have hreal : ‖A.det‖ ^ 2 = ∏ i : Fin n, ‖InnerProductSpace.gramSchmidt ℂ v i‖ ^ 2 := by
    norm_cast at hgs
    exact Complex.ofReal_inj.mp hgs
  rw [hreal]
  refine Finset.prod_le_prod₀ (fun i _ => sq_nonneg _) fun i _ => ?_
  have hle := InnerProductSpace.norm_gramSchmidt_le ℂ v i
  have hsq : ‖InnerProductSpace.gramSchmidt ℂ v i‖ ^ 2 ≤ ‖v i‖ ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (InnerProductSpace.gramSchmidt ℂ v i), norm_nonneg (v i)])
      hle
  rw [EuclideanSpace.norm_sq_eq (v i)] at hsq
  exact hsq

end Matrix

namespace Polynomial

/-- Sum of squares of the integer coefficients of `p : ℤ[X]`. -/
@[expose] noncomputable def coeffSqNorm (p : ℤ[X]) : ℕ :=
  ∑ i ∈ p.support, (p.coeff i).natAbs ^ 2

/-- `coeffSqNorm p` expressed as a sum over `Finset.range (p.natDegree + 1)`. -/
theorem coeffSqNorm_eq_sum_range (p : ℤ[X]) :
    coeffSqNorm p = ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i).natAbs ^ 2 := by
  rw [coeffSqNorm]
  refine Finset.sum_subset (fun i hi => Finset.mem_range.mpr (Nat.lt_succ_of_le
    (le_natDegree_of_mem_supp i hi))) ?_
  intro i _ hi
  simp only [mem_support_iff, not_not] at hi
  simp only [hi, Int.natAbs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

/-- Real cast of `coeffSqNorm p`. -/
theorem coeffSqNorm_cast_real (p : ℤ[X]) :
    (coeffSqNorm p : ℝ) = ∑ i ∈ p.support, ((p.coeff i : ℝ)) ^ 2 := by
  rw [coeffSqNorm, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]

/-- If every lower coefficient of `p : ℚ[X]` satisfies `|p.coeff i| ≤ M` (`0 ≤ M`), then every
complex root `z` of `p` satisfies `‖z‖ < M / |p.leadingCoeff| + 1`. -/
theorem norm_lt_cauchyBound_of_forall_coeff_le {p : ℚ[X]} (hp : p ≠ 0) {M : ℚ} (hM0 : 0 ≤ M)
    (hM : ∀ i < p.natDegree, |p.coeff i| ≤ M) {z : ℂ}
    (hz : (p.map (algebraMap ℚ ℂ)).IsRoot z) :
    ‖z‖ < ((M / |p.leadingCoeff| + 1 : ℚ) : ℝ) := by
  let pC : ℂ[X] := p.map (algebraMap ℚ ℂ)
  have hpC : pC ≠ 0 := Polynomial.map_ne_zero_iff (algebraMap ℚ ℂ).injective |>.mpr hp
  have hcb := hz.norm_lt_cauchyBound hpC
  have hlt : ‖z‖ < (pC.cauchyBound : ℝ) := hcb
  refine lt_of_lt_of_le hlt ?_
  have hdeg : pC.natDegree = p.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℂ).injective p
  have hlead : ‖pC.leadingCoeff‖ = |((p.leadingCoeff : ℚ) : ℝ)| := by
    rw [Polynomial.leadingCoeff_map_of_injective (algebraMap ℚ ℂ).injective p,
      eq_ratCast, Complex.norm_ratCast]
  have hlead_pos : 0 < ‖pC.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hpC)
  let s : NNReal := (Finset.range pC.natDegree).sup (fun i => ‖pC.coeff i‖₊)
  let Mnn : NNReal := ⟨(M : ℝ), by exact_mod_cast hM0⟩
  have hs_le : s ≤ Mnn := by
    refine Finset.sup_le fun i hi => ?_
    have hi' : i < p.natDegree := by
      rw [← hdeg]
      exact Finset.mem_range.mp hi
    change ‖pC.coeff i‖ ≤ (M : ℝ)
    rw [Polynomial.coeff_map, eq_ratCast, Complex.norm_ratCast]
    exact_mod_cast hM i hi'
  have hsup : (s : ℝ) ≤ (M : ℝ) := hs_le
  have hcb_eq : (pC.cauchyBound : ℝ) = (s : ℝ) / ‖pC.leadingCoeff‖ + 1 := by
    rw [Polynomial.cauchyBound, NNReal.coe_add, NNReal.coe_div, NNReal.coe_one, coe_nnnorm]
  rw [hcb_eq, Rat.cast_add, Rat.cast_div, Rat.cast_abs, Rat.cast_one, ← hlead]
  gcongr

/-- Real-root specialization of `norm_lt_cauchyBound_of_forall_coeff_le`. -/
theorem abs_lt_cauchyBound_of_forall_coeff_le {p : ℚ[X]} (hp : p ≠ 0) {M : ℚ} (hM0 : 0 ≤ M)
    (hM : ∀ i < p.natDegree, |p.coeff i| ≤ M) {r : ℝ}
    (hr : (p.map (algebraMap ℚ ℝ)).IsRoot r) :
    |r| < ((M / |p.leadingCoeff| + 1 : ℚ) : ℝ) := by
  have hz : (p.map (algebraMap ℚ ℂ)).IsRoot (r : ℂ) := by
    have hmap : p.map (algebraMap ℚ ℂ) = (p.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ) := by
      rw [Polynomial.map_map, Subsingleton.elim ((algebraMap ℝ ℂ).comp (algebraMap ℚ ℝ))
        (algebraMap ℚ ℂ)]
    rw [hmap]
    exact hr.map (algebraMap ℝ ℂ)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    norm_lt_cauchyBound_of_forall_coeff_le hp hM0 hM hz

/-- Under an injective leading-coefficient homomorphism into a domain, polynomial discriminant
commutes with `Polynomial.map`. -/
theorem discr_map_of_leadingCoeff_ne_zero {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    (φ : R →+* S) {f : R[X]} (hf : 0 < f.degree) (hφ : φ f.leadingCoeff ≠ 0) :
    (f.map φ).discr = φ f.discr := by
  have hf_nat : 0 < f.natDegree := natDegree_pos_iff_degree_pos.mpr hf
  have hdeg_map : (f.map φ).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_iff.mpr (Or.inl hφ)
  have hdeg_pos : 0 < (f.map φ).degree := by
    rw [← natDegree_pos_iff_degree_pos, hdeg_map]
    exact hf_nat
  have hres := Polynomial.resultant_map_map f f.derivative f.natDegree (f.natDegree - 1) φ
  rw [Polynomial.resultant_deriv hf, ← Polynomial.derivative_map,
    ← hdeg_map, Polynomial.resultant_deriv hdeg_pos, hdeg_map] at hres
  have hlead_map : (f.map φ).leadingCoeff = φ f.leadingCoeff := by
    rw [leadingCoeff, hdeg_map, coeff_map, leadingCoeff]
  rw [map_mul, map_mul, map_pow, map_neg, map_one, hlead_map] at hres
  have hunit : (-1 : S) ^ (f.natDegree * (f.natDegree - 1) / 2) * φ f.leadingCoeff ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hφ
  exact mul_left_cancel₀ hunit hres

/-- Combinatorial identity for the Vandermonde difference product over all ordered pairs `i ≠ j` of
`Fin d`: it equals `(-1) ^ (d * (d - 1) / 2) * (Matrix.vandermonde r).det ^ 2`. -/
private theorem prod_sub_erase_eq_vandermonde_sq {K : Type*} [CommRing K] (d : ℕ)
    (r : Fin d → K) :
    (∏ i : Fin d, ∏ j ∈ Finset.univ.erase i, (r i - r j)) =
      (-1 : K) ^ (d * (d - 1) / 2) * (Matrix.vandermonde r).det ^ 2 := by
  let U : Finset ((_ : Fin d) × Fin d) := Finset.univ.sigma fun i => Finset.Ioi i
  let swapSig : ((_ : Fin d) × Fin d) → ((_ : Fin d) × Fin d) := fun ⟨i, j⟩ => ⟨j, i⟩
  have hU_card : U.card = d * (d - 1) / 2 := by
    rw [Finset.card_sigma]
    have hsum : (∑ i : Fin d, (Finset.Ioi i).card) = ∑ k ∈ Finset.range d, (d - 1 - k) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.card_Ioi]
    rw [hsum, Finset.sum_range_reflect (fun k => k) d, Finset.sum_range_id]
  have hdet : (Matrix.vandermonde r).det = ∏ x ∈ U, (r x.2 - r x.1) := by
    rw [Matrix.det_vandermonde, Finset.prod_sigma']
  have hS : (Finset.univ.sigma fun i : Fin d => Finset.univ.erase i) =
      U ∪ U.image swapSig := by
    ext ⟨i, j⟩
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_erase, ne_eq, true_and, and_true,
      Finset.mem_union, Finset.mem_Ioi, Finset.mem_image, Sigma.exists, swapSig, Sigma.mk.injEq,
      U]
    constructor
    · intro hij
      rcases lt_or_gt_of_ne (Ne.symm hij) with hlt | hgt
      · exact Or.inl hlt
      · exact Or.inr ⟨j, i, hgt, rfl, heq_of_eq rfl⟩
    · rintro (hlt | ⟨a, b, hab, h1, h2⟩)
      · exact hlt.ne'
      · cases h1
        cases eq_of_heq h2
        exact hab.ne
  have hdisj : Disjoint U (U.image swapSig) := by
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hij him
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and, U] at hij
    simp only [Finset.mem_image, Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi,
      Sigma.exists, true_and, swapSig, Sigma.mk.injEq, U] at him
    obtain ⟨a, b, hab, h1, h2⟩ := him
    cases h1
    cases eq_of_heq h2
    exact lt_asymm hij hab
  have hswap_inj : Set.InjOn swapSig ↑U := by
    rintro ⟨a, b⟩ _ ⟨c, e⟩ _ h
    cases h
    rfl
  have hprod_lhs : (∏ i : Fin d, ∏ j ∈ Finset.univ.erase i, (r i - r j)) =
      ∏ x ∈ Finset.univ.sigma (fun i : Fin d => Finset.univ.erase i), (r x.1 - r x.2) :=
    Finset.prod_sigma' Finset.univ (fun i : Fin d => Finset.univ.erase i)
      (fun i j => r i - r j)
  rw [hprod_lhs, hS, Finset.prod_union hdisj, Finset.prod_image hswap_inj]
  have hU_neg : (∏ x ∈ U, (r x.1 - r x.2)) = (-1 : K) ^ U.card * ∏ x ∈ U, (r x.2 - r x.1) := by
    calc (∏ x ∈ U, (r x.1 - r x.2))
        = ∏ x ∈ U, ((-1 : K) * (r x.2 - r x.1)) := by
            refine Finset.prod_congr rfl fun x _ => ?_
            ring
      _ = (∏ _x ∈ U, (-1 : K)) * ∏ x ∈ U, (r x.2 - r x.1) := Finset.prod_mul_distrib
      _ = (-1 : K) ^ U.card * ∏ x ∈ U, (r x.2 - r x.1) := by rw [Finset.prod_const]
  have hU_swap : (∏ x ∈ U, (r (swapSig x).1 - r (swapSig x).2)) = ∏ x ∈ U, (r x.2 - r x.1) :=
    rfl
  rw [hU_neg, hU_swap, hU_card, hdet]
  ring

/-- Discriminant of a splitting polynomial `p : K[X]` of positive degree `d = p.natDegree` in terms
of its leading coefficient and the Vandermonde determinant of its roots `r : Fin d → K`. -/
theorem discr_eq_leadingCoeff_pow_mul_det_vandermonde_sq {K : Type*} [Field K]
    {p : K[X]} (hp : p.Splits) (hd : 0 < p.natDegree) (r : Fin p.natDegree → K)
    (hr : (Finset.univ.val.map r) = p.roots) :
    p.discr = p.leadingCoeff ^ (2 * p.natDegree - 2) * (Matrix.vandermonde r).det ^ 2 := by
  have hp0 : p ≠ 0 := fun h0 => by simp only [h0, natDegree_zero, lt_self_iff_false] at hd
  have hlead0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have hdeg_pos : 0 < p.degree := natDegree_pos_iff_degree_pos.mp hd
  have hderiv_deg : p.derivative.natDegree ≤ p.natDegree - 1 := natDegree_derivative_le p
  have hres_deriv := Polynomial.resultant_deriv hdeg_pos
  have hres_eval := Polynomial.resultant_eq_prod_eval p p.derivative (p.natDegree - 1) hderiv_deg hp
  rw [hres_eval] at hres_deriv
  have hp_prod : p = C p.leadingCoeff * ∏ j : Fin p.natDegree, (X - C (r j)) := by
    have heq := hp.eq_prod_roots
    rw [← hr, Multiset.map_map] at heq
    simpa only [Function.comp_def, Finset.prod_eq_multiset_prod] using heq
  have hderiv_eval : ∀ i : Fin p.natDegree,
      p.derivative.eval (r i) = p.leadingCoeff * ∏ j ∈ Finset.univ.erase i, (r i - r j) := by
    intro i
    conv_lhs => rw [hp_prod, derivative_C_mul, derivative_prod_finset]
    rw [eval_mul, eval_C]
    change p.leadingCoeff * evalRingHom (r i) _ = _
    rw [map_sum]
    congr 1
    have hsum : (∑ a : Fin p.natDegree, evalRingHom (r i)
          ((∏ b ∈ Finset.univ.erase a, (X - C (r b))) * derivative (X - C (r a)))) =
        ∑ a ∈ ({i} : Finset (Fin p.natDegree)), evalRingHom (r i)
          ((∏ b ∈ Finset.univ.erase a, (X - C (r b))) * derivative (X - C (r a))) := by
      refine (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_).symm
      have hai : i ≠ a := Ne.symm (by simpa only [Finset.mem_singleton] using ha)
      have hi_mem : i ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hai, Finset.mem_univ i⟩
      rw [map_mul, map_prod, Finset.prod_eq_zero hi_mem (by simp only [coe_evalRingHom,
        eval_sub, eval_X, eval_C, sub_self]), zero_mul]
    rw [hsum, Finset.sum_singleton, map_mul, derivative_X_sub_C, map_one, mul_one, map_prod]
    refine Finset.prod_congr rfl fun b _ => by
      simp only [coe_evalRingHom, eval_sub, eval_X, eval_C]
  have hroots_prod : (p.roots.map p.derivative.eval).prod =
      p.leadingCoeff ^ p.natDegree *
        ((-1 : K) ^ (p.natDegree * (p.natDegree - 1) / 2) * (Matrix.vandermonde r).det ^ 2) := by
    rw [← hr, Multiset.map_map]
    simp only [Function.comp_def]
    change (∏ i : Fin p.natDegree, p.derivative.eval (r i)) = _
    simp_rw [hderiv_eval]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      prod_sub_erase_eq_vandermonde_sq]
  rw [hroots_prod] at hres_deriv
  have hpow : p.natDegree - 1 + p.natDegree = 1 + (2 * p.natDegree - 2) := by omega
  have hcomb : p.leadingCoeff ^ (p.natDegree - 1) *
      (p.leadingCoeff ^ p.natDegree *
        ((-1 : K) ^ (p.natDegree * (p.natDegree - 1) / 2) * (Matrix.vandermonde r).det ^ 2)) =
      ((-1 : K) ^ (p.natDegree * (p.natDegree - 1) / 2) * p.leadingCoeff) *
        (p.leadingCoeff ^ (2 * p.natDegree - 2) * (Matrix.vandermonde r).det ^ 2) := by
    calc p.leadingCoeff ^ (p.natDegree - 1) *
          (p.leadingCoeff ^ p.natDegree *
            ((-1 : K) ^ (p.natDegree * (p.natDegree - 1) / 2) * (Matrix.vandermonde r).det ^ 2))
      _ = (p.leadingCoeff ^ (p.natDegree - 1) * p.leadingCoeff ^ p.natDegree) *
            ((-1 : K) ^ (p.natDegree * (p.natDegree - 1) / 2) *
              (Matrix.vandermonde r).det ^ 2) := by
            ring
      _ = (p.leadingCoeff ^ (1 + (2 * p.natDegree - 2))) *
            ((-1 : K) ^ (p.natDegree * (p.natDegree - 1) / 2) *
              (Matrix.vandermonde r).det ^ 2) := by
            rw [← pow_add, hpow]
      _ = ((-1 : K) ^ (p.natDegree * (p.natDegree - 1) / 2) * p.leadingCoeff) *
            (p.leadingCoeff ^ (2 * p.natDegree - 2) * (Matrix.vandermonde r).det ^ 2) := by
            rw [pow_add, pow_one]; ring
  rw [hcomb] at hres_deriv
  have hunit : (-1 : K) ^ (p.natDegree * (p.natDegree - 1) / 2) * p.leadingCoeff ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hlead0
  exact (mul_left_cancel₀ hunit hres_deriv).symm

/-- Elementary sum-of-squares bound `6 * ∑ k ∈ range d, k ^ 2 ≤ 2 * d ^ 3`. -/
private theorem six_mul_sum_range_sq_le (d : ℕ) :
    6 * ∑ k ∈ Finset.range d, k ^ 2 ≤ 2 * d ^ 3 := by
  induction d with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, le_refl]
  | succ d ih =>
    rw [Finset.sum_range_succ, mul_add]
    have hpow3 : 2 * d ^ 3 + 6 * d ^ 2 ≤ 2 * (d + 1) ^ 3 := by
      have hring : 2 * (d + 1) ^ 3 = 2 * d ^ 3 + 6 * d ^ 2 + 6 * d + 2 := by ring
      omega
    omega

/-- Difference of powers norm bound when `‖y‖ ≤ ‖x‖` and `k < d` (`2 ≤ d`). -/
private theorem norm_pow_sub_pow_le {x y : ℂ} (hxy : ‖y‖ ≤ ‖x‖) {k d : ℕ} (hkd : k < d)
    (hd : 2 ≤ d) :
    ‖x ^ k - y ^ k‖ ≤ ‖x - y‖ * (k : ℝ) * (max 1 ‖x‖) ^ (d - 2) := by
  rw [← geom_sum₂_mul x y k, norm_mul, mul_comm ‖_‖ ‖x - y‖, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hM : ∀ m ∈ Finset.range k, ‖x ^ m * y ^ (k - 1 - m)‖ ≤ (max 1 ‖x‖) ^ (d - 2) := by
    intro m hm
    have hmk : m < k := Finset.mem_range.mp hm
    have hm1 : 1 ≤ k := Nat.one_le_of_lt hmk
    have hexp : m + (k - 1 - m) = k - 1 := by omega
    have h1M : 1 ≤ max 1 ‖x‖ := le_max_left 1 ‖x‖
    have hxM : ‖x‖ ≤ max 1 ‖x‖ := le_max_right 1 ‖x‖
    have hyM : ‖y‖ ≤ max 1 ‖x‖ := le_trans hxy hxM
    calc ‖x ^ m * y ^ (k - 1 - m)‖
        = ‖x‖ ^ m * ‖y‖ ^ (k - 1 - m) := by rw [norm_mul, norm_pow, norm_pow]
      _ ≤ (max 1 ‖x‖) ^ m * (max 1 ‖x‖) ^ (k - 1 - m) := by gcongr
      _ = (max 1 ‖x‖) ^ (k - 1) := by rw [← pow_add, hexp]
      _ ≤ (max 1 ‖x‖) ^ (d - 2) := pow_le_pow_right₀ h1M (by omega)
  calc ‖∑ m ∈ Finset.range k, x ^ m * y ^ (k - 1 - m)‖
      ≤ ∑ m ∈ Finset.range k, ‖x ^ m * y ^ (k - 1 - m)‖ := norm_sum_le _ _
    _ ≤ (Finset.range k).card • (max 1 ‖x‖) ^ (d - 2) := Finset.sum_le_card_nsmul _ _ _ hM
    _ = (k : ℝ) * (max 1 ‖x‖) ^ (d - 2) := by rw [Finset.card_range, nsmul_eq_mul]

/-- Bound on `‖(Matrix.vandermonde r).det‖ ^ 2` isolating a pair `r i₀`, `r j₀` of roots. -/
private theorem norm_det_vandermonde_sq_le {d : ℕ} (hd : 2 ≤ d) (r : Fin d → ℂ)
    {i₀ j₀ : Fin d} (hne : i₀ ≠ j₀) :
    ‖(Matrix.vandermonde r).det‖ ^ 2 ≤
      ‖r i₀ - r j₀‖ ^ 2 * ((d : ℝ) ^ (d + 2) / 3) *
        (∏ i : Fin d, max 1 ‖r i‖) ^ (2 * (d - 1)) := by
  wlog hnorm : ‖r i₀‖ ≤ ‖r j₀‖ generalizing i₀ j₀
  · have hswap := this hne.symm (le_of_not_ge hnorm)
    rwa [norm_sub_rev] at hswap
  let V : Matrix (Fin d) (Fin d) ℂ := Matrix.vandermonde r
  let W : Matrix (Fin d) (Fin d) ℂ := V.updateRow j₀ (V j₀ + (-1 : ℂ) • V i₀)
  have hdetW : W.det = V.det := Matrix.det_updateRow_add_smul_self V hne.symm (-1 : ℂ)
  have hhad := Matrix.hadamard_det_sq_le W
  rw [hdetW] at hhad
  have hrow_other : ∀ i : Fin d, i ≠ j₀ →
      ∑ k : Fin d, ‖W i k‖ ^ 2 ≤ (d : ℝ) * (max 1 ‖r i‖) ^ (2 * (d - 1)) := by
    intro i hij
    have hentry : ∀ k : Fin d, ‖W i k‖ ^ 2 ≤ (max 1 ‖r i‖) ^ (2 * (d - 1)) := by
      intro k
      have hWi : W i k = r i ^ (k : ℕ) := by
        simp only [W, Matrix.updateRow_ne hij, V, Matrix.vandermonde_apply]
      have h1M : 1 ≤ max 1 ‖r i‖ := le_max_left 1 ‖r i‖
      have hrM : ‖r i‖ ≤ max 1 ‖r i‖ := le_max_right 1 ‖r i‖
      rw [hWi, norm_pow]
      calc (‖r i‖ ^ (k : ℕ)) ^ 2
          ≤ ((max 1 ‖r i‖) ^ (k : ℕ)) ^ 2 := by gcongr
        _ = (max 1 ‖r i‖) ^ ((k : ℕ) * 2) := by rw [← pow_mul]
        _ = (max 1 ‖r i‖) ^ (2 * (k : ℕ)) := by rw [mul_comm]
        _ ≤ (max 1 ‖r i‖) ^ (2 * (d - 1)) := by
            refine pow_le_pow_right₀ h1M ?_
            have hk : (k : ℕ) < d := k.2
            omega
    calc ∑ k : Fin d, ‖W i k‖ ^ 2
        ≤ ∑ _k : Fin d, (max 1 ‖r i‖) ^ (2 * (d - 1)) := Finset.sum_le_sum fun k _ => hentry k
      _ = (d : ℝ) * (max 1 ‖r i‖) ^ (2 * (d - 1)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hrow_j0 :
      ∑ k : Fin d, ‖W j₀ k‖ ^ 2 ≤
        ‖r i₀ - r j₀‖ ^ 2 * ((d : ℝ) ^ 3 / 3) * (max 1 ‖r j₀‖) ^ (2 * (d - 1)) := by
    have hentry : ∀ k : Fin d,
        ‖W j₀ k‖ ^ 2 ≤
          ‖r i₀ - r j₀‖ ^ 2 * (k : ℝ) ^ 2 * (max 1 ‖r j₀‖) ^ (2 * (d - 2)) := by
      intro k
      have hWj : W j₀ k = r j₀ ^ (k : ℕ) - r i₀ ^ (k : ℕ) := by
        simp only [W, Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul,
          one_mul, ← sub_eq_add_neg, V, Matrix.vandermonde_apply]
      rw [hWj]
      have hdiff := norm_pow_sub_pow_le hnorm k.2 hd
      rw [norm_sub_rev (r j₀) (r i₀)] at hdiff
      have hsq : ‖r j₀ ^ (k : ℕ) - r i₀ ^ (k : ℕ)‖ ^ 2 ≤
          (‖r i₀ - r j₀‖ * (k : ℝ) * (max 1 ‖r j₀‖) ^ (d - 2)) ^ 2 := by
        refine sq_le_sq' ?_ hdiff
        have hpos : 0 ≤ ‖r i₀ - r j₀‖ * (k : ℝ) * (max 1 ‖r j₀‖) ^ (d - 2) :=
          mul_nonneg (mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
            (pow_nonneg (le_trans zero_le_one (le_max_left 1 _)) _)
        linarith [norm_nonneg (r j₀ ^ (k : ℕ) - r i₀ ^ (k : ℕ))]
      refine hsq.trans_eq ?_
      rw [mul_pow, mul_pow, ← pow_mul, mul_comm (d - 2) 2]
    have hsum_sq : (∑ k : Fin d, (k : ℝ) ^ 2) ≤ (d : ℝ) ^ 3 / 3 := by
      have h6 := six_mul_sum_range_sq_le d
      have h6R : (6 : ℝ) * ∑ k ∈ Finset.range d, (k : ℝ) ^ 2 ≤ 2 * (d : ℝ) ^ 3 := by
        exact_mod_cast h6
      rw [← Fin.sum_univ_eq_sum_range] at h6R
      linarith
    have hpowM : (max 1 ‖r j₀‖) ^ (2 * (d - 2)) ≤ (max 1 ‖r j₀‖) ^ (2 * (d - 1)) :=
      pow_le_pow_right₀ (le_max_left 1 _) (by omega)
    calc ∑ k : Fin d, ‖W j₀ k‖ ^ 2
        ≤ ∑ k : Fin d, ‖r i₀ - r j₀‖ ^ 2 * (k : ℝ) ^ 2 * (max 1 ‖r j₀‖) ^ (2 * (d - 2)) :=
          Finset.sum_le_sum fun k _ => hentry k
      _ = ‖r i₀ - r j₀‖ ^ 2 * (∑ k : Fin d, (k : ℝ) ^ 2) * (max 1 ‖r j₀‖) ^ (2 * (d - 2)) := by
          simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ ‖r i₀ - r j₀‖ ^ 2 * ((d : ℝ) ^ 3 / 3) * (max 1 ‖r j₀‖) ^ (2 * (d - 1)) := by
          gcongr
  have hprod_bound :
      ∏ i : Fin d, ∑ k : Fin d, ‖W i k‖ ^ 2 ≤
        ∏ i : Fin d,
          ((if i = j₀ then ‖r i₀ - r j₀‖ ^ 2 * ((d : ℝ) ^ 3 / 3) else (d : ℝ)) *
            (max 1 ‖r i‖) ^ (2 * (d - 1))) := by
    refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _) fun i _ => ?_
    by_cases hij : i = j₀
    · subst hij
      simpa only [↓reduceIte] using hrow_j0
    · simpa only [hij, ↓reduceIte] using hrow_other i hij
  rw [Finset.prod_mul_distrib] at hprod_bound
  have hprod_coeff :
      (∏ i : Fin d, if i = j₀ then ‖r i₀ - r j₀‖ ^ 2 * ((d : ℝ) ^ 3 / 3) else (d : ℝ)) =
        ‖r i₀ - r j₀‖ ^ 2 * ((d : ℝ) ^ (d + 2) / 3) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j₀)]
    simp only [↓reduceIte]
    have herase : (∏ i ∈ Finset.univ.erase j₀,
        if i = j₀ then ‖r i₀ - r j₀‖ ^ 2 * ((d : ℝ) ^ 3 / 3) else (d : ℝ)) =
        (d : ℝ) ^ (d - 1) := by
      have hconst : (∏ i ∈ Finset.univ.erase j₀,
          if i = j₀ then ‖r i₀ - r j₀‖ ^ 2 * ((d : ℝ) ^ 3 / 3) else (d : ℝ)) =
          ∏ _i ∈ Finset.univ.erase j₀, (d : ℝ) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        simp only [(Finset.mem_erase.mp hi).1, ↓reduceIte]
      rw [hconst, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j₀),
        Finset.card_univ, Fintype.card_fin]
    rw [herase]
    have hd_pow : (d : ℝ) ^ 3 * (d : ℝ) ^ (d - 1) = (d : ℝ) ^ (d + 2) := by
      rw [← pow_add]
      congr 1
      omega
    calc ‖r i₀ - r j₀‖ ^ 2 * ((d : ℝ) ^ 3 / 3) * (d : ℝ) ^ (d - 1)
        = ‖r i₀ - r j₀‖ ^ 2 * (((d : ℝ) ^ 3 * (d : ℝ) ^ (d - 1)) / 3) := by ring
      _ = ‖r i₀ - r j₀‖ ^ 2 * ((d : ℝ) ^ (d + 2) / 3) := by rw [hd_pow]
  have hprod_M : (∏ i : Fin d, (max 1 ‖r i‖) ^ (2 * (d - 1))) =
      (∏ i : Fin d, max 1 ‖r i‖) ^ (2 * (d - 1)) := by
    rw [Finset.prod_pow]
  rw [hprod_coeff, hprod_M] at hprod_bound
  exact hhad.trans hprod_bound

/-- Mignotte-type root-separation lower bound in terms of the Mahler measure of `p : ℤ[X]`:
any two distinct complex roots `α ≠ β` of `p` (`2 ≤ p.natDegree`,
`(p.map (algebraMap ℤ ℚ)).Separable`) satisfy
`3 ≤ ‖α - β‖ ^ 2 * d ^ (d + 2) * mahlerMeasure (p.map (algebraMap ℤ ℂ)) ^ (2 * (d - 1))`. -/
theorem mignotte_sep_mahler_complex {p : ℤ[X]} (hd : 2 ≤ p.natDegree)
    (hsep : (p.map (algebraMap ℤ ℚ)).Separable) {α β : ℂ}
    (hα : (p.map (algebraMap ℤ ℂ)).IsRoot α) (hβ : (p.map (algebraMap ℤ ℂ)).IsRoot β)
    (hne : α ≠ β) :
    (3 : ℝ) ≤
      ‖α - β‖ ^ 2 * (p.natDegree : ℝ) ^ (p.natDegree + 2) *
        (p.map (algebraMap ℤ ℂ)).mahlerMeasure ^ (2 * (p.natDegree - 1)) := by
  let d := p.natDegree
  let pC : ℂ[X] := p.map (algebraMap ℤ ℂ)
  have hinjC : Function.Injective (algebraMap ℤ ℂ) := Int.cast_injective
  have hp0 : p ≠ 0 := fun h0 => by simp only [h0, natDegree_zero] at hd; omega
  have hleadZ : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have hleadC : (algebraMap ℤ ℂ) p.leadingCoeff ≠ 0 := by
    simp only [eq_intCast, Int.cast_ne_zero, ne_eq]
    exact hleadZ
  have hdegC : pC.natDegree = d := natDegree_map_eq_of_injective hinjC p
  have hpC0 : pC ≠ 0 := (Polynomial.map_ne_zero_iff hinjC).mpr hp0
  have hpC_sep : pC.Separable := by
    have hmap : pC = (p.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℂ) := by
      rw [Polynomial.map_map, Subsingleton.elim ((algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ))
        (algebraMap ℤ ℂ)]
    rw [hmap]
    exact hsep.map
  have hsplits : pC.Splits := IsAlgClosed.splits pC
  have hlen : pC.roots.toList.length = pC.natDegree := by
    rw [Multiset.length_toList, ← hsplits.natDegree_eq_card_roots]
  let L := pC.roots.toList
  let r : Fin pC.natDegree → ℂ := fun i => L[i.1]'(i.2.trans_eq hlen.symm)
  have hList_eq : List.ofFn r = L := by
    refine List.ext_get ?_ fun n hn1 hn2 => ?_
    · rw [List.length_ofFn]
      exact hlen.symm
    · simp only [List.get_eq_getElem, List.getElem_ofFn, r]
  have hr_roots : Finset.univ.val.map r = pC.roots := by
    change Multiset.ofList (List.map r (List.finRange pC.natDegree)) = pC.roots
    rw [← List.ofFn_eq_map, hList_eq, Multiset.coe_toList]
  have hr_inj : Function.Injective r := by
    have hnodup_L : L.Nodup := Multiset.coe_nodup.mp (by
      rw [Multiset.coe_toList]
      exact nodup_roots hpC_sep)
    intro i j hij
    have heq := (List.Nodup.getElem_inj_iff hnodup_L).mp hij
    exact Fin.ext heq
  have hα_mem : α ∈ L := Multiset.mem_toList.mpr ((mem_roots hpC0).mpr hα.eq_zero)
  have hβ_mem : β ∈ L := Multiset.mem_toList.mpr ((mem_roots hpC0).mpr hβ.eq_zero)
  obtain ⟨i₀', hi₀', hri₀⟩ := List.mem_iff_getElem.mp hα_mem
  obtain ⟨j₀', hj₀', hrj₀⟩ := List.mem_iff_getElem.mp hβ_mem
  let i₀ : Fin pC.natDegree := ⟨i₀', hi₀'.trans_eq hlen⟩
  let j₀ : Fin pC.natDegree := ⟨j₀', hj₀'.trans_eq hlen⟩
  have hr_i₀ : r i₀ = α := hri₀
  have hr_j₀ : r j₀ = β := hrj₀
  have hij_ne : i₀ ≠ j₀ := by
    intro heq
    apply hne
    rw [← hr_i₀, ← hr_j₀, heq]
  have hd_pos : 0 < pC.natDegree := by rw [hdegC]; omega
  have hdiscr_vand := discr_eq_leadingCoeff_pow_mul_det_vandermonde_sq hsplits hd_pos r hr_roots
  have hdiscr_map : pC.discr = ((p.discr : ℤ) : ℂ) := by
    have hdegZ : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (by omega)
    exact discr_map_of_leadingCoeff_ne_zero (algebraMap ℤ ℂ) hdegZ hleadC
  have hvand_ne0 : (Matrix.vandermonde r).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hr_inj
  have hpC_discr_ne0 : pC.discr ≠ 0 := by
    rw [hdiscr_vand]
    exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hpC0)) (pow_ne_zero _ hvand_ne0)
  have hp_discr_ne0 : p.discr ≠ 0 := by
    intro hz
    apply hpC_discr_ne0
    rw [hdiscr_map, hz, Int.cast_zero]
  have hdiscr_norm_ge1 : (1 : ℝ) ≤ ‖pC.discr‖ := by
    rw [hdiscr_map, Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hp_discr_ne0
  have hdiscr_norm_eq : ‖pC.discr‖ =
      ‖pC.leadingCoeff‖ ^ (2 * (pC.natDegree - 1)) * ‖(Matrix.vandermonde r).det‖ ^ 2 := by
    rw [hdiscr_vand, norm_mul, norm_pow, norm_pow]
    congr 2
    omega
  have hvand_bound := norm_det_vandermonde_sq_le (hdegC.symm ▸ hd) r hij_ne
  rw [hr_i₀, hr_j₀] at hvand_bound
  have hmahler : pC.mahlerMeasure = ‖pC.leadingCoeff‖ * ∏ i : Fin pC.natDegree, max 1 ‖r i‖ := by
    rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots, ← hr_roots, Multiset.map_map]
    rfl
  have hcomb : ‖pC.leadingCoeff‖ ^ (2 * (pC.natDegree - 1)) * ‖(Matrix.vandermonde r).det‖ ^ 2 ≤
      ‖α - β‖ ^ 2 * ((d : ℝ) ^ (d + 2) / 3) * pC.mahlerMeasure ^ (2 * (d - 1)) := by
    calc ‖pC.leadingCoeff‖ ^ (2 * (pC.natDegree - 1)) * ‖(Matrix.vandermonde r).det‖ ^ 2
        ≤ ‖pC.leadingCoeff‖ ^ (2 * (pC.natDegree - 1)) *
            (‖α - β‖ ^ 2 * ((pC.natDegree : ℝ) ^ (pC.natDegree + 2) / 3) *
              (∏ i : Fin pC.natDegree, max 1 ‖r i‖) ^ (2 * (pC.natDegree - 1))) := by gcongr
      _ = ‖α - β‖ ^ 2 * ((pC.natDegree : ℝ) ^ (pC.natDegree + 2) / 3) *
            (‖pC.leadingCoeff‖ * ∏ i : Fin pC.natDegree, max 1 ‖r i‖) ^
              (2 * (pC.natDegree - 1)) := by rw [mul_pow]; ring
      _ = ‖α - β‖ ^ 2 * ((pC.natDegree : ℝ) ^ (pC.natDegree + 2) / 3) *
            pC.mahlerMeasure ^ (2 * (pC.natDegree - 1)) := by rw [hmahler]
      _ = ‖α - β‖ ^ 2 * ((d : ℝ) ^ (d + 2) / 3) * pC.mahlerMeasure ^ (2 * (d - 1)) := by
          rw [hdegC]
  have hle : (1 : ℝ) ≤ ‖α - β‖ ^ 2 * ((d : ℝ) ^ (d + 2) / 3) * pC.mahlerMeasure ^ (2 * (d - 1)) :=
    hdiscr_norm_ge1.trans (hdiscr_norm_eq.symm ▸ hcomb)
  linarith

/-- Mignotte-type root-separation lower bound over `ℂ` using the integer coefficient squared norm
`coeffSqNorm p` via Landau's inequality `mahlerMeasure p ≤ √(coeffSqNorm p)`. -/
theorem mignotte_sep_sqNorm_complex {p : ℤ[X]} (hd : 2 ≤ p.natDegree)
    (hsep : (p.map (algebraMap ℤ ℚ)).Separable) {α β : ℂ}
    (hα : (p.map (algebraMap ℤ ℂ)).IsRoot α) (hβ : (p.map (algebraMap ℤ ℂ)).IsRoot β)
    (hne : α ≠ β) :
    (3 : ℝ) ≤
      ‖α - β‖ ^ 2 *
        ((p.natDegree ^ (p.natDegree + 2) * coeffSqNorm p ^ (p.natDegree - 1) : ℕ) : ℝ) := by
  let pC : ℂ[X] := p.map (algebraMap ℤ ℂ)
  have hinjC : Function.Injective (algebraMap ℤ ℂ) := Int.cast_injective
  have hlandau : pC.mahlerMeasure ^ 2 ≤ (coeffSqNorm p : ℝ) := by
    have h1 := Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff pC
    have hsum_nonneg : 0 ≤ ∑ i ∈ pC.support, ‖pC.coeff i‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsq : pC.mahlerMeasure ^ 2 ≤ ∑ i ∈ pC.support, ‖pC.coeff i‖ ^ 2 := by
      calc pC.mahlerMeasure ^ 2
          ≤ (√(∑ i ∈ pC.support, ‖pC.coeff i‖ ^ 2)) ^ 2 :=
            sq_le_sq' (by
              linarith [mahlerMeasure_nonneg pC,
                Real.sqrt_nonneg (∑ i ∈ pC.support, ‖pC.coeff i‖ ^ 2)]) h1
        _ = ∑ i ∈ pC.support, ‖pC.coeff i‖ ^ 2 := Real.sq_sqrt hsum_nonneg
    refine hsq.trans_eq ?_
    rw [coeffSqNorm_cast_real, Polynomial.support_map_of_injective p hinjC]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.coeff_map, eq_intCast, Complex.norm_intCast, sq_abs]
  have hmahler_pow : pC.mahlerMeasure ^ (2 * (p.natDegree - 1)) ≤
      (coeffSqNorm p : ℝ) ^ (p.natDegree - 1) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg _) hlandau (p.natDegree - 1)
  have hsep_m := mignotte_sep_mahler_complex hd hsep hα hβ hne
  have hbound : ‖α - β‖ ^ 2 * (p.natDegree : ℝ) ^ (p.natDegree + 2) *
        pC.mahlerMeasure ^ (2 * (p.natDegree - 1)) ≤
      ‖α - β‖ ^ 2 *
        ((p.natDegree ^ (p.natDegree + 2) * coeffSqNorm p ^ (p.natDegree - 1) : ℕ) : ℝ) := by
    push_cast
    rw [← mul_assoc]
    gcongr
  exact hsep_m.trans hbound

/-- Mignotte-type root-separation lower bound for real roots of `p : ℤ[X]`. -/
theorem mignotte_sep_sqNorm_real {p : ℤ[X]} (hd : 2 ≤ p.natDegree)
    (hsep : (p.map (algebraMap ℤ ℚ)).Separable) {α β : ℝ}
    (hα : (p.map (algebraMap ℤ ℝ)).IsRoot α) (hβ : (p.map (algebraMap ℤ ℝ)).IsRoot β)
    (hne : α ≠ β) :
    (3 : ℝ) ≤
      |α - β| ^ 2 *
        ((p.natDegree ^ (p.natDegree + 2) * coeffSqNorm p ^ (p.natDegree - 1) : ℕ) : ℝ) := by
  have hmap : p.map (algebraMap ℤ ℂ) = (p.map (algebraMap ℤ ℝ)).map (algebraMap ℝ ℂ) := by
    rw [Polynomial.map_map, Subsingleton.elim ((algebraMap ℝ ℂ).comp (algebraMap ℤ ℝ))
      (algebraMap ℤ ℂ)]
  have hαC : (p.map (algebraMap ℤ ℂ)).IsRoot (α : ℂ) := by
    rw [hmap]
    exact hα.map (algebraMap ℝ ℂ)
  have hβC : (p.map (algebraMap ℤ ℂ)).IsRoot (β : ℂ) := by
    rw [hmap]
    exact hβ.map (algebraMap ℝ ℂ)
  have hneC : (α : ℂ) ≠ (β : ℂ) := fun h => hne (Complex.ofReal_injective h)
  have hbound := mignotte_sep_sqNorm_complex hd hsep hαC hβC hneC
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hbound

/-- Mignotte-type root-separation lower bound for a separable rational polynomial `q : ℚ[X]`
witnessed by a nonzero rational multiple `p.map (algebraMap ℤ ℚ) = C c * q` with `p : ℤ[X]`. -/
theorem mignotte_sep_sqNorm_rat {q : ℚ[X]} {p : ℤ[X]} (hd : 2 ≤ q.natDegree) (hsep : q.Separable)
    {c : ℚ} (hc : c ≠ 0) (hpq : p.map (algebraMap ℤ ℚ) = C c * q) {α β : ℝ}
    (hα : (q.map (algebraMap ℚ ℝ)).IsRoot α) (hβ : (q.map (algebraMap ℚ ℝ)).IsRoot β)
    (hne : α ≠ β) :
    (3 : ℝ) ≤
      |α - β| ^ 2 *
        ((q.natDegree ^ (q.natDegree + 2) * coeffSqNorm p ^ (q.natDegree - 1) : ℕ) : ℝ) := by
  have hinjQ : Function.Injective (algebraMap ℤ ℚ) := Int.cast_injective
  have hdeg_eq : p.natDegree = q.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective hinjQ p, hpq,
      Polynomial.natDegree_C_mul hc]
  have hp_sep : (p.map (algebraMap ℤ ℚ)).Separable := by
    rw [hpq]
    have hCc : (C c).Separable := (separable_C c).mpr hc.isUnit
    have hcop : IsCoprime (C c) q := ⟨C c⁻¹, 0, by simp only [← C_mul, inv_mul_cancel₀ hc, C_1,
      zero_mul, add_zero]⟩
    exact hCc.mul hsep hcop
  have hmapR : p.map (algebraMap ℤ ℝ) = C (c : ℝ) * q.map (algebraMap ℚ ℝ) := by
    have h1 : p.map (algebraMap ℤ ℝ) = (p.map (algebraMap ℤ ℚ)).map (algebraMap ℚ ℝ) := by
      rw [Polynomial.map_map, Subsingleton.elim ((algebraMap ℚ ℝ).comp (algebraMap ℤ ℚ))
        (algebraMap ℤ ℝ)]
    rw [h1, hpq, Polynomial.map_mul, Polynomial.map_C]
    rfl
  have hαp : (p.map (algebraMap ℤ ℝ)).IsRoot α := by
    rw [IsRoot.def, hmapR, eval_mul, hα.eq_zero, mul_zero]
  have hβp : (p.map (algebraMap ℤ ℝ)).IsRoot β := by
    rw [IsRoot.def, hmapR, eval_mul, hβ.eq_zero, mul_zero]
  have hbound := mignotte_sep_sqNorm_real (hdeg_eq.symm ▸ hd) hp_sep hαp hβp hne
  rwa [hdeg_eq] at hbound

end Polynomial
