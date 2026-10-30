/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Foundations.RingTheory.CyclicIntRing
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Executable coefficient operations for the existing cyclic integer quotient

The existing CyclicIntRing remains the ring model. Its multiplication coefficients are
finite cyclic convolutions, with an explicit natural partner index suitable for native array
access. Partial-sum magnitude bounds account for the actual intermediate accumulators.

The quotient expansion and multiplication proof adapt Spec/Sec3/Theorem17/Cyclic.lean,
lines 52–141, at anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
The function representation and partial-sum bound below serve the native coefficient kernel.
No additional ring type or execution model is introduced.
-/

public section

namespace Cslib.CyclicIntRing

/-- The unique partner below p whose sum with i has residue r, when r and i are below p. -/
@[expose] def subIndex (p r i : ℕ) : ℕ := if i ≤ r then r - i else r + p - i

/-- Cyclic coefficient indexing remains within the coefficient array. -/
theorem subIndex_lt {p r i : ℕ} (hr : r < p) (hi : i < p) : subIndex p r i < p := by
  unfold subIndex
  split_ifs <;> omega

/-- Partial convolution of two coefficient arrays, without assumptions about their lengths. -/
@[expose] def partialConvolution (p : ℕ) (u v : ℕ → ℤ) (r k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range k, u i * v (subIndex p r i)

/-- The executable cyclic convolution of two arrays of p coefficients. -/
@[expose] def convolution (p : ℕ) (u v : ℕ → ℤ) (r : ℕ) : ℤ :=
  partialConvolution p u v r p

/-- The initial accumulator is zero. -/
@[simp] theorem partialConvolution_zero (p : ℕ) (u v : ℕ → ℤ) (r : ℕ) :
    partialConvolution p u v r 0 = 0 := by simp [partialConvolution]

/-- The next actual multiply/accumulate term. -/
theorem partialConvolution_succ (p : ℕ) (u v : ℕ → ℤ) (r k : ℕ) :
    partialConvolution p u v r (k + 1) =
      partialConvolution p u v r k + u k * v (subIndex p r k) := by
  exact Finset.sum_range_succ _ _

/-- Every partial accumulator is bounded by the number of terms times the input envelopes. -/
theorem partialConvolution_natAbs_le {p r k A B : ℕ} {u v : ℕ → ℤ}
    (hr : r < p) (hk : k ≤ p)
    (hu : ∀ i < p, (u i).natAbs ≤ A) (hv : ∀ i < p, (v i).natAbs ≤ B) :
    (partialConvolution p u v r k).natAbs ≤ k * (A * B) := by
  calc
    _ ≤ ∑ i ∈ Finset.range k, (u i * v (subIndex p r i)).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range k, A * B := by
      apply Finset.sum_le_sum
      intro i hi
      have hip : i < p := (Finset.mem_range.mp hi).trans_le hk
      rw [Int.natAbs_mul]
      exact Nat.mul_le_mul (hu i hip) (hv _ (subIndex_lt hr hip))
    _ = k * (A * B) := by simp

variable {p : ℕ}

/-- Quotient representatives have no coefficients at degrees at least p. -/
theorem coeff_eq_zero_of_le (hp : p ≠ 0) (z : CyclicIntRing p) {r : ℕ} (hr : p ≤ r) :
    coeff hp r z = 0 := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [coeff_apply, AdjoinRoot.modByMonicHom_mk]
  apply Polynomial.coeff_eq_zero_of_degree_lt
  refine lt_of_lt_of_le
    (Polynomial.degree_modByMonic_lt f (Polynomial.monic_X_pow_sub_C (1 : ℤ) hp)) ?_
  rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
  exact_mod_cast hr

/-- Expand an existing quotient element in its p coefficient powers. -/
theorem eq_sum_coeff (hp : p ≠ 0) (z : CyclicIntRing p) :
    z = ∑ i ∈ Finset.range p, coeff hp i z • x p ^ i := by
  have hmk := AdjoinRoot.mk_leftInverse (Polynomial.monic_X_pow_sub_C (1 : ℤ) hp) z
  set f := AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow_sub_C (1 : ℤ) hp) z with hf
  have hdeg : f.natDegree < p := by
    by_contra hc
    have hlead : f.coeff f.natDegree = 0 := coeff_eq_zero_of_le hp z (not_lt.mp hc)
    rw [Polynomial.leadingCoeff_eq_zero.mp hlead, Polynomial.natDegree_zero] at hc
    exact hc (Nat.pos_of_ne_zero hp)
  conv_lhs => rw [← hmk, Polynomial.as_sum_range' f p hdeg, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X,
    AdjoinRoot.mk_C, zsmul_eq_mul]
  simp [coeff_apply, x, hf]

private theorem mod_eq_iff_subIndex {i j r : ℕ} (hi : i < p) (hj : j < p) (hr : r < p) :
    r = (i + j) % p ↔ j = subIndex p r i := by
  unfold subIndex
  by_cases h : i + j < p
  · rw [Nat.mod_eq_of_lt h]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod (not_lt.mp h), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega

/-- Coefficient multiplication in the existing quotient is exactly executable convolution. -/
theorem coeff_mul_eq_convolution (hp : p ≠ 0) (z w : CyclicIntRing p)
    {r : ℕ} (hr : r < p) :
    coeff hp r (z * w) = convolution p (fun i => coeff hp i z) (fun i => coeff hp i w) r := by
  conv_lhs => rw [eq_sum_coeff hp z, eq_sum_coeff hp w, Finset.sum_mul_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hip := Finset.mem_range.mp hi
  have hj := subIndex_lt hr hip
  rw [map_sum]
  simp only [smul_mul_smul_comm, ← pow_add, map_zsmul, coeff_x_pow, smul_eq_mul]
  rw [Finset.sum_eq_single (subIndex p r i)]
  · rw [ite_eq_left ((mod_eq_iff_subIndex hip hj hr).mpr rfl), mul_one]
  · intro j hj' hne
    rw [ite_eq_right fun h => hne ((mod_eq_iff_subIndex hip (Finset.mem_range.mp hj') hr).mp h),
      mul_zero]
  · exact fun h => absurd (Finset.mem_range.mpr hj) h

end Cslib.CyclicIntRing
