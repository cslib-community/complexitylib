/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORTransfer
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Geometric eigenvectors of the signed carry matrix

The full spectral calculation in [WangLvShenZhang2027], Theorem 5(ii),
PDF pp. 17–18. `signedMatrix` is the transfer matrix already derived from actual
word addition, reindexed by `Fin`. The explicit odd roots give an invertible
geometric eigenvector matrix, with a proved Fourier inverse. `bitRunFactor_spectrum`
gives the weighted eigenvalue-power sum for independent uniform full-width words.
Here width is `(h + 1) + j`, bit position is `j`, and the run has `z` additions;
`h` counts the bits above the observed bit. The trigonometric identification and
decay bounds are supplied by `AddXNORDecay`.
-/

public section

open scoped BigOperators

namespace Cslib.Cryptanalysis.AddXNOR

/-- Complex form of the signed carry matrix, indexed by integer low states. -/
@[expose] def signedMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun t s => if t < s then -1 else 1

/-- Reindexing the actual word transfer gives exactly the spectral matrix. -/
theorem signedMatrix_carryMatrix (j : ℕ) (t s : BitVec j) :
    signedMatrix (2 ^ j) (BitVec.equivFin t) (BitVec.equivFin s) =
      (carryMatrix j t s : ℂ) := by
  simp only [signedMatrix, carryMatrix, Fin.lt_def, BitVec.equivFin_apply, BitVec.val_toFin]
  split <;> norm_num

private theorem signed_sum (N : ℕ) (t : Fin N) (r : ℂ) :
    (signedMatrix N).mulVec (fun s => r ^ s.val) t =
      2 * (∑ s ∈ Finset.range (t.val + 1), r ^ s) - ∑ s ∈ Finset.range N, r ^ s := by
  simp only [Matrix.mulVec, dotProduct, signedMatrix, Fin.lt_def]
  have ht : t.val + 1 ≤ N := by omega
  have he : N = (t.val + 1) + (N - (t.val + 1)) := by omega
  rw [show (∑ s : Fin N, (if t.val < s.val then (-1 : ℂ) else 1) * r ^ s.val) =
    ∑ s ∈ Finset.range N, (if t.val < s then (-1 : ℂ) else 1) * r ^ s from
      Fin.sum_univ_eq_sum_range
        (fun s => (if t.val < s then (-1 : ℂ) else 1) * r ^ s) N]
  conv_lhs => arg 1; rw [he]
  conv_rhs => arg 2; arg 1; rw [he]
  conv_lhs => rw [Finset.sum_range_add]
  conv_rhs => arg 2; rw [Finset.sum_range_add]
  have hp : (∑ s ∈ Finset.range (t.val + 1),
      (if t.val < s then (-1 : ℂ) else 1) * r ^ s) =
      ∑ s ∈ Finset.range (t.val + 1), r ^ s := by
    apply Finset.sum_congr rfl
    intro s hs
    simp only [Finset.mem_range] at hs
    rw [ite_eq_right (by omega), one_mul]
  have hn : (∑ s ∈ Finset.range (N - (t.val + 1)),
      (if t.val < t.val + 1 + s then (-1 : ℂ) else 1) * r ^ (t.val + 1 + s)) =
      -(∑ s ∈ Finset.range (N - (t.val + 1)), r ^ (t.val + 1 + s)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [ite_eq_left (by omega), neg_one_mul]
  rw [hp, hn]
  ring

/-- Every root of r^N=-1 gives the paper's geometric eigenvector, with its
exact eigenvalue. No eigenvalue or transition formula is assumed. -/
theorem signedMatrix_geometric_eigenvector (N : ℕ) (r : ℂ) (hr : r ^ N = -1)
    (t : Fin N) :
    (signedMatrix N).mulVec (fun s => r ^ s.val) t =
      (2 * r / (r - 1)) * r ^ t.val := by
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, one_pow] at hr
    norm_num at hr
  rw [signed_sum, geom_sum_eq hr1, geom_sum_eq hr1, hr, pow_succ]
  field_simp
  ring

/-- The N distinct odd roots of unity used by the source diagonalization. -/
@[expose] noncomputable def carryRoot (N : ℕ) (k : Fin N) : ℂ :=
  Complex.exp (((2 * k.val + 1 : ℕ) : ℂ) * (Real.pi : ℂ) / N * Complex.I)

/-- These are actual roots of r^N=-1 for every positive dimension. -/
theorem carryRoot_pow (N : ℕ) (k : Fin N) : carryRoot N k ^ N = -1 := by
  have hk := k.isLt
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  rw [carryRoot, ← Complex.exp_nat_mul]
  have he : (N : ℂ) * ((2 * k.val + 1 : ℕ) * (Real.pi : ℂ) / N * Complex.I) =
      (2 * k.val + 1 : ℕ) * ((Real.pi : ℂ) * Complex.I) := by field_simp
  rw [he, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  rw [pow_add, pow_mul]
  norm_num

/-- No two indices give the same odd root. -/
theorem carryRoot_injective (N : ℕ) : Function.Injective (carryRoot N) := by
  intro k l he
  have hk := k.isLt
  have hl := l.isLt
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  obtain ⟨z, hz⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hi := congrArg Complex.im hz
  norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im,
    Complex.normSq_ofReal] at hi
  have heq : (k.val : ℝ) - l.val = (z : ℝ) * N := by
    field_simp at hi
    nlinarith [Real.pi_pos]
  have hei : (k.val : ℤ) - l.val = z * N := by exact_mod_cast heq
  have hzi : z = 0 := by
    have hn : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
    nlinarith
  rw [hzi, zero_mul, sub_eq_zero] at hei
  exact Fin.ext (by exact_mod_cast hei)

/-- The explicit complex eigenvalues, before rewriting as 1-i cot(theta). -/
@[expose] noncomputable def carryEigenvalue (N : ℕ) (k : Fin N) : ℂ :=
  2 * carryRoot N k / (carryRoot N k - 1)

/-- All of the explicitly constructed geometric vectors are eigenvectors. -/
theorem carryRoot_eigenvector (N : ℕ) (k t : Fin N) :
    (signedMatrix N).mulVec (fun s => carryRoot N k ^ s.val) t =
      carryEigenvalue N k * carryRoot N k ^ t.val :=
  signedMatrix_geometric_eigenvector N (carryRoot N k) (carryRoot_pow N k) t

/-- Each explicit root is on the unit circle. -/
theorem norm_carryRoot (N : ℕ) (k : Fin N) : ‖carryRoot N k‖ = 1 := by
  rw [carryRoot, Complex.norm_exp]
  norm_num [Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

/-- An odd root is nonzero. -/
theorem carryRoot_ne_zero (N : ℕ) (k : Fin N) : carryRoot N k ≠ 0 := by
  intro h
  have he := norm_carryRoot N k
  rw [h, norm_zero] at he
  norm_num at he

/-- An odd root never equals one. -/
theorem carryRoot_ne_one (N : ℕ) (k : Fin N) : carryRoot N k ≠ 1 := by
  intro h
  have he := carryRoot_pow N k
  rw [h, one_pow] at he
  norm_num at he

/-- Inverse discrete Fourier matrix for the odd roots. -/
@[expose] noncomputable def carryFourierInverse (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun k s => (carryRoot N k)⁻¹ ^ s.val / N

private theorem root_orthogonality (N : ℕ) (k l : Fin N) :
    (∑ s : Fin N, (carryRoot N k)⁻¹ ^ s.val * carryRoot N l ^ s.val) =
      if k = l then (N : ℂ) else 0 := by
  by_cases h : k = l
  · subst l
    simp only [← mul_pow, inv_mul_cancel₀ (carryRoot_ne_zero N k), one_pow]
    simp
  · have hr : carryRoot N l / carryRoot N k ≠ 1 := by
      intro he
      have heq := (div_eq_one_iff_eq (carryRoot_ne_zero N k)).mp he
      exact h ((carryRoot_injective N heq).symm)
    have hp : (carryRoot N l / carryRoot N k) ^ N = 1 := by
      rw [div_pow, carryRoot_pow, carryRoot_pow]
      norm_num
    simp only [← mul_pow, ← div_eq_inv_mul, Fin.sum_univ_eq_sum_range,
      geom_sum_eq hr, hp, sub_self, zero_div, ite_eq_right h]

/-- Columns are the explicit geometric eigenvectors. -/
@[expose] noncomputable def carryEigenvectors (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  (Matrix.vandermonde (carryRoot N)).transpose

/-- The displayed Fourier inverse really is the inverse of the eigenvector matrix. -/
theorem carryFourierInverse_mul (N : ℕ) :
    carryFourierInverse N * carryEigenvectors N = 1 := by
  ext k l
  have hN : (N : ℂ) ≠ 0 := by
    have hk := k.isLt
    exact_mod_cast (show N ≠ 0 by omega)
  simp only [Matrix.mul_apply, carryFourierInverse, carryEigenvectors,
    Matrix.transpose_apply, Matrix.vandermonde_apply, div_mul_eq_mul_div]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, root_orthogonality]
  by_cases h : k = l <;> simp [h, hN, Matrix.one_apply]

/-- The eigenvector matrix is invertible, including the empty-dimension convention. -/
theorem carryEigenvectors_det_ne_zero (N : ℕ) : (carryEigenvectors N).det ≠ 0 := by
  rw [carryEigenvectors, Matrix.det_transpose, Matrix.det_vandermonde_ne_zero_iff]
  exact carryRoot_injective N

/-- Explicit eigensystem identity for the actual signed carry matrix. -/
theorem carry_eigensystem (N : ℕ) :
    signedMatrix N * carryEigenvectors N =
      carryEigenvectors N * Matrix.diagonal (carryEigenvalue N) := by
  ext t k
  rw [Matrix.mul_diagonal]
  change (signedMatrix N).mulVec (fun s => carryRoot N k ^ s.val) t =
    carryRoot N k ^ t.val * carryEigenvalue N k
  rw [carryRoot_eigenvector, mul_comm]

/-- Explicit diagonalization, derived from the word transfer matrix entries. -/
theorem carry_diagonalization (N : ℕ) :
    (carryEigenvectors N)⁻¹ * signedMatrix N * carryEigenvectors N =
      Matrix.diagonal (carryEigenvalue N) := by
  rw [Matrix.mul_assoc, carry_eigensystem, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (carryEigenvectors_det_ne_zero N)),
    Matrix.one_mul]

/-- Closed form of the inverse eigenvector matrix. -/
theorem carryEigenvectors_inv (N : ℕ) :
    (carryEigenvectors N)⁻¹ = carryFourierInverse N := by
  have hi := Matrix.mul_nonsing_inv (carryEigenvectors N)
    (isUnit_iff_ne_zero.mpr (carryEigenvectors_det_ne_zero N))
  calc
    _ = (carryFourierInverse N * carryEigenvectors N) * (carryEigenvectors N)⁻¹ := by
      rw [carryFourierInverse_mul, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, hi, Matrix.mul_one]

/-- Every power is explicitly diagonalized using the same matrices. -/
theorem signedMatrix_pow (N z : ℕ) :
    signedMatrix N ^ z = carryEigenvectors N *
      Matrix.diagonal (fun k => carryEigenvalue N k ^ z) * carryFourierInverse N := by
  have hi := Matrix.mul_nonsing_inv (carryEigenvectors N)
    (isUnit_iff_ne_zero.mpr (carryEigenvectors_det_ne_zero N))
  rw [carryEigenvectors_inv] at hi
  have he : signedMatrix N ^ z * carryEigenvectors N =
      carryEigenvectors N * Matrix.diagonal (fun k => carryEigenvalue N k ^ z) := by
    induction z with
    | zero => simp
    | succ z ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, carry_eigensystem,
        Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
      congr 2
      funext k
      exact (pow_succ' _ _).symm
  calc
    _ = (signedMatrix N ^ z * carryEigenvectors N) * carryFourierInverse N := by
      rw [Matrix.mul_assoc, hi, Matrix.mul_one]
    _ = _ := by rw [he]

private theorem root_weight (N : ℕ) (k : Fin N) :
    (∑ t : Fin N, carryRoot N k ^ t.val) *
      (∑ s : Fin N, (carryRoot N k)⁻¹ ^ s.val) =
        (Complex.normSq (carryEigenvalue N k) : ℂ) := by
  have hr0 := carryRoot_ne_zero N k
  have hr1 := carryRoot_ne_one N k
  have hri : (carryRoot N k)⁻¹ ≠ 1 := inv_ne_one.mpr hr1
  have hc : (starRingEnd ℂ) (carryRoot N k) = (carryRoot N k)⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, norm_carryRoot]
    norm_num
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range,
    geom_sum_eq hr1, geom_sum_eq hri, inv_pow, carryRoot_pow]
  rw [Complex.normSq_eq_conj_mul_self, carryEigenvalue]
  simp only [map_div₀, map_mul, map_ofNat, map_sub, map_one, hc]
  field_simp
  ring

/-- Sum of every matrix-power entry, in the source's spectral weights. -/
theorem signedMatrix_pow_sum (N z : ℕ) :
    (∑ t : Fin N, ∑ s : Fin N, (signedMatrix N ^ z) t s) =
      (N : ℂ)⁻¹ * ∑ k : Fin N,
        (Complex.normSq (carryEigenvalue N k) : ℂ) * carryEigenvalue N k ^ z := by
  rw [signedMatrix_pow]
  have he (t s : Fin N) :
      (carryEigenvectors N * Matrix.diagonal (fun k => carryEigenvalue N k ^ z) *
        carryFourierInverse N) t s =
      ∑ k, (carryRoot N k ^ t.val * carryEigenvalue N k ^ z) *
        ((carryRoot N k)⁻¹ ^ s.val / N) := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, carryEigenvectors, Matrix.transpose_apply,
      Matrix.vandermonde_apply, carryFourierInverse]
  simp only [he]
  conv_lhs => arg 2; ext t; rw [Finset.sum_comm]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← root_weight]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro s _
  ring

private theorem signedMatrix_pow_carryMatrix (j z : ℕ) (t s : BitVec j) :
    (signedMatrix (2 ^ j) ^ z) (BitVec.equivFin t) (BitVec.equivFin s) =
      ((carryMatrix j ^ z) t s : ℂ) := by
  induction z generalizing t s with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, BitVec.equivFin_apply]
    by_cases h : t = s
    · subst s; norm_num
    · have hn : t.toFin ≠ s.toFin := fun he => h (BitVec.toFin_injective he)
      simp [h, hn]
  | succ z ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Rat.cast_sum]
    symm
    apply Fintype.sum_equiv BitVec.equivFin.toEquiv
    intro a
    rw [Rat.cast_mul]
    change ((carryMatrix j ^ z) t a : ℂ) * (carryMatrix j a s : ℂ) =
      (signedMatrix (2 ^ j) ^ z) (BitVec.equivFin t) (BitVec.equivFin a) *
        signedMatrix (2 ^ j) (BitVec.equivFin a) (BitVec.equivFin s)
    rw [ih, signedMatrix_carryMatrix]

/-- Theorem 5(ii)'s exact spectral sum, derived from independent uniform
full-width word operations. `normSq` is the squared complex absolute value.
The eigenvalues are explicitly `2*r/(r-1)` for the odd roots `r`; this is the
algebraic form of the source's `1-i*cot(theta)` values. -/
theorem bitRunFactor_spectrum (h j z : ℕ) :
    (bitRunFactor ((h + 1) + j) j z : ℂ) =
      (2 ^ j : ℂ)⁻¹ ^ (z + 2) * ∑ k : Fin (2 ^ j),
        (Complex.normSq (carryEigenvalue (2 ^ j) k) : ℂ) *
          carryEigenvalue (2 ^ j) k ^ z := by
  rw [bitRunFactor_matrix]
  simp only [← Matrix.transpose_pow, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, mul_one]
  push_cast
  have hs : (∑ s : BitVec j, ∑ t : BitVec j, ((carryMatrix j ^ z) t s : ℂ)) =
      ∑ t : Fin (2 ^ j), ∑ s : Fin (2 ^ j), (signedMatrix (2 ^ j) ^ z) t s := by
    rw [Finset.sum_comm]
    apply Fintype.sum_equiv BitVec.equivFin.toEquiv
    intro t
    apply Fintype.sum_equiv BitVec.equivFin.toEquiv
    intro s
    exact (signedMatrix_pow_carryMatrix j z t s).symm
  rw [hs, signedMatrix_pow_sum]
  simp only [show z + 2 = (z + 1) + 1 by omega, pow_succ, Nat.cast_pow, Nat.cast_ofNat]
  ring

end Cslib.Cryptanalysis.AddXNOR
