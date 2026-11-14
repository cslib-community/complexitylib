/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.MaximalMinorSquareSaturation

/-!
# The wide rectangular simplex theorem

This file completes the case `2 ≤ n < m`.  The local Schur-chart argument
places a power of the pivot times the homogenized polynomial in the square
of the maximal-minor ideal.  Generic determinantal primaryness cancels that
pivot power, and tau-homogenization then reconstructs the original
polynomial modulo the simplex equation.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`WideSimplexTheorem.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

namespace WidePolynomial

open GeneralAsymmetricC1

/-- The homogenized polynomial belongs globally to the square of the
maximal-minor ideal. -/
theorem tauHomogenizeWide_mem_maximalMinorIdeal_sq
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (P : WidePoly (k + 1) (k + r))
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P) :
    tauHomogenizeWide (by omega : 0 < k + 1)
        (by omega : 0 < k + r) P ∈
      maximalMinorIdeal (k + 1) (k + r) ^ 2 := by
  obtain ⟨N, hN⟩ :=
    exists_pivot_pow_mul_tauHomogenize_mem_maximalMinorIdeal_sq
      hk hr P hDPI hRKO
  exact mem_maximalMinorIdeal_sq_of_pivot_pow_mul_mem hr hN

/-- Core parametrized form of the paper's wide theorem.  Here the matrix
has `(k+1)` rows and `(k+r)` columns; the strict wide case is `1 < r`.
The slightly stronger hypothesis `0 < r` also includes the square boundary. -/
theorem wide_simplex_maximalMinor_sq_core
    {k r : ℕ} (hk : 0 < k) (hr : 0 < r)
    (P : WidePoly (k + 1) (k + r))
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P) :
    P ∈ maximalMinorIdeal (k + 1) (k + r) ^ 2 ⊔
      Ideal.span (Set.singleton (tauPolyWide (by omega : 0 < k + 1)
        (by omega : 0 < k + r) - 1) : Set (WidePoly (k + 1) (k + r))) := by
  let H := tauHomogenizeWide (by omega : 0 < k + 1)
    (by omega : 0 < k + r) P
  let J := Ideal.span (Set.singleton (tauPolyWide (by omega : 0 < k + 1)
    (by omega : 0 < k + r) - 1) : Set (WidePoly (k + 1) (k + r)))
  have hH : H ∈ maximalMinorIdeal (k + 1) (k + r) ^ 2 :=
    tauHomogenizeWide_mem_maximalMinorIdeal_sq hk hr P hDPI hRKO
  obtain ⟨K, hK⟩ := tauHomogenizeWide_sub_original
    (by omega : 0 < k + 1) (by omega : 0 < k + r) P
  have hgen : tauPolyWide (by omega : 0 < k + 1)
      (by omega : 0 < k + r) - 1 ∈ J := by
    exact Ideal.subset_span (Set.mem_singleton _)
  have hkernel :
      (tauPolyWide (by omega : 0 < k + 1)
        (by omega : 0 < k + r) - 1) * K ∈ J :=
    J.mul_mem_right K hgen
  have hHsup : H ∈ maximalMinorIdeal (k + 1) (k + r) ^ 2 ⊔ J :=
    (show maximalMinorIdeal (k + 1) (k + r) ^ 2 ≤
      maximalMinorIdeal (k + 1) (k + r) ^ 2 ⊔ J from le_sup_left) hH
  have hkernelsup :
      (tauPolyWide (by omega : 0 < k + 1)
        (by omega : 0 < k + r) - 1) * K ∈
          maximalMinorIdeal (k + 1) (k + r) ^ 2 ⊔ J :=
    (show J ≤ maximalMinorIdeal (k + 1) (k + r) ^ 2 ⊔ J from
      le_sup_right) hkernel
  change P ∈ maximalMinorIdeal (k + 1) (k + r) ^ 2 ⊔ J
  have hsub :=
    (maximalMinorIdeal (k + 1) (k + r) ^ 2 ⊔ J).sub_mem
      hHsup hkernelsup
  have hdiff : H - P =
      (tauPolyWide (by omega : 0 < k + 1)
        (by omega : 0 < k + r) - 1) * K := by
    simpa [H] using hK
  have hP : P = H -
      (tauPolyWide (by omega : 0 < k + 1)
        (by omega : 0 < k + r) - 1) * K := by
    calc
      P = H - (H - P) := by ring
      _ = H - (tauPolyWide (by omega : 0 < k + 1)
          (by omega : 0 < k + r) - 1) * K := by rw [hdiff]
  rw [hP]
  exact hsub

/-- Paper-facing form for arbitrary dimensions `2 ≤ n < m`:
`P` belongs to the square of the generic maximal-minor ideal modulo the
simplex equation `tau - 1`. -/
theorem wide_simplex_maximalMinor_sq
    {n m : ℕ} (hn : 2 ≤ n) (hnm : n < m)
    (P : WidePoly n m)
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P) :
    P ∈ maximalMinorIdeal n m ^ 2 ⊔
      Ideal.span (Set.singleton (tauPolyWide (by omega : 0 < n)
        (by omega : 0 < m) - 1) : Set (WidePoly n m)) := by
  cases n with
  | zero => omega
  | succ k =>
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le
        (show k ≤ m by omega)
      exact wide_simplex_maximalMinor_sq_core
        (k := k) (r := r) (by omega) (by omega) P hDPI hRKO

/-! ## Degree consequence -/

/-- Every maximal minor has no monomial below total degree `n`, so the
maximal-minor ideal lies in the `n`th power of the variable ideal. -/
lemma maximalMinorIdeal_le_idealOfVars_pow (n m : ℕ) :
    maximalMinorIdeal n m ≤
      MvPolynomial.idealOfVars (WideVar n m) ℝ ^ n := by
  rw [maximalMinorIdeal, Ideal.span_le]
  rintro _ ⟨S, rfl⟩
  apply (MvPolynomial.mem_pow_idealOfVars_iff' n _).mpr
  intro d hd
  exact (maximalMinorPoly_isHomogeneous S).coeff_eq_zero (by omega)

/-- Consequently, every element of the square has no monomial below total
degree `2*n`. -/
lemma maximalMinorIdeal_sq_le_idealOfVars_pow_two_mul (n m : ℕ) :
    maximalMinorIdeal n m ^ 2 ≤
      MvPolynomial.idealOfVars (WideVar n m) ℝ ^ (2 * n) := by
  calc
    maximalMinorIdeal n m ^ 2 ≤
        (MvPolynomial.idealOfVars (WideVar n m) ℝ ^ n) ^ 2 :=
      Ideal.pow_right_mono (maximalMinorIdeal_le_idealOfVars_pow n m) 2
    _ = MvPolynomial.idealOfVars (WideVar n m) ℝ ^ (n * 2) := by
      rw [pow_mul]
    _ = MvPolynomial.idealOfVars (WideVar n m) ℝ ^ (2 * n) := by
      rw [Nat.mul_comm]

/-- If the polynomial is nonzero at some point of the simplex, its total
degree is at least `2*n`. -/
theorem wide_simplex_totalDegree_lower_bound
    {n m : ℕ} (hn : 2 ≤ n) (hnm : n < m)
    (P : WidePoly n m)
    (hDPI : PolynomialDPI P) (hRKO : PolynomialRKO P)
    (hPnonzero : ∃ U : Mat n m, Simplex U ∧ peval P U ≠ 0) :
    2 * n ≤ P.totalDegree := by
  let H := tauHomogenizeWide (by omega : 0 < n) (by omega : 0 < m) P
  have hHmem : H ∈ maximalMinorIdeal n m ^ 2 := by
    cases n with
    | zero => omega
    | succ k =>
        obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le
          (show k ≤ m by omega)
        exact tauHomogenizeWide_mem_maximalMinorIdeal_sq
          (k := k) (r := r) (by omega) (by omega) P hDPI hRKO
  obtain ⟨U, hU, hPU⟩ := hPnonzero
  have hHne : H ≠ 0 := by
    intro hzero
    have heval : peval H U = peval P U := by
      exact tauHomogenizeWide_eval_eq_on_simplex
        (by omega : 0 < n) (by omega : 0 < m) P hU
    rw [hzero] at heval
    simp only [peval, map_zero] at heval
    exact hPU heval.symm
  have hHvars : H ∈
      MvPolynomial.idealOfVars (WideVar n m) ℝ ^ (2 * n) :=
    (maximalMinorIdeal_sq_le_idealOfVars_pow_two_mul n m) hHmem
  obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero hHne
  have hdsupport : d ∈ H.support := MvPolynomial.mem_support_iff.mpr hd
  have hdlower : 2 * n ≤ d.degree :=
    (MvPolynomial.mem_pow_idealOfVars_iff (2 * n) H).mp hHvars d hdsupport
  have hdupper : d.degree ≤ H.totalDegree :=
    MvPolynomial.le_totalDegree hdsupport
  have hHdegree : H.totalDegree = P.totalDegree :=
    (tauHomogenizeWide_isHomogeneous
      (by omega : 0 < n) (by omega : 0 < m) P).totalDegree hHne
  omega


end WidePolynomial

end

end Cslib.FiniteSampleInformation
