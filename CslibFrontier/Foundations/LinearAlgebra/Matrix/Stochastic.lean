/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/Stochastic.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Stationary vectors of row-stochastic matrices

Every real row-stochastic matrix `M` over a finite nonempty type has a *stationary* probability
vector: `p ᵥ* M = p` with `p ≥ 0` and `∑ i, p i = 1`. In the language of Markov chains, every
finite chain has a stationary distribution.

The proof is linear algebra. Since `M *ᵥ 1 = 1`, the matrix `M - 1` is singular, so some nonzero
`v` has `v ᵥ* M = v`. By the triangle inequality the entrywise absolute value `|v|` satisfies
`|v| ≤ |v| ᵥ* M`, and both sides have the same total because the rows of `M` sum to `1`. So
`|v| ᵥ* M = |v|`, and `|v|` normalized is the stationary vector.

Stationary vectors are what the Blum–Mansour reduction from swap regret to external regret
needs ([BlumMansour2007], §3).

## Main definitions

* `Matrix.stationaryVec`: a chosen stationary probability vector of a row-stochastic matrix.

## Main results

* `Matrix.exists_vecMul_eq_self_of_mem_rowStochastic`: a row-stochastic matrix has a stationary
  probability vector.
* `Matrix.stationaryVec_nonneg`, `Matrix.sum_stationaryVec`, `Matrix.stationaryVec_vecMul`: the
  chosen vector is a stationary probability vector.

## References

* [A. Blum, Y. Mansour, *From External to Internal Regret*][BlumMansour2007]
-/

public section

namespace Matrix

open Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Every real row-stochastic matrix over a finite nonempty type has a stationary probability
vector `p`: `p ᵥ* M = p`, `0 ≤ p` and `∑ i, p i = 1`. -/
theorem exists_vecMul_eq_self_of_mem_rowStochastic [Nonempty n] {M : Matrix n n ℝ}
    (hM : M ∈ rowStochastic ℝ n) :
    ∃ p : n → ℝ, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ p ᵥ* M = p := by
  have hdet : (M - 1).det = 0 := by
    refine exists_mulVec_eq_zero_iff.1 ⟨1, one_ne_zero, ?_⟩
    rw [sub_mulVec, one_mulVec, one_vecMul_of_mem_rowStochastic hM, sub_self]
  obtain ⟨v, hv0, hv⟩ := exists_vecMul_eq_zero_iff.2 hdet
  rw [vecMul_sub, vecMul_one, sub_eq_zero] at hv
  set w : n → ℝ := fun i => |v i|
  have hle : ∀ j, w j ≤ (w ᵥ* M) j := fun j => by
    calc w j = |(v ᵥ* M) j| := by rw [hv]
      _ = |∑ i, v i * M i j| := rfl
      _ ≤ ∑ i, |v i * M i j| := abs_sum_le_sum_abs _ _
      _ = (w ᵥ* M) j := sum_congr rfl fun i _ => by
          rw [abs_mul, abs_of_nonneg (nonneg_of_mem_rowStochastic hM)]
  have htotal : ∑ j, (w ᵥ* M) j = ∑ j, w j := by
    simp only [vecMul, dotProduct]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_sum, sum_row_of_mem_rowStochastic hM, mul_one]
  have hw : w ᵥ* M = w := by
    have h0 : ∑ j, ((w ᵥ* M) j - w j) = 0 := by rw [sum_sub_distrib, htotal, sub_self]
    funext j
    exact (sub_eq_zero.1 ((sum_eq_zero_iff_of_nonneg fun j _ => sub_nonneg.2 (hle j)).1 h0 j
      (mem_univ j)))
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
  have hs : 0 < ∑ i, w i :=
    sum_pos' (fun i _ => abs_nonneg (v i)) ⟨k, mem_univ k, abs_pos.2 hk⟩
  refine ⟨(∑ i, w i)⁻¹ • w, fun i => ?_, ?_, ?_⟩
  · exact mul_nonneg (inv_nonneg.2 hs.le) (abs_nonneg (v i))
  · simp only [Pi.smul_apply, smul_eq_mul, ← mul_sum]
    exact inv_mul_cancel₀ hs.ne'
  · rw [smul_vecMul, hw]

open Classical in
/-- A stationary probability vector of a row-stochastic matrix `M`, chosen by
`exists_vecMul_eq_self_of_mem_rowStochastic`; `0` if `M` is not row-stochastic or `n` is empty. -/
noncomputable def stationaryVec (M : Matrix n n ℝ) : n → ℝ :=
  if h : Nonempty n ∧ M ∈ rowStochastic ℝ n then
    haveI := h.1
    Classical.choose (exists_vecMul_eq_self_of_mem_rowStochastic h.2)
  else 0

private theorem stationaryVec_spec [Nonempty n] {M : Matrix n n ℝ} (hM : M ∈ rowStochastic ℝ n) :
    (∀ i, 0 ≤ stationaryVec M i) ∧ ∑ i, stationaryVec M i = 1 ∧
      stationaryVec M ᵥ* M = stationaryVec M := by
  classical
  have h : Nonempty n ∧ M ∈ rowStochastic ℝ n := ⟨inferInstance, hM⟩
  rw [stationaryVec, dite_eq_left h]
  exact Classical.choose_spec (exists_vecMul_eq_self_of_mem_rowStochastic h.2)

/-- The chosen stationary vector is nonnegative. -/
theorem stationaryVec_nonneg [Nonempty n] {M : Matrix n n ℝ} (hM : M ∈ rowStochastic ℝ n)
    (i : n) : 0 ≤ stationaryVec M i :=
  (stationaryVec_spec hM).1 i

/-- The chosen stationary vector sums to `1`. -/
theorem sum_stationaryVec [Nonempty n] {M : Matrix n n ℝ} (hM : M ∈ rowStochastic ℝ n) :
    ∑ i, stationaryVec M i = 1 :=
  (stationaryVec_spec hM).2.1

/-- The chosen stationary vector is stationary: `stationaryVec M ᵥ* M = stationaryVec M`. -/
theorem stationaryVec_vecMul [Nonempty n] {M : Matrix n n ℝ} (hM : M ∈ rowStochastic ℝ n) :
    stationaryVec M ᵥ* M = stationaryVec M :=
  (stationaryVec_spec hM).2.2

end Matrix
