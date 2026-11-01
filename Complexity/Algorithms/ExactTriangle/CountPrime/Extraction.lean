/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.CountPrime

/-!
# Nonnegative selected coefficients for modular triangle counting

These bridges justify the real counter's unsigned extraction and summation from the existing
cyclic product specification. They do not assume a matrix multiplication or native execution.
-/

public section

namespace Cslib.Algorithms.ExactTriangle.CountPrime

open Cslib.Algorithms.MatrixMultiplication.Strassen

/-- The unsigned value extracted from one actual original-coordinate product coefficient. -/
@[expose] def pairCoefficient {n : ℕ} (p k : ℕ)
    (wAB wBC wAC : Fin n → Fin n → ℤ) (a b : Fin n) : ℕ :=
  (multiply p k (pCoefficients p wAC) (qCoefficients p wBC)
    (Nat.Morton.index a b * p + ((-wAB a b) % (p : ℤ)).toNat)).natAbs

/-- Nonnegativity makes signed decoding by division by two an exact natural count. -/
theorem pairCoefficient_cast {n p k : ℕ} (hp : p ≠ 0) (hn : n ≤ 2 ^ k)
    (wAB wBC wAC : Fin n → Fin n → ℤ) (a b : Fin n) :
    (pairCoefficient p k wAB wBC wAC a b : ℤ) =
      multiply p k (pCoefficients p wAC) (qCoefficients p wBC)
        (Nat.Morton.index a b * p + ((-wAB a b) % (p : ℤ)).toNat) := by
  exact Int.natAbs_of_nonneg
    (multiply_entry_bounds hp hn wBC wAC a b _ (Int.natMod_lt hp)).1

/-- Each selected coefficient counts at most the original side many middle vertices. -/
theorem pairCoefficient_le {n p k : ℕ} (hp : p ≠ 0) (hn : n ≤ 2 ^ k)
    (wAB wBC wAC : Fin n → Fin n → ℤ) (a b : Fin n) :
    pairCoefficient p k wAB wBC wAC a b ≤ n := by
  have he := pairCoefficient_cast hp hn wAB wBC wAC a b
  have hb := (multiply_entry_bounds hp hn wBC wAC a b
    (((-wAB a b) % (p : ℤ)).toNat) (Int.natMod_lt hp)).2
  omega

/-- All selected original-coordinate coefficients sum to the existing modular triangle count. -/
theorem sum_pairCoefficient {n p k : ℕ} (hp : p ≠ 0) (hn : n ≤ 2 ^ k)
    (wAB wBC wAC : Fin n → Fin n → ℤ) :
    ∑ a : Fin n, ∑ b : Fin n, pairCoefficient p k wAB wBC wAC a b =
      countZeroMod wAB wBC wAC p := by
  apply Int.natCast_inj.mp
  push_cast
  simp_rw [pairCoefficient_cast hp hn]
  exact count_eq hp hn wAB wBC wAC

/-- The selected counts in the exact original row-major order traversed by native code.
Out-of-range entries are zero, so empty input requires no arbitrary coordinate witness. -/
@[expose] def rowMajorCoefficient {n : ℕ} (p k : ℕ)
    (wAB wBC wAC : Fin n → Fin n → ℤ) (i : ℕ) : ℕ :=
  if h : i < n * n then
    let q := finProdFinEquiv.symm (⟨i, h⟩ : Fin (n * n))
    pairCoefficient p k wAB wBC wAC q.1 q.2
  else 0

/-- The real row-major coefficient bound supplies the native prefix-accumulator admission. -/
theorem rowMajorCoefficient_le {n p k i : ℕ} (hp : p ≠ 0) (hn : n ≤ 2 ^ k)
    (wAB wBC wAC : Fin n → Fin n → ℤ) :
    rowMajorCoefficient p k wAB wBC wAC i ≤ n := by
  unfold rowMajorCoefficient
  split_ifs
  · exact pairCoefficient_le hp hn wAB wBC wAC _ _
  · omega

/-- Summation in the actual native scan order preserves the existing modular count. -/
theorem sum_rowMajorCoefficient {n p k : ℕ} (hp : p ≠ 0) (hn : n ≤ 2 ^ k)
    (wAB wBC wAC : Fin n → Fin n → ℤ) :
    ∑ i ∈ Finset.range (n * n), rowMajorCoefficient p k wAB wBC wAC i =
      countZeroMod wAB wBC wAC p := by
  rw [Finset.sum_range]
  simp only [rowMajorCoefficient, Fin.isLt, dite_true]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin n × Fin n ≃ Fin (n * n))]
  rw [Fintype.sum_prod_type]
  change (∑ a : Fin n, ∑ b : Fin n, pairCoefficient p k wAB wBC wAC
    (finProdFinEquiv.symm (finProdFinEquiv (a, b))).1
    (finProdFinEquiv.symm (finProdFinEquiv (a, b))).2) = _
  simpa only [Equiv.symm_apply_apply] using sum_pairCoefficient hp hn wAB wBC wAC

end Cslib.Algorithms.ExactTriangle.CountPrime
