/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.SIS.Module
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Polynomial interpretation of negacyclic coefficient vectors

The existing `negacyclicMul` operation represents multiplication in `R[X]/(X^n + 1)`.
This module identifies its coefficient vectors with Mathlib's canonical quotient for positive
`n` over a nontrivial commutative ring. No primality or irreducibility assumption is needed.
The positive-dimension restriction matters: at `n = 0` the quotient is `R/(2)`.

## Main definitions

* `negacyclicEquiv`: the linear equivalence from coefficient vectors to the polynomial quotient.

## Main results

* `negacyclicEquiv_mul`: the equivalence carries `negacyclicMul` to quotient multiplication.
* `negacyclicEquiv_moduleSISMap`: the existing Module-SIS map is a quotient-ring matrix product.

## References

Original supporting representation algebra for the coefficient model in `SIS.Module`.
-/

public section

namespace Cslib.Crypto

open Polynomial Module

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}

/-- Coefficient vectors of positive length are the unique representatives of degree less than
`n` in `R[X]/(X^n + 1)`. The source uses its usual pointwise module structure, while
multiplication is represented by `negacyclicMul`, not pointwise multiplication. -/
noncomputable def negacyclicEquiv (hn : n ≠ 0) :
    (Fin n → R) ≃ₗ[R] AdjoinRoot ((X : R[X]) ^ n + 1) :=
  ((AdjoinRoot.powerBasisAux' (by simpa using monic_X_pow_add_C (1 : R) hn)).reindex
    (finCongr (by simp))).equivFun.symm

/-- The quotient representative is the usual polynomial evaluation at the residue of `X`. -/
theorem negacyclicEquiv_apply (hn : n ≠ 0) (a : Fin n → R) :
    negacyclicEquiv hn a =
      ∑ i, algebraMap R _ (a i) * AdjoinRoot.root ((X : R[X]) ^ n + 1) ^ (i : ℕ) := by
  rw [negacyclicEquiv, Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Basis.reindex_apply]
  change a i • (AdjoinRoot.powerBasis' _).basis _ = _
  erw [PowerBasis.basis_eq_pow, Algebra.smul_def]
  rfl

omit [Nontrivial R] in
private theorem negacyclic_root_pow :
    AdjoinRoot.root ((X : R[X]) ^ n + 1) ^ n = -1 := by
  have h := AdjoinRoot.eval₂_root ((X : R[X]) ^ n + 1)
  simpa only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one, add_eq_zero_iff_eq_neg] using h

omit [Nontrivial R] in
private theorem negacyclic_column (hn : n ≠ 0) (a : Fin n → R) (j : Fin n) :
    ∑ i, algebraMap R _ (rotMatrix a i j) *
        AdjoinRoot.root ((X : R[X]) ^ n + 1) ^ (i : ℕ) =
      (∑ i, algebraMap R _ (a i) *
        AdjoinRoot.root ((X : R[X]) ^ n + 1) ^ (i : ℕ)) *
      AdjoinRoot.root ((X : R[X]) ^ n + 1) ^ (j : ℕ) := by
  let : NeZero n := ⟨hn⟩
  rw [← (Equiv.addRight j).sum_comp, Finset.sum_mul]
  rotate_left
  · simp
  apply Finset.sum_congr rfl
  intro i _
  change algebraMap R _ (rotMatrix a (i + j) j) *
    AdjoinRoot.root ((X : R[X]) ^ n + 1) ^ (i + j).val = _
  by_cases h : n ≤ i.val + j.val
  · have hv : (i + j).val = i.val + j.val - n := by
      simp only [Fin.val_add_eq_ite, ite_eq_left h]
    have hj : ¬j.val ≤ (i + j).val := by omega
    have hi : (⟨n + (i + j).val - j.val, by omega⟩ : Fin n) = i := by
      ext
      dsimp
      omega
    simp only [rotMatrix, Matrix.of_apply, dite_eq_right hj, hi, map_neg]
    rw [mul_assoc, ← pow_add]
    have he : i.val + j.val = n + (i + j).val := by omega
    rw [he, pow_add, negacyclic_root_pow]
    ring
  · have hv : (i + j).val = i.val + j.val := by
      simp only [Fin.val_add_eq_ite, ite_eq_right h]
    have hj : j.val ≤ (i + j).val := by omega
    have hi : (⟨(i + j).val - j.val, by omega⟩ : Fin n) = i := by
      ext
      dsimp
      omega
    simp only [rotMatrix, Matrix.of_apply, dite_eq_left hj, hi]
    rw [mul_assoc, ← pow_add, hv]

/-- Negacyclic coefficient multiplication is exactly multiplication in the canonical quotient. -/
theorem negacyclicEquiv_mul (hn : n ≠ 0) (a b : Fin n → R) :
    negacyclicEquiv hn (negacyclicMul a b) =
      negacyclicEquiv hn a * negacyclicEquiv hn b := by
  simp only [negacyclicEquiv_apply, negacyclicMul, Matrix.mulVec, dotProduct,
    map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_right_comm (algebraMap R _ (rotMatrix a _ _)), ← Finset.sum_mul,
    negacyclic_column hn]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The existing Module-SIS map evaluates to a matrix-vector product over the polynomial quotient.
This identifies the coefficient model without any primality or irreducibility assumption. -/
theorem negacyclicEquiv_moduleSISMap {d k q : ℕ} [Nontrivial (ZMod q)] (hn : n ≠ 0)
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q))
    (z : Fin k → Fin n → ZMod q) (i : Fin d) :
    negacyclicEquiv hn (moduleSISMap A z i) =
      ∑ j, negacyclicEquiv hn (A i j) * negacyclicEquiv hn (z j) := by
  simp only [moduleSISMap, map_sum, negacyclicEquiv_mul]

end Cslib.Crypto
