/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.Negacyclic
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Polynomial interpretation of negacyclic coefficient vectors

For `n ≠ 0`, the ring `Negacyclic R n` represents `R[X]/(X^n + 1)` on coefficient vectors. This
module identifies it with Mathlib's canonical quotient `AdjoinRoot (X^n + 1)` as an `R`-algebra, for
positive `n` over a nontrivial commutative ring. No primality or irreducibility assumption is
needed. The positive-dimension restriction matters: at `n = 0` the quotient is `R[X]/(2)`, while
`Negacyclic R 0` is the zero ring, a chosen zero-dimensional extension. Matrix-vector products,
such as the Module-SIS map read through `ofCoeffs_comp_moduleSISMap`, transport entrywise to the
quotient.

## Main definitions

* `negacyclicEquiv`: the `R`-algebra equivalence from `Negacyclic R n` to the polynomial quotient.

## Main results

* `negacyclicEquiv_apply`: the equivalence evaluates a coefficient vector at the residue of `X`.
* `negacyclicEquiv_mulVec`: the equivalence maps `A *ᵥ z` entrywise to the quotient ring.

## References

Original supporting representation algebra for the coefficient model in `SIS.Module`.
-/

public section

namespace Cslib.Crypto

open Polynomial Module Negacyclic
open scoped _root_.Matrix

variable {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}

/-- Coefficient vectors of positive length are the unique representatives of degree less than
`n` in `R[X]/(X^n + 1)`. -/
private noncomputable def negacyclicLinearEquiv (hn : n ≠ 0) :
    (Fin n → R) ≃ₗ[R] AdjoinRoot ((X : R[X]) ^ n + 1) :=
  ((AdjoinRoot.powerBasisAux' (by simpa using monic_X_pow_add_C (1 : R) hn)).reindex
    (finCongr (by simp))).equivFun.symm

private theorem negacyclicLinearEquiv_apply (hn : n ≠ 0) (a : Fin n → R) :
    negacyclicLinearEquiv hn a =
      ∑ i, algebraMap R _ (a i) * AdjoinRoot.root ((X : R[X]) ^ n + 1) ^ (i : ℕ) := by
  rw [negacyclicLinearEquiv, Basis.equivFun_symm_apply]
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

private theorem negacyclicLinearEquiv_mul (hn : n ≠ 0) (a b : Fin n → R) :
    negacyclicLinearEquiv hn (negacyclicMul a b) =
      negacyclicLinearEquiv hn a * negacyclicLinearEquiv hn b := by
  simp only [negacyclicLinearEquiv_apply, negacyclicMul, Matrix.mulVec, dotProduct,
    map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_right_comm (algebraMap R _ (rotMatrix a _ _)), ← Finset.sum_mul,
    negacyclic_column hn]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem negacyclicLinearEquiv_one (hn : n ≠ 0) :
    negacyclicLinearEquiv hn (1 : Negacyclic R n).coeffs = 1 := by
  let : NeZero n := ⟨hn⟩
  rw [negacyclicLinearEquiv_apply, Fintype.sum_eq_single 0 fun i hi => by
    simp [Negacyclic.coeffs_one, Fin.val_eq_zero_iff, hi]]
  simp [Negacyclic.coeffs_one]

/-- For positive `n`, `Negacyclic R n` is Mathlib's canonical quotient `R[X]/(X^n + 1)`: an
element is the polynomial with its coefficients, taken modulo `X^n + 1`. -/
noncomputable def negacyclicEquiv (hn : n ≠ 0) :
    Negacyclic R n ≃ₐ[R] AdjoinRoot ((X : R[X]) ^ n + 1) :=
  AlgEquiv.ofLinearEquiv ((coeffsLinearEquiv R).trans (negacyclicLinearEquiv hn))
    (negacyclicLinearEquiv_one hn)
    (fun a b => negacyclicLinearEquiv_mul hn a.coeffs b.coeffs)

/-- The quotient representative is the usual polynomial evaluation at the residue of `X`. -/
theorem negacyclicEquiv_apply (hn : n ≠ 0) (a : Negacyclic R n) :
    negacyclicEquiv hn a =
      ∑ i, algebraMap R _ (a.coeffs i) * AdjoinRoot.root ((X : R[X]) ^ n + 1) ^ (i : ℕ) :=
  negacyclicLinearEquiv_apply hn a.coeffs

/-- Matrix-vector products over `Negacyclic R n` map entrywise to the quotient ring. -/
theorem negacyclicEquiv_mulVec (hn : n ≠ 0) {d k : ℕ}
    (A : Matrix (Fin d) (Fin k) (Negacyclic R n)) (z : Fin k → Negacyclic R n) :
    negacyclicEquiv hn ∘ (A *ᵥ z) = A.map (negacyclicEquiv hn) *ᵥ (negacyclicEquiv hn ∘ z) :=
  funext fun i => RingHom.map_mulVec (negacyclicEquiv hn).toRingEquiv.toRingHom A z i

end Cslib.Crypto
