/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Int.Radix
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.IntegerKernel
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.VertexOrientation
public import CslibFrontier.GameTheory.Bimatrix.BestResponsePolytope
public import CslibFrontier.GameTheory.Bimatrix.ShapleyOrientation
public import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Perturbed best-response polytopes, integer bases, and exact rational Nash recovery

This module supplies the quantitative and polyhedral infrastructure turning arbitrary rational
bimatrix games into nondegenerate integer-matrix Lemke–Howson instances whose nonzero completely
labelled vertices yield exact rational Nash equilibria.

Following [vonStengel2007, Section 3.6], for positive integer payoff matrices
`A B : Matrix (Fin m) (Fin n) ℤ` with entries in `[1, H]`, we perturb the right-hand sides of
the scaled best-response polytopes `P_ε = {x ≥ 0 | Bᵀ x ≤ K^n + K^(n-1-j)}` and
`Q_ε = {y ≥ 0 | A y ≤ K^m + K^(m-1-i)}` with `K = 2 ^ bitBound m n H`.

## Main definitions

* `Cslib.GameTheory.BimatrixGame.bitBound`: explicit polynomial bit bound `E` such that `K = 2 ^ E`
  makes `(P_ε, Q_ε)` nondegenerate and supports exact unperturbed Nash extraction.
* `Cslib.GameTheory.BimatrixGame.intMatP`, `Cslib.GameTheory.BimatrixGame.intMatQ`,
  `Cslib.GameTheory.BimatrixGame.pertRhsPInt`, `Cslib.GameTheory.BimatrixGame.pertRhsQInt`:
  integral constraint matrices and perturbed right-hand sides.
* `Cslib.GameTheory.BimatrixGame.IsFeasibleBasis`: pure integer Cramer feasibility predicate for
  `k`-element tight bases.
* `Cslib.GameTheory.BimatrixGame.cramerVec`, `Cslib.GameTheory.BimatrixGame.basisSignNum`:
  signed Cramer numerator vector for an integer basis system.

## Main results

* `Cslib.GameTheory.BimatrixGame.isNash_smul`: positive scaling invariance of `IsNash`.
* `Cslib.GameTheory.BimatrixGame.isNondegenerateSystem_pertP`,
  `Cslib.GameTheory.BimatrixGame.isNondegenerateSystem_pertQ`: nondegeneracy of `(P_ε, Q_ε)` over
  every ordered field (`ℚ`, `ℝ`) whenever `kernelVecBound` is below `K`.
* `Cslib.GameTheory.BimatrixGame.isFeasibleBasis_iff_ratBasisSol_le`,
  `Cslib.GameTheory.BimatrixGame.isVertex_ratBasisSol_of_isFeasibleBasis`,
  `Cslib.GameTheory.BimatrixGame.exists_isFeasibleBasis_of_isVertex`: equivalence between integer
  feasible bases and vertices of `(P_ε, Q_ε)`.
* `Cslib.GameTheory.BimatrixGame.isNash_extractNum`: any nonzero completely labelled basis pair of
  `(P_ε, Q_ε)` extracts an exact rational Nash equilibrium of `⟨A, B⟩`.

## References

* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive
  form*][vonStengel2007], Sections 3.5–3.6
-/

public section

open Finset Matrix

namespace Cslib.GameTheory.BimatrixGame

section Scaling

variable {M N : Type*} [Fintype M] [Fintype N]

/-- Positive scalar multiplication of both payoff matrices preserves `IsNash`. -/
theorem isNash_smul {D : ℝ} (hD : 0 < D) (G : BimatrixGame M N) (x : M → ℝ) (y : N → ℝ) :
    ({ A := D • G.A, B := D • G.B } : BimatrixGame M N).IsNash x y ↔ G.IsNash x y := by
  simp only [isNash_iff, isBestResponse₁_iff, isBestResponse₂_iff, isPureBestResponse₁_iff,
    isPureBestResponse₂_iff, Matrix.smul_mulVec, Matrix.vecMul_smul, Pi.smul_apply, smul_eq_mul,
    mul_le_mul_iff_right₀ hD]

end Scaling

section BitBound

/-- Explicit polynomial exponent `E` so that `2 ^ E` suffices for both nondegeneracy and exact
unperturbed Nash extraction on positive integer `m × n` games bounded by `H`. -/
@[expose] def bitBound (m n H : ℕ) : ℕ :=
  4 * (m + n) * (m + n + Nat.log 2 H + 3)

private lemma factorial_le_two_pow_sq (k : ℕ) : k.factorial ≤ 2 ^ (k ^ 2) :=
  calc k.factorial ≤ k ^ k := Nat.factorial_le_pow k
    _ ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left Nat.lt_two_pow_self.le k
    _ = 2 ^ (k ^ 2) := by rw [← pow_mul, sq]

private lemma kernelVecBound_mul_lt_two_pow_aux {a b H : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Matrix.kernelVecBound a H * (b + 1) < 2 ^ bitBound a b H := by
  set L := Nat.log 2 H + 1
  set s := a + b
  have hHL : H < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) H
  have ha_le : a ≤ s := Nat.le_add_right a b
  have hb_le : b ≤ s := Nat.le_add_left b a
  have hL_pos : 1 ≤ L := Nat.succ_pos _
  have hs_ge : 2 ≤ s := by omega
  have hfac : a.factorial ≤ 2 ^ (s ^ 2) :=
    (factorial_le_two_pow_sq a).trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left ha_le 2))
  have hb1 : b + 1 ≤ 2 ^ s :=
    (by omega : b + 1 ≤ s).trans Nat.lt_two_pow_self.le
  have hbase : a * ((a + 1) * H) ^ 2 + 1 ≤ 2 ^ (3 * s + 2 * L + 3) := by
    have hs1 : a + 1 ≤ 2 ^ (s + 1) := by
      calc a + 1 ≤ s + 1 := by omega
        _ ≤ 2 ^ (s + 1) := Nat.lt_two_pow_self.le
    have ha1 : a ≤ 2 ^ s := ha_le.trans Nat.lt_two_pow_self.le
    have hprod1 : (a + 1) * H ≤ 2 ^ (s + L + 1) := by
      calc (a + 1) * H ≤ 2 ^ (s + 1) * 2 ^ L := Nat.mul_le_mul hs1 hHL.le
        _ = 2 ^ (s + L + 1) := by rw [← pow_add]; congr 1; ring
    have hsq : ((a + 1) * H) ^ 2 ≤ 2 ^ (2 * s + 2 * L + 2) := by
      calc ((a + 1) * H) ^ 2 ≤ (2 ^ (s + L + 1)) ^ 2 := Nat.pow_le_pow_left hprod1 2
        _ = 2 ^ (2 * s + 2 * L + 2) := by rw [← pow_mul]; congr 1; ring
    calc a * ((a + 1) * H) ^ 2 + 1
        ≤ 2 ^ s * 2 ^ (2 * s + 2 * L + 2) + 1 := by
          gcongr
      _ = 2 ^ (3 * s + 2 * L + 2) + 1 := by rw [← pow_add]; congr 1; ring
      _ ≤ 2 ^ (3 * s + 2 * L + 2) + 2 ^ (3 * s + 2 * L + 2) :=
          Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2 ^ (3 * s + 2 * L + 3) := by rw [pow_succ]; ring
  have hpow : (a * ((a + 1) * H) ^ 2 + 1) ^ a ≤ 2 ^ (s * (3 * s + 2 * L + 3)) := by
    calc (a * ((a + 1) * H) ^ 2 + 1) ^ a
        ≤ (2 ^ (3 * s + 2 * L + 3)) ^ a := Nat.pow_le_pow_left hbase a
      _ = 2 ^ (a * (3 * s + 2 * L + 3)) := by rw [← pow_mul, mul_comm (3 * s + 2 * L + 3) a]
      _ ≤ 2 ^ (s * (3 * s + 2 * L + 3)) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ ha_le)
  have hexp : s ^ 2 + s * (3 * s + 2 * L + 3) + s < bitBound a b H := by
    change s ^ 2 + s * (3 * s + 2 * L + 3) + s < 4 * s * (s + (L - 1) + 3)
    have hL_eq : L - 1 + 3 = L + 2 := by omega
    rw [show s + (L - 1) + 3 = s + L + 2 by omega]
    nlinarith [hs_ge, hL_pos]
  calc Matrix.kernelVecBound a H * (b + 1)
      = a.factorial * (a * ((a + 1) * H) ^ 2 + 1) ^ a * (b + 1) := rfl
    _ ≤ 2 ^ (s ^ 2) * 2 ^ (s * (3 * s + 2 * L + 3)) * 2 ^ s :=
        Nat.mul_le_mul (Nat.mul_le_mul hfac hpow) hb1
    _ = 2 ^ (s ^ 2 + s * (3 * s + 2 * L + 3) + s) := by rw [← pow_add, ← pow_add]
    _ < 2 ^ bitBound a b H := Nat.pow_lt_pow_right (by norm_num) hexp

/-- Strict bit bound dominating `kernelVecBound m H * (n + 1)`. -/
theorem kernelVecBound_mul_lt_two_pow_bitBound {m n H : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Matrix.kernelVecBound m H * (n + 1) < 2 ^ bitBound m n H :=
  kernelVecBound_mul_lt_two_pow_aux hm hn

/-- Symmetric strict bit bound dominating `kernelVecBound n H * (m + 1)`. -/
theorem kernelVecBound_mul_lt_two_pow_bitBound_symm {m n H : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Matrix.kernelVecBound n H * (m + 1) < 2 ^ bitBound m n H := by
  have hbit : bitBound n m H = bitBound m n H := by
    simp only [bitBound, Nat.add_comm n m]
  rw [← hbit]
  exact kernelVecBound_mul_lt_two_pow_aux hn hm

private lemma cramerScale_lt_two_pow_aux {a b H : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (a.factorial * H ^ a) * (1 + a * a.factorial * H ^ (a + 1)) < 2 ^ bitBound a b H := by
  set L := Nat.log 2 H + 1
  set s := a + b
  have hHL : H < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) H
  have ha_le : a ≤ s := Nat.le_add_right a b
  have hL_pos : 1 ≤ L := Nat.succ_pos _
  have hs_ge : 2 ≤ s := by omega
  have hfac : a.factorial ≤ 2 ^ (s ^ 2) :=
    (factorial_le_two_pow_sq a).trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left ha_le 2))
  have ha_pow : a ≤ 2 ^ s := ha_le.trans Nat.lt_two_pow_self.le
  have hHa : H ^ a ≤ 2 ^ (s * L) := by
    calc H ^ a ≤ (2 ^ L) ^ a := Nat.pow_le_pow_left hHL.le a
      _ = 2 ^ (a * L) := by rw [← pow_mul, mul_comm L a]
      _ ≤ 2 ^ (s * L) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right L ha_le)
  have hHa1 : H ^ (a + 1) ≤ 2 ^ ((s + 1) * L) := by
    calc H ^ (a + 1) ≤ (2 ^ L) ^ (a + 1) := Nat.pow_le_pow_left hHL.le (a + 1)
      _ = 2 ^ ((a + 1) * L) := by rw [← pow_mul, mul_comm L (a + 1)]
      _ ≤ 2 ^ ((s + 1) * L) :=
          Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right L (by omega))
  have hleft : a.factorial * H ^ a ≤ 2 ^ (s ^ 2 + s * L) := by
    calc a.factorial * H ^ a ≤ 2 ^ (s ^ 2) * 2 ^ (s * L) := Nat.mul_le_mul hfac hHa
      _ = 2 ^ (s ^ 2 + s * L) := by rw [← pow_add]
  have hright : 1 + a * a.factorial * H ^ (a + 1) ≤ 2 ^ (s + s ^ 2 + (s + 1) * L + 1) := by
    have hm : a * a.factorial * H ^ (a + 1) ≤ 2 ^ (s + s ^ 2 + (s + 1) * L) := by
      calc a * a.factorial * H ^ (a + 1)
          ≤ 2 ^ s * 2 ^ (s ^ 2) * 2 ^ ((s + 1) * L) :=
            Nat.mul_le_mul (Nat.mul_le_mul ha_pow hfac) hHa1
        _ = 2 ^ (s + s ^ 2 + (s + 1) * L) := by rw [← pow_add, ← pow_add]
    calc 1 + a * a.factorial * H ^ (a + 1)
        ≤ 2 ^ (s + s ^ 2 + (s + 1) * L) + 2 ^ (s + s ^ 2 + (s + 1) * L) :=
          Nat.add_le_add Nat.one_le_two_pow hm
      _ = 2 ^ (s + s ^ 2 + (s + 1) * L + 1) := by rw [pow_succ]; ring
  have hexp : (s ^ 2 + s * L) + (s + s ^ 2 + (s + 1) * L + 1) < bitBound a b H := by
    change (s ^ 2 + s * L) + (s + s ^ 2 + (s + 1) * L + 1) < 4 * s * (s + (L - 1) + 3)
    rw [show s + (L - 1) + 3 = s + L + 2 by omega]
    nlinarith [hs_ge, hL_pos]
  calc (a.factorial * H ^ a) * (1 + a * a.factorial * H ^ (a + 1))
      ≤ 2 ^ (s ^ 2 + s * L) * 2 ^ (s + s ^ 2 + (s + 1) * L + 1) :=
        Nat.mul_le_mul hleft hright
    _ = 2 ^ ((s ^ 2 + s * L) + (s + s ^ 2 + (s + 1) * L + 1)) := by rw [← pow_add]
    _ < 2 ^ bitBound a b H := Nat.pow_lt_pow_right (by norm_num) hexp

/-- Strict Cramer rounding bound for player 1 (`m`) under `K = 2 ^ bitBound m n H`. -/
theorem cramerScale_lt_two_pow_bitBound {m n H : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (m.factorial * H ^ m) * (1 + m * m.factorial * H ^ (m + 1)) < 2 ^ bitBound m n H :=
  cramerScale_lt_two_pow_aux hm hn

/-- Symmetric strict Cramer rounding bound for player 2 (`n`) under `K = 2 ^ bitBound m n H`. -/
theorem cramerScale_lt_two_pow_bitBound_symm {m n H : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (n.factorial * H ^ n) * (1 + n * n.factorial * H ^ (n + 1)) < 2 ^ bitBound m n H := by
  have hbit : bitBound n m H = bitBound m n H := by
    simp only [bitBound, Nat.add_comm n m]
  rw [← hbit]
  exact cramerScale_lt_two_pow_aux hn hm

end BitBound

section Polytopes

/-- Integer constraint matrix `[-I_m; Bᵀ]` for best-response polytope `P`. -/
@[expose] def intMatP {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m ⊕ Fin n) (Fin m) ℤ :=
  Matrix.fromRows (-1) Bᵀ

/-- Integer constraint matrix `[A; -I_n]` for best-response polytope `Q`. -/
@[expose] def intMatQ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m ⊕ Fin n) (Fin n) ℤ :=
  Matrix.fromRows A (-1)

/-- Unperturbed integer right-hand side `[0; 1]` for `P`. -/
@[expose] def intRhsP (m n : ℕ) : Fin m ⊕ Fin n → ℤ :=
  Sum.elim 0 1

/-- Unperturbed integer right-hand side `[1; 0]` for `Q`. -/
@[expose] def intRhsQ (m n : ℕ) : Fin m ⊕ Fin n → ℤ :=
  Sum.elim 1 0

/-- Perturbed integer right-hand side `[0; K^n + K^(n-1-j)]` for `P_ε`. -/
@[expose] def pertRhsPInt (m n : ℕ) (K : ℤ) : Fin m ⊕ Fin n → ℤ :=
  Sum.elim 0 (fun j => K ^ n + K ^ (n - 1 - j.1))

/-- Perturbed integer right-hand side `[K^m + K^(m-1-i); 0]` for `Q_ε`. -/
@[expose] def pertRhsQInt (m n : ℕ) (K : ℤ) : Fin m ⊕ Fin n → ℤ :=
  Sum.elim (fun i => K ^ m + K ^ (m - 1 - i.1)) 0

@[simp]
theorem intMatP_inl {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℤ) (i i' : Fin m) :
    intMatP B (.inl i) i' = if i = i' then -1 else 0 := by
  simp only [intMatP, Matrix.fromRows_apply_inl, Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> simp

@[simp]
theorem intMatP_inr {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℤ) (j : Fin n) (i : Fin m) :
    intMatP B (.inr j) i = B i j := by
  simp [intMatP]

@[simp]
theorem intMatQ_inl {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (i : Fin m) (j : Fin n) :
    intMatQ A (.inl i) j = A i j := by
  simp [intMatQ]

@[simp]
theorem intMatQ_inr {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (j j' : Fin n) :
    intMatQ A (.inr j) j' = if j = j' then -1 else 0 := by
  simp only [intMatQ, Matrix.fromRows_apply_inr, Matrix.neg_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem intMatP_map_eq_matP {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℤ) :
    (intMatP B).map (Int.cast : ℤ → ℝ) =
      ({ A := A.map Int.cast, B := B.map Int.cast } : BimatrixGame (Fin m) (Fin n)).matP := by
  ext r c
  let G : BimatrixGame (Fin m) (Fin n) := { A := A.map Int.cast, B := B.map Int.cast }
  have hcol : ((intMatP B).map (Int.cast : ℤ → ℝ)) *ᵥ Pi.single c (1 : ℝ) =
      G.matP *ᵥ Pi.single c (1 : ℝ) := by
    ext r'
    cases r' with
    | inl i =>
      rw [G.matP_mulVec_inl]
      simp only [mulVec, dotProduct, Matrix.map_apply, intMatP_inl, Int.cast_ite, Int.cast_neg,
        Int.cast_one, Int.cast_zero, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, eq_comm]
      split_ifs <;> simp
    | inr j =>
      rw [G.matP_mulVec_inr]
      simp [mulVec, dotProduct, vecMul, intMatP_inr, Pi.single_apply, G]
  have hr := congrFun hcol r
  simpa only [mulVec_single, Pi.smul_apply, op_smul_eq_mul, mul_one, col_apply] using hr

theorem intMatQ_map_eq_matQ {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℤ) :
    (intMatQ A).map (Int.cast : ℤ → ℝ) =
      ({ A := A.map Int.cast, B := B.map Int.cast } : BimatrixGame (Fin m) (Fin n)).matQ := by
  ext r c
  let G : BimatrixGame (Fin m) (Fin n) := { A := A.map Int.cast, B := B.map Int.cast }
  have hcol : ((intMatQ A).map (Int.cast : ℤ → ℝ)) *ᵥ Pi.single c (1 : ℝ) =
      G.matQ *ᵥ Pi.single c (1 : ℝ) := by
    ext r'
    cases r' with
    | inl i =>
      rw [G.matQ_mulVec_inl]
      simp [mulVec, dotProduct, intMatQ_inl, Pi.single_apply, G]
    | inr j =>
      rw [G.matQ_mulVec_inr]
      simp only [mulVec, dotProduct, Matrix.map_apply, intMatQ_inr, Int.cast_ite, Int.cast_neg,
        Int.cast_one, Int.cast_zero, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, eq_comm]
      split_ifs <;> simp
  have hr := congrFun hcol r
  simpa only [mulVec_single, Pi.smul_apply, op_smul_eq_mul, mul_one, col_apply] using hr

/-- Swapping `Sum.inl` and `Sum.inr` turns `intMatQ A` into `intMatP Aᵀ`. -/
theorem intMatQ_submatrix_sumComm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (intMatQ A).submatrix (Equiv.sumComm (Fin n) (Fin m)) id = intMatP Aᵀ := by
  ext r c
  cases r <;> simp [intMatQ, intMatP]

/-- Swapping `Sum.inl` and `Sum.inr` turns `pertRhsQInt m n K` into `pertRhsPInt n m K`. -/
theorem pertRhsQInt_comp_sumComm (m n : ℕ) (K : ℤ) :
    pertRhsQInt m n K ∘ Equiv.sumComm (Fin n) (Fin m) = pertRhsPInt n m K := by
  funext r
  cases r <;> rfl

/-- Boundedness (zero recession cone) of `intMatP B` over any ordered field `K` when `1 ≤ B`. -/
theorem recession_intMatP {m n : ℕ} {B : Matrix (Fin m) (Fin n) ℤ} (hn : 0 < n)
    (hB : ∀ i j, 1 ≤ B i j)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (v : Fin m → K) (hv : (intMatP B).map Int.cast *ᵥ v ≤ 0) : v = 0 := by
  have hv_nonneg : ∀ i, 0 ≤ v i := fun i => by
    have hrow := hv (.inl i)
    simp only [mulVec, dotProduct, Matrix.map_apply, intMatP_inl, Int.cast_ite, Int.cast_neg,
      Int.cast_one, Int.cast_zero, ite_mul, neg_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, Pi.zero_apply, neg_nonpos] at hrow
    exact hrow
  have hsum0 : ∑ i : Fin m, ((B i ⟨0, hn⟩ : ℤ) : K) * v i = 0 := by
    have hrow := hv (.inr ⟨0, hn⟩)
    simp only [mulVec, dotProduct, Matrix.map_apply, intMatP_inr, Pi.zero_apply] at hrow
    have hnonneg : 0 ≤ ∑ i : Fin m, ((B i ⟨0, hn⟩ : ℤ) : K) * v i :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (by exact_mod_cast (by linarith [hB i ⟨0, hn⟩] : (0 : ℤ) ≤ B i ⟨0, hn⟩))
          (hv_nonneg i)
    exact le_antisymm hrow hnonneg
  ext i
  have hterm : ((B i ⟨0, hn⟩ : ℤ) : K) * v i = 0 := by
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      mul_nonneg (by exact_mod_cast (by linarith [hB k ⟨0, hn⟩] : (0 : ℤ) ≤ B k ⟨0, hn⟩))
        (hv_nonneg k))] at hsum0
    exact hsum0 i (Finset.mem_univ i)
  have hBpos : ((B i ⟨0, hn⟩ : ℤ) : K) ≠ 0 := by
    exact_mod_cast (by linarith [hB i ⟨0, hn⟩] : B i ⟨0, hn⟩ ≠ 0)
  exact (mul_eq_zero.1 hterm).resolve_left hBpos

/-- Boundedness (zero recession cone) of `intMatQ A` over any ordered field `K` when `1 ≤ A`. -/
theorem recession_intMatQ {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} (hm : 0 < m)
    (hA : ∀ i j, 1 ≤ A i j)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (v : Fin n → K) (hv : (intMatQ A).map Int.cast *ᵥ v ≤ 0) : v = 0 := by
  have hsub : (intMatP Aᵀ).map Int.cast *ᵥ v ≤ 0 := fun r => by
    have hrow : ((intMatP Aᵀ).map Int.cast *ᵥ v : Fin n ⊕ Fin m → K) r =
        ((intMatQ A).map Int.cast *ᵥ v : Fin m ⊕ Fin n → K) (Equiv.sumComm (Fin n) (Fin m) r) := by
      simp only [mulVec, dotProduct, Matrix.map_apply, ← intMatQ_submatrix_sumComm A,
        Matrix.submatrix_apply, id_eq]
    rw [hrow]
    exact hv _
  exact recession_intMatP hm (fun j i => hA i j) v hsub

/-- `0` is a vertex of `P_ε` with tight rows `Finset.univ.image Sum.inl` when `0 < K_B`. -/
theorem isVertex_zero_pertP {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℤ) {K_B : ℤ} (hK : 0 < K_B)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    IsVertex ((intMatP B).map Int.cast) (fun r => (pertRhsPInt m n K_B r : K)) 0 ∧
      tightRows ((intMatP B).map Int.cast) (fun r => (pertRhsPInt m n K_B r : K)) (0 : Fin m → K) =
        Finset.univ.image Sum.inl := by
  have hle : ((intMatP B).map Int.cast) *ᵥ (0 : Fin m → K) ≤
      fun r => (pertRhsPInt m n K_B r : K) := fun r => by
    rw [mulVec_zero, Pi.zero_apply]
    cases r with
    | inl i => simp [pertRhsPInt]
    | inr j =>
      simp only [pertRhsPInt, Sum.elim_inr, Int.cast_add, Int.cast_pow]
      positivity
  have htight : tightRows ((intMatP B).map Int.cast)
      (fun r => (pertRhsPInt m n K_B r : K)) (0 : Fin m → K) = Finset.univ.image Sum.inl := by
    ext r
    simp only [mem_tightRows, mulVec_zero, Pi.zero_apply, Finset.mem_image, Finset.mem_univ,
      true_and]
    cases r with
    | inl i =>
      simp [pertRhsPInt]
    | inr j =>
      simp only [pertRhsPInt, Sum.elim_inr, Int.cast_add, Int.cast_pow, reduceCtorEq, exists_false,
        iff_false]
      have hpos : (0 : K) < (K_B : K) ^ n + (K_B : K) ^ (n - 1 - j.1) := by positivity
      exact hpos.ne
  refine ⟨?_, htight⟩
  refine isVertex_iff.2 ⟨hle, fun v hv => ?_⟩
  ext i
  have hi := hv (.inl i) (htight ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i))
  simpa [intMatP, Matrix.mulVec, dotProduct, Matrix.one_apply] using hi

/-- `0` is a vertex of `Q_ε` with tight rows `Finset.univ.image Sum.inr` when `0 < K_B`. -/
theorem isVertex_zero_pertQ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) {K_B : ℤ} (hK : 0 < K_B)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    IsVertex ((intMatQ A).map Int.cast) (fun r => (pertRhsQInt m n K_B r : K)) 0 ∧
      tightRows ((intMatQ A).map Int.cast) (fun r => (pertRhsQInt m n K_B r : K)) (0 : Fin n → K) =
        Finset.univ.image Sum.inr := by
  have hle : ((intMatQ A).map Int.cast) *ᵥ (0 : Fin n → K) ≤
      fun r => (pertRhsQInt m n K_B r : K) := fun r => by
    rw [mulVec_zero, Pi.zero_apply]
    cases r with
    | inl i =>
      simp only [pertRhsQInt, Sum.elim_inl, Int.cast_add, Int.cast_pow]
      positivity
    | inr j => simp [pertRhsQInt]
  have htight : tightRows ((intMatQ A).map Int.cast)
      (fun r => (pertRhsQInt m n K_B r : K)) (0 : Fin n → K) = Finset.univ.image Sum.inr := by
    ext r
    simp only [mem_tightRows, mulVec_zero, Pi.zero_apply, Finset.mem_image, Finset.mem_univ,
      true_and]
    cases r with
    | inl i =>
      simp only [pertRhsQInt, Sum.elim_inl, Int.cast_add, Int.cast_pow, reduceCtorEq, exists_false,
        iff_false]
      have hpos : (0 : K) < (K_B : K) ^ m + (K_B : K) ^ (m - 1 - i.1) := by positivity
      exact hpos.ne
    | inr j => simp [pertRhsQInt]
  refine ⟨?_, htight⟩
  refine isVertex_iff.2 ⟨hle, fun v hv => ?_⟩
  ext j
  have hj := hv (.inr j) (htight ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j))
  simpa [intMatQ, Matrix.mulVec, dotProduct, Matrix.one_apply] using hj

/-- `(0, 0)` is a completely labelled vertex pair of `(P_ε, Q_ε)`. -/
theorem completelyLabeled_zero_zero_pert {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℤ)
    {K_B : ℤ} (hK : 0 < K_B) {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    LemkeHowson.CompletelyLabeled ((intMatP B).map Int.cast)
      (fun r => (pertRhsPInt m n K_B r : K))
      ((intMatQ A).map Int.cast) (fun r => (pertRhsQInt m n K_B r : K))
      (0 : Fin m → K) (0 : Fin n → K) := by
  rw [LemkeHowson.completelyLabeled_iff]
  intro r
  rw [(isVertex_zero_pertP B hK (K := K)).2, (isVertex_zero_pertQ A hK (K := K)).2]
  cases r with
  | inl i => exact .inl (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  | inr j => exact .inr (Finset.mem_image_of_mem _ (Finset.mem_univ j))

end Polytopes

section Nondegeneracy

/-- Every entry of `intMatP B` has absolute value at most `H` when `1 ≤ B i j ≤ H`. -/
theorem abs_intMatP_le {m n H : ℕ} {B : Matrix (Fin m) (Fin n) ℤ} (hH : 1 ≤ H)
    (hB : ∀ i j, 1 ≤ B i j ∧ B i j ≤ H) (r : Fin m ⊕ Fin n) (c : Fin m) :
    |intMatP B r c| ≤ H := by
  cases r with
  | inl i =>
    rw [intMatP_inl]
    split_ifs
    · simpa using (by exact_mod_cast hH : (1 : ℤ) ≤ H)
    · simp
  | inr j =>
    rw [intMatP_inr]
    have hj := hB c j
    rw [abs_of_pos (by linarith [hj.1])]
    exact hj.2

/-- Every entry of `intMatQ A` has absolute value at most `H` when `1 ≤ A i j ≤ H`. -/
theorem abs_intMatQ_le {m n H : ℕ} {A : Matrix (Fin m) (Fin n) ℤ} (hH : 1 ≤ H)
    (hA : ∀ i j, 1 ≤ A i j ∧ A i j ≤ H) (r : Fin m ⊕ Fin n) (c : Fin n) :
    |intMatQ A r c| ≤ H := by
  have hEq : intMatQ A r c = (intMatP Aᵀ) (Equiv.sumComm (Fin m) (Fin n) r) c := by
    have h := congrFun (congrFun (intMatQ_submatrix_sumComm A) (Equiv.sumComm (Fin m) (Fin n) r)) c
    simpa only [Matrix.submatrix_apply, id_eq, Equiv.sumComm_apply, Sum.swap_swap] using h
  rw [hEq]
  exact abs_intMatP_le hH (fun j i => hA i j) _ _

/-- **Nondegeneracy of `P_ε`.** Over any ordered field `K`, if `kernelVecBound m H * (n + 1) < K_B`,
then `intMatP B *ᵥ x ≤ pertRhsPInt m n K_B` is nondegenerate. -/
theorem isNondegenerateSystem_pertP {m n H : ℕ} {B : Matrix (Fin m) (Fin n) ℤ}
    (hH : 1 ≤ H) (hB : ∀ i j, 1 ≤ B i j ∧ B i j ≤ H) {K_B : ℤ}
    (hK : (Matrix.kernelVecBound m H * (n + 1) : ℤ) < K_B)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    IsNondegenerateSystem ((intMatP B).map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin m) K)
      (fun r => (pertRhsPInt m n K_B r : K)) := by
  rw [isNondegenerateSystem_iff]
  intro x _
  by_contra hlt
  push Not at hlt
  rw [Fintype.card_fin] at hlt
  set T := tightRows ((intMatP B).map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin m) K)
    (fun r => (pertRhsPInt m n K_B r : K)) x
  let M : Matrix (Fin m) T ℤ := fun i r => intMatP B r.1 i
  have hM_bd : ∀ (i : Fin m) (r : T), |M i r| ≤ H := fun i r => abs_intMatP_le hH hB r.1 i
  have hcard : Fintype.card (Fin m) < Fintype.card T := by simp [Fintype.card_coe, hlt]
  obtain ⟨c, hc0, hMc, hc_bd⟩ := Matrix.exists_int_mulVec_eq_zero_of_card_lt M hM_bd hcard
  rw [Fintype.card_fin] at hc_bd
  have hsumK : ∑ r : T, (c r : K) * (pertRhsPInt m n K_B r.1 : K) = 0 := by
    calc ∑ r : T, (c r : K) * (pertRhsPInt m n K_B r.1 : K)
        = ∑ r : T, (c r : K) *
            (((intMatP B).map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin m) K) *ᵥ x) r.1 := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [mem_tightRows.1 r.2]
      _ = ∑ i : Fin m, x i * ∑ r : T, (c r : K) * ((M i r : ℤ) : K) := by
          simp only [mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, M]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i : Fin m, x i * 0 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hi : ∑ r : T, M i r * c r = 0 := congrFun hMc i
          have hiK : ∑ r : T, (c r : K) * ((M i r : ℤ) : K) = 0 := by
            have := congrArg (Int.cast : ℤ → K) hi
            simpa only [Int.cast_sum, Int.cast_mul, Int.cast_zero, mul_comm] using this
          rw [hiK]
      _ = 0 := by simp
  have hsumZ : ∑ r : T, c r * pertRhsPInt m n K_B r.1 = 0 := by
    apply Int.cast_injective (α := K)
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_zero] using hsumK
  let cFull : Fin m ⊕ Fin n → ℤ := fun r => if hr : r ∈ T then c ⟨r, hr⟩ else 0
  have hsum_full : ∑ j : Fin n, cFull (.inr j) * (K_B ^ n + K_B ^ (n - 1 - j.1)) = 0 := by
    have h1 : ∑ r : T, c r * pertRhsPInt m n K_B r.1 =
        ∑ r ∈ T, cFull r * pertRhsPInt m n K_B r := by
      rw [← Finset.sum_coe_sort T (fun r => cFull r * pertRhsPInt m n K_B r)]
      refine Finset.sum_congr rfl fun r _ => by simp [cFull, r.2]
    have h2 : ∑ r ∈ T, cFull r * pertRhsPInt m n K_B r =
        ∑ r : Fin m ⊕ Fin n, cFull r * pertRhsPInt m n K_B r := by
      rw [← Finset.sum_subset (Finset.subset_univ T)]
      intro r _ hr; simp [cFull, hr]
    calc ∑ j : Fin n, cFull (.inr j) * (K_B ^ n + K_B ^ (n - 1 - j.1))
        = ∑ r : Fin m ⊕ Fin n, cFull r * pertRhsPInt m n K_B r := by
          rw [Fintype.sum_sum_type]
          have hinl0 : ∑ i : Fin m, cFull (.inl i) * pertRhsPInt m n K_B (.inl i) = 0 := by
            simp [pertRhsPInt]
          rw [hinl0, zero_add]
          rfl
      _ = ∑ r ∈ T, cFull r * pertRhsPInt m n K_B r := h2.symm
      _ = ∑ r : T, c r * pertRhsPInt m n K_B r.1 := h1.symm
      _ = 0 := hsumZ
  let a : ℕ → ℤ := fun k =>
    if hk : k < n then cFull (.inr ⟨n - 1 - k, by omega⟩)
    else if k = n then ∑ j : Fin n, cFull (.inr j)
    else 0
  have hradix_sum : ∑ k ∈ Finset.range (n + 1), a k * K_B ^ k = 0 := by
    rw [Finset.sum_range_succ]
    have ha_n : a n = ∑ j : Fin n, cFull (.inr j) := by
      dsimp only [a]
      rw [dite_eq_right (Nat.lt_irrefl n), ite_eq_left rfl]
    rw [ha_n]
    have hlow : ∑ k ∈ Finset.range n, a k * K_B ^ k =
        ∑ j : Fin n, cFull (.inr j) * K_B ^ (n - 1 - j.1) := by
      rw [← Finset.sum_coe_sort (Finset.range n) (fun k => a k * K_B ^ k)]
      let e : Fin n ≃ ↥(Finset.range n) :=
        { toFun := fun j => ⟨n - 1 - j.1, Finset.mem_range.2 (by omega)⟩
          invFun := fun k => ⟨n - 1 - k.1, by have := Finset.mem_range.1 k.2; omega⟩
          left_inv := fun j => Fin.ext (Nat.sub_sub_self (by omega))
          right_inv := fun k => Subtype.ext (Nat.sub_sub_self (by
            have := Finset.mem_range.1 k.2; omega)) }
      rw [← Fintype.sum_equiv e (fun j => cFull (.inr j) * K_B ^ (n - 1 - j.1))
        (fun k : ↥(Finset.range n) => a k.1 * K_B ^ k.1) (fun j => ?_)]
      have hlt_n : n - 1 - j.1 < n := by omega
      have he_val : (e j : ℕ) = n - 1 - j.1 := rfl
      dsimp only [a]
      rw [he_val, dite_eq_left hlt_n]
      exact congrArg (fun j' => cFull (.inr j') * K_B ^ (n - 1 - j.1))
        (Fin.ext (Nat.sub_sub_self (show j.1 ≤ n - 1 by omega))).symm
    rw [hlow]
    calc (∑ j : Fin n, cFull (.inr j) * K_B ^ (n - 1 - j.1)) +
          (∑ j : Fin n, cFull (.inr j)) * K_B ^ n
        = ∑ j : Fin n, cFull (.inr j) * (K_B ^ n + K_B ^ (n - 1 - j.1)) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := hsum_full
  have ha_bd : ∀ k < n + 1, |a k| < K_B := fun k hk => by
    have hK' : (Matrix.kernelVecBound m H : ℤ) * (n + 1 : ℤ) < K_B := by exact_mod_cast hK
    have hcFull_bd : ∀ r, |cFull r| ≤ Matrix.kernelVecBound m H := fun r => by
      by_cases hr : r ∈ T
      · simpa [cFull, hr] using hc_bd ⟨r, hr⟩
      · simp only [cFull, dite_eq_right hr, abs_zero]
        exact Int.natCast_nonneg _
    have hle1 : (Matrix.kernelVecBound m H : ℤ) ≤
        (Matrix.kernelVecBound m H : ℤ) * (n + 1 : ℤ) := by
      have h0 : (0 : ℤ) ≤ Matrix.kernelVecBound m H := Int.natCast_nonneg _
      nlinarith
    by_cases hkn : k < n
    · simp only [a, dite_eq_left hkn]
      exact (hcFull_bd _).trans_lt (hle1.trans_lt hK')
    · have hkeq : k = n := by omega
      simp only [a, dite_eq_right hkn, ite_eq_left hkeq]
      have hsum_bd : |∑ j : Fin n, cFull (.inr j)| ≤
          (n : ℤ) * Matrix.kernelVecBound m H := by
        calc |∑ j : Fin n, cFull (.inr j)|
            ≤ ∑ j : Fin n, |cFull (.inr j)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j : Fin n, (Matrix.kernelVecBound m H : ℤ) :=
              Finset.sum_le_sum fun j _ => hcFull_bd _
          _ = (n : ℤ) * Matrix.kernelVecBound m H := by simp
      have hlt_mul : (n : ℤ) * Matrix.kernelVecBound m H <
          (Matrix.kernelVecBound m H : ℤ) * (n + 1 : ℤ) := by
        have hpos : 0 < Matrix.kernelVecBound m H := by
          dsimp [Matrix.kernelVecBound]
          exact Nat.mul_pos (Nat.factorial_pos m) (Nat.pow_pos (Nat.succ_pos _))
        nlinarith
      exact (hsum_bd.trans_lt hlt_mul).trans hK'
  have ha_zero := Int.eq_zero_of_sum_mul_pow_eq_zero ha_bd hradix_sum
  have hc_inr0 : ∀ j : Fin n, cFull (.inr j) = 0 := fun j => by
    have hk := ha_zero (n - 1 - j.1) (by omega)
    simp only [a, dite_eq_left (show n - 1 - j.1 < n by omega)] at hk
    have hj_eq : (⟨n - 1 - (n - 1 - j.1), by omega⟩ : Fin n) = j :=
      Fin.ext (Nat.sub_sub_self (by omega))
    rw [hj_eq] at hk
    exact hk
  have hc_inl0 : ∀ i : Fin m, cFull (.inl i) = 0 := fun i => by
    have hi : ∑ r : T, M i r * c r = 0 := congrFun hMc i
    have hsplit : ∑ r : T, M i r * c r = ∑ r : Fin m ⊕ Fin n, intMatP B r i * cFull r := by
      have hT : ∑ r : T, M i r * c r = ∑ r ∈ T, intMatP B r i * cFull r := by
        rw [← Finset.sum_coe_sort T (fun r => intMatP B r i * cFull r)]
        refine Finset.sum_congr rfl fun r _ => by simp [cFull, M, r.2]
      rw [hT, ← Finset.sum_subset (Finset.subset_univ T)]
      intro r _ hr; simp [cFull, hr]
    rw [hsplit, Fintype.sum_sum_type] at hi
    have hinr0 : ∑ j : Fin n, intMatP B (.inr j) i * cFull (.inr j) = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hc_inr0 j, mul_zero]
    rw [hinr0, add_zero] at hi
    simpa [intMatP_inl] using hi
  apply hc0
  ext ⟨rval, hr⟩
  cases rval with
  | inl i =>
    have := hc_inl0 i
    simpa [cFull, hr] using this
  | inr j =>
    have := hc_inr0 j
    simpa [cFull, hr] using this

/-- **Nondegeneracy of `Q_ε`** derived from `isNondegenerateSystem_pertP` via row transposition. -/
theorem isNondegenerateSystem_pertQ {m n H : ℕ} {A : Matrix (Fin m) (Fin n) ℤ}
    (hH : 1 ≤ H) (hA : ∀ i j, 1 ≤ A i j ∧ A i j ≤ H) {K_B : ℤ}
    (hK : (Matrix.kernelVecBound n H * (m + 1) : ℤ) < K_B)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    IsNondegenerateSystem ((intMatQ A).map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin n) K)
      (fun r => (pertRhsQInt m n K_B r : K)) := by
  have hnd := isNondegenerateSystem_pertP (B := Aᵀ) hH (fun j i => hA i j) hK (K := K)
  rw [isNondegenerateSystem_iff] at hnd ⊢
  intro y hy
  let e := Equiv.sumComm (Fin n) (Fin m)
  have hrow : ∀ r, ((intMatP Aᵀ).map Int.cast *ᵥ y : Fin n ⊕ Fin m → K) r =
      ((intMatQ A).map Int.cast *ᵥ y : Fin m ⊕ Fin n → K) (e r) := fun r => by
    simp only [mulVec, dotProduct, Matrix.map_apply, ← intMatQ_submatrix_sumComm A,
      Matrix.submatrix_apply, id_eq, e]
  have hrhs : ∀ r, (pertRhsPInt n m K_B r : K) = (pertRhsQInt m n K_B (e r) : K) := fun r => by
    simpa [e] using congrArg (Int.cast : ℤ → K) (congrFun (pertRhsQInt_comp_sumComm m n K_B) r).symm
  have hy' : (intMatP Aᵀ).map Int.cast *ᵥ y ≤ fun r => (pertRhsPInt n m K_B r : K) := fun r => by
    dsimp only
    rw [hrow r, hrhs r]
    exact hy (e r)
  have hcard_eq : (tightRows ((intMatQ A).map Int.cast : Matrix (Fin m ⊕ Fin n) (Fin n) K)
      (fun r => (pertRhsQInt m n K_B r : K)) y).card =
      (tightRows ((intMatP Aᵀ).map Int.cast : Matrix (Fin n ⊕ Fin m) (Fin n) K)
        (fun r => (pertRhsPInt n m K_B r : K)) y).card := by
    refine Finset.card_bij (fun r _ => e.symm r) ?_ ?_ ?_
    · intro r hr
      rw [mem_tightRows] at hr ⊢
      have he : e (e.symm r) = r := e.apply_symm_apply r
      rw [hrow, hrhs, he]
      exact hr
    · intro r₁ _ r₂ _ h
      exact e.symm.injective h
    · intro r hr
      refine ⟨e r, ?_, e.symm_apply_apply r⟩
      rw [mem_tightRows] at hr ⊢
      rw [← hrow r, ← hrhs r]
      exact hr
  rw [hcard_eq]
  exact hnd y hy'

end Nondegeneracy

section BasisVertex

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [LinearOrder κ]

/-- Square integer submatrix indexed by an `m`-element tight basis `T ⊆ κ`. -/
@[expose] def basisMat {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (T : Finset κ) (hT : T.card = k) :
    Matrix (Fin k) (Fin k) ℤ :=
  M_int.submatrix (fun i => (T.orderIsoOfFin hT i : κ)) id

/-- Cramer numerator vector `M.cramer (b|_T)` in `ℤ^k`. -/
@[expose] def cramerVec {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (b_int : κ → ℤ)
    (T : Finset κ) (hT : T.card = k) : Fin k → ℤ :=
  (basisMat M_int T hT).cramer (fun i => b_int (T.orderIsoOfFin hT i : κ))

/-- Sign-adjusted integer numerator `det(M).sign • cramerVec`. -/
@[expose] def basisSignNum {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (b_int : κ → ℤ)
    (T : Finset κ) (hT : T.card = k) : Fin k → ℤ :=
  fun i => (basisMat M_int T hT).det.sign * cramerVec M_int b_int T hT i

/-- Positive (when nonsingular) integer denominator `|det(M)|`. -/
@[expose] def basisAbsDet {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (T : Finset κ) (hT : T.card = k) :
    ℤ :=
  |(basisMat M_int T hT).det|

/-- Exact rational solution `(det M)⁻¹ • cramerVec` to the basis equations
`(M_int|_T) *ᵥ x = b|_T`. -/
@[expose] noncomputable def ratBasisSol {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (b_int : κ → ℤ)
    (T : Finset κ) (hT : T.card = k) : Fin k → ℚ :=
  fun i => (cramerVec M_int b_int T hT i : ℚ) / ((basisMat M_int T hT).det : ℚ)

/-- Pure integer feasibility and nonsingularity condition for basis `T` of `(M_int, b_int)`. -/
@[expose] def IsFeasibleBasis {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (b_int : κ → ℤ)
    (T : Finset κ) (hT : T.card = k) : Prop :=
  let M := basisMat M_int T hT
  M.det ≠ 0 ∧ ∀ r : κ, M.det.sign * ((M_int r) ⬝ᵥ cramerVec M_int b_int T hT) ≤ |M.det| * b_int r

omit [Fintype κ] [DecidableEq κ] in
theorem basisSignNum_div_basisAbsDet {k : ℕ} (M_int : Matrix κ (Fin k) ℤ) (b_int : κ → ℤ)
    (T : Finset κ) (hT : T.card = k) (hdet : (basisMat M_int T hT).det ≠ 0) (i : Fin k) :
    (basisSignNum M_int b_int T hT i : ℚ) / (basisAbsDet M_int T hT : ℚ) =
      ratBasisSol M_int b_int T hT i := by
  set D := (basisMat M_int T hT).det
  have hD_cast : (D : ℚ) ≠ 0 := Int.cast_ne_zero.2 hdet
  have hS_ne : D.sign ≠ 0 := by
    rcases lt_trichotomy D 0 with h | h | h
    · simp [Int.sign_eq_neg_one_of_neg h]
    · exact absurd h hdet
    · simp [Int.sign_eq_one_of_pos h]
  have hS_cast : (D.sign : ℚ) ≠ 0 := Int.cast_ne_zero.2 hS_ne
  have hmul : (D.sign * D : ℤ) = |D| := (Int.sign_mul_self D).trans (Int.natCast_natAbs D)
  have hmulQ : (D.sign : ℚ) * (D : ℚ) = ((|D| : ℤ) : ℚ) := by
    simpa only [Int.cast_mul] using congrArg (Int.cast : ℤ → ℚ) hmul
  dsimp only [basisSignNum, basisAbsDet, ratBasisSol]
  rw [← hmulQ, Int.cast_mul]
  exact mul_div_mul_left _ _ hS_cast

omit [Fintype κ] [DecidableEq κ] in
theorem ratBasisSol_tight {k : ℕ} {M_int : Matrix κ (Fin k) ℤ} {b_int : κ → ℤ}
    {T : Finset κ} {hT : T.card = k} (hdet : (basisMat M_int T hT).det ≠ 0)
    {r : κ} (hr : r ∈ T)
    {K : Type*} [Field K] [CharZero K] :
    ((M_int.map Int.cast : Matrix κ (Fin k) K) *ᵥ fun i => (ratBasisSol M_int b_int T hT i : K)) r =
      (b_int r : K) := by
  let M := basisMat M_int T hT
  let ord := (T.orderIsoOfFin hT).toEquiv
  let i₀ : Fin k := ord.symm ⟨r, hr⟩
  have hi₀ : (T.orderIsoOfFin hT i₀ : κ) = r :=
    congrArg Subtype.val (ord.apply_symm_apply ⟨r, hr⟩)
  have hrow : ∀ j : Fin k, M_int r j = M i₀ j := fun j => by
    change M_int r j = M_int (T.orderIsoOfFin hT i₀ : κ) j
    rw [hi₀]
  have hMc : M *ᵥ cramerVec M_int b_int T hT = M.det • fun i => b_int (T.orderIsoOfFin hT i : κ) :=
    Matrix.mulVec_cramer M _
  have hi_val : (M *ᵥ cramerVec M_int b_int T hT) i₀ = M.det * b_int r := by
    have hi_eq := congrFun hMc i₀
    dsimp only [Pi.smul_apply, smul_eq_mul] at hi_eq
    rwa [hi₀] at hi_eq
  have hi_valQ : (∑ j : Fin k, (M i₀ j : ℚ) * (cramerVec M_int b_int T hT j : ℚ)) =
      (M.det : ℚ) * (b_int r : ℚ) := by
    have hZ : ∑ j : Fin k, M i₀ j * cramerVec M_int b_int T hT j = M.det * b_int r := hi_val
    have := congrArg (Int.cast : ℤ → ℚ) hZ
    simpa only [Int.cast_sum, Int.cast_mul] using this
  have hrat : (∑ j : Fin k, (M i₀ j : ℚ) * ratBasisSol M_int b_int T hT j) = (b_int r : ℚ) := by
    have hM_ne : (M.det : ℚ) ≠ 0 := Int.cast_ne_zero.2 hdet
    have hsum : ∑ j : Fin k, (M i₀ j : ℚ) * ratBasisSol M_int b_int T hT j =
        (M.det : ℚ)⁻¹ * ∑ j : Fin k, (M i₀ j : ℚ) * (cramerVec M_int b_int T hT j : ℚ) := by
      simp only [ratBasisSol, div_eq_inv_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hsum, hi_valQ, inv_mul_cancel_left₀ hM_ne]
  have hK := congrArg (Rat.cast : ℚ → K) hrat
  rw [Rat.cast_sum] at hK
  simpa only [mulVec, dotProduct, Matrix.map_apply, hrow, Rat.cast_mul, Rat.cast_intCast] using hK

omit [Fintype κ] [DecidableEq κ] in
theorem isFeasibleBasis_iff_ratBasisSol_le {k : ℕ} {M_int : Matrix κ (Fin k) ℤ} {b_int : κ → ℤ}
    {T : Finset κ} {hT : T.card = k} (hdet : (basisMat M_int T hT).det ≠ 0) :
    IsFeasibleBasis M_int b_int T hT ↔
      (M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ ratBasisSol M_int b_int T hT ≤
        fun r => (b_int r : ℚ) := by
  set M := basisMat M_int T hT
  have hD_pos : (0 : ℚ) < ((|M.det| : ℤ) : ℚ) := Int.cast_pos.2 (abs_pos.2 hdet)
  have hmul : (M.det.sign : ℚ) * (M.det : ℚ) = ((|M.det| : ℤ) : ℚ) := by
    have hZ : (M.det.sign * M.det : ℤ) = |M.det| :=
      (Int.sign_mul_self M.det).trans (Int.natCast_natAbs M.det)
    simpa only [Int.cast_mul] using congrArg (Int.cast : ℤ → ℚ) hZ
  have hM : (M.det : ℚ) ≠ 0 := Int.cast_ne_zero.2 hdet
  constructor
  · intro hfb r
    have hrZ : (M.det.sign * (M_int r ⬝ᵥ cramerVec M_int b_int T hT) : ℤ) ≤ |M.det| * b_int r :=
      hfb.2 r
    have hrQ : (M.det.sign : ℚ) *
          ∑ j : Fin k, (M_int r j : ℚ) * (cramerVec M_int b_int T hT j : ℚ) ≤
        ((|M.det| : ℤ) : ℚ) * (b_int r : ℚ) := by
      simpa only [Int.cast_mul, Int.cast_sum, dotProduct] using (Int.cast_le (R := ℚ)).2 hrZ
    apply le_of_mul_le_mul_left _ hD_pos
    calc ((|M.det| : ℤ) : ℚ) *
            ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ ratBasisSol M_int b_int T hT) r
        = (M.det.sign : ℚ) * (M.det : ℚ) *
            ∑ j : Fin k, (M_int r j : ℚ) * ((cramerVec M_int b_int T hT j : ℚ) / (M.det : ℚ)) := by
          rw [hmul]; rfl
      _ = (M.det.sign : ℚ) * ∑ j : Fin k, (M_int r j : ℚ) * (cramerVec M_int b_int T hT j : ℚ) := by
          rw [mul_assoc, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_left_comm, mul_div_cancel₀ _ hM]
      _ ≤ ((|M.det| : ℤ) : ℚ) * (b_int r : ℚ) := hrQ
  · intro h
    refine ⟨hdet, fun r => ?_⟩
    have hrQ := mul_le_mul_of_nonneg_left (h r) hD_pos.le
    dsimp only at hrQ
    have hlhs : ((|M.det| : ℤ) : ℚ) * ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ
        ratBasisSol M_int b_int T hT) r =
        (M.det.sign : ℚ) * ∑ j : Fin k, (M_int r j : ℚ) * (cramerVec M_int b_int T hT j : ℚ) := by
      change ((|M.det| : ℤ) : ℚ) * ∑ j : Fin k, (M_int r j : ℚ) *
          ((cramerVec M_int b_int T hT j : ℚ) / (M.det : ℚ)) = _
      rw [← hmul, mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, mul_div_cancel₀ _ hM]
    rw [hlhs] at hrQ
    have hrZ : (M.det.sign * (M_int r ⬝ᵥ cramerVec M_int b_int T hT) : ℤ) ≤ |M.det| * b_int r := by
      rw [← Int.cast_le (R := ℚ)]
      simpa only [dotProduct, Int.cast_mul, Int.cast_sum] using hrQ
    exact hrZ

omit [DecidableEq κ] in
theorem isVertex_ratBasisSol_of_isFeasibleBasis {k : ℕ} {M_int : Matrix κ (Fin k) ℤ}
    {b_int : κ → ℤ} {T : Finset κ} {hT : T.card = k}
    (hfb : IsFeasibleBasis M_int b_int T hT)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    IsVertex (M_int.map Int.cast : Matrix κ (Fin k) K) (fun r => (b_int r : K))
        (fun i => (ratBasisSol M_int b_int T hT i : K)) ∧
      T ⊆ tightRows (M_int.map Int.cast : Matrix κ (Fin k) K) (fun r => (b_int r : K))
        (fun i => (ratBasisSol M_int b_int T hT i : K)) := by
  have hdet := hfb.1
  have hleQ := (isFeasibleBasis_iff_ratBasisSol_le hdet).1 hfb
  have hleK : (M_int.map Int.cast : Matrix κ (Fin k) K) *ᵥ
      (fun i => (ratBasisSol M_int b_int T hT i : K)) ≤ fun r => (b_int r : K) := fun r => by
    have hK := (Rat.cast_le (K := K)).2 (hleQ r)
    simpa only [mulVec, dotProduct, Matrix.map_apply, Rat.cast_sum, Rat.cast_mul,
      Rat.cast_intCast] using hK
  have hsub : T ⊆ tightRows (M_int.map Int.cast : Matrix κ (Fin k) K) (fun r => (b_int r : K))
      (fun i => (ratBasisSol M_int b_int T hT i : K)) := fun r hr => by
    rw [mem_tightRows]
    exact ratBasisSol_tight hdet hr
  have hdetK : ((M_int.map Int.cast : Matrix κ (Fin k) K).submatrix
      (fun i => ((T.orderIsoOfFin hT).toEquiv i : κ)) id).det ≠ 0 := by
    have hmat : (M_int.map Int.cast : Matrix κ (Fin k) K).submatrix
          (fun i => ((T.orderIsoOfFin hT).toEquiv i : κ)) id =
        (basisMat M_int T hT).map Int.cast := by
      ext i j; rfl
    rw [hmat, ← Int.cast_det]
    exact Int.cast_ne_zero.2 hdet
  exact ⟨isVertex_of_det_submatrix_ne_zero hleK hsub (T.orderIsoOfFin hT).toEquiv hdetK, hsub⟩

omit [DecidableEq κ] in
theorem tightRows_ratBasisSol_eq {k : ℕ} {M_int : Matrix κ (Fin k) ℤ} {b_int : κ → ℤ}
    {T : Finset κ} {hT : T.card = k} (hfb : IsFeasibleBasis M_int b_int T hT)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hnd : IsNondegenerateSystem (M_int.map Int.cast : Matrix κ (Fin k) K)
      (fun r => (b_int r : K))) :
    tightRows (M_int.map Int.cast : Matrix κ (Fin k) K) (fun r => (b_int r : K))
      (fun i => (ratBasisSol M_int b_int T hT i : K)) = T := by
  obtain ⟨hvx, hsub⟩ := isVertex_ratBasisSol_of_isFeasibleBasis hfb (K := K)
  have hcard : (tightRows (M_int.map Int.cast : Matrix κ (Fin k) K) (fun r => (b_int r : K))
      (fun i => (ratBasisSol M_int b_int T hT i : K))).card = k := by
    simpa only [Fintype.card_fin] using hvx.card_tightRows hnd
  exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hT])).symm

omit [DecidableEq κ] in
theorem exists_isFeasibleBasis_of_isVertex {k : ℕ} {M_int : Matrix κ (Fin k) ℤ} {b_int : κ → ℤ}
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (hnd : IsNondegenerateSystem (M_int.map Int.cast : Matrix κ (Fin k) K)
      (fun r => (b_int r : K)))
    {x : Fin k → K} (hx : IsVertex (M_int.map Int.cast : Matrix κ (Fin k) K)
      (fun r => (b_int r : K)) x) :
    let T := tightRows (M_int.map Int.cast : Matrix κ (Fin k) K) (fun r => (b_int r : K)) x
    ∃ hT : T.card = k,
      IsFeasibleBasis M_int b_int T hT ∧
        x = fun i => (ratBasisSol M_int b_int T hT i : K) := by
  intro T
  have hT : T.card = k := by simpa only [Fintype.card_fin] using hx.card_tightRows hnd
  have hdetK := hx.det_submatrix_ne_zero (T.orderIsoOfFin hT).toEquiv
  have hmat : (M_int.map Int.cast : Matrix κ (Fin k) K).submatrix
      (fun i => ((T.orderIsoOfFin hT).toEquiv i : κ)) id = (basisMat M_int T hT).map Int.cast := by
    ext i j; rfl
  have hdetZ : (basisMat M_int T hT).det ≠ 0 := by
    intro h0
    rw [hmat, ← Int.cast_det, h0, Int.cast_zero] at hdetK
    exact hdetK rfl
  have hxeq : x = fun i => (ratBasisSol M_int b_int T hT i : K) := by
    apply Matrix.mulVec_injective_of_det_ne_zero hdetK
    ext i
    rw [hmat]
    change ((M_int.map Int.cast : Matrix κ (Fin k) K) *ᵥ x) (T.orderIsoOfFin hT i : κ) =
      ((M_int.map Int.cast : Matrix κ (Fin k) K) *ᵥ
        fun j => (ratBasisSol M_int b_int T hT j : K)) (T.orderIsoOfFin hT i : κ)
    rw [mem_tightRows.1 (T.orderIsoOfFin hT i).2, ratBasisSol_tight hdetZ (T.orderIsoOfFin hT i).2]
  have hleQ : (M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ ratBasisSol M_int b_int T hT ≤
      fun r => (b_int r : ℚ) := fun r => by
    have hr := hx.mulVec_le r
    rw [hxeq] at hr
    rw [← Rat.cast_le (K := K)]
    simpa only [mulVec, dotProduct, Matrix.map_apply, Rat.cast_sum, Rat.cast_mul,
      Rat.cast_intCast] using hr
  exact ⟨hT, (isFeasibleBasis_iff_ratBasisSol_le hdetZ).2 hleQ, hxeq⟩

omit [Fintype κ] [DecidableEq κ] in
theorem abs_det_basisMat_le {k H : ℕ} {M_int : Matrix κ (Fin k) ℤ}
    (hM : ∀ r c, |M_int r c| ≤ H) (T : Finset κ) (hT : T.card = k) :
    |(basisMat M_int T hT).det| ≤ (k.factorial * H ^ k : ℕ) := by
  have hmat : ∀ r c, |basisMat M_int T hT r c| ≤ (H : ℤ) := fun i j => hM _ j
  simpa [nsmul_eq_mul] using Matrix.det_le (abv := AbsoluteValue.abs) hmat

omit [Fintype κ] [DecidableEq κ] in
theorem abs_cramerVec_le {k H : ℕ} {M_int : Matrix κ (Fin k) ℤ} {b_int : κ → ℤ}
    (hM : ∀ r c, |M_int r c| ≤ H) (hb : ∀ r, |b_int r| ≤ H) (T : Finset κ) (hT : T.card = k)
    (i : Fin k) :
    |cramerVec M_int b_int T hT i| ≤ (k.factorial * H ^ k : ℕ) := by
  rw [cramerVec, Matrix.cramer_apply]
  have hcol : ∀ r c,
      |((basisMat M_int T hT).updateCol i fun j => b_int (T.orderIsoOfFin hT j : κ)) r c| ≤
        (H : ℤ) := by
    intro r c
    by_cases hc : c = i
    · subst hc; simp [Matrix.updateCol_self, hb]
    · simp [Matrix.updateCol_ne hc, hM, basisMat]
  simpa [nsmul_eq_mul] using Matrix.det_le (abv := AbsoluteValue.abs) hcol

omit [Fintype κ] [DecidableEq κ] in
/-- Core Cramer rounding theorem: if the perturbed rhs `b_pert` satisfies
`0 ≤ b_pert - K_B^p * b_unpert ≤ K_B^(p-1)` (`p ≥ 1`) with
`K_B > (k! * H^k) * (1 + k * k! * H^(k+1))`,
then any feasible basis `T` for `(M_int, b_pert)` gives an **exact** feasible solution
`basisSignNum M_int b_unpert T hT` for the unperturbed integer system `(M_int, b_unpert)` with
all rows in `T` still tight. -/
theorem unperturbed_feasible_of_pert {k H p : ℕ} {M_int : Matrix κ (Fin k) ℤ}
    {b_pert b_unpert : κ → ℤ} {T : Finset κ} {hT : T.card = k} {K_B : ℤ}
    (hk : 0 < k) (hH : 1 ≤ H) (hp : 1 ≤ p)
    (hM : ∀ r c, |M_int r c| ≤ H)
    (hb_pert_diff : ∀ r, 0 ≤ b_pert r - K_B ^ p * b_unpert r ∧
      b_pert r - K_B ^ p * b_unpert r ≤ K_B ^ (p - 1))
    (hK : ((k.factorial * H ^ k) * (1 + k * k.factorial * H ^ (k + 1)) : ℤ) < K_B)
    (hfb : IsFeasibleBasis M_int b_pert T hT) :
    (basisMat M_int T hT).det ≠ 0 ∧
      (∀ r ∈ T, M_int r ⬝ᵥ basisSignNum M_int b_unpert T hT =
        basisAbsDet M_int T hT * b_unpert r) ∧
      (∀ r : κ, M_int r ⬝ᵥ basisSignNum M_int b_unpert T hT ≤
        basisAbsDet M_int T hT * b_unpert r) := by
  have hdet := hfb.1
  have hK_pos : 0 < K_B := by
    have h0 : (0 : ℤ) ≤ (k.factorial * H ^ k) * (1 + k * k.factorial * H ^ (k + 1)) := by positivity
    exact lt_of_le_of_lt h0 hK
  have hKp_pos : (0 : ℚ) < (K_B : ℚ) ^ p := by exact_mod_cast pow_pos hK_pos p
  set M := basisMat M_int T hT
  set u : Fin k → ℚ := ((K_B : ℚ) ^ p)⁻¹ • ratBasisSol M_int b_pert T hT
  set v : Fin k → ℚ := ratBasisSol M_int b_unpert T hT
  have hu_le : ∀ r : κ, ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ u) r ≤
      (b_unpert r : ℚ) + (K_B : ℚ)⁻¹ := fun r => by
    have hle := (isFeasibleBasis_iff_ratBasisSol_le hdet).1 hfb r
    have hmul : ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ u) r ≤
        (b_pert r : ℚ) / (K_B : ℚ) ^ p := by
      rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right hle hKp_pos.le
    have hbd := (hb_pert_diff r).2
    have hbdQ : (b_pert r : ℚ) ≤ (K_B : ℚ) ^ p * (b_unpert r : ℚ) + (K_B : ℚ) ^ (p - 1) := by
      have : (b_pert r : ℚ) - (K_B : ℚ) ^ p * (b_unpert r : ℚ) ≤ (K_B : ℚ) ^ (p - 1) := by
        exact_mod_cast hbd
      linarith
    have hdiv : ((K_B : ℚ) ^ p * (b_unpert r : ℚ) + (K_B : ℚ) ^ (p - 1)) / (K_B : ℚ) ^ p =
        (b_unpert r : ℚ) + (K_B : ℚ)⁻¹ := by
      have hK_ne : (K_B : ℚ) ≠ 0 := Int.cast_ne_zero.2 hK_pos.ne'
      have hp_eq : (K_B : ℚ) ^ p = (K_B : ℚ) * (K_B : ℚ) ^ (p - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hp]
      rw [hp_eq]
      field_simp
    exact hmul.trans ((div_le_div_of_nonneg_right hbdQ hKp_pos.le).trans_eq hdiv)
  let δ : Fin k → ℚ := fun i =>
    ((M.map Int.cast : Matrix (Fin k) (Fin k) ℚ) *ᵥ (u - v)) i
  have hδ_bd : ∀ i : Fin k, |δ i| ≤ (K_B : ℚ)⁻¹ := fun i => by
    have hri := (T.orderIsoOfFin hT i).2
    have hu_tight : ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ u) (T.orderIsoOfFin hT i : κ) =
        (b_pert (T.orderIsoOfFin hT i : κ) : ℚ) / (K_B : ℚ) ^ p := by
      have hqt := ratBasisSol_tight (b_int := b_pert) hdet hri (K := ℚ)
      simp only [Rat.cast_id] at hqt
      rw [mulVec_smul, Pi.smul_apply, smul_eq_mul, inv_mul_eq_div, hqt]
    have hv_tight : ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ v) (T.orderIsoOfFin hT i : κ) =
        (b_unpert (T.orderIsoOfFin hT i : κ) : ℚ) := by
      have hqt := ratBasisSol_tight (b_int := b_unpert) hdet hri (K := ℚ)
      simpa only [Rat.cast_id] using hqt
    have hδ_eq : δ i = (b_pert (T.orderIsoOfFin hT i : κ) : ℚ) / (K_B : ℚ) ^ p -
        (b_unpert (T.orderIsoOfFin hT i : κ) : ℚ) := by
      dsimp only [δ]
      rw [mulVec_sub, Pi.sub_apply]
      change ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ u) (T.orderIsoOfFin hT i : κ) -
          ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ v) (T.orderIsoOfFin hT i : κ) = _
      rw [hu_tight, hv_tight]
    have hdiff := hb_pert_diff (T.orderIsoOfFin hT i : κ)
    have hK_ne : (K_B : ℚ) ≠ 0 := Int.cast_ne_zero.2 hK_pos.ne'
    have h0 : 0 ≤ δ i := by
      rw [hδ_eq, sub_nonneg, le_div_iff₀ hKp_pos]
      have : (K_B : ℚ) ^ p * (b_unpert (T.orderIsoOfFin hT i : κ) : ℚ) ≤
          (b_pert (T.orderIsoOfFin hT i : κ) : ℚ) := by
        exact_mod_cast (by linarith [hdiff.1] :
          K_B ^ p * b_unpert (T.orderIsoOfFin hT i : κ) ≤ b_pert (T.orderIsoOfFin hT i : κ))
      linarith
    have h1 : δ i ≤ (K_B : ℚ)⁻¹ := by
      rw [hδ_eq, sub_le_iff_le_add']
      have hdiv : ((K_B : ℚ) ^ p * (b_unpert (T.orderIsoOfFin hT i : κ) : ℚ) +
            (K_B : ℚ) ^ (p - 1)) / (K_B : ℚ) ^ p =
          (b_unpert (T.orderIsoOfFin hT i : κ) : ℚ) + (K_B : ℚ)⁻¹ := by
        have hp_eq : (K_B : ℚ) ^ p = (K_B : ℚ) * (K_B : ℚ) ^ (p - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hp]
        rw [hp_eq]
        field_simp
      have hbdQ : (b_pert (T.orderIsoOfFin hT i : κ) : ℚ) ≤
          (K_B : ℚ) ^ p * (b_unpert (T.orderIsoOfFin hT i : κ) : ℚ) + (K_B : ℚ) ^ (p - 1) := by
        exact_mod_cast (by linarith [hdiff.2] :
          b_pert (T.orderIsoOfFin hT i : κ) ≤
            K_B ^ p * b_unpert (T.orderIsoOfFin hT i : κ) + K_B ^ (p - 1))
      exact (div_le_div_of_nonneg_right hbdQ hKp_pos.le).trans_eq hdiv
    rw [abs_of_nonneg h0]
    exact h1
  have hMc_eq : (M.det : ℚ) • (u - v) = (M.map Int.cast : Matrix (Fin k) (Fin k) ℚ).cramer δ := by
    have hdetQ : ((M.map Int.cast : Matrix (Fin k) (Fin k) ℚ).det) ≠ 0 := by
      rw [← Int.cast_det]
      exact Int.cast_ne_zero.2 hdet
    apply Matrix.mulVec_injective_of_det_ne_zero hdetQ
    rw [Matrix.mulVec_cramer, ← Int.cast_det, mulVec_smul]
  have hdiff_bd : ∀ j : Fin k, |u j - v j| ≤ ((k.factorial * H ^ k : ℕ) : ℚ) / (K_B : ℚ) := by
    intro j
    have hj_eq := congrFun hMc_eq j
    have hj_cramer : (M.det : ℚ) * (u j - v j) =
        ((M.map Int.cast : Matrix (Fin k) (Fin k) ℚ).updateCol j δ).det := by
      simpa only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Matrix.cramer_apply] using hj_eq
    have hK_mul : (K_B : ℚ) * (M.det : ℚ) * (u j - v j) =
        ((M.map Int.cast : Matrix (Fin k) (Fin k) ℚ).updateCol j ((K_B : ℚ) • δ)).det := by
      rw [mul_assoc, hj_cramer, ← Matrix.det_updateCol_smul]
    have hK_abs : |((M.map Int.cast : Matrix (Fin k) (Fin k) ℚ).updateCol j ((K_B : ℚ) • δ)).det| ≤
        ((k.factorial * H ^ k : ℕ) : ℚ) := by
      have hcol : ∀ r c,
          |((M.map Int.cast : Matrix (Fin k) (Fin k) ℚ).updateCol j ((K_B : ℚ) • δ)) r c| ≤
            (H : ℚ) := by
        intro r c
        by_cases hc : c = j
        · subst hc
          simp only [Matrix.updateCol_self, Pi.smul_apply, smul_eq_mul, abs_mul,
            abs_of_pos (by exact_mod_cast hK_pos : (0 : ℚ) < K_B)]
          calc (K_B : ℚ) * |δ r| ≤ (K_B : ℚ) * (K_B : ℚ)⁻¹ :=
                mul_le_mul_of_nonneg_left (hδ_bd r) (by exact_mod_cast hK_pos.le)
            _ = 1 := mul_inv_cancel₀ (Int.cast_ne_zero.2 hK_pos.ne')
            _ ≤ (H : ℚ) := by exact_mod_cast hH
        · simp only [Matrix.updateCol_ne hc, Matrix.map_apply]
          exact_mod_cast hM _ c
      simpa [nsmul_eq_mul] using Matrix.det_le (abv := AbsoluteValue.abs) hcol
    rw [← hK_mul, abs_mul, abs_mul, abs_of_pos (by exact_mod_cast hK_pos : (0 : ℚ) < K_B)] at hK_abs
    have hD1 : (1 : ℚ) ≤ |((M.det : ℚ))| := by
      exact_mod_cast Int.one_le_abs hdet
    have hKb_le : (K_B : ℚ) * |u j - v j| ≤ ((k.factorial * H ^ k : ℕ) : ℚ) := by
      have hK_nonneg : (0 : ℚ) ≤ K_B := by exact_mod_cast hK_pos.le
      calc (K_B : ℚ) * |u j - v j|
          = (K_B : ℚ) * 1 * |u j - v j| := by ring
        _ ≤ (K_B : ℚ) * |((M.det : ℚ))| * |u j - v j| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD1 hK_nonneg) (abs_nonneg _)
        _ ≤ ((k.factorial * H ^ k : ℕ) : ℚ) := hK_abs
    rwa [le_div_iff₀ (by exact_mod_cast hK_pos : (0 : ℚ) < K_B), mul_comm]
  refine ⟨hdet, ?_, ?_⟩
  · intro r hr
    apply Int.cast_injective (α := ℚ)
    have htight := ratBasisSol_tight (b_int := b_unpert) hdet hr (K := ℚ)
    have hD_pos : (0 : ℚ) < basisAbsDet M_int T hT := by
      exact_mod_cast abs_pos.2 hdet
    have hdot : ∑ j : Fin k, (M_int r j : ℚ) * (basisSignNum M_int b_unpert T hT j : ℚ) =
        (basisAbsDet M_int T hT : ℚ) *
          ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ v) r := by
      rw [mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hvj := basisSignNum_div_basisAbsDet M_int b_unpert T hT hdet j
      dsimp only [v]
      change (M_int r j : ℚ) * (basisSignNum M_int b_unpert T hT j : ℚ) =
        (basisAbsDet M_int T hT : ℚ) * ((M_int r j : ℚ) * ratBasisSol M_int b_unpert T hT j)
      rw [← hvj]
      field_simp [hD_pos.ne']
    simp only [Rat.cast_id] at htight
    dsimp only [v] at hdot
    rw [htight] at hdot
    simpa only [dotProduct, Int.cast_sum, Int.cast_mul] using hdot
  · intro r
    have hrow_diff : |((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ v) r -
        ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ u) r| ≤
        (k : ℚ) * (H : ℚ) * (((k.factorial * H ^ k : ℕ) : ℚ) / (K_B : ℚ)) := by
      rw [← Pi.sub_apply, ← mulVec_sub, mulVec, dotProduct]
      calc |∑ j : Fin k, (M_int r j : ℚ) * (v j - u j)|
          ≤ ∑ j : Fin k, |(M_int r j : ℚ) * (v j - u j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin k, (H : ℚ) * (((k.factorial * H ^ k : ℕ) : ℚ) / (K_B : ℚ)) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul, abs_sub_comm]
            exact mul_le_mul (by exact_mod_cast hM r j) (hdiff_bd j) (abs_nonneg _)
              (by exact_mod_cast Nat.zero_le H)
        _ = (k : ℚ) * (H : ℚ) * (((k.factorial * H ^ k : ℕ) : ℚ) / (K_B : ℚ)) := by
            simp [mul_assoc]
    have hv_le : ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ v) r - (b_unpert r : ℚ) ≤
        ((1 + k * k.factorial * H ^ (k + 1) : ℕ) : ℚ) / (K_B : ℚ) := by
      have h1 := (abs_sub_le_iff.1 hrow_diff).1
      have h2 := hu_le r
      have hrhs : (K_B : ℚ)⁻¹ + (k : ℚ) * (H : ℚ) *
            (((k.factorial * H ^ k : ℕ) : ℚ) / (K_B : ℚ)) =
          ((1 + k * k.factorial * H ^ (k + 1) : ℕ) : ℚ) / (K_B : ℚ) := by
        push_cast
        rw [pow_succ']
        have hK_ne : (K_B : ℚ) ≠ 0 := Int.cast_ne_zero.2 hK_pos.ne'
        field_simp
      linarith
    have hD_le : (basisAbsDet M_int T hT : ℚ) ≤ ((k.factorial * H ^ k : ℕ) : ℚ) := by
      exact_mod_cast abs_det_basisMat_le hM T hT
    have hD_pos : (0 : ℚ) < basisAbsDet M_int T hT := by exact_mod_cast abs_pos.2 hdet
    have hprod_lt : (basisAbsDet M_int T hT : ℚ) *
        (((1 + k * k.factorial * H ^ (k + 1) : ℕ) : ℚ) / (K_B : ℚ)) < 1 := by
      have h1 : (basisAbsDet M_int T hT : ℚ) *
            (((1 + k * k.factorial * H ^ (k + 1) : ℕ) : ℚ) / (K_B : ℚ)) ≤
          ((k.factorial * H ^ k : ℕ) : ℚ) *
            (((1 + k * k.factorial * H ^ (k + 1) : ℕ) : ℚ) / (K_B : ℚ)) := by
        gcongr
      have h2 : ((k.factorial * H ^ k : ℕ) : ℚ) *
            (((1 + k * k.factorial * H ^ (k + 1) : ℕ) : ℚ) / (K_B : ℚ)) < 1 := by
        rw [mul_div_assoc', div_lt_one (by exact_mod_cast hK_pos : (0 : ℚ) < K_B)]
        exact_mod_cast hK
      exact h1.trans_lt h2
    have hZ_lt : ((M_int r ⬝ᵥ basisSignNum M_int b_unpert T hT -
        basisAbsDet M_int T hT * b_unpert r : ℤ) : ℚ) < 1 := by
      have hdot : ((M_int r ⬝ᵥ basisSignNum M_int b_unpert T hT : ℤ) : ℚ) =
          (basisAbsDet M_int T hT : ℚ) * ((M_int.map Int.cast : Matrix κ (Fin k) ℚ) *ᵥ v) r := by
        simp only [dotProduct, mulVec, Int.cast_sum, Int.cast_mul, Matrix.map_apply,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hvj := basisSignNum_div_basisAbsDet M_int b_unpert T hT hdet j
        dsimp only [v]
        change (M_int r j : ℚ) * (basisSignNum M_int b_unpert T hT j : ℚ) =
          (basisAbsDet M_int T hT : ℚ) * ((M_int r j : ℚ) * ratBasisSol M_int b_unpert T hT j)
        rw [← hvj]
        field_simp [hD_pos.ne']
      rw [Int.cast_sub, Int.cast_mul, hdot, ← mul_sub]
      exact (mul_le_mul_of_nonneg_left hv_le hD_pos.le).trans_lt hprod_lt
    have hZ_le : M_int r ⬝ᵥ basisSignNum M_int b_unpert T hT -
        basisAbsDet M_int T hT * b_unpert r ≤ 0 := by
      have hZ : M_int r ⬝ᵥ basisSignNum M_int b_unpert T hT -
          basisAbsDet M_int T hT * b_unpert r < 1 := by exact_mod_cast hZ_lt
      omega
    omega

end BasisVertex

section ExactRecovery

/-- Exact Nash equilibrium extraction from any nonzero completely labelled basis pair `(T₁, T₂)`
of `(P_ε, Q_ε)` with `K_B = 2 ^ bitBound m n H`. -/
theorem isNash_extractNum {m n H : ℕ} [LinearOrder (Fin m ⊕ Fin n)]
    {A B : Matrix (Fin m) (Fin n) ℤ}
    (hm : 0 < m) (hn : 0 < n) (hH : 1 ≤ H)
    (hA : ∀ i j, 1 ≤ A i j ∧ A i j ≤ H) (hB : ∀ i j, 1 ≤ B i j ∧ B i j ≤ H)
    {T₁ T₂ : Finset (Fin m ⊕ Fin n)} {hT₁ : T₁.card = m} {hT₂ : T₂.card = n}
    (hP : IsFeasibleBasis (intMatP B) (pertRhsPInt m n ((2 : ℤ) ^ bitBound m n H)) T₁ hT₁)
    (hQ : IsFeasibleBasis (intMatQ A) (pertRhsQInt m n ((2 : ℤ) ^ bitBound m n H)) T₂ hT₂)
    (huniv : T₁ ∪ T₂ = Finset.univ)
    (hne0 : (T₁, T₂) ≠ (Finset.univ.image Sum.inl, Finset.univ.image Sum.inr)) :
    let numP := basisSignNum (intMatP B) (intRhsP m n) T₁ hT₁
    let numQ := basisSignNum (intMatQ A) (intRhsQ m n) T₂ hT₂
    let S₁ := ∑ i : Fin m, numP i
    let S₂ := ∑ j : Fin n, numQ j
    (∀ i, 0 ≤ numP i) ∧ 0 < S₁ ∧ (∀ i, |numP i| ≤ (m.factorial * H ^ m : ℕ)) ∧
      (∀ j, 0 ≤ numQ j) ∧ 0 < S₂ ∧ (∀ j, |numQ j| ≤ (n.factorial * H ^ n : ℕ)) ∧
      ({ A := A.map Int.cast, B := B.map Int.cast } : BimatrixGame (Fin m) (Fin n)).IsNash
        (fun i => (numP i : ℝ) / (S₁ : ℝ)) (fun j => (numQ j : ℝ) / (S₂ : ℝ)) := by
  intro numP numQ S₁ S₂
  set K_B : ℤ := (2 : ℤ) ^ bitBound m n H
  have hK_pos : 0 < K_B := by positivity
  have hK_P : ((m.factorial * H ^ m) * (1 + m * m.factorial * H ^ (m + 1)) : ℤ) < K_B := by
    change ((m.factorial * H ^ m * (1 + m * m.factorial * H ^ (m + 1)) : ℕ) : ℤ) <
      ((2 ^ bitBound m n H : ℕ) : ℤ)
    exact Int.ofNat_lt.2 (cramerScale_lt_two_pow_bitBound hm hn)
  have hK_Q : ((n.factorial * H ^ n) * (1 + n * n.factorial * H ^ (n + 1)) : ℤ) < K_B := by
    change ((n.factorial * H ^ n * (1 + n * n.factorial * H ^ (n + 1)) : ℕ) : ℤ) <
      ((2 ^ bitBound m n H : ℕ) : ℤ)
    exact Int.ofNat_lt.2 (cramerScale_lt_two_pow_bitBound_symm hm hn)
  have hdiffP : ∀ r, 0 ≤ pertRhsPInt m n K_B r - K_B ^ n * intRhsP m n r ∧
      pertRhsPInt m n K_B r - K_B ^ n * intRhsP m n r ≤ K_B ^ (n - 1) := fun r => by
    cases r with
    | inl i =>
      simp only [pertRhsPInt, intRhsP, Sum.elim_inl, Pi.zero_apply, mul_zero, sub_zero]
      exact ⟨le_rfl, pow_nonneg hK_pos.le _⟩
    | inr j =>
      change 0 ≤ K_B ^ n + K_B ^ (n - 1 - j.1) - K_B ^ n * 1 ∧
        K_B ^ n + K_B ^ (n - 1 - j.1) - K_B ^ n * 1 ≤ K_B ^ (n - 1)
      rw [mul_one, add_sub_cancel_left]
      exact ⟨pow_nonneg hK_pos.le _,
        pow_le_pow_right₀ (by omega : 1 ≤ K_B) (Nat.sub_le (n - 1) j.1)⟩
  have hdiffQ : ∀ r, 0 ≤ pertRhsQInt m n K_B r - K_B ^ m * intRhsQ m n r ∧
      pertRhsQInt m n K_B r - K_B ^ m * intRhsQ m n r ≤ K_B ^ (m - 1) := fun r => by
    cases r with
    | inl i =>
      change 0 ≤ K_B ^ m + K_B ^ (m - 1 - i.1) - K_B ^ m * 1 ∧
        K_B ^ m + K_B ^ (m - 1 - i.1) - K_B ^ m * 1 ≤ K_B ^ (m - 1)
      rw [mul_one, add_sub_cancel_left]
      exact ⟨pow_nonneg hK_pos.le _,
        pow_le_pow_right₀ (by omega : 1 ≤ K_B) (Nat.sub_le (m - 1) i.1)⟩
    | inr j =>
      simp only [pertRhsQInt, intRhsQ, Sum.elim_inr, Pi.zero_apply, mul_zero, sub_zero]
      exact ⟨le_rfl, pow_nonneg hK_pos.le _⟩
  obtain ⟨hdetP, hP_tight, hP_le⟩ := unperturbed_feasible_of_pert hm hH hn
    (fun r c => abs_intMatP_le hH hB r c) hdiffP hK_P hP
  obtain ⟨hdetQ, hQ_tight, hQ_le⟩ := unperturbed_feasible_of_pert hn hH hm
    (fun r c => abs_intMatQ_le hH hA r c) hdiffQ hK_Q hQ
  set D₁ := basisAbsDet (intMatP B) T₁ hT₁
  set D₂ := basisAbsDet (intMatQ A) T₂ hT₂
  have hD₁ : 0 < D₁ := abs_pos.2 hdetP
  have hD₂ : 0 < D₂ := abs_pos.2 hdetQ
  have hnumP_nn : ∀ i, 0 ≤ numP i := fun i => by
    have hrow := hP_le (.inl i)
    have h0 : intRhsP m n (.inl i) = 0 := rfl
    have hdot : intMatP B (.inl i) ⬝ᵥ numP = -numP i := by
      simp [dotProduct, intMatP_inl]
    rw [h0, hdot, mul_zero] at hrow
    omega
  have hnumQ_nn : ∀ j, 0 ≤ numQ j := fun j => by
    have hrow := hQ_le (.inr j)
    have h0 : intRhsQ m n (.inr j) = 0 := rfl
    have hdot : intMatQ A (.inr j) ⬝ᵥ numQ = -numQ j := by
      simp [dotProduct, intMatQ_inr]
    rw [h0, hdot, mul_zero] at hrow
    omega
  have hP_bd : ∀ i, |numP i| ≤ (m.factorial * H ^ m : ℕ) := fun i => by
    have hsign : |(basisMat (intMatP B) T₁ hT₁).det.sign| ≤ 1 := by
      rcases lt_or_gt_of_ne hdetP with h | h <;>
        simp [Int.sign_eq_neg_one_of_neg, Int.sign_eq_one_of_pos, h]
    have hc : |cramerVec (intMatP B) (intRhsP m n) T₁ hT₁ i| ≤ (m.factorial * H ^ m : ℕ) :=
      abs_cramerVec_le (fun r c => abs_intMatP_le hH hB r c)
        (fun r => by cases r <;> simp [intRhsP, hH]) T₁ hT₁ i
    calc |numP i| = |(basisMat (intMatP B) T₁ hT₁).det.sign| *
          |cramerVec (intMatP B) (intRhsP m n) T₁ hT₁ i| := abs_mul _ _
      _ ≤ 1 * (m.factorial * H ^ m : ℕ) := mul_le_mul hsign hc (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hQ_bd : ∀ j, |numQ j| ≤ (n.factorial * H ^ n : ℕ) := fun j => by
    have hsign : |(basisMat (intMatQ A) T₂ hT₂).det.sign| ≤ 1 := by
      rcases lt_or_gt_of_ne hdetQ with h | h <;>
        simp [Int.sign_eq_neg_one_of_neg, Int.sign_eq_one_of_pos, h]
    have hc : |cramerVec (intMatQ A) (intRhsQ m n) T₂ hT₂ j| ≤ (n.factorial * H ^ n : ℕ) :=
      abs_cramerVec_le (fun r c => abs_intMatQ_le hH hA r c)
        (fun r => by cases r <;> simp [intRhsQ, hH]) T₂ hT₂ j
    calc |numQ j| = |(basisMat (intMatQ A) T₂ hT₂).det.sign| *
          |cramerVec (intMatQ A) (intRhsQ m n) T₂ hT₂ j| := abs_mul _ _
      _ ≤ 1 * (n.factorial * H ^ n : ℕ) := mul_le_mul hsign hc (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hdisj : Disjoint T₁ T₂ := by
    rw [Finset.disjoint_iff_inter_eq_empty, Finset.eq_empty_iff_forall_notMem]
    have huc := Finset.card_union_add_card_inter T₁ T₂
    rw [hT₁, hT₂, huniv, Finset.card_univ, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin] at huc
    intro r hr
    have hpos : 0 < (T₁ ∩ T₂).card := Finset.card_pos.2 ⟨r, hr⟩
    omega
  have hT₁_ne : T₁ ≠ Finset.univ.image Sum.inl := by
    intro h1
    apply hne0
    refine Prod.ext h1 ?_
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      rcases r with i | j
      · exfalso
        exact Finset.disjoint_left.1 hdisj (h1 ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i)) hr
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
    · rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, Fintype.card_fin,
        hT₂]
  have hT₂_ne : T₂ ≠ Finset.univ.image Sum.inr := by
    intro h2
    apply hT₁_ne
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      rcases r with i | j
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      · exfalso
        exact Finset.disjoint_right.1 hdisj (h2 ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j)) hr
    · rw [Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ, Fintype.card_fin,
        hT₁]
  have hex_inr : ∃ j : Fin n, Sum.inr j ∈ T₁ := by
    by_contra hnone
    push Not at hnone
    apply hT₁_ne
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      rcases r with i | j
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      · exact absurd hr (hnone j)
    · rw [Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ, Fintype.card_fin,
        hT₁]
  have hex_inl : ∃ i : Fin m, Sum.inl i ∈ T₂ := by
    by_contra hnone
    push Not at hnone
    apply hT₂_ne
    apply Finset.eq_of_subset_of_card_le
    · intro r hr
      rcases r with i | j
      · exact absurd hr (hnone i)
      · exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
    · rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, Fintype.card_fin,
        hT₂]
  have hnumP_ne : numP ≠ 0 := by
    obtain ⟨j, hj⟩ := hex_inr
    intro h0
    have ht : intMatP B (.inr j) ⬝ᵥ numP = D₁ * intRhsP m n (.inr j) := hP_tight (.inr j) hj
    rw [h0, dotProduct_zero] at ht
    have hr1 : intRhsP m n (.inr j) = 1 := rfl
    rw [hr1, mul_one] at ht
    omega
  have hnumQ_ne : numQ ≠ 0 := by
    obtain ⟨i, hi⟩ := hex_inl
    intro h0
    have ht : intMatQ A (.inl i) ⬝ᵥ numQ = D₂ * intRhsQ m n (.inl i) := hQ_tight (.inl i) hi
    rw [h0, dotProduct_zero] at ht
    have hr1 : intRhsQ m n (.inl i) = 1 := rfl
    rw [hr1, mul_one] at ht
    omega
  have hS₁ : 0 < S₁ := by
    obtain ⟨i₀, hi₀⟩ : ∃ i, numP i ≠ 0 := Function.ne_iff.1 hnumP_ne
    have hpos : 0 < numP i₀ := lt_of_le_of_ne (hnumP_nn i₀) hi₀.symm
    have hle : numP i₀ ≤ S₁ :=
      Finset.single_le_sum (fun i _ => hnumP_nn i) (Finset.mem_univ i₀)
    omega
  have hS₂ : 0 < S₂ := by
    obtain ⟨j₀, hj₀⟩ : ∃ j, numQ j ≠ 0 := Function.ne_iff.1 hnumQ_ne
    have hpos : 0 < numQ j₀ := lt_of_le_of_ne (hnumQ_nn j₀) hj₀.symm
    have hle : numQ j₀ ≤ S₂ :=
      Finset.single_le_sum (fun j _ => hnumQ_nn j) (Finset.mem_univ j₀)
    omega
  refine ⟨hnumP_nn, hS₁, hP_bd, hnumQ_nn, hS₂, hQ_bd, ?_⟩
  let G : BimatrixGame (Fin m) (Fin n) := BimatrixGame.mk (A.map Int.cast) (B.map Int.cast)
  let x₀ : Fin m → ℝ := fun i => (numP i : ℝ) / (D₁ : ℝ)
  let y₀ : Fin n → ℝ := fun j => (numQ j : ℝ) / (D₂ : ℝ)
  have hD₁R : (0 : ℝ) < D₁ := by exact_mod_cast hD₁
  have hD₂R : (0 : ℝ) < D₂ := by exact_mod_cast hD₂
  have hS₁R : (0 : ℝ) < S₁ := by exact_mod_cast hS₁
  have hS₂R : (0 : ℝ) < S₂ := by exact_mod_cast hS₂
  have hx₀_le : G.matP *ᵥ x₀ ≤ rhsP (Fin m) (Fin n) := fun r => by
    rw [← intMatP_map_eq_matP A B]
    have hrZ : ((intMatP B r ⬝ᵥ numP : ℤ) : ℝ) ≤ (D₁ : ℝ) * (intRhsP m n r : ℝ) := by
      simpa only [Int.cast_mul] using (Int.cast_le (R := ℝ)).2 (hP_le r)
    have hlhs : ((intMatP B).map (Int.cast : ℤ → ℝ) *ᵥ x₀) r =
        ((intMatP B r ⬝ᵥ numP : ℤ) : ℝ) / (D₁ : ℝ) := by
      simp only [mulVec, dotProduct, Matrix.map_apply, x₀, Int.cast_sum, Int.cast_mul,
        div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
    have hrhs : rhsP (Fin m) (Fin n) r = (intRhsP m n r : ℝ) := by
      cases r <;> simp [rhsP_inl, rhsP_inr, intRhsP]
    rw [hlhs, hrhs, div_le_iff₀ hD₁R]
    simpa only [mul_comm] using hrZ
  have hy₀_le : G.matQ *ᵥ y₀ ≤ rhsQ (Fin m) (Fin n) := fun r => by
    rw [← intMatQ_map_eq_matQ A B]
    have hrZ : ((intMatQ A r ⬝ᵥ numQ : ℤ) : ℝ) ≤ (D₂ : ℝ) * (intRhsQ m n r : ℝ) := by
      simpa only [Int.cast_mul] using (Int.cast_le (R := ℝ)).2 (hQ_le r)
    have hlhs : ((intMatQ A).map (Int.cast : ℤ → ℝ) *ᵥ y₀) r =
        ((intMatQ A r ⬝ᵥ numQ : ℤ) : ℝ) / (D₂ : ℝ) := by
      simp only [mulVec, dotProduct, Matrix.map_apply, y₀, Int.cast_sum, Int.cast_mul,
        div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
    have hrhs : rhsQ (Fin m) (Fin n) r = (intRhsQ m n r : ℝ) := by
      cases r <;> simp [rhsQ_inl, rhsQ_inr, intRhsQ]
    rw [hlhs, hrhs, div_le_iff₀ hD₂R]
    simpa only [mul_comm] using hrZ
  have hcl : LemkeHowson.CompletelyLabeled G.matP (rhsP (Fin m) (Fin n))
      G.matQ (rhsQ (Fin m) (Fin n)) x₀ y₀ := by
    rw [LemkeHowson.completelyLabeled_iff]
    intro r
    have hr : r ∈ T₁ ∨ r ∈ T₂ := Finset.mem_union.1 (huniv ▸ Finset.mem_univ r)
    rcases hr with hr1 | hr2
    · left
      rw [mem_tightRows, ← intMatP_map_eq_matP A B]
      have hlhs : ((intMatP B).map (Int.cast : ℤ → ℝ) *ᵥ x₀) r =
          ((intMatP B r ⬝ᵥ numP : ℤ) : ℝ) / (D₁ : ℝ) := by
        simp only [mulVec, dotProduct, Matrix.map_apply, x₀, Int.cast_sum, Int.cast_mul,
          div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
      have hrZ : ((intMatP B r ⬝ᵥ numP : ℤ) : ℝ) = (D₁ : ℝ) * (intRhsP m n r : ℝ) := by
        simpa only [Int.cast_mul] using congrArg (Int.cast : ℤ → ℝ) (hP_tight r hr1)
      have hrhs : rhsP (Fin m) (Fin n) r = (intRhsP m n r : ℝ) := by
        cases r <;> simp [rhsP_inl, rhsP_inr, intRhsP]
      rw [hlhs, hrZ, hrhs, mul_div_cancel_left₀ _ hD₁R.ne']
    · right
      rw [mem_tightRows, ← intMatQ_map_eq_matQ A B]
      have hlhs : ((intMatQ A).map (Int.cast : ℤ → ℝ) *ᵥ y₀) r =
          ((intMatQ A r ⬝ᵥ numQ : ℤ) : ℝ) / (D₂ : ℝ) := by
        simp only [mulVec, dotProduct, Matrix.map_apply, y₀, Int.cast_sum, Int.cast_mul,
          div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
      have hrZ : ((intMatQ A r ⬝ᵥ numQ : ℤ) : ℝ) = (D₂ : ℝ) * (intRhsQ m n r : ℝ) := by
        simpa only [Int.cast_mul] using congrArg (Int.cast : ℤ → ℝ) (hQ_tight r hr2)
      have hrhs : rhsQ (Fin m) (Fin n) r = (intRhsQ m n r : ℝ) := by
        cases r <;> simp [rhsQ_inl, rhsQ_inr, intRhsQ]
      rw [hlhs, hrZ, hrhs, mul_div_cancel_left₀ _ hD₂R.ne']
  have hx₀_ne : x₀ ≠ 0 := fun h0 => hnumP_ne (funext fun i => by
    have := congrFun h0 i
    simp only [x₀, Pi.zero_apply, div_eq_zero_iff, Int.cast_eq_zero] at this
    exact this.resolve_right hD₁.ne')
  have hnash := isNash_of_completelyLabeled hx₀_le hy₀_le hcl hx₀_ne
  have hx_eq : (∑ i : Fin m, x₀ i)⁻¹ • x₀ = fun i => (numP i : ℝ) / (S₁ : ℝ) := by
    ext i
    have hsum : (∑ x : Fin m, x₀ x) = (S₁ : ℝ) / (D₁ : ℝ) := by
      simp only [x₀, div_eq_mul_inv, ← Finset.sum_mul, S₁, Int.cast_sum]
    simp only [Pi.smul_apply, smul_eq_mul, hsum, inv_div]
    change ((D₁ : ℝ) / (S₁ : ℝ)) * ((numP i : ℝ) / (D₁ : ℝ)) = (numP i : ℝ) / (S₁ : ℝ)
    field_simp [hD₁R.ne', hS₁R.ne']
  have hy_eq : (∑ j : Fin n, y₀ j)⁻¹ • y₀ = fun j => (numQ j : ℝ) / (S₂ : ℝ) := by
    ext j
    have hsum : (∑ x : Fin n, y₀ x) = (S₂ : ℝ) / (D₂ : ℝ) := by
      simp only [y₀, div_eq_mul_inv, ← Finset.sum_mul, S₂, Int.cast_sum]
    simp only [Pi.smul_apply, smul_eq_mul, hsum, inv_div]
    change ((D₂ : ℝ) / (S₂ : ℝ)) * ((numQ j : ℝ) / (D₂ : ℝ)) = (numQ j : ℝ) / (S₂ : ℝ)
    field_simp [hD₂R.ne', hS₂R.ne']
  simpa only [hx_eq, hy_eq] using hnash

end ExactRecovery

section RationalNormalization

/-- Common denominator scaling factor for two rational `m × n` payoff matrices. -/
@[expose] def clearDenomScale {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  ∏ i : Fin m, ∏ j : Fin n, (A i j).den * (B i j).den

theorem clearDenomScale_pos {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    0 < clearDenomScale A B := by
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
  exact Nat.mul_pos (Nat.pos_of_ne_zero (A i j).den_nz) (Nat.pos_of_ne_zero (B i j).den_nz)

theorem den_dvd_clearDenomScale_left {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) : (A i j).den ∣ clearDenomScale A B := by
  have hd : (A i j).den ∣ (A i j).den * (B i j).den := dvd_mul_right _ _
  have hrow : (A i j).den * (B i j).den ∣ ∏ c : Fin n, (A i c).den * (B i c).den :=
    Finset.dvd_prod_of_mem (fun c => (A i c).den * (B i c).den) (Finset.mem_univ j)
  have hall : (∏ c : Fin n, (A i c).den * (B i c).den) ∣ clearDenomScale A B :=
    Finset.dvd_prod_of_mem (fun r => ∏ c : Fin n, (A r c).den * (B r c).den) (Finset.mem_univ i)
  exact dvd_trans hd (dvd_trans hrow hall)

theorem den_dvd_clearDenomScale_right {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) (j : Fin n) : (B i j).den ∣ clearDenomScale A B := by
  have hd : (B i j).den ∣ (A i j).den * (B i j).den := dvd_mul_left _ _
  have hrow : (A i j).den * (B i j).den ∣ ∏ c : Fin n, (A i c).den * (B i c).den :=
    Finset.dvd_prod_of_mem (fun c => (A i c).den * (B i c).den) (Finset.mem_univ j)
  have hall : (∏ c : Fin n, (A i c).den * (B i c).den) ∣ clearDenomScale A B :=
    Finset.dvd_prod_of_mem (fun r => ∏ c : Fin n, (A r c).den * (B r c).den) (Finset.mem_univ i)
  exact dvd_trans hd (dvd_trans hrow hall)

/-- Integer numerator after scaling `M` by `clearDenomScale A B`. -/
@[expose] def clearDenomInt {m n : ℕ} (A B M : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin n) ℤ :=
  fun i j => (M i j).num * ((clearDenomScale A B / (M i j).den : ℕ) : ℤ)

/-- Shift constant guaranteeing positivity of both scaled payoff matrices. -/
@[expose] def clearDenomShift {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) : ℤ :=
  1 + ∑ i : Fin m, ∑ j : Fin n,
    (|clearDenomInt A B A i j| + |clearDenomInt A B B i j|)

/-- Positive integer normalized first payoff matrix. -/
@[expose] def clearDenomPosA {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin n) ℤ :=
  fun i j => clearDenomInt A B A i j + clearDenomShift A B

/-- Positive integer normalized second payoff matrix. -/
@[expose] def clearDenomPosB {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    Matrix (Fin m) (Fin n) ℤ :=
  fun i j => clearDenomInt A B B i j + clearDenomShift A B

/-- Entry upper bound `H` for both `clearDenomPosA A B` and `clearDenomPosB A B`. -/
@[expose] def clearDenomBound {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) : ℕ :=
  2 * (clearDenomShift A B).natAbs

theorem one_le_clearDenomBound {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    1 ≤ clearDenomBound A B := by
  have h1 : 1 ≤ clearDenomShift A B := by
    have hnn : 0 ≤ ∑ i : Fin m, ∑ j : Fin n,
        (|clearDenomInt A B A i j| + |clearDenomInt A B B i j|) :=
      Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
    dsimp only [clearDenomShift]
    linarith
  dsimp only [clearDenomBound]
  omega

theorem clearDenomPos_bounds {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) (i : Fin m) (j : Fin n) :
    1 ≤ clearDenomPosA A B i j ∧ clearDenomPosA A B i j ≤ clearDenomBound A B ∧
      1 ≤ clearDenomPosB A B i j ∧ clearDenomPosB A B i j ≤ clearDenomBound A B := by
  have hS : 1 ≤ clearDenomShift A B := by
    have hnn : 0 ≤ ∑ r : Fin m, ∑ c : Fin n,
        (|clearDenomInt A B A r c| + |clearDenomInt A B B r c|) :=
      Finset.sum_nonneg fun _ _ =>
        Finset.sum_nonneg fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)
    dsimp only [clearDenomShift]
    linarith
  have hterm : |clearDenomInt A B A i j| + |clearDenomInt A B B i j| ≤ clearDenomShift A B - 1 := by
    have h1 : |clearDenomInt A B A i j| + |clearDenomInt A B B i j| ≤
        ∑ c : Fin n, (|clearDenomInt A B A i c| + |clearDenomInt A B B i c|) :=
      Finset.single_le_sum (f := fun c => |clearDenomInt A B A i c| + |clearDenomInt A B B i c|)
        (fun c _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ j)
    have h2 : (∑ c : Fin n, (|clearDenomInt A B A i c| + |clearDenomInt A B B i c|)) ≤
        ∑ r : Fin m, ∑ c : Fin n, (|clearDenomInt A B A r c| + |clearDenomInt A B B r c|) :=
      Finset.single_le_sum
        (f := fun r => ∑ c : Fin n, (|clearDenomInt A B A r c| + |clearDenomInt A B B r c|))
        (fun r _ => Finset.sum_nonneg fun c _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
        (Finset.mem_univ i)
    dsimp only [clearDenomShift]
    linarith
  have hA := abs_le.1 (show |clearDenomInt A B A i j| ≤ clearDenomShift A B - 1 by
    linarith [abs_nonneg (clearDenomInt A B B i j)])
  have hB := abs_le.1 (show |clearDenomInt A B B i j| ≤ clearDenomShift A B - 1 by
    linarith [abs_nonneg (clearDenomInt A B A i j)])
  have hBnd : ((clearDenomBound A B : ℕ) : ℤ) = 2 * clearDenomShift A B := by
    dsimp only [clearDenomBound]
    have hpos : ((clearDenomShift A B).natAbs : ℤ) = clearDenomShift A B :=
      Int.natAbs_of_nonneg (by omega)
    omega
  dsimp only [clearDenomPosA, clearDenomPosB]
  omega

/-- Nash equilibria of the positive integer normalized game `⟨clearDenomPosA, clearDenomPosB⟩`
coincide with Nash equilibria of the rational game `⟨A, B⟩`. -/
theorem isNash_clearDenomPos {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    (BimatrixGame.mk ((clearDenomPosA A B).map Int.cast)
        ((clearDenomPosB A B).map Int.cast) : BimatrixGame (Fin m) (Fin n)).IsNash x y ↔
      (BimatrixGame.mk (A.map Rat.cast) (B.map Rat.cast) :
        BimatrixGame (Fin m) (Fin n)).IsNash x y := by
  let D : ℝ := ((clearDenomScale A B : ℕ) : ℝ)
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast clearDenomScale_pos A B
  have hcast : ∀ (M : Matrix (Fin m) (Fin n) ℚ),
      (∀ i j, (M i j).den ∣ clearDenomScale A B) →
      ∀ i j, ((clearDenomInt A B M i j : ℤ) : ℝ) = D * (M i j : ℝ) := fun M hd i j => by
    have hnat : (M i j).den * (clearDenomScale A B / (M i j).den) = clearDenomScale A B :=
      Nat.mul_div_cancel' (hd i j)
    have hden_ne : ((M i j).den : ℝ) ≠ 0 := by exact_mod_cast (M i j).den_nz
    have hrat : ((M i j : ℚ) : ℝ) = ((M i j).num : ℝ) / ((M i j).den : ℝ) := by
      exact_mod_cast (Rat.num_div_den (M i j)).symm
    have hnatR : ((M i j).den : ℝ) * ((clearDenomScale A B / (M i j).den : ℕ) : ℝ) = D := by
      dsimp only [D]
      exact_mod_cast hnat
    simp only [clearDenomInt, Int.cast_mul, Int.cast_natCast]
    rw [hrat, ← hnatR]
    field_simp
  have hcastA : ∀ i j, ((clearDenomInt A B A i j : ℤ) : ℝ) = D * (A i j : ℝ) :=
    hcast A (den_dvd_clearDenomScale_left A B)
  have hcastB : ∀ i j, ((clearDenomInt A B B i j : ℤ) : ℝ) = D * (B i j : ℝ) :=
    hcast B (den_dvd_clearDenomScale_right A B)
  let G : BimatrixGame (Fin m) (Fin n) := BimatrixGame.mk (A.map Rat.cast) (B.map Rat.cast)
  let GD : BimatrixGame (Fin m) (Fin n) := BimatrixGame.mk (D • G.A) (D • G.B)
  have hA_eq : (clearDenomPosA A B).map (Int.cast : ℤ → ℝ) =
      (GD.addConst (clearDenomShift A B : ℝ)).A := by
    ext i j
    simp [GD, G, clearDenomPosA, hcastA]
  have hB_eq : (clearDenomPosB A B).map (Int.cast : ℤ → ℝ) =
      (GD.addConst (clearDenomShift A B : ℝ)).B := by
    ext i j
    simp [GD, G, clearDenomPosB, hcastB]
  have hadd : (BimatrixGame.mk ((clearDenomPosA A B).map Int.cast)
      ((clearDenomPosB A B).map Int.cast) : BimatrixGame (Fin m) (Fin n)) =
      GD.addConst (clearDenomShift A B : ℝ) :=
    congr_arg₂ BimatrixGame.mk hA_eq hB_eq
  rw [hadd, isNash_addConst, isNash_smul hD G]

end RationalNormalization

end Cslib.GameTheory.BimatrixGame
