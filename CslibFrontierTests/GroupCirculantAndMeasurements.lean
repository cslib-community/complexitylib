/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Foundations.LinearAlgebra.Matrix.GroupCirculant
import CslibFrontier.Foundations.LinearAlgebra.Matrix.KroneckerRank
import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearMeasurements
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FinCases

/-!
# Tests for group-circulant spectra, Kronecker powers, and linear-measurement bounds
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GroupCirculantAndMeasurements

open Finset Matrix
open scoped BigOperators Kronecker

/-! ### 1. Nonsingular minors, Kronecker product rank, and Kronecker powers -/

private def rankOneMat : Matrix (Fin 2) (Fin 2) ℚ :=
  of ![![1, -1], ![2, -2]]

theorem rank_rankOneMat : rankOneMat.rank = 1 := by
  have hle : rankOneMat.rank ≤ 1 := by
    let C : Matrix (Fin 2) (Fin 1) ℚ := of ![![1], ![2]]
    let D : Matrix (Fin 1) (Fin 2) ℚ := of ![![1, -1]]
    have hCD : rankOneMat = C * D := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [rankOneMat, C, D, Matrix.mul_apply]
    calc rankOneMat.rank = (C * D).rank := by rw [hCD]
      _ ≤ C.rank := rank_mul_le_left C D
      _ ≤ Fintype.card (Fin 1) := rank_le_card_width C
      _ = 1 := rfl
  have hne : rankOneMat.rank ≠ 0 := by
    rw [ne_eq, Matrix.rank_eq_zero_iff]
    intro h0
    have h00 := congrFun (congrFun h0 0) 0
    norm_num [rankOneMat] at h00
  omega

example :
    (∃ (r c : Fin rankOneMat.rank → Fin 2),
      Function.Injective r ∧ Function.Injective c ∧ (rankOneMat.submatrix r c).det ≠ 0) ∧
    (rankOneMat ⊗ₖ rankOneMat).rank = 1 ∧
    (kroneckerPow rankOneMat 3).rank = 1 := by
  refine ⟨exists_submatrix_det_ne_zero rankOneMat, ?_, ?_⟩
  · rw [rank_kronecker, rank_rankOneMat]
  · rw [rank_kroneckerPow, rank_rankOneMat, one_pow]

example : (kroneckerPow (sylvesterTwo ℚ) 3).rank = 8 := by
  rw [← cubeCharMatrix_eq_kroneckerPow, rank_cubeCharMatrix (by norm_num : (2 : ℚ) ≠ 0),
    Fintype.card_fin]
  decide

example :
    let v : Fin 2 → Bool → ℚ := fun _ b => if b then 0 else 1
    kroneckerPow (sylvesterTwo ℚ) 2 *ᵥ (fun y => ∏ i, v i (y i)) =
      fun x => ∏ i : Fin 2, (sylvesterTwo ℚ *ᵥ v i) (x i) :=
  kroneckerPow_mulVec_prod (sylvesterTwo ℚ) 2 (fun _ b => if b then 0 else 1)

/-! ### 2. Group-circulant spectra, Walsh–Hadamard matrices, and Cayley/DFT bridges -/

private noncomputable def diff3 : ZMod 3 → ℂ :=
  fun g => if g = 0 then 1 else if g = 1 then -1 else 0

theorem rank_circulant_diff3 :
    (circulant diff3).rank = 2 ∧
      Nat.card {ψ : AddChar (ZMod 3) ℂ // circulantEigenvalue diff3 ψ ≠ 0} = 2 := by
  have hr : (circulant diff3).rank = 2 := by
    have hle : (circulant diff3).rank ≤ 2 := by
      let J : Matrix (ZMod 3) (ZMod 3) ℂ := of fun _ _ => 1
      have hsum0 : ∑ g : ZMod 3, diff3 g = 0 := by
        have h3 : (univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
        rw [h3, sum_insert (by decide), sum_insert (by decide), sum_singleton]
        have h01 : (1 : ZMod 3) ≠ 0 := by decide
        have h20 : (2 : ZMod 3) ≠ 0 := by decide
        have h21 : (2 : ZMod 3) ≠ 1 := by decide
        simp [diff3, h01, h20, h21]
      have hmul : circulant diff3 * J = 0 := by
        ext i j
        rw [Matrix.mul_apply, Matrix.zero_apply]
        have heq : (∑ k : ZMod 3, circulant diff3 i k * J k j) = ∑ g : ZMod 3, diff3 g := by
          refine Fintype.sum_equiv (Equiv.subLeft i) _ _ fun k => ?_
          simp [J, Equiv.subLeft_apply]
        rw [heq, hsum0]
      have hJ : 1 ≤ J.rank := by
        have hJne : J.rank ≠ 0 := by
          rw [ne_eq, Matrix.rank_eq_zero_iff]
          intro h0
          have h00 := congrFun (congrFun h0 0) 0
          norm_num [J] at h00
        omega
      have hsum := rank_add_rank_le_card_of_mul_eq_zero hmul
      rw [ZMod.card 3] at hsum
      omega
    have hge : 2 ≤ (circulant diff3).rank := by
      let emb : Fin 2 → ZMod 3 := ![0, 1]
      let S : Matrix (Fin 2) (Fin 2) ℂ := (circulant diff3).submatrix emb emb
      have hdet : S.det ≠ 0 := by
        rw [Matrix.det_fin_two]
        have h01 : (0 : ZMod 3) - 1 ≠ 0 ∧ (0 : ZMod 3) - 1 ≠ 1 := by decide
        have h10 : (1 : ZMod 3) - 0 = 1 ∧ (1 : ZMod 3) ≠ 0 := by decide
        simp only [S, submatrix_apply, circulant_apply, emb, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_fin_one, sub_self, diff3, ↓reduceIte,
          h01.1, h01.2, h10.1, h10.2]
        norm_num
      have hunit : IsUnit S := (isUnit_iff_isUnit_det S).mpr (IsUnit.mk0 _ hdet)
      have hSrank : S.rank = 2 := by simpa using rank_of_isUnit S hunit
      have hsub := rank_submatrix_le (circulant diff3) emb emb
      rwa [hSrank] at hsub
    omega
  exact ⟨hr, (rank_circulant_complex diff3).symm.trans hr⟩

example :
    let w : ZMod 3 → ℚ := fun g => if g = 0 then 1 else if g = 1 then -1 else 0
    (circulant w).rank =
      Nat.card {ψ : AddChar (ZMod 3) ℂ // circulantEigenvalue (fun g => (w g : ℂ)) ψ ≠ 0} :=
  rank_circulant_rat _

private def evenCubeWeight : (Fin 2 → Bool) → ℚ :=
  fun x => if x 0 = x 1 then 1 else 0

theorem rank_circulant_evenCubeWeight : (circulant evenCubeWeight).rank = 2 := by
  rw [rank_circulant_cube (by norm_num : (2 : ℚ) ≠ 0) evenCubeWeight]
  let f : Finset (Fin 2) → ℚ := fun S =>
    ∑ x : Fin 2 → Bool, evenCubeWeight x * Cslib.BitString.chi ℚ S x
  have hf : ∀ S : Finset (Fin 2), f S = 1 + (-1 : ℚ) ^ #S := by
    intro S
    have heq : f S = ∑ x ∈ univ.filter (fun x : Fin 2 → Bool => x 0 = x 1),
        Cslib.BitString.chi ℚ S x := by
      dsimp only [f]
      rw [sum_filter]
      refine sum_congr rfl fun x _ => ?_
      dsimp only [evenCubeWeight]
      split_ifs <;> simp
    have hpair : (univ.filter fun x : Fin 2 → Bool => x 0 = x 1) =
        {fun _ => false, fun _ => true} := by decide
    rw [heq, hpair, sum_pair (by decide)]
    simp [Cslib.BitString.chi]
  have hfilter : (univ.filter fun S : Finset (Fin 2) => f S ≠ 0) = {∅, univ} := by
    ext S
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, hf]
    have hcases : S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = univ := by
      revert S
      decide
    rcases hcases with rfl | rfl | rfl | rfl
    · simp
    · norm_num
    · norm_num
    · have hcard : #(univ : Finset (Fin 2)) = 2 := by decide
      rw [hcard]
      norm_num
  change #(univ.filter fun S : Finset (Fin 2) => f S ≠ 0) = 2
  rw [hfilter, card_pair (by decide)]

example : cubeCharMatrix ℚ (Fin 2) * cubeCharMatrix ℚ (Fin 2) =
    (4 : ℚ) • (1 : Matrix (Fin 2 → Bool) (Fin 2 → Bool) ℚ) := by
  have h := cubeCharMatrix_mul_self ℚ (Fin 2)
  norm_num at h
  exact h

example (s : Fin 2 → Fin 2 → Bool) (f : (Fin 2 → Bool) → ℝ) :
    (Cslib.RotationMap.cubeCayley s).walk f = circulant (cubeCayleyWeight s) *ᵥ f :=
  cubeCayley_walk_eq_circulant_mulVec s f

example :
    let s : Fin 2 → Fin 2 → Bool := ![fun _ => false, fun _ => true]
    ∀ S : Finset (Fin 2),
      circulantEigenvalue (cubeCayleyWeight s) (Cslib.BitString.chiChar ℝ S) =
        Cslib.BitString.bias ((Cslib.Probability.PMF.uniformOfFintype (Fin 2)).map s) S :=
  circulantEigenvalue_cubeCayleyWeight _

example (w : Fin 2 → ℚ) (k : Fin 2) :
    circulant w *ᵥ (fun j : Fin 2 => (-1 : ℚ) ^ ((j : ℕ) * k)) =
      Cslib.dft (-1 : ℚ) (fun i : Fin 2 => w (-i)) k •
        (fun j : Fin 2 => (-1 : ℚ) ^ ((j : ℕ) * k)) :=
  circulant_mulVec_pow_eq_dft_smul (by norm_num : (-1 : ℚ) ^ 2 = 1) w k

/-! ### 3. Row-basis selection, `(2n + 1)^r` value bound, and fibre identities -/

private def redundantTrinary : Matrix (Fin 4) (Fin 3) ℚ :=
  of ![![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![-1, 1, 0]]

theorem isUnitTrinary_redundantTrinary : IsUnitTrinary redundantTrinary := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [redundantTrinary]

theorem rank_redundantTrinary : redundantTrinary.rank = 2 := by
  have hle : redundantTrinary.rank ≤ 2 := by
    let C : Matrix (Fin 4) (Fin 2) ℚ := of ![![1, 0], ![0, 1], ![1, 1], ![-1, 0]]
    let D : Matrix (Fin 2) (Fin 3) ℚ := of ![![1, -1, 0], ![0, 1, -1]]
    have hCD : redundantTrinary = C * D := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [redundantTrinary, C, D, Matrix.mul_apply, Fin.sum_univ_two]
    calc redundantTrinary.rank = (C * D).rank := by rw [hCD]
      _ ≤ C.rank := rank_mul_le_left C D
      _ ≤ Fintype.card (Fin 2) := rank_le_card_width C
      _ = 2 := rfl
  have hge : 2 ≤ redundantTrinary.rank := by
    let r2 : Fin 2 → Fin 4 := ![0, 1]
    let c2 : Fin 2 → Fin 3 := ![0, 1]
    let S : Matrix (Fin 2) (Fin 2) ℚ := redundantTrinary.submatrix r2 c2
    have hdet : S.det ≠ 0 := by
      rw [Matrix.det_fin_two]
      simp [S, redundantTrinary, r2, c2]
    have hunit : IsUnit S := (isUnit_iff_isUnit_det S).mpr (IsUnit.mk0 _ hdet)
    have hSrank : S.rank = 2 := by simpa using rank_of_isUnit S hunit
    exact hSrank ▸ rank_submatrix_le redundantTrinary r2 c2
  omega

theorem redundantTrinary_value_bounds :
    let φ := fun (x : Fin 3 → Bool) (j : Fin 3) => Cslib.BitString.bitVal ℚ (x j)
    2 ≤ #(measurementValues redundantTrinary φ univ) ∧
      #(measurementValues redundantTrinary φ univ) ≤ 49 ∧
      #(univ.image fun x : Fin 3 → Bool =>
          redundantTrinary *ᵥ fun j => (-1 : ℚ) ^ (x j).toNat) ≤ 49 := by
  dsimp only
  let φ := fun (x : Fin 3 → Bool) (j : Fin 3) => Cslib.BitString.bitVal ℚ (x j)
  refine ⟨?_, ?_, ?_⟩
  · have hmem0 : redundantTrinary *ᵥ φ (fun _ => false) ∈
        measurementValues redundantTrinary φ univ := mem_image_of_mem _ (mem_univ _)
    have hmem1 : redundantTrinary *ᵥ φ ![true, false, false] ∈
        measurementValues redundantTrinary φ univ := mem_image_of_mem _ (mem_univ _)
    have hne : redundantTrinary *ᵥ φ (fun _ => false) ≠
        redundantTrinary *ᵥ φ ![true, false, false] := by
      intro h
      have h0 := congrFun h 0
      simp [φ, redundantTrinary, mulVec, dotProduct, Fin.sum_univ_three,
        Cslib.BitString.bitVal] at h0
    exact Finset.one_lt_card_iff.mpr ⟨_, _, hmem0, hmem1, hne⟩
  · have hb := card_image_mulVec_bitVal_le_pow_rank redundantTrinary
      isUnitTrinary_redundantTrinary univ
    rw [rank_redundantTrinary] at hb
    exact hb
  · have hs := card_image_mulVec_sign_le_pow_rank redundantTrinary
      isUnitTrinary_redundantTrinary univ
    rw [rank_redundantTrinary] at hs
    exact hs

theorem redundantTrinary_compressed_fibre_sum (g : (Fin 4 → ℚ) → ℚ) (w : (Fin 3 → Bool) → ℚ) :
    let B := selectRowBasis redundantTrinary
    let φ := fun (x : Fin 3 → Bool) (j : Fin 3) => Cslib.BitString.bitVal ℚ (x j)
    (redundantTrinary.submatrix B.rowIdx id).rank = 2 ∧
      (∑ x : Fin 3 → Bool, g (redundantTrinary *ᵥ φ x) * w x) =
        ∑ y ∈ measurementValues (redundantTrinary.submatrix B.rowIdx id) φ univ,
          g (B.reconstruct y) *
            ∑ x ∈ measurementFiber (redundantTrinary.submatrix B.rowIdx id) φ univ y, w x := by
  dsimp only
  refine ⟨(selectRowBasis redundantTrinary).rank_submatrix_eq.trans rank_redundantTrinary, ?_⟩
  exact (selectRowBasis redundantTrinary).sum_mul_comp_mulVec _ univ g w

example :
    let φ := fun (x : Fin 3 → Bool) (j : Fin 3) => Cslib.BitString.bitVal ℚ (x j)
    ∃ y ∈ measurementValues redundantTrinary φ univ,
      8 ≤ 49 * #(measurementFiber redundantTrinary φ univ y) := by
  have hex := exists_le_card_measurementFiber_bitVal redundantTrinary
    isUnitTrinary_redundantTrinary (univ_nonempty (α := Fin 3 → Bool))
  simpa [rank_redundantTrinary] using hex

example (M : Matrix (Fin 2) (Fin 3) (ZMod 3)) (x₀ : Fin 3 → ZMod 3) :
    #(univ.filter fun x : Fin 3 → ZMod 3 => M *ᵥ x = M *ᵥ x₀) =
      #(univ.filter fun z : Fin 3 → ZMod 3 => M *ᵥ z = 0) :=
  card_filter_mulVec_eq_card_ker M x₀

example (w : ZMod 3 × ZMod 2 → ℂ) (y : ZMod 3) :
    (3 : ℂ) * ∑ x ∈ univ.filter (fun x : ZMod 3 × ZMod 2 => x.1 = y), w x =
      ∑ ψ : AddChar (ZMod 3) ℂ, ψ (-y) * ∑ x : ZMod 3 × ZMod 2, ψ x.1 * w x := by
  have h := AddChar.card_mul_sum_filter_eq (AddMonoidHom.fst (ZMod 3) (ZMod 2)) y w
  rwa [ZMod.card 3, Nat.cast_ofNat] at h

example (w : (Fin 3 → ZMod 2) → ℝ) (y : Fin 2 → ZMod 2) :
    let M : Matrix (Fin 2) (Fin 3) (ZMod 2) := of ![![1, 1, 0], ![0, 1, 1]]
    (4 : ℝ) * ∑ x ∈ univ.filter (fun x => M *ᵥ x = y), w x =
      ∑ u : Fin 2 → ZMod 2, (-1 : ℝ) ^ (u ⬝ᵥ y).val *
        ∑ x : Fin 3 → ZMod 2, (-1 : ℝ) ^ ((Mᵀ *ᵥ u) ⬝ᵥ x).val * w x := by
  dsimp only
  have h := two_pow_mul_sum_filter_mulVec_zmodTwo (of ![![1, 1, 0], ![0, 1, 1]]) y w
  have h4 : (2 : ℝ) ^ Fintype.card (Fin 2) = 4 := by norm_num
  rwa [h4] at h

end CslibFrontierTests.GroupCirculantAndMeasurements
