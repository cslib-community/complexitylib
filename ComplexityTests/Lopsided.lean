/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.ExactTriangle.Lopsided
import Complexity.Foundations.Data.Int.LogBounds
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Concrete tests for padding, counts, queried answers and signed reconstruction. -/

open Cslib.Algorithms.ExactTriangle
open LopsidedGraph

private abbrev twoNeighbors : LopsidedGraph 2 where
  M := Fin 2
  adjA a _ := a = 0
  adjB _ b := b = 1
  W := {(0, 1)}

private def padded : Fin 2 ↪ Fin 3 := ⟨fun v => ⟨v.val, by omega⟩,
  fun _ _ h => Fin.ext (show _ from congrArg (fun v : Fin 3 => v.val) h)⟩

example : twoNeighbors.commonNeighborCount 0 1 = 2 := by
  norm_num [commonNeighborCount, twoNeighbors, Finset.univ_fin2]
  rfl

example : twoNeighbors.HasCommonNeighbor 0 1 := ⟨0, rfl, rfl⟩

example : ¬twoNeighbors.HasCommonNeighbor 1 1 := by
  simp [HasCommonNeighbor, twoNeighbors]

example : twoNeighbors.matX padded 0 2 = 0 ∧ twoNeighbors.matY padded 2 1 = 0 := by
  have h : (2 : Fin 3) ∉ Set.range padded := by
    rintro ⟨v, hv⟩
    have hv' : v.val = 2 := congrArg (fun w : Fin 3 => w.val) hv
    have := v.isLt
    omega
  exact ⟨matX_apply_of_notMem_range _ _ _ h, matY_apply_of_notMem_range _ _ h _⟩

example : (twoNeighbors.matX padded * twoNeighbors.matY padded) 0 1 = 2 := by
  rw [matX_mul_matY_apply]
  norm_num [commonNeighborCount, twoNeighbors, Finset.univ_fin2]
  rfl

-- Values away from the sole query are deliberately incorrect and still allowed.
example : Set.EqOn (fun q : Fin 2 × Fin 2 => if q = (0, 1) then 2 else 99)
    (fun q => twoNeighbors.commonNeighborCount q.1 q.2) (twoNeighbors.W : Set _) := by
  intro q hq
  have h : q = (0, 1) := by simpa [twoNeighbors] using hq
  subst q
  norm_num [commonNeighborCount, twoNeighbors, Finset.univ_fin2]
  rfl

private abbrev emptyMiddle : LopsidedGraph 1 where
  M := Fin 0
  adjA _ _ := True
  adjB _ _ := True
  W := {(0, 0)}

example : emptyMiddle.commonNeighborCount 0 0 = 0 := by
  simp [commonNeighborCount, emptyMiddle]

example : ¬emptyMiddle.HasCommonNeighbor 0 0 := by
  simp [HasCommonNeighbor, emptyMiddle]

example : (emptyMiddle.matX (Function.Embedding.refl _) *
    emptyMiddle.matY (Function.Embedding.refl _)) 0 0 = 0 := by
  rw [matX_mul_matY_apply]
  simp [commonNeighborCount, emptyMiddle]

private def signedX : Matrix (Fin 1) (Fin 2) ℤ := !![-3, 2]
private def signedY : Matrix (Fin 2) (Fin 1) ℤ := !![2; -1]

example : (signedX * signedY) 0 0 = -8 := by
  norm_num [signedX, signedY, Matrix.mul_apply, Fin.sum_univ_two]

example : (signedBitInstance signedX signedY {(0, 0)} true false 0 1).commonNeighborCount
    0 0 = 1 := by
  classical
  simp only [signedBitInstance, commonNeighborCount_ofMatrices, ↓reduceIte]
  norm_num [signedX, signedY,
    Cslib.Matrix.bit, posPart_def, negPart_def, Finset.univ_fin2,
    Finset.filter_insert, Finset.filter_singleton]

example : (signedBitInstance signedX signedY {(0, 0)} false true 1 0).commonNeighborCount
    0 0 = 1 := by
  classical
  simp only [signedBitInstance, commonNeighborCount_ofMatrices, ↓reduceIte]
  norm_num [signedX, signedY,
    Cslib.Matrix.bit, posPart_def, negPart_def, Finset.univ_fin2,
    Finset.filter_insert, Finset.filter_singleton]

-- Apply the signed reconstruction theorem to an actual product, including all four signs.
example : (∑ i ∈ Finset.range 2, ∑ j ∈ Finset.range 2, (2 : ℤ) ^ (i + j) *
    (((signedBitInstance signedX signedY {(0, 0)} false false i j).commonNeighborCount 0 0 : ℤ)
      - ((signedBitInstance signedX signedY {(0, 0)} false true i j).commonNeighborCount 0 0 : ℤ)
      - ((signedBitInstance signedX signedY {(0, 0)} true false i j).commonNeighborCount 0 0 : ℤ)
      + ((signedBitInstance signedX signedY {(0, 0)} true true i j).commonNeighborCount 0 0 : ℤ)))
    = -8 := by
  rw [← mul_apply_eq_sum_signedBitInstance_counts signedX signedY {(0, 0)} 2
    (by intro a j; fin_cases a; fin_cases j <;> norm_num [signedX])
    (by intro j b; fin_cases j <;> fin_cases b <;> norm_num [signedY])]
  norm_num [signedX, signedY, Matrix.mul_apply, Fin.sum_univ_two]

example : Cslib.Matrix.bit (!![-1, 0, 3] : Matrix (Fin 1) (Fin 3) ℤ) 1 0 0 = 1 := by
  norm_num [Cslib.Matrix.bit]

example : |(-7 : ℤ)| < 2 ^ (Nat.log 2 7 + 1) := by
  exact Int.abs_lt_two_pow_log_succ (-7) (by norm_num)

example : |(0 : ℤ)| < 2 ^ (Nat.log 2 0 + 1) := by
  exact Int.abs_lt_two_pow_log_succ 0 (by norm_num)

example : (signedX * (-signedY)) 0 0 = 8 := by
  norm_num [signedX, signedY, Matrix.mul_apply, Fin.sum_univ_two]

example : (ofMatrices (!![1, 1] : Matrix (Fin 1) (Fin 2) ℤ) !![1; 1]
    {(0, 0)}).commonNeighborCount 0 0 = 2 := by
  have h := mul_apply_eq_commonNeighborCount_ofMatrices
    (!![1, 1] : Matrix (Fin 1) (Fin 2) ℤ) !![1; 1] {(0, 0)}
    (by intro a j; fin_cases a; fin_cases j <;> simp)
    (by intro j b; fin_cases j <;> fin_cases b <;> simp) 0 0
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h
  exact_mod_cast h.symm

example : (signedBitInstance signedX (-signedY) {(0, 0)} true true 0 1).commonNeighborCount
    0 0 = 1 := by
  classical
  simp only [signedBitInstance, commonNeighborCount_ofMatrices, ↓reduceIte]
  norm_num [signedX, signedY,
    Cslib.Matrix.bit, posPart_def, negPart_def, Finset.univ_fin2,
    Finset.filter_insert, Finset.filter_singleton]

example : (signedBitInstances signedX signedY {(0, 0)} 2 (true, false, 0, 1)).W =
    {(0, 0)} := rfl

example : Fintype.card (Bool × Bool × Fin 2 × Fin 2) = 16 := by decide

-- Empty outer parts with a genuinely nonempty middle part still give an empty product.
example : (0 : Matrix (Fin 0) (Fin 3) ℤ) * (0 : Matrix (Fin 3) (Fin 0) ℤ) = 0 := by
  ext a b
  exact Fin.elim0 a

example : Set.EqOn (fun _ : Fin 0 × Fin 0 => (99 : ℕ))
    (fun q =>
      (ofMatrices (0 : Matrix (Fin 0) (Fin 3) ℤ) 0 ∅).commonNeighborCount q.1 q.2)
    (∅ : Set (Fin 0 × Fin 0)) := by
  simp

-- With beta zero, strict magnitude bounds are satisfied by zero matrices of nonempty shape.
example : ((0 : Matrix (Fin 1) (Fin 2) ℤ) * (0 : Matrix (Fin 2) (Fin 1) ℤ)) 0 0 = 0 := by
  have h := mul_apply_eq_sum_signedBitInstance_counts (0 : Matrix (Fin 1) (Fin 2) ℤ) 0 {(0, 0)} 0
    (by simp) (by simp) 0 0
  simpa only [Finset.range_zero, Finset.sum_empty] using h

-- A queried edge with disjoint middle neighborhoods is a negative triangle query.
example : let I := ofMatrices (!![1, 0] : Matrix (Fin 1) (Fin 2) ℤ) !![0; 1] {(0, 0)}
    (0, 0) ∈ I.W ∧ I.commonNeighborCount 0 0 = 0 := by
  dsimp only
  constructor
  · simp [ofMatrices]
  · rw [commonNeighborCount_ofMatrices]
    norm_num [Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton]
