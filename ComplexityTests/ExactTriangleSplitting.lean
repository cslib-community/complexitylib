/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.ExactTriangle.Witnesses
import Mathlib.Tactic.NormNum.NatSqrt

open Cslib.Algorithms.ExactTriangle Cslib.Matrix

-- Row-major chunks, including the short last chunk and the first empty chunk.
example : chunk (Finset.univ : Finset (Fin 2 × Fin 2)) 3 0 =
    {(0, 0), (0, 1), (1, 0)} := by decide
example : chunk (Finset.univ : Finset (Fin 2 × Fin 2)) 3 1 = {(1, 1)} := by decide
example : chunk (Finset.univ : Finset (Fin 2 × Fin 2)) 3 2 = ∅ := by decide
example : chunk (∅ : Finset (Fin 2 × Fin 2)) 3 0 = ∅ := by decide
example : numChunks (Finset.univ : Finset (Fin 2 × Fin 2)) 3 = 2 := by
  rw [numChunks, Nat.ceilDiv_eq_add_pred_div]
  decide

private theorem pieceSize16 : pieceSize 16 2 = 2 := by
  rw [pieceSize, sOf]
  norm_num [Nat.ceilDiv_eq_add_pred_div]
private theorem queryCap16 : queryCap 16 16 = 64 := by norm_num [queryCap]
example : queryCap 17 17 = 70 := by norm_num [queryCap]
example : queryCap 0 16 = 0 := by norm_num [queryCap]
example : queryCap 16 0 = 0 := by norm_num [queryCap]

-- Boundary indices belong to adjacent pieces; out-of-range pieces are empty.
example : (1 : Fin 16) ∈ piece 16 16 2 0 ∧ (2 : Fin 16) ∈ piece 16 16 2 1 := by
  simp [piece, pieceSize16]
example : piece 16 16 2 8 = ∅ := by
  ext c
  simp only [piece, pieceSize16, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false]
  omega
example : piece 0 16 2 0 = ∅ := by simp [piece]
example : numPieces 16 16 2 = 8 := by
  rw [numPieces, pieceSize16, Nat.ceilDiv_eq_add_pred_div]

private def zeroWeight : Fin 16 → Fin 16 → ℤ := fun _ _ => 0
private def falseWeight : Fin 16 → Fin 16 → ℤ := fun _ _ => 6

-- The prime window admits p = 3 at the smallest supported D.
private theorem prime3 : 3 ∈ primesInRange 16 := by
  rw [mem_primesInRange_iff_sq]
  decide

-- All-zero matrices supply an admitted, nonempty splitting with the promised bounds.
example : (totalChunks zeroWeight 16 3 : ℝ) ≤ 3 + Real.sqrt 16 :=
  (totalChunks_le zeroWeight (by decide) (by decide) prime3).1
example : ((instanceIndices zeroWeight 16 2 3).card : ℝ) ≤ 4 * 16 * 2 :=
  card_instanceIndices_le zeroWeight (by decide) (by decide) (by decide) prime3
example : Fintype.card (lopInstance zeroWeight zeroWeight zeroWeight 16 2 3 (0, 0, 0)).M ≤ 16 :=
  card_middle_lopInstance zeroWeight zeroWeight zeroWeight (by decide) (by decide) prime3 _

-- Residues include negative weights, and are independent of exact zero sums.
example : (0, 0) ∈ residueClass (fun _ _ : Fin 1 => -1) 3 2 := by decide
example : IsFalsePositive falseWeight zeroWeight zeroWeight 3 (0, 0, 0) := by decide
example : ¬ HasZeroTriangle falseWeight zeroWeight zeroWeight := by
  simp [HasZeroTriangle, falseWeight, zeroWeight]
example : HasZeroTriangle zeroWeight zeroWeight zeroWeight := ⟨0, 0, 0, rfl⟩

-- Recovery rejects a modular false positive; a true zero returns a witness on its first scan.
example : scanPiece falseWeight zeroWeight zeroWeight 16 2 0 0 0 = none := by
  rw [scanPiece_eq_none_iff]
  intro c _
  norm_num [weightSum, falseWeight, zeroWeight]
example : scanPiece zeroWeight zeroWeight zeroWeight 16 2 0 0 0 = some 0 := by
  simp [scanPiece, piece, pieceSize16, weightSum, zeroWeight, List.finRange_succ]
example : runScans falseWeight zeroWeight zeroWeight 16 2
    [(((0 : Fin 3), 0, 0), (0, 0))] = (none, 1) := by
  have hscan : scanPiece falseWeight zeroWeight zeroWeight 16 2 0 0 0 = none := by
    rw [scanPiece_eq_none_iff]
    intro c _
    norm_num [weightSum, falseWeight, zeroWeight]
  simp [runScans, hscan]
example : runScans zeroWeight zeroWeight zeroWeight 16 2
    [(((0 : Fin 3), 0, 0), (0, 0)), ((0, 0, 1), (1, 1))] = (some (0, 0, 0), 1) := by
  simp [runScans, scanPiece, piece, pieceSize16, weightSum, zeroWeight, List.finRange_succ]

-- The query at rank 63 ends chunk 0; rank 64 starts chunk 1.
example : (3, 15) ∈ chunkOf zeroWeight 16 3 0 0 := by
  have hclass : residueClass zeroWeight 3 0 = Finset.univ := by
    ext q
    simp [residueClass, zeroWeight]
  simp [chunkOf, queryCap16, hclass, chunk, rankIn_univ, pairIndex]
example : (4, 0) ∈ chunkOf zeroWeight 16 3 0 1 := by
  have hclass : residueClass zeroWeight 3 0 = Finset.univ := by
    ext q
    simp [residueClass, zeroWeight]
  simp [chunkOf, queryCap16, hclass, chunk, rankIn_univ, pairIndex]

private theorem falseQuery : (0, 0) ∈
    (lopInstance falseWeight zeroWeight zeroWeight 16 2 3 (0, 0, 0)).W := by
  change (0, 0) ∈ chunkOf falseWeight 16 3 0 0
  have hclass : residueClass falseWeight 3 0 = Finset.univ := by
    ext q
    norm_num [residueClass, falseWeight, Int.ModEq]
  simp [chunkOf, queryCap16, hclass, chunk, rankIn_univ, pairIndex]

-- A modular query really is accepted despite the absence of any exact zero triangle.
example :
    (lopInstance falseWeight zeroWeight zeroWeight 16 2 3 (0, 0, 0)).HasCommonNeighbor 0 0 := by
  rw [hasCommonNeighbor_lopInstance_iff falseWeight zeroWeight zeroWeight (by decide) falseQuery]
  refine ⟨0, ?_, ?_⟩
  · simp [piece, pieceSize16]
  · decide

-- Supply the actual finite modular answers, rather than an abstract unconstrained answer premise.
private def modularAnswers (wAB wBC wAC : Fin 16 → Fin 16 → ℤ)
    (ι : InstanceIndex 3) (q : Fin 16 × Fin 16) : Bool :=
  decide (∃ c ∈ piece 16 16 2 ι.2.2, weightSum wAB wBC wAC q.1 q.2 c ≡ 0 [ZMOD (3 : ℤ)])

private theorem modularAnswers_correct (wAB wBC wAC : Fin 16 → Fin 16 → ℤ) :
    AnswersCorrect wAB wBC wAC 16 2 3 (modularAnswers wAB wBC wAC) := by
  intro ι _ q hq
  apply propext
  simp only [modularAnswers, decide_eq_true_eq]
  exact (hasCommonNeighbor_lopInstance_iff wAB wBC wAC (by decide) hq).symm

private theorem zeroSelected : IsSelectedPrime zeroWeight zeroWeight zeroWeight 16 3 := by
  refine ⟨prime3, fun q _ => ?_⟩
  simp [countZeroMod, weightSum, zeroWeight]

-- The complete recovery theorem is inhabited at its smallest admitted n and D.
example : ∃ L, IsScanOrder zeroWeight zeroWeight zeroWeight 16 2 3
    (modularAnswers zeroWeight zeroWeight zeroWeight) L ∧
    (runScans zeroWeight zeroWeight zeroWeight 16 2 L).1 ≠ none ∧
    (runScans zeroWeight zeroWeight zeroWeight 16 2 L).2 ≤ 1 := by
  obtain ⟨L, hL⟩ := exists_isScanOrder zeroWeight zeroWeight zeroWeight 16 2 3
    (modularAnswers zeroWeight zeroWeight zeroWeight)
  have hc := modularAnswers_correct zeroWeight zeroWeight zeroWeight
  obtain ⟨hout, hcount⟩ := recovery_correct (by decide) (by decide) (by decide)
    zeroWeight zeroWeight zeroWeight zeroSelected hc hL
  refine ⟨L, hL, fun hn => hout.2 hn ⟨0, 0, 0, rfl⟩, ?_⟩
  simpa [falsePositiveCount, IsFalsePositive, weightSum, zeroWeight] using hcount

private theorem falseSelected : IsSelectedPrime falseWeight zeroWeight zeroWeight 16 3 := by
  refine ⟨prime3, fun q hq => ?_⟩
  obtain ⟨hprime, -, hsq⟩ := mem_primesInRange_iff_sq.mp hq
  have hq : q = 2 ∨ q = 3 := by
    have := hprime.two_le
    have : q < 4 := by nlinarith
    omega
  rcases hq with rfl | rfl <;>
    norm_num [countZeroMod, weightSum, falseWeight, zeroWeight, Int.ModEq]

example : ∃ L, IsScanOrder falseWeight zeroWeight zeroWeight 16 2 3
    (modularAnswers falseWeight zeroWeight zeroWeight) L ∧
    (runScans falseWeight zeroWeight zeroWeight 16 2 L).1 = none := by
  obtain ⟨L, hL⟩ := exists_isScanOrder falseWeight zeroWeight zeroWeight 16 2 3
    (modularAnswers falseWeight zeroWeight zeroWeight)
  refine ⟨L, hL, (recovery_eq_none_iff (by decide) (by decide) (by decide)
    falseWeight zeroWeight zeroWeight falseSelected
    (modularAnswers_correct falseWeight zeroWeight zeroWeight) hL).mpr ?_⟩
  simp [HasZeroTriangle, falseWeight, zeroWeight]
