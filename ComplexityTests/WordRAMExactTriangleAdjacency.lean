/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationAdjacency
import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationBounds
import Complexity.Foundations.Data.List.Lookup

/-! # Native prepared adjacency with signed asymmetric input -/

namespace ComplexityTests.WordRAMExactTriangleAdjacency

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle

private def weightAt (i : Fin 768) : ℤ :=
  if i.val = 273 then 1 else if i.val = 513 then -1 else 0

private def values : List ℤ := List.ofFn weightAt

private def wAB (a b : Fin 16) : ℤ := values.getD (pairIndex (a, b)) 0
private def wBC (b c : Fin 16) : ℤ := values.getD (256 + pairIndex (b, c)) 0
private def wAC (a c : Fin 16) : ℤ := values.getD (512 + pairIndex (a, c)) 0

private theorem values_bound : ∀ z ∈ values, z.natAbs ≤ 1 := by
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  dsimp only [weightAt]
  split_ifs <;> decide

private theorem values_get_zero {i : ℕ} (hi : i < 256) : values.getD i 0 = 0 := by
  rw [values, List.getD_ofFn_of_lt weightAt (by omega)]
  simp only [weightAt, show i ≠ 273 by omega, show i ≠ 513 by omega, ↓reduceIte]

private theorem wAB_zero (a b : Fin 16) : wAB a b = 0 := by
  apply values_get_zero
  change a.val * 16 + b.val < 256
  have ha := a.isLt
  have hb := b.isLt
  omega

private theorem piece_size : pieceSize 16 1 = 4 := by
  have hs : sOf 16 = 4 := by
    change Nat.sqrt 16 = 4
    have hl : 4 ≤ Nat.sqrt 16 := Nat.le_sqrt.mpr (by decide)
    have hu : Nat.sqrt 16 < 5 := Nat.sqrt_lt.mpr (by decide)
    omega
  simp only [pieceSize, hs, ceilDiv_one]

private theorem query_capacity : queryCap 16 16 = 64 := by
  have hl : 64 ≤ Nat.sqrt 4096 := Nat.le_sqrt.mpr (by decide)
  have hu : Nat.sqrt 4096 < 65 := Nat.sqrt_lt.mpr (by decide)
  have hs : Nat.sqrt 4096 = 64 := by omega
  simpa only [queryCap, Nat.reducePow, Nat.reduceDiv] using hs

private theorem first_index : (0, 0, 0) ∈ instanceIndices wAB 16 1 3 := by
  rw [mem_instanceIndices]
  have hclass : (residueClass wAB 3 0).card = 256 := by
    have hset : residueClass wAB 3 0 = Finset.univ := by
      ext q
      simp only [residueClass, Finset.mem_filter, Finset.mem_univ, true_and, wAB_zero]
      decide
    rw [hset]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.reduceMul]
  constructor
  · simp only [numChunks, hclass, query_capacity]
    norm_num [Nat.ceilDiv_eq_add_pred_div]
  · norm_num [numPieces, piece_size, Nat.ceilDiv_eq_add_pred_div]

set_option maxRecDepth 4096 in
-- The actual initialized 768-weight memory witness exceeds the default expression depth.
/-- Signed asymmetric input gives two actual adjacent cells and two padded zeros in the
same initialized run. The client supplies neither a run nor a padding/coordinate premise. -/
example : ∃ y t, t ≤ 2826240 ∧
    Runs (PreparationInput.width 16 16 1 3 1) PreparationInput.flatProgram
      (State.init (PreparationInput.input 16 16 1 3 values))
      ⟨Instances.program.size, y⟩ (t - 1) ∧
    Executes (PreparationInput.width 16 16 1 3 1) PreparationInput.flatProgram
      (State.init (PreparationInput.input 16 16 1 3 values))
      (y.regs Instances.output) t ∧
    y.mem (y.regs Instances.output + 11) = 1 ∧
    y.mem (y.regs Instances.output + 343) = 1 ∧
    y.mem (y.regs Instances.output + 18) = 0 ∧
    y.mem (y.regs Instances.output + 455) = 0 := by
  have hp : 3 ∈ Nat.sqrtPrimeWindow 16 :=
    Nat.mem_sqrtPrimeWindow_iff_sq.mpr ⟨by decide, by decide, by decide⟩
  obtain ⟨y, t, ht, hr, he, hout, -, -⟩ := PreparationBounds.runs_input
    (n := 16) (D := 16) (g := 1) (p := 3) (A := 1) values
    (by simp only [values, List.length_ofFn])
    (by decide) (by decide) (by decide) hp values_bound le_rfl
  obtain ⟨hactive, hzero⟩ := PreparationSpec.instance_adjacency
    (fun q => values.getD q 0) wAB wBC wAC
    (by decide) (by decide) (by decide) hp
    (by intro a b; rfl) (by intro b c; rfl) (by intro a c; rfl)
    hout (0, 0, 0) first_index
  have hc : (1 : Fin 16) ∈ piece 16 16 1 0 := by
    rw [mem_piece, piece_size]
    decide
  have hAC : wAC 0 1 = -1 := by
    change values.getD 513 0 = -1
    rw [values, List.getD_ofFn_of_lt weightAt (by decide)]
    rfl
  have hBC : wBC 1 1 = 1 := by
    change values.getD 273 0 = 1
    rw [values, List.getD_ofFn_of_lt weightAt (by decide)]
    rfl
  have ha := hactive 0 1 1 hc 2
  norm_num [ChunkCatalogue.before, piece_size] at ha
  have hz := hzero 0 1 12 (by rw [piece_size]; decide)
  norm_num [ChunkCatalogue.before] at hz
  refine ⟨y, t, ht, hr, he, ha.1.mpr ?_, ha.2.mpr ?_, hz.1, hz.2⟩
  · change (2 : ℤ) ≡ wAC 0 1 + 0 [ZMOD (3 : ℤ)]
    rw [hAC]
    decide
  · change (2 : ℤ) ≡ -wBC 1 1 [ZMOD (3 : ℤ)]
    rw [hBC]
    decide

end ComplexityTests.WordRAMExactTriangleAdjacency
