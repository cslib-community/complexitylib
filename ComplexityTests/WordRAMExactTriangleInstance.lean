/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ExactTriangle.InstancePair
import Complexity.Algorithms.WordRAM.ExactTriangle.Instances
import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationInput
import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationBounds

/-! # Native ET instance-pair records and matrix padding -/

namespace ComplexityTests.WordRAMExactTriangleInstance

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ExactTriangle.InstancePair

private def leftValues : List ℕ := [0, 1, 1, 0]
private def rightValues : List ℕ := [0, 0, 1, 1]

private def initial : Data 32 where
  regs i := match i.val with
    | 17 => 5 | 18 => 9 | 19 => 30 | 20 => 2 | 21 => 5 | 22 => 2
    | 23 => 0 | 24 => 2 | 25 => 1 | 26 => 13 | 27 => 3 | 28 => 1 | _ => 0
  mem j := if 5 ≤ j ∧ j < 9 then leftValues.getD (j - 5) 0
    else if 9 ≤ j ∧ j < 13 then rightValues.getD (j - 9) 0
    else if j = 29 then 99 else if j = 56 then 77 else if j = 13 then 41 else 88

/-- The native pair writer overwrites nonzero output garbage, writes both computed matrix
pointers, pads the fifth middle coordinate with zero, and preserves query/source sentinels. -/
example : (program.eval 8 10 initial).map (fun (y, _) =>
    ((List.range 6).map (fun i => y.mem (30 + i)),
      (List.range 10).map (fun i => y.mem (36 + i)),
      (List.range 10).map (fun i => y.mem (46 + i)), [y.mem 13, y.mem 29, y.mem 56])) =
    some ([1, 1, 13, 3, 36, 46], [0, 1, 1, 0, 0, 1, 0, 0, 1, 0],
      [1, 0, 0, 1, 1, 0, 0, 1, 0, 0], [41, 99, 77]) := by decide +kernel

/-- Fully admitted general execution produces the real record and both concrete matrix
corners/padded positions in the same memory witness. -/
example : ∃ y, ExecWithin 8 program initial y 438 ∧
    y.mem 30 = 1 ∧ y.mem 32 = 13 ∧ y.mem 34 = 36 ∧ y.mem 35 = 46 ∧
    y.mem 37 = 1 ∧ y.mem 40 = 0 ∧ y.mem 46 = 1 ∧ y.mem 55 = 0 ∧
    y.mem 13 = 41 ∧ y.mem 29 = 99 ∧ y.mem 56 = 77 := by
  have hleft : ∀ i : Fin 4,
      initial.mem (5 + i.val) = leftValues.getD i.val 0 := by decide
  have hright : ∀ i : Fin 4,
      initial.mem (9 + i.val) = rightValues.getD i.val 0 := by decide
  obtain ⟨y, hy, hrecord, hL, hR, hf⟩ := exec (w := 8) initial
    (fun i => leftValues.getD i 0) (fun i => rightValues.getD i 0)
    (by decide) (by decide)
    (by
      intro i hi
      have hv : ∀ j : Fin 4, leftValues.getD j.val 0 < 2 := by decide
      exact hv ⟨i, hi⟩)
    (by
      intro i hi
      have hv : ∀ j : Fin 4, rightValues.getD j.val 0 < 2 := by decide
      exact hv ⟨i, hi⟩)
    (by intro i hi; exact hleft ⟨i, hi⟩)
    (by intro i hi; exact hright ⟨i, hi⟩)
    (by decide) (by decide) (by decide)
  have hr0 := hrecord 0
  have hr2 := hrecord 2
  have hr4 := hrecord 4
  have hr5 := hrecord 5
  have hl1 := hL ⟨1, by decide⟩
  have hl4 := hL ⟨4, by decide⟩
  have hb0 := hR ⟨0, by decide⟩
  have hb9 := hR ⟨9, by decide⟩
  refine ⟨y, hy, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hr0
  · exact hr2
  · exact hr4
  · exact hr5
  · exact hl1
  · exact hl4
  · exact hb0
  · exact hb9
  · exact (hf 13 (by decide)).trans (by decide)
  · exact (hf 29 (by decide)).trans (by decide)
  · exact (hf 56 (by decide)).trans (by decide)

end ComplexityTests.WordRAMExactTriangleInstance

namespace ComplexityTests.WordRAMExactTriangleInstances

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle.Instances

private def input : List ℕ := [1, 1, 1, 2] ++ ([-1, 0, 1] : List ℤ).map Signed.encode

-- Unfolding all composed kernels, their nested loops and the outer visit exceeds the default
-- expression recursion depth. Kernel reduction checks the actual initialized interpreter.
set_option maxRecDepth 4096 in
example : (program.eval 10 4 (.init input)).map (fun (y, _) =>
    ([y.regs output, y.regs produced, y.regs heap],
      (List.range 8).map (fun i => y.mem (20 + i)), [y.mem 5, y.mem 17, y.mem 28])) =
    some ([20, 1, 28], [1, 0, 15, 1, 26, 27, 1, 1], [3, 1, 0]) := by decide +kernel

-- Even with no visits, unfolding the composed initialization exceeds the default recursion depth.
set_option maxRecDepth 4096 in
example : (program.eval 10 4 (.init [0, 1, 0, 2])).map (fun (y, _) =>
    [y.regs output, y.regs produced, y.regs heap,
      y.mem 0, y.mem 1, y.mem 2, y.mem 3, y.mem 4]) =
    some [7, 0, 7, 4, 0, 1, 0, 2] := by decide +kernel

/-- The real input words fit, but the output addresses require more than four bits. -/
example : InputFits 4 input ∧ program.eval 4 4 (.init input) = none := by decide +kernel

/-- The complete public initialized theorem is inhabited for signed weights. Both the actual
prefix/halt and concrete allocation/input readback use the same returned state. -/
example : ∃ y t, t ≤ 431 ∧
    Runs (PreparationInput.width 1 1 1 2 1) PreparationInput.flatProgram
      (State.init input) ⟨program.size, y⟩ (t - 1) ∧
    Executes (PreparationInput.width 1 1 1 2 1) PreparationInput.flatProgram
      (State.init input) 20 t ∧
    y.regs produced = 1 ∧ y.regs heap = 28 ∧ y.mem 5 = 3 ∧ y.mem 28 = 0 := by
  let values : List ℤ := [-1, 0, 1]
  obtain ⟨y, t, ht, hr, he, hout, -, -⟩ := PreparationInput.runs_input
    (n := 1) (D := 1) (g := 1) (p := 2) (A := 1) values
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro z hz; simp only [values, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl <;> decide) le_rfl
  let C := fun rho => Nat.count (fun q => (values.getD q 0 % (2 : ℤ)).toNat = rho) 1
  have hK : ChunkCatalogue.before C (Cslib.Algorithms.ExactTriangle.queryCap 1 1) 2 = 1 := by
    decide
  have hH : Cslib.Algorithms.ExactTriangle.numPieces 1 1 1 = 1 := by decide
  have hcost : Instances.timeBound 1 1 2 1 1 = 431 := by decide
  change t ≤ Instances.timeBound 1 1 2
    (ChunkCatalogue.before C (Cslib.Algorithms.ExactTriangle.queryCap 1 1) 2)
    (Cslib.Algorithms.ExactTriangle.numPieces 1 1 1) at ht
  rw [hK, hH, hcost] at ht
  obtain ⟨-, -, -, hout, hcount, hheap, -, -, -, -, -, hframe⟩ := hout
  change y.regs output = 17 + 3 * ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 1 1) 2 at hout
  change y.regs produced = ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 1 1) 2 *
      Cslib.Algorithms.ExactTriangle.numPieces 1 1 1 at hcount
  change y.regs heap = 17 + 3 * ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 1 1) 2 +
      ChunkCatalogue.before C (Cslib.Algorithms.ExactTriangle.queryCap 1 1) 2 *
        Cslib.Algorithms.ExactTriangle.numPieces 1 1 1 * 8 at hheap
  have ho : y.regs output = 20 := by simpa only [hK, Nat.reduceAdd, Nat.reduceMul] using hout
  have hc : y.regs produced = 1 := by
    simpa only [hK, hH, Nat.reduceMul] using hcount
  have hh : y.regs heap = 28 := by
    simpa only [hK, hH, Nat.reduceAdd, Nat.reduceMul] using hheap
  refine ⟨y, t, ht, hr, ?_, hc, hh, ?_, ?_⟩
  · simpa only [ho, input, values, PreparationInput.input] using he
  · exact hframe 5 (Or.inl (by decide))
  · apply hframe 28
    apply Or.inr
    change 17 + 3 * ChunkCatalogue.before C (Cslib.Algorithms.ExactTriangle.queryCap 1 1) 2 +
      ChunkCatalogue.before C (Cslib.Algorithms.ExactTriangle.queryCap 1 1) 2 *
        Cslib.Algorithms.ExactTriangle.numPieces 1 1 1 * 8 ≤ 28
    rw [hK, hH]

private def sourceValues : List ℤ := List.replicate 768 0

set_option maxRecDepth 4096 in
-- This source-admissible client installs 768 concrete weights; type checking its actual
-- initialized state and flattened matrix readback exceeds the default expression depth.
/-- A source-admissible `n=D=16`, `p=3` instance checks the quantitative theorem, actual first
record, active adjacency cells, padded cells and complete allocation end. No execution premise
is supplied, and no interpreter reduction over the large composed run is needed. -/
example : ∃ y t, t ≤ 2826240 ∧
    Runs (PreparationInput.width 16 16 1 3 0) PreparationInput.flatProgram
      (State.init (PreparationInput.input 16 16 1 3 sourceValues)) ⟨program.size, y⟩ (t - 1) ∧
    Executes (PreparationInput.width 16 16 1 3 0) PreparationInput.flatProgram
      (State.init (PreparationInput.input 16 16 1 3 sourceValues)) 3092 t ∧
    y.regs produced = 16 ∧ y.regs heap = 11380 ∧
    y.mem 3094 = 1544 ∧ y.mem 3095 = 64 ∧
    y.mem 3098 = 1 ∧ y.mem 3110 = 0 ∧ y.mem 3354 = 1 ∧ y.mem 3546 = 0 := by
  have hprime : 3 ∈ Nat.sqrtPrimeWindow 16 :=
    Nat.mem_sqrtPrimeWindow_iff_sq.mpr
      ⟨by decide, by decide, by decide⟩
  obtain ⟨y, t, ht, hr, he, hout, -, -⟩ := PreparationBounds.runs_input
    (n := 16) (D := 16) (g := 1) (p := 3) (A := 0) sourceValues
    (by simp only [sourceValues, List.length_replicate])
    (by decide) (by decide) (by decide) hprime
    (by intro z hz; have : z = 0 := List.mem_replicate.mp hz |>.2; subst z; decide) le_rfl
  have hR (q : ℕ) : (sourceValues.getD q 0 % (3 : ℤ)).toNat = 0 := by
    change ((List.replicate 768 (0 : ℤ))[q]?.getD 0 % (3 : ℤ)).toNat = 0
    rw [List.getElem?_getD_replicate_default_eq]
    rfl
  let C := fun rho => Nat.count (fun q => (sourceValues.getD q 0 % (3 : ℤ)).toNat = rho) 256
  have hc0 : C 0 = 256 := Nat.count_of_forall fun q _ => hR q
  have hc1 : C 1 = 0 := Nat.count_of_forall_not fun q _ => by rw [hR]; decide
  have hc2 : C 2 = 0 := Nat.count_of_forall_not fun q _ => by rw [hR]; decide
  have hQ : Cslib.Algorithms.ExactTriangle.queryCap 16 16 = 64 := by
    have hl : 64 ≤ Nat.sqrt 4096 := Nat.le_sqrt.mpr (by decide)
    have hu : Nat.sqrt 4096 < 65 := Nat.sqrt_lt.mpr (by decide)
    have hs : Nat.sqrt 4096 = 64 := by omega
    simpa only [Cslib.Algorithms.ExactTriangle.queryCap, Nat.reducePow, Nat.reduceDiv] using hs
  have hS : Cslib.Algorithms.ExactTriangle.sOf 16 = 4 := by
    change Nat.sqrt 16 = 4
    have hl : 4 ≤ Nat.sqrt 16 := Nat.le_sqrt.mpr (by decide)
    have hu : Nat.sqrt 16 < 5 := Nat.sqrt_lt.mpr (by decide)
    omega
  have hB : Cslib.Algorithms.ExactTriangle.pieceSize 16 1 = 4 := by
    simp only [Cslib.Algorithms.ExactTriangle.pieceSize, hS, ceilDiv_one]
  have hH : Cslib.Algorithms.ExactTriangle.numPieces 16 16 1 = 4 := by
    norm_num [Cslib.Algorithms.ExactTriangle.numPieces, hB, Nat.ceilDiv_eq_add_pred_div]
  have hK : ChunkCatalogue.before C (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 3 = 4 := by
    simp only [ChunkCatalogue.before, Finset.sum_range_succ, Finset.sum_range_zero,
      hc0, hc1, hc2, hQ, Nat.ceilDiv_eq_add_pred_div]
  obtain ⟨-, -, -, ho, hc, hh, -, -, -, hdesc, hblocks, -⟩ := hout
  change y.regs output = 3080 + 3 * ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 3 at ho
  change y.regs produced = ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 3 *
      Cslib.Algorithms.ExactTriangle.numPieces 16 16 1 at hc
  change y.regs heap = 3080 + 3 * ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 3 +
      ChunkCatalogue.before C (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 3 *
        Cslib.Algorithms.ExactTriangle.numPieces 16 16 1 * 518 at hh
  have hout : y.regs output = 3092 := by simpa only [hK, Nat.reduceAdd, Nat.reduceMul] using ho
  have hcount : y.regs produced = 16 := by
    simpa only [hK, hH, Nat.reduceMul] using hc
  have hheap : y.regs heap = 11380 := by
    simpa only [hK, hH, Nat.reduceAdd, Nat.reduceMul] using hh
  have hd := hdesc 0 (by decide) 0 (by change 0 < C 0 ⌈/⌉ _; rw [hc0, hQ]; decide)
  have hpref : ChunkCatalogue.before C (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 0 = 0 := by
    simp [ChunkCatalogue.before]
  have hd0 : y.mem 3080 = 0 := by
    have hd' := hd.1
    change y.mem (3080 + 3 * (ChunkCatalogue.before C
      (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 0 + 0)) = 0 at hd'
    simpa only [hpref, Nat.reduceAdd, Nat.reduceMul] using hd'
  obtain ⟨hrec, hleft, hright⟩ := hblocks 0
    (by change 0 < ChunkCatalogue.before C _ 3 * _; rw [hK, hH]; decide)
  have hr2 := hrec 2
  have hr3 := hrec 3
  have hl0 := hleft ⟨0, by change 0 < 256; decide⟩
  have hl12 := hleft ⟨12, by change 12 < 256; decide⟩
  have hb0 := hright ⟨0, by change 0 < 256; decide⟩
  have hb192 := hright ⟨192, by change 192 < 256; decide⟩
  have hd1 := hd.2.1
  simp only [Nat.zero_mul, Nat.add_zero] at hd1
  change y.mem (3080 + 3 * (ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 0 + 0) + 1) = 1544 at hd1
  rw [hpref] at hd1
  have hd2 := hd.2.2
  simp only [Nat.zero_mul] at hd2
  change y.mem (3080 + 3 * (ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 0 + 0) + 2) =
      min (Cslib.Algorithms.ExactTriangle.queryCap 16 16) (C 0 - 0) at hd2
  rw [hpref, hQ, hc0] at hd2
  simp only [hH, Nat.zero_div, Nat.zero_mod, Nat.zero_mul, Nat.add_zero]
    at hr2 hr3 hl0 hl12 hb0 hb192
  change y.mem (3080 + 3 * ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 3 + 2) = y.mem 3081 at hr2
  change y.mem (3080 + 3 * ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 3 + 3) = y.mem 3082 at hr3
  change y.mem (3080 + 3 * ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 3 + 6) = _ at hl0
  change y.mem (3080 + 3 * ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 3 + 6 + 12) = _ at hl12
  change y.mem (3080 + 3 * ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 3 + 6 + 256) = _ at hb0
  change y.mem (3080 + 3 * ChunkCatalogue.before C
    (Cslib.Algorithms.ExactTriangle.queryCap 16 16) 3 + 6 + 256 + 192) = _ at hb192
  rw [hK] at hr2 hr3 hl0 hl12 hb0 hb192
  norm_num only [hH, hB, hR, hd0, WriteMatrices.entry] at hl0 hl12 hb0 hb192
  refine ⟨y, t, ht, hr, ?_, hcount, hheap, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hout] using he
  · exact hr2.trans hd1
  · exact hr3.trans hd2
  · exact hl0
  · exact hl12
  · exact hb0
  · exact hb192

end ComplexityTests.WordRAMExactTriangleInstances
