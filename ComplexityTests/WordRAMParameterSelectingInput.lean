/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.SourceBounds

/-!
# Admitted complete initialized small and large executions

The signed one-cell clients discharge every actual execution premise, tie the verdict to the
same prefix state and charge halt. The symbolic large family satisfies the real fast geometry;
it uses the general proved execution instead of evaluating its enormous native run.
-/

namespace ComplexityTests.WordRAMParameterSelectingInput

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle
open ParameterSelecting

example :
    let W := inputWidth 0 0 []
    ∃ (y : Data 640) (t : ℕ), t + 1 ≤ 82 ∧
      Runs W (entryProgram.program Reg.result) (State.init (CountPrime.inputWords 0 0 []))
        ⟨entryProgram.size, y⟩ t ∧
      Executes W (entryProgram.program Reg.result)
        (State.init (CountPrime.inputWords 0 0 [])) 0 (t + 1) ∧
      y.regs Reg.result = 0 := by
  obtain ⟨hi, p, mem, y, t, ht, hr, he, hb, hf, hiff, rest⟩ :=
    runs_input (n := 0) (F := 0) [] (by decide) (by decide) le_rfl
  have negative : ¬HasZeroTriangle
      (fun i j : Fin 0 => ([] : List ℤ).getD (pairIndex (i, j)) 0)
      (fun i j => ([] : List ℤ).getD (0 * 0 + pairIndex (i, j)) 0)
      (fun i j => ([] : List ℤ).getD (2 * (0 * 0) + pairIndex (i, j)) 0) := by
    rintro ⟨a, b, c, h⟩
    exact Fin.elim0 a
  have result : y.regs Reg.result = 0 := hf.resolve_right (fun h => negative (hiff.mp h))
  refine ⟨y, t, ?_, hr, ?_, result⟩
  · simpa only [timeBound, stageBudget, DyadicParameters.timeBound, ParameterChoice.blocks,
      ParameterChoice.level, Nat.log_zero_right, Nat.zero_div, Nat.mul_zero, Nat.add_zero,
      Nat.zero_mul, lt_self_iff_false, dite_false, Nat.reduceAdd, Nat.reduceMul] using ht
  · simpa only [result] using he

example :
    let values : List ℤ := [-1, -1, 2]
    let W := inputWidth 1 2 values
    ∃ (y : Data 640) (t : ℕ), t + 1 ≤ 121 ∧
      Runs W (entryProgram.program Reg.result) (State.init (CountPrime.inputWords 1 2 values))
        ⟨entryProgram.size, y⟩ t ∧
      Executes W (entryProgram.program Reg.result)
        (State.init (CountPrime.inputWords 1 2 values)) 1 (t + 1) ∧
      y.regs Reg.result = 1 := by
  obtain ⟨hi, p, mem, y, t, ht, hr, he, hb, hf, hiff, hp, hz, rest⟩ :=
    runs_input (n := 1) (F := 2) [-1, -1, 2] (by decide) (by decide) le_rfl
  have solution : HasZeroTriangle
      (fun i j : Fin 1 => ([-1, -1, 2] : List ℤ).getD (pairIndex (i, j)) 0)
      (fun i j => ([-1, -1, 2] : List ℤ).getD (1 * 1 + pairIndex (i, j)) 0)
      (fun i j => ([-1, -1, 2] : List ℤ).getD (2 * (1 * 1) + pairIndex (i, j)) 0) := by
    exact ⟨0, 0, 0, by norm_num [pairIndex]⟩
  have result := hiff.mpr solution
  refine ⟨y, t, ?_, hr, ?_, result⟩
  · simpa only [timeBound, stageBudget, DyadicParameters.timeBound, ParameterChoice.blocks,
      ParameterChoice.level, Nat.log_one_right, Nat.zero_div, Nat.mul_zero, Nat.add_zero,
      Nat.zero_mul, lt_self_iff_false, dite_false, Nat.reduceAdd, Nat.reduceMul] using ht
  · simpa only [result] using he

example :
    let values : List ℤ := [-1, -1, 1]
    let W := inputWidth 1 1 values
    ∃ (y : Data 640) (t : ℕ),
      Runs W (entryProgram.program Reg.result) (State.init (CountPrime.inputWords 1 1 values))
        ⟨entryProgram.size, y⟩ t ∧
      Executes W (entryProgram.program Reg.result)
        (State.init (CountPrime.inputWords 1 1 values)) 0 (t + 1) ∧
      y.regs Reg.result = 0 := by
  obtain ⟨hi, p, mem, y, t, ht, hr, he, hb, hf, hiff, rest⟩ :=
    runs_input (n := 1) (F := 1) [-1, -1, 1] (by decide) (by decide) le_rfl
  have negative : ¬HasZeroTriangle
      (fun i j : Fin 1 => ([-1, -1, 1] : List ℤ).getD (pairIndex (i, j)) 0)
      (fun i j => ([-1, -1, 1] : List ℤ).getD (1 * 1 + pairIndex (i, j)) 0)
      (fun i j => ([-1, -1, 1] : List ℤ).getD (2 * (1 * 1) + pairIndex (i, j)) 0) := by
    rintro ⟨a, b, c, h⟩
    have ea : a.val = 0 := by omega
    have eb : b.val = 0 := by omega
    have ec : c.val = 0 := by omega
    norm_num [pairIndex, ea, eb, ec] at h
  have result : y.regs Reg.result = 0 := hf.resolve_right (fun h => negative (hiff.mp h))
  exact ⟨y, t, hr, by simpa only [result] using he, result⟩

-- This client intentionally names the source's exact constant threshold 2^1296.
set_option exponentiation.threshold 1300 in
/-- Every dimension in the actual nontrivial parameter regime has an admitted complete run.
The selected prime conclusion is discharged from computed geometry, not an extra premise. -/
example (n : ℕ) (z : ℤ) (hn : 2 ^ 1296 ≤ n) :
    let values : List ℤ := List.replicate (3 * (n * n)) z
    let W := inputWidth n z.natAbs values
    ∃ (p : ℕ) (y : Data 640) (t : ℕ),
      Runs W (entryProgram.program Reg.result)
        (State.init (CountPrime.inputWords n z.natAbs values))
        ⟨entryProgram.size, y⟩ t ∧
      Executes W (entryProgram.program Reg.result)
        (State.init (CountPrime.inputWords n z.natAbs values)) (y.regs Reg.result) (t + 1) ∧
      (y.regs Reg.result = 1 ↔ z = 0) ∧
      IsSelectedPrime
        (fun i j : Fin n => values.getD (pairIndex (i, j)) 0)
        (fun i j => values.getD (n * n + pairIndex (i, j)) 0)
        (fun i j => values.getD (2 * (n * n) + pairIndex (i, j)) 0)
        (ParameterChoice.window n) p := by
  have hfast : 0 < ParameterChoice.blocks n := by
    rw [ParameterChoice.blocks_pos_iff]
    exact hn
  have hpos : 0 < n := (Nat.two_pow_pos 1296).trans_le hn
  obtain ⟨hi, p, mem, y, t, ht, hr, he, hb, hf, hiff, hp, rest⟩ :=
    runs_input (n := n) (F := z.natAbs) (List.replicate (3 * (n * n)) z) (by simp)
      (by simp) le_rfl
  have cell (i j : Fin n) : pairIndex (i, j) < n * n := by
    simpa only [pairIndex, Fin.coe_mkDivMod, Nat.mul_comm] using (Fin.mkDivMod i j).isLt
  have one (q : ℕ) (hq : q < 3 * (n * n)) :
      (List.replicate (3 * (n * n)) z).getD q 0 = z := List.getD_replicate z hq
  have triangle : HasZeroTriangle
      (fun i j : Fin n => (List.replicate (3 * (n * n)) z).getD (pairIndex (i, j)) 0)
      (fun i j => (List.replicate (3 * (n * n)) z).getD (n * n + pairIndex (i, j)) 0)
      (fun i j => (List.replicate (3 * (n * n)) z).getD (2 * (n * n) + pairIndex (i, j)) 0)
      ↔ z = 0 := by
    constructor
    · rintro ⟨a, b, c, h⟩
      dsimp only at h
      rw [one (pairIndex (a, b)) (by have := cell a b; omega),
        one (n * n + pairIndex (b, c)) (by have := cell b c; omega),
        one (2 * (n * n) + pairIndex (a, c)) (by have := cell a c; omega)] at h
      omega
    · intro hz
      refine ⟨⟨0, hpos⟩, ⟨0, hpos⟩, ⟨0, hpos⟩, ?_⟩
      simp [hz, List.getD_eq_getElem?_getD]
  exact ⟨p, y, t, hr, he, hiff.trans triangle, hp hfast⟩

end ComplexityTests.WordRAMParameterSelectingInput
