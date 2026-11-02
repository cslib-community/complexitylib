/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection
import Mathlib.Data.List.GetD
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
# Original-input prime selection with the real modular counter

These clients discharge original numerical/magnitude/geometry premises and retain the same
native final state in prefix, halt, selected prime and count. Interpreter regressions call
the entire actual counter, complementing the separate controller-score tests.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMPrimeSelectionExecution

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

private def truth (n p : ℕ) (values : List ℤ) : ℕ :=
  Cslib.Algorithms.ExactTriangle.countZeroMod
    (fun α β : Fin n => values.getD (α.val * n + β.val) 0)
    (fun α β : Fin n => values.getD (n * n + α.val * n + β.val) 0)
    (fun α β : Fin n => values.getD (2 * (n * n) + α.val * n + β.val) 0) p

-- The original sum four is counted modulo two but not three, so the actual count improves.
#guard match entryProgram.eval 32 6000 (.init (CountPrime.inputWords 1 16 [4, 0, 0])) with
  | some (y, _) => y.regs Reg.best == 3 && y.regs Reg.bestCount == 0 &&
      y.regs Reg.found == 1 && y.mem 3 == 8
  | none => false

-- Signed cancellation gives equal actual counts and retains the first window prime.
#guard match entryProgram.eval 32 6000 (.init (CountPrime.inputWords 1 16 [-2, 1, 1])) with
  | some (y, _) => y.regs Reg.best == 2 && y.regs Reg.bestCount == 1 && y.mem 3 == 5
  | none => false

-- Empty original matrices still select a real prime with actual zero modular count.
#guard match entryProgram.eval 32 6000 (.init (CountPrime.inputWords 0 16 [])) with
  | some (y, _) => y.regs Reg.best == 2 && y.regs Reg.bestCount == 0 && y.mem 2 == 16
  | none => false

example : ∃ y t, t + 1 ≤ 5511 ∧
    Runs 32 (entryProgram.program Reg.best) (State.init (CountPrime.inputWords 1 16 [4, 0, 0]))
      ⟨entryProgram.size, y⟩ t ∧
    Executes 32 (entryProgram.program Reg.best) (State.init (CountPrime.inputWords 1 16 [4, 0, 0]))
      3 (t + 1) ∧ y.regs Reg.best = 3 ∧ y.regs Reg.bestCount = 0 ∧ y.mem 3 = 8 := by
  obtain ⟨_, y, t, ht, run, halt, _, hp, hc, _, frame⟩ := runs_input
    (W := 32) (n := 1) (D := 16) (A := 4) [4, 0, 0]
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3 : 3 ∈ Nat.sqrtPrimeWindow 16 :=
    Nat.mem_sqrtPrimeWindow_iff_sq.2 ⟨by decide, by decide, by decide⟩
  have hw := Nat.mem_sqrtPrimeWindow_iff_sq.1 hp.1
  have hlo : 2 ≤ y.regs Reg.best := hw.1.two_le
  have hhi : y.regs Reg.best ≤ 3 := by nlinarith only [hw.2.2]
  have hb : y.regs Reg.best = 3 := by
    have cases : y.regs Reg.best = 2 ∨ y.regs Reg.best = 3 := by omega
    rcases cases with h2 | h3
    · have hm := hp.2 3 h3
      rw [h2] at hm
      change truth 1 2 [4, 0, 0] ≤ truth 1 3 [4, 0, 0] at hm
      have bad : ¬(truth 1 2 [4, 0, 0] ≤ truth 1 3 [4, 0, 0]) := by decide
      exact (bad hm).elim
    · exact h3
  have hc0 : y.regs Reg.bestCount = 0 := by
    rw [hb] at hc
    change y.regs Reg.bestCount = truth 1 3 [4, 0, 0] at hc
    exact hc.trans (by decide)
  refine ⟨y, t, ?_, run, ?_, hb, hc0, frame 3 (Or.inl (by decide))⟩
  · simpa only [show timeBound 1 16 + 16 = 5511 by decide +kernel] using ht
  · simpa only [hb] using halt

-- The geometry used for logarithmic width and the finite false-positive theorem is inhabited.
-- This is a kernel proof of the actual run, not an interpreter run on a large zero matrix.
private def zeros : List ℤ := List.replicate (3 * (16 * 16)) 0

example : ∃ y t,
    Runs 256 (entryProgram.program Reg.best) (State.init (CountPrime.inputWords 16 16 zeros))
      ⟨entryProgram.size, y⟩ t ∧
    Executes 256 (entryProgram.program Reg.best) (State.init (CountPrime.inputWords 16 16 zeros))
      (y.regs Reg.best) (t + 1) ∧
    (t + 1 : ℝ) ≤ 3704 * (Nat.sqrt 16 + 1 : ℝ) ^ 3 * (16 + 1 : ℝ) ^ (281 / 100 : ℝ) +
      42 * (16 + 1 : ℝ) ∧
    (Cslib.Algorithms.ExactTriangle.falsePositiveCount
      (fun _ _ : Fin 16 => (0 : ℤ)) (fun _ _ => 0) (fun _ _ => 0) (y.regs Reg.best) : ℝ) ≤
        Cslib.Algorithms.ExactTriangle.falsePositiveConst *
          (1 * (16 : ℝ) ^ 3 * Real.log 16 / Real.sqrt 16) := by
  have hzero (i : ℕ) : zeros.getD i 0 = 0 := by
    exact List.getElem?_getD_replicate_default_eq 0 (3 * (16 * 16)) i
  obtain ⟨_, y, t, ht, run, halt, _, hp, _, _, _⟩ := runs_input
    (W := 256) (n := 16) (D := 16) (A := 0) zeros
    (by simp only [zeros, List.length_replicate]) (by decide)
    (by
      intro z hz
      obtain ⟨_, rfl⟩ := List.mem_replicate.mp hz
      decide)
    ((admissionWidth_le_log (κ := 1) (by decide) (by decide) (by decide)).trans (by decide))
  have hp0 : Cslib.Algorithms.ExactTriangle.IsSelectedPrime
      (fun _ _ : Fin 16 => (0 : ℤ)) (fun _ _ => 0) (fun _ _ => 0) 16 (y.regs Reg.best) := by
    simpa only [hzero] using hp
  have weights : Cslib.Algorithms.ExactTriangle.WeightsBoundedBy
      (fun _ _ : Fin 16 => (0 : ℤ)) (fun _ _ => 0) (fun _ _ => 0) ((16 : ℝ) ^ (1 : ℝ)) := by
    norm_num [Cslib.Algorithms.ExactTriangle.WeightsBoundedBy]
  refine ⟨y, t, run, halt, ?_, ?_⟩
  · have htR : (t + 1 : ℝ) ≤ ((timeBound 16 16 + 16 : ℕ) : ℝ) := by exact_mod_cast ht
    exact htR.trans (timeBound_le_subcubic 16 16)
  · exact Cslib.Algorithms.ExactTriangle.falsePositiveCount_le_const_mul
      (by decide) (by decide) (by norm_num) _ _ _ weights hp0

end ComplexityTests.WordRAMPrimeSelectionExecution
