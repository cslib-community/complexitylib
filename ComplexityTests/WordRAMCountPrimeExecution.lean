/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime

/-!
# Fully admitted complete modular-counter clients

Every witness below is the same actual State.init prefix and halting state. These kernel
proof clients complement the interpreter's dirty-workspace, padding and transpose regressions.
The resource predicates are discharged from original inputs, not assumed as certificates.
-/

namespace ComplexityTests.WordRAMCountPrimeExecution

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

private def truth (n p : ℕ) (values : List ℤ) : ℕ :=
  Cslib.Algorithms.ExactTriangle.countZeroMod
    (fun α β : Fin n => values.getD (α.val * n + β.val) 0)
    (fun α β : Fin n => values.getD (n * n + α.val * n + β.val) 0)
    (fun α β : Fin n => values.getD (2 * (n * n) + α.val * n + β.val) 0) p

-- A nonzero original sum is counted modulo three. The derived width is met exactly.
example : ∃ y : Data 128, ∃ t, t + 1 ≤ 736 ∧
    Runs (admissionWidth 1 3 4) (entryProgram.program Reg.result)
      (State.init (inputWords 1 3 [-2, 1, 4])) ⟨entryProgram.size, y⟩ t ∧
    Executes (admissionWidth 1 3 4) (entryProgram.program Reg.result)
      (State.init (inputWords 1 3 [-2, 1, 4])) 1 (t + 1) ∧
    y.regs Reg.result = 1 ∧ y.mem 3 = 5 := by
  obtain ⟨_, y, t, ht, run, halt, result, _, frame⟩ :=
    runs_input (W := admissionWidth 1 3 4) (n := 1) (p := 3) (A := 4)
      [-2, 1, 4] (by decide) (by decide) (by decide) le_rfl
  change y.regs Reg.result = truth 1 3 [-2, 1, 4] at result
  rw [show truth 1 3 [-2, 1, 4] = 1 by decide] at result
  refine ⟨y, t, ?_, run, ?_, result, ?_⟩
  · simpa only [show cost 1 3 + 10 = 736 by decide] using ht
  · simpa only [result] using halt
  · exact frame 3 (Or.inl (by decide))

-- The same signed data has no modular-zero triangle modulo five.
example : ∃ y : Data 128, ∃ t, t + 1 ≤ 1454 ∧
    Runs (admissionWidth 1 5 4) (entryProgram.program Reg.result)
      (State.init (inputWords 1 5 [-2, 1, 4])) ⟨entryProgram.size, y⟩ t ∧
    Executes (admissionWidth 1 5 4) (entryProgram.program Reg.result)
      (State.init (inputWords 1 5 [-2, 1, 4])) 0 (t + 1) ∧ y.mem 3 = 5 := by
  obtain ⟨_, y, t, ht, run, halt, result, _, frame⟩ :=
    runs_input (W := admissionWidth 1 5 4) (n := 1) (p := 5) (A := 4)
      [-2, 1, 4] (by decide) (by decide) (by decide) le_rfl
  change y.regs Reg.result = truth 1 5 [-2, 1, 4] at result
  rw [show truth 1 5 [-2, 1, 4] = 0 by decide] at result
  exact ⟨y, t, by simpa only [show cost 1 5 + 10 = 1454 by decide] using ht,
    run, by simpa only [result] using halt, frame 3 (Or.inl (by decide))⟩

private def asymmetric : List ℤ :=
  [-1, 0, 2, -3, 1, -2, 3, 0, 0, 4, -2, 1]

-- Positive recursion depth, an asymmetric BC transpose and signed nonzero coefficients.
example : ∃ y : Data 128, ∃ t, t + 1 ≤ 4596 ∧
    Runs (admissionWidth 2 2 4) (entryProgram.program Reg.result)
      (State.init (inputWords 2 2 asymmetric)) ⟨entryProgram.size, y⟩ t ∧
    Executes (admissionWidth 2 2 4) (entryProgram.program Reg.result)
      (State.init (inputWords 2 2 asymmetric)) 4 (t + 1) ∧
    y.mem 0 = 14 ∧ y.mem 3 = 3 := by
  obtain ⟨_, y, t, ht, run, halt, result, _, frame⟩ :=
    runs_input (W := admissionWidth 2 2 4) (n := 2) (p := 2) (A := 4)
      asymmetric (by decide) (by decide) (by decide) le_rfl
  change y.regs Reg.result = truth 2 2 asymmetric at result
  rw [show truth 2 2 asymmetric = 4 by decide] at result
  exact ⟨y, t, by simpa only [show cost 2 2 + 10 = 4596 by decide] using ht,
    run, by simpa only [result] using halt, frame 0 (Or.inl (by decide)),
    frame 3 (Or.inl (by decide))⟩

private def aliasedCaller : Data 128 :=
  (((((Data.init ([3] ++ List.replicate 30 99 ++ [777])).set Reg.side 1).set
    Reg.modulus 3).set Reg.inputAB 1).set Reg.inputBC 1).set Reg.inputAC 1 |>.set Reg.scratch 2

-- Original arrays may share a source address; scratch is dirty and its outside sentinel survives.
example : ∃ y : Data 128, ExecWithin 12 program aliasedCaller y 726 ∧
    y.regs Reg.result = 1 ∧ y.mem 1 = 3 ∧ y.mem 32 = 777 := by
  have read : ∀ i < 1 * 1, aliasedCaller.mem (1 + i) = Signed.encode (-1) := by
    intro i hi
    have he : i = 0 := by omega
    subst i
    rfl
  have side : aliasedCaller.regs Reg.side = 1 := by rfl
  have modulus : aliasedCaller.regs Reg.modulus = 3 := by rfl
  have ab : aliasedCaller.regs Reg.inputAB = 1 := by rfl
  have bc : aliasedCaller.regs Reg.inputBC = 1 := by rfl
  have ac : aliasedCaller.regs Reg.inputAC = 1 := by rfl
  have space : aliasedCaller.regs Reg.scratch = 2 := by rfl
  obtain ⟨y, he, _, result, frame⟩ := exec (w := 10) (n := 1) (p := 3) (scratch := 2)
    (a := 1) (b := 1) (c := 1) (A := 1) aliasedCaller
    (fun _ => -1) (fun _ => -1) (fun _ => -1) (by decide) side modulus ab bc ac space
    (by decide) (by decide) (by decide)
    (by intro i hi; decide) (by intro i hi; decide) (by intro i hi; decide)
    read read read (by decide) (by decide)
  change y.regs Reg.result = Cslib.Algorithms.ExactTriangle.countZeroMod
    (fun _ _ : Fin 1 => -1) (fun _ _ : Fin 1 => -1) (fun _ _ : Fin 1 => -1) 3 at result
  rw [show Cslib.Algorithms.ExactTriangle.countZeroMod
    (fun _ _ : Fin 1 => -1) (fun _ _ : Fin 1 => -1) (fun _ _ : Fin 1 => -1) 3 = 1 by decide]
    at result
  exact ⟨y, by simpa only [show cost 1 3 = 726 by decide] using he,
    result, frame 1 (Or.inl (by decide)), frame 32 (Or.inr (by decide))⟩

-- Modulus one is admitted even though it is not prime; every original triple is modular-zero.
example : ∃ y : Data 128, ∃ t, t + 1 ≤ 354 ∧
    Runs (admissionWidth 1 1 4) (entryProgram.program Reg.result)
      (State.init (inputWords 1 1 [-2, 1, 4])) ⟨entryProgram.size, y⟩ t ∧
    Executes (admissionWidth 1 1 4) (entryProgram.program Reg.result)
      (State.init (inputWords 1 1 [-2, 1, 4])) 1 (t + 1) := by
  obtain ⟨_, y, t, ht, run, halt, result, _, _⟩ :=
    runs_input (W := admissionWidth 1 1 4) (n := 1) (p := 1) (A := 4)
      [-2, 1, 4] (by decide) (by decide) (by decide) le_rfl
  change y.regs Reg.result = truth 1 1 [-2, 1, 4] at result
  rw [show truth 1 1 [-2, 1, 4] = 1 by decide] at result
  exact ⟨y, t, by simpa only [show cost 1 1 + 10 = 354 by decide] using ht,
    run, by simpa only [result] using halt⟩

-- The actual empty-input path still computes powers, padding and the scalar product.
example : ∃ y : Data 128, ∃ t, t + 1 ≤ 412 ∧
    Runs (admissionWidth 0 2 0) (entryProgram.program Reg.result)
      (State.init (inputWords 0 2 [])) ⟨entryProgram.size, y⟩ t ∧
    Executes (admissionWidth 0 2 0) (entryProgram.program Reg.result)
      (State.init (inputWords 0 2 [])) 0 (t + 1) := by
  obtain ⟨_, y, t, ht, run, halt, result, _, _⟩ :=
    runs_input (W := admissionWidth 0 2 0) (n := 0) (p := 2) (A := 0)
      [] (by decide) (by decide) (by decide) le_rfl
  change y.regs Reg.result = truth 0 2 [] at result
  rw [show truth 0 2 [] = 0 by decide] at result
  exact ⟨y, t, by simpa only [show cost 0 2 + 10 = 412 by decide] using ht,
    run, by simpa only [result] using halt⟩

-- The explicit source regime is admitted without any intermediate word/layout hypothesis.
example : admissionWidth 2 2 4 ≤ 25 * Nat.clog 2 4 ∧ wordBound 2 2 4 ≤ 4 ^ 26 := by
  exact ⟨admissionWidth_le_log (κ := 1) (by decide) (by decide),
    wordBound_le_pow (κ := 1) (by decide) (by decide)⟩

-- Native time really has a subcubic n exponent; the runtime p factor is retained.
example : (281 / 100 : ℝ) < 3 ∧
    ((cost 2 2 + 10 : ℕ) : ℝ) ≤ 3704 * (2 + 1 : ℝ) ^ 2 *
      (2 + 1 : ℝ) ^ (281 / 100 : ℝ) := by
  exact ⟨by norm_num, cost_le_subcubic 2 2⟩

end ComplexityTests.WordRAMCountPrimeExecution
