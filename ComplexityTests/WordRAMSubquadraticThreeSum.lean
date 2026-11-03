/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Subquadratic

/-!
# Admitted initialized ordinary 3SUM at the strict-subquadratic charge

Constant zero inputs of every admitted large length return one, using three distinct positions
with repeated values. Positive-one and negative-one inputs return zero at the same uniform
asymptotic charge. The two-zero boundary client returns zero because positions must be distinct.
These are kernel-checked clients of the actual initialized program, not supplied executions,
restatements of signatures or enormous VM fixtures.
-/

namespace ComplexityTests.WordRAMSubquadraticThreeSum

open Cslib.WordRAM Cslib.Algorithms.ThreeSum
open Cslib.Algorithms.WordRAM.ThreeSum.Decision
open Cslib.Algorithms.WordRAM.ExactTriangle

private def values (n : ℕ) (z : ℤ) : List ℤ := List.replicate n z
private def W (n : ℕ) : ℕ := width 1 123357 n

private theorem constant_solution_iff {n : ℕ} (hn : 3 ≤ n) (z : ℤ) :
    HasSolution (fun _ : Fin n => z) ↔ z = 0 := by
  constructor
  · rintro ⟨i, j, k, _, _, _, h⟩
    change z + z + z = 0 at h
    omega
  · intro hz
    refine ⟨(⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n), (⟨2, by omega⟩ : Fin n),
      by simp, by simp, by simp, ?_⟩
    simp [hz]

private def TimedConstant (z : ℤ) (answer : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 3 ≤ N ∧ ∀ n ≥ N,
    ∃ (y : Data 848) (steps : ℕ),
      InputFits (W n) ((values n z).map Signed.encode) ∧
      Executes (W n) (flatProgram 1 ParameterSelecting.callee)
        (State.init ((values n z).map Signed.encode)) answer steps ∧
      Runs (W n) (flatProgram 1 ParameterSelecting.callee)
        (State.init ((values n z).map Signed.encode))
        ⟨(program 1 ParameterSelecting.callee).size, y⟩ (steps - 1) ∧
      (steps : ℝ) ≤ C * (n : ℝ) ^ (2 - 1 / 5184 : ℝ) ∧
      y.regs (controllerRegisters 633 Cslib.Algorithms.WordRAM.ThreeSum.Decision.answer) = answer

private theorem timed_constant (z : ℤ) (hz : |z| ≤ (1 : ℤ)) :
    TimedConstant z (if z = 0 then 1 else 0) := by
  obtain ⟨C, hC, N, _, hrun⟩ := exists_subquadratic_runs 1
  refine ⟨C, hC, max N 3, le_max_right _ _, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn3 : 3 ≤ n := (le_max_right _ _).trans hn
  have hv : ∀ v ∈ values n z, |v| ≤ (((values n z).length + 2) ^ 1 : ℕ) := by
    intro v hv
    have heq : v = z := (List.mem_replicate.mp hv).2
    subst v
    simp only [values, List.length_replicate, pow_one]
    exact hz.trans (by omega)
  obtain ⟨hi, y, steps, he, hr, _, ht, hb, hiff, hbounded, hprefix⟩ :=
    hrun (values n z) (W n) (by simp only [values, List.length_replicate, W]; rfl) hv
  have ht' : (steps : ℝ) ≤ C * (n : ℝ) ^ (2 - 1 / 5184 : ℝ) := by
    simpa only [values, List.length_replicate] using ht (by simpa only [values,
      List.length_replicate] using hnN)
  have hiff' : y.regs (controllerRegisters 633 answer) = 1 ↔ z = 0 := by
    have hiff0 : y.regs (controllerRegisters 633 answer) = 1 ↔
        HasSolution (fun _ : Fin (values n z).length => z) := by
      simpa only [values, Fin.getElem_fin, List.getElem_replicate] using hiff
    exact hiff0.trans (constant_solution_iff (by simpa only [values,
      List.length_replicate] using hn3) z)
  have hans : y.regs (controllerRegisters 633 answer) = (if z = 0 then 1 else 0) := by
    split_ifs with hz0
    · exact hiff'.mpr hz0
    · have hnot : y.regs (controllerRegisters 633 answer) ≠ 1 :=
        fun h => hz0 (hiff'.mp h)
      omega
  exact ⟨y, steps, hi, by simpa only [hans] using he, hr, ht', hans⟩

example : TimedConstant 0 1 := by simpa using timed_constant 0 (by decide)
example : TimedConstant 1 0 := by simpa using timed_constant 1 (by decide)
example : TimedConstant (-1) 0 := by simpa using timed_constant (-1) (by decide)

example : ∃ (y : Data 848) (steps : ℕ),
    Executes (W 2) (flatProgram 1 ParameterSelecting.callee)
      (State.init ([0, 0].map Signed.encode)) 0 steps ∧
    Runs (W 2) (flatProgram 1 ParameterSelecting.callee)
      (State.init ([0, 0].map Signed.encode))
      ⟨(program 1 ParameterSelecting.callee).size, y⟩ (steps - 1) := by
  obtain ⟨_, _, _, _, hrun⟩ := exists_subquadratic_runs 1
  obtain ⟨_, y, steps, he, hr, _, _, hb, hiff, _, _⟩ :=
    hrun [0, 0] (W 2) (by decide) (by simp)
  have hno : ¬HasSolution (fun _ : Fin 2 => (0 : ℤ)) := by
    dsimp only [HasSolution]
    decide
  have hans : y.regs (controllerRegisters 633 answer) = 0 := by
    have hnot : y.regs (controllerRegisters 633 answer) ≠ 1 := by
      intro h
      apply hno
      have hs := hiff.mp h
      change HasSolution (fun i : Fin 2 => (List.replicate 2 (0 : ℤ))[i]) at hs
      simpa only [Fin.getElem_fin, List.getElem_replicate] using hs
    omega
  exact ⟨y, steps, by simpa only [hans] using he, hr⟩

end ComplexityTests.WordRAMSubquadraticThreeSum
