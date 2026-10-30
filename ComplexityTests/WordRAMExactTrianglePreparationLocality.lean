/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationLocality
import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationInput

/-!
# Actual prepared readback survives a dirty heap cell

This small producer-only client distinguishes protected readback from the producer's original
external frame. The full thin-solver clients retain their valid positive geometry elsewhere.
-/

namespace ComplexityTests.WordRAMExactTrianglePreparationLocality

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ExactTriangle

example : ∃ a z : Data 64,
    ExecWithin (PreparationInput.width 1 1 1 2 0) Instances.program
      (.init (PreparationInput.input 1 1 1 2 [0, 0, 0])) a
      (Instances.timeBound 1 1 2 1 1 - 1) ∧
    Instances.Output 1 1 1 2 (fun q => ([0, 0, 0] : List ℤ).getD q 0) z z ∧
    z.mem (a.regs Instances.heap) = 77 ∧
    ¬ Instances.Output 1 1 1 2 (fun q => ([0, 0, 0] : List ℤ).getD q 0)
      (.init (PreparationInput.input 1 1 1 2 [0, 0, 0])) z := by
  obtain ⟨a, ha, hout, _, _⟩ := PreparationInput.exec_input (n := 1) (D := 1) (g := 1)
    (p := 2) (A := 0) (W := PreparationInput.width 1 1 1 2 0) [0, 0, 0]
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with h | h | h <;> subst v <;> decide) le_rfl
  let z := a.write (a.regs Instances.heap) 77
  have hmem : Set.EqOn z.mem a.mem (Set.Iio (a.regs Instances.heap)) := by
    intro u hu
    change Function.update a.mem (a.regs Instances.heap) 77 u = a.mem u
    exact Function.update_of_ne (by change u < a.regs Instances.heap at hu; omega) _ _
  have hnew := hout.reframe (z := z) (fun q => ([0, 0, 0] : List ℤ).getD q 0) rfl hmem
  have dirty : z.mem (a.regs Instances.heap) = 77 := by
    simp only [z, Data.write_mem, Function.update_self]
  have hheap : 17 ≤ a.regs Instances.heap := by
    have hh := hout.2.2.2.2.2.1
    change a.regs Instances.heap = _ + _ at hh
    omega
  have old_zero : (Data.init (PreparationInput.input 1 1 1 2 [0, 0, 0]) : Data 64).mem
      (a.regs Instances.heap) = 0 := by
    cases he : a.regs Instances.heap with
    | zero => omega
    | succ u =>
      change (PreparationInput.input 1 1 1 2 [0, 0, 0]).getD u 0 = 0
      apply List.getD_eq_default
      have hu : 7 ≤ u := by omega
      exact hu
  refine ⟨a, z, ?_, hnew, dirty, ?_⟩
  · convert ha using 1
    decide
  · intro hbad
    have he := hbad.2.2.2.2.2.2.2.2.2.2.2 (a.regs Instances.heap)
      (Or.inr hout.2.2.2.2.2.1.ge)
    rw [dirty, old_zero] at he
    contradiction

end ComplexityTests.WordRAMExactTrianglePreparationLocality
