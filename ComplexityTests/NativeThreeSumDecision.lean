/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ThreeSum.Decision

/-! # Live complete ordinary-host clients

Every callee premise is supplied by the actual proved finite exhaustive block. These clients
exercise initialized execution and the existing distinct-position predicate, rather than an
abstract whole-host solver hypothesis. Tiny inputs also run through the actual flat interpreter.
-/

namespace ComplexityTests.NativeThreeSumDecision

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ThreeSum
open Cslib.Algorithms.ThreeSum (HasSolution)

private def live : Host.Callee 17 := Host.Slow.callee

-- Small-input execution is intentional and does not erase preprocessing instance lists.
/-- info: true -/
#guard_msgs in
#eval decide ((run 4 (Decision.flatProgram 1 live) 10 (State.init ([] : List ℕ))) = some (0, 7))

/-- info: true -/
#guard_msgs in
#eval decide ((run 4 (Decision.flatProgram 1 live) 10 (State.init [Signed.encode 0])) = some (0, 7))

/-- info: true -/
#guard_msgs in
#eval decide ((run 4 (Decision.flatProgram 1 live) 10
  (State.init [Signed.encode 0, Signed.encode 0])) = some (0, 7))

-- Repeated values are allowed; only positions must be different.
example : ∃ (y : Data (Decision.registerCount 17)) (steps : ℕ),
    Executes (Decision.width 1 live.widthCoefficient 3) (Decision.flatProgram 1 live)
      (State.init (([-2, 1, 1] : List ℤ).map Signed.encode)) 1 steps ∧
    Runs (Decision.width 1 live.widthCoefficient 3) (Decision.flatProgram 1 live)
      (State.init (([-2, 1, 1] : List ℤ).map Signed.encode))
      ⟨(Decision.program 1 live).size, y⟩ (steps - 1) ∧ steps ≤ Decision.cost 1 live 3 := by
  obtain ⟨y, steps, he, hr, ht, _, hans, _⟩ := Decision.runs_input (κ := 1)
    [-2, 1, 1] live le_rfl (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> decide)
  have hs : HasSolution (fun i : Fin 3 => ([-2, 1, 1] : List ℤ)[i]) :=
    ⟨0, 1, 2, by decide, by decide, by decide, by decide⟩
  rw [hans.mpr hs] at he
  exact ⟨y, steps, he, hr, ht⟩

example : ∃ steps, Executes (Decision.width 1 live.widthCoefficient 3)
    (Decision.flatProgram 1 live)
    (State.init (([1, 1, 1] : List ℤ).map Signed.encode)) 0 steps ∧
    steps ≤ Decision.cost 1 live 3 := by
  obtain ⟨y, steps, he, _, ht, hb, hans, _⟩ := Decision.runs_input (κ := 1)
    [1, 1, 1] live le_rfl (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl <;> decide)
  have hn : ¬HasSolution (fun i : Fin 3 => ([1, 1, 1] : List ℤ)[i]) := by
    rintro ⟨i, j, k, _, _, _, h⟩
    have hv (u : Fin 3) : ([1, 1, 1] : List ℤ)[u] = 1 := by fin_cases u <;> rfl
    simp only [hv] at h
    norm_num at h
  have h0 : y.regs (Decision.controllerRegisters 17 Decision.answer) = 0 := by
    have := hans.not.mpr hn
    omega
  rw [h0] at he
  exact ⟨steps, he, ht⟩

end ComplexityTests.NativeThreeSumDecision
