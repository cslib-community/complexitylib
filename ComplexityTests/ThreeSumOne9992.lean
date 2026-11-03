/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ThreeSum.Decision.One9992
import Mathlib.Tactic.FinCases

/-!
# Actual ordinary 3SUM clients at the completed exponent

These clients use the real automatic box callee from original signed lists. Empty and short
inputs evaluate the complete program's existing early rejection. Checked kernel fixtures
then retain the actual prefix and halt for repeated-value success and nonzero/short failures.
The theorem's uniform eventual charge is carried by the same successful run witness.
Semantic clients use the standard decision API at arbitrary admitted wider words and discharge
its input-fit premise from `Admissible`, rather than assuming it separately.
-/

namespace ComplexityTests.ThreeSumOne9992

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ThreeSum
open Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.ThreeSum (HasSolution)

-- The concrete final program rejects fewer than three positions before any ET call.
/-- info: true -/
#guard_msgs in
#eval decide (run 4 (Decision.boxFlatProgram 1) 10
  (State.init ([] : List ℕ)) = some (0, 7))

/-- info: true -/
#guard_msgs in
#eval decide (run 4 (Decision.boxFlatProgram 1) 10
  (State.init [Signed.encode 0, Signed.encode 0]) = some (0, 7))

/-- The compact decision contract accepts repeated values at distinct positions, at every
admitted wider physical word size. -/
theorem repeatedValue_answers {W : ℕ} (hW : Decision.width 1 123357 3 ≤ W) :
    (Decision.boxFlatProgram 1).Answers W
      (([-2, 1, 1] : List ℤ).map Signed.encode) True
      (Decision.cost 1 ParameterSelecting.callee 3) := by
  have ha : Decision.Admissible 1 [-2, 1, 1] W := by
    refine ⟨hW, ?_⟩
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> decide
  have h := Decision.boxFlatProgram_decidesInTime 1 [-2, 1, 1] W ha ha.inputFits
  apply h.congr
  exact iff_true_intro ⟨0, 1, 2, by decide, by decide, by decide, by decide⟩

/-- The same semantic contract rejects an empty list; correctness is not restricted to the
eventual complexity range. -/
theorem empty_answers {W : ℕ} (hW : Decision.width 1 123357 0 ≤ W) :
    (Decision.boxFlatProgram 1).Answers W [] False
      (Decision.cost 1 ParameterSelecting.callee 0) := by
  have ha : Decision.Admissible 1 [] W := ⟨hW, by simp⟩
  have h := Decision.boxFlatProgram_decidesInTime 1 [] W ha ha.inputFits
  apply h.congr
  exact iff_false_intro (by rintro ⟨i, _⟩; exact Fin.elim0 i)

-- Polynomial magnitude is an actual input restriction, independently of available width.
example (W : ℕ) : ¬Decision.Admissible 1 [6, 0, 0] W := by
  intro h
  have := h.2 6 (by simp)
  norm_num at this

private theorem checked_case (input : List ℤ) (bit : ℕ) (hbit : bit ≤ 1)
    (hv : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ 1 : ℕ))
    (hspec : HasSolution (fun i : Fin input.length => input[i]) ↔ bit = 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∃ y : Data 848, ∃ steps : ℕ,
      Executes (Decision.width 1 123357 input.length)
        (Decision.boxFlatProgram 1)
        (State.init (input.map Signed.encode)) bit steps ∧
      Runs (Decision.width 1 123357 input.length)
        (Decision.boxFlatProgram 1)
        (State.init (input.map Signed.encode))
        ⟨(Decision.boxProgram 1).size, y⟩ (steps - 1) ∧
      steps ≤ Decision.cost 1 ParameterSelecting.callee input.length ∧
      (N ≤ input.length → (steps : ℝ) ≤ C * (input.length : ℝ) ^ (2499 / 1250 : ℝ)) ∧
      y.Bounded (Decision.width 1 123357 input.length) := by
  obtain ⟨C, hC, N, -, hrun⟩ := Decision.exists_one9992_runs 1
  obtain ⟨hi, y, steps, he, hr, ht, htime, hflag, hiff, hb, -⟩ :=
    hrun input (Decision.width 1 123357 input.length) le_rfl hv
  have flag : y.regs (Decision.controllerRegisters 633 Decision.answer) = bit := by
    by_cases h : bit = 1
    · exact (hiff.mpr (hspec.mpr h)).trans h.symm
    · have hn := hspec.not.mpr h
      have hy := hiff.not.mpr hn
      omega
  refine ⟨C, hC, N, y, steps, ?_, hr, ht, htime, hb⟩
  simpa only [flag] using he

-- Distinct positions with repeated input values are a genuine positive instance.
example : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∃ y : Data 848, ∃ steps : ℕ,
    Executes (Decision.width 1 123357 3) (Decision.boxFlatProgram 1)
      (State.init (([-2, 1, 1] : List ℤ).map Signed.encode)) 1 steps ∧
    Runs (Decision.width 1 123357 3) (Decision.boxFlatProgram 1)
      (State.init (([-2, 1, 1] : List ℤ).map Signed.encode))
      ⟨(Decision.boxProgram 1).size, y⟩ (steps - 1) ∧
    steps ≤ Decision.cost 1 ParameterSelecting.callee 3 ∧
    (N ≤ 3 → (steps : ℝ) ≤ C * (3 : ℝ) ^ (2499 / 1250 : ℝ)) ∧
    y.Bounded (Decision.width 1 123357 3) := by
  apply checked_case [-2, 1, 1] 1 (by decide)
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> decide
  · have hs : HasSolution (fun i : Fin 3 => ([-2, 1, 1] : List ℤ)[i]) :=
      ⟨0, 1, 2, by decide, by decide, by decide, by decide⟩
    exact iff_of_true hs rfl

-- A nonzero constant array has no original zero triple.
example : ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∃ y : Data 848, ∃ steps : ℕ,
    Executes (Decision.width 1 123357 3) (Decision.boxFlatProgram 1)
      (State.init (([1, 1, 1] : List ℤ).map Signed.encode)) 0 steps ∧
    Runs (Decision.width 1 123357 3) (Decision.boxFlatProgram 1)
      (State.init (([1, 1, 1] : List ℤ).map Signed.encode))
      ⟨(Decision.boxProgram 1).size, y⟩ (steps - 1) ∧
    steps ≤ Decision.cost 1 ParameterSelecting.callee 3 ∧
    (N ≤ 3 → (steps : ℝ) ≤ C * (3 : ℝ) ^ (2499 / 1250 : ℝ)) ∧
    y.Bounded (Decision.width 1 123357 3) := by
  apply checked_case [1, 1, 1] 0 (by decide)
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> decide
  · have hn : ¬HasSolution (fun i : Fin 3 => ([1, 1, 1] : List ℤ)[i]) := by
      rintro ⟨i, j, k, -, -, -, hz⟩
      have value (u : Fin 3) : ([1, 1, 1] : List ℤ)[u] = 1 := by fin_cases u <;> rfl
      simp only [value] at hz
      norm_num at hz
    exact iff_of_false hn (by decide)

end ComplexityTests.ThreeSumOne9992
