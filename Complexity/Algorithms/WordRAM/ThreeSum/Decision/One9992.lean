/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Transfer
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Code
public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Asymptotics

/-!
# Ordinary native integer 3SUM in time O(n^1.9992)

For each fixed polynomial magnitude exponent, one fixed standard Word-RAM program computes
all reductions, parameters, primes and answers. It runs from canonical signed original input
and decides zero-sum triples of distinct input positions, allowing repeated input values.
Correctness holds at every length and every admitted wider physical width; one time coefficient
and threshold precede all inputs and widths. The charged halt and prehalt prefix share a state.
Every such prefix has polynomial original-input words and zero support above that envelope.

The concrete automatic box callee has exponent `3-33/20000`. The actual ordinary reduction
then gives exponent `2499/1250 = 1.9992`, retaining preprocessing, every call, control and halt.
No solver, selected prime, layout, execution or time law is a hypothesis of this endpoint.

This adapts the quantitative target of `Theorem_22_3SUM` in `EndStatement.lean:94-96` at
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. Its per-magnitude-exponent
program/word/time quantifiers (`EndStatement.lean:67-70`) correspond to the outer fixed `κ`
here. The native statement uses the existing standard unsigned Word-RAM basis, canonical signed
encoding and the larger allowed bound `(n+2)^κ`; it supplies every-wide-width runs and polynomial
prefix support. Costs are unit Word-RAM instructions. The source's separate signed modular
machine and its `SolvedInTime` predicate are not imported.

## Main results

* `exists_one9992_runs`: complete initialized charged execution at exponent 1.9992.

## References

The quantitative target is Theorem 22 of [AlmanWilliams2026]; the pinned formal statement
and the native-model correspondence are identified above.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.ThreeSum (HasSolution)

/-- Explicit computable standard native code for the final ordinary 3SUM algorithm. -/
@[expose] def boxProgram (κ : ℕ) : Code .standard 848 :=
  programOfCode κ ParameterSelecting.program

/-- Its actual assembled code with one final raw Boolean halt. -/
@[expose] def boxFlatProgram (κ : ℕ) : Program .standard 848 :=
  (boxProgram κ).program (controllerRegisters 633 answer)

/-- The executable syntax is the actual code certified by the concrete callee. -/
theorem boxProgram_eq (κ : ℕ) : boxProgram κ = program κ ParameterSelecting.callee := by
  simpa only [boxProgram, ParameterSelecting.callee_code] using
    programOfCode_eq_program κ ParameterSelecting.callee

/-- Both presentations assemble the identical finite native program. -/
theorem boxFlatProgram_eq (κ : ℕ) :
    boxFlatProgram κ = flatProgram κ ParameterSelecting.callee := by
  unfold boxFlatProgram flatProgram
  rw [boxProgram_eq]

/-- The fixed native program is correct at every admitted input length; its strict-subquadratic
step bound is uniform beyond one threshold per original magnitude exponent. Both actual runs
use the same initialized state and pre-halt witness, with the halt included in steps. -/
theorem exists_one9992_runs (κ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ¬(boxProgram κ).ReadsWidth ∧ ∀ (input : List ℤ) (W : ℕ),
      width κ 123357 input.length ≤ W →
      (∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) →
      InputFits W (input.map Signed.encode) ∧ ∃ (y : Data 848) (steps : ℕ),
        Executes W (boxFlatProgram κ)
          (State.init (input.map Signed.encode)) (y.regs (controllerRegisters 633 answer)) steps ∧
        Runs W (boxFlatProgram κ)
          (State.init (input.map Signed.encode)) ⟨(boxProgram κ).size, y⟩
          (steps - 1) ∧
        steps ≤ cost κ ParameterSelecting.callee input.length ∧
        (N ≤ input.length → (steps : ℝ) ≤ C * (input.length : ℝ) ^ (2499 / 1250 : ℝ)) ∧
        y.regs (controllerRegisters 633 answer) ≤ 1 ∧
        (y.regs (controllerRegisters 633 answer) = 1 ↔
          HasSolution (fun i : Fin input.length => input[i])) ∧ y.Bounded W ∧
        ∀ (s : State 848) (t : ℕ),
          Runs W (boxFlatProgram κ)
            (State.init (input.map Signed.encode)) s t →
          (∀ i, s.data.regs i < (input.length + 2) ^ (2 * widthCoefficient κ 123357)) ∧
          (∀ a, s.data.mem a < (input.length + 2) ^ (2 * widthCoefficient κ 123357)) ∧
          (∀ a, (input.length + 2) ^ (2 * widthCoefficient κ 123357) ≤ a → s.data.mem a = 0) := by
  have hcallee : ∀ ν : ℕ, 1 ≤ ν → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ F ≤ (n + 2) ^ ν,
        (ParameterSelecting.callee.time n F : ℝ) ≤
          C * (n : ℝ) ^ (3 - 33 / 20000 : ℝ) := by
    intro ν hν
    obtain ⟨C, hC, N, -, htime⟩ := ParameterSelecting.exists_time_subcubic_bound hν
    exact ⟨C, hC, N, htime⟩
  simpa only [← boxProgram_eq κ, ← boxFlatProgram_eq κ,
    ParameterSelecting.callee_widthCoefficient] using
    exists_runs_of_callee_time ParameterSelecting.callee (δ := 33 / 20000)
      (a := 2499 / 1250) (by norm_num) (by norm_num) (by norm_num) hcallee κ

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
