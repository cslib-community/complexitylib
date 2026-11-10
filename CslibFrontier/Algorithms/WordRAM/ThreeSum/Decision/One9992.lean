/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Transfer
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Admissible
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Asymptotics
public import CslibFrontier.Computability.WordRAM.Time

/-!
# Ordinary native integer 3SUM in time O(n^1.9992)

For each fixed polynomial magnitude exponent, one fixed standard Word-RAM program computes
all reductions, parameters, primes and answers. It runs from canonical signed original input
and decides zero-sum triples of distinct input positions, allowing repeated input values.
Correctness holds at every length and every physical width admitted by `Admissible`, that is
at least `width κ 123357 n` at length `n`; one time coefficient and threshold precede all inputs
and widths. The charged halt and prehalt prefix share a state.
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

* `boxFlatProgram_decidesInTime`: the fixed program decides distinct-position integer 3SUM.
* `uniformDecidableInO_one9992`: uniform decision in time O(n^1.9992).
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
  program κ ParameterSelecting.program

/-- Its actual assembled code with one final raw Boolean halt. -/
@[expose] def boxFlatProgram (κ : ℕ) : Program .standard 848 :=
  flatProgram κ ParameterSelecting.program

private theorem callee_time_subcubic (ν : ℕ) (hν : 1 ≤ ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ F ≤ (n + 2) ^ ν,
      (ParameterSelecting.callee.time n F : ℝ) ≤
        C * (n : ℝ) ^ (3 - 33 / 20000 : ℝ) := by
  obtain ⟨C, hC, N, -, htime⟩ := ParameterSelecting.exists_time_subcubic_bound hν
  exact ⟨C, hC, N, htime⟩

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
  simpa only [boxProgram, boxFlatProgram, ParameterSelecting.callee_code,
    ParameterSelecting.callee_widthCoefficient] using
    exists_runs_of_callee_time ParameterSelecting.callee (δ := 33 / 20000)
      (a := 2499 / 1250) (by norm_num) (by norm_num) (by norm_num) callee_time_subcubic κ

/-- One coefficient and threshold bound the complete charged cost, independently of physical
width. Preprocessing, all calls, outer control, and the final halt are included. -/
theorem exists_one9992_cost_bound (κ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      (cost κ ParameterSelecting.callee n : ℝ) ≤
        C * (n : ℝ) ^ (2499 / 1250 : ℝ) :=
  exists_cost_bound ParameterSelecting.callee (δ := 33 / 20000)
    (by norm_num) (by norm_num) (by norm_num) callee_time_subcubic κ

/-- The explicit fixed program decides ordinary integer 3SUM within its complete charged cost
on every admitted input, including lengths below the asymptotic threshold. -/
theorem boxFlatProgram_decidesInTime (κ : ℕ) :
    (boxFlatProgram κ).DecidesInTime (fun _ (input : List ℤ) => input.map Signed.encode)
      {input | HasSolution (fun i : Fin input.length => input[i])}
      (fun input _ => cost κ ParameterSelecting.callee input.length) (Admissible κ) := by
  intro input W h _
  obtain ⟨_, _, _, _, hrun⟩ := exists_one9992_runs κ
  obtain ⟨_, y, steps, he, _, ht, _, hbit, hiff, _, _⟩ := hrun input W h.1 h.2
  exact ⟨y.regs (controllerRegisters 633 answer), steps, he, ht, hbit, hiff⟩

/-- Uniform standard Word-RAM decision in O(n^1.9992) instructions for polynomially bounded
signed integers. The natural ceiling only expresses the real power in the existing natural-valued
time API; its coefficient and threshold are shared by all admitted physical widths. -/
theorem uniformDecidableInO_one9992 (κ : ℕ) :
    UniformDecidableInO .standard
      {input : List ℤ | HasSolution (fun i : Fin input.length => input[i])}
      (fun _ input => input.map Signed.encode) List.length
      (fun n _ => ⌈(n : ℝ) ^ (2499 / 1250 : ℝ)⌉₊) (Admissible κ) := by
  obtain ⟨C, hC, N, hcost⟩ := exists_one9992_cost_bound κ
  refine ⟨fun input _ => cost κ ParameterSelecting.callee input.length,
    ⟨848, boxFlatProgram κ, boxFlatProgram_decidesInTime κ⟩,
    ⌈C⌉₊, N, Nat.ceil_pos.mpr hC, ?_⟩
  intro input W hn _
  apply (Nat.cast_le (α := ℝ)).mp
  push_cast
  exact (hcost input.length hn).trans
    (mul_le_mul (Nat.le_ceil C) (Nat.le_ceil _) (Real.rpow_nonneg (by positivity) _)
      (by positivity))

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
