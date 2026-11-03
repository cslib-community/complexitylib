/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.DyadicCost
public import Complexity.Algorithms.WordRAM.ThreeSum.Decision.Intermediates

/-!
# Actual native ordinary 3SUM execution with a strict-subquadratic charge

For each fixed natural magnitude exponent, the existing ordinary host and the concrete
parameter-selecting ET callee form one fixed native standard Word-RAM program. It begins at
actual initialized canonical signed input, admits every sufficiently wide logarithmic word,
and decides the existing distinct-position integer 3SUM predicate, including repeated values.

Correctness covers every input length; only the bound `Oκ(n^(2−1/5184))` is eventual. One
coefficient and threshold precede every input and physical width. The program computes its
parameters, primes, matrices and answers; no execution, time, layout or solver law is supplied.

## Main results

* `exists_subquadratic_runs`: actual initialized prefix and charged halt, exact original verdict,
  and uniform strict-subquadratic charged steps for polynomially bounded integer inputs.

This is original conservative composition of the existing native reductions and actual ET
solver. It concerns charged standard Word-RAM instructions, not bit/Turing time or arbitrary
real-number 3SUM. It does not prove the source's tuned exponent 1.9992.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.ThreeSum (HasSolution)

/-- The fixed native program is correct at every admitted input length; its strict-subquadratic
step bound is uniform beyond one threshold per original magnitude exponent. Both actual runs
use the same initialized state and pre-halt witness, with the halt included in steps. -/
theorem exists_subquadratic_runs (κ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ¬(program κ ParameterSelecting.callee).ReadsWidth ∧ ∀ (input : List ℤ) (W : ℕ),
      width κ 123357 input.length ≤ W →
      (∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) →
      InputFits W (input.map Signed.encode) ∧ ∃ (y : Data 848) (steps : ℕ),
        Executes W (flatProgram κ ParameterSelecting.callee)
          (State.init (input.map Signed.encode)) (y.regs (controllerRegisters 633 answer)) steps ∧
        Runs W (flatProgram κ ParameterSelecting.callee)
          (State.init (input.map Signed.encode)) ⟨(program κ ParameterSelecting.callee).size, y⟩
          (steps - 1) ∧
        steps ≤ cost κ ParameterSelecting.callee input.length ∧
        (N ≤ input.length → (steps : ℝ) ≤ C * (input.length : ℝ) ^ (2 - 1 / 5184 : ℝ)) ∧
        y.regs (controllerRegisters 633 answer) ≤ 1 ∧
        (y.regs (controllerRegisters 633 answer) = 1 ↔
          HasSolution (fun i : Fin input.length => input[i])) ∧ y.Bounded W ∧
        ∀ (s : State 848) (t : ℕ),
          Runs W (flatProgram κ ParameterSelecting.callee)
            (State.init (input.map Signed.encode)) s t →
          (∀ i, s.data.regs i < (input.length + 2) ^ (2 * widthCoefficient κ 123357)) ∧
          (∀ a, s.data.mem a < (input.length + 2) ^ (2 * widthCoefficient κ 123357)) ∧
          (∀ a, (input.length + 2) ^ (2 * widthCoefficient κ 123357) ≤ a → s.data.mem a = 0) := by
  obtain ⟨C, hC, N, hc⟩ := exists_cost_subquadratic_bound κ
  refine ⟨C, hC, N, not_readsWidth κ ParameterSelecting.callee, ?_⟩
  intro input W hW' hv
  have hW : width κ ParameterSelecting.callee.widthCoefficient input.length ≤ W := by
    simpa only [ParameterSelecting.callee_widthCoefficient] using hW'
  have hi := ChanHe.Preprocessing.input_fits input
    ((preprocessing_width_le κ ParameterSelecting.callee.widthCoefficient input.length).trans hW) hv
  obtain ⟨y, steps, he, hr, ht, hb, hiff, hbounded⟩ :=
    runs_input input ParameterSelecting.callee hW hv
  refine ⟨hi, y, steps, he, hr, ht,
    fun hn => ((Nat.cast_le (α := ℝ)).mpr ht).trans (hc input.length hn), hb, hiff, hbounded, ?_⟩
  intro s t hs
  obtain ⟨hregs, hmem⟩ := intermediates_polynomial input ParameterSelecting.callee hW hv hs
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ParameterSelecting.callee_widthCoefficient] using hregs
  · simpa only [ParameterSelecting.callee_widthCoefficient] using hmem
  · intro a ha
    apply space_polynomial input ParameterSelecting.callee hW hv hs
    simpa only [ParameterSelecting.callee_widthCoefficient] using ha

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
