/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Runtime
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Intermediates

/-!
# Initialized ordinary 3SUM execution from a quantitative callee bound

A concrete certified callee with uniform polynomial-weight saving δ supplies the actual native
ordinary host at every admitted input length and width. The eventual charged exponent may be
any a > 2-δ/2, for 0 < δ ≤ 1. Prefix, halt and verdict share one state; word and zero-support
bounds are polynomial in the original input, independently of the physical width.

## Main results

* `exists_runs_of_callee_time`: initialized charged execution with the requested exponent.

A consumer must discharge the quantitative premise using its actual native callee theorem.
The generic proof imports no particular supplier, solver or selected-prime implementation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM
open Cslib.Algorithms.ThreeSum (HasSolution)

/-- The fixed native program is correct at every admitted input length; its requested-exponent
step bound is uniform beyond one threshold per original magnitude exponent. Both actual runs
use the same initialized state and pre-halt witness, with the halt included in steps. -/
theorem exists_runs_of_callee_time {r : ℕ} (c : Host.Callee r) {δ a : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 2 - δ / 2 < a)
    (hc : ∀ κ : ℕ, 1 ≤ κ → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ∀ n ≥ N, ∀ F ≤ (n + 2) ^ κ,
        (c.time n F : ℝ) ≤ C * (n : ℝ) ^ (3 - δ)) (κ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
      ¬(program κ c.code).ReadsWidth ∧ ∀ (input : List ℤ) (W : ℕ),
      width κ c.widthCoefficient input.length ≤ W →
      (∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) →
      InputFits W (input.map Signed.encode) ∧ ∃ (y : Data (registerCount r)) (steps : ℕ),
        Executes W (flatProgram κ c.code)
          (State.init (input.map Signed.encode))
          (y.regs (controllerRegisters r answer)) steps ∧
        Runs W (flatProgram κ c.code)
          (State.init (input.map Signed.encode)) ⟨(program κ c.code).size, y⟩
          (steps - 1) ∧
        steps ≤ cost κ c input.length ∧
        (N ≤ input.length → (steps : ℝ) ≤ C * (input.length : ℝ) ^ a) ∧
        y.regs (controllerRegisters r answer) ≤ 1 ∧
        (y.regs (controllerRegisters r answer) = 1 ↔
          HasSolution (fun i : Fin input.length => input[i])) ∧ y.Bounded W ∧
        ∀ (s : State (registerCount r)) (t : ℕ),
          Runs W (flatProgram κ c.code)
            (State.init (input.map Signed.encode)) s t →
          (∀ i, s.data.regs i < (input.length + 2) ^ (2 * widthCoefficient κ c.widthCoefficient)) ∧
          (∀ a, s.data.mem a < (input.length + 2) ^ (2 * widthCoefficient κ c.widthCoefficient)) ∧
          (∀ a, (input.length + 2) ^ (2 * widthCoefficient κ c.widthCoefficient) ≤ a →
            s.data.mem a = 0) := by
  obtain ⟨C, hC, N, hc⟩ := exists_cost_bound c hδ hδ1 ha hc κ
  refine ⟨C, hC, N, not_readsWidth κ c, ?_⟩
  intro input W hW hv
  have hi := ChanHe.Preprocessing.input_fits input
    ((preprocessing_width_le κ c.widthCoefficient input.length).trans hW) hv
  obtain ⟨y, steps, he, hr, ht, hb, hiff, hbounded⟩ :=
    runs_input input c hW hv
  refine ⟨hi, y, steps, he, hr, ht,
    fun hn => ((Nat.cast_le (α := ℝ)).mpr ht).trans (hc input.length hn), hb, hiff, hbounded, ?_⟩
  exact fun s t hs => prefix_polynomial input c hW hv hs

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
