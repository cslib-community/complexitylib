/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Input

/-!
# Flat standard-WordRAM clients for the complete encoders

## Main results

* `Encoding.runs_left`, `Encoding.runs_right`: actual flat runs from `State.init`, the complete
  output memory block, preserved outside frame, and a charged final halt.
* `Encoding.program_length_le`: one finite code-size bound independent of depth and width.

The final halt returns the output block's address. Its length is `10^L` and its cells contain
the canonical signed encodings of the public mathematical values.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

set_option maxRecDepth 4096 in
-- Kernel reduction flattens the finite instruction list, including each signed arithmetic block.
/-- A single code-size bound for both fixed encoders, including the final halt. -/
theorem program_length_le (side : Bool) : ((program side).program output).length ≤ 4096 := by
  cases side <;> decide

/-- Every one of the `10^L` flat output cells corresponds to exactly one original leaf. -/
theorem leafIndex_bijective (L : ℕ) : Function.Bijective (leafIndex (L := L)) := by
  have h : Function.Bijective (fun τ : Leaf L => fun i => termDigits.symm (τ i)) :=
    (Equiv.piCongrRight fun _ : Fin L => termDigits.symm).bijective
  change Function.Bijective (fun τ : Leaf L =>
    finFunctionFinEquiv (fun i => termDigits.symm (τ i)))
  exact finFunctionFinEquiv.bijective.comp h

/-- Actual flat native left-encoding execution. The prefix exposes every output memory cell;
the same run then halts at its fixed final instruction, charging one more instruction. -/
theorem runs_left {w L : ℕ} (hw : 0 < w) (a : LeftStr L → ℤ) (A : ℤ)
    (hA : 0 ≤ A) (ha : ∀ u, |a u| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L)) :
    InputFits (w + 2) (inputL a) ∧
    ∃ y n, n ≤ timeBound L ∧
      Runs (w + 2) ((program false).program output) (State.init (inputL a))
        ⟨(program false).size, y⟩ n ∧
      Executes (w + 2) ((program false).program output) (State.init (inputL a))
        (outputBase L) (n + 1) ∧
      (∀ τ, y.mem (outputBase L + (leafIndex τ).val) = encode (encodingL a τ)) ∧
      (∀ b, ¬(outputBase L ≤ b ∧ b < scratchBase L + 10 ^ L) →
        y.mem b = (State.init (inputL a) : State 32).data.mem b) := by
  obtain ⟨hi, y, ⟨n, hn, he⟩, _, hv, hf, ho, _⟩ := exec_left hw a A hA ha hmag haddr
  refine ⟨hi, y, n, hn, ?_, ?_, hv, hf⟩
  · simpa only [Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := (program false).program output) (Program.Contains.self _).append_left
  · simpa only [ho, State.init] using he.executes output

/-- Actual flat native right-encoding execution, with all output cells and the same charged
standard-WordRAM calling convention and final halt. -/
theorem runs_right {w L : ℕ} (hw : 0 < w) (a : RightStr L → ℤ) (A : ℤ)
    (hA : 0 ≤ A) (ha : ∀ u, |a u| ≤ A)
    (hmag : (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (haddr : Fits (w + 2) (addressBound L)) :
    InputFits (w + 2) (inputR a) ∧
    ∃ y n, n ≤ timeBound L ∧
      Runs (w + 2) ((program true).program output) (State.init (inputR a))
        ⟨(program true).size, y⟩ n ∧
      Executes (w + 2) ((program true).program output) (State.init (inputR a))
        (outputBase L) (n + 1) ∧
      (∀ τ, y.mem (outputBase L + (leafIndex τ).val) = encode (encodingR a τ)) ∧
      (∀ b, ¬(outputBase L ≤ b ∧ b < scratchBase L + 10 ^ L) →
        y.mem b = (State.init (inputR a) : State 32).data.mem b) := by
  obtain ⟨hi, y, ⟨n, hn, he⟩, _, hv, hf, ho, _⟩ := exec_right hw a A hA ha hmag haddr
  refine ⟨hi, y, n, hn, ?_, ?_, hv, hf⟩
  · simpa only [Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := (program true).program output) (Program.Contains.self _).append_left
  · simpa only [ho, State.init] using he.executes output

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
