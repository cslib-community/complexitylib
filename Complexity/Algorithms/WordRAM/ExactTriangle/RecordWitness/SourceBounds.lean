/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Flat
public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.NumericBounds

/-!
# All-prefix word and support bounds for candidate recovery

Every reachable prefix of the initialized producer/product/verifier at any admitted wider width
satisfies the original-input word and memory-support bound `wordBound`, derived from the
minimum-width halting run `runs_input` and width-independent prefix transport. The numerical
logarithmic width and polynomial word estimates (`admissionWidth_le_log`, `wordBound_le_pow`) live
in `RecordWitness.NumericBounds`.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- At every admitted wider width, every actual prefix has original-input polynomial words
and zero memory above the same original-input envelope. Dirty pre-normalization loads are
included because the entire actual native execution is compared with its minimum-width run. -/
theorem bounded_reachable_original {W m n g p A k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W)
    {s : State 400} (hr : Runs W (entryProgram.program Reg.found)
      (State.init (PreparationInput.input n (D m) g p values)) s k) :
    (∀ i, s.data.regs i < wordBound n (D m) g p A) ∧
      (∀ a, s.data.mem a < wordBound n (D m) g p A) ∧
      ∀ a, wordBound n (D m) g p A ≤ a → s.data.mem a = 0 := by
  obtain ⟨hi, a, idx, ha, hout, hidx, hord, y, t, S, ht, hpref, he, -⟩ :=
    runs_input values hlen hD hg hp hN hv le_rfl
  exact hr.prefix_bounds_init entryProgram_fixed.2 hW hi he le_rfl

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
