/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime.Flat
public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.NumericBounds

/-!
# Original-input bounds for every fixed-prime native prefix

The admission remains logarithmic for polynomial original weights and bounded scalar headers.
The actual minimum-width halting run controls all wider prefixes, including dirty loads and
all reused-workspace calls. The support envelope is independent of the physical width, and
does not instruct the machine to clear or snapshot that range.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Every actually reached state at every admitted wider width has the same original-input
polynomial word/support envelope. The concrete minimum-width run, not an assumed execution
certificate, supplies the comparison run. -/
theorem bounded_reachable_original {W m n g p A k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : FixedPrime.admissionWidth n (D m) g p A ≤ W)
    {s : State 416} (hr : Runs W (program.program FixedPrime.Reg.found)
      (State.init (PreparationInput.input n (D m) g p values)) s k) :
    (∀ i, s.data.regs i < FixedPrime.wordBound n (D m) g p A) ∧
      (∀ a, s.data.mem a < FixedPrime.wordBound n (D m) g p A) ∧
      ∀ a, FixedPrime.wordBound n (D m) g p A ≤ a → s.data.mem a = 0 := by
  obtain ⟨hi, a, hout, y, t, ht, hpref, he, -⟩ :=
    runs_input values hlen hD hg hp hN hv le_rfl
  exact hr.prefix_bounds_init program_fixed.2 hW hi he le_rfl

end Cslib.Algorithms.WordRAM.ExactTriangle.StreamingFixedPrime
