/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Foundations.BooleanAnalysis.OddForm

/-!
Odd-parity forms on the cube and functions supported on the unit vectors `Pi.single i true`.
-/

open Cslib Cslib.BitString Finset

namespace BooleanAnalysisOddFormTests

-- The parity of a unit vector on `S` is membership in `S`.
example : parityOn ({0, 2} : Finset (Fin 3)) (Pi.single 2 true) = true := by
  simp [parityOn_single]

example : parityOn ({0, 2} : Finset (Fin 3)) (Pi.single 1 true) = false := by
  simp [parityOn_single]

-- `onSingles a` is `a i` at `Pi.single i true` and `0` at the zero vector; its odd-parity form on
-- `S` is the block sum `∑_{i ∈ S} a i`, so its total over all sets is `2 ^ (|ι| - 1) ∑ a`.
example (a : Fin 3 → ℝ) : onSingles a (Pi.single 1 true) = a 1 := onSingles_single a 1

example (a : Fin 3 → ℝ) : onSingles a 0 = 0 := onSingles_zero a

example (a : Fin 3 → ℝ) : oddForm (onSingles a) {0, 2} = a 0 + a 2 := by
  rw [oddForm_onSingles, sum_pair (by decide)]

example (a : Fin 3 → ℝ) :
    2 * ∑ S, oddForm (onSingles a) S = 2 ^ 3 * ∑ i, a i := by
  rw [two_mul_sum_oddForm, onSingles_zero, sub_zero, Fintype.card_fin]
  simpa using sum_onSingles_mul a fun _ => 1

-- Two distinct nonzero points are both odd on a quarter of the `2 ^ 3` sets.
example : 4 * ∑ S : Finset (Fin 3), ((parityOn S (Pi.single 0 true)).toNat : ℝ) *
    (parityOn S (Pi.single 1 true)).toNat = 2 ^ 3 := by
  rw [four_mul_sum_toNat_parityOn_mul]
  have h0 : (Pi.single 0 true : Fin 3 → Bool) ≠ Pi.single 1 true :=
    fun h => by simpa using congrFun h 0
  simp [h0]

end BooleanAnalysisOddFormTests
