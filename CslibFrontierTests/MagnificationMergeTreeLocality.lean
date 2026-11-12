/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.Magnification.MergeTree.Locality

/-!
# Tests: `MCSP[s]` in a local circuit class

For `s(n) = n + 2`, `MCSP[s]` is in the local circuit class with the merge-tree parameters. At
input length `16` (`n = 4`, `s = 6`) these are at most `342` oracle gates of fan-in at most
`15552`, at most `3` of them on any path, and at most `347` gates. The size bound is `3` at
length `0`, so `LocalCircuitClass.of_two_pow`'s side condition `1 ≤ S 0` needs no `+ 1`.
-/

namespace CslibFrontierTests.MagnificationMergeTreeLocality

open Cslib Cslib.Circuits.Boolean Cslib.MCSP

/-- `s(n) = n + 2` meets both hypotheses `n ≤ s(n)` and `2 ≤ s(n)`. -/
example :
    LocalCircuitClass (fun m => 128 * m / (Nat.log 2 m + 2) + 1)
      (fun m => 12 * (Nat.log 2 m + 2) ^ 4)
      (fun m => Nat.log 2 m / Nat.log 2 (Nat.log 2 m + 2) + 1)
      (fun m => 129 * m / (Nat.log 2 m + 2) + 3)
      (GapMCSP.yesSet (· + 2)) (GapMCSP.noSet (· + 2)) :=
  localCircuitClass_MCSP (s := (· + 2)) (fun _ => by omega) (fun _ => by omega)

/-- The parameters above at input length `16`, where `n = 4` and `s = 6`. -/
example :
    128 * 16 / (Nat.log 2 16 + 2) + 1 = 342 ∧ 12 * (Nat.log 2 16 + 2) ^ 4 = 15552 ∧
      Nat.log 2 16 / Nat.log 2 (Nat.log 2 16 + 2) + 1 = 3 ∧
      129 * 16 / (Nat.log 2 16 + 2) + 3 = 347 := by
  have h16 : Nat.log 2 16 = 4 := by
    rw [show 16 = 2 ^ 4 by rfl, Nat.log_pow (by norm_num)]
  have h6 : Nat.log 2 6 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  simp [h16, h6]

/-- At length `0` the size bound of `localCircuitClass_MCSP` is `3`, for every `s`. -/
example (s : ℕ → ℕ) : 129 * 0 / s (Nat.log 2 0) + 3 = 3 := by
  simp

end CslibFrontierTests.MagnificationMergeTreeLocality
