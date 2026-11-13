/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Complexity.Problems.Permanent.ZeroOne

/-! Checked clients of Goldreich's Proposition 6.22: integer permanents from 0/1 permanents. -/

namespace CslibFrontierTests.PermanentZeroOne

open Cslib.Complexity Turing.MultiTapeTM

/-- The `1 × 1` table `[[2]]` becomes a `5 × 5` 0/1 table: the original vertex, then a doubling
and a relay vertex for each of the two bits of `2`. -/
example : natTableToZeroOne [[2]] =
    [[false, true, false, false, false],
     [true, true, true, false, false],
     [true, false, true, false, false],
     [false, true, false, true, true],
     [false, true, false, false, true]] := by
  decide

/-- Its permanent is the original entry. -/
example : ZeroOnePermanent (natTableToZeroOne [[2]]) = 2 := by
  rw [zeroOnePermanent_natTableToZeroOne]
  simp [Matrix.permanent, tableMatrix_apply]

/-- A negative entry is recovered from the residue of the 0/1 permanent. -/
example : recoverPermanent ([[-3]], ZeroOnePermanent (intTableToZeroOne [[-3]])) = -3 := by
  rw [← intPermanent_eq_recoverPermanent_intTableToZeroOne]
  simp [IntPermanent, Matrix.permanent, tableMatrix_apply]

/-- The dimension of the 0/1 table is `n + 2 L n²`. -/
example (A : List (List ℕ)) :
    (natTableToZeroOne A).length = A.length + 2 * natChainLength A * (A.length * A.length) :=
  length_natTableToZeroOne A

/-- The query and recovery maps are native polynomial-time machines under the dense encodings. -/
example : ComputableInPolyTime intTableToZeroOne encIntTable encBoolTable :=
  computableInPolyTime_intTableToZeroOne

example : ComputableInPolyTime recoverPermanent (encPair encIntTable encNat) encIntBin :=
  computableInPolyTime_recoverPermanent

/-- Proposition 6.22 as a metric reduction, composed with a metric reduction into the integer
permanent: anything reducing to `IntPermanent` reduces to `ZeroOnePermanent`. -/
example {α Y : Type} {enc : α ↪ List Bool} {encY : Y ↪ List Bool} {f : α → Y}
    (h : MetricReducible enc encIntTable encY encIntBin f IntPermanent) :
    MetricReducible enc encBoolTable encY encNat f ZeroOnePermanent :=
  h.trans metricReducible_intPermanent_zeroOnePermanent

/-- The nonnegative step alone is parsimonious. -/
example : ParsimoniousReducible encNatTable encBoolTable NatPermanent ZeroOnePermanent :=
  parsimoniousReducible_natPermanent_zeroOnePermanent

end CslibFrontierTests.PermanentZeroOne
