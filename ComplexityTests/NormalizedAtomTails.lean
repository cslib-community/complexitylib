/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
-- upstream: candidate

import Complexity.Foundations.Probability.NormalizedAtomRows.ClippedTail

/-! Nonconstant correlated endpoint moments and genuine zero-extension behavior.
The exact moment catches an invalid independence/rarity discount on noise. -/

open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators

namespace NormalizedAtomTailsTests

/-- The same Boolean seed controls both factors; their product has fourth moment 257/2. -/
example : rowNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True)
    (fun (_ : Bool) (_ : Unit) => True)
    (fun σ (_ _ : Unit) => (if σ then (2 : ℝ) else 1) * (if σ then 2 else 1)) = 257 / 2 := by
  norm_num [rowNormPow, expect, Fintype.univ_bool]
  norm_num [NNRat.smul_def]

/-- A nonzero first coordinate and changing retained second coordinate telescope exactly;
zero extension is literal on the other endpoint. -/
example (i : ℕ) (y : Bool) :
    uncompressedRow (fun j z ν => if ν = 0 then (1 : ℝ) else
      (if z then (j + 1 : ℕ) else 0) - (if j = 0 then 0 else if z then j else 0))
      (fun _ _ => 0) (i + 1) y 1 = (if y then ((i + 1 : ℕ) : ℝ) else 0) := by
  simpa only [Nat.cast_zero] using uncompressed_second_telescope
    (fun j z => if z then (j : ℝ) else 0) (fun _ _ => (1 : ℝ)) (fun _ _ => 0)
    (fun _ => rfl) i y

end NormalizedAtomTailsTests
