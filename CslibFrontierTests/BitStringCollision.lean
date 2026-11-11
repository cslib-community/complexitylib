/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/
import CslibFrontier.Probability.BitString.Collision
/-!
# Tests for random-function evaluation uniformity and shifted bit-string collisions

Instantiates `CslibFrontier/Probability/BitString/Collision.lean` on concrete `BitString 4` point
schedules, sets and caches, without importing any encryption-mode API.
-/
namespace Cslib.BitString.CollisionTests
open Cslib.BitString Cslib.Probability
open scoped ENNReal
/-- A fixed nonzero 4-bit offset. -/
def offset4 : BitString 4 := ![true, false, true, false]
/-- An injective two-point evaluation schedule on `BitString 4`. -/
def pts4 : Fin 2 → BitString 4 := ![0, offset4]
theorem pts4_injective : Function.Injective pts4 := by decide
example :
    (PMF.uniformOfFintype (BitString 4 → BitString 4)).map (fun g i => g (pts4 i)) =
      PMF.uniformOfFintype (Fin 2 → BitString 4) :=
  map_evalPoints_uniformOfFintype pts4_injective
example (m : Fin 2 → BitString 4) :
    (PMF.uniformOfFintype (BitString 4 → BitString 4)).map (fun g i => g (pts4 i) + m i) =
      PMF.uniformOfFintype (Fin 2 → BitString 4) :=
  map_xorEvalPoints_uniformOfFintype pts4_injective m
example :
    (PMF.uniformOfFintype (BitString 4)).toOuterMeasure
        {u | u + offset4 ∈ ({0, offset4} : Finset (BitString 4))} =
      2 * ((2 : ℝ≥0∞) ^ 4)⁻¹ := by
  have hcard : ({0, offset4} : Finset (BitString 4)).card = 2 := by decide
  rw [toOuterMeasure_addRight_mem_finset_eq, hcard]
  norm_num
/-- The list bound counts a repeated cache entry once per occurrence. -/
example :
    (PMF.uniformOfFintype (BitString 4)).toOuterMeasure {u | u + offset4 ∈ [0, 0, offset4]} ≤
      3 * ((2 : ℝ≥0∞) ^ 4)⁻¹ := by
  simpa using toOuterMeasure_addRight_mem_list_le [0, 0, offset4] offset4
end Cslib.BitString.CollisionTests
