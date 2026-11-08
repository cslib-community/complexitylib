/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.VOLE.MulCheck
import CslibFrontier.Probability.PMF.Uniform

/-!
# VOLE multiplication soundness examples

The false gate `0 * 0 = -1`, zero masks and affine claim `delta` accept precisely at `0, 1`.
This attains the two-root bound over `ZMod 5` and accepts every key over `ZMod 2`.
-/

namespace ComplexityTests.Crypto.VOLEMulCheck

open Cslib.Crypto.Protocols.VOLE Cslib.Probability
open scoped ENNReal

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- A false claim has exactly two accepting keys; the bound is not merely an upper estimate.
example : (0 : ZMod 5) * 0 ≠ -1 := by decide

example : (Finset.univ.filter fun delta : ZMod 5 =>
    (0 * delta + 0) * (0 * delta + 0) - ((-1) * delta + 0) * delta =
      1 * delta + 0) = {0, 1} := by decide

example : (PMF.uniformOfFintype (ZMod 5)).toOuterMeasure
    {delta | (0 * delta + 0) * (0 * delta + 0) - ((-1) * delta + 0) * delta =
      1 * delta + 0} = 2 / (5 : ℝ≥0∞) := by
  rw [PMF.toOuterMeasure_uniformOfFintype]
  have hcard : (Finset.univ.filter fun delta : ZMod 5 =>
      (0 * delta + 0) * (0 * delta + 0) - ((-1) * delta + 0) * delta =
        1 * delta + 0).card = 2 := by decide
  simp only [Set.mem_ofPred_eq, hcard, ZMod.card, Nat.cast_ofNat, div_eq_mul_inv]

-- The theorem intentionally permits a probability-one false claim over the smallest field.
example : (0 : ZMod 2) * 0 ≠ -1 := by decide

example (delta : ZMod 2) :
    (0 * delta + 0) * (0 * delta + 0) - ((-1) * delta + 0) * delta =
      1 * delta + 0 := by
  fin_cases delta <;> decide

-- Honest coefficients pass at every key, including zero, with nonzero values and masks.
example (delta : ZMod 5) :
    (2 * delta + 1) * (3 * delta + 2) - (1 * delta + 4) * delta =
      voleMulCrossTerm 2 1 3 2 4 * delta + voleMulConstTerm 1 2 := by
  exact voleMulCheck rfl rfl rfl (by decide)

-- A randomized claim can correlate its coefficients with all its private state; the key
-- remains independent. Here the sender chooses the affine slope uniformly in the field.
example : (do
    let slope ← PMF.uniformOfFintype (ZMod 5)
    let delta ← PMF.uniformOfFintype (ZMod 5)
    return (slope, delta)).toOuterMeasure
    {r | (0 : ZMod 5) * 0 ≠ -1 ∧
      (0 * r.2 + 0) * (0 * r.2 + 0) - ((-1) * r.2 + 0) * r.2 =
        r.1 * r.2 + 0} ≤ 2 / (5 : ℝ≥0∞) := by
  simpa only [ZMod.card, Nat.cast_ofNat, id_eq] using
    toOuterMeasure_voleMulCheck_bind_le (PMF.uniformOfFintype (ZMod 5))
      (fun _ => 0) (fun _ => 0) (fun _ => -1) (fun _ => 0) (fun _ => 0)
      (fun _ => 0) id (fun _ => 0)

-- If the sender could adapt its constant term to the key, a false gate would always pass.
-- This lies outside the theorem's experiment and checks the significance of its sampling order.
example (delta : ZMod 5) :
    (0 * delta + 0) * (0 * delta + 0) - ((-1) * delta + 0) * delta =
      0 * delta + delta ^ 2 := by ring

end ComplexityTests.Crypto.VOLEMulCheck
