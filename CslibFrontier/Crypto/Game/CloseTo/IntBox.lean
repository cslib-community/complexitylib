/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.CloseTo.UniformNat
public import CslibFrontier.Languages.Probabilistic.IntBox

/-!
# Statistical distance of the integer-box samplers

`sampleIntBox B width` factors through the residue sampler
`ProbComp.sampleModNat width (2 * B + 1)`, so `closeTo_uniform_sampleModNat` bounds its
distance from the exact uniform law on `[-B, B]` by `(2 * B + 1) / 2 ^ width`. The
`m`-coordinate samplers lose at most this much per coordinate. The dyadic centered sampler is
exact.

## Main results

* `Cslib.Probability.closeTo_uniformBox1D_sampleIntBox`: the 1D bound `(2 * B + 1) / 2 ^ width`.
* `Cslib.Probability.closeTo_uniform_intBox_sampleIntBoxVec`,
  `Cslib.Probability.closeTo_uniform_intBox_sampleIntBoxList`: the bound
  `m * ((2 * B + 1) / 2 ^ width)` on `intBox (Fin m) B`, for vectors and for lists.
* `Cslib.Probability.closeTo_uniformDyadicIntBox_sampleDyadicIntBox`: distance `0`.
-/

public section

namespace Cslib.Probability

open Probability.PMF
open scoped ENNReal

/-- **1D box sampler statistical distance.** `sampleIntBox B width` is within
`(2 * B + 1) / 2 ^ width` of the exact uniform distribution `uniformBox1D B` on `[-B, B]`. -/
theorem closeTo_uniformBox1D_sampleIntBox (B width : ℕ) :
    CloseTo (uniformBox1D B) (ProbComp.eval (sampleIntBox B width))
      ((2 * B + 1 : ℝ≥0∞) / 2 ^ width) := by
  rw [← uniformOfFintype_zmod_map_boxShift B, eval_sampleIntBox_eq_map_zmod B width]
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    (closeTo_uniform_sampleModNat width (2 * B + 1)).map (fun r => boxShift B r.val)

/-- **Multi-coordinate box sampler statistical distance (vector form).** `sampleIntBoxVec B m width`
is within `m * ((2 * B + 1) / 2 ^ width)` of the exact uniform distribution on
`intBox (Fin m) B = [-B, B]^m`. -/
theorem closeTo_uniform_intBox_sampleIntBoxVec (B m width : ℕ) :
    CloseTo (PMF.uniformOfFinset (intBox (Fin m) B) (intBox_nonempty B))
      (ProbComp.eval (sampleIntBoxVec B m width))
      ((m : ℝ≥0∞) * ((2 * B + 1 : ℝ≥0∞) / 2 ^ width)) := by
  rw [← iid_uniformBox1D B m, eval_sampleIntBoxVec_eq_iid B m width]
  have h1 := closeTo_uniformBox1D_sampleIntBox B width
  induction m with
  | zero =>
    simp only [PMF.iid, Nat.cast_zero, zero_mul, CloseTo.refl]
  | succ m ih =>
    simp only [PMF.iid, PMF.monad_bind_eq_bind]
    refine (CloseTo.bind h1 (fun a _ => CloseTo.map ih (Fin.cons (α := fun _ => ℤ) a))).mono ?_
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

/-- **Multi-coordinate box sampler statistical distance (list form).** `sampleIntBoxList B m width`
is within `m * ((2 * B + 1) / 2 ^ width)` of the encoded uniform distribution on
`intBox (Fin m) B`. -/
theorem closeTo_uniform_intBox_sampleIntBoxList (B m width : ℕ) :
    CloseTo ((PMF.uniformOfFinset (intBox (Fin m) B) (intBox_nonempty B)).map List.ofFn)
      (ProbComp.eval (sampleIntBoxList B m width))
      ((m : ℝ≥0∞) * ((2 * B + 1 : ℝ≥0∞) / 2 ^ width)) := by
  rw [eval_sampleIntBoxList_eq_map_ofFn]
  exact (closeTo_uniform_intBox_sampleIntBoxVec B m width).map List.ofFn

/-- `sampleDyadicIntBox width` has `0` statistical distance from `uniformDyadicIntBox width`. -/
theorem closeTo_uniformDyadicIntBox_sampleDyadicIntBox (width : ℕ) :
    CloseTo (uniformDyadicIntBox width) (ProbComp.eval (sampleDyadicIntBox width)) 0 := by
  rw [eval_sampleDyadicIntBox]
  exact CloseTo.refl _

end Cslib.Probability
