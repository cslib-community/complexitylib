/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.OneWayInversion
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Tests: learning by inversion without weak one-way functions

The inner-product family keys an `n`-bit point by an `n`-bit key and labels it by their inner
product over `𝔽₂`, so its concepts are the `2 ^ n` parities of subsets of the coordinates. Its
labelling map, on a key and two points, outputs the points followed by their labels. Without weak
one-way functions, `2 n` examples suffice for some uniform strict PPT inverter to give a learner
with uniform error at most `1 / 2` except with probability at most `1 / q n + 2⁻ⁿ`, on infinitely
many scales.
-/
namespace CslibFrontierTests.LearningOneWayInversion

open Cslib.MachineLearning.UniformLearning Cslib.MachineLearning.UniformLearning.OneWayInversion
open Cslib.MachineLearning.PACLearning Cslib.Crypto Cslib.Probability Turing.MultiTapeTM Filter
open scoped ENNReal

/-- The inner product over `𝔽₂` of the first `n` bits of a word with the rest. -/
private def innerProduct (n : ℕ) (w : List Bool) : Bool :=
  (List.zipWith (· && ·) (w.take n) (w.drop n)).foldl xor false

/-- The key `01` labels the point `11` by their inner product `1`. -/
example : family (fun n => n) innerProduct 2 ![false, true] ![true, true] = true := by
  decide

/-- The labelling map at scale `2` with two samples: key `01`, points `10` and `11`, and three
spare bits. The labels are the inner products `0` and `1`. -/
example : labelMap (fun n => n) (fun _ => 2) innerProduct 2
    [false, true, true, false, true, true, false, false, false] =
    [true, false, true, true, false, true] := by
  decide

private theorem computableInPolyTime_innerProduct :
    ComputableInPolyTime (fun p : ℕ × List Bool => innerProduct p.1 p.2)
      (encPair encUnary encBits) encBool := by
  unfold innerProduct
  fun_prop

/-- Without weak one-way functions, `2 n` examples of the inner-product family give uniform error
at most `1 / 2` except with probability `1 / q n + 2⁻ⁿ`, on infinitely many scales. -/
example (hOWF : ¬ ∃ f, WeakOneWay f) {q : Polynomial ℕ} (hq : ∀ n, 0 < q.eval n) :
    ∃ A : Inverter, IsPPT encBits A ∧ ∃ᶠ n in atTop,
      (learningExperiment (fun n => n) (fun n => 2 * n) innerProduct A n).toOuterMeasure
          {(K, _, K') | 1 / 2 < uniformError (family (fun n => n) innerProduct n K)
            (family (fun n => n) innerProduct n K')} ≤
        ((q.eval n : ℕ) : ℝ≥0∞)⁻¹ + 2⁻¹ ^ n := by
  obtain ⟨A, hA, hfreq⟩ := exists_learner_of_not_exists_weakOneWay (fun n => n) (fun n => 2 * n)
    innerProduct hOWF (by fun_prop) (by fun_prop) computableInPolyTime_innerProduct hq
  refine ⟨A, hA, hfreq.mono fun n hn => (hn (1 / 2) (by norm_num)).trans_eq ?_⟩
  rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat, ENNReal.one_sub_inv_two,
    pow_mul, ← mul_pow, show (2 : ℝ≥0∞) * 2⁻¹ ^ 2 = 2⁻¹ by
      rw [pow_two, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]]

end CslibFrontierTests.LearningOneWayInversion
