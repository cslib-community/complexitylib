/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.OneWayInversion
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Tests: learning by inversion without weak one-way functions

The parity family keys an `n`-bit point by an `n`-bit key and labels it by the parity of the key
and the point together. Its labelling map, on a key and two points, outputs the points followed by
their labels. Without weak one-way functions, `2 n` examples suffice for some uniform strict PPT
learner to reach uniform error at most `1 / 2` with failure probability at most `1 / q n + 2⁻ⁿ`,
on infinitely many scales.
-/

namespace CslibFrontierTests.LearningOneWayInversion

open Cslib.MachineLearning.UniformLearning Cslib.MachineLearning.UniformLearning.OneWayInversion
open Cslib.MachineLearning.PACLearning Cslib.Crypto Cslib.Probability Turing.MultiTapeTM Filter
open scoped ENNReal

/-- The parity of a word. -/
private def parity (_ : ℕ) (w : List Bool) : Bool := w.foldl xor false

/-- The parity family labels a point by the parity of the key and the point. -/
example (K x : Fin 2 → Bool) :
    family (fun n => n) parity 2 K x = (List.ofFn K ++ List.ofFn x).foldl xor false :=
  rfl

/-- The labelling map at scale `1` with two samples: key `true`, points `false` and `true`, and a
spare bit. The labels are the parities `true` and `false`. -/
example : labelMap (fun n => n) (fun _ => 2) parity 1 [true, false, true, false] =
    [false, true, true, false] := by
  decide

private theorem computableInPolyTime_parity :
    ComputableInPolyTime (fun p : ℕ × List Bool => parity p.1 p.2) (encPair encUnary encBits)
      encBool := by
  unfold parity
  fun_prop

/-- Without weak one-way functions, `2 n` examples of the parity family give uniform error at most
`1 / 2` except with probability `1 / q n + 2⁻ⁿ`, on infinitely many scales. -/
example (hOWF : ¬ ∃ f, WeakOneWay f) {q : Polynomial ℕ} (hq : ∀ n, 0 < q.eval n) :
    ∃ A : Inverter, IsPPT encBits A ∧ ∃ᶠ n in atTop,
      (learningExperiment (fun n => n) (fun n => 2 * n) parity A n).toOuterMeasure
          {(K, _, K') | 1 / 2 < uniformError (family (fun n => n) parity n K)
            (family (fun n => n) parity n K')} ≤
        ((q.eval n : ℕ) : ℝ≥0∞)⁻¹ + 2⁻¹ ^ n := by
  obtain ⟨A, hA, hfreq⟩ := exists_learner_of_not_exists_weakOneWay (fun n => n) (fun n => 2 * n)
    parity hOWF (by fun_prop) (by fun_prop) computableInPolyTime_parity hq
  refine ⟨A, hA, hfreq.mono fun n hn => (hn (1 / 2) (by norm_num)).trans_eq ?_⟩
  rw [one_div, ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat, ENNReal.one_sub_inv_two,
    pow_mul, ← mul_pow, show (2 : ℝ≥0∞) * 2⁻¹ ^ 2 = 2⁻¹ by
      rw [pow_two, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]]

end CslibFrontierTests.LearningOneWayInversion
