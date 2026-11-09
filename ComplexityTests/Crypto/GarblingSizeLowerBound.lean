/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Crypto.Primitives.Garbling.SizeLowerBound
import Complexity.Probability.Entropy.Guessing
import Mathlib.Algebra.Ring.BooleanRing

/-! # Garbling size lower bounds: checked instances

A one-time pad `G = X + K` with the key `K` observed: the hidden value `X` keeps `m` bits of
entropy given `K`, and `(K, G)` decodes it without error, so the size bound gives exactly `m ≤ m`.
A deterministic joint law has no conditional entropy, so the maximum a posteriori guess never errs
on it. The continuity bounds apply to a point mass against the uniform bit. -/

namespace ComplexityTests.GarblingSizeLowerBound

open Cslib Cslib.Probability.PMF Cslib.Crypto.Garbling

/-- An observed key `K`, a hidden value `X` and the pad `G = X + K`, all of `m` bits. -/
noncomputable def padReal (m : ℕ) : PMF (BitString m × BitString m × BitString m) :=
  (uniformOfFintype (BitString m)).bind fun k =>
    (uniformOfFintype (BitString m)).map fun x => (k, x, x + k)

/-- The view of `(K, X)`, with `X` uniform and independent of the key. -/
noncomputable def padIdeal (m : ℕ) : PMF (BitString m × BitString m) :=
  (uniformOfFintype (BitString m)).bind fun k => (uniformOfFintype (BitString m)).map (k, ·)

theorem padReal_map (m : ℕ) : (padReal m).map (fun w => (w.1, w.2.1)) = padIdeal m := by
  simp only [padReal, padIdeal, PMF.map_bind, PMF.map_comp]
  rfl

theorem conditionalEntropy_padIdeal (m : ℕ) : conditionalEntropy (padIdeal m) = m := by
  rw [padIdeal, conditionalEntropy_bind_pair, entropy_uniform, ← Finset.sum_mul, sum_toReal,
    one_mul, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

/-- Removing the key recovers the hidden value. -/
def unpad {m : ℕ} (kg : BitString m × BitString m) : BitString m := kg.2 + kg.1

theorem decodingError_padReal (m : ℕ) :
    (padReal m).toOuterMeasure {w | unpad (w.1, w.2.2) ≠ w.2.1} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro w hw
  simp only [padReal, PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hw
  obtain ⟨k, -, x, -, rfl⟩ := hw
  simp only [Set.mem_ofPred_eq, not_not, unpad]
  funext i
  simp only [Pi.add_apply]
  cases x i <;> cases k i <;> decide

-- The size bound for the one-time pad: every slack term vanishes and the bound is `m ≤ m`.
example (m : ℕ) : (m : ℝ) - 0 * Real.logb 2 (Fintype.card (BitString m)) -
    condEntropyModulus 0 -
      (Real.binEntropy ((padReal m).toOuterMeasure {w | unpad (w.1, w.2.2) ≠ w.2.1}).toReal /
          Real.log 2 +
        ((padReal m).toOuterMeasure {w | unpad (w.1, w.2.2) ≠ w.2.1}).toReal *
          Real.logb 2 (Fintype.card (BitString m) - 1)) ≤ m :=
  sub_le_bitLength_of_recover (padReal m) (padIdeal m) unpad
    (by rw [padReal_map, dist_self]) (conditionalEntropy_padIdeal m).symm.le

-- With no decoding error and no distance, the slack is zero.
example (m : ℕ) : (m : ℝ) - 0 * Real.logb 2 (Fintype.card (BitString m)) -
    condEntropyModulus 0 -
      (Real.binEntropy ((padReal m).toOuterMeasure {w | unpad (w.1, w.2.2) ≠ w.2.1}).toReal /
          Real.log 2 +
        ((padReal m).toOuterMeasure {w | unpad (w.1, w.2.2) ≠ w.2.1}).toReal *
          Real.logb 2 (Fintype.card (BitString m) - 1)) = m := by
  rw [decodingError_padReal]
  simp

-- A deterministic joint law has zero conditional entropy, so the MAP guess never errs.
example (y x : Bool) :
    ((PMF.pure (y, x)).toOuterMeasure
      {z | maxPosteriorGuess (PMF.pure (y, x)) z.1 ≠ z.2}).toReal ≤ 0 := by
  have h := errorProb_maxPosteriorGuess_le_log_two_mul (PMF.pure (y, x))
  have h0 : conditionalEntropy (PMF.pure (y, x)) = 0 := by
    simp [conditionalEntropy]
  rwa [h0, mul_zero] at h

-- Continuity for a point mass against the uniform bit, whose conditional entropies are `0` and `1`.
example :
    |conditionalEntropy (PMF.pure ((), false)) -
        conditionalEntropy ((uniformOfFintype Bool).map ((), ·))| ≤
      1 * Real.logb 2 (Fintype.card Bool) + condEntropyModulus 1 :=
  abs_conditionalEntropy_sub_le (dist_le_one _ _)

-- The same pair of laws, extended by a constant third component, for mutual information.
example :
    |condMutualInfo (PMF.pure ((), false, ())) -
        condMutualInfo ((uniformOfFintype Bool).map ((), ·, ()))| ≤
      1 * Real.logb 2 (Fintype.card Bool) + 2 * condEntropyModulus 1 :=
  abs_condMutualInfo_sub_le (dist_le_one _ _)

end ComplexityTests.GarblingSizeLowerBound
