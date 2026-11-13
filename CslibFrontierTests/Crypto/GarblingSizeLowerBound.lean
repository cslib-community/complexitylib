/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Primitives.Garbling.SizeLowerBound
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Logb
import CslibFrontier.Probability.Entropy.Guessing
import Mathlib.Algebra.Ring.BooleanRing

/-! # Garbling size lower bounds: checked instances

A one-time pad `G = X + K` with the key `K` observed: the hidden value `X` keeps `m` bits of
entropy given `K`, and `(K, G)` decodes it without error, so the size bound gives exactly `m ≤ m`.
A deterministic joint law has no conditional entropy, so the maximum a posteriori guess never errs
on it. The continuity bounds apply to a point mass against the uniform bit. -/

namespace CslibFrontierTests.GarblingSizeLowerBound

open Cslib Cslib.Probability.PMF Cslib.Crypto.Garbling

/-- The law of a key `K` and a hidden value `X`, uniform and independent. It is both the real
probability space, on which the observation is `K`, the hidden value is `X` and the garbled
material is the pad `G = X + K`, and the simulated law of `(K, X)`. -/
noncomputable def padIdeal (m : ℕ) : PMF (BitString m × BitString m) :=
  (uniformOfFintype (BitString m)).bind fun k => (uniformOfFintype (BitString m)).map (k, ·)

theorem conditionalEntropy_padIdeal (m : ℕ) : conditionalEntropy (padIdeal m) = m := by
  rw [padIdeal, conditionalEntropy_bind_pair, entropy_uniform, ← Finset.sum_mul, sum_toReal,
    one_mul, BitString.logb_card]

/-- The pad `G = X + K` of a key `K` and a hidden value `X`. -/
def pad {m : ℕ} (kx : BitString m × BitString m) : BitString m := kx.2 + kx.1

/-- Removing the key recovers the hidden value. -/
def unpad {m : ℕ} (kg : BitString m × BitString m) : BitString m := kg.2 + kg.1

theorem unpad_pad {m : ℕ} (kx : BitString m × BitString m) : unpad (kx.1, pad kx) = kx.2 := by
  funext i
  simp only [unpad, pad, Pi.add_apply]
  cases kx.1 i <;> cases kx.2 i <;> decide

theorem decodingError_pad (m : ℕ) :
    (padIdeal m).toOuterMeasure {kx | unpad (kx.1, pad kx) ≠ kx.2} = 0 := by
  simp [unpad_pad]

-- The size bound for the one-time pad, on the space of key and hidden value: every slack term
-- vanishes and the bound is `m ≤ m`.
example (m : ℕ) : (m : ℝ) - 0 * Real.logb 2 (Fintype.card (BitString m)) -
    condEntropyModulus 0 -
      (Real.binEntropy ((padIdeal m).toOuterMeasure {kx | unpad (kx.1, pad kx) ≠ kx.2}).toReal /
          Real.log 2 +
        ((padIdeal m).toOuterMeasure {kx | unpad (kx.1, pad kx) ≠ kx.2}).toReal *
          Real.logb 2 (Fintype.card (BitString m) - 1)) ≤ m :=
  sub_le_bitLength_of_recover (padIdeal m) Prod.fst Prod.snd pad (padIdeal m) unpad
    (by rw [show (fun kx : BitString m × BitString m => (kx.1, kx.2)) = id from rfl, PMF.map_id,
      dist_self]) (conditionalEntropy_padIdeal m).symm.le

-- With no decoding error and no distance, the slack is zero.
example (m : ℕ) : (m : ℝ) - 0 * Real.logb 2 (Fintype.card (BitString m)) -
    condEntropyModulus 0 -
      (Real.binEntropy ((padIdeal m).toOuterMeasure {kx | unpad (kx.1, pad kx) ≠ kx.2}).toReal /
          Real.log 2 +
        ((padIdeal m).toOuterMeasure {kx | unpad (kx.1, pad kx) ≠ kx.2}).toReal *
          Real.logb 2 (Fintype.card (BitString m) - 1)) = m := by
  rw [decodingError_pad]
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

end CslibFrontierTests.GarblingSizeLowerBound
