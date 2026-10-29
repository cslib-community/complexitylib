/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

-- upstream: local-only (formal abstract library)

import Complexity.Computability.Circuit.Boolean.Braverman.Fooling
import Cslib.Probability.StatisticalDistance

/-! # Bridge for Braverman's theorem

The library states `k`-wise independence through biases (`Cslib.BitString.IsKWiseIndependent`)
and fooling through expectations (`Cslib.BitString.Fools`). This bridge proves that vanishing
biases on all nonempty sets of at most `k` coordinates is the same as uniform marginals on all sets
of at most `k` coordinates, and restates Braverman's theorem with probabilities and counts.
-/

namespace ComplexityAbstracts.BravermanBridge

open Finset Cslib.BitString Cslib.Probability.PMF
open scoped BigOperators

variable {n k : ℕ}

/-- A distribution on bit strings has vanishing biases on all nonempty sets of at most `k`
coordinates exactly when its marginal on every set of at most `k` coordinates is uniform. -/
theorem isKWiseIndependent_iff_map_restrict {X : PMF (Fin n → Bool)} :
    IsKWiseIndependent k X ↔
      ∀ T : Finset (Fin n), T.card ≤ k → ∀ y : T → Bool, X.map T.restrict y = (2 ^ T.card)⁻¹ := by
  constructor
  · intro hX T hT y
    have h := hX.dist_map_restrict_le hT
    rw [mul_zero, zero_div] at h
    rw [dist_le_zero.1 h, uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_coe]
    push_cast
    rfl
  · intro hX S hS hSk
    have : Nonempty S := hS.to_subtype
    have hY (z : S → Bool) : ((X.map S.restrict) z).toReal = 1 / 2 ^ #S := by
      rw [hX S hSk z, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, one_div]
    have h0 : ∑ z : S → Bool, chi ℝ univ z = 0 := by
      have h := expect_chi (ι := S) univ
      rw [ite_eq_right univ_nonempty.ne_empty, Fintype.expect_eq_sum_div_card, div_eq_zero_iff] at h
      exact h.resolve_right (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    have hb : bias X S = bias (X.map S.restrict) univ := by
      rw [bias_map_restrict, univ_eq_attach, attach_map_val]
    rw [hb, bias]
    simp only [hY, ← mul_sum, h0, mul_zero, abs_zero, le_refl]

/-- **Braverman's theorem**, with probabilities and counts: a circuit of the unbounded fan-in basis
of depth at most `d`, with at most `2 ^ q` gates of fan-in less than `2 ^ q`, outputs `true` with
probability within `2 ^ (-q)` of the fraction of inputs on which it is `true`, under every
distribution whose marginals on all sets of at most `(64 q) ^ ((2 d + 3) (d + 7) + 1)`
coordinates are uniform. -/
theorem braverman {d q : ℕ} (hq : 1 ≤ q)
    (C : Cslib.Circuits.Circuit Cslib.Circuits.Boolean.Unbounded.signature n 1)
    (fanIn : C.FanInAtMost (2 ^ q - 1)) (size : C.size ≤ 2 ^ q) (depth : C.depth ≤ d)
    (X : PMF (Fin n → Bool))
    (independent : ∀ T : Finset (Fin n), T.card ≤ k → ∀ y : T → Bool,
      X.map T.restrict y = (2 ^ T.card)⁻¹)
    (hk : (64 * q) ^ ((2 * d + 3) * (d + 7) + 1) ≤ k) :
    |(univ.filter fun x => C.eval Cslib.Circuits.Boolean.Unbounded.interpretation x 0 = true).sum
        (fun x => (X x).toReal) -
      ((univ.filter fun x =>
        C.eval Cslib.Circuits.Boolean.Unbounded.interpretation x 0 = true).card : ℝ) / 2 ^ n| ≤
      1 / 2 ^ q := by
  have h := Cslib.Circuits.Boolean.Braverman.fools_of_isKWiseIndependent hq C fanIn size depth hk
    (isKWiseIndependent_iff_map_restrict.2 independent)
  rw [Fools] at h
  convert h using 3
  · rw [sum_filter]
    refine sum_congr rfl fun x _ => ?_
    cases C.eval Cslib.Circuits.Boolean.Unbounded.interpretation x 0 <;> simp
  · rw [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simp only [bitVal, sum_boole, Nat.cast_pow, Nat.cast_ofNat]

end ComplexityAbstracts.BravermanBridge
