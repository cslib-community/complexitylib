/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.ExponentLifting
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithmic query bounds from discrepancy lifting

The power bound becomes the usual query-depth times alphabet-bit-length bound. A separate
scalar equivalence translates a polynomial alphabet requirement into a lower bound on the
number of bits, without imposing a representation of alphabet elements as bit strings.
-/

public section

namespace Cslib.Communication.Lifting

open Probability

/-- Taking logarithms of the simulator's power estimate. -/
theorem queryDepth_mul_log_le {m : ℝ} {d k c : ℕ} (hm : 0 < m)
    (h : m ^ d ≤ (8 : ℝ) ^ (256 * k * c)) :
    (d : ℝ) * Real.log m ≤ 768 * k * c * Real.log 2 := by
  have hlog := Real.log_le_log (by positivity : 0 < m ^ d) h
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 3 using 1; norm_num
  rw [Real.log_pow, Real.log_pow, h8] at hlog
  push_cast at hlog
  nlinarith [hlog]

/-- A polynomial alphabet threshold is equivalent to a linear lower bound on bit length. -/
theorem polynomial_le_two_pow_iff {n C b : ℕ} (hn : 0 < n) :
    n ^ C ≤ 2 ^ b ↔ (C : ℝ) * Real.log n ≤ (b : ℝ) * Real.log 2 := by
  have hlog := Real.log_le_log_iff
    (by positivity : 0 < (n : ℝ) ^ C) (by positivity : 0 < (2 : ℝ) ^ b)
  rw [Real.log_pow, Real.log_pow] at hlog
  exact (by exact_mod_cast hlog.symm)

/-- On a binary alphabet of `b` bits, the power estimate bounds query depth times `b`. -/
theorem queryDepth_mul_bits_le {b d k c : ℕ}
    (h : ((2 : ℝ) ^ b) ^ d ≤ (8 : ℝ) ^ (256 * k * c)) :
    d * b ≤ 768 * k * c := by
  have hl := queryDepth_mul_log_le (by positivity : 0 < (2 : ℝ) ^ b) h
  rw [Real.log_pow, ← mul_assoc] at hl
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := (mul_le_mul_iff_left₀ hlog).mp hl
  exact_mod_cast hb

/-- Deterministic discrepancy lifting in logarithmic query-cost form. -/
theorem exists_decisionTree_logarithmic {n m k : ℕ} [NeZero m] {η : ℝ} {O : Type*}
    (hk : 1 ≤ k) (hη : 1 ≤ 2 * (k : ℝ) * η)
    (hn : 2 ≤ n) (hm : n ^ (2048 * k ^ 2) ≤ m)
    (g : Fin m → Fin m → Bool)
    (hdisc : discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤ (m : ℝ) ^ (-η))
    (R : (Fin n → Bool) → O → Prop)
    (p : Protocol (Fin n → Fin m) (Fin n → Fin m) O)
    (hp : ∀ x y, R (fun i => g (x i) (y i)) (p.run x y)) :
    ∃ t : DecisionTree (Fin n) O, (∀ z, R z (t.eval z)) ∧
      (t.depth : ℝ) * Real.log m ≤ 768 * k * p.depth * Real.log 2 := by
  obtain ⟨t, ht, hd⟩ := exists_decisionTree_of_discrepancy_exponent hk hη hn hm g hdisc R p hp
  exact ⟨t, ht, queryDepth_mul_log_le (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)) hd⟩

end Cslib.Communication.Lifting
