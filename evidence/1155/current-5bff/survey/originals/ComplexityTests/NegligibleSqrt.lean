/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Negligible.Basic

/-! Square-root closure of negligible advantages, including composition and missing premises. -/

namespace ComplexityTests.NegligibleSqrt

open Cslib.Crypto
open scoped NNReal

example {ε : ℕ → ℝ≥0} (hε : Negligible ε) :
    Negligible (fun n => NNReal.sqrt (ε n)) := by
  fail_if_success (clear hε; fun_prop)
  fun_prop

example {ε δ : ℕ → ℝ≥0} (hε : Negligible ε) (hδ : Negligible δ) :
    Negligible (fun n => NNReal.sqrt (ε n + δ n)) := by fun_prop

example : Negligible (fun n => NNReal.sqrt ((1 / 4 : ℝ≥0) ^ n)) :=
  (negligible_geometric (by norm_num : (1 / 4 : ℝ≥0) < 1)).sqrt

example {ε : ℕ → ℝ≥0} (hle : ∀ n, ε n ≤ (1 / 4 : ℝ≥0) ^ n) :
    Negligible (fun n => NNReal.sqrt (ε n)) :=
  negligible_of_le (negligible_geometric (by norm_num : (1 / 4 : ℝ≥0) < 1)).sqrt
    (fun n => NNReal.sqrt_le_sqrt.mpr (hle n))

example : ∀ᶠ n : ℕ in Filter.atTop,
    (NNReal.sqrt ((1 / 4 : ℝ≥0) ^ n) : ℝ) ≤ 1 / (n + 1 : ℝ) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (negligible_geometric (by norm_num : (1 / 4 : ℝ≥0) < 1)).sqrt.eventually_le_inv_polynomial
      (p := fun n => n + 1) (by fun_prop) (by intro n; lia)

end ComplexityTests.NegligibleSqrt
