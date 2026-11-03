/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Callee

/-!
# Strict-subcubic time of the actual parameter-selecting ET callee

The concrete host interface selects the real fast branch beyond a fixed threshold. Its
content-independent time field is then the already proved natural dyadic allowance. The
threshold is chosen before all original weight bounds, matrices, layout and physical width.

## Main results

* `exists_time_subcubic_bound`: the actual callee time field is uniformly strict-subcubic
  for polynomial original weights. The callee's unconditional semantics still use the real
  exhaustive branch at smaller dimensions.

This original composition does not assume a fast solver, supplied time law or selected prime.
It does not yet bound the repeated ordinary 3SUM host calls or prove the tuned 1.9992 endpoint.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.Algorithms.ExactTriangle

-- Normalize only the existing fixed fast-threshold numeral while transporting its bound.
set_option exponentiation.threshold 1296 in
/-- A single coefficient and dimension threshold per weight exponent bound the actual
Host.Callee time field, uniformly before every admitted original magnitude. -/
theorem exists_time_subcubic_bound {κ : ℕ} (hκ : 1 ≤ κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ^ 1296 ≤ N ∧
      ∀ n ≥ N, ∀ F ≤ (n + 2) ^ κ,
        (callee.time n F : ℝ) ≤ C * (n : ℝ) ^ (3 - 1 / 1296 : ℝ) := by
  obtain ⟨C, hC, N, hN, ht⟩ := CallableFixedPrime.exists_dyadicTime_subcubic_bound hκ
  refine ⟨C, hC, N, hN, ?_⟩
  intro n hn F hF
  rw [callee_time, callerTime, ite_eq_left ((ParameterChoice.blocks_pos_iff n).mpr (hN.trans hn))]
  exact ht n hn F hF

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
