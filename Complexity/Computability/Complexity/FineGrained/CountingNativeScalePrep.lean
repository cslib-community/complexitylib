/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.SparseCountingScale

/-!
# Private scale preparation for the native counting endpoint

This unaggregated preparation module bounds the clamped search round count for every declared
size `N` and occurring-variable count `v ≤ N`. It reuses Anton Kovsharov's eventual estimate in
`SparseCountingScale`; a fixed natural coefficient absorbs every input below its threshold.
It does not construct a counter or certify its time or independent workspace.

## Main results

* `exists_clamped_rounds_le_interpolationScale`: a private all-input round-count estimate with
  exponent multiplier `16`, for use in the accepted `CountingNativeEndpoint` join of #1226.
-/

-- The assigned preparation fragment intentionally exports no public declarations.
set_option linter.privateModule false

namespace Cslib.Complexity.SubexponentialSAT

open Filter ReplacementParams

/-- One fixed natural coefficient bounds the clamped round count, including its extra terminal
step, for every `N` and `v ≤ N`. No lower bound on `N` or `numGroups N` is assumed. -/
private theorem exists_clamped_rounds_le_interpolationScale :
    ∃ C : ℕ, 0 < C ∧ ∀ N v : ℕ, v ≤ N →
      ((2 ^ (v / max 1 (numGroups N) + 2) + 1 : ℕ) : ℝ) ≤
        (C : ℝ) * (2 : ℝ) ^ (16 * interpolationScale N) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (SparseCountingScale.eventually_two_le_numGroups.and
      SparseCountingScale.eventually_div_numGroups_le)
  let C : ℕ := 2 ^ (N₀ + 2) + 5
  refine ⟨C, by dsimp [C]; positivity, fun N v hv => ?_⟩
  have hscale : (1 : ℝ) ≤ (2 : ℝ) ^ (16 * interpolationScale N) :=
    Real.one_le_rpow one_le_two (mul_nonneg (by norm_num) (interpolationScale_nonneg N))
  by_cases hN : N < N₀
  · have hexp : v / max 1 (numGroups N) + 2 ≤ N₀ + 2 :=
      Nat.add_le_add_right ((Nat.div_le_self _ _).trans (hv.trans hN.le)) 2
    have hrounds : 2 ^ (v / max 1 (numGroups N) + 2) + 1 ≤ C := by
      have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
      dsimp [C]
      omega
    exact (Nat.cast_le.mpr hrounds).trans
      (le_mul_of_one_le_right (Nat.cast_nonneg C) hscale)
  · obtain ⟨hgroups, hdiv⟩ := hN₀ N (Nat.le_of_not_lt hN)
    have hclamp : max 1 (numGroups N) = numGroups N := max_eq_right (by omega)
    have hexp : ((v / max 1 (numGroups N) : ℕ) : ℝ) ≤ 16 * interpolationScale N := by
      calc
        ((v / max 1 (numGroups N) : ℕ) : ℝ) ≤ (v : ℝ) / (max 1 (numGroups N) : ℕ) :=
          Nat.cast_div_le
        _ ≤ (N : ℝ) / (numGroups N : ℝ) := by
          rw [hclamp]
          exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hv) (Nat.cast_nonneg _)
        _ ≤ 16 * interpolationScale N := hdiv
    have htwo : (2 : ℝ) ^ (v / max 1 (numGroups N)) ≤
        (2 : ℝ) ^ (16 * interpolationScale N) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two hexp
    have hrounds : ((2 ^ (v / max 1 (numGroups N) + 2) + 1 : ℕ) : ℝ) ≤
        5 * (2 : ℝ) ^ (16 * interpolationScale N) := by
      push_cast
      rw [pow_add]
      norm_num
      nlinarith
    have hC : (5 : ℝ) ≤ C := Nat.cast_le.mpr (Nat.le_add_left 5 _)
    exact hrounds.trans (mul_le_mul_of_nonneg_right hC (by positivity))

end Cslib.Complexity.SubexponentialSAT
