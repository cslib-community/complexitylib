/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Superquadratic sensitivity separation: scalar bounds

Solution of the coupled scalar recurrences `u (n + 1) ≤ (1 + ε) * u n + 3 * v n` and
`v (n + 1) ≤ ε * u n + 3 * v n` with `u 0 ≤ L` and `v 0 ≤ 0`. Under the budget
`ε * 3 ^ (d + 1) ≤ 2`, the normalized side profile `u` stays below `2 * L` for the first `d` levels,
while the joint profile `v` is at most `ε * L * (3 ^ n - 1)`.

## Main results

* `geometric_error_le`: under the budget, the accumulated error `(3 / 2) * ε * L * (3 ^ n - 1)` is
  at most `L` for `n ≤ d`.
* `coupled_profiles_bound`: solutions of the coupled recurrences satisfy `u n ≤ 2 * L` and
  `v n ≤ ε * L * (3 ^ n - 1)` for `n ≤ d`.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/ScalarBounds.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

public section

namespace Cslib.QueryComplexity.SensitivitySeparation

namespace Internal

/-- If `n ≤ d`, `0 ≤ ε`, `0 ≤ L` and `ε * 3 ^ (d + 1) ≤ 2`, then
`(3 / 2) * ε * L * (3 ^ n - 1) ≤ L`. -/
theorem geometric_error_le {d n : ℕ} (hn : n ≤ d) {ε L : ℝ}
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2) :
    (3 / 2 : ℝ) * ε * L * (3 ^ n - 1) ≤ L := by
  have hp : (3 : ℝ) ^ (n + 1) ≤ 3 ^ (d + 1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ hn)
  have hb := (mul_le_mul_of_nonneg_left hp hε).trans hbudget
  have hm := mul_le_mul_of_nonneg_right hb hL
  rw [pow_succ] at hm
  nlinarith [mul_nonneg hε hL]

/-- If `0 ≤ ε`, `0 ≤ L`, `ε * 3 ^ (d + 1) ≤ 2`, `u 0 ≤ L`, `v 0 ≤ 0`, and for all `n < d` both
`u (n + 1) ≤ (1 + ε) * u n + 3 * v n` and `v (n + 1) ≤ ε * u n + 3 * v n`, then `u n ≤ 2 * L` and
`v n ≤ ε * L * (3 ^ n - 1)` for all `n ≤ d`. -/
theorem coupled_profiles_bound (d : ℕ) (u v : ℕ → ℝ) (ε L : ℝ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L) (hbudget : ε * 3 ^ (d + 1) ≤ 2)
    (hu0 : u 0 ≤ L) (hv0 : v 0 ≤ 0)
    (hu : ∀ n < d, u (n + 1) ≤ (1 + ε) * u n + 3 * v n)
    (hv : ∀ n < d, v (n + 1) ≤ ε * u n + 3 * v n) :
    ∀ n ≤ d, u n ≤ 2 * L ∧ v n ≤ ε * L * (3 ^ n - 1) := by
  have strong : ∀ n ≤ d,
      u n ≤ L + (3 / 2 : ℝ) * ε * L * (3 ^ n - 1) ∧
        v n ≤ ε * L * (3 ^ n - 1) := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa using And.intro hu0 hv0
    | succ n ih =>
        intro hn
        have hnd : n ≤ d := by omega
        obtain ⟨hun, hvn⟩ := ih hnd
        have he := geometric_error_le hnd hε hL hbudget
        have hun' : u n ≤ 2 * L := by linarith
        have heu := mul_le_mul_of_nonneg_left hun' hε
        have hnu := hu n (by omega)
        have hnv := hv n (by omega)
        constructor
        · rw [pow_succ]
          nlinarith [mul_nonneg hε hL]
        · rw [pow_succ]
          nlinarith
  intro n hn
  obtain ⟨hun, hvn⟩ := strong n hn
  have he := geometric_error_le hn hε hL hbudget
  exact ⟨by linarith, hvn⟩

end Internal

end Cslib.QueryComplexity.SensitivitySeparation
