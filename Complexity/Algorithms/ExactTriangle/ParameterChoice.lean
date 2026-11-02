/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Log

/-!
# A coarse dyadic family for the concrete ExactTriangle pipeline

These original conservative choices match the current native geometry `D^18 ≤ n` and
balance its group factor against the `D^(1/18)` product saving: `g^36 = D`.
They are not an attribution of Anthropic's tuned parameters or a proof of the final 1.9992
endpoint. The small regime is explicitly identified for subsequent finite-solver dispatch.
-/

public section

namespace Cslib.Algorithms.ExactTriangle.ParameterChoice

/-- Number of complete blocks of 1296 binary input-size bits. -/
@[expose] def blocks (n : ℕ) : ℕ := Nat.log 2 n / 1296

/-- The thin-product matrix parameter is a multiple of 36. -/
@[expose] def level (n : ℕ) : ℕ := 36 * blocks n

/-- Prime-window and thin-product dimension parameter. -/
@[expose] def window (n : ℕ) : ℕ := 4 ^ level n

/-- The group count balancing the two existing native solver terms. -/
@[expose] def groups (n : ℕ) : ℕ := 4 ^ blocks n

/-- Tensor depth for the existing thin-product implementation. -/
@[expose] def tensorDepth (n : ℕ) : ℕ := 19 * level n

/-- Block rounding never exceeds the available binary logarithm. -/
theorem blocks_mul_le_log (n : ℕ) : 1296 * blocks n ≤ Nat.log 2 n := by
  simpa only [blocks, Nat.mul_comm] using Nat.div_mul_le_self (Nat.log 2 n) 1296

/-- The scale exponent is bounded by the original binary logarithm. -/
theorem blocks_le_log (n : ℕ) : blocks n ≤ Nat.log 2 n := Nat.div_le_self _ _

/-- The matrix exponent also fits below the original binary logarithm. -/
theorem level_le_log (n : ℕ) : level n ≤ Nat.log 2 n := by
  have h := blocks_mul_le_log n
  dsimp only [level]
  omega

/-- The group parameter is always positive, including on empty input. -/
theorem groups_pos (n : ℕ) : 0 < groups n := by
  unfold groups
  exact Nat.pow_pos (by decide)

/-- The two parameters have the exact balance needed by subsequent cost composition. -/
theorem groups_pow (n : ℕ) : groups n ^ 36 = window n := by
  simp only [groups, window, level, ← Nat.pow_mul]
  congr 1
  omega

/-- Exact dyadic form of the geometry reservation. -/
theorem window_pow (n : ℕ) : window n ^ 18 = 2 ^ (1296 * blocks n) := by
  change (4 ^ (36 * blocks n)) ^ 18 = _
  rw [← Nat.pow_mul]
  change (2 ^ 2) ^ (36 * blocks n * 18) = _
  rw [← Nat.pow_mul]
  congr 1
  omega

/-- Every positive input admits the exact thin-product size condition. At zero the chosen
window is one and the fast branch is disabled instead. -/
theorem geometry {n : ℕ} (hn : 0 < n) : window n ^ 18 ≤ n := by
  rw [window_pow]
  exact (Nat.pow_le_pow_right (by decide) (blocks_mul_le_log n)).trans
    (Nat.pow_log_le_self 2 hn.ne')

/-- The reserved window never exceeds a positive original dimension. -/
theorem window_le {n : ℕ} (hn : 0 < n) : window n ≤ n :=
  (Nat.le_self_pow (by decide : 18 ≠ 0) _).trans (geometry hn)

/-- The group count is no larger than the chosen window. -/
theorem groups_le_window (n : ℕ) : groups n ≤ window n := by
  apply Nat.pow_le_pow_right (by decide)
  unfold level
  omega

/-- Both powers are bounded by the original dimension plus one, including empty input. -/
theorem powers_le (n : ℕ) : groups n ≤ n + 1 ∧ window n ≤ n + 1 := by
  by_cases hn : n = 0
  · subst n
    simp [groups, window, level, blocks]
  · have hw := (window_le (by omega : 0 < n)).trans (Nat.le_succ n)
    exact ⟨(groups_le_window n).trans hw, hw⟩

/-- The large-geometry branch is exactly the explicit constant input threshold. -/
theorem blocks_pos_iff (n : ℕ) : 0 < blocks n ↔ 2 ^ 1296 ≤ n := by
  by_cases hn : n = 0
  · subst n
    have hp := Nat.two_pow_pos 1296
    simp only [blocks, Nat.log_zero_right, Nat.zero_div]
    omega
  · have hd : 0 < Nat.log 2 n / 1296 ↔ 1296 ≤ Nat.log 2 n := by omega
    exact hd.trans (Nat.le_log_iff_pow_le (by decide) hn)

/-- A positive block count supplies the solver's nontrivial window hypothesis. -/
theorem window_ge_sixteen {n : ℕ} (hn : 0 < blocks n) : 16 ≤ window n := by
  change 4 ^ 2 ≤ 4 ^ level n
  apply Nat.pow_le_pow_right (by decide)
  unfold level
  omega

private theorem expanded_group_power (n k : ℕ) :
    (4 * groups n) ^ k = 2 ^ (2 * ((blocks n + 1) * k)) := by
  rw [groups, ← Nat.pow_succ', ← Nat.pow_mul]
  change (2 ^ 2) ^ ((blocks n + 1) * k) = _
  rw [← Nat.pow_mul]

/-- Rounding loses only a fixed factor in the parameter's eventual growth rate. This exact
integer inequality will support later real-power/asymptotic composition. -/
theorem size_lt_groups_pow (n : ℕ) : n < (4 * groups n) ^ 648 := by
  have hl : Nat.log 2 n + 1 ≤ 1296 * (blocks n + 1) := by dsimp only [blocks]; omega
  have hp := (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hl)
  have he := expanded_group_power n 648
  have hexp : 2 * ((blocks n + 1) * 648) = 1296 * (blocks n + 1) := by omega
  rw [hexp] at he
  rw [he]
  exact hp

end Cslib.Algorithms.ExactTriangle.ParameterChoice
