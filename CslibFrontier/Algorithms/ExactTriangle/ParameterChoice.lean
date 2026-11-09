/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer-block parameters for the native box endpoint

The parameters are chosen to put the different native costs on the common scale `n³/g`.
Here `n` is the Exact Triangle dimension, `D` the prime-window parameter and `g` the group
count. Before choosing integer values, the relevant inequalities are:

* `D^18 ≤ n` for the box backend's geometry;
* `D*g² ≤ n` to bound preparation `n²*D*g` by `n³/g`;
* `g² ≤ sqrt(D)` to bound query control by the same scale;
* `g² ≤ D^(8/125)` to turn product work `n³*g*D^(-8/125)` into `n³/g`.

`ParameterChoice.CostGeometry` proves the last three inequalities and their cost consequences.
The chosen family reserves the stronger `D^19 ≤ n` and uses `g=4^(2b)`, `D=4^(63b)`.
The product balance becomes `4*125 ≤ 63*8`, or `500 ≤ 504`; `63b` is also a multiple of
nine as required by the box tradeoff. Reserving nineteen powers of `D` then requires
`2*63*19*b = 2394*b ≤ log₂ n`, explaining `b = floor(log₂(n)/2394)`.
The existing box construction uses tensor depth `L=21m` at `m=63b`.

This integer rounding gives `n^(2/1197) < 16*g` and hence the raw cost scale
`n³/g ≤ 16*n^(3-2/1197)`. It does not remove logarithmic factors: the native finite ledger
retains `(21m+1)²*(m+1)` and the selected-prime scan term. Their degree-three logarithmic
coefficient is absorbed later in `WordRAM.ExactTriangle.DyadicCost.Asymptotics`.

`blocks_pos_iff` identifies the exact fast-branch cutoff `n ≥ 2^2394`. Below it the automatic
solver uses its exhaustive branch. This is a proved feasible family, not an optimal parameter
choice or a practical crossover estimate. The arithmetic tuning is original; the source's
fractional-root parameter computation is not implemented by these definitions.
-/

public section

namespace Cslib.Algorithms.ExactTriangle.ParameterChoice

/-- Number of complete blocks of 2394 binary input-size bits. -/
@[expose] def blocks (n : ℕ) : ℕ := Nat.log 2 n / 2394

/-- The thin-product matrix parameter is a multiple of 63. -/
@[expose] def level (n : ℕ) : ℕ := 63 * blocks n

/-- Prime-window and thin-product dimension parameter. -/
@[expose] def window (n : ℕ) : ℕ := 4 ^ level n

/-- The group count balancing the two existing native solver terms. -/
@[expose] def groups (n : ℕ) : ℕ := 4 ^ (2 * blocks n)

/-- Tensor depth for the existing thin-product implementation. -/
@[expose] def tensorDepth (n : ℕ) : ℕ := 21 * level n

/-- Block rounding never exceeds the available binary logarithm. -/
theorem blocks_mul_le_log (n : ℕ) : 2394 * blocks n ≤ Nat.log 2 n := by
  simpa only [blocks, Nat.mul_comm] using Nat.div_mul_le_self (Nat.log 2 n) 2394

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

/-- Exact dyadic form of the geometry reservation. -/
theorem window_pow (n : ℕ) : window n ^ 19 = 2 ^ (2394 * blocks n) := by
  change (4 ^ (63 * blocks n)) ^ 19 = _
  rw [← Nat.pow_mul]
  change (2 ^ 2) ^ (63 * blocks n * 19) = _
  rw [← Nat.pow_mul]
  congr 1
  omega

/-- Every positive input admits the exact thin-product size condition. At zero the chosen
window is one and the fast branch is disabled instead. -/
theorem geometry_nineteen {n : ℕ} (hn : 0 < n) : window n ^ 19 ≤ n := by
  rw [window_pow]
  exact (Nat.pow_le_pow_right (by decide) (blocks_mul_le_log n)).trans
    (Nat.pow_log_le_self 2 hn.ne')

/-- The box backend requires only eighteen of the nineteen reserved window factors. -/
theorem geometry {n : ℕ} (hn : 0 < n) : window n ^ 18 ≤ n :=
  (Nat.pow_le_pow_right (Nat.one_le_pow _ _ (by decide : 1 ≤ (4 : ℕ)))
    (by decide : 18 ≤ 19)).trans (geometry_nineteen hn)

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

-- Allow only the fixed dyadic reservation exponent in numeral coercions.
set_option exponentiation.threshold 2394 in
/-- The large-geometry branch is exactly the explicit constant input threshold. -/
theorem blocks_pos_iff (n : ℕ) : 0 < blocks n ↔ 2 ^ 2394 ≤ n := by
  by_cases hn : n = 0
  · subst n
    have hp := Nat.two_pow_pos 2394
    simp only [blocks, Nat.log_zero_right, Nat.zero_div]
    omega
  · have hd : 0 < Nat.log 2 n / 2394 ↔ 2394 ≤ Nat.log 2 n := by omega
    exact hd.trans (Nat.le_log_iff_pow_le (by decide) hn)

/-- A positive block count supplies the solver's nontrivial window hypothesis. -/
theorem window_ge_sixteen {n : ℕ} (hn : 0 < blocks n) : 16 ≤ window n := by
  change 4 ^ 2 ≤ 4 ^ level n
  apply Nat.pow_le_pow_right (by decide)
  unfold level
  omega

-- Allow only the fixed dyadic reservation exponent in numeral coercions.
set_option exponentiation.threshold 2394 in
/-- Squaring permits an exact integer exponent for the rounded group count. -/
theorem size_sq_lt_groups_pow (n : ℕ) : n ^ 2 < (16 * groups n) ^ 1197 := by
  have hl : Nat.log 2 n + 1 ≤ 2394 * (blocks n + 1) := by dsimp only [blocks]; omega
  have hp := (Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hl)
  have hs : n ^ 2 < (2 ^ (2394 * (blocks n + 1))) ^ 2 := by nlinarith only [hp]
  have he : (16 * groups n) ^ 1197 = (2 ^ (2394 * (blocks n + 1))) ^ 2 := by
    simp only [groups, show (16 : ℕ) = 4 ^ 2 from rfl, ← pow_add, ← pow_mul]
    change (2 ^ 2) ^ ((2 + 2 * blocks n) * 1197) = 2 ^ (2394 * (blocks n + 1) * 2)
    rw [← pow_mul]
    congr 1
    omega
  rwa [he]

-- Allow only the fixed dyadic reservation exponent in numeral coercions.
set_option exponentiation.threshold 2394 in
/-- A positive block count excludes empty input. -/
theorem pos_of_blocks_pos {n : ℕ} (hf : 0 < blocks n) : 0 < n :=
  lt_of_lt_of_le (Nat.two_pow_pos 2394) ((blocks_pos_iff n).mp hf)

/-- The group parameter is at least one, including small input. -/
theorem one_le_groups (n : ℕ) : 1 ≤ groups n := groups_pos n

/-- The window parameter is positive at every input. -/
theorem window_pos (n : ℕ) : 0 < window n := Nat.pow_pos (by decide)

/-- The group count cannot consume more than the original positive dimension. -/
theorem groups_le {n : ℕ} (hn : 0 < n) : groups n ≤ n :=
  (groups_le_window n).trans (window_le hn)

end Cslib.Algorithms.ExactTriangle.ParameterChoice
