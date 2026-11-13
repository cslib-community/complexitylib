/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.AdjacentPair.Balanced
public import CslibFrontier.Computability.QueryComplexity.AdjacentPair.Blocks
public import CslibFrontier.Computability.DecisionTree.Sensitivity

/-!
# Adjacent-pair block functions: sensitivity versus block sensitivity

[AroraBarak07], Chapter 11 Exercise 2 (web draft 2007-01-08, printed page 218 / PDF page 234),
partitions `n` input bits into `⌊√n⌋` contiguous blocks of about `√n` bits each and accepts
when some block has exactly two adjacent true bits and all its other bits are false. Its
sensitivity is `Θ(√n)` while its block sensitivity, certificate complexity and decision-tree
complexity are `Θ(n)`.

The formal function `adjacentPairSqrt n` uses `k = Nat.sqrt n` blocks with sizes
`n / k + [i < n % k]` (`sqrtBlockSizes`), laid out consecutively, so every length is covered and
not just squares. Adjacency is linear within a block, with overlapping choices allowed: `0110`
in a four-bit block is accepted. Small lengths follow the same definition: for `n = 0` there are
no blocks and the function is constantly false, and for `1 ≤ n ≤ 3` there is one block of `n`
bits. The quantitative bounds below are stated for `n ≥ 4`, where every block has at least two
bits. Measures are CSLib's native `sensitivity`, `blockSensitivity`, `certificateComplexity`
and `DecisionTree.complexity`.

## Main definitions

* `Cslib.BitString.adjacentPairSqrt`: the exercise function on `n` bits.

## Main results

* `Cslib.BitString.sqrt_le_sensitivity_adjacentPairSqrt`,
  `Cslib.BitString.sensitivity_adjacentPairSqrt_le`: `⌊√n⌋ ≤ s(f_n) ≤ 3⌊√n⌋`.
* `Cslib.BitString.card_le_three_mul_blockSensitivity_adjacentPairSqrt`: `n ≤ 3 bs(f_n)`.
* `Cslib.BitString.adjacentPairSqrt_measures`: the full chain
  `⌊√n⌋ ≤ s ≤ 3⌊√n⌋`, `n ≤ 3 bs`, `bs ≤ C ≤ D ≤ n`.

The bounds give `s(f_n) = Θ(√n)` and `bs(f_n) = C(f_n) = D(f_n) = Θ(n)`. No exact formulas
for these measures (for instance `D(f_n) = n`) are claimed.
-/

public section

namespace Cslib.BitString

open QueryComplexity

/-- The function of [AroraBarak07], Chapter 11 Exercise 2, on `n` bits: accept when one of the
`Nat.sqrt n` balanced contiguous blocks contains exactly two adjacent true bits and no other
true bit. -/
@[expose] def adjacentPairSqrt (n : ℕ) : BooleanFunction n :=
  adjacentPairBlocks (sum_sqrtBlockSizes n)

/-- On the empty input length there are no blocks and the function rejects. -/
@[simp] theorem adjacentPairSqrt_zero_length (x : BitString 0) : adjacentPairSqrt 0 x = false := by
  cases h : adjacentPairSqrt 0 x with
  | false => rfl
  | true =>
    obtain ⟨b, _⟩ := adjacentPairBlocks_eq_true_iff.mp h
    exact absurd b.isLt (by simp)

/-- **Sensitivity lower bound**: `⌊√n⌋ ≤ s(f_n)` for `n ≥ 4`. -/
theorem sqrt_le_sensitivity_adjacentPairSqrt {n : ℕ} (hn : 4 ≤ n) :
    Nat.sqrt n ≤ sensitivity (adjacentPairSqrt n) := by
  have hk : 0 < Nat.sqrt n := Nat.sqrt_pos.mpr (by omega)
  let b : Fin (Nat.sqrt n) := ⟨0, hk⟩
  exact (sqrt_le_sqrtBlockSizes n b).trans
    (le_sensitivity_adjacentPairBlocks _ (two_le_sqrtBlockSizes hn b))

/-- **Sensitivity upper bound**: `s(f_n) ≤ 3⌊√n⌋` for every `n`. -/
theorem sensitivity_adjacentPairSqrt_le (n : ℕ) :
    sensitivity (adjacentPairSqrt n) ≤ 3 * Nat.sqrt n := by
  have h := sensitivity_adjacentPairBlocks_le (sum_sqrtBlockSizes n) (sqrtBlockSizes_le n)
  rw [max_self] at h
  exact h

/-- **Block-sensitivity lower bound**: `n ≤ 3 bs(f_n)` for `n ≥ 4`. -/
theorem card_le_three_mul_blockSensitivity_adjacentPairSqrt {n : ℕ} (hn : 4 ≤ n) :
    n ≤ 3 * blockSensitivity (adjacentPairSqrt n) :=
  card_le_three_mul_blockSensitivity_adjacentPairBlocks _ (two_le_sqrtBlockSizes hn)

/-- **Arora–Barak Chapter 11 Exercise 2.** For `n ≥ 4`, with `k = Nat.sqrt n`,
`k ≤ s(f_n) ≤ 3k`, `n ≤ 3 bs(f_n)` and `bs(f_n) ≤ C(f_n) ≤ D(f_n) ≤ n`. Hence
`s(f_n) = Θ(√n)` while `bs(f_n)`, `C(f_n)` and `D(f_n)` are `Θ(n)`. -/
theorem adjacentPairSqrt_measures {n : ℕ} (hn : 4 ≤ n) :
    Nat.sqrt n ≤ sensitivity (adjacentPairSqrt n) ∧
      sensitivity (adjacentPairSqrt n) ≤ 3 * Nat.sqrt n ∧
      n ≤ 3 * blockSensitivity (adjacentPairSqrt n) ∧
      blockSensitivity (adjacentPairSqrt n) ≤ certificateComplexity (adjacentPairSqrt n) ∧
      certificateComplexity (adjacentPairSqrt n) ≤ DecisionTree.complexity (adjacentPairSqrt n) ∧
      DecisionTree.complexity (adjacentPairSqrt n) ≤ n :=
  ⟨sqrt_le_sensitivity_adjacentPairSqrt hn, sensitivity_adjacentPairSqrt_le n,
    card_le_three_mul_blockSensitivity_adjacentPairSqrt hn,
    blockSensitivity_le_certificateComplexity _,
    DecisionTree.certificateComplexity_le_complexity _,
    (DecisionTree.complexity_le_card _).trans_eq (Fintype.card_fin n)⟩

end Cslib.BitString
