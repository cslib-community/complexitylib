/-
Copyright (c) 2026 Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.Log

/-!
# Sparsity and list-length parameters for initial and greedy parity tests

Shared CNF-free parameter definitions for the initial parity-check matrix construction and greedy
row-augmentation procedure of [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH],
§§6.1–6.2, Lemmas 6.1–6.2 (pp. 40–42), with `μ = ⌊log₂ m⌋ + 1`.

## Main definitions

* `Cslib.BitString.initialRowWeightBound`: `D₀(B, m) = 320000 * B ^ 2 * (Nat.log 2 m + 1) ^ 3`.
* `Cslib.BitString.greedyRowListLength`: `P(B, m) = 20000 * B ^ 2 * (Nat.log 2 m + 1) ^ 2`.

## Main results

* `Cslib.BitString.greedyRowListLength_le_initialRowWeightBound`: `P(B, m) ≤ D₀(B, m)`.
* `Cslib.BitString.max_initialRowWeightBound_greedyRowListLength`: hence `max D₀ P = D₀`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §§6.1–6.2, Lemmas 6.1–6.2
-/

@[expose] public section

namespace Cslib.BitString

/-- The Lemma 6.1 initial row weight bound `D₀(B, m) = 320000 * B ^ 2 * (Nat.log 2 m + 1) ^ 3`
([OpenAI2026ETH], §6.1, Lemma 6.1). -/
def initialRowWeightBound (B m : ℕ) : ℕ :=
  320000 * B ^ 2 * (Nat.log 2 m + 1) ^ 3

/-- The Lemma 6.1–6.2 support denominator and greedy candidate list length
`P(B, m) = 20000 * B ^ 2 * (Nat.log 2 m + 1) ^ 2` ([OpenAI2026ETH], §§6.1–6.2, Lemmas 6.1–6.2). -/
def greedyRowListLength (B m : ℕ) : ℕ :=
  20000 * B ^ 2 * (Nat.log 2 m + 1) ^ 2

/-- For all `B, m : ℕ`, the Lemma 6.2 greedy list length
`P = 20000 * B ^ 2 * (Nat.log 2 m + 1) ^ 2` is at most the Lemma 6.1 initial row weight bound
`D₀ = 320000 * B ^ 2 * (Nat.log 2 m + 1) ^ 3`. -/
theorem greedyRowListLength_le_initialRowWeightBound (B m : ℕ) :
    greedyRowListLength B m ≤ initialRowWeightBound B m := by
  unfold greedyRowListLength initialRowWeightBound
  have h1 : 20000 * B ^ 2 ≤ 320000 * B ^ 2 :=
    Nat.mul_le_mul_right (B ^ 2) (by decide)
  have h2 : (Nat.log 2 m + 1) ^ 2 ≤ (Nat.log 2 m + 1) ^ 3 :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by decide)
  exact Nat.mul_le_mul h1 h2

/-- Consequently `max (initialRowWeightBound B m) (greedyRowListLength B m)` simplifies to
`initialRowWeightBound B m`. -/
@[simp]
theorem max_initialRowWeightBound_greedyRowListLength (B m : ℕ) :
    max (initialRowWeightBound B m) (greedyRowListLength B m) =
      initialRowWeightBound B m :=
  max_eq_left (greedyRowListLength_le_initialRowWeightBound B m)

end Cslib.BitString
