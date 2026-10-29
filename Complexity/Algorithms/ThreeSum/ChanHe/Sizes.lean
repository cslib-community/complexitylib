/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.ChanHe.FromNumbers

/-!
# Explicit Chan–He size bounds for polynomially bounded integers

Adapted from [Sizes.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Theorem21a/ChanHe/Sizes.lean) and the parameter definitions in
`PaperStatements.lean`, at `anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
This module extracts the concrete natural-number bounds. It does not import the source's
asymptotic calculus, native machine or running-time claims.

## Main definitions

* `lenOf`: the common output length `8 * mPar n (2n^κ)^2`.
* `numBound`: a degree-seven logarithmic bound on the number of instances.
* `workBound`: a bound on candidate-prime/element pairs, not RAM instructions.

## Main results

* `threeSum_iff_exists_convolution`: the finite reduction at polynomial magnitudes.
* `length_instances_pow_le`, `abs_instances_pow_le`, `scanPairs_pow_le`: explicit bounds.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020], Theorem 5.1.
-/

@[expose] public section

namespace Cslib.Algorithms.ThreeSum.ChanHe

open Finset

/-- The common length of instances for inputs bounded by `n^κ`. -/
def lenOf (κ n : ℕ) : ℕ := 8 * mPar n (2 * n ^ κ) ^ 2

/-- A degree-seven logarithmic upper bound on the number of instances, for `n ≥ 2`. -/
def numBound (κ n : ℕ) : ℕ := 128 * (κ + 2) ^ 2 * (Nat.log 2 n + 1) ^ 7

/-- Bound on candidate-prime/element pairs scanned, excluding all other preprocessing work. -/
def workBound (κ n : ℕ) : ℕ := numBound κ n * (2 * mPar n (2 * n ^ κ) * (3 * n))

/-- `labelBits (2 n^κ) ≤ κ(⌊log₂ n⌋ + 1) + 3`. -/
theorem labelBits_pow_le (n κ : ℕ) : labelBits (2 * n ^ κ) ≤ κ * (Nat.log 2 n + 1) + 3 := by
  have hn : n ≤ 2 ^ (Nat.log 2 n + 1) := (Nat.lt_pow_succ_log_self (by norm_num) n).le
  refine Nat.succ_le_succ ((Nat.log_mono_right ?_).trans_eq
    (Nat.log_pow (by norm_num) (κ * (Nat.log 2 n + 1) + 2)))
  calc 2 * (2 * n ^ κ) ≤ 2 * (2 * (2 ^ (Nat.log 2 n + 1)) ^ κ) := by gcongr
    _ = 2 ^ (κ * (Nat.log 2 n + 1) + 2) := by rw [← pow_mul, mul_comm κ]; ring

/-- An explicit square-root times squared-logarithm bound on the searched primes.
This elementary estimate is original to the adaptation; it is a size bound, not a time bound. -/
theorem mPar_pow_le (n κ : ℕ) :
    mPar n (2 * n ^ κ) ≤
      (5 * κ + 16) * (10 * κ + 40) * (Nat.sqrt n + 1) * (Nat.log 2 n + 1) ^ 2 := by
  let L := Nat.log 2 n + 1
  let A := 5 * κ + 16
  have hL : 1 ≤ L := Nat.le_add_left 1 _
  have hbits : labelBits (2 * n ^ κ) ≤ (κ + 3) * L :=
    (labelBits_pow_le n κ).trans (by dsimp [L]; nlinarith)
  have hunit : 1 ≤ (Nat.sqrt n + 1) * L := by nlinarith
  have hw : wPar n (2 * n ^ κ) + 1 ≤ A * (Nat.sqrt n + 1) * L := by
    calc wPar n (2 * n ^ κ) + 1
        ≤ 5 * ((κ + 3) * L) * (Nat.sqrt n + 1) + 1 := by
          unfold wPar
          gcongr
      _ ≤ 5 * ((κ + 3) * L) * (Nat.sqrt n + 1) + (Nat.sqrt n + 1) * L :=
          Nat.add_le_add_left hunit _
      _ = A * (Nat.sqrt n + 1) * L := by dsimp [A]; ring
  have hroot : Nat.sqrt n + 1 ≤ 2 ^ L :=
    (Nat.add_le_add_right (Nat.sqrt_le_self n) 1).trans
      (Nat.lt_pow_succ_log_self (by decide) n)
  have hpow : wPar n (2 * n ^ κ) + 1 ≤ 2 ^ (A + 2 * L) := by
    calc wPar n (2 * n ^ κ) + 1 ≤ A * (Nat.sqrt n + 1) * L := hw
      _ ≤ 2 ^ A * 2 ^ L * 2 ^ L :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.lt_two_pow_self (n := A)).le hroot)
            (Nat.lt_two_pow_self (n := L)).le
      _ = 2 ^ (A + 2 * L) := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hlog : Nat.log 2 (wPar n (2 * n ^ κ) + 1) ≤ A + 2 * L :=
    (Nat.log_mono_right hpow).trans_eq (Nat.log_pow (by decide) _)
  calc mPar n (2 * n ^ κ)
      ≤ (A * (Nat.sqrt n + 1) * L) * (2 * (A + 2 * L) + 4) := by
        unfold mPar
        gcongr
    _ ≤ (A * (Nat.sqrt n + 1) * L) * ((2 * A + 8) * L) := by
        gcongr
        nlinarith
    _ = (5 * κ + 16) * (10 * κ + 40) * (Nat.sqrt n + 1) * L ^ 2 := by dsimp [A]; ring

/-- At polynomial magnitudes every convolution array has length at most `n` times a
fourth-degree logarithm, with an explicit constant depending only on `κ`. -/
theorem lenOf_le (κ n : ℕ) (hn : 1 ≤ n) :
    lenOf κ n ≤ 32 * ((5 * κ + 16) * (10 * κ + 40)) ^ 2 * n *
      (Nat.log 2 n + 1) ^ 4 := by
  have hroot : (Nat.sqrt n + 1) ^ 2 ≤ 4 * n := by
    have := Nat.sqrt_le n
    have := Nat.sqrt_le_self n
    nlinarith
  calc lenOf κ n
      ≤ 8 * ((5 * κ + 16) * (10 * κ + 40) * (Nat.sqrt n + 1) *
          (Nat.log 2 n + 1) ^ 2) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (mPar_pow_le n κ) 2)
    _ = 8 * ((5 * κ + 16) * (10 * κ + 40)) ^ 2 * (Nat.sqrt n + 1) ^ 2 *
          (Nat.log 2 n + 1) ^ 4 := by ring
    _ ≤ 8 * ((5 * κ + 16) * (10 * κ + 40)) ^ 2 * (4 * n) *
          (Nat.log 2 n + 1) ^ 4 := by gcongr
    _ = 32 * ((5 * κ + 16) * (10 * κ + 40)) ^ 2 * n * (Nat.log 2 n + 1) ^ 4 := by ring

/-- The instances are not empty arrays. -/
theorem one_le_lenOf (κ n : ℕ) : 1 ≤ lenOf κ n :=
  Nat.succ_le_of_lt (by unfold lenOf mPar; positivity)

/-! ## Correctness, the number of instances, their entries, and the count for the searches -/

/-- **The number of instances is at most `numBound κ n`.** -/
theorem length_instances_pow_le (n κ : ℕ) (hn : 2 ≤ n) (x : Fin n → ℤ) :
    (instances n (n ^ κ) x).length ≤ numBound κ n := by
  have hlog : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) hn
  have hΛ : labelBits (2 * n ^ κ) ≤ (κ + 2) * (Nat.log 2 n + 1) :=
    (labelBits_pow_le n κ).trans (by rw [add_mul]; omega)
  have hone : 1 ≤ ((κ + 2) * (Nat.log 2 n + 1)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  calc (instances n (n ^ κ) x).length
      ≤ (2 * labelBits (2 * n ^ κ) ^ 2 + 2) * (2 * Nat.log 2 n + 2) ^ 5 := length_instances_le ..
    _ ≤ (2 * ((κ + 2) * (Nat.log 2 n + 1)) ^ 2 + 2 * ((κ + 2) * (Nat.log 2 n + 1)) ^ 2) *
        (2 * Nat.log 2 n + 2) ^ 5 := by gcongr; omega
    _ = numBound κ n := by unfold numBound; ring

section input

variable {κ n : ℕ} {x : Fin n → ℤ}

/-- **The searches look at no more than `workBound κ n` pairs.**  This bounds the count
`scanPairs`, which we define; it is not a running time. -/
theorem scanPairs_pow_le (hn : 2 ≤ n) (hx : ∀ i, |x i| ≤ (n : ℤ) ^ κ) :
    scanPairs n (n ^ κ) x ≤ workBound κ n :=
  (scanPairs_le (by omega) (by exact_mod_cast hx)).trans
    (Nat.mul_le_mul_right _ (length_instances_pow_le n κ hn x))

/-- **The entries of the instances have absolute value at most `120 n^κ + 40`.** -/
theorem abs_instances_pow_le (hn : 2 ≤ n) (hx : ∀ i, |x i| ≤ (n : ℤ) ^ κ) {y : ℕ → ℤ}
    (hy : y ∈ instances n (n ^ κ) x) (u : ℕ) : |y u| ≤ 120 * (n : ℤ) ^ κ + 40 := by
  exact_mod_cast abs_instances_le (by omega) (by exact_mod_cast hx) hy u

/-- The full finite reduction at polynomial input magnitudes. -/
theorem threeSum_iff_exists_convolution (hn : 2 ≤ n) (hx : ∀ i, |x i| ≤ (n : ℤ) ^ κ) :
    HasSolution x ↔ ∃ y ∈ instances n (n ^ κ) x, Convolution (lenOf κ n) y :=
  instances_correct n (n ^ κ) (by omega) x (by exact_mod_cast hx)

end input

end Cslib.Algorithms.ThreeSum.ChanHe
