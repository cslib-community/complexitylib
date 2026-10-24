/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Uhlig's recovery code

Uhlig's two-copy construction stores bits `x 0, …, x (M - 1)` as the `M + 1` adjacent sums
`x 0, x 0 ^^ x 1, …, x (M - 2) ^^ x (M - 1), x (M - 1)`. Sums of code positions are taken in
the Boolean ring, where addition is exclusive or. Each bit is the sum of an initial segment of
the code and also the sum of the complementary final segment. For two requests `a` and `b`, the
smaller request uses the initial segment ending at its index and the larger request uses the
final segment after its index. These recovery sets are disjoint even when `a = b`, so every code
position serves at most one request.

The code is stated for sequences indexed by `ℕ`; only the value at `M` must vanish.

## Main definitions

* `Cslib.BitString.Uhlig.code`: the adjacent sums of a sequence.
* `Cslib.BitString.Uhlig.first`, `Cslib.BitString.Uhlig.second`: the code positions used by the
  first and second of two requests.

## Main results

* `Cslib.BitString.Uhlig.sum_range_code`: recovery from an initial segment.
* `Cslib.BitString.Uhlig.sum_Ico_code`: recovery from a final segment.
* `Cslib.BitString.Uhlig.second_eq_false_of_first`: the two recovery sets are disjoint.
* `Cslib.BitString.Uhlig.sum_first_code_route`, `Cslib.BitString.Uhlig.sum_second_code_route`:
  each request recovers its bit when every code position reads the input of the request that
  uses it.

## References

* [D. Uhlig, *Networks computing Boolean functions for multiple input values*][Uhlig1992].
* [I. Wegener, *The Complexity of Boolean Functions*][Wegener1987], proof of Theorem 10.2.3.
* Adapted from MassProduction/Uhlig.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.BitString.Uhlig

open Finset

/-- Uhlig's code of a bit sequence: position `0` holds `x 0` and position `j + 1` holds
`x j ^^ x (j + 1)`. -/
def code (x : ℕ → Bool) : ℕ → Bool
  | 0 => x 0
  | j + 1 => x j ^^ x (j + 1)

/-- The code positions up to `a` sum to `x a`. -/
theorem sum_range_code (x : ℕ → Bool) (a : ℕ) : ∑ j ∈ range (a + 1), code x j = x a := by
  induction a with
  | zero => simp [code]
  | succ a ih =>
    rw [sum_range_succ, ih, code]
    cases x a <;> cases x (a + 1) <;> rfl

/-- If `x M` vanishes, the code positions after `a`, up to `M`, also sum to `x a`. -/
theorem sum_Ico_code {x : ℕ → Bool} {M a : ℕ} (hx : x M = false) (ha : a ≤ M) :
    ∑ j ∈ Ico (a + 1) (M + 1), code x j = x a := by
  have h := sum_range_add_sum_Ico (code x) (Nat.succ_le_succ ha)
  rw [sum_range_code, sum_range_code, hx] at h
  revert h
  cases x a <;> cases ∑ j ∈ Ico (a + 1) (M + 1), code x j <;> decide

/-- With requests `a` and `b`, the first request uses position `j` when the requests are in
order and `j ≤ a`, or out of order and `a < j`. -/
def first (a b j : ℕ) : Bool :=
  decide (a ≤ b ↔ j ≤ a)

/-- With requests `a` and `b`, the second request uses position `j` when the requests are in
order and `b < j`, or out of order and `j ≤ b`. -/
def second (a b j : ℕ) : Bool :=
  decide (a ≤ b ↔ b < j)

/-- No code position serves both requests, including when `a = b`. -/
theorem second_eq_false_of_first {a b j : ℕ} (h : first a b j = true) : second a b j = false := by
  simp only [first, second, decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢
  omega

private theorem sum_and_eq_sum_filter (s : Finset ℕ) (c v : ℕ → Bool) :
    ∑ j ∈ s, (c j && v j) = ∑ j ∈ s.filter (fun j => c j = true), v j := by
  rw [sum_filter]
  exact sum_congr rfl fun j _ => by cases c j <;> rfl

/-- The first request recovers `x a` from its positions. The other index is arbitrary. -/
theorem sum_first_code {x : ℕ → Bool} {M a : ℕ} (hx : x M = false) (ha : a < M) (b : ℕ) :
    ∑ j ∈ range (M + 1), (first a b j && code x j) = x a := by
  rw [sum_and_eq_sum_filter]
  by_cases hab : a ≤ b
  · rw [show (range (M + 1)).filter (fun j => first a b j = true) = range (a + 1) by
      ext j; simp only [mem_filter, mem_range, first, decide_eq_true_eq]; omega]
    exact sum_range_code x a
  · rw [show (range (M + 1)).filter (fun j => first a b j = true) = Ico (a + 1) (M + 1) by
      ext j; simp only [mem_filter, mem_range, mem_Ico, first, decide_eq_true_eq]; omega]
    exact sum_Ico_code hx ha.le

/-- The second request recovers `x b` from its positions. The other index is arbitrary. -/
theorem sum_second_code {x : ℕ → Bool} {M b : ℕ} (hx : x M = false) (hb : b < M) (a : ℕ) :
    ∑ j ∈ range (M + 1), (second a b j && code x j) = x b := by
  rw [sum_and_eq_sum_filter]
  by_cases hab : a ≤ b
  · rw [show (range (M + 1)).filter (fun j => second a b j = true) = Ico (b + 1) (M + 1) by
      ext j; simp only [mem_filter, mem_range, mem_Ico, second, decide_eq_true_eq]; omega]
    exact sum_Ico_code hx hb.le
  · rw [show (range (M + 1)).filter (fun j => second a b j = true) = range (b + 1) by
      ext j; simp only [mem_filter, mem_range, second, decide_eq_true_eq]; omega]
    exact sum_range_code x b

/-- Route the first input `z` to the first request's positions and `z'` to all others. Then
the first request recovers its bit of `z`. -/
theorem sum_first_code_route {Z : Type*} {h : Z → ℕ → Bool} {M a : ℕ}
    (hM : ∀ z, h z M = false) (ha : a < M) (b : ℕ) (z z' : Z) :
    ∑ j ∈ range (M + 1), (first a b j && code (h (if first a b j then z else z')) j) =
      h z a := by
  rw [← sum_first_code (hM z) ha b]
  exact sum_congr rfl fun j _ => by cases first a b j <;> rfl

/-- With the same routing, the second request recovers its bit of `z'`. -/
theorem sum_second_code_route {Z : Type*} {h : Z → ℕ → Bool} {M b : ℕ}
    (hM : ∀ z, h z M = false) (hb : b < M) (a : ℕ) (z z' : Z) :
    ∑ j ∈ range (M + 1), (second a b j && code (h (if first a b j then z else z')) j) =
      h z' b := by
  rw [← sum_second_code (hM z') hb a]
  refine sum_congr rfl fun j _ => ?_
  cases hs : second a b j
  · rfl
  · have hf : first a b j = false := by
      cases hf : first a b j
      · rfl
      · exact absurd (second_eq_false_of_first hf) (by simp [hs])
    simp [hf]

end Cslib.BitString.Uhlig
