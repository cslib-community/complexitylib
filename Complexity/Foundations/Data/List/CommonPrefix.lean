/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Lex
import Complexity.Foundations.Data.List.Lex

/-!
# Length of the longest common prefix of two lists

`List.lcpLen u v` is the length of the longest common prefix of `u` and `v`. The string algorithms
use it as a specification: suffix and LCP arrays
(`Complexity.Algorithms.Lean.SuffixArray`) and the Z-function
(`Complexity.Algorithms.Lean.ZFunction`).

## Main definitions

* `List.lcpLen`: length of the longest common prefix of two lists.

## Main results

* `List.le_lcpLen_iff`: `k ≤ lcpLen u v` iff both lists have length at least `k` and agree on
  their first `k` entries.
* `List.lcpLen_eq_add_lcpLen_drop`: a known common prefix of length `h` splits off.
* `List.min_lcpLen_eq_of_take_eq`: lists that agree on their first `m` entries have the same
  longest common prefix with any list, up to `m`.
* `List.length_le_lcpLen_append_iff`: `u ++ x` and `v` share `|u|` leading entries iff `u` is a
  prefix of `v`.
* `List.lcpLen_le_lcpLen_of_le_of_le_left` and `List.lcpLen_le_lcpLen_of_le_of_le_right`: a list
  lexicographically between two others shares their longest common prefix.
-/

public section

namespace List

variable {α : Type*}

/-- Length of the longest common prefix of `u` and `v`. -/
def lcpLen [DecidableEq α] : List α → List α → ℕ
  | a :: u, b :: v => if a = b then lcpLen u v + 1 else 0
  | _, _ => 0

section lcp

variable [DecidableEq α]

@[simp] theorem lcpLen_nil_left (v : List α) : lcpLen [] v = 0 := by
  cases v <;> rfl

@[simp] theorem lcpLen_nil_right (u : List α) : lcpLen u [] = 0 := by
  cases u <;> rfl

theorem lcpLen_cons_cons (a b : α) (u v : List α) :
    lcpLen (a :: u) (b :: v) = if a = b then lcpLen u v + 1 else 0 := by
  rw [lcpLen]

@[simp] theorem lcpLen_cons_cons_self (a : α) (u v : List α) :
    lcpLen (a :: u) (a :: v) = lcpLen u v + 1 := by
  simp only [lcpLen_cons_cons, ↓reduceIte]

@[simp] theorem lcpLen_self (u : List α) : lcpLen u u = u.length := by
  induction u with
  | nil => rw [lcpLen_nil_left, length_nil]
  | cons a u ih => rw [lcpLen_cons_cons_self, ih, length_cons]

theorem lcpLen_comm (u v : List α) : lcpLen u v = lcpLen v u := by
  induction u generalizing v with
  | nil => simp only [lcpLen_nil_left, lcpLen_nil_right]
  | cons a u ih =>
    cases v with
    | nil => simp only [lcpLen_nil_left, lcpLen_nil_right]
    | cons b v =>
      simp only [lcpLen_cons_cons, ih v]
      by_cases h : a = b
      · simp only [h, ↓reduceIte]
      · simp only [h, ↓reduceIte, Ne.symm h]

theorem lcpLen_le_length_left (u v : List α) : lcpLen u v ≤ u.length := by
  induction u generalizing v with
  | nil => simp only [lcpLen_nil_left, length_nil, Nat.le_refl]
  | cons a u ih =>
    cases v with
    | nil => simp only [lcpLen_nil_right, Nat.zero_le]
    | cons b v =>
      rw [lcpLen_cons_cons]
      split_ifs
      · have := ih v
        simp only [length_cons]
        omega
      · exact Nat.zero_le _

theorem lcpLen_le_length_right (u v : List α) : lcpLen u v ≤ v.length := by
  rw [lcpLen_comm]
  exact lcpLen_le_length_left v u

/-- `k ≤ lcpLen u v` iff both lists have length at least `k` and agree on their first `k`
entries. -/
theorem le_lcpLen_iff {u v : List α} {k : ℕ} :
    k ≤ lcpLen u v ↔ k ≤ u.length ∧ k ≤ v.length ∧ u.take k = v.take k := by
  induction k generalizing u v with
  | zero => simp only [Nat.zero_le, take_zero, and_self]
  | succ k ih =>
    cases u with
    | nil => simp only [lcpLen_nil_left, length_nil]; omega
    | cons a u =>
      cases v with
      | nil => simp only [lcpLen_nil_right, length_nil]; omega
      | cons b v =>
        rw [lcpLen_cons_cons, take_succ_cons, take_succ_cons, cons_eq_cons, length_cons,
          length_cons]
        by_cases hab : a = b
        · simp only [hab, ↓reduceIte, true_and, Nat.add_le_add_iff_right, ih]
        · simp only [hab, ↓reduceIte, false_and, and_false, iff_false]
          omega

/-- A common prefix of length `h` splits off the longest common prefix. -/
theorem lcpLen_eq_add_lcpLen_drop {u v : List α} {h : ℕ} (hh : h ≤ lcpLen u v) :
    lcpLen u v = h + lcpLen (u.drop h) (v.drop h) := by
  induction h generalizing u v with
  | zero => simp only [drop_zero, Nat.zero_add]
  | succ h ih =>
    cases u with
    | nil => simp only [lcpLen_nil_left] at hh; omega
    | cons a u =>
      cases v with
      | nil => simp only [lcpLen_nil_right] at hh; omega
      | cons b v =>
        rw [lcpLen_cons_cons] at hh ⊢
        by_cases hab : a = b
        · simp only [hab, ↓reduceIte] at hh ⊢
          rw [ih (by omega), drop_succ_cons, drop_succ_cons]
          omega
        · simp only [hab, ↓reduceIte] at hh
          omega

/-- Dropping one leading entry from both lists shortens their longest common prefix by at most
one. -/
theorem lcpLen_sub_one_le_lcpLen_tail (u v : List α) :
    lcpLen u v - 1 ≤ lcpLen u.tail v.tail := by
  cases u with
  | nil => simp only [lcpLen_nil_left, Nat.zero_sub, Nat.zero_le]
  | cons a u =>
    cases v with
    | nil => simp only [lcpLen_nil_right, Nat.zero_sub, Nat.zero_le]
    | cons b v =>
      rw [lcpLen_cons_cons, tail_cons, tail_cons]
      split_ifs <;> omega

/-- Lists that agree on their first `m` entries have the same longest common prefix with any
list `x`, up to `m`. -/
theorem min_lcpLen_eq_of_take_eq {u v : List α} (x : List α) {m : ℕ} (hu : m ≤ u.length)
    (hv : m ≤ v.length) (h : u.take m = v.take m) :
    min (lcpLen x u) m = min (lcpLen x v) m := by
  have key : ∀ k ≤ m, k ≤ lcpLen x u ↔ k ≤ lcpLen x v := by
    intro k hk
    have huk : u.take k = v.take k := by
      rw [← Nat.min_eq_left hk, ← take_take, h, take_take]
    rw [le_lcpLen_iff, le_lcpLen_iff, huk]
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, by omega, h3⟩, fun ⟨h1, _, h3⟩ => ⟨h1, by omega, h3⟩⟩
  have h1 := (key (min (lcpLen x u) m) (Nat.min_le_right _ _)).mp (Nat.min_le_left _ _)
  have h2 := (key (min (lcpLen x v) m) (Nat.min_le_right _ _)).mpr (Nat.min_le_left _ _)
  omega

/-- `u ++ x` and `v` share their first `|u|` entries iff `u` is a prefix of `v`. -/
theorem length_le_lcpLen_append_iff {u x v : List α} :
    u.length ≤ lcpLen (u ++ x) v ↔ u <+: v := by
  rw [le_lcpLen_iff, take_left, prefix_iff_eq_take, length_append]
  constructor
  · rintro ⟨_, _, h⟩
    exact h
  · intro h
    have := congrArg length h
    rw [length_take] at this
    exact ⟨by omega, by omega, h⟩

end lcp

section order

variable [LinearOrder α]

/-- A list lexicographically between `u` and `x` shares at least `lcpLen u x` leading entries
with `u`. -/
theorem lcpLen_le_lcpLen_of_le_of_le_left {u v x : List α} (huv : u ≤ v) (hvx : v ≤ x) :
    lcpLen u x ≤ lcpLen u v := by
  set k := lcpLen u x
  obtain ⟨hku, hkx, htake⟩ := le_lcpLen_iff.mp (le_refl k)
  have hpu : u.take k <+: u := take_prefix k u
  have hpx : u.take k <+: x := htake ▸ take_prefix k x
  have hpv : u.take k <+: v := IsPrefix.of_prefix_of_le_of_le hpu hpx huv hvx
  have hlen : (u.take k).length = k := by simp only [length_take]; omega
  refine le_lcpLen_iff.mpr ⟨hku, ?_, ?_⟩
  · have := hpv.length_le; omega
  · have := prefix_iff_eq_take.mp hpv
    rw [hlen] at this
    exact this

/-- A list lexicographically between `u` and `x` shares at least `lcpLen u x` leading entries
with `x`. -/
theorem lcpLen_le_lcpLen_of_le_of_le_right {u v x : List α} (huv : u ≤ v) (hvx : v ≤ x) :
    lcpLen u x ≤ lcpLen v x := by
  set k := lcpLen u x
  obtain ⟨hku, hkx, htake⟩ := le_lcpLen_iff.mp (le_refl k)
  have hpu : u.take k <+: u := take_prefix k u
  have hpx : u.take k <+: x := htake ▸ take_prefix k x
  have hpv : u.take k <+: v := IsPrefix.of_prefix_of_le_of_le hpu hpx huv hvx
  have hlen : (u.take k).length = k := by simp only [length_take]; omega
  refine le_lcpLen_iff.mpr ⟨?_, hkx, ?_⟩
  · have := hpv.length_le; omega
  · have := prefix_iff_eq_take.mp hpv
    rw [hlen] at this
    rw [← this, htake]

end order

end List
