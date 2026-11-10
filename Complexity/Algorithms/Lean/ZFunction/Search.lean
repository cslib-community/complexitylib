/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.KMP.Search
public import Complexity.Algorithms.Lean.ZFunction.Basic
import Mathlib.Data.List.Sort

/-!
# Exact pattern matching with the Z-algorithm

The pattern `p` occurs in the text `t` at shift `i` iff the Z-function of `p ++ t` is at least
`|p|` at position `|p| + i` (`[Gusfield1997]`, Section 1.5). `zMatchesM p t` computes the
Z-function of `p ++ t` with the Z-algorithm and reads off these shifts. Its output is the KMP
specification `kmpMatchesList p t` (`zMatches_eq_kmpMatchesList`), and it makes at most
`2 * (|p| + |t|) - 3` character comparisons.

## Source Conventions

* **Shifts:** `0`-indexed, as in `Cslib.Algorithms.Lean.KMP`. The shift `|t|` is reported exactly
  when `p` is empty.
* **No separator:** Gusfield uses `p $ t` with a separator `$` that occurs in neither word. Here
  there is no separator: values of the Z-function above `|p|` are allowed, and a shift `i` is
  reported when the value at `|p| + i` is at least `|p|`.

## Cost Model

As in `Cslib.Algorithms.Lean.ZFunction.Basic`: one `TimeM` tick per character comparison.
Building `p ++ t` and filtering the shifts are free.

## Main definitions

* `Cslib.Algorithms.Lean.ZFunction.zMatchesM`, `zMatches`: the shifts of `p` in `t` from the
  Z-function of `p ++ t`.

## Main results

* `Cslib.Algorithms.Lean.ZFunction.mem_zMatches_iff`: `i ∈ zMatches p t` iff `i ≤ |t|` and `p`
  is a prefix of `t.drop i`.
* `Cslib.Algorithms.Lean.ZFunction.zMatches_eq_kmpMatchesList`: the Z-algorithm and KMP report
  the same shifts.
* `Cslib.Algorithms.Lean.ZFunction.zMatchesM_time_le`: at most `2 * (|p| + |t|) - 3` character
  comparisons.

## References

* [D. Gusfield, *Algorithms on Strings, Trees, and Sequences*][Gusfield1997]
-/

public section

namespace Cslib.Algorithms.Lean.ZFunction

open Cslib.Algorithms.Lean

variable {α : Type*} [DecidableEq α]

/-- The shifts `i ≤ |t|` at which `p` occurs in `t`, read off the Z-function of `p ++ t`: those
whose value at `|p| + i` is at least `|p|`. The value past the end is taken to be `0`. -/
def zMatchesM (p t : Array α) : TimeM ℕ (List ℕ) := do
  let z ← zAlgorithmM (p ++ t)
  return (List.range (t.size + 1)).filter fun i => p.size ≤ z.getD (p.size + i) 0

/-- Exact pattern matching with the Z-algorithm on lists. -/
def zMatches (p t : List α) : List ℕ :=
  (zMatchesM p.toArray t.toArray).ret

/-- **Correctness of Z-algorithm matching**: `i ∈ zMatches p t` iff `p` occurs in `t` at shift
`i`. -/
theorem mem_zMatches_iff (p t : List α) (i : ℕ) :
    i ∈ zMatches p t ↔ i ≤ t.length ∧ p <+: t.drop i := by
  have hz := ret_zAlgorithmM (p.toArray ++ t.toArray)
  rw [Array.toList_append, List.toList_toArray, List.toList_toArray] at hz
  have hsize : (zAlgorithmM (p.toArray ++ t.toArray)).ret.size = p.length + t.length := by
    grind [Array.length_toList, length_zFunction, List.length_append]
  simp only [zMatches, zMatchesM, TimeM.ret_bind, TimeM.ret_pure, List.mem_filter,
    List.mem_range, decide_eq_true_eq, List.size_toArray]
  by_cases hi : i < t.length
  · have hget : (zAlgorithmM (p.toArray ++ t.toArray)).ret.getD (p.length + i) 0 =
        List.lcpLen (p ++ t) (t.drop i) := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega), Option.getD_some,
        ← Array.getElem_toList]
      simp only [hz, getElem_zFunction, List.drop_append, List.drop_eq_nil_of_le (Nat.le_add_right
        p.length i), List.nil_append, Nat.add_sub_cancel_left]
    rw [hget, List.length_le_lcpLen_append_iff]
    exact ⟨fun ⟨_, h⟩ => ⟨by omega, h⟩, fun ⟨_, h⟩ => ⟨by omega, h⟩⟩
  · constructor
    · rintro ⟨hit, hle⟩
      have hit : i = t.length := by omega
      subst hit
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega),
        Option.getD_none] at hle
      have hp : p = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
      subst hp
      exact ⟨le_refl _, List.nil_prefix⟩
    · rintro ⟨hit, hpre⟩
      have hit : i = t.length := by omega
      subst hit
      rw [List.drop_length, List.prefix_nil] at hpre
      subst hpre
      exact ⟨by omega, by simp only [List.length_nil, Nat.zero_le]⟩

/-- `zMatches p t` lists the shifts in strictly increasing order. -/
theorem pairwise_lt_zMatches (p t : List α) : (zMatches p t).Pairwise (· < ·) := by
  simp only [zMatches, zMatchesM, TimeM.ret_bind, TimeM.ret_pure]
  exact List.pairwise_lt_range.filter _

/-- **Z-algorithm matching agrees with KMP**: both report the shifts of `p` in `t` in increasing
order. -/
theorem zMatches_eq_kmpMatchesList (p t : List α) : zMatches p t = KMP.kmpMatchesList p t :=
  (pairwise_lt_zMatches p t).eq_of_mem_iff (KMP.pairwise_lt_kmpMatchesList p t) fun i => by
    rw [mem_zMatches_iff, KMP.mem_kmpMatchesList_iff]

/-- **Linear bound for Z-algorithm matching**: at most `2 * (|p| + |t|) - 3` character
comparisons. -/
theorem zMatchesM_time_le (p t : Array α) :
    (zMatchesM p t).time ≤ 2 * (p.size + t.size) - 3 := by
  have := zAlgorithmM_time_le (p ++ t)
  rw [Array.size_append] at this
  simp only [zMatchesM, TimeM.time_bind, TimeM.time_pure, Nat.add_zero]
  exact this

end Cslib.Algorithms.Lean.ZFunction
