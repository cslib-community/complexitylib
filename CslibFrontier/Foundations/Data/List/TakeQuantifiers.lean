/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Basic

/-!
# Quantifying over words through a prefix

A predicate that looks only at the first `n` entries of a word of length `m ≥ n` holds for some
(every) such word exactly when it holds for some (every) word of length `n`: a short word is the
prefix of its padding (`List.exists_length_eq_take_iff`, `List.forall_length_eq_take_iff`).
Complexity-class arguments use this to pad certificate blocks to longer, uniform or easily computed
lengths and let the verifier cut them back.

## Main results

* `List.exists_length_eq_take_iff`, `List.forall_length_eq_take_iff`: quantifying over words of
  length `m` through their length-`n` prefix quantifies over words of length `n`.
-/

public section

namespace List

variable {α : Type*} [Inhabited α] {n m : ℕ} {P : List α → Prop}

/-- Some word of length `m ≥ n` has a length-`n` prefix satisfying `P` exactly when some word of
length `n` satisfies `P`. -/
theorem exists_length_eq_take_iff (h : n ≤ m) :
    (∃ w : List α, w.length = m ∧ P (w.take n)) ↔ ∃ w : List α, w.length = n ∧ P w := by
  refine ⟨fun ⟨w, hw, hP⟩ => ⟨w.take n, by rw [length_take, hw, Nat.min_eq_left h], hP⟩,
    fun ⟨w, hw, hP⟩ => ⟨w ++ replicate (m - n) default, ?_, ?_⟩⟩
  · rw [length_append, length_replicate, hw, Nat.add_sub_cancel' h]
  · rwa [take_left' hw]

/-- Every word of length `m ≥ n` has a length-`n` prefix satisfying `P` exactly when every word of
length `n` satisfies `P`. -/
theorem forall_length_eq_take_iff (h : n ≤ m) :
    (∀ w : List α, w.length = m → P (w.take n)) ↔ ∀ w : List α, w.length = n → P w := by
  refine ⟨fun hP w hw => ?_,
    fun hP w hw => hP _ (by rw [length_take, hw, Nat.min_eq_left h])⟩
  have := hP (w ++ replicate (m - n) default)
    (by rw [length_append, length_replicate, hw, Nat.add_sub_cancel' h])
  rwa [take_left' hw] at this

end List
