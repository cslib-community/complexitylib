/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.List.Append
public import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.GetD

/-!
# Unary coding of natural numbers

The delimiter-terminated unary code `unaryCode n = 1ⁿ 0` encodes natural numbers as Boolean words
such that concatenations of encoded words are uniquely decodable (`flatMap_unaryCode_injective`).

## Main definitions

* `List.unaryCode`: `n` copies of `true` followed by `false`.

## Main results

* `List.flatMap_unaryCode_injective`: concatenated unary codes uniquely determine the sequence of
  numbers.
* `List.primrec_unaryCode`: the unary encoding is primitive recursive.
* `List.getD_replicate_true_append_false_of_le`, `List.getD_replicate_true_append_false_add`: the
  bits of a unary block followed by `false`, and of what follows it.
-/

public section

namespace List

/-- The unary code of a natural number: `n` letters `true` followed by `false`. Distinct
sequences of numbers have distinct concatenated codes. -/
@[expose] def unaryCode (n : ℕ) : List Bool := List.replicate n true ++ [false]

theorem flatMap_unaryCode_injective : Function.Injective fun w : List ℕ => w.flatMap unaryCode := by
  intro u
  induction u with
  | nil =>
    rintro (_ | ⟨n, v⟩) h
    · rfl
    · simp [unaryCode] at h
  | cons m u ih =>
    rintro (_ | ⟨n, v⟩) h
    · simp [unaryCode] at h
    · simp only [List.flatMap_cons, unaryCode, List.append_assoc, List.singleton_append] at h
      obtain ⟨rfl, hx⟩ := List.replicate_true_append_false_inj h
      rw [ih hx]

theorem primrec_unaryCode : Primrec unaryCode := by
  have : Primrec fun n => (List.range n).map fun _ => true :=
    Primrec.list_map Primrec.list_range (Primrec.const true).to₂
  refine (Primrec.list_append.comp this (Primrec.const [false])).of_eq fun n => ?_
  rw [unaryCode, List.map_const', List.length_range]

/-- Within a unary block of `true` bits followed by `false`, the bits are set before the end of
the block. -/
theorem getD_replicate_true_append_false_of_le {m i : ℕ} (l : List Bool) (h : i ≤ m) :
    (replicate m true ++ false :: l).getD i false = decide (i < m) := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · rw [getD_append _ _ _ _ (by simpa using h)]
    simp [h]
  · rw [getD_append_right _ _ _ _ (by simp)]
    simp

/-- After a unary block of `m` `true` bits followed by `false`, the bits are those of the rest. -/
theorem getD_replicate_true_append_false_add (m i : ℕ) (l : List Bool) :
    (replicate m true ++ false :: l).getD (m + 1 + i) false = l.getD i false := by
  rw [getD_append_right _ _ _ _ (by simp only [length_replicate]; omega)]
  simp only [length_replicate, show m + 1 + i - m = i + 1 by omega, getD_cons_succ]

end List
