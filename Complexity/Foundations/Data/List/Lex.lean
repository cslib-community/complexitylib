/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/List/Lex.lean`)

public import Complexity.Init
public import Mathlib.Data.List.Lex

/-!
# Prefixes and intervals in the lexicographic order on lists

A prefix of a list is lexicographically at most that list (`List.isPrefix_le`), and the extensions
of any prefix form an order-convex interval under the lexicographic order
(`List.IsPrefix.of_le_of_le`, `List.IsPrefix.of_prefix_of_le_of_le`). Lists of equal length keep a
strict comparison when anything is appended to them (`List.append_lt_append_of_lt_of_length_eq`).

Mathlib's lexicographic `LinearOrder` on lists replaces core's `≤` on lists, so core's
`List.cons_le_cons_iff` does not apply to it; `List.cons_le_cons_iff'` is its counterpart.

## Main results

* `List.cons_le_cons_iff'`: `a :: l ≤ b :: l'` iff `a < b`, or `a = b` and `l ≤ l'`.
* `List.append_lt_append_of_lt_of_length_eq`: if `a < b` and `a`, `b` have the same length, then
  `a ++ c < b ++ d`.
* `List.isPrefix_le`: if `a <+: b`, then `a ≤ b` lexicographically.
* `List.IsPrefix.of_le_of_le`: if `p <+: b` and `p ≤ c ≤ b`, then `p <+: c`.
* `List.IsPrefix.of_prefix_of_le_of_le`: if `p <+: a`, `p <+: b`, and `a ≤ c ≤ b`, then `p <+: c`.
-/

@[expose] public section

namespace List

universe u
variable {α : Type u} [LinearOrder α]

/-- Comparing lists with heads: compare the heads, and the tails when the heads agree. -/
theorem cons_le_cons_iff' {a b : α} {l l' : List α} :
    a :: l ≤ b :: l' ↔ a < b ∨ a = b ∧ l ≤ l' := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, show a :: l < b :: l' ↔ Lex (· < ·) (a :: l) (b :: l')
    from Iff.rfl, cons_lex_cons_iff]
  constructor
  · rintro ((h | ⟨rfl, h⟩) | h)
    · exact .inl h
    · exact .inr ⟨rfl, .inl h⟩
    · obtain ⟨rfl, rfl⟩ := List.cons.inj h
      exact .inr ⟨rfl, .inr rfl⟩
  · rintro (h | ⟨rfl, h | rfl⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr ⟨rfl, h⟩)
    · exact .inr rfl

/-- A strict comparison between lists of the same length survives appending anything to them:
it is decided at a position inside both. -/
theorem append_lt_append_of_lt_of_length_eq {a b : List α} (h : a < b)
    (hlen : a.length = b.length) (c d : List α) : a ++ c < b ++ d := by
  change Lex (· < ·) a b at h
  change Lex (· < ·) (a ++ c) (b ++ d)
  induction h with
  | nil => simp at hlen
  | cons _ ih => exact .cons (ih (by simpa using hlen))
  | rel h => exact .rel h

/-- A list is lexicographically at most every list it is a prefix of. -/
theorem isPrefix_le {a b : List α} (h : a <+: b) : a ≤ b := by
  obtain ⟨tail, rfl⟩ := h
  induction a with
  | nil =>
    cases tail with
    | nil => exact le_rfl
    | cons _ _ => exact le_of_lt (show ([] : List α) < _ from List.Lex.nil)
  | cons a as ih => exact List.cons_le_cons a ih

/-- A list lexicographically between a prefix `p` of `b` and `b` itself also has `p` as a prefix. -/
theorem IsPrefix.of_le_of_le {p b c : List α}
    (hb : p <+: b) (hpc : p ≤ c) (hcb : c ≤ b) : p <+: c := by
  induction p generalizing b c with
  | nil => exact List.nil_prefix
  | cons h p ih =>
    obtain ⟨bs, rfl⟩ := hb
    cases c with
    | nil =>
      have hlt : ([] : List α) < h :: p := List.Lex.nil
      exact (not_lt_of_ge hpc hlt).elim
    | cons k cs =>
      have head_le {a b : α} {as bs : List α} (hh : a :: as ≤ b :: bs) : a ≤ b := by
        rcases lt_or_eq_of_le hh with hh | hh
        · exact List.head_le_of_lt hh
        · exact (List.cons.inj hh).1.le
      have hk : h = k := le_antisymm (head_le hpc) (head_le hcb)
      subst k
      have tail_le {as bs : List α} (hh : h :: as ≤ h :: bs) : as ≤ bs := by
        rcases lt_or_eq_of_le hh with hh | hh
        · exact le_of_lt (show as < bs from List.lex_cons_iff.mp hh)
        · exact (List.cons.inj hh).2.le
      obtain ⟨ds, he⟩ := ih ⟨bs, rfl⟩ (tail_le hpc) (tail_le hcb)
      exact ⟨ds, congrArg (List.cons h) he⟩

/-- Lists with a common prefix form a lexicographic interval. -/
theorem IsPrefix.of_prefix_of_le_of_le {p a b c : List α}
    (ha : p <+: a) (hb : p <+: b) (hac : a ≤ c) (hcb : c ≤ b) : p <+: c :=
  hb.of_le_of_le ((isPrefix_le ha).trans hac) hcb

end List
