/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Basic
public import Mathlib.Order.Basic

/-!
# Ranks and blocks in sorted lists

In a list sorted by a key, the entries with a given key form one contiguous block, which starts
right after the entries with smaller keys. These facts underlie counting-sort and rank arguments,
such as the LF-mapping of the Burrows–Wheeler transform.

## Main results

* `List.getElem?_filter_countP_take`: among the entries satisfying `p`, entry `r` sits at the
  number of earlier entries satisfying `p`.
* `List.Pairwise.filter_key_eq`: in a list sorted by a key `f`, the entries with key `g` are the
  block that starts after the entries with smaller key.
* `List.Pairwise.count_take_countP_lt_add`: in a sorted list, the prefix that ends `k` places
  into the block of `c` contains `min k (l.count c)` copies of `c`.
-/

public section

namespace List

/-- Among the entries satisfying `p`, entry `r` is preceded by exactly the matching entries of
`l.take r`. -/
theorem getElem?_filter_countP_take {α : Type*} (p : α → Bool) {l : List α} {r : ℕ}
    (hr : r < l.length) (hp : p l[r]) :
    (l.filter p)[(l.take r).countP p]? = some l[r] := by
  have hl : l = l.take r ++ l[r] :: l.drop (r + 1) := by
    rw [← drop_eq_getElem_cons hr, take_append_drop]
  have : l.filter p = (l.take r).filter p ++ l[r] :: (l.drop (r + 1)).filter p := by
    conv_lhs => rw [hl]
    rw [filter_append, filter_cons_of_pos hp]
  rw [this, countP_eq_length_filter, getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- In a list sorted by a key `f`, the entries with key `g` form one block, which starts after
the entries with smaller key. -/
theorem Pairwise.filter_key_eq {α β : Type*} [LinearOrder β] (f : α → β) (g : β) :
    ∀ {l : List α}, l.Pairwise (fun x y => f x ≤ f y) →
      l.filter (fun x => f x = g) =
        (l.drop (l.countP (fun x => f x < g))).take (l.countP (fun x => f x = g))
  | [], _ => by simp
  | x :: l, h => by
    rw [pairwise_cons] at h
    have ih := Pairwise.filter_key_eq f g h.2
    rcases lt_trichotomy (f x) g with hx | hx | hx
    · have e1 : (x :: l).countP (fun x => f x < g) = l.countP (fun x => f x < g) + 1 :=
        countP_cons_of_pos (by simpa using hx)
      have e2 : (x :: l).countP (fun x => f x = g) = l.countP (fun x => f x = g) :=
        countP_cons_of_neg (by simpa using hx.ne)
      rw [filter_cons_of_neg (by simpa using hx.ne), e1, e2, drop_succ_cons]
      exact ih
    · have hlt : l.countP (fun x => f x < g) = 0 :=
        countP_eq_zero.mpr fun y hy => by simpa [← hx] using h.1 y hy
      have e1 : (x :: l).countP (fun x => f x < g) = 0 := by
        rw [countP_cons_of_neg (by simp [hx]), hlt]
      have e2 : (x :: l).countP (fun x => f x = g) = l.countP (fun x => f x = g) + 1 :=
        countP_cons_of_pos (by simpa using hx)
      rw [hlt, drop_zero] at ih
      rw [filter_cons_of_pos (by simpa using hx), e1, e2, drop_zero, ih, take_succ_cons]
    · have hne : ∀ y ∈ l, ¬ f y = g ∧ ¬ f y < g := fun y hy =>
        ⟨(lt_of_lt_of_le hx (h.1 y hy)).ne', not_lt.mpr (hx.le.trans (h.1 y hy))⟩
      have h1 : l.countP (fun x => f x < g) = 0 :=
        countP_eq_zero.mpr fun y hy => by simpa using (hne y hy).2
      have h2 : l.countP (fun x => f x = g) = 0 :=
        countP_eq_zero.mpr fun y hy => by simpa using (hne y hy).1
      have h3 : l.filter (fun x => f x = g) = [] :=
        filter_eq_nil_iff.mpr fun y hy => by simpa using (hne y hy).1
      simp [hx.ne', not_lt.mpr hx.le, h1, h2, h3]

/-- In a sorted list, the prefix that ends `k` places into the block of `c` contains
`min k (l.count c)` copies of `c`. -/
theorem Pairwise.count_take_countP_lt_add {α : Type*} [LinearOrder α] (c : α) (k : ℕ) :
    ∀ {l : List α}, l.Pairwise (· ≤ ·) →
      (l.take (l.countP (· < c) + k)).count c = min k (l.count c)
  | [], _ => by simp
  | x :: l, h => by
    rw [pairwise_cons] at h
    rcases lt_trichotomy x c with hx | rfl | hx
    · rw [countP_cons_of_pos (by simpa using hx), Nat.add_right_comm, take_succ_cons,
        count_cons_of_ne hx.ne, count_cons_of_ne hx.ne,
        Pairwise.count_take_countP_lt_add c k h.2]
    · have hlt : l.countP (· < x) = 0 :=
        countP_eq_zero.mpr fun y hy => by simpa using h.1 y hy
      rw [countP_cons_of_neg (by simp), hlt, Nat.zero_add, count_cons_self]
      cases k with
      | zero => simp
      | succ k =>
        rw [take_succ_cons, count_cons_self]
        have := Pairwise.count_take_countP_lt_add x k h.2
        rw [hlt, Nat.zero_add] at this
        rw [this, Nat.succ_min_succ]
    · have hne : ∀ y ∈ l, ¬ y < c ∧ y ≠ c := fun y hy =>
        ⟨not_lt.mpr (hx.le.trans (h.1 y hy)), (lt_of_lt_of_le hx (h.1 y hy)).ne'⟩
      have h1 : (x :: l).countP (· < c) = 0 :=
        countP_eq_zero.mpr fun y hy => by
          rcases mem_cons.mp hy with rfl | hy
          · simpa using not_lt.mpr hx.le
          · simpa using (hne y hy).1
      have h2 : (x :: l).count c = 0 :=
        count_eq_zero.mpr fun hy => by
          rcases mem_cons.mp hy with h' | hy
          · exact hx.ne' h'.symm
          · exact (hne c hy).2 rfl
      rw [h1, h2, Nat.zero_add, Nat.min_zero, count_eq_zero]
      exact fun hc => count_eq_zero.mp h2 (take_subset _ _ hc)

end List
