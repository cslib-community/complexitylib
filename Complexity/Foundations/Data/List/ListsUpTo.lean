/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring

/-!
# Short lists over a list

`List.listsUpTo l r` lists the lists of length at most `r` whose entries come from `l`
(`List.mem_listsUpTo`). There are at most `(l.length + 1) ^ r` of them
(`List.length_listsUpTo_le`), so for a fixed `r` the listing has polynomial length.

## Main definitions

* `List.listsUpTo`: the lists of length at most `r` with entries from `l`.

## Main results

* `List.mem_listsUpTo`: membership in `List.listsUpTo l r`.
* `List.length_listsUpTo_le`: there are at most `(l.length + 1) ^ r` such lists.
* `List.nodup_listsUpTo`: over a list without duplicates, the listing has no duplicates.
-/

@[expose] public section

namespace List

variable {α : Type*}

/-- The lists of length at most `r` with entries from `l`: the empty list, then each entry of `l`
followed by each list of length at most `r - 1`. -/
def listsUpTo (l : List α) : ℕ → List (List α)
  | 0 => [[]]
  | r + 1 => [] :: l.flatMap fun a => (listsUpTo l r).map (a :: ·)

/-- A list is in `listsUpTo l r` exactly when it has length at most `r` and entries from `l`. -/
theorem mem_listsUpTo {l : List α} {r : ℕ} {P : List α} :
    P ∈ listsUpTo l r ↔ P.length ≤ r ∧ ∀ a ∈ P, a ∈ l := by
  induction r generalizing P with
  | zero => cases P <;> simp [listsUpTo]
  | succ r ih =>
    cases P with
    | nil => simp [listsUpTo]
    | cons a P =>
      simp only [listsUpTo, mem_cons, reduceCtorEq, false_or, mem_flatMap, mem_map,
        cons.injEq, length_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨b, hb, Q, hQ, rfl, rfl⟩
        have := ih.1 hQ
        exact ⟨by omega, hb, this.2⟩
      · rintro ⟨hlen, ha, hP⟩
        exact ⟨a, ha, P, ih.2 ⟨by omega, hP⟩, rfl, rfl⟩

/-- There are at most `(l.length + 1) ^ r` lists of length at most `r` with entries from `l`. -/
theorem length_listsUpTo_le (l : List α) (r : ℕ) :
    (listsUpTo l r).length ≤ (l.length + 1) ^ r := by
  induction r with
  | zero => simp [listsUpTo]
  | succ r ih =>
    simp only [listsUpTo, length_cons, length_flatMap, length_map, map_const', sum_replicate,
      smul_eq_mul]
    calc l.length * (listsUpTo l r).length + 1
        ≤ l.length * (l.length + 1) ^ r + (l.length + 1) ^ r := by
          gcongr
          exact Nat.one_le_pow _ _ (by omega)
      _ = (l.length + 1) ^ (r + 1) := by ring

/-- Over a list without duplicates, the short lists have no duplicates. -/
theorem nodup_listsUpTo {l : List α} (hl : l.Nodup) (r : ℕ) : (l.listsUpTo r).Nodup := by
  induction r with
  | zero => simp [listsUpTo]
  | succ r ih =>
    rw [listsUpTo, nodup_cons, nodup_flatMap]
    refine ⟨by simp, fun a _ => ih.map cons_injective, ?_⟩
    refine hl.pairwise_of_forall_ne fun a _ b _ hab P hPa hPb => ?_
    obtain ⟨Q, -, rfl⟩ := mem_map.1 hPa
    obtain ⟨Q', -, h⟩ := mem_map.1 hPb
    exact hab (cons.inj h).1.symm

end List
