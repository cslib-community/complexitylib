/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.Nodup
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Relation

/-!
# Breadth-first search by rounds

A round of breadth-first search (`Cslib.Reachability.expand`) appends to the list of the elements
found so far every successor of one of them that has not been found yet. The found elements stay
distinct, a round only appends, and a round adds nothing exactly when the found elements are
closed under successors. So if at most `N` distinct elements are reachable from `start`, after
`N` rounds from `[start]` (`Cslib.Reachability.search`) the found elements are exactly the
reachable ones (`Cslib.Reachability.mem_search_iff`): each round before closure finds a new
element. The number of rounds, not a search for a fixed point, keeps the algorithm a plain
iteration, as polynomial-time certificates need.

## Main definitions

* `Cslib.Reachability.insertNew`: append an element to a list if not already present.
* `Cslib.Reachability.expand`: one round of breadth-first search.
* `Cslib.Reachability.search`: a number of rounds from a start element.

## Main results

* `Cslib.Reachability.nodup_search`: the found elements are distinct.
* `Cslib.Reachability.reflTransGen_of_mem_search`: the found elements are reachable.
* `Cslib.Reachability.mem_search_iff`: after as many rounds as there are reachable elements, the
  found elements are the reachable ones.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 7.14][Sipser2013]
-/

@[expose] public section

namespace Cslib.Reachability

variable {α : Type*} [DecidableEq α] {succ : α → List α}

/-- Append an element unless it is already in the list. -/
def insertNew (found : List α) (a : α) : List α := if a ∈ found then found else found ++ [a]

/-- **One round of breadth-first search**: append, in order, every successor of a found element
that has not been found yet. -/
def expand (succ : α → List α) (found : List α) : List α :=
  (found.flatMap succ).foldl insertNew found

/-- `rounds` rounds of breadth-first search from `start`. -/
def search (succ : α → List α) (rounds : ℕ) (start : α) : List α :=
  (expand succ)^[rounds] [start]

/-- Zero rounds of breadth-first search return the singleton list `[start]`. -/
@[simp] theorem search_zero (start : α) : search succ 0 start = [start] := rfl

/-- `rounds + 1` rounds of breadth-first search apply `expand` to the result of `rounds` rounds. -/
theorem search_succ (rounds : ℕ) (start : α) :
    search succ (rounds + 1) start = expand succ (search succ rounds start) :=
  Function.iterate_succ_apply' _ _ _

private theorem prefix_foldl_insertNew (l found : List α) : found <+: l.foldl insertNew found := by
  induction l generalizing found with
  | nil => exact List.prefix_refl _
  | cons a l ih =>
    refine List.IsPrefix.trans ?_ (ih _)
    unfold insertNew
    split_ifs
    · exact List.prefix_refl _
    · exact List.prefix_append _ _

private theorem mem_foldl_insertNew {l found : List α} {a : α} :
    a ∈ l.foldl insertNew found ↔ a ∈ found ∨ a ∈ l := by
  induction l generalizing found with
  | nil => simp
  | cons b l ih =>
    rw [List.foldl_cons, ih, List.mem_cons]
    unfold insertNew
    split_ifs with hb
    · constructor
      · tauto
      · rintro (h | rfl | h)
        · exact .inl h
        · exact .inl hb
        · exact .inr h
    · simp only [List.mem_append, List.mem_singleton]
      tauto

private theorem nodup_foldl_insertNew {l found : List α} (h : found.Nodup) :
    (l.foldl insertNew found).Nodup := by
  induction l generalizing found with
  | nil => exact h
  | cons a l ih =>
    refine ih ?_
    unfold insertNew
    split_ifs with ha
    · exact h
    · exact List.nodup_append.mpr ⟨h, List.nodup_singleton a, fun b hb c hc => by
        rintro rfl
        exact ha (by simpa using List.mem_singleton.mp hc ▸ hb)⟩

/-- A round only appends. -/
theorem prefix_expand (found : List α) : found <+: expand succ found :=
  prefix_foldl_insertNew _ _

/-- The elements found after a round are those found before and their successors. -/
theorem mem_expand {found : List α} {a : α} :
    a ∈ expand succ found ↔ a ∈ found ∨ ∃ b ∈ found, a ∈ succ b := by
  rw [expand, mem_foldl_insertNew, List.mem_flatMap]

/-- A round keeps the found elements distinct. -/
theorem nodup_expand {found : List α} (h : found.Nodup) : (expand succ found).Nodup :=
  nodup_foldl_insertNew h

/-- A round adds nothing exactly when the found elements are closed under successors. -/
theorem expand_eq_self_iff {found : List α} :
    expand succ found = found ↔ ∀ b ∈ found, ∀ a ∈ succ b, a ∈ found := by
  constructor
  · intro h b hb a ha
    rw [← h]
    exact mem_expand.mpr (.inr ⟨b, hb, ha⟩)
  · intro h
    have hsub : ∀ l : List α, (∀ a ∈ l, a ∈ found) → l.foldl insertNew found = found := by
      intro l hl
      induction l with
      | nil => rfl
      | cons a l ih =>
        have ha : a ∈ found := hl a (by simp)
        simp only [List.foldl_cons, insertNew, ha, ↓reduceIte]
        exact ih fun b hb => hl b (by simp [hb])
    exact hsub _ fun a ha => by
      obtain ⟨b, hb, ha⟩ := List.mem_flatMap.mp ha
      exact h b hb a ha

/-- A round that adds something makes the list longer. -/
private theorem length_lt_expand {found : List α} (h : expand succ found ≠ found) :
    found.length < (expand succ found).length := by
  obtain ⟨rest, hrest⟩ := prefix_expand (succ := succ) found
  rcases rest with _ | ⟨a, rest⟩
  · exact absurd (by simpa using hrest.symm) h
  · rw [← hrest]
    simp

/-- The rounds only append. -/
theorem prefix_search {i j : ℕ} (hij : i ≤ j) (start : α) :
    search succ i start <+: search succ j start := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => exact List.prefix_refl _
  | succ d ih =>
    refine (ih (Nat.le_add_right _ _)).trans ?_
    rw [← Nat.add_assoc, search_succ]
    exact prefix_expand _

private theorem start_mem_search (rounds : ℕ) (start : α) : start ∈ search succ rounds start :=
  (prefix_search (Nat.zero_le rounds) start).subset (by simp)

/-- **The found elements are distinct.** -/
theorem nodup_search (rounds : ℕ) (start : α) : (search succ rounds start).Nodup := by
  induction rounds with
  | zero => exact List.nodup_singleton start
  | succ rounds ih =>
    rw [search_succ]
    exact nodup_expand ih

/-- **The found elements are reachable.** -/
theorem reflTransGen_of_mem_search {rounds : ℕ} {start a : α}
    (h : a ∈ search succ rounds start) : Relation.ReflTransGen (fun b c => c ∈ succ b) start a := by
  induction rounds generalizing a with
  | zero =>
    obtain rfl := List.mem_singleton.mp h
    exact .refl
  | succ rounds ih =>
    rw [search_succ] at h
    rcases mem_expand.mp h with h | ⟨b, hb, ha⟩
    · exact ih h
    · exact (ih hb).tail ha

/-- Each round before the found elements are closed finds a new element. -/
private theorem succ_le_length_search_or_closed (rounds : ℕ) (start : α) :
    rounds + 1 ≤ (search succ rounds start).length ∨
      expand succ (search succ rounds start) = search succ rounds start := by
  induction rounds with
  | zero => exact .inl (by simp)
  | succ rounds ih =>
    have hsucc := search_succ (succ := succ) rounds start
    by_cases hfix : expand succ (search succ rounds start) = search succ rounds start
    · exact .inr (by rw [hsucc, hfix, hfix])
    · rcases ih with ih | ih
      · exact .inl (by rw [hsucc]; have := length_lt_expand hfix; omega)
      · exact absurd ih hfix

/-- **After as many rounds as there are reachable elements, the found elements are the reachable
ones.** If every list of distinct elements reachable from `start` has at most `bound` entries, then
after at least `bound` rounds the found elements are closed under successors, so they include
every reachable element. -/
theorem mem_search_iff {rounds bound : ℕ} {start a : α}
    (hbound : ∀ l : List α, l.Nodup →
      (∀ b ∈ l, Relation.ReflTransGen (fun b c => c ∈ succ b) start b) → l.length ≤ bound)
    (hrounds : bound ≤ rounds) :
    a ∈ search succ rounds start ↔ Relation.ReflTransGen (fun b c => c ∈ succ b) start a := by
  refine ⟨reflTransGen_of_mem_search, fun h => ?_⟩
  have hclosed : expand succ (search succ rounds start) = search succ rounds start := by
    refine (succ_le_length_search_or_closed rounds start).resolve_left fun hlen => ?_
    have := hbound _ (nodup_search rounds start) fun b hb => reflTransGen_of_mem_search hb
    omega
  induction h with
  | refl => exact start_mem_search rounds start
  | tail _ hstep ih => exact expand_eq_self_iff.mp hclosed _ ih _ hstep

end Cslib.Reachability
