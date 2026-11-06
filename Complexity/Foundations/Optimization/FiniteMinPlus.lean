/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.List.Forall2
import Mathlib.Tactic

/-!
# Witness-producing finite min-plus optimization

The finite recurrence used in [XuGaoHu2027], Theorem 4.1 (PDF p. 9).
Each row lists the available choices for one group. `solve` returns an actual
choice from each row, minimizing the sum of ordered additive scores at an exact natural
cost. Unreachable costs return `none`, rather than an arbitrary default score.

`solve` is the recursive reference implementation; `table` shares its subproblems
in arrays and `memoFirstCrossing` scans the resulting table. These prove correctness
and recovery. This module does not certify the paper's trimmed-curve, doubling
implementation or its resource bound. In particular recursive calls are not shared by `solve`.
-/

public section

namespace Cslib.FiniteMinPlus

variable {α β : Type*} [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]

/-- An actual choice from every input row, in row order. -/
@[expose] def Admissible (rows : List (List α)) (plan : List α) : Prop :=
  List.Forall₂ (fun row a => a ∈ row) rows plan

/-- Total additive cost or score of a recovered plan. -/
@[expose] def total {β : Type*} [AddMonoid β] (f : α → β) (plan : List α) : β :=
  (plan.map f).sum

/-- Candidate extensions at one exact cost; subtraction is guarded. -/
@[expose] def extensions (cost : α → ℕ) (row : List α)
    (old : ℕ → Option (List α)) (k : ℕ) : List (List α) :=
  row.flatMap fun a =>
    if cost a ≤ k then ((old (k - cost a)).map (a :: ·)).toList else []

/-- Exact min-plus recurrence, retaining the minimizing witnesses. -/
@[expose] def solve (cost : α → ℕ) (score : α → β) :
    List (List α) → ℕ → Option (List α)
  | [], k => if k = 0 then some [] else none
  | row :: rows, k =>
    (extensions cost row (solve cost score rows) k).argmin (total score)

private theorem mem_extensions (cost : α → ℕ) (row : List α)
    (old : ℕ → Option (List α)) (k : ℕ) (p : List α) :
    p ∈ extensions cost row old k ↔
      ∃ a ∈ row, ∃ q, cost a ≤ k ∧ old (k - cost a) = some q ∧ p = a :: q := by
  simp only [extensions, List.mem_flatMap]
  constructor
  · rintro ⟨a, ha, hp⟩
    split_ifs at hp with h
    · cases ho : old (k - cost a) with
      | none => simp [ho] at hp
      | some q =>
        simp only [ho, Option.map_some, Option.toList_some, List.mem_singleton] at hp
        exact ⟨a, ha, q, h, ho, hp⟩
    · simp at hp
  · rintro ⟨a, ha, q, h, ho, rfl⟩
    exact ⟨a, ha, by simp [h, ho]⟩

/-- Soundness, existence and global optimality of the recovered finite plan. -/
theorem solve_spec (cost : α → ℕ) (score : α → β) (rows : List (List α)) (k : ℕ) :
    (∀ p, solve cost score rows k = some p →
      Admissible rows p ∧ total cost p = k ∧
        ∀ q, Admissible rows q → total cost q = k → total score p ≤ total score q) ∧
    (solve cost score rows k = none ↔
      ¬ ∃ q, Admissible rows q ∧ total cost q = k) := by
  induction rows generalizing k with
  | nil =>
    constructor
    · intro p hp
      simp only [solve] at hp
      split_ifs at hp with hk
      · cases hp
        subst k
        refine ⟨List.Forall₂.nil, rfl, ?_⟩
        intro q hq _
        cases q with
        | nil => exact le_rfl
        | cons => cases hq
    · simp only [solve]
      split_ifs with hk
      · subst k
        simp only [false_iff, not_not]
        exact ⟨[], List.Forall₂.nil, rfl⟩
      · constructor
        · intro _ ⟨q, hq, hcost⟩
          cases q with
          | nil => exact hk hcost.symm
          | cons => cases hq
        · intro _; rfl
  | cons row rows ih =>
    have sound : ∀ p ∈ extensions cost row (solve cost score rows) k,
        Admissible (row :: rows) p ∧ total cost p = k := by
      intro p hp
      obtain ⟨a, ha, q, hle, hq, rfl⟩ := (mem_extensions ..).mp hp
      obtain ⟨hqv, hqc, _⟩ := (ih (k - cost a)).1 q hq
      refine ⟨List.Forall₂.cons ha hqv, ?_⟩
      simp only [total, List.map_cons, List.sum_cons] at hqc ⊢
      omega
    have dominate : ∀ q, Admissible (row :: rows) q → total cost q = k →
        ∃ p ∈ extensions cost row (solve cost score rows) k,
          total score p ≤ total score q := by
      intro q hq hcost
      cases q with
      | nil => cases hq
      | cons a q =>
        obtain ⟨ha, hqv⟩ := List.forall₂_cons.mp hq
        have hle : cost a ≤ k := by
          change cost a + total cost q = k at hcost
          omega
        have hqc : total cost q = k - cost a := by
          change cost a + total cost q = k at hcost
          omega
        cases hp : solve cost score rows (k - cost a) with
        | none => exact False.elim ((ih _).2.mp hp ⟨q, hqv, hqc⟩)
        | some p =>
          obtain ⟨_, _, hmin⟩ := (ih _).1 p hp
          refine ⟨a :: p, (mem_extensions ..).mpr ⟨a, ha, p, hle, hp, rfl⟩, ?_⟩
          simpa only [total, List.map_cons, List.sum_cons] using
            add_le_add (le_refl (score a)) (hmin q hqv hqc)
    constructor
    · intro p hp
      have hmem := List.argmin_mem (show
        p ∈ (extensions cost row (solve cost score rows) k).argmin (total score) from hp)
      obtain ⟨hv, hc⟩ := sound p hmem
      refine ⟨hv, hc, ?_⟩
      intro q hq hqc
      obtain ⟨r, hr, hle⟩ := dominate q hq hqc
      exact (List.le_of_mem_argmin hr (show
        p ∈ (extensions cost row (solve cost score rows) k).argmin (total score) from hp)).trans hle
    · constructor
      · intro hp ⟨q, hq, hqc⟩
        obtain ⟨p, hp', _⟩ := dominate q hq hqc
        have hempty := List.argmin_eq_none.mp (show
          (extensions cost row (solve cost score rows) k).argmin (total score) = none from hp)
        rw [hempty] at hp'
        exact List.not_mem_nil hp'
      · intro hnone
        cases hp : solve cost score (row :: rows) k with
        | none => rfl
        | some p =>
          have hmem := List.argmin_mem (show
            p ∈ (extensions cost row (solve cost score rows) k).argmin (total score) from hp)
          exact False.elim (hnone ⟨p, sound p hmem⟩)

/-- A nonpositive returned score is equivalent to an actual nonpositive plan. -/
theorem crossing_iff (cost : α → ℕ) (score : α → β)
    (rows : List (List α)) (k : ℕ) :
    (∃ p, solve cost score rows k = some p ∧ total score p ≤ 0) ↔
      ∃ q, Admissible rows q ∧ total cost q = k ∧ total score q ≤ 0 := by
  constructor
  · rintro ⟨p, hp, hs⟩
    obtain ⟨hv, hc, _⟩ := (solve_spec cost score rows k).1 p hp
    exact ⟨p, hv, hc, hs⟩
  · rintro ⟨q, hq, hc, hs⟩
    cases hp : solve cost score rows k with
    | none => exact False.elim ((solve_spec cost score rows k).2.mp hp ⟨q, hq, hc⟩)
    | some p =>
      exact ⟨p, rfl, ((solve_spec cost score rows k).1 p hp).2.2 q hq hc |>.trans hs⟩

/-- All recovered nonpositive plans up to a finite search cap. -/
@[expose] def crossings (cost : α → ℕ) (score : α → β)
    (rows : List (List α)) (cap : ℕ) : List (List α) :=
  (List.range (cap + 1)).flatMap fun k =>
    ((solve cost score rows k).filter fun p => total score p ≤ 0).toList

/-- Compute the first nonpositive crossing, including its actual row choices. -/
@[expose] def firstCrossing (cost : α → ℕ) (score : α → β)
    (rows : List (List α)) (cap : ℕ) : Option (List α) :=
  (crossings cost score rows cap).argmin (total cost)

omit [IsOrderedAddMonoid β] in
private theorem mem_crossings (cost : α → ℕ) (score : α → β)
    (rows : List (List α)) (cap : ℕ) (p : List α) :
    p ∈ crossings cost score rows cap ↔
      ∃ k ≤ cap, solve cost score rows k = some p ∧ total score p ≤ 0 := by
  simp only [crossings, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨k, hk, hp⟩
    cases hs : solve cost score rows k with
    | none => simp [hs] at hp
    | some q =>
      simp only [hs, Option.filter_some] at hp
      split_ifs at hp with hq
      · simp only [Option.toList_some, List.mem_singleton] at hp
        subst p
        exact ⟨k, by omega, hs, of_decide_eq_true hq⟩
      · simp at hp
  · rintro ⟨k, hk, hs, hp⟩
    exact ⟨k, by omega, by simp [hs, hp]⟩

/-- The first crossing is an actual globally least-cost nonpositive plan.
The comparison includes plans beyond the search cap. -/
theorem firstCrossing_spec (cost : α → ℕ) (score : α → β)
    (rows : List (List α)) (cap : ℕ) (p : List α)
    (hp : firstCrossing cost score rows cap = some p) :
    Admissible rows p ∧ total cost p ≤ cap ∧ total score p ≤ 0 ∧
      ∀ q, Admissible rows q → total score q ≤ 0 → total cost p ≤ total cost q := by
  have hm := List.argmin_mem hp
  obtain ⟨k, hk, hs, hscore⟩ := (mem_crossings ..).mp hm
  obtain ⟨hv, hc, _⟩ := (solve_spec cost score rows k).1 p hs
  refine ⟨hv, hc ▸ hk, hscore, ?_⟩
  intro q hq hsq
  by_cases hcap : total cost q ≤ cap
  · obtain ⟨r, hr, hsr⟩ := (crossing_iff cost score rows (total cost q)).mpr
      ⟨q, hq, rfl, hsq⟩
    have hrc := ((solve_spec cost score rows _).1 r hr).2.1
    have hrm := (mem_crossings cost score rows cap r).mpr ⟨_, hcap, hr, hsr⟩
    exact hrc ▸ List.le_of_mem_argmin hrm hp
  · omega

/-- The recovered plan also minimizes score among plans at its exact cost. -/
theorem firstCrossing_score_minimal (cost : α → ℕ) (score : α → β)
    (rows : List (List α)) (cap : ℕ) (p : List α)
    (hp : firstCrossing cost score rows cap = some p) :
    ∀ q, Admissible rows q → total cost q = total cost p →
      total score p ≤ total score q := by
  obtain ⟨k, _, hs, _⟩ := (mem_crossings ..).mp (List.argmin_mem hp)
  obtain ⟨_, hc, hmin⟩ := (solve_spec cost score rows k).1 p hs
  intro q hq hqc
  exact hmin q hq (hqc.trans hc)

/-- A finite search returns `none` exactly when there is no crossing within its cap. -/
theorem firstCrossing_eq_none (cost : α → ℕ) (score : α → β)
    (rows : List (List α)) (cap : ℕ) :
    firstCrossing cost score rows cap = none ↔
      ¬ ∃ q, Admissible rows q ∧ total cost q ≤ cap ∧ total score q ≤ 0 := by
  constructor
  · intro h ⟨q, hq, hc, hs⟩
    obtain ⟨r, hr, hrs⟩ := (crossing_iff cost score rows (total cost q)).mpr
      ⟨q, hq, rfl, hs⟩
    have hm := (mem_crossings cost score rows cap r).mpr ⟨_, hc, hr, hrs⟩
    have he : crossings cost score rows cap = [] := List.argmin_eq_none.mp h
    rw [he] at hm
    exact List.not_mem_nil hm
  · intro h
    cases hp : firstCrossing cost score rows cap with
    | none => rfl
    | some p =>
      obtain ⟨hv, hc, hs, _⟩ := firstCrossing_spec cost score rows cap p hp
      exact False.elim (h ⟨p, hv, hc, hs⟩)

/-- A shared array of all recurrence values up to `cap`. Each preceding row is
computed once and looked up by array index when extending a choice. -/
@[expose] def table (cost : α → ℕ) (score : α → β) :
    List (List α) → (cap : ℕ) → Array (Option (List α))
  | [], cap => Array.ofFn fun k : Fin (cap + 1) =>
      if k.val = 0 then some [] else none
  | row :: rows, cap =>
    let old := table cost score rows cap
    Array.ofFn fun k : Fin (cap + 1) =>
      (extensions cost row (fun j => old[j]?.join) k.val).argmin (total score)

omit [IsOrderedAddMonoid β] in
/-- The shared array computes the exact witness-producing recurrence.
Truncation discards no predecessor of any queried cost within the cap. -/
theorem table_correct (cost : α → ℕ) (score : α → β)
    (rows : List (List α)) (cap k : ℕ) (hk : k ≤ cap) :
    (table cost score rows cap)[k]?.join = solve cost score rows k := by
  induction rows generalizing k with
  | nil => simp [table, show k < cap + 1 by omega, solve]
  | cons row rows ih =>
    simp only [table, Array.getElem?_ofFn, show k < cap + 1 by omega,
      dite_true, Option.join_some, solve]
    congr 1
    apply congrArg (List.flatMap · row)
    funext a
    dsimp only
    split_ifs with h
    · rw [ih (k - cost a) (by omega)]
    · rfl

/-- Scan a memoized table for the least-cost nonpositive witness. -/
@[expose] def memoFirstCrossing (cost : α → ℕ) (score : α → β)
    (rows : List (List α)) (cap : ℕ) : Option (List α) :=
  let values := table cost score rows cap
  ((List.range (cap + 1)).flatMap fun k =>
    ((values[k]?.join).filter fun p => total score p ≤ 0).toList).argmin (total cost)

omit [IsOrderedAddMonoid β] in
/-- Memoization preserves the recovered witness, including deterministic tie-breaking. -/
theorem memoFirstCrossing_eq (cost : α → ℕ) (score : α → β)
    (rows : List (List α)) (cap : ℕ) :
    memoFirstCrossing cost score rows cap = firstCrossing cost score rows cap := by
  unfold memoFirstCrossing firstCrossing crossings
  dsimp only
  congr 1
  apply List.flatMap_congr
  intro k hk
  rw [table_correct cost score rows cap k (by have := List.mem_range.mp hk; omega)]

end Cslib.FiniteMinPlus
