/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Optimization.FiniteMinPlus
public import Cslib.Algorithms.Lean.TimeM
import Mathlib.Tactic

/-!
# Cached min-plus convolution

Executable convolution with cached scalar scores and persistent witness links.
Unlike `FiniteMinPlus.table`, comparisons never traverse recovered plans.
The arithmetic RAM interpretation charges constant-size record access, natural
index arithmetic, array access, list cons, score addition and score comparison.
An addition/comparison of a score is one operation here; a client using a pair
of rational scores must multiply these charges by a constant. Rational bit time,
array ownership/copying and allocation by the Lean runtime are not asserted.

`cell_time` and `table_time` derive counts from the actual nested loops. Input
scores must already be cached; computing those scores is a separate obligation.

## Main definitions

* `table`: shared arrays with cached scalar scores and persistent witness links.
* `curve`: one minimizing actual alternative per exact cost.
* `scan`: first nonpositive reachable entry, in increasing-cost order.

## Main results

* `table_correct`: refinement of the existing witness recurrence, including ties.
* `curve_dominates`: no original choice is lost without a same-cost improvement.
* `table_time`, `curve_time`, `scan_time`: counts derived from the executable loops.
-/

public section

namespace Cslib.FiniteMinPlus.Cached

open Algorithms.Lean

variable {α β : Type*} [AddCommMonoid β] [LinearOrder β]

/-- Count a list with a charged increment/dispatch for each visited element. -/
@[expose] def lengthM {α : Type*} : List α → TimeM ℕ ℕ
  | [] => pure 0
  | _ :: xs => do
    let n ← lengthM xs
    TimeM.tick 1
    pure (n + 1)

/-- The measured traversal returns the list length and charges that traversal. -/
theorem lengthM_spec {α : Type*} (xs : List α) :
    (lengthM xs).ret = xs.length ∧ (lengthM xs).time = xs.length := by
  induction xs with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih => simp [lengthM, ih.1, ih.2]

/-- A precomputed group alternative, with constant-time access to its score and cost. -/
structure Item (α β : Type*) where
  /-- The actual choice, held by reference. -/
  value : α
  /-- Number of deletions in this group. -/
  cost : ℕ
  /-- Cached additive objective. -/
  score : β

/-- A persistent chain of choices and its cached total score. Consing shares its tail. -/
structure Entry (α β : Type*) where
  /-- Recovered choices, in input row order. -/
  plan : List α
  /-- Cached total score. -/
  score : β

/-- Compare two reachable cells, keeping the left one on a tie. -/
@[expose] def better (a b : Option (Entry α β)) : Option (Entry α β) :=
  match a, b with
  | none, b => b
  | a, none => a
  | some a, some b => if a.score ≤ b.score then some a else some b

/-- Extend one cached predecessor. The eight charged operations are the cost
comparison, index subtraction, array lookup, option inspection, score addition,
witness cons, record construction and loop dispatch. Unused operations are padded. -/
@[expose] def extend (a : Item α β) (old : Array (Option (Entry α β)))
    (k : ℕ) : TimeM ℕ (Option (Entry α β)) :=
  ⟨if a.cost ≤ k then
      (old[k - a.cost]?.join).map fun e => ⟨a.value :: e.plan, a.score + e.score⟩
    else none, 8⟩

/-- Scan actual alternatives. Four further operations cover option dispatch,
score comparison, selection and return/loop control. -/
@[expose] def cell (old : Array (Option (Entry α β))) (k : ℕ) :
    List (Item α β) → TimeM ℕ (Option (Entry α β))
  | [] => pure none
  | a :: row => do
    let x ← extend a old k
    let y ← cell old k row
    TimeM.tick 4
    pure (better x y)

/-- The scan cost follows from the executed list recursion, regardless of reachability. -/
theorem cell_time (old : Array (Option (Entry α β))) (k : ℕ)
    (row : List (Item α β)) : (cell old k row).time = 12 * row.length := by
  induction row with
  | nil => rfl
  | cons a row ih => simp [cell, extend, ih]; omega

/-- Tabulate cells by ascending index, with one charged push and one index increment.
The recursive result is used linearly; array updates need not copy shared arrays. -/
@[expose] def rowTable (old : Array (Option (Entry α β))) (row : List (Item α β)) :
    ℕ → TimeM ℕ (Array (Option (Entry α β)))
  | 0 => pure #[]
  | k + 1 => do
    let out ← rowTable old row k
    let e ← cell old k row
    TimeM.tick 2
    pure (out.push e)

/-- Exact executed work for one row, including materializing its array. -/
theorem rowTable_time (old : Array (Option (Entry α β))) (row : List (Item α β))
    (width : ℕ) : (rowTable old row width).time = (12 * row.length + 2) * width := by
  induction width with
  | zero => rfl
  | succ k ih => simp [rowTable, cell_time, ih]; ring

/-- Initialize unreachable cells, except the zero-cost empty plan. -/
@[expose] def initial : ℕ → TimeM ℕ (Array (Option (Entry α β)))
  | 0 => pure #[]
  | k + 1 => do
    let out ← initial k
    TimeM.tick 3
    pure (out.push (if k = 0 then some ⟨[], 0⟩ else none))

omit [LinearOrder β] in
/-- Initialization charges a comparison, push and loop/index operation per cell. -/
theorem initial_time (width : ℕ) :
    (initial (α := α) (β := β) width).time = 3 * width := by
  induction width with
  | zero => rfl
  | succ k ih => simp [initial, ih]; omega

/-- Shared scalar-score tables. Only the preceding array is read; all witness tails
are persistent links, rather than rescored plans. -/
@[expose] def table (width : ℕ) :
    List (List (Item α β)) → TimeM ℕ (Array (Option (Entry α β)))
  | [] => initial width
  | row :: rows => do
    let old ← table width rows
    rowTable old row width

/-- Exact operation count, derived from the table's executable recursion. -/
theorem table_time (width : ℕ) (rows : List (List (Item α β))) :
    (table width rows).time =
      (3 + (rows.map fun row => 12 * row.length + 2).sum) * width := by
  induction rows with
  | nil => simp [table, initial_time]
  | cons row rows ih => simp [table, rowTable_time, ih]; ring

/-- Sum of group-curve lengths controls the convolution, not the number of subsets. -/
theorem table_time_le (width n : ℕ) (rows : List (List (Item α β)))
    (hlength : (rows.map List.length).sum ≤ 2 * n) (hgroups : rows.length ≤ n) :
    (table width rows).time ≤ (26 * n + 3) * width := by
  rw [table_time]
  have hs : (rows.map fun row => 12 * row.length + 2).sum =
      12 * (rows.map List.length).sum + 2 * rows.length := by
    clear hlength hgroups
    induction rows with
    | nil => rfl
    | cons row rows ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  rw [hs]
  exact Nat.mul_le_mul_right width (by omega)

/-- Cached entries carry exactly the sum of the scores of their witness links. -/
@[expose] def Coherent (score : α → β) (e : Option (Entry α β)) : Prop :=
  ∀ x, e = some x → x.score = total score x.plan

private theorem better_coherent (score : α → β) (a b : Option (Entry α β))
    (ha : Coherent score a) (hb : Coherent score b) :
    Coherent score (better a b) := by
  cases a <;> cases b <;> simp only [better]
  · exact hb
  · exact hb
  · exact ha
  · split_ifs <;> assumption

private theorem better_argmin (score : α → β) (a b : Option (Entry α β))
    (ha : Coherent score a) (hb : Coherent score b) (ps : List (List α))
    (hp : b.map Entry.plan = ps.argmin (total score)) :
    (better a b).map Entry.plan =
      ((a.map Entry.plan).toList ++ ps).argmin (total score) := by
  cases a with
  | none => simpa [better] using hp
  | some a =>
    have has := ha a rfl
    cases b with
    | none => simp [better, List.argmin_cons, ← hp]
    | some b =>
      have hbs := hb b rfl
      simp only [Option.map_some, Option.toList_some, List.singleton_append,
        List.argmin_cons, ← hp, better]
      rw [has, hbs]
      by_cases h : total score a.plan ≤ total score b.plan
      · simp [h, not_lt.mpr h]
      · simp [h, lt_of_not_ge h]

/-- A cached cell refines the reviewed witness recurrence, including its tie rule.
Scores and costs are read from the input records, not recomputed from plans. -/
theorem cell_correct (cost : α → ℕ) (score : α → β)
    (old : Array (Option (Entry α β))) (k : ℕ) (row : List (Item α β))
    (hrow : ∀ a ∈ row, a.cost = cost a.value ∧ a.score = score a.value)
    (hold : ∀ j : ℕ, Coherent score (old[j]?.join)) :
    Coherent score (cell old k row).ret ∧
      (cell old k row).ret.map Entry.plan =
        (extensions cost (row.map Item.value)
          (fun j => (old[j]?.join).map Entry.plan) k).argmin (total score) := by
  induction row with
  | nil => simp [cell, Coherent, extensions, List.argmin]
  | cons a row ih =>
    obtain ⟨hac, has⟩ := hrow a (by simp)
    obtain ⟨hc, he⟩ := ih (fun b hb => hrow b (by simp [hb]))
    have hx : Coherent score (extend a old k).ret := by
      intro x hx
      simp only [extend] at hx
      split_ifs at hx with h
      · cases ho : old[k - a.cost]?.join with
        | none => simp [ho] at hx
        | some e =>
          simp only [ho, Option.map_some, Option.some.injEq] at hx
          subst x
          simp only [total, List.map_cons, List.sum_cons]
          rw [has, hold _ e ho]
          rfl
    refine ⟨better_coherent score _ _ hx hc, ?_⟩
    change (better _ _).map Entry.plan = _
    rw [better_argmin score _ _ hx hc _ he]
    congr 1
    simp only [extensions, List.map_cons, List.flatMap_cons]
    congr 1
    simp only [extend, hac]
    split_ifs <;> simp [Option.map_map, Function.comp_def]

/-- Every materialized row has its requested width. -/
theorem rowTable_size (old : Array (Option (Entry α β))) (row : List (Item α β))
    (width : ℕ) : (rowTable old row width).ret.size = width := by
  induction width with
  | zero => rfl
  | succ k ih => simp [rowTable, ih]

/-- Reading a materialized cell agrees with executing its scan once. -/
theorem rowTable_get (old : Array (Option (Entry α β))) (row : List (Item α β))
    (width k : ℕ) (hk : k < width) :
    ((rowTable old row width).ret[k]?).join = (cell old k row).ret := by
  induction width with
  | zero => omega
  | succ width ih =>
    simp only [rowTable, TimeM.ret_bind, TimeM.ret_pure, Array.getElem?_push, rowTable_size]
    by_cases h : k = width
    · simp [h]
    · simp only [h, ite_false]
      exact ih (by omega)

omit [LinearOrder β] in
private theorem initial_get (width k : ℕ) :
    (initial (α := α) (β := β) width).ret[k]?.join =
      if k < width ∧ k = 0 then some ⟨[], 0⟩ else none := by
  have hsize : ∀ w, (initial (α := α) (β := β) w).ret.size = w := by
    intro w
    induction w with
    | zero => rfl
    | succ w ih => simp [initial, ih]
  induction width with
  | zero => simp [initial]
  | succ width ih =>
    simp only [initial, TimeM.ret_bind, TimeM.ret_pure, Array.getElem?_push, hsize]
    by_cases h : k = width
    · subst k
      simp only [ite_true, Option.join_some]
      split_ifs <;> simp_all
    · simp only [h, ite_false, ih]
      by_cases hz : k = 0 <;> simp_all; omega

/-- Correctness of every cached table entry against the existing finite optimizer.
This covers unreachable costs and proves the stored score without rescoring it. -/
theorem table_correct (cost : α → ℕ) (score : α → β)
    (rows : List (List (Item α β))) (width : ℕ)
    (hrows : ∀ row ∈ rows, ∀ a ∈ row, a.cost = cost a.value ∧ a.score = score a.value) :
    ∀ k, Coherent score ((table width rows).ret[k]?.join) ∧
      ((table width rows).ret[k]?.join).map Entry.plan =
        if k < width then solve cost score (rows.map (List.map Item.value)) k else none := by
  induction rows with
  | nil =>
    intro k
    simp only [table, initial_get, List.map_nil, solve]
    split_ifs <;> simp_all [Coherent, total]
  | cons row rows ih =>
    have ht := ih (fun r hr => hrows r (by simp [hr]))
    intro k
    simp only [table, TimeM.ret_bind]
    by_cases hk : k < width
    · rw [rowTable_get _ _ _ _ hk]
      obtain ⟨hc, he⟩ := cell_correct cost score (table width rows).ret k row
        (hrows row (by simp)) (fun j => (ht j).1)
      refine ⟨hc, ?_⟩
      rw [he]
      simp only [hk, ite_true, List.map_cons, solve]
      congr 1
      unfold extensions
      apply List.flatMap_congr
      intro a ha
      dsimp only
      split_ifs with h
      · rw [(ht (k - cost a)).2]
        simp only [show k - cost a < width by omega, ite_true]
      · rfl
    · have ho : (rowTable (table width rows).ret row width).ret[k]? = none :=
        Array.getElem?_eq_none (by rw [rowTable_size]; omega)
      simp only [ho, Option.join_none, Coherent, Option.map_none, hk, ite_false]
      simp

omit [AddCommMonoid β] in
section

/-- Select one cached alternative of an exact cost. Four operations per input
cover the cost test, score comparison, option selection and loop dispatch. -/
@[expose] def minimumAt (k : ℕ) : List (Item α β) → TimeM ℕ (Option (Item α β))
  | [] => pure none
  | a :: row => do
    let b ← minimumAt k row
    TimeM.tick 4
    pure (if a.cost = k then
      match b with
      | none => some a
      | some b => if a.score ≤ b.score then some a else some b
      else b)

/-- The compression scan is linear in the cached alternatives. -/
theorem minimumAt_time (k : ℕ) (row : List (Item α β)) :
    (minimumAt k row).time = 4 * row.length := by
  induction row with
  | nil => rfl
  | cons a row ih => simp [minimumAt, ih]; omega

/-- Compression is exactly minimization over the alternatives at the requested cost. -/
theorem minimumAt_correct (k : ℕ) (row : List (Item α β)) :
    (minimumAt k row).ret = (row.filter (fun a => a.cost = k)).argmin Item.score := by
  induction row with
  | nil => rfl
  | cons a row ih =>
    simp only [minimumAt, TimeM.ret_bind, TimeM.ret_pure, ih, List.filter_cons]
    by_cases h : a.cost = k
    · simp only [h, decide_true, ite_true, List.argmin_cons]
      cases hb : (row.filter (fun a => a.cost = k)).argmin Item.score with
      | none => rfl
      | some b =>
        by_cases he : a.score ≤ b.score
        · simp [he, not_lt.mpr he]
        · simp [he, lt_of_not_ge he]
    · simp [h]

/-- Materialize one optimum per deletion count, discarding unreachable counts. -/
@[expose] def curve (row : List (Item α β)) : ℕ → TimeM ℕ (List (Item α β))
  | 0 => pure []
  | k + 1 => do
    let out ← curve row k
    let e ← minimumAt k row
    TimeM.tick 2
    pure (e.toList ++ out)

/-- Exact preprocessing work, including one scan for every deletion count. -/
theorem curve_time (row : List (Item α β)) (width : ℕ) :
    (curve row width).time = (4 * row.length + 2) * width := by
  induction width with
  | zero => rfl
  | succ k ih => simp [curve, minimumAt_time, ih]; ring

/-- Compression has at most one alternative per requested count. -/
theorem curve_length (row : List (Item α β)) (width : ℕ) :
    (curve row width).ret.length ≤ width := by
  induction width with
  | zero => rfl
  | succ k ih =>
    simp only [curve, TimeM.ret_bind, TimeM.ret_pure, List.length_append]
    cases (minimumAt k row).ret <;> simp_all <;> omega

/-- Compression introduces no invented choices. -/
theorem mem_curve (row : List (Item α β)) (width : ℕ) (a : Item α β)
    (ha : a ∈ (curve row width).ret) : a ∈ row ∧ a.cost < width := by
  induction width with
  | zero => cases ha
  | succ k ih =>
    simp only [curve, TimeM.ret_bind, TimeM.ret_pure, List.mem_append] at ha
    rcases ha with ha | ha
    · have he := List.argmin_mem (show a ∈
        (row.filter (fun a => a.cost = k)).argmin Item.score from
          by simpa only [← minimumAt_correct, Option.mem_toList, Option.mem_def] using ha)
      obtain ⟨hm, hc⟩ := List.mem_filter.mp he
      exact ⟨hm, by have := of_decide_eq_true hc; omega⟩
    · obtain ⟨hm, hc⟩ := ih ha
      exact ⟨hm, by omega⟩

/-- Every original alternative is dominated by a retained alternative of the same cost. -/
theorem curve_dominates (row : List (Item α β)) (width : ℕ) (a : Item α β)
    (ha : a ∈ row) (hc : a.cost < width) :
    ∃ b ∈ (curve row width).ret, b.cost = a.cost ∧ b.score ≤ a.score := by
  induction width with
  | zero => omega
  | succ k ih =>
    by_cases h : a.cost < k
    · obtain ⟨b, hb, he, hs⟩ := ih h
      refine ⟨b, ?_, he, hs⟩
      simp only [curve, TimeM.ret_bind, TimeM.ret_pure, List.mem_append]
      exact Or.inr hb
    · have he : a.cost = k := by omega
      have hm : a ∈ row.filter (fun a => a.cost = k) := by simp [ha, he]
      cases hb : (minimumAt k row).ret with
      | none =>
        have hz := List.argmin_eq_none.mp ((minimumAt_correct k row).symm.trans hb)
        rw [hz] at hm
        cases hm
      | some b =>
        have hb' : b ∈ (row.filter (fun a => a.cost = k)).argmin Item.score :=
          (minimumAt_correct k row).symm.trans hb
        have hmem := List.mem_filter.mp (List.argmin_mem hb')
        refine ⟨b, ?_, ?_, List.le_of_mem_argmin hm hb'⟩
        · simp [curve, hb]
        · have := of_decide_eq_true hmem.2
          omega

end

/-- An index and a reachable cell, found without rescoring its witness. -/
structure Hit (α β : Type*) where
  /-- Exact total cost, equal to the table index. -/
  index : ℕ
  /-- Cached entry at that index. -/
  entry : Entry α β

/-- Whether a table contains a nonpositive reachable score at an index. -/
@[expose] def Crosses (a : Array (Option (Entry α β))) (k : ℕ) : Prop :=
  ∃ e, a[k]?.join = some e ∧ e.score ≤ 0

/-- Scan increasing costs. Each iteration charges a read, option inspection,
score comparison and loop/index dispatch; early success stops execution. -/
@[expose] def scan (a : Array (Option (Entry α β))) (start : ℕ) :
    ℕ → TimeM ℕ (Option (Hit α β))
  | 0 => pure none
  | fuel + 1 => do
    TimeM.tick 4
    match a[start]?.join with
    | none => scan a (start + 1) fuel
    | some e =>
      if e.score ≤ 0 then pure (some ⟨start, e⟩)
      else scan a (start + 1) fuel

/-- Scanning charges only the inspected cells. -/
theorem scan_time (a : Array (Option (Entry α β))) (start fuel : ℕ) :
    (scan a start fuel).time ≤ 4 * fuel := by
  induction fuel generalizing start with
  | zero => exact le_rfl
  | succ fuel ih =>
    simp only [scan, TimeM.time_bind, TimeM.time_tick]
    cases a[start]?.join with
    | none => dsimp only; have := ih (start + 1); omega
    | some e =>
      dsimp only
      by_cases h : e.score ≤ 0
      · simp only [h, ite_true, TimeM.time_pure]; omega
      · simp only [h, ite_false]
        have := ih (start + 1)
        omega

/-- Failure means that every inspected cost lacks a nonpositive reachable entry. -/
theorem scan_none (a : Array (Option (Entry α β))) (start fuel : ℕ) :
    (scan a start fuel).ret = none ↔
      ∀ k, start ≤ k → k < start + fuel → ¬ Crosses a k := by
  induction fuel generalizing start with
  | zero => simp [scan]; omega
  | succ fuel ih =>
    simp only [scan, TimeM.ret_bind]
    have hr : (∀ k, start ≤ k → k < start + (fuel + 1) → ¬ Crosses a k) ↔
        ¬ Crosses a start ∧
          ∀ k, start + 1 ≤ k → k < start + 1 + fuel → ¬ Crosses a k := by
      constructor
      · intro h
        exact ⟨h start le_rfl (by omega), fun k hk hl => h k (by omega) (by omega)⟩
      · rintro ⟨h, ht⟩ k hk hl
        by_cases he : k = start
        · simpa only [he] using h
        · exact ht k (by omega) (by omega)
    rw [hr]
    cases he : a[start]?.join with
    | none => simp [ih, Crosses, he]
    | some e =>
      by_cases hs : e.score ≤ 0
      · simp [hs, Crosses, he]
      · simp [hs, Crosses, he, ih]

/-- A successful scan gives the first crossing, its cached score and its actual witness. -/
theorem scan_some (a : Array (Option (Entry α β))) (start fuel : ℕ) (h : Hit α β)
    (hh : (scan a start fuel).ret = some h) :
    start ≤ h.index ∧ h.index < start + fuel ∧
      a[h.index]?.join = some h.entry ∧ h.entry.score ≤ 0 ∧
      ∀ k, start ≤ k → k < h.index → ¬ Crosses a k := by
  induction fuel generalizing start with
  | zero => cases hh
  | succ fuel ih =>
    simp only [scan, TimeM.ret_bind] at hh
    have next (hn : ¬ Crosses a start)
        (hh : (scan a (start + 1) fuel).ret = some h) :
        start ≤ h.index ∧ h.index < start + (fuel + 1) ∧
          a[h.index]?.join = some h.entry ∧ h.entry.score ≤ 0 ∧
          ∀ k, start ≤ k → k < h.index → ¬ Crosses a k := by
      obtain ⟨hl, hu, he, hs, hf⟩ := ih (start + 1) hh
      refine ⟨by omega, by omega, he, hs, ?_⟩
      intro k hk hlt
      by_cases heq : k = start
      · simpa only [heq] using hn
      · exact hf k (by omega) hlt
    cases he : a[start]?.join with
    | none =>
      rw [he] at hh
      exact next (by simp [Crosses, he]) hh
    | some e =>
      rw [he] at hh
      dsimp only at hh
      split_ifs at hh with hs
      · cases hh
        dsimp only
        exact ⟨le_rfl, by omega, he, hs, by intro k hk hl; omega⟩
      · exact next (by simpa [Crosses, he] using hs) hh

end Cslib.FiniteMinPlus.Cached
