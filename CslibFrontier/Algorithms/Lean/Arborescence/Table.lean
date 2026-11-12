/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Arborescence.ChuLiuEdmonds
public import CslibFrontier.Algorithms.Lean.TimeM.Loops
import CslibFrontier.Foundations.Data.List.ArgMin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Ring

/-!
# Materialized-table Chu–Liu/Edmonds in `TimeM` (`O(n³)`)

Whereas `Cslib.Algorithms.Lean.Arborescence.edmonds` passes contracted adjacency predicates and cost
functions across recursive calls as unmemoised closures, this module materializes per-level `n × n`
`Vector` tables (`AdjTable`, `CostTable`) indexed through `FinEnum.equiv` and runs the contraction
algorithm in `Cslib.Algorithms.Lean.TimeM ℕ` (`edmondsTableM`).

Because each level stores its contracted graph, costs, cycle membership mask, other-cycle-cost sum,
and best-entry / best-exit tables in flat `Fin n`-indexed `Vector` arrays before recursing, no level
re-evaluates earlier levels. On an `n`-vertex digraph, each contraction level performs at most
`13 * n ^ 2` ticks, and contraction shrinks the set of live vertices, giving an explicit charged
bound of `13 * n ^ 3 + 2 * n ^ 2 ≤ 15 * n ^ 3` steps including table initialization
(`time_edmondsTableM_le`). Transfer lemmas identify the returned
parent map with `ChuLiuEdmonds.edmonds` (`edmondsTableM_ret_eq_edmonds`), transferring all
correctness and optimality theorems (`edmondsTable_spec`, `edmondsTable_optimal`).

## Cost model

All `TimeM ℕ` charges model unit-cost RAM / array execution on `n × n` tables with `O(1)`
indexing and `O(1)` arithmetic/comparison in `β`:

* initialization (`initAdjTableM`, `initCostTableM`): `2 * n ^ 2` ticks (`1` per table entry);
* `argMinFinM`: `n` ticks (one comparison/filter step per element of `Fin n`);
* `selectParentsM`: `n ^ 2 + 2 * n` ticks (tabulate candidate minimizers per vertex, check
  feasibility, unwrap parent array);
* `findCycleM`: at most `n ^ 2 + n` ticks (scan candidate non-root vertices and trace up to `n`
  parent pointers);
* `cycleMaskM` and `otherCycleCostM`: at most `n ^ 2 + 2 * n` ticks (mark the cycle in a Boolean
  mask and tabulate `∑ y ∈ C \ {x}, c y (f y)` for each `x ∈ C` without subtraction);
* `bestEntryTableM` and `bestExitTableM`: `2 * n ^ 2` ticks;
* `contractAdjTableM` and `contractCostTableM`: `2 * n ^ 2` ticks (one `O(1)` lookup per cell
  from the precomputed level tables);
* `expandParentTableM`: `n` ticks.

The non-recursive work at any contraction level is at most `7 * n ^ 2 + 6 * n ≤ 13 * n ^ 2` ticks
(and at most `5 * n ^ 2` at the terminal non-contracting level), so `edmondsTableAuxM` runs in at
most `13 * n ^ 3` ticks; including `2 * n ^ 2` table initialization, `edmondsTableM` and
`edmondsOutTableM` run in at most `13 * n ^ 3 + 2 * n ^ 2 ≤ 15 * n ^ 3` (`O(n³)`) ticks in
total. Sparse `O(n m)` and `O(m log n)` / `O(m + n log n)` implementations remain tracked
separately in #3526.

## Main definitions

* `Cslib.Algorithms.Lean.Arborescence.AdjTable`, `CostTable`, `ParentTable`: materialized `Vector`
  tables on `Fin n`.
* `Cslib.Algorithms.Lean.Arborescence.edmondsTableAuxM`: fuel-indexed `TimeM ℕ` contraction solver
  on `Fin n`.
* `Cslib.Algorithms.Lean.Arborescence.edmondsTableM`,
  `Cslib.Algorithms.Lean.Arborescence.edmondsOutTableM`: entry points for arbitrary `[FinEnum V]`,
  transported via `FinEnum.equiv`.

## Main results

* `Cslib.Algorithms.Lean.Arborescence.edmondsTableM_ret_eq_edmonds`,
  `Cslib.Algorithms.Lean.Arborescence.edmondsOutTableM_ret_eq_edmondsOut`: the materialized table
  algorithm returns the exact same parent map as `edmonds` / `edmondsOut`.
* `Cslib.Algorithms.Lean.Arborescence.edmondsTable_spec`,
  `Cslib.Algorithms.Lean.Arborescence.edmondsTable_optimal`,
  `Cslib.Algorithms.Lean.Arborescence.edmondsOutTable_spec`: transferred correctness and
  optimality.
* `Cslib.Algorithms.Lean.Arborescence.time_edmondsTableAuxM_le` (`≤ 13 * n ^ 3`),
  `Cslib.Algorithms.Lean.Arborescence.time_edmondsTableM_le`,
  `Cslib.Algorithms.Lean.Arborescence.time_edmondsOutTableM_le` (`≤ 15 * n ^ 3`): explicit
  `O(n³)` charged step bounds.

## References

* [J. Edmonds, *Optimum Branchings*][Edmonds1967Branchings], Section 4
-/

public section

namespace Cslib.Algorithms.Lean.Arborescence

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.TimeM

/-! ### Materialized tables and helpers -/

/-- An `n × n` materialized adjacency matrix over `Fin n`. -/
abbrev AdjTable (n : ℕ) : Type := Vector (Vector Bool n) n

/-- An `n × n` materialized arc-cost table over `Fin n`. -/
abbrev CostTable (β : Type*) (n : ℕ) : Type _ := Vector (Vector β n) n

/-- A materialized parent vector over `Fin n`. -/
abbrev ParentTable (n : ℕ) : Type := Vector (Fin n) n

/-- Materialize the `n × n` Boolean adjacency matrix of a relation on `Fin n` (`n ^ 2` ticks). -/
@[expose] def initAdjTableM (n : ℕ) (adj : Fin n → Fin n → Bool) : TimeM ℕ (AdjTable n) :=
  Vector.ofFnM fun u : Fin n => Vector.ofFnM fun w : Fin n => do ✓ pure (adj u w)

/-- Materialize the `n × n` cost matrix on `Fin n` (`n ^ 2` ticks). -/
@[expose] def initCostTableM {β : Type*} (n : ℕ) (cost : Fin n → Fin n → β) :
    TimeM ℕ (CostTable β n) :=
  Vector.ofFnM fun u : Fin n => Vector.ofFnM fun w : Fin n => do ✓ pure (cost u w)

private theorem time_initAdjTableM (n : ℕ) (adj : Fin n → Fin n → Bool) :
    (initAdjTableM n adj).time = n ^ 2 := by
  unfold initAdjTableM
  simp [time_vectorOfFnM, sq]

private theorem ret_initAdjTableM (n : ℕ) (adj : Fin n → Fin n → Bool) (u w : Fin n) :
    (initAdjTableM n adj).ret[u.1][w.1] = adj u w := by
  unfold initAdjTableM
  simp [ret_vectorOfFnM]

private theorem time_initCostTableM {β : Type*} (n : ℕ) (cost : Fin n → Fin n → β) :
    (initCostTableM n cost).time = n ^ 2 := by
  unfold initCostTableM
  simp [time_vectorOfFnM, sq]

private theorem ret_initCostTableM {β : Type*} (n : ℕ) (cost : Fin n → Fin n → β) (u w : Fin n) :
    (initCostTableM n cost).ret[u.1][w.1] = cost u w := by
  unfold initCostTableM
  simp [ret_vectorOfFnM]

/-- Scan `List.finRange n` for the first minimizer of `val` satisfying `pred`, charging one tick
per scanned index (`n` ticks total). -/
@[expose] def argMinFinM {β : Type*} [LinearOrder β] (n : ℕ) (pred : Fin n → Bool)
    (val : Fin n → β) : TimeM ℕ (Option (Fin n)) :=
  (List.finRange n).foldlM
    (fun acc i => do ✓ pure (if pred i then List.argAux (fun x y => val x < val y) acc i else acc))
    none

private theorem time_argMinFinM {β : Type*} [LinearOrder β] (n : ℕ) (pred : Fin n → Bool)
    (val : Fin n → β) : (argMinFinM n pred val).time = n := by
  unfold argMinFinM
  rw [time_foldlM_of_time_eq _ _ _ (c := 1) (fun _ _ => by simp), List.length_finRange, mul_one]

private theorem foldl_argAux_skip {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (pred : α → Bool) (l : List α) (acc : Option α) :
    l.foldl (fun a i => if pred i then List.argAux r a i else a) acc =
      (l.filter pred).foldl (List.argAux r) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons i l ih =>
    cases h : pred i
    · rw [List.filter_cons_of_neg (by simp [h])]
      simp only [List.foldl_cons, h, Bool.false_eq_true, ↓reduceIte]
      exact ih acc
    · rw [List.filter_cons_of_pos (by simp [h])]
      simp only [List.foldl_cons, h, ↓reduceIte]
      exact ih (List.argAux r acc i)

private theorem ret_argMinFinM {β : Type*} [LinearOrder β] (n : ℕ) (pred : Fin n → Bool)
    (val : Fin n → β) :
    (argMinFinM n pred val).ret = ((List.finRange n).filter pred).argmin val := by
  unfold argMinFinM
  rw [ret_foldlM]
  simp only [ret_bind, ret_pure]
  exact foldl_argAux_skip (fun x y => val x < val y) pred (List.finRange n) none

/-! ### Per-level subroutines -/

section Level

variable {β : Type*} [LinearOrder β] {n : ℕ}

/-- Result of selecting optimal parents. -/
structure SelectParentsResult (n : ℕ) where
  /-- True if every non-root node has at least one incoming edge, so a valid parent was found. -/
  feasible : Bool
  /-- The selected parents. -/
  parents : ParentTable n

/-- Select the cheapest outgoing candidate parent for every non-root vertex (`r` maps to `some r`),
check feasibility, and materialize the parent vector `f`. -/
@[expose] def selectParentsM (a : AdjTable n) (c : CostTable β n) (r : Fin n) :
    TimeM ℕ (SelectParentsResult n) := do
  let opts ← Vector.ofFnM fun v : Fin n =>
    if v = r then (pure (some r) : TimeM ℕ (Option (Fin n)))
    else argMinFinM n (fun w => a[v.1][w.1] && w != v) (fun w => c[v.1][w.1])
  let feas ← (List.finRange n).foldlM
    (fun acc v => do ✓ pure (acc && opts[v.1].isSome)) true
  let tbl ← Vector.ofFnM fun v : Fin n => do ✓ pure (opts[v.1].getD v)
  pure { feasible := feas, parents := tbl }

private theorem ret_selectParentsM (a : AdjTable n) (c : CostTable β n) (r : Fin n) :
    let optFn : Fin n → Option (Fin n) := fun v =>
      if v = r then some r
      else ((List.finRange n).filter fun w => a[v.1][w.1] && w != v).argmin (fun w => c[v.1][w.1])
    (selectParentsM a c r).ret =
      { feasible := (List.finRange n).all (fun v => (optFn v).isSome)
      , parents := Vector.ofFn fun v => (optFn v).getD v } := by
  intro optFn
  have hopts : (Vector.ofFnM fun v : Fin n =>
      if v = r then (pure (some r) : TimeM ℕ (Option (Fin n)))
      else argMinFinM n (fun w => a[v.1][w.1] && w != v) (fun w => c[v.1][w.1])).ret =
      Vector.ofFn optFn := by
    rw [ret_vectorOfFnM]
    ext i hi
    simp only [Vector.getElem_ofFn, optFn]
    split_ifs <;> simp [ret_argMinFinM]
  unfold selectParentsM
  simp only [ret_bind, ret_pure, hopts, ret_foldlM, ret_vectorOfFnM]
  congr 1
  · have hvec : ∀ v : Fin n, (Vector.ofFn optFn)[v.1] = optFn v := fun v => by simp
    have hfold : ∀ (l : List (Fin n)) (b : Bool),
        l.foldl (fun acc v => acc && (Vector.ofFn optFn)[v.1].isSome) b =
          (b && l.all fun v => (optFn v).isSome) := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons x l ih =>
        intro b
        simp only [List.foldl_cons, List.all_cons]
        rw [hvec x, ih, Bool.and_assoc]
    rw [hfold, Bool.true_and]
  · ext i hi
    simp [Vector.getElem_ofFn]

private theorem time_selectParentsM (a : AdjTable n) (c : CostTable β n) (r : Fin n) :
    (selectParentsM a c r).time ≤ n ^ 2 + 2 * n := by
  unfold selectParentsM
  simp only [time_bind, time_pure, add_zero]
  rw [Nat.two_mul]
  refine Nat.add_le_add ?_ (Nat.add_le_add (le_of_eq ?_) (le_of_eq ?_))
  · rw [time_vectorOfFnM]
    calc ∑ v : Fin n, (if v = r then (pure (some r) : TimeM ℕ (Option (Fin n)))
            else argMinFinM n (fun w => a[v.1][w.1] && w != v) (fun w => c[v.1][w.1])).time
        ≤ ∑ _v : Fin n, n := Finset.sum_le_sum fun v _ => by
          by_cases hv : v = r
          · simp [hv]
          · simp [hv, time_argMinFinM]
      _ = n ^ 2 := by simp [sq]
  · rw [time_foldlM_of_time_eq _ _ _ (c := 1) (fun _ _ => by simp), List.length_finRange, mul_one]
  · rw [time_vectorOfFnM]
    simp

/-- Fold state for cycle search. -/
structure CycleSearchState (n : ℕ) where
  /-- Current node in the traversal. -/
  current : Fin n
  /-- True if the traversal has hit the starting node again. -/
  hit : Bool

/-- Test whether iterating `f` starting from `x` returns to `x` within `n` steps (`n` ticks). -/
@[expose] def hasCycleFromM (x : Fin n) (f : ParentTable n) : TimeM ℕ Bool := do
  let st ← (List.range n).foldlM
    (fun (st : CycleSearchState n) _ => do
      ✓
      let cur := st.current; let hit := st.hit
      let nxt := f[cur.1]
      pure { current := nxt, hit := hit || (nxt == x) : CycleSearchState n })
    ({ current := x, hit := false } : CycleSearchState n)
  pure st.hit

private theorem time_hasCycleFromM (x : Fin n) (f : ParentTable n) :
    (hasCycleFromM x f).time = n := by
  unfold hasCycleFromM
  simp only [time_bind, time_pure, add_zero]
  rw [time_foldlM_of_time_eq _ _ _ (c := 1) (fun _ _ => by simp), List.length_range, mul_one]

private theorem ret_hasCycleFromM (x : Fin n) (f : ParentTable n) :
    (hasCycleFromM x f).ret =
      (List.range n).any fun k => (fun i : Fin n => f[i.1])^[k + 1] x == x := by
  unfold hasCycleFromM
  simp only [ret_bind, ret_pure, ret_foldlM]
  have hinv : ∀ m : ℕ,
      (List.range m).foldl
        (fun (st : CycleSearchState n) _ =>
          let cur := st.current; let hit := st.hit
          { current := f[cur.1], hit := hit || (f[cur.1] == x) : CycleSearchState n })
            ({ current := x, hit := false } : CycleSearchState n) =
      { current := ((fun i : Fin n => f[i.1])^[m] x),
        hit := (List.range m).any fun k => (fun i : Fin n => f[i.1])^[k + 1] x == x } := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false,
        Function.iterate_succ_apply']
  exact congrArg CycleSearchState.hit (hinv n)

/-- Find the first vertex `x ≠ r` lying on a cycle of `f`, if any (`≤ n ^ 2 + n` ticks). -/
@[expose] def findCycleM (r : Fin n) (f : ParentTable n) : TimeM ℕ (Option (Fin n)) :=
  (List.finRange n).foldlM
    (fun acc x => do
      ✓
      match acc with
      | some x0 => pure (some x0)
      | none =>
        if x == r then pure none
        else do
          let hit ← hasCycleFromM x f
          pure (if hit then some x else none))
    none

private theorem time_findCycleM (r : Fin n) (f : ParentTable n) :
    (findCycleM r f).time ≤ n ^ 2 + n := by
  unfold findCycleM
  have hstep : ∀ (l : List (Fin n)) (acc : Option (Fin n)),
      (l.foldlM
        (fun acc x => do
          ✓
          match acc with
          | some x0 => pure (some x0)
          | none =>
            if x == r then pure none
            else do
              let hit ← hasCycleFromM x f
              pure (if hit then some x else none))
        acc).time ≤ l.length * (n + 1) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons x l ih =>
      intro acc
      rw [List.foldlM_cons, time_bind]
      let inner : TimeM ℕ (Option (Fin n)) := do
        ✓
        match acc with
        | some x0 => pure (some x0)
        | none =>
          if x == r then pure none
          else do
            let hit ← hasCycleFromM x f
            pure (if hit then some x else none)
      have hhd : inner.time ≤ n + 1 := by
        dsimp only [inner]
        cases acc with
        | some x0 => simp
        | none =>
          by_cases hxr : (x == r) = true
          · simp [hxr]
          · simp only [hxr, Bool.false_eq_true, ↓reduceIte, time_bind, time_tick,
              time_hasCycleFromM, time_pure, add_zero]
            omega
      have htl := ih inner.ret
      have hle : inner.time + _ ≤ _ := Nat.add_le_add hhd htl
      simp only [List.length_cons, Nat.succ_mul, Nat.add_comm (l.length * (n + 1))] at hle ⊢
      exact hle
  have h := hstep (List.finRange n) none
  rw [List.length_finRange] at h
  exact h.trans_eq (by ring)

private def findStep {α : Type*} (p : α → Bool) (a : Option α) (x : α) : Option α :=
  match a with
  | some x0 => some x0
  | none => if p x then some x else none

private theorem foldl_find_step {α : Type*} (p : α → Bool) :
    ∀ (l : List α) (acc : Option α),
      l.foldl (findStep p) acc =
      match acc with | some x0 => some x0 | none => l.find? p
  | [], acc => by cases acc <;> rfl
  | x :: l, some x0 => by
    simp only [List.foldl_cons, findStep]
    exact foldl_find_step p l (some x0)
  | x :: l, none => by
    simp only [List.foldl_cons, findStep, List.find?_cons]
    cases h : p x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact foldl_find_step p l none
    · simp only [↓reduceIte]
      exact foldl_find_step p l (some x)

private theorem ret_findCycleM (r : Fin n) (f : ParentTable n) :
    (findCycleM r f).ret =
      (List.finRange n).find? fun x =>
        x != r && (List.range n).any fun k => (fun i : Fin n => f[i.1])^[k + 1] x == x := by
  unfold findCycleM
  rw [ret_foldlM]
  have hcongr : ∀ {γ δ : Type} (l : List γ) (acc : δ) (f₁ f₂ : δ → γ → δ),
      (∀ a x, f₁ a x = f₂ a x) → l.foldl f₁ acc = l.foldl f₂ acc := by
    intro γ δ l acc f₁ f₂ h
    have : f₁ = f₂ := funext fun a => funext fun x => h a x
    subst this
    rfl
  let p : Fin n → Bool := fun x =>
    x != r && (List.range n).any fun k => (fun i : Fin n => f[i.1])^[k + 1] x == x
  rw [hcongr (List.finRange n) none _ (findStep p) fun acc x => ?_]
  · rw [foldl_find_step p (List.finRange n) none]
  · cases acc with
    | some x0 => rfl
    | none =>
      by_cases hxr : x == r
      · simp [findStep, p, hxr, bne]
      · simp [findStep, p, hxr, bne, ret_hasCycleFromM]

/-- Fold state for cycle masking. -/
structure CycleMaskState (n : ℕ) where
  /-- Current node in the traversal. -/
  current : Fin n
  /-- Accumulator for the cycle mask. -/
  mask : Vector Bool n

/-- Materialize the cycle indicator vector `inCycle` of the orbit `cycleOf f x0` (`2 * n` ticks). -/
@[expose] def cycleMaskM (f : ParentTable n) (x0 : Fin n) : TimeM ℕ (Vector Bool n) := do
  let init ← Vector.ofFnM fun _ : Fin n => do ✓ pure false
  let st ← (List.range n).foldlM
    (fun (st : CycleMaskState n) _ => do
      ✓
      let cur := st.current; let mask := st.mask
      pure { current := f[cur.1], mask := mask.set cur.1 true cur.2 : CycleMaskState n })
    ({ current := x0, mask := init } : CycleMaskState n)
  pure st.mask

private theorem time_cycleMaskM (f : ParentTable n) (x0 : Fin n) :
    (cycleMaskM f x0).time = 2 * n := by
  unfold cycleMaskM
  simp only [time_bind, time_pure, add_zero]
  rw [time_vectorOfFnM, time_foldlM_of_time_eq _ _ _ (c := 1) (fun _ _ => by simp),
    List.length_range]
  simp only [time_bind, time_tick, time_pure, add_zero, Finset.sum_const, Finset.card_fin,
    smul_eq_mul, mul_one]
  omega

private theorem cycleMask_loop_spec (f : ParentTable n) (x0 : Fin n) :
    ∀ (m : ℕ) (init : Vector Bool n),
      let res := (List.range m).foldl
        (fun (st : CycleMaskState n) _ =>
          let cur := st.current; let mask := st.mask
          { current := f[cur.1], mask := mask.set cur.1 true cur.2 : CycleMaskState n })
        ({ current := x0, mask := init } : CycleMaskState n)
      res.current = (fun i : Fin n => f[i.1])^[m] x0 ∧
        ∀ j : Fin n,
          (res.mask[j.1] = true ↔ init[j.1] = true ∨ ∃ k < m, (fun i : Fin n => f[i.1])^[k] x0 = j)
  | 0, init => by
    simp
  | m + 1, init => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := cycleMask_loop_spec f x0 m init
    rcases ih with ⟨ih1, ih2⟩
    constructor
    · simp only [ih1, Function.iterate_succ_apply']
    · intro j
      simp only [Vector.getElem_set]
      by_cases hj : ((List.range m).foldl
          (fun (st : CycleMaskState n) _ =>
            let cur := st.current; let mask := st.mask
            { current := f[cur.1], mask := mask.set cur.1 true cur.2 })
          ({ current := x0, mask := init } : CycleMaskState n)).1.1 = j.1
      · have hj' : (fun i : Fin n => f[i.1])^[m] x0 = j := Fin.ext (ih1 ▸ hj)
        simp only [hj, ↓reduceIte, true_iff]
        exact Or.inr ⟨m, Nat.lt_succ_self m, hj'⟩
      · have hj' : (fun i : Fin n => f[i.1])^[m] x0 ≠ j := fun h => hj (by simp [ih1, h])
        simp only [hj, ↓reduceIte, ih2 j]
        constructor
        · rintro (hinit | ⟨k, hk, hkj⟩)
          · exact Or.inl hinit
          · exact Or.inr ⟨k, Nat.lt_succ_of_lt hk, hkj⟩
        · rintro (hinit | ⟨k, hk, hkj⟩)
          · exact Or.inl hinit
          · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
            · exact Or.inr ⟨k, hk, hkj⟩
            · exact absurd hkj hj'

private theorem ret_cycleMaskM (f : ParentTable n) (x0 : Fin n) (y : Fin n) :
    (cycleMaskM f x0).ret[y.1] = true ↔ ∃ k < n, (fun i : Fin n => f[i.1])^[k] x0 = y := by
  unfold cycleMaskM
  simp only [ret_bind, ret_pure, ret_foldlM]
  have hspec := (cycleMask_loop_spec f x0 n
    (Vector.ofFnM fun _ : Fin n => do ✓ pure false).ret).2 y
  have hinit : ((Vector.ofFnM fun _ : Fin n => do ✓ pure false).ret)[y.1] = false := by
    simp [ret_vectorOfFnM]
  simpa [hinit] using hspec

/-- Materialize `bestEntry` for every vertex `u : Fin n` (`n ^ 2` ticks). -/
@[expose] def bestEntryTableM (a : AdjTable n) (c : CostTable β n) (inCycle : Vector Bool n) :
    TimeM ℕ (Vector (Option (Fin n)) n) :=
  Vector.ofFnM fun u : Fin n =>
    argMinFinM n (fun y => inCycle[y.1] && a[u.1][y.1]) (fun y => c[u.1][y.1])

private theorem time_bestEntryTableM (a : AdjTable n) (c : CostTable β n)
    (inCycle : Vector Bool n) : (bestEntryTableM a c inCycle).time = n ^ 2 := by
  unfold bestEntryTableM
  rw [time_vectorOfFnM]
  simp [time_argMinFinM, sq]

private theorem ret_bestEntryTableM (a : AdjTable n) (c : CostTable β n)
    (inCycle : Vector Bool n) (u : Fin n) :
    (bestEntryTableM a c inCycle).ret[u.1] =
      ((List.finRange n).filter fun y => inCycle[y.1] && a[u.1][y.1]).argmin
        (fun y => c[u.1][y.1]) := by
  unfold bestEntryTableM
  rw [ret_vectorOfFnM, Vector.getElem_ofFn, ret_argMinFinM]

section AddMonoidLevel

variable [AddCommMonoid β]

/-- Tabulate for every `x : Fin n` the sum `∑ y ∈ C.erase x, c y (f y)` when `x ∈ C`, without
using subtraction (`≤ n ^ 2` ticks). -/
@[expose] def otherCycleCostM (c : CostTable β n) (f : ParentTable n)
    (inCycle : Vector Bool n) : TimeM ℕ (Vector β n) :=
  Vector.ofFnM fun x : Fin n =>
    if inCycle[x.1] then
      (List.finRange n).foldlM
        (fun acc y => do ✓ pure (if inCycle[y.1] && y != x then acc + c[y.1][f[y.1].1] else acc))
        0
    else do ✓ pure 0

omit [LinearOrder β] in
private theorem time_otherCycleCostM (c : CostTable β n) (f : ParentTable n)
    (inCycle : Vector Bool n) : (otherCycleCostM c f inCycle).time ≤ n ^ 2 := by
  unfold otherCycleCostM
  rw [time_vectorOfFnM]
  calc ∑ x : Fin n, _ ≤ ∑ _x : Fin n, n := Finset.sum_le_sum fun x _ => by
        split_ifs
        · rw [time_foldlM_of_time_eq _ _ _ (c := 1) (fun _ _ => by simp),
            List.length_finRange, mul_one]
        · have hx : 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le x.1) x.isLt)
          simpa using hx
    _ = n ^ 2 := by simp [sq]

omit [LinearOrder β] in
private theorem foldl_add_filter {α : Type*} (pred : α → Bool) (val : α → β) :
    ∀ (l : List α) (acc : β),
      l.foldl (fun a y => if pred y then a + val y else a) acc =
        acc + ((l.filter pred).map val).sum
  | [], acc => by simp
  | y :: l, acc => by
    cases h : pred y
    · rw [List.filter_cons_of_neg (by simp [h])]
      simp only [List.foldl_cons, h, Bool.false_eq_true, ↓reduceIte]
      exact foldl_add_filter pred val l acc
    · rw [List.filter_cons_of_pos (by simp [h])]
      simp only [List.foldl_cons, h, ↓reduceIte, List.map_cons, List.sum_cons]
      rw [foldl_add_filter pred val l (acc + val y), add_assoc]

omit [LinearOrder β] in
private theorem ret_otherCycleCostM (c : CostTable β n) (f : ParentTable n)
    (inCycle : Vector Bool n) (C : Finset (Fin n)) (hC : ∀ y : Fin n, inCycle[y.1] = true ↔ y ∈ C)
    {x : Fin n} (hx : x ∈ C) :
    (otherCycleCostM c f inCycle).ret[x.1] = ∑ y ∈ C.erase x, c[y.1][f[y.1].1] := by
  unfold otherCycleCostM
  rw [ret_vectorOfFnM, Vector.getElem_ofFn]
  have hxin : inCycle[x.1] = true := (hC x).mpr hx
  simp only [hxin, ↓reduceIte, ret_foldlM, ret_bind, ret_pure]
  rw [foldl_add_filter (fun y => inCycle[y.1] && y != x) (fun y => c[y.1][f[y.1].1])]
  rw [zero_add]
  have hnd : ((List.finRange n).filter (fun y => inCycle[y.1] && y != x)).Nodup :=
    (List.nodup_finRange n).filter _
  rw [← List.sum_toFinset _ hnd]
  congr 1
  ext y
  simp [hC, and_comm]

/-- Materialize `bestExit` for every vertex `w : Fin n` (`n ^ 2` ticks). -/
@[expose] def bestExitTableM (a : AdjTable n) (c : CostTable β n)
    (inCycle : Vector Bool n) (otherCycleCost : Vector β n) :
    TimeM ℕ (Vector (Option (Fin n)) n) :=
  Vector.ofFnM fun w : Fin n =>
    argMinFinM n (fun x => inCycle[x.1] && a[x.1][w.1])
      (fun x => c[x.1][w.1] + otherCycleCost[x.1])

private theorem time_bestExitTableM (a : AdjTable n) (c : CostTable β n)
    (inCycle : Vector Bool n) (otherCycleCost : Vector β n) :
    (bestExitTableM a c inCycle otherCycleCost).time = n ^ 2 := by
  unfold bestExitTableM
  rw [time_vectorOfFnM]
  simp [time_argMinFinM, sq]

private theorem ret_bestExitTableM (a : AdjTable n) (c : CostTable β n)
    (inCycle : Vector Bool n) (otherCycleCost : Vector β n) (w : Fin n) :
    (bestExitTableM a c inCycle otherCycleCost).ret[w.1] =
      ((List.finRange n).filter fun x => inCycle[x.1] && a[x.1][w.1]).argmin
        (fun x => c[x.1][w.1] + otherCycleCost[x.1]) := by
  unfold bestExitTableM
  rw [ret_vectorOfFnM, Vector.getElem_ofFn, ret_argMinFinM]

end AddMonoidLevel

/-- Materialize the contracted `n × n` adjacency table using only `O(1)` table lookups (`n ^ 2`
ticks). -/
@[expose] def contractAdjTableM (a : AdjTable n) (inCycle : Vector Bool n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 r : Fin n) :
    TimeM ℕ (AdjTable n) :=
  Vector.ofFnM fun u : Fin n => Vector.ofFnM fun w : Fin n => do
    ✓
    pure <|
      if inCycle[u.1] then
        if u == x0 then !(inCycle[w.1]) && (bestExit[w.1]).isSome
        else w == r
      else
        if inCycle[w.1] then (w == x0) && (bestEntry[u.1]).isSome
        else a[u.1][w.1]

private theorem time_contractAdjTableM (a : AdjTable n) (inCycle : Vector Bool n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 r : Fin n) :
    (contractAdjTableM a inCycle bestEntry bestExit x0 r).time = n ^ 2 := by
  unfold contractAdjTableM
  simp [time_vectorOfFnM, sq]

private theorem ret_contractAdjTableM (a : AdjTable n) (inCycle : Vector Bool n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 r u w : Fin n) :
    (contractAdjTableM a inCycle bestEntry bestExit x0 r).ret[u.1][w.1] =
      if inCycle[u.1] then
        if u == x0 then !(inCycle[w.1]) && (bestExit[w.1]).isSome
        else w == r
      else
        if inCycle[w.1] then (w == x0) && (bestEntry[u.1]).isSome
        else a[u.1][w.1] := by
  unfold contractAdjTableM
  simp [ret_vectorOfFnM]

omit [LinearOrder β] in
/-- Materialize the contracted `n × n` cost table using only `O(1)` table lookups (`n ^ 2`
ticks). -/
@[expose] def contractCostTableM [AddCommMonoid β] (c : CostTable β n) (inCycle : Vector Bool n)
    (otherCycleCost : Vector β n) (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 : Fin n) :
    TimeM ℕ (CostTable β n) :=
  Vector.ofFnM fun u : Fin n => Vector.ofFnM fun w : Fin n => do
    ✓
    pure <|
      if inCycle[u.1] then
        if u == x0 then
          match bestExit[w.1] with
          | some x => c[x.1][w.1] + otherCycleCost[x.1]
          | none => c[u.1][w.1]
        else 0
      else
        if w == x0 then
          match bestEntry[u.1] with
          | some y => c[u.1][y.1]
          | none => c[u.1][w.1]
        else c[u.1][w.1]

omit [LinearOrder β] in
private theorem time_contractCostTableM [AddCommMonoid β] (c : CostTable β n)
    (inCycle : Vector Bool n) (otherCycleCost : Vector β n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 : Fin n) :
    (contractCostTableM c inCycle otherCycleCost bestEntry bestExit x0).time = n ^ 2 := by
  unfold contractCostTableM
  simp [time_vectorOfFnM, sq]

omit [LinearOrder β] in
private theorem ret_contractCostTableM [AddCommMonoid β] (c : CostTable β n)
    (inCycle : Vector Bool n) (otherCycleCost : Vector β n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 u w : Fin n) :
    (contractCostTableM c inCycle otherCycleCost bestEntry bestExit x0).ret[u.1][w.1] =
      if inCycle[u.1] then
        if u == x0 then
          match bestExit[w.1] with
          | some x => c[x.1][w.1] + otherCycleCost[x.1]
          | none => c[u.1][w.1]
        else 0
      else
        if w == x0 then
          match bestEntry[u.1] with
          | some y => c[u.1][y.1]
          | none => c[u.1][w.1]
        else c[u.1][w.1] := by
  unfold contractCostTableM
  simp [ret_vectorOfFnM]

/-- Expand a contracted parent vector `q` using the precomputed level tables (`n` ticks). -/
@[expose] def expandParentTableM (f : ParentTable n) (inCycle : Vector Bool n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 : Fin n) (q : ParentTable n) :
    TimeM ℕ (ParentTable n) :=
  Vector.ofFnM fun v : Fin n => do
    ✓
    pure <|
      if inCycle[v.1] then
        match bestExit[(q[x0.1]).1] with
        | some x => if v == x then q[x0.1] else f[v.1]
        | none => f[v.1]
      else if q[v.1] == x0 then (bestEntry[v.1]).getD v
      else q[v.1]

private theorem time_expandParentTableM (f : ParentTable n) (inCycle : Vector Bool n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 : Fin n) (q : ParentTable n) :
    (expandParentTableM f inCycle bestEntry bestExit x0 q).time = n := by
  unfold expandParentTableM
  simp [time_vectorOfFnM]

private theorem ret_expandParentTableM (f : ParentTable n) (inCycle : Vector Bool n)
    (bestEntry bestExit : Vector (Option (Fin n)) n) (x0 : Fin n) (q : ParentTable n)
    (v : Fin n) :
    (expandParentTableM f inCycle bestEntry bestExit x0 q).ret[v.1] =
      if inCycle[v.1] then
        match bestExit[(q[x0.1]).1] with
        | some x => if v == x then q[x0.1] else f[v.1]
        | none => f[v.1]
      else if q[v.1] == x0 then (bestEntry[v.1]).getD v
      else q[v.1] := by
  unfold expandParentTableM
  simp [ret_vectorOfFnM]

end Level

/-! ### Full contraction solver -/

section Main

variable {β : Type*} [LinearOrder β] [AddCommMonoid β]

/-- Materialized-table Chu–Liu/Edmonds recursion with fuel `fuel` in `TimeM ℕ` on `Fin n`. -/
@[expose] def edmondsTableAuxM {n : ℕ} (r : Fin n) :
    ℕ → AdjTable n → CostTable β n → TimeM ℕ (Option (ParentTable n))
  | 0, _, _ => pure none
  | fuel + 1, a, c =>
    let sel := selectParentsM a c r
    if sel.ret.feasible then
      let cyc := findCycleM r sel.ret.parents
      match cyc.ret with
      | none => { ret := some sel.ret.parents, time := sel.time + cyc.time }
      | some x0 =>
        let inCycle := cycleMaskM sel.ret.parents x0
        let other := otherCycleCostM c sel.ret.parents inCycle.ret
        let bEntry := bestEntryTableM a c inCycle.ret
        let bExit := bestExitTableM a c inCycle.ret other.ret
        let a' := contractAdjTableM a inCycle.ret bEntry.ret bExit.ret x0 r
        let c' := contractCostTableM c inCycle.ret other.ret bEntry.ret bExit.ret x0
        let sub := edmondsTableAuxM r fuel a'.ret c'.ret
        match sub.ret with
        | none =>
          { ret := none,
            time := sel.time + cyc.time + inCycle.time + other.time + bEntry.time + bExit.time +
              a'.time + c'.time + sub.time }
        | some q =>
          let exp := expandParentTableM sel.ret.parents inCycle.ret bEntry.ret bExit.ret x0 q
          { ret := some exp.ret,
            time := sel.time + cyc.time + inCycle.time + other.time + bEntry.time + bExit.time +
              a'.time + c'.time + sub.time + exp.time }
    else { ret := none, time := sel.time }

/-! ### Equivalence with `edmondsAux` -/

section Transfer

omit [AddCommMonoid β] in
private theorem selectParentsM_spec {V : Type*} [FinEnum V]
    (a : AdjTable (FinEnum.card V)) (c : CostTable β (FinEnum.card V))
    (aV : V → V → Bool) (cV : V → V → β) (rV : V)
    (ha : ∀ u w, a[u.1][w.1] =
      aV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hc : ∀ u w, c[u.1][w.1] =
      cV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w)) :
    let sel := (selectParentsM a c (@FinEnum.equiv V _ rV)).ret
    (sel.feasible = true ↔ ∀ v : V, v ≠ rV → candidates aV v ≠ []) ∧
      ∀ i : Fin (FinEnum.card V),
        (@FinEnum.equiv V _).symm (sel.parents[i.1]) =
          cheapestParent aV cV rV ((@FinEnum.equiv V _).symm i) := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  let n := FinEnum.card V
  let r := e rV
  let optFn : Fin n → Option (Fin n) := fun v =>
    if v = r then some r
    else ((List.finRange n).filter fun w => a[v.1][w.1] && w != v).argmin (fun w => c[v.1][w.1])
  have hcand (v : Fin n) :
      ((List.finRange n).filter fun w => a[v.1][w.1] && w != v).map e.symm =
        candidates aV (e.symm v) := by
    unfold candidates FinEnum.toList
    rw [List.filter_map]
    refine congrArg (List.map e.symm) (List.filter_congr fun w _ => ?_)
    dsimp only [e]
    rw [ha v w]
    have hneq : (w != v) = ((@FinEnum.equiv V _).symm w != (@FinEnum.equiv V _).symm v) :=
      Bool.eq_iff_iff.mpr (by simp [bne_iff_ne, (@FinEnum.equiv V _).symm.injective.eq_iff])
    rw [hneq]
    rfl
  have hopt_eq (v : Fin n) :
      (optFn v).map e.symm =
        if e.symm v = rV then some rV
        else List.argmin (cV (e.symm v)) (candidates aV (e.symm v)) := by
    dsimp only [optFn]
    have hvr : v = r ↔ e.symm v = rV := e.symm_apply_eq.symm
    by_cases hv : v = r
    · have hvV : e.symm v = rV := hvr.mp hv
      simp [hv, r, e]
    · have hvV : e.symm v ≠ rV := fun h => hv (hvr.mpr h)
      simp only [hv, ↓reduceIte, hvV]
      rw [← hcand v, ← List.argmin_map_equiv e.symm _ (cV (e.symm v))]
      congr 1
      refine congrArg (List.argmin · _) ?_
      funext w
      exact hc v w
  have hopt_some (v : Fin n) :
      (optFn v).isSome = true ↔ (e.symm v = rV ∨ candidates aV (e.symm v) ≠ []) := by
    have h := congrArg Option.isSome (hopt_eq v)
    simp only [Option.isSome_map] at h
    rw [h]
    split_ifs with hvr
    · simp [hvr]
    · simp [hvr, Option.isSome_iff_ne_none, List.argmin_eq_none]
  rw [ret_selectParentsM]
  dsimp only
  constructor
  · rw [List.all_eq_true]
    constructor
    · intro h v hv
      have h' := (hopt_some (e v)).mp (h (e v) (List.mem_finRange _))
      simpa [e, hv] using h'
    · intro h v _
      by_cases hvr : e.symm v = rV
      · exact (hopt_some v).mpr (Or.inl hvr)
      · exact (hopt_some v).mpr (Or.inr (h _ hvr))
  · intro i
    have h := congrArg (Option.getD · (e.symm i)) (hopt_eq i)
    simp only [Vector.getElem_ofFn]
    have hget : ∀ (o : Option (Fin n)) (d : Fin n),
        e.symm (o.getD d) = (o.map e.symm).getD (e.symm d) :=
      fun o d => by cases o <;> rfl
    rw [hget, h]
    unfold cheapestParent
    dsimp only [e]
    by_cases hir : (@FinEnum.equiv V _).symm i = rV <;> simp [hir]

private theorem findCycleM_spec {V : Type*} [FinEnum V] (f : ParentTable (FinEnum.card V))
    (fV : V → V)
    (hf : ∀ i : Fin (FinEnum.card V),
      (@FinEnum.equiv V _).symm f[i.1] = fV ((@FinEnum.equiv V _).symm i))
    (rV : V) :
    ((findCycleM (@FinEnum.equiv V _ rV) f).ret).map (@FinEnum.equiv V _).symm =
      findCycle rV fV := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  let n := FinEnum.card V
  let f' : Fin n → Fin n := fun i => f[i.1]
  have hsem : Function.Semiconj e.symm f' fV := hf
  have hiter : ∀ k (x : Fin n), e.symm (f'^[k] x) = fV^[k] (e.symm x) := fun k x =>
    hsem.iterate_right k x
  rw [ret_findCycleM]
  unfold findCycle FinEnum.toList
  rw [List.find?_map]
  have hpred : ∀ x : Fin n,
      (x != e rV && (List.range n).any fun k => f'^[k + 1] x == x) =
      (e.symm x != rV && (List.range n).any fun k => fV^[k + 1] (e.symm x) == e.symm x) := by
    intro x
    have hxr : (x == e rV) = (e.symm x == rV) :=
      Bool.eq_iff_iff.mpr (by
        simp only [beq_iff_eq]
        exact ⟨fun h => by subst h; simp [e], fun h => by rw [← h]; simp [e]⟩)
    have hxb : (x != e rV) = (e.symm x != rV) := by
      simp only [bne, hxr]
    rw [hxb]
    congr 1
    refine congrArg (List.any (List.range n)) (funext fun k => ?_)
    have := hiter (k + 1) x
    exact Bool.eq_iff_iff.mpr (by
      simp only [beq_iff_eq]
      exact ⟨fun h => by rw [← this, h], fun h => e.symm.injective (by rw [this, h])⟩)
  have hfind : ((List.finRange n).find? fun x =>
      x != e rV && (List.range n).any fun k => f'^[k + 1] x == x) =
      ((List.finRange n).find? fun x =>
        e.symm x != rV && (List.range n).any fun k => fV^[k + 1] (e.symm x) == e.symm x) := by
    congr 1
    funext x
    exact hpred x
  rw [hfind]
  rfl

private theorem cycleMask_spec {V : Type*} [FinEnum V] (f : ParentTable (FinEnum.card V))
    (fV : V → V)
    (hf : ∀ i, (@FinEnum.equiv V _).symm f[i.1] = fV ((@FinEnum.equiv V _).symm i))
    (x0 : Fin (FinEnum.card V)) (y : Fin (FinEnum.card V)) :
    (cycleMaskM f x0).ret[y.1] = true ↔
      (@FinEnum.equiv V _).symm y ∈ cycleOf fV ((@FinEnum.equiv V _).symm x0) := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  let n := FinEnum.card V
  let f' : Fin n → Fin n := fun i => f[i.1]
  have hsem : Function.Semiconj e.symm f' fV := hf
  have hiter : ∀ k (x : Fin n), e.symm (f'^[k] x) = fV^[k] (e.symm x) := fun k x =>
    hsem.iterate_right k x
  rw [ret_cycleMaskM, mem_cycleOf]
  constructor
  · rintro ⟨k, hk, hky⟩
    exact ⟨k, hk, by rw [← hiter k x0, hky]⟩
  · rintro ⟨k, hk, hky⟩
    exact ⟨k, hk, e.symm.injective (by rw [hiter k x0, hky])⟩

omit [LinearOrder β] in
private theorem otherCycleCostM_spec {V : Type*} [FinEnum V]
    (c : CostTable β (FinEnum.card V)) (f : ParentTable (FinEnum.card V))
    (inCycle : Vector Bool (FinEnum.card V))
    (cV : V → V → β) (fV : V → V) (C : Finset V)
    (hc : ∀ u w, c[u.1][w.1] =
      cV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hf : ∀ i, (@FinEnum.equiv V _).symm f[i.1] = fV ((@FinEnum.equiv V _).symm i))
    (hmask : ∀ y, inCycle[y.1] = true ↔ (@FinEnum.equiv V _).symm y ∈ C)
    {x : Fin (FinEnum.card V)} (hx : inCycle[x.1] = true) :
    (otherCycleCostM c f inCycle).ret[x.1] =
      ∑ y ∈ C.erase ((@FinEnum.equiv V _).symm x), cV y (fV y) := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  let CFin : Finset (Fin (FinEnum.card V)) := Finset.univ.filter fun y => inCycle[y.1] = true
  have hCFin (y : Fin (FinEnum.card V)) : inCycle[y.1] = true ↔ y ∈ CFin := by simp [CFin]
  rw [ret_otherCycleCostM c f inCycle CFin hCFin ((hCFin x).mp hx)]
  refine Finset.sum_bij (fun y _ => e.symm y) ?_ ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_erase] at hy ⊢
    exact ⟨e.symm.injective.ne hy.1, (hmask y).mp ((hCFin y).mpr hy.2)⟩
  · intro y₁ _ y₂ _ h
    exact e.symm.injective h
  · intro y hy
    rw [Finset.mem_erase] at hy
    refine ⟨e y, Finset.mem_erase.mpr ⟨fun h => hy.1 (by simpa [e] using congrArg e.symm h),
      (hCFin (e y)).mp ((hmask (e y)).mpr (by simpa [e] using hy.2))⟩, by simp [e]⟩
  · intro y _
    rw [hc y f[y.1], hf y]

omit [AddCommMonoid β] in
private theorem bestEntryTableM_spec {V : Type*} [FinEnum V]
    (a : AdjTable (FinEnum.card V)) (c : CostTable β (FinEnum.card V))
    (inCycle : Vector Bool (FinEnum.card V))
    (aV : V → V → Bool) (cV : V → V → β) (C : Finset V)
    (ha : ∀ u w, a[u.1][w.1] =
      aV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hc : ∀ u w, c[u.1][w.1] =
      cV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hmask : ∀ y, inCycle[y.1] = true ↔ (@FinEnum.equiv V _).symm y ∈ C)
    (u : Fin (FinEnum.card V)) :
    (bestEntryTableM a c inCycle).ret[u.1].map (@FinEnum.equiv V _).symm =
      bestEntry aV cV C ((@FinEnum.equiv V _).symm u) := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  let n := FinEnum.card V
  rw [ret_bestEntryTableM]
  unfold bestEntry FinEnum.toList
  have hcost : (fun y : Fin n => c[u.1][y.1]) = cV (e.symm u) ∘ e.symm := funext fun y => hc u y
  rw [hcost, List.argmin_map_equiv e.symm]
  have hfil : ((List.finRange n).filter fun y => inCycle[y.1] && a[u.1][y.1]).map e.symm =
      ((List.finRange n).map e.symm).filter fun y => decide (y ∈ C) && aV (e.symm u) y := by
    rw [List.filter_map]
    refine congrArg (List.map e.symm) (List.filter_congr fun y _ => ?_)
    dsimp only [e]
    have hy : inCycle[y.1] = decide ((@FinEnum.equiv V _).symm y ∈ C) :=
      Bool.eq_iff_iff.mpr (by simpa using hmask y)
    rw [hy, ha u y]
    rfl
  rw [hfil]

private theorem bestExitTableM_spec {V : Type*} [FinEnum V]
    (a : AdjTable (FinEnum.card V)) (c : CostTable β (FinEnum.card V))
    (inCycle : Vector Bool (FinEnum.card V)) (other : Vector β (FinEnum.card V))
    (aV : V → V → Bool) (cV : V → V → β) (fV : V → V) (C : Finset V)
    (ha : ∀ u w, a[u.1][w.1] =
      aV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hc : ∀ u w, c[u.1][w.1] =
      cV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hmask : ∀ y, inCycle[y.1] = true ↔ (@FinEnum.equiv V _).symm y ∈ C)
    (hother : ∀ {x}, inCycle[x.1] = true →
      other[x.1] = ∑ y ∈ C.erase ((@FinEnum.equiv V _).symm x), cV y (fV y))
    (w : Fin (FinEnum.card V)) :
    (bestExitTableM a c inCycle other).ret[w.1].map (@FinEnum.equiv V _).symm =
      bestExit aV cV fV C ((@FinEnum.equiv V _).symm w) := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  let n := FinEnum.card V
  rw [ret_bestExitTableM]
  unfold bestExit FinEnum.toList
  set l := (List.finRange n).filter fun x => inCycle[x.1] && a[x.1][w.1]
  have hcomp : l.argmin (fun x => c[x.1][w.1] + other[x.1]) =
      l.argmin ((fun x => exitCost cV fV C x (e.symm w)) ∘ e.symm) := by
    refine List.argmin_congr_mem l l (fun _ hx => hx) fun x hx => ?_
    have hxin : inCycle[x.1] = true :=
      (Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp hx).2).1
    dsimp only [Function.comp_def, e]
    rw [hc x w, hother hxin, exitCost]
  rw [hcomp]
  dsimp only [e]
  rw [List.argmin_map_equiv (@FinEnum.equiv V _).symm l
    (fun x => exitCost cV fV C x ((@FinEnum.equiv V _).symm w)), List.filter_map]
  refine congrArg (List.argmin _) (congrArg (List.map (@FinEnum.equiv V _).symm)
    (List.filter_congr fun x _ => ?_))
  have hx : inCycle[x.1] = decide ((@FinEnum.equiv V _).symm x ∈ C) :=
    Bool.eq_iff_iff.mpr (by simpa using hmask x)
  rw [hx, ha x w]
  rfl

private theorem contractAdjTableM_spec {V : Type*} [FinEnum V]
    (a : AdjTable (FinEnum.card V)) (inCycle : Vector Bool (FinEnum.card V))
    (bEntry bExit : Vector (Option (Fin (FinEnum.card V))) (FinEnum.card V))
    (x0 : Fin (FinEnum.card V)) (aV : V → V → Bool) (C : Finset V) (rV : V)
    (ha : ∀ u w, a[u.1][w.1] =
      aV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hmask : ∀ y, inCycle[y.1] = true ↔ (@FinEnum.equiv V _).symm y ∈ C)
    (hbEntry_isSome : ∀ u : Fin (FinEnum.card V), bEntry[u.1].isSome =
      ((List.finRange (FinEnum.card V)).any fun y => inCycle[y.1] && a[u.1][y.1]))
    (hbExit_isSome : ∀ w : Fin (FinEnum.card V), bExit[w.1].isSome =
      ((List.finRange (FinEnum.card V)).any fun x => inCycle[x.1] && a[x.1][w.1]))
    (u w : Fin (FinEnum.card V)) :
    (contractAdjTableM a inCycle bEntry bExit x0 (@FinEnum.equiv V _ rV)).ret[u.1][w.1] =
      contractAdj aV C ((@FinEnum.equiv V _).symm x0) rV
        ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w) := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  rw [ret_contractAdjTableM]
  unfold contractAdj FinEnum.toList
  have hex : bExit[w.1].isSome =
      ((List.finRange (FinEnum.card V)).map e.symm).any
        (fun x => decide (x ∈ C) && aV x (e.symm w)) := by
    rw [hbExit_isSome w, List.any_map]
    refine congrArg (List.any (List.finRange _)) (funext fun x => ?_)
    dsimp only [Function.comp_def, e]
    have hx : inCycle[x.1] = decide ((@FinEnum.equiv V _).symm x ∈ C) :=
      Bool.eq_iff_iff.mpr (by simpa using hmask x)
    rw [hx, ha x w]
  have hen : bEntry[u.1].isSome =
      ((List.finRange (FinEnum.card V)).map e.symm).any
        (fun y => decide (y ∈ C) && aV (e.symm u) y) := by
    rw [hbEntry_isSome u, List.any_map]
    refine congrArg (List.any (List.finRange _)) (funext fun y => ?_)
    dsimp only [Function.comp_def, e]
    have hy : inCycle[y.1] = decide ((@FinEnum.equiv V _).symm y ∈ C) :=
      Bool.eq_iff_iff.mpr (by simpa using hmask y)
    rw [hy, ha u y]
  have hwr' : (w == (@FinEnum.equiv V _) rV) = decide ((@FinEnum.equiv V _).symm w = rV) :=
    Bool.eq_iff_iff.mpr (by simpa [beq_iff_eq] using (@FinEnum.equiv V _).symm_apply_eq.symm)
  have hwx : (w == x0) = decide ((@FinEnum.equiv V _).symm w = (@FinEnum.equiv V _).symm x0) :=
    Bool.eq_iff_iff.mpr (by simp [beq_iff_eq, (@FinEnum.equiv V _).symm.injective.eq_iff])
  have hw_dec : inCycle[w.1] = decide ((@FinEnum.equiv V _).symm w ∈ C) :=
    Bool.eq_iff_iff.mpr (by simpa using hmask w)
  dsimp only [e] at hex hen
  by_cases hu : inCycle[u.1] = true
  · simp only [hu, ↓reduceIte, (hmask u).mp hu]
    by_cases hux' : u = x0
    · subst hux'
      simp [hex, hw_dec]
    · simp [hux', (@FinEnum.equiv V _).symm.injective.eq_iff, hwr']
  · have huV : (@FinEnum.equiv V _).symm u ∉ C := fun h => hu ((hmask u).mpr h)
    simp only [hu, Bool.false_eq_true, ↓reduceIte, huV]
    by_cases hw : inCycle[w.1] = true
    · simp [hw, (hmask w).mp hw, hen, hwx]
    · have hwV : (@FinEnum.equiv V _).symm w ∉ C := fun h => hw ((hmask w).mpr h)
      simp [hw, hwV, ha u w]

private theorem contractCostTableM_spec {V : Type*} [FinEnum V]
    (c : CostTable β (FinEnum.card V)) (inCycle : Vector Bool (FinEnum.card V))
    (other : Vector β (FinEnum.card V))
    (bEntry bExit : Vector (Option (Fin (FinEnum.card V))) (FinEnum.card V))
    (x0 : Fin (FinEnum.card V))
    (aV : V → V → Bool) (cV : V → V → β) (fV : V → V) (C : Finset V)
    (hc : ∀ u w, c[u.1][w.1] =
      cV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w))
    (hmask : ∀ y, inCycle[y.1] = true ↔ (@FinEnum.equiv V _).symm y ∈ C)
    (hother : ∀ {x}, inCycle[x.1] = true →
      other[x.1] = ∑ y ∈ C.erase ((@FinEnum.equiv V _).symm x), cV y (fV y))
    (hbEntry : ∀ u : Fin (FinEnum.card V), bEntry[u.1].map (@FinEnum.equiv V _).symm =
      bestEntry aV cV C ((@FinEnum.equiv V _).symm u))
    (hbExit : ∀ w : Fin (FinEnum.card V), bExit[w.1].map (@FinEnum.equiv V _).symm =
      bestExit aV cV fV C ((@FinEnum.equiv V _).symm w))
    (hbExit_mem : ∀ (w xs : Fin (FinEnum.card V)), bExit[w.1] = some xs → inCycle[xs.1] = true)
    (u w : Fin (FinEnum.card V)) :
    (contractCostTableM c inCycle other bEntry bExit x0).ret[u.1][w.1] =
      contractCost aV cV fV C ((@FinEnum.equiv V _).symm x0)
        ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w) := by
  rw [ret_contractCostTableM]
  unfold contractCost
  by_cases hu : inCycle[u.1] = true
  · simp only [hu, ↓reduceIte, (hmask u).mp hu]
    by_cases hux' : u = x0
    · subst hux'
      simp only [beq_self_eq_true, ↓reduceIte]
      have hbo := hbExit w
      cases hbx : bExit[w.1] with
      | none =>
        rw [hbx, Option.map_none] at hbo
        rw [← hbo]
        dsimp only
        exact hc u w
      | some xs =>
        have hxsC := hbExit_mem w xs hbx
        rw [hbx, Option.map_some] at hbo
        rw [← hbo]
        dsimp only
        rw [hc xs w, hother hxsC, exitCost]
    · simp [beq_iff_eq, hux', (@FinEnum.equiv V _).symm.injective.eq_iff]
  · have huV : (@FinEnum.equiv V _).symm u ∉ C := fun h => hu ((hmask u).mpr h)
    simp only [hu, Bool.false_eq_true, ↓reduceIte, huV]
    by_cases hwx' : w = x0
    · subst hwx'
      simp only [beq_self_eq_true, ↓reduceIte]
      have hbi := hbEntry u
      cases hby : bEntry[u.1] with
      | none =>
        rw [hby, Option.map_none] at hbi
        rw [← hbi]
        dsimp only
        exact hc u w
      | some y =>
        rw [hby, Option.map_some] at hbi
        rw [← hbi]
        dsimp only
        exact hc u y
    · simp [beq_iff_eq, hwx', (@FinEnum.equiv V _).symm.injective.eq_iff, hc u w]

private theorem expandParentTableM_spec {V : Type*} [FinEnum V]
    (f : ParentTable (FinEnum.card V)) (inCycle : Vector Bool (FinEnum.card V))
    (bEntry bExit : Vector (Option (Fin (FinEnum.card V))) (FinEnum.card V))
    (x0 : Fin (FinEnum.card V)) (q : ParentTable (FinEnum.card V))
    (aV : V → V → Bool) (cV : V → V → β) (fV : V → V) (C : Finset V) (qV : V → V)
    (hf : ∀ i, (@FinEnum.equiv V _).symm f[i.1] = fV ((@FinEnum.equiv V _).symm i))
    (hq : ∀ v, (@FinEnum.equiv V _).symm q[(@FinEnum.equiv V _ v).1] = qV v)
    (hmask : ∀ y, inCycle[y.1] = true ↔ (@FinEnum.equiv V _).symm y ∈ C)
    (hbEntry : ∀ u : Fin (FinEnum.card V), bEntry[u.1].map (@FinEnum.equiv V _).symm =
      bestEntry aV cV C ((@FinEnum.equiv V _).symm u))
    (hbExit : ∀ w : Fin (FinEnum.card V), bExit[w.1].map (@FinEnum.equiv V _).symm =
      bestExit aV cV fV C ((@FinEnum.equiv V _).symm w))
    (v : V) :
    (@FinEnum.equiv V _).symm
        ((expandParentTableM f inCycle bEntry bExit x0 q).ret[(@FinEnum.equiv V _ v).1]) =
      expandParent aV cV fV C ((@FinEnum.equiv V _).symm x0) qV v := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  rw [ret_expandParentTableM]
  unfold expandParent
  have hv : inCycle[(@FinEnum.equiv V _ v).1] = true ↔ v ∈ C := by
    simpa [e] using hmask (e v)
  by_cases hvC : inCycle[(@FinEnum.equiv V _ v).1] = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hvC), ite_eq_left_of_eq_true _ _ (eq_true (hv.mp hvC))]
    have hbo := hbExit q[x0.1]
    have hqx0 : e.symm q[x0.1] = qV (e.symm x0) := by
      simpa [e] using hq (e.symm x0)
    rw [hqx0] at hbo
    cases hbx : bExit[q[x0.1].1] with
    | none =>
      rw [hbx, Option.map_none] at hbo
      rw [← hbo]
      dsimp only
      simpa [e] using hf (e v)
    | some xs =>
      rw [hbx, Option.map_some] at hbo
      rw [← hbo]
      dsimp only
      by_cases hvxs : @FinEnum.equiv V _ v = xs
      · have hvxs' : v = (@FinEnum.equiv V _).symm xs := by rw [← hvxs]; simp
        subst hvxs'
        dsimp only [e] at hqx0
        simpa using hqx0
      · have hvxs' : v ≠ (@FinEnum.equiv V _).symm xs := fun h => hvxs (by rw [h]; simp)
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [beq_iff_eq, hvxs])),
          ite_eq_right_of_eq_false _ _ (eq_false hvxs')]
        simpa [e] using hf (e v)
  · have hvV : v ∉ C := fun h => hvC (hv.mpr h)
    rw [ite_eq_right_of_eq_false _ _ (eq_false hvC),
      ite_eq_right_of_eq_false _ _ (eq_false hvV)]
    by_cases hqeq : q[(@FinEnum.equiv V _ v).1] = x0
    · have hqV : qV v = (@FinEnum.equiv V _).symm x0 :=
        (hq v).symm.trans (congrArg (@FinEnum.equiv V _).symm hqeq)
      rw [ite_eq_left_of_eq_true _ _ (eq_true (beq_iff_eq.mpr hqeq)),
        ite_eq_left_of_eq_true _ _ (eq_true hqV)]
      have hbi := hbEntry (@FinEnum.equiv V _ v)
      have hev : (@FinEnum.equiv V _).symm (@FinEnum.equiv V _ v) = v := by simp
      rw [hev] at hbi
      rw [← hbi]
      cases bEntry[(@FinEnum.equiv V _ v).1] <;> simp
    · have hqV : qV v ≠ (@FinEnum.equiv V _).symm x0 :=
        fun h => hqeq ((@FinEnum.equiv V _).symm.injective ((hq v).trans h))
      rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [beq_iff_eq, hqeq])),
        ite_eq_right_of_eq_false _ _ (eq_false hqV)]
      exact hq v

/-- **Exact equivalence with `ChuLiuEdmonds.edmondsAux`**: at every recursion depth `fuel`, the
materialized table solver `edmondsTableAuxM` computes the exact same parent map (up to
`FinEnum.equiv`) as `ChuLiuEdmonds.edmondsAux`. -/
theorem edmondsTableAuxM_ret_eq_edmondsAux {V : Type*} [FinEnum V] :
    ∀ (fuel : ℕ) (a : AdjTable (FinEnum.card V)) (c : CostTable β (FinEnum.card V))
      (aV : V → V → Bool) (cV : V → V → β) (rV : V),
      (∀ u w, a[u.1][w.1] =
        aV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w)) →
      (∀ u w, c[u.1][w.1] =
        cV ((@FinEnum.equiv V _).symm u) ((@FinEnum.equiv V _).symm w)) →
      (edmondsTableAuxM (@FinEnum.equiv V _ rV) fuel a c).ret.map
        (fun p v => (@FinEnum.equiv V _).symm p[((@FinEnum.equiv V _) v).1]) =
        edmondsAux rV fuel aV cV
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel + 1, a, c, aV, cV, rV, ha, hc => by
    let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
    obtain ⟨hfeas, hf⟩ := selectParentsM_spec a c aV cV rV ha hc
    set sel := (selectParentsM a c (e rV)).ret
    set fV := cheapestParent aV cV rV
    by_cases hcond : sel.feasible = true
    · have hcondV : ∀ v, v ≠ rV → candidates aV v ≠ [] := hfeas.mp hcond
      have hcyc := findCycleM_spec sel.parents fV hf rV
      cases hcycm : (findCycleM (e rV) sel.parents).ret with
      | none =>
        have hcycV : findCycle rV fV = none := by rw [← hcyc, hcycm]; rfl
        have hret : (edmondsTableAuxM (e rV) (fuel + 1) a c).ret = some sel.parents := by
          dsimp only [edmondsTableAuxM, sel]
          rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), hcycm]
        rw [hret, Option.map_some, edmondsAux, ite_eq_left hcondV, hcycV]
        congr 1
        funext v
        simpa [e] using hf (e v)
      | some x0 =>
        have hcycV : findCycle rV fV = some (e.symm x0) := by rw [← hcyc, hcycm]; rfl
        set C := cycleOf fV (e.symm x0)
        set inCycle := (cycleMaskM sel.parents x0).ret
        set other := (otherCycleCostM c sel.parents inCycle).ret
        set bEntry := (bestEntryTableM a c inCycle).ret
        set bExit := (bestExitTableM a c inCycle other).ret
        set a' := (contractAdjTableM a inCycle bEntry bExit x0 (e rV)).ret
        set c' := (contractCostTableM c inCycle other bEntry bExit x0).ret
        have hmask (y : Fin (FinEnum.card V)) : inCycle[y.1] = true ↔ e.symm y ∈ C :=
          cycleMask_spec sel.parents fV hf x0 y
        have hother {x} (hx : inCycle[x.1] = true) :
            other[x.1] = ∑ y ∈ C.erase (e.symm x), cV y (fV y) :=
          otherCycleCostM_spec c sel.parents inCycle cV fV C hc hf hmask hx
        have hbEntry (u : Fin (FinEnum.card V)) :
            bEntry[u.1].map e.symm = bestEntry aV cV C (e.symm u) :=
          bestEntryTableM_spec a c inCycle aV cV C ha hc hmask u
        have hbExit (w : Fin (FinEnum.card V)) :
            bExit[w.1].map e.symm = bestExit aV cV fV C (e.symm w) :=
          bestExitTableM_spec a c inCycle other aV cV fV C ha hc hmask hother w
        have hbEntry_isSome (u : Fin (FinEnum.card V)) : bEntry[u.1].isSome =
            (List.finRange (FinEnum.card V)).any fun y => inCycle[y.1] && a[u.1][y.1] := by
          dsimp only [bEntry]
          rw [ret_bestEntryTableM, List.isSome_argmin_filter]
        have hbExit_isSome (w : Fin (FinEnum.card V)) : bExit[w.1].isSome =
            (List.finRange (FinEnum.card V)).any fun x => inCycle[x.1] && a[x.1][w.1] := by
          dsimp only [bExit]
          rw [ret_bestExitTableM, List.isSome_argmin_filter]
        have hbExit_mem (w xs : Fin (FinEnum.card V)) (hbx : bExit[w.1] = some xs) :
            inCycle[xs.1] = true := by
          dsimp only [bExit] at hbx
          rw [ret_bestExitTableM] at hbx
          exact (Bool.and_eq_true _ _ |>.mp (List.mem_filter.mp (List.argmin_mem hbx)).2).1
        have ha' : ∀ u w, a'[u.1][w.1] =
            contractAdj aV C (e.symm x0) rV (e.symm u) (e.symm w) :=
          contractAdjTableM_spec a inCycle bEntry bExit x0 aV C rV ha hmask
            hbEntry_isSome hbExit_isSome
        have hc' : ∀ u w, c'[u.1][w.1] =
            contractCost aV cV fV C (e.symm x0) (e.symm u) (e.symm w) :=
          contractCostTableM_spec c inCycle other bEntry bExit x0 aV cV fV C hc hmask hother
            hbEntry hbExit hbExit_mem
        have hih := edmondsTableAuxM_ret_eq_edmondsAux fuel a' c'
          (contractAdj aV C (e.symm x0) rV) (contractCost aV cV fV C (e.symm x0)) rV ha' hc'
        have hstep :
            (edmondsTableAuxM (e rV) (fuel + 1) a c).ret =
              match (edmondsTableAuxM (e rV) fuel a' c').ret with
              | none => none
              | some q => some (expandParentTableM sel.parents inCycle bEntry bExit x0 q).ret := by
          dsimp only [edmondsTableAuxM, sel]
          rw [ite_eq_left_of_eq_true _ _ (eq_true hcond), hcycm]
          dsimp only
          cases hsub : (edmondsTableAuxM (e rV) fuel a' c').ret <;> rfl
        rw [hstep, edmondsAux, ite_eq_left hcondV, hcycV]
        dsimp only
        rw [← hih]
        cases hsub : (edmondsTableAuxM (e rV) fuel a' c').ret with
        | none => rfl
        | some q =>
          simp only [Option.map_some]
          congr 1
          funext v
          exact expandParentTableM_spec sel.parents inCycle bEntry bExit x0 q aV cV fV C
            (fun w => e.symm q[(e w).1]) hf (fun _ => rfl) hmask hbEntry hbExit v
    · have hncondV : ¬ ∀ v, v ≠ rV → candidates aV v ≠ [] := fun h => hcond (hfeas.mpr h)
      have hret : (edmondsTableAuxM (e rV) (fuel + 1) a c).ret = none := by
        dsimp only [edmondsTableAuxM, sel]
        rw [ite_eq_right_of_eq_false _ _ (eq_false hcond)]
      rw [hret, Option.map_none, edmondsAux, ite_eq_right hncondV]

end Transfer

/-! ### Explicit `O(n³)` charged time bound -/

section TimeBound

private theorem time_edmondsTableAuxM_le_of_live {n : ℕ} (r : Fin n) :
    ∀ (fuel : ℕ) (a : AdjTable n) (c : CostTable β n),
      (liveVertices (fun u w : Fin n => a[u.1][w.1]) r).card < fuel →
      (edmondsTableAuxM r fuel a c).time ≤
        ((liveVertices (fun u w : Fin n => a[u.1][w.1]) r).card + 1) * (13 * n ^ 2)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, a, c, hfuel => by
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le r.1) r.isLt
    have hn_le : n ≤ n ^ 2 := Nat.le_self_pow (by decide) n
    have hsel := time_selectParentsM a c r
    set sel := (selectParentsM a c r).ret
    by_cases hfeas : sel.feasible = true
    · have hfind := time_findCycleM r sel.parents
      cases hcyc : (findCycleM r sel.parents).ret with
      | none =>
        have ht : (edmondsTableAuxM r (fuel + 1) a c).time =
            (selectParentsM a c r).time + (findCycleM r sel.parents).time := by
          simp [edmondsTableAuxM, sel, hfeas, hcyc]
        have hstep : (selectParentsM a c r).time + (findCycleM r sel.parents).time
            ≤ 13 * n ^ 2 := by
          omega
        calc (edmondsTableAuxM r (fuel + 1) a c).time ≤ 13 * n ^ 2 := ht ▸ hstep
          _ ≤ (_ + 1) * (13 * n ^ 2) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      | some x0 =>
        have hx0_find : (List.finRange n).find? (fun x =>
            x != r && (List.range n).any fun k =>
              (fun i : Fin n => sel.parents[i.1])^[k + 1] x == x) =
            some x0 := by
          simpa [ret_findCycleM] using hcyc
        have hx0_mem := List.find?_some hx0_find
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.any_eq_true, List.mem_range,
          beq_iff_eq] at hx0_mem
        obtain ⟨hx0r, kcyc, hkcyc, hper⟩ := hx0_mem
        set aV : Fin n → Fin n → Bool := fun u w => a[u.1][w.1]
        set fV : Fin n → Fin n := fun i => sel.parents[i.1]
        set C : Finset (Fin n) := cycleOf fV x0
        have hm : Function.IsPeriodicPt fV (kcyc + 1) x0 := hper
        have hm0 : 0 < kcyc + 1 := Nat.succ_pos kcyc
        have hmc : kcyc + 1 ≤ FinEnum.card (Fin n) := by
          rw [FinEnum.card_fin]
          exact hkcyc
        have hx0C : x0 ∈ C := iterate_mem_cycleOf hm hm0 hmc 0
        have hfC : ∀ y ∈ C, fV y ∈ C := fun y hy => map_mem_cycleOf hm hm0 hmc hy
        have hfr : fV r = r := by
          have hs := congrArg (fun (p : SelectParentsResult n) => p.parents[r.1])
            (ret_selectParentsM a c r)
          simpa [sel, fV] using hs
        have hrC : r ∉ C := root_notMem_cycleOf r hfr hx0r hm hm0 hmc
        have hCr : ∀ y ∈ C, y ≠ r := fun y hy h => hrC (h ▸ hy)
        have hfeas_all : ∀ y : Fin n, y ≠ r →
            ∃ m, ((List.finRange n).filter fun w => a[y.1][w.1] && w != y).argmin
              (fun w => c[y.1][w.1]) = some m ∧ fV y = m := by
          intro y hyr
          have hs := ret_selectParentsM a c r
          have hall : (List.finRange n).all (fun v =>
              (if v = r then some r
              else ((List.finRange n).filter fun w => a[v.1][w.1] && w != v).argmin
                (fun w => c[v.1][w.1])).isSome) = true := by
            have := congrArg SelectParentsResult.feasible hs
            simpa [sel] using this.symm.trans hfeas
          have hy_some := (List.all_eq_true.mp hall) y (List.mem_finRange y)
          simp only [hyr, ↓reduceIte, Option.isSome_iff_exists] at hy_some
          obtain ⟨m, hm_eq⟩ := hy_some
          refine ⟨m, hm_eq, ?_⟩
          have htbl := congrArg (fun (p : SelectParentsResult n) => p.parents[y.1]) hs
          simpa [sel, fV, hyr, hm_eq] using htbl
        have hfa : ∀ y ∈ C, aV y (fV y) = true ∧ fV y ≠ y := by
          intro y hy
          obtain ⟨m, hm_eq, hfy⟩ := hfeas_all y (hCr y hy)
          have hmem := List.argmin_mem hm_eq
          simp only [List.mem_filter, List.mem_finRange, true_and, Bool.and_eq_true,
            bne_iff_ne, ne_eq] at hmem
          rw [hfy]
          exact hmem
        have hss := liveVertices_ssubset hfC hfa hx0C hrC
        set inCycle := (cycleMaskM sel.parents x0).ret
        set other := (otherCycleCostM c sel.parents inCycle).ret
        set bEntry := (bestEntryTableM a c inCycle).ret
        set bExit := (bestExitTableM a c inCycle other).ret
        set a' := (contractAdjTableM a inCycle bEntry bExit x0 r).ret
        set c' := (contractCostTableM c inCycle other bEntry bExit x0).ret
        have ha'_eq : ∀ u w : Fin n, a'[u.1][w.1] = contractAdj aV C x0 r u w := by
          intro u w
          have hmask : ∀ y : Fin n, inCycle[y.1] = true ↔ y ∈ C := fun y => by
            dsimp [inCycle, C, fV]
            rw [ret_cycleMaskM, mem_cycleOf, FinEnum.card_fin]
          have hany_congr : ∀ q : Fin n → Bool,
              (List.finRange n).any q = (FinEnum.toList (Fin n)).any q := by
            intro q
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true]
            exact ⟨fun ⟨x, _, hqx⟩ => ⟨x, FinEnum.mem_toList x, hqx⟩,
              fun ⟨x, _, hqx⟩ => ⟨x, List.mem_finRange x, hqx⟩⟩
          have hex : bExit[w.1].isSome =
              (FinEnum.toList (Fin n)).any (fun x => decide (x ∈ C) && aV x w) := by
            dsimp only [bExit]
            rw [ret_bestExitTableM, List.isSome_argmin_filter, ← hany_congr]
            refine congrArg (List.any (List.finRange n)) (funext fun x => ?_)
            have hxbool : inCycle[x.1] = decide (x ∈ C) :=
              Bool.eq_iff_iff.mpr (by simpa using hmask x)
            rw [hxbool]
          have hen : bEntry[u.1].isSome =
              (FinEnum.toList (Fin n)).any (fun y => decide (y ∈ C) && aV u y) := by
            dsimp only [bEntry]
            rw [ret_bestEntryTableM, List.isSome_argmin_filter, ← hany_congr]
            refine congrArg (List.any (List.finRange n)) (funext fun y => ?_)
            have hybool : inCycle[y.1] = decide (y ∈ C) :=
              Bool.eq_iff_iff.mpr (by simpa using hmask y)
            rw [hybool]
          dsimp only [a']
          rw [ret_contractAdjTableM]
          unfold contractAdj
          have hw_dec : inCycle[w.1] = decide (w ∈ C) :=
            Bool.eq_iff_iff.mpr (by simpa using hmask w)
          have hwx : (w == x0) = decide (w = x0) := Bool.eq_iff_iff.mpr (by simp [beq_iff_eq])
          have hwr : (w == r) = decide (w = r) := Bool.eq_iff_iff.mpr (by simp [beq_iff_eq])
          by_cases hu : inCycle[u.1] = true
          · simp only [hu, ↓reduceIte, (hmask u).mp hu]
            by_cases hux : u = x0
            · subst hux
              simp [hex, hw_dec]
            · simp [hux, hwr]
          · simp only [hu, Bool.false_eq_true, ↓reduceIte, (hmask u).not.mp hu]
            by_cases hw : inCycle[w.1] = true
            · simp [hw, (hmask w).mp hw, hen, hwx]
            · simp [hw, (hmask w).not.mp hw, aV]
        have ha'_func : (fun u w : Fin n => a'[u.1][w.1]) = contractAdj aV C x0 r := by
          funext u w
          exact ha'_eq u w
        have hlt_card : (liveVertices (fun u w : Fin n => a'[u.1][w.1]) r).card < fuel := by
          rw [ha'_func]
          have := Finset.card_lt_card hss
          omega
        have hih := time_edmondsTableAuxM_le_of_live r fuel a' c' hlt_card
        have hcard_le : (liveVertices (fun u w : Fin n => a'[u.1][w.1]) r).card + 1 ≤
            (liveVertices aV r).card := by
          rw [ha'_func]
          exact Finset.card_lt_card hss
        have hsub_le : (edmondsTableAuxM r fuel a' c').time ≤
            (liveVertices aV r).card * (13 * n ^ 2) :=
          hih.trans (Nat.mul_le_mul_right _ hcard_le)
        have h1 := time_cycleMaskM sel.parents x0
        have h2 := time_otherCycleCostM c sel.parents inCycle
        have h3 := time_bestEntryTableM a c inCycle
        have h4 := time_bestExitTableM a c inCycle other
        have h5 := time_contractAdjTableM a inCycle bEntry bExit x0 r
        have h6 := time_contractCostTableM c inCycle other bEntry bExit x0
        have hrec_eq : (edmondsTableAuxM r (fuel + 1) a c).time =
            (selectParentsM a c r).time + (findCycleM r sel.parents).time +
              (cycleMaskM sel.parents x0).time + (otherCycleCostM c sel.parents inCycle).time +
              (bestEntryTableM a c inCycle).time + (bestExitTableM a c inCycle other).time +
              (contractAdjTableM a inCycle bEntry bExit x0 r).time +
              (contractCostTableM c inCycle other bEntry bExit x0).time +
              (edmondsTableAuxM r fuel a' c').time +
              match (edmondsTableAuxM r fuel a' c').ret with
              | none => 0
              | some q => (expandParentTableM sel.parents inCycle bEntry bExit x0 q).time := by
          dsimp only [edmondsTableAuxM, sel]
          rw [ite_eq_left_of_eq_true _ _ (eq_true hfeas), hcyc]
          dsimp only
          cases hsub : (edmondsTableAuxM r fuel a' c').ret <;>
            simp [sel, inCycle, other, bEntry, bExit, a', c', add_assoc]
        have hexp_le : (match (edmondsTableAuxM r fuel a' c').ret with
            | none => 0
            | some q => (expandParentTableM sel.parents inCycle bEntry bExit x0 q).time) ≤ n := by
          cases (edmondsTableAuxM r fuel a' c').ret with
          | none => exact Nat.zero_le n
          | some q => exact (time_expandParentTableM sel.parents inCycle bEntry bExit x0 q).le
        have hlocal : (selectParentsM a c r).time + (findCycleM r sel.parents).time +
            (cycleMaskM sel.parents x0).time + (otherCycleCostM c sel.parents inCycle).time +
            (bestEntryTableM a c inCycle).time + (bestExitTableM a c inCycle other).time +
            (contractAdjTableM a inCycle bEntry bExit x0 r).time +
            (contractCostTableM c inCycle other bEntry bExit x0).time +
            (match (edmondsTableAuxM r fuel a' c').ret with
            | none => 0
            | some q =>
              (expandParentTableM sel.parents inCycle bEntry bExit x0 q).time) ≤ 13 * n ^ 2 := by
          omega
        calc (edmondsTableAuxM r (fuel + 1) a c).time ≤
              13 * n ^ 2 + (edmondsTableAuxM r fuel a' c').time := by
              rw [hrec_eq]
              omega
          _ ≤ 13 * n ^ 2 + (liveVertices aV r).card * (13 * n ^ 2) := Nat.add_le_add_left hsub_le _
          _ = ((liveVertices aV r).card + 1) * (13 * n ^ 2) := by ring
    · have ht : (edmondsTableAuxM r (fuel + 1) a c).time = (selectParentsM a c r).time := by
        dsimp only [edmondsTableAuxM, sel]
        rw [ite_eq_right_of_eq_false _ _ (eq_false hfeas)]
      calc (edmondsTableAuxM r (fuel + 1) a c).time ≤ n ^ 2 + 2 * n := ht ▸ hsel
        _ ≤ 13 * n ^ 2 := by omega
        _ ≤ ((liveVertices (fun u w : Fin n => a[u.1][w.1]) r).card + 1) * (13 * n ^ 2) :=
          Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

/-- Charged step bound for `edmondsTableAuxM` with fuel `n`: at most `n * (13 * n ^ 2) = 13 * n ^ 3`
ticks (`n = 0` takes `0` ticks). -/
theorem time_edmondsTableAuxM_le {n : ℕ} (r : Fin n) (a : AdjTable n) (c : CostTable β n) :
    (edmondsTableAuxM r n a c).time ≤ 13 * n ^ 3 := by
  have hlt : (liveVertices (fun u w : Fin n => a[u.1][w.1]) r).card < n := by
    simpa [FinEnum.card_fin] using liveVertices_card_lt (fun u w : Fin n => a[u.1][w.1]) r
  have hle : (liveVertices (fun u w : Fin n => a[u.1][w.1]) r).card + 1 ≤ n := hlt
  calc (edmondsTableAuxM r n a c).time
      ≤ ((liveVertices (fun u w : Fin n => a[u.1][w.1]) r).card + 1) * (13 * n ^ 2) :=
        time_edmondsTableAuxM_le_of_live r n a c hlt
    _ ≤ n * (13 * n ^ 2) := Nat.mul_le_mul_right _ hle
    _ = 13 * n ^ 3 := by ring

/-! ### Top-level materialized solvers for `[FinEnum V]` -/

/-- Materialized-table Chu–Liu/Edmonds algorithm in `TimeM ℕ` for spanning in-arborescences
rooted at `r`, transporting `G` and `c` onto flat `Fin (FinEnum.card V)` tables via
`FinEnum.equiv`. -/
@[expose] def edmondsTableM {V : Type*} [FinEnum V] (G : Digraph V) [DecidableRel G.Adj]
    (c : V → V → β) (r : V) : TimeM ℕ (Option (V → V)) :=
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  let a := initAdjTableM (FinEnum.card V) fun u w => decide (G.Adj (e.symm u) (e.symm w))
  let ct := initCostTableM (FinEnum.card V) fun u w => c (e.symm u) (e.symm w)
  let res := edmondsTableAuxM (e r) (FinEnum.card V) a.ret ct.ret
  { ret := res.ret.map fun p v => e.symm p[(e v).1], time := a.time + ct.time + res.time }

/-- **Equivalence with `ChuLiuEdmonds.edmonds`:** `edmondsTableM` returns the exact same parent
map as `edmonds`. -/
theorem edmondsTableM_ret_eq_edmonds {V : Type*} [FinEnum V] (G : Digraph V) [DecidableRel G.Adj]
    (c : V → V → β) (r : V) : (edmondsTableM G c r).ret = edmonds G c r := by
  exact edmondsTableAuxM_ret_eq_edmondsAux (FinEnum.card V) _ _
    (fun u w => decide (G.Adj u w)) c r
    (fun u w => ret_initAdjTableM _ _ u w) (fun u w => ret_initCostTableM _ _ u w)

private theorem time_edmondsInitAndAux_le (n : ℕ) (r : Fin n)
    (aFn : Fin n → Fin n → Bool) (cFn : Fin n → Fin n → β) :
    (initAdjTableM n aFn).time + (initCostTableM n cFn).time +
        (edmondsTableAuxM r n (initAdjTableM n aFn).ret (initCostTableM n cFn).ret).time ≤
      15 * n ^ 3 := by
  have ha := time_initAdjTableM n aFn
  have hc := time_initCostTableM n cFn
  have haux :=
    time_edmondsTableAuxM_le r (initAdjTableM n aFn).ret (initCostTableM n cFn).ret
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) r.isLt
  have hn2 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by decide)
  omega

/-- **`O(n³)` charged step bound for `edmondsTableM`**: initializing the `n × n` tables and
running the contraction solver takes at most `13 * n ^ 3 + 2 * n ^ 2 ≤ 15 * n ^ 3` ticks on `n`
vertices. -/
theorem time_edmondsTableM_le {V : Type*} [FinEnum V] (G : Digraph V) [DecidableRel G.Adj]
    (c : V → V → β) (r : V) :
    (edmondsTableM G c r).time ≤ 15 * (FinEnum.card V) ^ 3 := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  exact time_edmondsInitAndAux_le (FinEnum.card V) (e r)
    (fun u w => decide (G.Adj (e.symm u) (e.symm w))) (fun u w => c (e.symm u) (e.symm w))

/-- Materialized-table correctness for spanning in-arborescences, transferred from
`edmonds_spec`. -/
theorem edmondsTable_spec [IsOrderedAddMonoid β] {V : Type*} [FinEnum V]
    {G : Digraph V} [DecidableRel G.Adj] {c : V → V → β} {r : V} :
    (∀ p, (edmondsTableM G c r).ret = some p →
      IsInArborescenceParent G.Adj r p ∧
        ∀ t, IsInArborescenceParent G.Adj r t → parentCost c r p ≤ parentCost c r t) ∧
    ((edmondsTableM G c r).ret = none → ∀ t, ¬ IsInArborescenceParent G.Adj r t) := by
  rw [edmondsTableM_ret_eq_edmonds]
  exact edmonds_spec

/-- Materialized-table optimality over `Digraph.IsInArborescence`, transferred from
`edmonds_optimal`. -/
theorem edmondsTable_optimal [IsOrderedAddMonoid β] {V : Type*} [FinEnum V]
    {G : Digraph V} [DecidableRel G.Adj] {c : V → V → β} {r : V}
    {p : V → V} (hp : (edmondsTableM G c r).ret = some p) :
    (Digraph.parentDigraph r p).IsInArborescence r ∧ Digraph.parentDigraph r p ≤ G ∧
      ∀ (T : Digraph V) [DecidableRel T.Adj], T.IsInArborescence r → T ≤ G →
        arcCost (Digraph.parentDigraph r p) c ≤ arcCost T c := by
  rw [edmondsTableM_ret_eq_edmonds] at hp
  exact edmonds_optimal hp

/-- Materialized-table Chu–Liu/Edmonds algorithm in `TimeM ℕ` for out-arborescences (arcs
directed away from `r`). -/
@[expose] def edmondsOutTableM {V : Type*} [FinEnum V] (G : Digraph V) [DecidableRel G.Adj]
    (c : V → V → β) (r : V) : TimeM ℕ (Option (V → V)) :=
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  let a := initAdjTableM (FinEnum.card V) fun u w => decide (G.Adj (e.symm w) (e.symm u))
  let ct := initCostTableM (FinEnum.card V) fun u w => c (e.symm w) (e.symm u)
  let res := edmondsTableAuxM (e r) (FinEnum.card V) a.ret ct.ret
  { ret := res.ret.map fun p v => e.symm p[(e v).1], time := a.time + ct.time + res.time }

/-- `edmondsOutTableM` computes the exact same parent map as `edmondsOut`. -/
theorem edmondsOutTableM_ret_eq_edmondsOut {V : Type*} [FinEnum V] (G : Digraph V)
    [DecidableRel G.Adj] (c : V → V → β) (r : V) :
    (edmondsOutTableM G c r).ret = edmondsOut G c r := by
  exact edmondsTableAuxM_ret_eq_edmondsAux (FinEnum.card V) _ _
    (fun u w => decide (G.Adj w u)) (fun u w => c w u) r
    (fun u w => ret_initAdjTableM _ _ u w) (fun u w => ret_initCostTableM _ _ u w)

/-- **`O(n³)` charged step bound for `edmondsOutTableM`**: initializing the reversed `n × n`
tables and running the contraction solver takes at most `13 * n ^ 3 + 2 * n ^ 2 ≤ 15 * n ^ 3`
ticks on `n` vertices. -/
theorem time_edmondsOutTableM_le {V : Type*} [FinEnum V] (G : Digraph V) [DecidableRel G.Adj]
    (c : V → V → β) (r : V) :
    (edmondsOutTableM G c r).time ≤ 15 * (FinEnum.card V) ^ 3 := by
  let e : V ≃ Fin (FinEnum.card V) := @FinEnum.equiv V _
  exact time_edmondsInitAndAux_le (FinEnum.card V) (e r)
    (fun u w => decide (G.Adj (e.symm w) (e.symm u))) (fun u w => c (e.symm w) (e.symm u))

/-- Materialized-table correctness for out-arborescences, transferred from `edmondsOut_spec`. -/
theorem edmondsOutTable_spec [IsOrderedAddMonoid β] {V : Type*} [FinEnum V]
    {G : Digraph V} [DecidableRel G.Adj] {c : V → V → β} {r : V} :
    (∀ p, (edmondsOutTableM G c r).ret = some p →
      IsInArborescenceParent (fun u w => G.Adj w u) r p ∧
        ∀ t, IsInArborescenceParent (fun u w => G.Adj w u) r t →
          parentCost (fun u w => c w u) r p ≤ parentCost (fun u w => c w u) r t) ∧
    ((edmondsOutTableM G c r).ret = none →
      ∀ t, ¬ IsInArborescenceParent (fun u w => G.Adj w u) r t) := by
  rw [edmondsOutTableM_ret_eq_edmondsOut]
  exact edmondsOut_spec

end TimeBound

end Main

end Cslib.Algorithms.Lean.Arborescence
