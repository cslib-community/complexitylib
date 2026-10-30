/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.VanEmdeBoas.Stateful
public import ComplexityTests.OrderedSet

/-!
Boundary and adaptive examples for the recursive vEB algorithms (`member`, `insert`, `erase`,
`minimum`, `successor`, `predecessor`) and their `OrderedSet` realization. These evaluate Lean
functions and active recursive-call counts; they do not measure or certify RAM running time.
-/

open Cslib.Algorithms.Lean.VanEmdeBoas
open Cslib.OrderedSet Cslib.Stateful

@[expose] public section

namespace ComplexityTests.VanEmdeBoas

/-- Insert a list of keys into the empty vEB tree of depth `d`. -/
def ofList (d : ℕ) (xs : List ℕ) : Tree d :=
  xs.foldl Tree.insert (Tree.empty d)

private def membership (d : ℕ) (xs : List ℕ) : List Bool :=
  (List.range (universeSize d + 1)).map (ofList d xs).member

private def successors (d : ℕ) (xs : List ℕ) : List (Option ℕ) :=
  (List.range (universeSize d + 1)).map (ofList d xs).successor

private def predecessors (d : ℕ) (xs : List ℕ) : List (Option ℕ) :=
  (List.range (universeSize d + 1)).map (ofList d xs).predecessor

/-- The representation invariant holds on the empty tree and after descending/duplicate
insertions and deletions. -/
theorem valid_empty_inserted_and_erased :
    (Tree.empty 2).Valid ∧
      (ofList 2 [15, 12, 8, 4, 0, 15]).Valid ∧
      (((ofList 2 [15, 12, 8, 4, 0, 15]).erase 0).erase 15).Valid := by
  have hv : (ofList 2 [15, 12, 8, 4, 0, 15]).Valid := by
    unfold ofList
    simp only [List.foldl_cons, List.foldl_nil]
    iterate 6 apply Tree.valid_insert (hx := by decide)
    exact Tree.valid_empty 2
  exact ⟨Tree.valid_empty 2, hv, Tree.valid_erase (Tree.valid_erase hv 0) 15⟩

/-- Deleting absent keys (empty cluster, singleton-cluster miss, multi-key cluster miss, and
out-of-range) leaves a valid tree structurally unchanged. -/
theorem erase_absent_keys_eq :
    let t := ofList 2 [0, 4, 5, 12, 15]
    let ts := ofList 2 [0, 4, 12, 15]
    t.erase 2 = t ∧ ts.erase 6 = ts ∧ t.erase 6 = t ∧ t.erase 13 = t ∧ t.erase 99 = t := by
  have hv : (ofList 2 [0, 4, 5, 12, 15]).Valid := by
    unfold ofList
    simp only [List.foldl_cons, List.foldl_nil]
    iterate 5 apply Tree.valid_insert (hx := by decide)
    exact Tree.valid_empty 2
  have hvs : (ofList 2 [0, 4, 12, 15]).Valid := by
    unfold ofList
    simp only [List.foldl_cons, List.foldl_nil]
    iterate 4 apply Tree.valid_insert (hx := by decide)
    exact Tree.valid_empty 2
  have hnot {u : Tree 2} (hu : u.Valid) (x : ℕ) (hm : u.member x = false) :
      ¬u.Contains x := by
    rw [← Tree.member_iff_contains hu]
    simp only [hm, Bool.false_eq_true, not_false_eq_true]
  exact ⟨Tree.erase_eq_of_not_contains hv (hnot hv 2 (by decide)),
    Tree.erase_eq_of_not_contains hvs (hnot hvs 6 (by decide)),
    Tree.erase_eq_of_not_contains hv (hnot hv 6 (by decide)),
    Tree.erase_eq_of_not_contains hv (hnot hv 13 (by decide)),
    Tree.erase_eq_of_not_contains hv (hnot hv 99 (by decide))⟩

-- Base-case (`d = 0`), descending-minima (`d = 2`), and duplicate-insertion membership,
-- successor, and predecessor evaluations (including minimum-exclusion fallback `predecessor 4 = 0`
-- and out-of-universe query `16`).
example :
    (membership 0 [] = [false, false, false] ∧
      successors 0 [] = [none, none, none] ∧
      predecessors 0 [] = [none, none, none] ∧
      membership 0 [0, 0] = [true, false, false] ∧
      successors 0 [0, 0] = [none, none, none] ∧
      predecessors 0 [0, 0] = [none, some 0, some 0] ∧
      membership 0 [1, 1] = [false, true, false] ∧
      successors 0 [1, 1] = [some 1, none, none] ∧
      predecessors 0 [1, 1] = [none, none, some 1] ∧
      membership 0 [1, 0, 1, 0] = [true, true, false] ∧
      successors 0 [1, 0, 1, 0] = [some 1, none, none] ∧
      predecessors 0 [1, 0, 1, 0] = [none, some 0, some 1]) ∧
    membership 2 [15, 12, 8, 4, 0] =
      [true, false, false, false, true, false, false, false, true, false, false, false,
        true, false, false, true, false] ∧
    successors 2 [15, 12, 8, 4, 0] =
      [some 4, some 4, some 4, some 4, some 8, some 8, some 8, some 8,
        some 12, some 12, some 12, some 12, some 15, some 15, some 15, none, none] ∧
    predecessors 2 [15, 12, 8, 4, 0] =
      [none, some 0, some 0, some 0, some 0, some 4, some 4, some 4,
        some 4, some 8, some 8, some 8, some 8, some 12, some 12, some 12, some 15] ∧
    membership 2 [8, 4, 12, 2, 10, 0, 15, 8, 4, 12, 2, 10, 0, 15] =
      membership 2 [0, 2, 4, 8, 10, 12, 15] ∧
    successors 2 [8, 4, 12, 2, 10, 0, 15, 8, 4, 12, 2, 10, 0, 15] =
      successors 2 [0, 2, 4, 8, 10, 12, 15] ∧
    predecessors 2 [8, 4, 12, 2, 10, 0, 15, 8, 4, 12, 2, 10, 0, 15] =
      predecessors 2 [0, 2, 4, 8, 10, 12, 15] := by
  decide

-- Intra-cluster vs summary-fallback predecessor queries on `[0, 4, 5, 12, 15]`.
example :
    let t := ofList 2 [0, 4, 5, 12, 15]
    t.predecessor 0 = none ∧
      t.predecessor 4 = some 0 ∧ -- minimum-exclusion fallback (`0` is not in any cluster)
      t.predecessor 5 = some 4 ∧ -- intra-cluster predecessor (`cluster 1` has min `0 < 1`)
      t.predecessor 6 = some 5 ∧ -- intra-cluster `M < x`
      t.predecessor 12 = some 5 ∧ -- summary predecessor (`cluster 3` min `0` not `< 0`, prev `1`)
      t.predecessor 15 = some 12 ∧ -- intra-cluster predecessor in `cluster 3`
      t.predecessor 16 = some 15 := by
  decide

-- Single-recursion deletion cases on `d = 0` and `d = 2`:
-- excluded-minimum promotion (`erase 0`), singleton-cluster summary deletion (`erase 4`),
-- multi-key cluster deletion (`erase 15`), and singleton-root `O(1)` clearing (`eraseVisits = 1`).
example :
    let t0 := ofList 0 [0, 1]
    ((t0.erase 2).bounds = some (0, 1) ∧
      (t0.erase 0).bounds = some (1, 1) ∧
      (t0.erase 1).bounds = some (0, 0) ∧
      ((t0.erase 0).erase 1).bounds = none) ∧
    let t := ofList 2 [0, 4, 5, 12, 15]
    let t1 := t.erase 0 -- promotes `4` from two-key cluster `1` (`{0, 1}` -> `{1}`)
    let t2 := t1.erase 4 -- promotes `5` from singleton cluster `1` and erases `1` from summary
    let t3 := t2.erase 15 -- erases `3` from two-key cluster `3` (`{0, 3}` -> `{0}`), updates max
    let t4 := t3.erase 5 -- promotes `12`, emptying cluster `3` (`m = M = 12`)
    let t5 := t4.erase 12 -- singleton root cleared in 1 active call
    t1.bounds = some (4, 15) ∧
      t2.bounds = some (5, 15) ∧
      t3.bounds = some (5, 12) ∧
      t4.bounds = some (12, 12) ∧
      t4.eraseVisits 12 = 1 ∧
      t5.bounds = none ∧
      (List.range 17).map t3.member =
        (List.range 17).map ([5, 12].contains ·) ∧
      (List.range 17).map t3.predecessor =
        [none, none, none, none, none, none,
          some 5, some 5, some 5, some 5, some 5, some 5, some 5,
          some 12, some 12, some 12, some 12] := by
  decide

private def adaptive (choosePresent : Bool) : Bool × Option ℕ × Bool :=
  let t := ofList 2 [7, 12]
  let first := if choosePresent then 7 else 3
  let t := if t.member first then t.insert 0 else t.insert first
  let next := t.successor 2
  let t := match next with
    | some x => t.insert (x - 1)
    | none => t.insert 15
  (t.member 0, next, t.member 2)

private def histories : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (List.range 4).flatMap fun x => (histories n).map (x :: ·)

private def agrees (xs : List ℕ) : Bool :=
  let t := ofList 1 xs
  (List.range 5).all fun x =>
    t.member x == xs.contains x &&
      t.successor x == ((List.range 4).filter fun y => xs.contains y && x < y).head?

-- Adaptive branching and all 256 four-insertion histories over the four-key universe (`d = 1`).
example :
    (adaptive true = (true, some 7, false) ∧ adaptive false = (false, some 3, true)) ∧
    (histories 3).all (fun xs => agrees (0 :: xs)) = true ∧
    (histories 3).all (fun xs => agrees (1 :: xs)) = true ∧
    (histories 3).all (fun xs => agrees (2 :: xs)) = true ∧
    (histories 3).all (fun xs => agrees (3 :: xs)) = true := by
  decide

private def agreesInsertThenErase (ins dels : List ℕ) : Bool :=
  let t := dels.foldl Tree.erase (ofList 1 ins)
  let present := fun y => ins.contains y && !dels.contains y
  (List.range 5).all fun x =>
    t.member x == present x &&
      t.successor x == ((List.range 4).filter fun y => present y && x < y).head? &&
      t.predecessor x == ((List.range 4).filter fun y => present y && y < x).getLast?

-- All 256 mixed 2-insert + 2-erase histories over the four-key universe (`d = 1`), checking
-- `member`, `successor`, and `predecessor` simultaneously.
example :
    (histories 2).all (fun ins =>
      (histories 2).all (fun dels => agreesInsertThenErase ins dels)) = true := by
  decide

/-- Adaptive `OrderedSet` client (`insertAll`, `firstTwo`, and two `extractMin` steps) over
`Fin (universeSize 2)`. -/
def priorityWorkflow :
    (spec (Fin (universeSize 2))).Client
      ((Option (Fin (universeSize 2)) × Option (Fin (universeSize 2))) ×
        Option (Fin (universeSize 2)) × Option (Fin (universeSize 2))) := do
  insertAll [12, 5, 0, 15, 4, 5]
  let pair ← firstTwo
  let first ← extractMin
  let second ← extractMin
  pure (pair, first, second)

private def priorityRes := run (Tree.empty 2) priorityWorkflow

-- Shared `OrderedSet` clients executed on `Tree 2` (`Fin (universeSize 2)`), checking answers,
-- final `finElements`, and active recursive-call traces (`≤ d + 1 = 3`).
example :
    priorityRes.1 = ((some 0, some 4), some 0, some 4) ∧
      priorityRes.2.1.finElements = {5, 12, 15} ∧
      priorityRes.2.2 = [1, 2, 3, 3, 3, 3, 1, 2, 1, 3, 1, 3] ∧
      priorityRes.2.2.all (· ≤ 3) = true := by
  decide

/-- End-to-end instantiation of `run_correct` and `Bound.client_const (callDepthBound 2)` on an
adaptive `OrderedSet` client over `Tree.empty 2`. -/
theorem priorityWorkflow_correct_and_bounded :
    (run (Tree.empty 2) priorityWorkflow).1 =
      ((spec (Fin (universeSize 2))).runClient ∅ priorityWorkflow).1 ∧
    Rep ((spec (Fin (universeSize 2))).runClient ∅ priorityWorkflow).2.1
      (run (Tree.empty 2) priorityWorkflow).2.1 ∧
    total id (run (Tree.empty 2) priorityWorkflow).2.2 ≤
      ((spec (Fin (universeSize 2))).runClient ∅ priorityWorkflow).2.2.length * 3 :=
  run_correct priorityWorkflow (rep_empty 2)

/--
info: 'Cslib.Algorithms.Lean.VanEmdeBoas.Tree.valid_empty' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tree.valid_empty

end ComplexityTests.VanEmdeBoas
