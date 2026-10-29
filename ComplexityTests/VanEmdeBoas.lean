/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.VanEmdeBoas.Elements

/-!
Boundary and adaptive examples for the recursive vEB algorithms. These evaluate Lean functions;
they do not measure or certify RAM running time.
-/

open Cslib.Algorithms.Lean.VanEmdeBoas

@[expose] public section

namespace ComplexityTests.VanEmdeBoas

/-- Insert a list of keys into the empty vEB tree of depth `d`. -/
def ofList (d : ℕ) (xs : List ℕ) : Tree d :=
  xs.foldl Tree.insert (Tree.empty d)

private def membership (d : ℕ) (xs : List ℕ) : List Bool :=
  (List.range (universeSize d + 1)).map (ofList d xs).member

private def successors (d : ℕ) (xs : List ℕ) : List (Option ℕ) :=
  (List.range (universeSize d + 1)).map (ofList d xs).successor

/-- The representation invariant holds on the empty tree and after descending/duplicate
insertions. -/
theorem valid_empty_and_inserted :
    (Tree.empty 2).Valid ∧ (ofList 2 [15, 12, 8, 4, 0, 15]).Valid := by
  refine ⟨Tree.valid_empty 2, ?_⟩
  unfold ofList
  simp only [List.foldl_cons, List.foldl_nil]
  iterate 6 apply Tree.valid_insert (hx := by decide)
  exact Tree.valid_empty 2

-- Base-case (`d = 0`), descending-minima (`d = 2`), and duplicate-insertion membership and
-- successor evaluations.
example :
    (membership 0 [] = [false, false, false] ∧
      successors 0 [] = [none, none, none] ∧
      membership 0 [0, 0] = [true, false, false] ∧
      successors 0 [0, 0] = [none, none, none] ∧
      membership 0 [1, 1] = [false, true, false] ∧
      successors 0 [1, 1] = [some 1, none, none] ∧
      membership 0 [1, 0, 1, 0] = [true, true, false] ∧
      successors 0 [1, 0, 1, 0] = [some 1, none, none]) ∧
    membership 2 [15, 12, 8, 4, 0] =
      [true, false, false, false, true, false, false, false, true, false, false, false,
        true, false, false, true, false] ∧
    successors 2 [15, 12, 8, 4, 0] =
      [some 4, some 4, some 4, some 4, some 8, some 8, some 8, some 8,
        some 12, some 12, some 12, some 12, some 15, some 15, some 15, none, none] ∧
    membership 2 [8, 4, 12, 2, 10, 0, 15, 8, 4, 12, 2, 10, 0, 15] =
      membership 2 [0, 2, 4, 8, 10, 12, 15] ∧
    successors 2 [8, 4, 12, 2, 10, 0, 15, 8, 4, 12, 2, 10, 0, 15] =
      successors 2 [0, 2, 4, 8, 10, 12, 15] := by
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

-- Adaptive branching and all 256 four-insertion histories over the four-key universe.
example :
    (adaptive true = (true, some 7, false) ∧ adaptive false = (false, some 3, true)) ∧
    (histories 3).all (fun xs => agrees (0 :: xs)) = true ∧
    (histories 3).all (fun xs => agrees (1 :: xs)) = true ∧
    (histories 3).all (fun xs => agrees (2 :: xs)) = true ∧
    (histories 3).all (fun xs => agrees (3 :: xs)) = true := by
  decide

/--
info: 'Cslib.Algorithms.Lean.VanEmdeBoas.Tree.valid_empty' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Tree.valid_empty

end ComplexityTests.VanEmdeBoas
