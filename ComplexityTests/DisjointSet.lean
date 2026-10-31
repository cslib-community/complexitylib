/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.DisjointSet.UnionFind

/-!
# Worked disjoint-set and union-find examples

These kernel-checked examples (using no `native_decide`) exercise:

1. Empty (`n = 0`) and singleton (`n = 1`) boundary cases.
2. Tightness of the logarithmic rank and traversal bounds (`uf.rank r = Nat.log 2 4 = 2` and
   `findSteps uf 0 = Nat.log 2 4 + 1 = 3` on a balanced 4-element merge sequence), together with
   observable step reduction from path compression on repeated `Op.same` queries.
3. Adaptive cycle filtering and component conservation via `spanningForestEdges` on a 6-vertex
   disconnected multigraph with redundant cycle edges.
4. Necessity of `ValidRank`: a legal `Batteries.UnionFind` chain of length `4` with artificial
   ranks `0, 1, 2, 3` violates `ValidRank` and exceeds both `Nat.log 2 4` and
   `Nat.log 2 4 + 1`.
-/

public section

namespace ComplexityTests.DisjointSet

open Cslib.Algorithms.Lean.DisjointSet
open Cslib.Algorithms.Lean.DisjointSet.UnionFind
open Cslib.Stateful

-- Empty and singleton universes are total and preserve component counts.
example :
    (init 0).numComp = 0 ∧
      (Partition.discrete 0).numComponents = 0 ∧
      (run (init 0) getNumComponents).1 = 0 ∧
      (run (init 0) getNumComponents).2.2 = [1] ∧
      (run (init 1) (union 0 0)).1 = false ∧
      (run (init 1) (union 0 0)).2.1.numComp = 1 ∧
      (run (init 1) (union 0 0)).2.2 = [3] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Build a balanced 4-element tree:
-- `union 0 1` links 0 -> 1 (rank 1), `union 2 3` links 2 -> 3 (rank 1),
-- and `union 1 3` links 1 -> 3 (rank 2), creating the 2-edge path 0 -> 1 -> 3.
def buildFourChain : (spec 4).Client (Bool × Bool × Bool) := do
  let m₁ ← union 0 1
  let m₂ ← union 2 3
  let m₃ ← union 1 3
  pure (m₁, m₂, m₃)

def stateFourChain : State 4 :=
  (run (init 4) buildFourChain).2.1

theorem validRank_stateFourChain : ValidRank stateFourChain.uf :=
  (run_correct buildFourChain (rep_init 4)).2.1.validRank

-- All three unions merge distinct components, reaching 1 component with root 3 of rank 2 = log₂ 4
-- and `findSteps` from leaf 0 equal to 3 = log₂ 4 + 1 (tightness of `findSteps_le_log_add_one`).
example :
    ValidRank stateFourChain.uf ∧
      (run (init 4) buildFourChain).1 = (true, true, true) ∧
      stateFourChain.numComp = 1 ∧
      stateFourChain.uf.rank 3 = 2 ∧
      Nat.log 2 stateFourChain.uf.size = 2 ∧
      findSteps stateFourChain.uf ⟨0, by decide⟩ = 3 ∧
      Nat.log 2 stateFourChain.uf.size + 1 = 3 :=
  ⟨validRank_stateFourChain, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- Querying `same 0 3` twice in succession compresses `0 -> 1 -> 3` to `0 -> 3`:
-- the first query inspects 3 + 1 = 4 nodes, and the second inspects 2 + 1 = 3 nodes.
private def querySameTwice : (spec 4).Client (Bool × Bool × Bool) := do
  let q₁ ← same 0 3
  let q₂ ← same 0 3
  let redundant ← union 0 2
  pure (q₁, q₂, redundant)

example :
    (run stateFourChain querySameTwice).1 = (true, true, false) ∧
      (run stateFourChain querySameTwice).2.2 = [4, 3, 5] ∧
      (run stateFourChain querySameTwice).2.1.numComp = 1 :=
  ⟨rfl, rfl, rfl⟩

-- Adaptive spanning-forest client on a 6-vertex graph with two cycle-closing edges `(0, 2)` and
-- `(4, 3)` and isolated vertex `5`.
private def sampleGraph : List (Fin 6 × Fin 6) :=
  [(0, 1), (1, 2), (0, 2), (3, 4), (4, 3)]

private def forestAndComponents :
    (spec 6).Client (List (Fin 6 × Fin 6) × ℕ × Bool × Bool) := do
  let forest ← spanningForestEdges sampleGraph
  let comps ← getNumComponents
  let c₀₂ ← same 0 2
  let c₀₃ ← same 0 3
  pure (forest, comps, c₀₂, c₀₃)

example :
    (run (init 6) forestAndComponents).1 = ([(0, 1), (1, 2), (3, 4)], 3, true, false) ∧
      (run (init 6) forestAndComponents).1 =
        ((spec 6).runClient (Partition.discrete 6) forestAndComponents).1 ∧
      total id (run (init 6) forestAndComponents).2.2 ≤
        (spec 6).totalCost (charge 6) (Partition.discrete 6)
          ((spec 6).runClient (Partition.discrete 6) forestAndComponents).2.2 ∧
      total id (run (init 6) (spanningForestEdges sampleGraph)).2.2 ≤
        sampleGraph.length * (2 * Nat.log 2 6 + 3) ∧
      (eval (spec 6) (spanningForestEdges sampleGraph) (Partition.discrete 6)).2.numComponents +
        (eval (spec 6) (spanningForestEdges sampleGraph) (Partition.discrete 6)).1.length = 6 := by
  refine ⟨rfl,
    (run_correct forestAndComponents (rep_init 6)).1,
    (run_correct forestAndComponents (rep_init 6)).2.2.1, ?_, ?_⟩
  · have h := (run_correct (spanningForestEdges sampleGraph) (rep_init 6)).2.2.2
    rwa [runClient_spanningForestEdges_length] at h
  · simpa using spanningForestEdges_numComponents_add_length sampleGraph (Partition.discrete 6)

-- History-adaptive `connectIfNew`: after `spanningForestEdges sampleGraph`, `(0, 2)` is already
-- connected (issuing 1 operation `[Op.same 0 2]`), whereas `(0, 3)` bridges two components
-- (issuing 2 operations `[Op.same 0 3, Op.union 0 3]`).
example :
    let p := (eval (spec 6) (spanningForestEdges sampleGraph) (Partition.discrete 6)).2
    ((spec 6).runClient p (connectIfNew 0 2)).1 = false ∧
      ((spec 6).runClient p (connectIfNew 0 2)).2.2 = [.same 0 2] ∧
      ((spec 6).runClient p (connectIfNew 0 3)).1 = true ∧
      ((spec 6).runClient p (connectIfNew 0 3)).2.2 = [.same 0 3, .union 0 3] :=
  ⟨rfl, rfl, rfl, rfl⟩

-- Existence form of `realized_client` instantiated at `rep_init`.
example :
    ∃ s' traces,
      Executes (Exec 6) (spanningForestEdges sampleGraph) (init 6)
        ((spec 6).runClient (Partition.discrete 6) (spanningForestEdges sampleGraph)).1 s' traces ∧
      Rep ((spec 6).runClient (Partition.discrete 6) (spanningForestEdges sampleGraph)).2.1 s' ∧
      total id traces ≤
        (spec 6).totalCost (charge 6) (Partition.discrete 6)
          ((spec 6).runClient (Partition.discrete 6) (spanningForestEdges sampleGraph)).2.2 :=
  realized_client (spanningForestEdges sampleGraph) (rep_init 6)

-- Necessity of `ValidRank`: a 4-node chain `0 -> 1 -> 2 -> 3` with artificial ranks `0, 1, 2, 3`
-- satisfies `Batteries.UnionFind`'s structural invariants (`parentD_lt` and `rankD_lt`), yet
-- violates `ValidRank` and exceeds both `Nat.log 2 4 = 2` and `Nat.log 2 4 + 1 = 3`.
private def unrankedChain : Batteries.UnionFind where
  arr := #[⟨1, 0⟩, ⟨2, 1⟩, ⟨3, 2⟩, ⟨3, 3⟩]
  parentD_lt {i} hi := by
    decide +revert
  rankD_lt {i} hne := by
    by_cases hi : i < 4
    · match i, hi with
      | 0, _ => decide
      | 1, _ => decide
      | 2, _ => decide
      | 3, _ => exact absurd rfl hne
    · exfalso
      exact hne (Batteries.UnionFind.parentD_of_not_lt hi)

example :
    unrankedChain.size = 4 ∧
      unrankedChain.rank 3 = 3 ∧
      Nat.log 2 unrankedChain.size = 2 ∧
      findSteps unrankedChain ⟨0, by decide⟩ = 4 ∧
      ¬ ValidRank unrankedChain := by
  refine ⟨rfl, rfl, rfl, rfl, fun hvalid => ?_⟩
  have hlog := hvalid.rank_le_log 3
  have hrk : unrankedChain.rank 3 = 3 := rfl
  have hsz : Nat.log 2 unrankedChain.size = 2 := rfl
  omega

end ComplexityTests.DisjointSet
