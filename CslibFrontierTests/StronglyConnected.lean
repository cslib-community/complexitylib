/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Problems.STCON.Completeness
import CslibFrontier.Computability.Complexity.Problems.StronglyConnected.Completeness
import CslibFrontier.Computability.Complexity.Problems.StronglyConnected.Reduction
import CslibFrontier.Computability.Complexity.Problems.StronglyConnected.Search

/-!
# Strongly connected digraph tests

Arora and Barak, Exercise 4.4: the language of strongly connected digraphs, encoded by adjacency
matrices, is `NL`-complete under logspace many-one reductions
(`Cslib.Complexity.StronglyConnected.logSpaceComplete`).

The language is neither empty nor everything: the two-cycle `0 ⇄ 1` is strongly connected, while
the single arc `0 → 1` is not, and the empty digraph is strongly connected. The encoding of the
two-cycle is pinned bit by bit, and the nondeterministic search accepts it and rejects the single
arc (`Cslib.Complexity.StronglyConnected.accepts_searchProgram_iff`). The reduction from directed
connectivity maps an instance without a path from `s` to `t` to a digraph that is not strongly
connected (`Cslib.Complexity.StronglyConnected.ofSTCON_mem_iff`).
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.StronglyConnected

open Cslib Cslib.Complexity

/-- The two-cycle `0 ⇄ 1`. -/
private def cycle : DigraphInstance where
  n := 2
  adj a b := decide (a ≠ b)

/-- The single arc `0 → 1`. -/
private def arc : DigraphInstance where
  n := 2
  adj a b := decide ((a : ℕ) = 0 ∧ (b : ℕ) = 1)

/-- The digraph without vertices. -/
private def empty : DigraphInstance where
  n := 0
  adj _ _ := false

-- The encoding of the two-cycle: `1^2 0`, then the matrix row by row.
example : cycle.encode = [true, true, false, false, true, true, false] := by
  decide

-- The matrix row by row.
example : adjacencyMatrix cycle.adj = (List.range 2).flatMap fun u =>
    (List.range 2).map fun v => decide (u ≠ v) :=
  adjacencyMatrix_eq_flatMap _ _ fun a b => by simp [cycle, Fin.val_eq_val]

private theorem cycle_mem : cycle ∈ StronglyConnected := by
  intro a b
  by_cases h : a = b
  · exact h ▸ .refl
  · exact .single (show decide (a ≠ b) = true by simpa using h)

private theorem arc_notMem : arc ∉ StronglyConnected := by
  have key : ∀ x, Relation.ReflTransGen arc.Adj ⟨1, by decide⟩ x → (x : ℕ) = 1 := by
    intro x hx
    induction hx with
    | refl => rfl
    | @tail y z _ hyz ih =>
      change decide ((y : ℕ) = 0 ∧ (z : ℕ) = 1) = true at hyz
      simp only [decide_eq_true_eq] at hyz
      omega
  intro h
  exact absurd (key _ (h ⟨1, by decide⟩ ⟨0, by decide⟩)) (by decide)

-- The empty digraph is strongly connected.
example : empty ∈ StronglyConnected := fun a => a.elim0

-- The search accepts the two-cycle and rejects the single arc.
example : StronglyConnected.searchProgram.toNondeterministicQueryMachine.Accepts cycle.encode :=
  (StronglyConnected.accepts_searchProgram_iff _).mpr cycle_mem

example :
    ¬ StronglyConnected.searchProgram.toNondeterministicQueryMachine.Accepts arc.encode :=
  fun h => arc_notMem ((StronglyConnected.accepts_searchProgram_iff _).mp h)

/-- No path from `0` to `1`: the single arc `1 → 0`. -/
private def backInstance : STCONInstance where
  n := 2
  adj a b := decide ((a : ℕ) = 1 ∧ (b : ℕ) = 0)
  s := 0
  t := 1

-- Its digraph has the arcs `1 → 0` (from the instance and to `s`), `0 → 0` (to `s`) and
-- `1 → 1` (from `t`), so `0` does not reach `1`.
example : StronglyConnected.ofSTCON backInstance ∉ StronglyConnected := by
  rw [StronglyConnected.ofSTCON_mem_iff, mem_STCON]
  have key : ∀ x, Relation.ReflTransGen backInstance.Adj backInstance.s x → (x : ℕ) = 0 := by
    intro x hx
    induction hx with
    | refl => rfl
    | @tail y z _ hyz ih =>
      change decide ((y : ℕ) = 1 ∧ (z : ℕ) = 0) = true at hyz
      simp only [decide_eq_true_eq] at hyz
      omega
  exact fun h => absurd (key _ h) (by decide)

-- The empty digraph is encoded by the header `0` alone, and the search accepts it.
example : empty.encode = [false] := by
  decide

example : StronglyConnected.searchProgram.toNondeterministicQueryMachine.Accepts empty.encode :=
  (StronglyConnected.accepts_searchProgram_iff _).mpr fun a => a.elim0

/-- Source and target coincide, with no arcs: the empty path connects `s` to `t`. -/
private def loopInstance : STCONInstance where
  n := 2
  adj _ _ := false
  s := 1
  t := 1

-- With `s = t`, the reduction adds arcs `v → s` and `s → v`, so the digraph is strongly connected.
example : StronglyConnected.ofSTCON loopInstance ∈ StronglyConnected :=
  (StronglyConnected.ofSTCON_mem_iff _).mpr .refl

-- The completeness theorem and its parts.
example : LogSpaceComplete NL encDigraph StronglyConnected :=
  StronglyConnected.logSpaceComplete

example : LogSpaceReducible encSTCON encDigraph STCON StronglyConnected :=
  StronglyConnected.logSpaceReducible_STCON

-- Strong connectivity and directed connectivity reduce to each other in logarithmic space.
example : LogSpaceReducible encDigraph encSTCON StronglyConnected STCON :=
  STCON.logSpaceComplete.2 encDigraph StronglyConnected StronglyConnected.mem_NL

example (h : StronglyConnected ∈ L encDigraph) : STCON ∈ L encSTCON :=
  STCON.mem_L_iff_forall_NL_eq_L.mpr (StronglyConnected.mem_L_iff_forall_NL_eq_L.mp h)

end CslibFrontierTests.StronglyConnected
