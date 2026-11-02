/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.StateTransition

/-!
# Adjacency-list queries as a state-transition specification

`AdjacencyList.spec n` is a read-only interface to a weighted directed graph on `Fin n`, given by
its adjacency lists of `(target, weight)` pairs. A client asks for the out-degree of a vertex
(`degree`) and for the `i`-th edge out of it (`edge`). The graph itself stays behind the
interface: a client sees one vertex and one weight per query, never a whole list. The state is
never changed. An edge query is admissible only below the out-degree.

An implementation stores the graph as it likes, for example as the offset and edge arrays that a
word RAM reads from its input. Its correctness and its charges are then proved against `step`.

## Main definitions

* `AdjacencyList.State`, `AdjacencyList.Op`, `AdjacencyList.step`, `AdjacencyList.valid`: the
  adjacency lists, the two queries with their answers, the transition function and the
  admissibility precondition.
* `AdjacencyList.spec`: the deterministic specification over `Fin n`.

## Main results

* `AdjacencyList.step_degree`, `AdjacencyList.step_edge`: the answers of the two queries.
-/

@[expose] public section

namespace Cslib.DataStructure.AdjacencyList

/-- The adjacency lists of a weighted directed graph on `Fin n`: `adj u` holds a pair `(v, c)`
for each edge from `u` to `v` of weight `c`. -/
abbrev State (n : ℕ) := Fin n → List (Fin n × ℕ)

/-- Queries to the adjacency lists of a graph on `Fin n`. -/
inductive Op (n : ℕ) where
  /-- The number of edges out of `u`. -/
  | degree (u : Fin n)
  /-- The `i`-th edge out of `u`, as its target and its weight. -/
  | edge (u : Fin n) (i : ℕ)
  deriving DecidableEq, Repr

/-- The answer types of the queries. -/
abbrev Op.Result {n : ℕ} : Op n → Type
  | .degree _ => ℕ
  | .edge _ _ => Fin n × ℕ

/-- The answers of the queries; the state never changes. An edge query past the out-degree is
inadmissible, and its answer `(u, 0)` is a placeholder. -/
def step {n : ℕ} (adj : State n) : (o : Op n) → State n × o.Result
  | .degree u => (adj, (adj u).length)
  | .edge u i => (adj, (adj u).getD i (u, 0))

/-- An edge query is admissible below the out-degree. -/
def valid {n : ℕ} (adj : State n) : Op n → Prop
  | .degree _ => True
  | .edge u i => i < (adj u).length

/-- The adjacency-list interface of graphs on `Fin n`. -/
abbrev spec (n : ℕ) : StateTransitionSpec :=
  StateTransitionSpec.ofFn (State := State n) (Op := Op n) (Result := Op.Result) step valid

/-- A degree query returns the length of the adjacency list. -/
@[simp]
theorem step_degree {n : ℕ} (adj : State n) (u : Fin n) :
    step adj (.degree u) = (adj, (adj u).length) := rfl

/-- An admissible edge query returns that entry of the adjacency list. -/
@[simp]
theorem step_edge {n : ℕ} (adj : State n) (u : Fin n) {i : ℕ} (hi : i < (adj u).length) :
    step adj (.edge u i) = (adj, (adj u)[i]) := by
  simp [step, List.getElem?_eq_getElem hi]

end Cslib.DataStructure.AdjacencyList
