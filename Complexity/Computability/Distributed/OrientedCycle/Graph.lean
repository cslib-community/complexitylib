/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Distributed.OrientedCycle.Basic
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.ZMod.Basic

/-!
# The oriented cycle as a `SimpleGraph`

The undirected graph underlying the oriented `n`-cycle `ZMod n` is Mathlib's circulant graph with
jump `1`, `OrientedCycle.graph n`. For `n = k + 1` it is `SimpleGraph.cycleGraph (k + 1)`
(`OrientedCycle.graph_succ_eq_cycleGraph`); for `n = 0` it is the two-way infinite path on `ℤ`.
Away from the one-node cycle, whose only node is its own successor, `IsProperColoring` is exactly
Mathlib's notion of a proper colouring of this graph (`OrientedCycle.isProperColoring_iff_adj`), so
the colourings computed in this directory are `SimpleGraph.Coloring`s.

## Main definitions

* `Cslib.Distributed.OrientedCycle.graph`: the undirected graph of the oriented `n`-cycle.
* `Cslib.Distributed.OrientedCycle.IsProperColoring.toColoring`: a proper colouring as a
  `SimpleGraph.Coloring`.

## Main results

* `Cslib.Distributed.OrientedCycle.graph_succ_eq_cycleGraph`: `graph (k + 1)` is Mathlib's
  `cycleGraph (k + 1)`.
* `Cslib.Distributed.OrientedCycle.isProperColoring_iff_adj`: proper colourings of the oriented
  cycle are the proper colourings of its graph, for `n ≠ 1`.
* `Cslib.Distributed.OrientedCycle.Algorithm.ColorsCycle.exists_coloring`: an algorithm that
  `c`-colours oriented cycles outputs a `SimpleGraph.Coloring` with `c` colours.
-/

public section

namespace Cslib.Distributed.OrientedCycle

/-- The undirected graph of the oriented `n`-cycle: Mathlib's circulant graph on `ZMod n` with jump
`1`, in which `u` and `v` are adjacent iff `u ≠ v` and one is the successor of the other. -/
abbrev graph (n : ℕ) : SimpleGraph (ZMod n) := SimpleGraph.circulantGraph {1}

theorem graph_adj {n : ℕ} {u v : ZMod n} :
    (graph n).Adj u v ↔ u ≠ v ∧ (u = v + 1 ∨ v = u + 1) := by
  simp only [graph, SimpleGraph.circulantGraph_adj, Set.mem_singleton_iff, sub_eq_iff_eq_add']

/-- For `n = k + 1` the graph of the oriented cycle is Mathlib's `cycleGraph (k + 1)` on
`Fin (k + 1) = ZMod (k + 1)`. -/
theorem graph_succ_eq_cycleGraph (k : ℕ) : graph (k + 1) = SimpleGraph.cycleGraph (k + 1) :=
  (SimpleGraph.cycleGraph_eq_circulantGraph k).symm

/-- Away from the one-node cycle no node is its own successor. -/
theorem self_ne_add_one {n : ℕ} (hn : n ≠ 1) (v : ZMod n) : v ≠ v + 1 := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.2 hn
  intro h
  exact one_ne_zero (left_eq_add.1 h)

theorem graph_adj_add_one {n : ℕ} (hn : n ≠ 1) (v : ZMod n) : (graph n).Adj v (v + 1) :=
  graph_adj.2 ⟨self_ne_add_one hn v, Or.inr rfl⟩

/-- For `n ≠ 1`, a colouring of the oriented cycle is proper iff adjacent nodes of its graph get
different colours. On the one-node cycle no colouring is proper, while its graph has no edges. -/
theorem isProperColoring_iff_adj {n : ℕ} (hn : n ≠ 1) {C : Type*} {c : ZMod n → C} :
    IsProperColoring c ↔ ∀ u v, (graph n).Adj u v → c u ≠ c v := by
  constructor
  · intro hc u v huv
    rcases (graph_adj.1 huv).2 with rfl | rfl
    · exact (hc v).symm
    · exact hc u
  · intro h v
    exact h v (v + 1) (graph_adj_add_one hn v)

/-- A proper colouring of the oriented cycle as a colouring of its graph. -/
@[expose] def IsProperColoring.toColoring {n : ℕ} (hn : n ≠ 1) {C : Type*} {c : ZMod n → C}
    (hc : IsProperColoring c) : (graph n).Coloring C :=
  SimpleGraph.Coloring.mk c fun {u v} huv => (isProperColoring_iff_adj hn).1 hc u v huv

@[simp] theorem IsProperColoring.toColoring_apply {n : ℕ} (hn : n ≠ 1) {C : Type*}
    {c : ZMod n → C} (hc : IsProperColoring c) (v : ZMod n) : hc.toColoring hn v = c v :=
  rfl

/-- An algorithm that properly `c`-colours every oriented `n`-cycle, `n ≠ 1`, in `t` rounds outputs
a colouring of `graph n` with colours `Fin c`. -/
theorem Algorithm.ColorsCycle.exists_coloring {S : Type*} {A : Algorithm ℕ S ℕ} {n t c : ℕ}
    (hn : n ≠ 1) (hA : A.ColorsCycle n t c) {x : ZMod n → ℕ} (hx : Function.Injective x)
    (hxn : ∀ v, x v < n) : ∃ C : (graph n).Coloring (Fin c), ∀ v, (C v : ℕ) = A.run x t v := by
  obtain ⟨h1, h2⟩ := hA x hx hxn
  refine ⟨SimpleGraph.Coloring.mk (fun v => ⟨A.run x t v, h2 v⟩) fun {u v} huv h => ?_,
    fun v => rfl⟩
  exact (isProperColoring_iff_adj hn).1 h1 u v huv (congrArg Fin.val h)

end Cslib.Distributed.OrientedCycle
