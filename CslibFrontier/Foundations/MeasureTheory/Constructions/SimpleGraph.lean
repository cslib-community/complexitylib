/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/MeasureTheory/Constructions/SimpleGraph.lean`)

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Constructions.SimpleGraph
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable sets of simple graphs

Mathlib pulls the measurable space on `SimpleGraph V` back along the adjacency relation. For
countable `V` single graphs are then measurable, since a graph is determined by its adjacency
relation. For finite `V` this makes `SimpleGraph V` a discrete measurable space
(`DiscreteMeasurableSpace` follows from `MeasurableSingletonClass` and `Finite (SimpleGraph V)`),
so every set of graphs on finitely many vertices is measurable (`MeasurableSet.of_discrete`). The
graphs avoiding a fixed set of edges form a measurable set for every countable `V`.

## Main results

* `SimpleGraph.instMeasurableSingletonClass`: single graphs are measurable for countable `V`.
* `SimpleGraph.measurableSet_disjoint_edgeSet`: events defined by forbidden edges are measurable.
-/

public section

namespace SimpleGraph

variable {V : Type*}

/-- For countable `V`, single graphs are measurable: a graph is determined by its adjacency
relation. With `Finite V` this makes `SimpleGraph V` a discrete measurable space, so every event
about a random graph on finitely many vertices is measurable. -/
instance instMeasurableSingletonClass [Countable V] :
    MeasurableSingletonClass (SimpleGraph V) where
  measurableSet_singleton G := by
    have : ({G} : Set (SimpleGraph V)) = Adj ⁻¹' {G.Adj} := by
      ext H
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => SimpleGraph.ext h⟩
    rw [this]
    exact measurable_adj (measurableSet_singleton _)

/-- The graphs with no edge in a given set form a measurable set. -/
theorem measurableSet_disjoint_edgeSet [Countable V] (t : Set (Sym2 V)) :
    MeasurableSet {G : SimpleGraph V | Disjoint t G.edgeSet} := by
  have : {G : SimpleGraph V | Disjoint t G.edgeSet} = ⋂ e ∈ t, {G | e ∈ G.edgeSet}ᶜ := by
    ext G; simp [Set.disjoint_left]
  rw [this]
  refine MeasurableSet.biInter (Set.to_countable t) fun e _ => ?_
  exact (measurableSet_setOfPred.2 ((measurable_set_iff.1 measurable_edgeSet) e)).compl

end SimpleGraph
