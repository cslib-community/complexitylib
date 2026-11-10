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
graphs with a prescribed pattern of edges and non-edges on a fixed set of pairs, in particular those
avoiding a fixed set of edges, form a measurable set for every countable `V`.

## Main results

* `SimpleGraph.instMeasurableSingletonClass`: single graphs are measurable for countable `V`.
* `SimpleGraph.measurableSet_edgePattern`: events prescribing edges and non-edges are measurable.
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

/-- The graphs with a prescribed pattern of edges and non-edges on a set of pairs form a
measurable set: `e ∈ t` is an edge exactly when `b e = true`. -/
theorem measurableSet_edgePattern [Countable V] (t : Set (Sym2 V)) (b : Sym2 V → Bool) :
    MeasurableSet {G : SimpleGraph V | ∀ e ∈ t, (e ∈ G.edgeSet ↔ b e = true)} := by
  have : {G : SimpleGraph V | ∀ e ∈ t, (e ∈ G.edgeSet ↔ b e = true)} =
      ⋂ e ∈ t, {G | e ∈ G.edgeSet ↔ b e = true} := by
    ext G; simp
  rw [this]
  refine MeasurableSet.biInter (Set.to_countable t) fun e _ => ?_
  have he : MeasurableSet {G : SimpleGraph V | e ∈ G.edgeSet} :=
    measurableSet_setOfPred.2 ((measurable_set_iff.1 measurable_edgeSet) e)
  cases b e
  · simp only [Bool.false_eq_true, iff_false]
    exact he.compl
  · simpa only [iff_true] using he

/-- The graphs with no edge in a given set form a measurable set. -/
theorem measurableSet_disjoint_edgeSet [Countable V] (t : Set (Sym2 V)) :
    MeasurableSet {G : SimpleGraph V | Disjoint t G.edgeSet} := by
  simpa [Set.disjoint_left] using measurableSet_edgePattern t fun _ => false

end SimpleGraph
