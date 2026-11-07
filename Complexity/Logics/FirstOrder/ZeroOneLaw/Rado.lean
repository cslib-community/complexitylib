/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.SimpleGraph.Rado
public import Complexity.Logics.FirstOrder.ZeroOneLaw
public import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.EquivFin

/-!
# The Rado graph and the almost-sure theory of `G(n, 1/2)`

The Rado graph `SimpleGraph.radoGraph` on `ℕ` has every extension property, so it is a model of
`Cslib.Logic.FO.graph.randomGraphTheory`. Since that theory is complete, a sentence of the graph
language holds almost surely in `G(n, 1/2)` exactly when it holds in the Rado graph, and holds
almost never otherwise [Fagin1976] [Libkin2004, Section 12.3].

The back-and-forth argument of `Cslib.Logic.FO.graph.aleph0_categorical_randomGraphTheory` also
gives the classical structure theory of the Rado graph [Rado1964]: every countable graph with
every extension property is isomorphic to it, every countable graph is an induced subgraph of it,
and it is isomorphic to its complement.

## Main results

* `Cslib.Logic.FO.graph.satisfies_extensionAxiom_iff_exists_adj`: the extension axioms in the
  finite-set form `∀ A B` disjoint, `∃ z ∉ A ∪ B` adjacent to all of `A` and none of `B`.
* `Cslib.Logic.FO.graph.model_radoGraph`: the Rado graph is a model of `randomGraphTheory`.
* `Cslib.Logic.FO.graph.tendsto_randomGraphProb_one_iff_radoGraph`,
  `Cslib.Logic.FO.graph.tendsto_randomGraphProb_zero_iff_radoGraph`: a sentence holds almost
  surely iff it holds in the Rado graph, and almost never iff it fails there.
* `Cslib.Logic.FO.graph.nonempty_iso_radoGraph`: uniqueness among countable graphs with every
  extension property.
* `Cslib.Logic.FO.graph.nonempty_embedding_radoGraph`: universality for countable graphs.
* `Cslib.Logic.FO.graph.nonempty_compl_iso_radoGraph`: the Rado graph is self-complementary.

## References

* [R. Fagin, *Probabilities on finite models*][Fagin1976]
* [R. Rado, *Universal graphs and universal functions*][Rado1964]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004], Section 12.3.
-/

public section

open FirstOrder Language Structure

namespace Cslib.Logic.FO.graph

/-! ### The extension axioms in finite-set form -/

/-- A simple graph satisfies every extension axiom exactly when, for all disjoint finite sets `A`
and `B` of vertices, some vertex outside `A ∪ B` is adjacent to every vertex of `A` and to no
vertex of `B`. -/
theorem satisfies_extensionAxiom_iff_exists_adj {V : Type*} (G : SimpleGraph V) :
    (∀ k s, Satisfies G (extensionAxiom k s)) ↔
      ∀ A B : Finset V, Disjoint A B →
        ∃ z, z ∉ A ∧ z ∉ B ∧ (∀ a ∈ A, G.Adj z a) ∧ ∀ b ∈ B, ¬G.Adj z b := by
  classical
  constructor
  · intro hG A B hAB
    -- Enumerate `A ∪ B` and prescribe adjacency exactly to the elements of `A`.
    let e := (A ∪ B).equivFin.symm
    let x : Fin (A ∪ B).card → V := fun i => (e i : V)
    have hx : Function.Injective x := Subtype.val_injective.comp e.injective
    obtain ⟨z, hz, hadj⟩ :=
      (satisfies_extensionAxiom_iff G _ _).1 (hG _ fun i => decide (x i ∈ A)) x hx
    have hx_surj : ∀ a ∈ A ∪ B, ∃ i, x i = a := fun a ha => ⟨e.symm ⟨a, ha⟩, by simp [x]⟩
    have hzadj : ∀ a ∈ A ∪ B, G.Adj z a ↔ a ∈ A := by
      intro a ha
      obtain ⟨i, rfl⟩ := hx_surj a ha
      rw [hadj i, decide_eq_true_iff]
    refine ⟨z, fun h => ?_, fun h => ?_, fun a ha => (hzadj a (Finset.mem_union_left _ ha)).2 ha,
      fun b hb h => Finset.disjoint_left.1 hAB ((hzadj b (Finset.mem_union_right _ hb)).1 h) hb⟩
    · obtain ⟨i, hi⟩ := hx_surj z (Finset.mem_union_left _ h)
      exact hz i hi.symm
    · obtain ⟨i, hi⟩ := hx_surj z (Finset.mem_union_right _ h)
      exact hz i hi.symm
  · intro hG k s
    rw [satisfies_extensionAxiom_iff]
    intro x hx
    obtain ⟨z, hzA, hzB, hA, hB⟩ := hG ((Finset.univ.filter fun i => s i = true).image x)
      ((Finset.univ.filter fun i => s i = false).image x) (by
        rw [Finset.disjoint_left]
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        rintro _ ⟨i, hi, rfl⟩ ⟨j, hj, hji⟩
        rw [hx hji, hi] at hj
        exact Bool.noConfusion hj)
    refine ⟨z, fun i hzi => ?_, fun i => ⟨fun h => ?_, fun h => hA _ (Finset.mem_image_of_mem _
      (by simpa using h))⟩⟩
    · cases hsi : s i
      · exact hzB (hzi ▸ Finset.mem_image_of_mem _ (by simpa using hsi))
      · exact hzA (hzi ▸ Finset.mem_image_of_mem _ (by simpa using hsi))
    · by_contra hsi
      exact hB _ (Finset.mem_image_of_mem _ (by simpa using hsi)) h

/-- A simple graph with every extension property is a model of the theory of the random graph. -/
theorem model_randomGraphTheory_of_satisfies {V : Type*} (G : SimpleGraph V)
    (hG : ∀ k s, Satisfies G (extensionAxiom k s)) :
    @Theory.Model _ V G.structure randomGraphTheory := by
  let := G.structure
  exact model_randomGraphTheory_iff.2
    ⟨inferInstance, fun k s => (realize_extensionAxiom s).1 (hG k s)⟩

/-- The complement of a graph with every extension property has every extension property: a
witness for the complementary pattern in `G` is a witness in `Gᶜ`. -/
theorem satisfies_extensionAxiom_compl {V : Type*} {G : SimpleGraph V}
    (hG : ∀ k s, Satisfies G (extensionAxiom k s)) (k : ℕ) (s : Fin k → Bool) :
    Satisfies Gᶜ (extensionAxiom k s) := by
  rw [satisfies_extensionAxiom_iff]
  intro x hx
  obtain ⟨z, hz, hadj⟩ := (satisfies_extensionAxiom_iff G k fun i => !s i).1 (hG _ _) x hx
  refine ⟨z, hz, fun i => ?_⟩
  rw [SimpleGraph.compl_adj, hadj i]
  cases s i <;> simp [hz i]

/-! ### The Rado graph is a model of the theory of the random graph -/

/-- The Rado graph satisfies every extension axiom. -/
theorem satisfies_extensionAxiom_radoGraph (k : ℕ) (s : Fin k → Bool) :
    Satisfies SimpleGraph.radoGraph (extensionAxiom k s) :=
  (satisfies_extensionAxiom_iff_exists_adj _).2 (fun _ _ => SimpleGraph.radoGraph_exists_adj) k s

/-- The Rado graph is a model of the theory of the random graph [Libkin2004, Section 12.3]. -/
theorem model_radoGraph :
    @Theory.Model _ ℕ SimpleGraph.radoGraph.structure randomGraphTheory :=
  model_randomGraphTheory_of_satisfies _ satisfies_extensionAxiom_radoGraph

/-- **The almost-sure theory of `G(n, 1/2)` is the theory of the Rado graph.** A sentence of the
graph language holds in `G(n, 1/2)` with probability tending to `1` exactly when it holds in the
Rado graph [Libkin2004, Section 12.3]. -/
theorem tendsto_randomGraphProb_one_iff_radoGraph (φ : Language.graph.Sentence) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop (nhds 1) ↔
      Satisfies SimpleGraph.radoGraph φ := by
  let := SimpleGraph.radoGraph.structure
  have := model_radoGraph
  rw [tendsto_randomGraphProb_one_iff]
  exact (isComplete_randomGraphTheory.realize_sentence_iff φ ℕ).symm

/-- A sentence of the graph language holds in `G(n, 1/2)` with probability tending to `0` exactly
when it fails in the Rado graph. -/
theorem tendsto_randomGraphProb_zero_iff_radoGraph (φ : Language.graph.Sentence) :
    Filter.Tendsto (fun n => randomGraphProb n fun G => Satisfies G φ) Filter.atTop (nhds 0) ↔
      ¬Satisfies SimpleGraph.radoGraph φ := by
  let := SimpleGraph.radoGraph.structure
  have := model_radoGraph
  rw [tendsto_randomGraphProb_zero_iff, ← satisfies_not]
  exact (isComplete_randomGraphTheory.realize_sentence_iff φ.not ℕ).symm

/-! ### Uniqueness, universality and self-complementarity -/

/-- An equivalence of graph-language structures `G.structure ≃ H.structure` is a graph
isomorphism. -/
private def isoOfEquiv {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : @Language.Equiv Language.graph V W G.structure H.structure) : G ≃g H where
  toEquiv := @Language.Equiv.toEquiv _ _ _ G.structure H.structure f
  map_rel_iff' {a b} := by
    let := G.structure
    let := H.structure
    exact f.map_rel adj ![a, b]

/-- An embedding of graph-language structures `G.structure ↪ H.structure` is an induced graph
embedding. -/
private def embeddingOfEmbedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : @Language.Embedding Language.graph V W G.structure H.structure) : G ↪g H where
  toEmbedding := @Language.Embedding.toEmbedding _ _ _ G.structure H.structure f
  map_rel_iff' {a b} := by
    let := G.structure
    let := H.structure
    exact f.map_rel adj ![a, b]

/-- **Uniqueness of the Rado graph.** Every countable simple graph with every extension property
is isomorphic to the Rado graph [Rado1964] [Libkin2004, Section 12.3]. -/
theorem nonempty_iso_radoGraph {V : Type*} [Countable V] (G : SimpleGraph V)
    (hG : ∀ k s, Satisfies G (extensionAxiom k s)) : Nonempty (G ≃g SimpleGraph.radoGraph) := by
  let := G.structure
  let := SimpleGraph.radoGraph.structure
  have hV := model_randomGraphTheory_iff.1 (model_randomGraphTheory_of_satisfies G hG)
  have hN := model_randomGraphTheory_iff.1 model_radoGraph
  obtain ⟨f, -⟩ := equiv_between_cg cg_of_countable cg_of_countable default
    (isExtensionPair_of_hasExtension hN.2) (isExtensionPair_of_hasExtension hV.2)
  exact ⟨isoOfEquiv f⟩

/-- **Universality of the Rado graph.** Every countable simple graph is an induced subgraph of the
Rado graph [Rado1964]. -/
theorem nonempty_embedding_radoGraph {V : Type*} [Countable V] (G : SimpleGraph V) :
    Nonempty (G ↪g SimpleGraph.radoGraph) := by
  let := G.structure
  let := SimpleGraph.radoGraph.structure
  have hN := model_randomGraphTheory_iff.1 model_radoGraph
  obtain ⟨f, -⟩ := embedding_from_cg (show Structure.CG Language.graph V from cg_of_countable)
    default (isExtensionPair_of_hasExtension hN.2)
  exact ⟨embeddingOfEmbedding f⟩

/-- The Rado graph is isomorphic to its complement. -/
theorem nonempty_compl_iso_radoGraph :
    Nonempty (SimpleGraph.radoGraphᶜ ≃g SimpleGraph.radoGraph) :=
  nonempty_iso_radoGraph _ (satisfies_extensionAxiom_compl satisfies_extensionAxiom_radoGraph)

end Cslib.Logic.FO.graph
