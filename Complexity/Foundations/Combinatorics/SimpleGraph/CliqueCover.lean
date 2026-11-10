/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Clique covers and colorings of the complement

The vertices of a finite simple graph are the union of at most `l` cliques exactly when the
complement of the graph is `l`-colorable: the color classes of a coloring of the complement are
cliques of the graph, and conversely each vertex may be colored by the index of a clique covering
it. This is the correspondence behind Karp's reduction from CHROMATIC NUMBER to CLIQUE COVER
[Karp1972].

## Main results

* `SimpleGraph.exists_cliqueCover_iff_colorable_compl`: a cover of the vertices by at most `l`
  cliques exists exactly when the complement is `l`-colorable.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

public section

namespace SimpleGraph

variable {V : Type*} [Finite V] {G : SimpleGraph V} {l : ℕ}

/-- **Clique covers are colorings of the complement.** The vertices of a finite graph are the
union of at most `l` cliques exactly when its complement is `l`-colorable. -/
theorem exists_cliqueCover_iff_colorable_compl :
    (∃ S : Finset (Finset V), S.card ≤ l ∧ (∀ s ∈ S, G.IsClique (s : Set V)) ∧
      ∀ v, ∃ s ∈ S, v ∈ s) ↔ Gᶜ.Colorable l := by
  classical
  have := Fintype.ofFinite V
  constructor
  · rintro ⟨S, hcard, hclique, hcover⟩
    choose f hfS hfv using hcover
    refine Colorable.mono hcard
      ⟨Coloring.mk (fun v => S.equivFin ⟨f v, hfS v⟩) fun {u v} huv heq => ?_⟩
    have hf : f u = f v := congrArg Subtype.val (S.equivFin.injective heq)
    rw [compl_adj] at huv
    exact huv.2 (hclique (f v) (hfS v) (hf ▸ hfv u) (hfv v) huv.1)
  · rintro ⟨C⟩
    refine ⟨(Finset.univ : Finset (Fin l)).image fun i => Finset.univ.filter fun v => C v = i,
      Finset.card_image_le.trans (by simp), fun s hs u hu v hv huv => ?_, fun v =>
        ⟨_, Finset.mem_image.2 ⟨C v, Finset.mem_univ _, rfl⟩, by simp⟩⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hu hv
    by_contra h
    exact C.valid ((compl_adj G u v).2 ⟨huv, h⟩) (hu.trans hv.symm)

end SimpleGraph
