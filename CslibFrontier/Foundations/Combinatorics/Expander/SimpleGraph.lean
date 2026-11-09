/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Basic
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Rotation maps of simple graphs

A rotation map determines a simple graph, in which distinct vertices are adjacent when an edge
joins them (`RotationMap.toSimpleGraph`). When the rotation map has neither self-loops nor
parallel edges (`RotationMap.IsSimple`), this loses nothing: the simple graph is regular of degree
`|D|`, its walk operator averages over the neighbors in the simple graph, and its edges between
two sets of vertices are those of the rotation map (`IsSimple.card_interedges`), so the results
on rotation maps, such as the expander mixing lemma, apply to it. Conversely, every `d`-regular
simple graph has a simple rotation map with labels `Fin d` (`exists_isSimple_toSimpleGraph_eq`).

## Main definitions

* `Cslib.RotationMap.toSimpleGraph`: the simple graph underlying a rotation map.
* `Cslib.RotationMap.IsSimple`: a rotation map without self-loops or parallel edges.

## Main results

* `Cslib.RotationMap.IsSimple.isRegularOfDegree`: the simple graph of a simple rotation map with
  labels `D` is regular of degree `|D|`.
* `Cslib.RotationMap.IsSimple.walk_apply_eq_sum_neighborFinset`,
  `Cslib.RotationMap.IsSimple.walk_apply_eq_adjMatrix_mulVec_div`,
  `Cslib.RotationMap.IsSimple.walk_eq_smul_adjMatrix_mulVec`: its walk operator averages over
  the neighbors and acts by the adjacency matrix divided by the degree.
* `Cslib.RotationMap.IsSimple.card_interedges`: its edges between two sets of vertices are those
  of the rotation map.
* `Cslib.RotationMap.exists_isSimple_toSimpleGraph_eq`: every `d`-regular simple graph is
  presented by a simple rotation map with labels `Fin d`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V D : Type*} (G : RotationMap V D)

/-- The simple graph underlying `G`: distinct vertices are adjacent when an edge of `G` joins
them. Self-loops are dropped and parallel edges merged. -/
def toSimpleGraph : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ i, G.neighbor u i = v
  symm.symm u _ := fun ⟨huv, i, hi⟩ ↦ ⟨huv.symm, (G.rot (u, i)).2, hi ▸ G.neighbor_neighbor_rot u i⟩
  loopless.irrefl _ h := h.1 rfl

/-- Distinct vertices are adjacent in the simple graph of `G` when an edge of `G` joins them. -/
@[simp]
theorem toSimpleGraph_adj {u v : V} : G.toSimpleGraph.Adj u v ↔ u ≠ v ∧ ∃ i, G.neighbor u i = v :=
  Iff.rfl

/-- Adjacency in the simple graph of a rotation map with finitely many labels is decidable. -/
instance [DecidableEq V] [Fintype D] : DecidableRel G.toSimpleGraph.Adj :=
  fun u v ↦ inferInstanceAs (Decidable (u ≠ v ∧ ∃ i, G.neighbor u i = v))

/-- `G` is simple: it has no self-loops and no parallel edges. -/
structure IsSimple : Prop where
  /-- No edge joins a vertex to itself. -/
  neighbor_ne (v : V) (i : D) : G.neighbor v i ≠ v
  /-- No two edges at a vertex lead to the same neighbor. -/
  neighbor_injective (v : V) : Function.Injective (G.neighbor v)

namespace IsSimple

variable {G}

/-- In the simple graph of a simple rotation map, `u` and `v` are adjacent exactly when `v` is a
neighbor of `u`. -/
theorem toSimpleGraph_adj_iff (hG : G.IsSimple) {u v : V} :
    G.toSimpleGraph.Adj u v ↔ ∃ i, G.neighbor u i = v :=
  ⟨And.right, fun ⟨i, hi⟩ ↦ ⟨hi ▸ (hG.neighbor_ne u i).symm, i, hi⟩⟩

variable [Fintype D]

/-- The neighbors of `v` in the simple graph are the ends of the edges at `v`. -/
theorem neighborFinset_eq [DecidableEq V] (hG : G.IsSimple) (v : V)
    [Fintype (G.toSimpleGraph.neighborSet v)] :
    G.toSimpleGraph.neighborFinset v = univ.image (G.neighbor v) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, hG.toSimpleGraph_adj_iff, mem_image, mem_univ,
    true_and]

/-- The simple graph of a simple rotation map with labels `D` is regular of degree `|D|`. -/
theorem isRegularOfDegree (hG : G.IsSimple) [G.toSimpleGraph.LocallyFinite] :
    G.toSimpleGraph.IsRegularOfDegree (Fintype.card D) := fun v ↦ by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hG.neighborFinset_eq,
    card_image_of_injective _ (hG.neighbor_injective v), card_univ]

/-- The walk operator of a simple rotation map averages over the neighbors in its simple graph. -/
theorem walk_apply_eq_sum_neighborFinset (hG : G.IsSimple) [G.toSimpleGraph.LocallyFinite]
    (f : V → ℝ) (v : V) :
    G.walk f v = (∑ w ∈ G.toSimpleGraph.neighborFinset v, f w) / Fintype.card D := by
  classical
  rw [RotationMap.walk_apply, Fintype.expect_eq_sum_div_card, hG.neighborFinset_eq,
    sum_image fun _ _ _ _ h ↦ hG.neighbor_injective v h]

/-- For a simple rotation map on a finite vertex set, the walk operator applies the adjacency matrix
of its simple graph divided by the degree `|D|`. -/
theorem walk_apply_eq_adjMatrix_mulVec_div [Fintype V] [DecidableEq V] (hG : G.IsSimple)
    (f : V → ℝ) (v : V) :
    G.walk f v = (G.toSimpleGraph.adjMatrix ℝ).mulVec f v / Fintype.card D := by
  rw [hG.walk_apply_eq_sum_neighborFinset, G.toSimpleGraph.adjMatrix_mulVec_apply]

/-- For a simple rotation map on a finite vertex set, the walk operator is the action of the
adjacency matrix of its simple graph scaled by `|D|⁻¹`. -/
theorem walk_eq_smul_adjMatrix_mulVec [Fintype V] [DecidableEq V] (hG : G.IsSimple)
    (f : V → ℝ) :
    G.walk f = (Fintype.card D : ℝ)⁻¹ • (G.toSimpleGraph.adjMatrix ℝ).mulVec f :=
  funext fun v ↦ by
    rw [Pi.smul_apply, hG.walk_apply_eq_adjMatrix_mulVec_div, div_eq_inv_mul, smul_eq_mul]

/-- The edges of the simple graph between two sets of vertices are those of the rotation map. -/
theorem card_interedges [DecidableEq V] [DecidableRel G.toSimpleGraph.Adj] (hG : G.IsSimple)
    (S T : Finset V) : #(G.toSimpleGraph.interedges S T) = #(G.interedges S T) := by
  refine (card_bij (fun p _ ↦ (p.1, G.neighbor p.1 p.2)) (fun p hp ↦ ?_) (fun p _ q _ h ↦ ?_)
    fun e he ↦ ?_).symm
  · rw [mem_interedges] at hp
    exact G.toSimpleGraph.mk_mem_interedges_iff.2
      ⟨hp.1, hp.2, hG.toSimpleGraph_adj_iff.2 ⟨_, rfl⟩⟩
  · obtain ⟨v, i⟩ := p
    obtain ⟨w, j⟩ := q
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [hG.neighbor_injective v h]
  · obtain ⟨hS, hT, hadj⟩ := G.toSimpleGraph.mem_interedges_iff.1 he
    obtain ⟨i, hi⟩ := hG.toSimpleGraph_adj_iff.1 hadj
    exact ⟨(e.1, i), mem_interedges.2 ⟨hS, hi ▸ hT⟩, by rw [hi]⟩

end IsSimple

/-- Every `d`-regular simple graph is the simple graph of a simple rotation map with labels `Fin d`,
obtained by numbering the neighbors of each vertex [Arora and Barak, Section 21.3][AroraBarak09]. -/
theorem exists_isSimple_toSimpleGraph_eq {H : SimpleGraph V} [H.LocallyFinite] {d : ℕ}
    (hH : H.IsRegularOfDegree d) :
    ∃ G : RotationMap V (Fin d), G.IsSimple ∧ G.toSimpleGraph = H := by
  let e (v : V) : Fin d ≃ H.neighborFinset v := (equivFinOfCardEq (hH v)).symm
  have mem (v : V) (i : Fin d) : v ∈ H.neighborFinset (e v i) :=
    (H.mem_neighborFinset _ _).2 ((H.mem_neighborFinset _ _).1 (e v i).2).symm
  let rot (p : V × Fin d) : V × Fin d := ((e p.1 p.2 : V), (e (e p.1 p.2)).symm ⟨p.1, mem p.1 p.2⟩)
  have hrot : Function.Involutive rot := fun ⟨v, i⟩ ↦ by
    have key (x : V) (hx : x = v) (w : V) (hw : w ∈ H.neighborFinset x) :
        (e x).symm ⟨w, hw⟩ = (e v).symm ⟨w, hx ▸ hw⟩ := by
      subst hx
      rfl
    simp only [rot, Equiv.apply_symm_apply]
    rw [key]
    · simp
    · simp
  refine ⟨⟨rot, hrot⟩, ⟨fun v i ↦ ?_, fun v i j h ↦ ?_⟩, ?_⟩
  · exact H.ne_of_adj ((H.mem_neighborFinset _ _).1 (e v i).2) |>.symm
  · exact (e v).injective (Subtype.ext h)
  · ext u v
    refine ⟨fun ⟨_, i, hi⟩ ↦ hi ▸ (H.mem_neighborFinset _ _).1 (e u i).2, fun h ↦ ⟨H.ne_of_adj h,
      (e u).symm ⟨v, (H.mem_neighborFinset _ _).2 h⟩, ?_⟩⟩
    simp [neighbor, rot]

end Cslib.RotationMap
