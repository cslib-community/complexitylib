/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Card

/-!
# Edge cuts and edge-disjoint paths in simple graphs

Mathlib target: `Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean`.

Edge-connectivity weak duality, closed-set cut certificates, injectivity of edge-disjoint path
families between distinct vertices, and the path-to-connectivity half of global Menger's theorem
for Mathlib's `SimpleGraph.IsEdgeReachable` and `SimpleGraph.IsEdgeConnected`.

## Main results

* `SimpleGraph.not_reachable_deleteEdges_of_forall_adj`: closed-set edge-cut certificate.
* `SimpleGraph.le_encard_of_edgeDisjoint_of_not_reachable`: weak duality between edge-disjoint
  walks and disconnecting edge sets.
* `SimpleGraph.injective_of_edgeDisjoint`: pairwise edge-disjoint walks between distinct vertices
  are automatically injective.
* `SimpleGraph.isEdgeConnected_of_forall_exists_edgeDisjoint`: `k` edge-disjoint paths between
  every pair of vertices force `IsEdgeConnected k`.

## References

* [R. Diestel, *Graph Theory*][Diestel2025], §1.4 and §3.3 (Corollary 3.3.5 (ii),
  Theorem 3.3.6 (ii))
-/

public section

namespace SimpleGraph

variable {V : Type*}

/-- Closed-set certificate for disconnection: if `u ∈ S`, `v ∉ S` and every edge leaving `S` lies
in `C`, then `u` and `v` are disconnected in `G.deleteEdges C`. -/
theorem not_reachable_deleteEdges_of_forall_adj {G : SimpleGraph V} {u v : V} {S : Set V}
    {C : Set (Sym2 V)} (hu : u ∈ S) (hv : v ∉ S)
    (hC : ∀ x ∈ S, ∀ y, G.Adj x y → y ∉ S → s(x, y) ∈ C) :
    ¬ (G.deleteEdges C).Reachable u v := by
  rintro ⟨p⟩
  obtain ⟨d, -, hdS, hdS'⟩ := p.exists_boundary_dart S hu hv
  have hadj := d.adj
  rw [deleteEdges_adj] at hadj
  exact hadj.2 (hC _ hdS _ hadj.1 hdS')

/-- **Weak duality, undirected edge form**: `k` pairwise edge-disjoint `u`–`v` walks force every
edge set disconnecting `u` from `v` to have at least `k` edges. -/
theorem le_encard_of_edgeDisjoint_of_not_reachable {G : SimpleGraph V} {u v : V} {k : ℕ}
    (W : Fin k → G.Walk u v) (hdisj : Pairwise fun i j => ∀ e ∈ (W i).edges, e ∉ (W j).edges)
    {C : Set (Sym2 V)} (hC : ¬ (G.deleteEdges C).Reachable u v) : (k : ℕ∞) ≤ C.encard := by
  classical
  have hmem : ∀ i, ∃ e ∈ (W i).edges, e ∈ C := by
    intro i
    by_contra h
    simp only [not_exists, not_and] at h
    exact hC ⟨(W i).toDeleteEdges C h⟩
  choose e he heC using hmem
  have hinj : Function.Injective e := by
    intro i j hij
    by_contra hne
    exact hdisj hne (e i) (he i) (by rw [hij]; exact he j)
  have hsub : ((Finset.univ.image e : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ C := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact heC i
  calc (k : ℕ∞) = ((Finset.univ.image e : Finset (Sym2 V)) : Set (Sym2 V)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
          Finset.card_univ, Fintype.card_fin]
    _ ≤ C.encard := Set.encard_le_encard hsub

/-- Pairwise edge-disjoint walks between distinct vertices are distinct. -/
theorem injective_of_edgeDisjoint {G : SimpleGraph V} {u v : V} (huv : u ≠ v) {ι : Type*}
    {W : ι → G.Walk u v} (hdisj : Pairwise fun i j => ∀ e ∈ (W i).edges, e ∉ (W j).edges) :
    Function.Injective W := by
  intro i j hij
  by_contra hne
  have hnil : ¬ (W i).Nil := fun h => huv (Walk.Nil.eq h)
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ (mt Walk.edges_eq_nil.mp hnil)
  exact hdisj hne e he (hij ▸ he)

/-- If every pair of distinct vertices is joined by `k` pairwise edge-disjoint walks, then `G` is
`k`-edge-connected. -/
theorem isEdgeConnected_of_forall_exists_edgeDisjoint {G : SimpleGraph V} {k : ℕ}
    (h : ∀ ⦃u v : V⦄, u ≠ v →
      ∃ W : Fin k → G.Walk u v, Pairwise fun i j => ∀ e ∈ (W i).edges, e ∉ (W j).edges) :
    G.IsEdgeConnected k := by
  intro u v s hs
  by_cases huv : u = v
  · subst huv; exact Reachable.refl u
  · obtain ⟨W, hdisj⟩ := h huv
    by_contra hreach
    exact absurd hs (not_lt.mpr (le_encard_of_edgeDisjoint_of_not_reachable W hdisj hreach))

end SimpleGraph
