/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Sides of tree edges

For an edge `uv` of a graph `T` on a finite vertex type, `SimpleGraph.edgeSide T u v` is the set of
vertices reachable from `u` once the edge `uv` is deleted. In a tree, the two sides of an edge
partition the vertices, a path crosses each of its edges from one side to the other, and a set that
no other tree edge crosses is a side. These are the fundamental cuts of a tree, used by Gomory–Hu
trees (`CslibFrontier.Algorithms.Lean.GomoryHu.Basic`).

## Main definitions

* `SimpleGraph.edgeSide`: the vertices reachable from `u` in `T` after deleting the edge `uv`.

## Main results

* `SimpleGraph.mem_edgeSide_swap`, `SimpleGraph.edgeSide_swap`: in a tree, the two sides of an
  edge are complementary.
* `SimpleGraph.mem_edgeSide_of_mem_darts`: along a path in a forest, the start and the end of the
  path lie on opposite sides of each edge of the path.
* `SimpleGraph.edgeSide_eq_of_forall_adj`: a set containing `u`, missing `v` and crossed by no
  other tree edge is the side of `uv` containing `u`.
-/

public section

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- The side of the edge `uv` containing `u` in a graph `T`: the vertices reachable from `u` once
the edge `s(u, v)` is deleted. For an edge `uv` of a tree, this is the component of `u` in
`T - uv`. -/
noncomputable def edgeSide (T : SimpleGraph V) (u v : V) : Finset V :=
  haveI := Classical.decPred fun x => (T.deleteEdges {s(u, v)}).Reachable u x
  Finset.univ.filter fun x => (T.deleteEdges {s(u, v)}).Reachable u x

variable {T : SimpleGraph V}

theorem mem_edgeSide {u v x : V} :
    x ∈ edgeSide T u v ↔ (T.deleteEdges {s(u, v)}).Reachable u x := by
  unfold edgeSide
  simp

theorem mem_edgeSide_self (u v : V) : u ∈ edgeSide T u v :=
  mem_edgeSide.mpr (Reachable.refl u)

theorem notMem_edgeSide_of_isAcyclic (hT : T.IsAcyclic) {u v : V} (huv : T.Adj u v) :
    v ∉ edgeSide T u v := fun h =>
  (isAcyclic_iff_forall_adj_isBridge.mp hT huv) (mem_edgeSide.mp h)

/-- In a tree, the two sides of an edge partition the vertices. -/
theorem mem_edgeSide_swap (hT : T.IsTree) {u v : V} (huv : T.Adj u v) (x : V) :
    x ∈ edgeSide T v u ↔ x ∉ edgeSide T u v := by
  rw [mem_edgeSide, mem_edgeSide, Sym2.eq_swap]
  have hbr := isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic huv
  rw [isBridge_iff] at hbr
  constructor
  · intro hv hu
    exact hbr (hu.trans hv.symm)
  · intro hu
    -- Every vertex reaches `u` or `v` in `T - uv`.
    have key : ∀ a b (q : T.Walk a b), ((T.deleteEdges {s(u, v)}).Reachable u b ∨
        (T.deleteEdges {s(u, v)}).Reachable v b) →
        ((T.deleteEdges {s(u, v)}).Reachable u a ∨ (T.deleteEdges {s(u, v)}).Reachable v a) := by
      intro a b q
      induction q with
      | nil => exact id
      | @cons a c b hac q ih =>
        intro hb
        by_cases he : s(a, c) = s(u, v)
        · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl (Reachable.refl _)
          · exact Or.inr (Reachable.refl _)
        · have hadj : (T.deleteEdges {s(u, v)}).Adj c a := by
            rw [deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_swap]
            exact ⟨hac.symm, he⟩
          exact (ih hb).imp (fun h => h.trans hadj.reachable) (fun h => h.trans hadj.reachable)
    obtain ⟨q⟩ := hT.connected.preconnected x u
    exact (key x u q (Or.inl (Reachable.refl u))).resolve_left hu

/-- In a tree, the side of `vu` containing `v` is the complement of the side of `uv` containing
`u`. -/
theorem edgeSide_swap [DecidableEq V] (hT : T.IsTree) {u v : V} (huv : T.Adj u v) :
    edgeSide T v u = (edgeSide T u v)ᶜ := by
  ext x
  rw [Finset.mem_compl]
  exact mem_edgeSide_swap hT huv x

/-- Along a path in a forest, the start and the end of the path lie on the two sides of each of
its darts. -/
theorem mem_edgeSide_of_mem_darts (hT : T.IsAcyclic) {s t : V} {p : T.Walk s t}
    (hp : p.IsPath) {d : T.Dart} (hd : d ∈ p.darts) :
    s ∈ edgeSide T d.fst d.snd ∧ t ∉ edgeSide T d.fst d.snd := by
  have hbr := isAcyclic_iff_forall_adj_isBridge.mp hT d.adj
  rw [isBridge_iff] at hbr
  have key : ∀ a b (q : T.Walk a b), q.IsPath → ∀ d ∈ q.darts,
      (T.deleteEdges {s(d.fst, d.snd)}).Reachable d.fst a ∧
        (T.deleteEdges {s(d.fst, d.snd)}).Reachable d.snd b := by
    intro a b q
    induction q with
    | nil => intro _ d hd; simp at hd
    | @cons a a' b haa' q ih =>
      intro hp d hd
      rw [Walk.cons_isPath_iff] at hp
      rw [Walk.darts_cons, List.mem_cons] at hd
      rcases hd with rfl | hd
      · refine ⟨Reachable.refl _, ?_⟩
        rw [reachable_deleteEdges_iff_exists_walk]
        exact ⟨q, fun h => hp.2 (q.fst_mem_support_of_mem_edges h)⟩
      · obtain ⟨h1, h2⟩ := ih hp.1 d hd
        refine ⟨?_, h2⟩
        have hne : s(a, a') ≠ s(d.fst, d.snd) := by
          intro h
          rcases Sym2.eq_iff.mp h with ⟨h', _⟩ | ⟨h', _⟩
          · exact hp.2 (h' ▸ q.dart_fst_mem_support_of_mem_darts hd)
          · exact hp.2 (h' ▸ q.dart_snd_mem_support_of_mem_darts hd)
        have hadj : (T.deleteEdges {s(d.fst, d.snd)}).Adj a' a := by
          rw [deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_swap]
          exact ⟨haa'.symm, hne⟩
        exact h1.trans hadj.reachable
  obtain ⟨h1, h2⟩ := key s t p hp d hd
  exact ⟨mem_edgeSide.mpr h1, fun h => hbr ((mem_edgeSide.mp h).trans h2.symm)⟩

/-- A criterion for the side of a tree edge: if `S` contains `u`, misses `v`, and no other edge of
the tree `T` crosses `S`, then `S` is the side of `uv` containing `u`. -/
theorem edgeSide_eq_of_forall_adj (hT : T.IsTree) {u v : V} (huv : T.Adj u v) {S : Finset V}
    (hu : u ∈ S) (hv : v ∉ S)
    (hS : ∀ ⦃x y : V⦄, T.Adj x y → s(x, y) ≠ s(u, v) → (x ∈ S ↔ y ∈ S)) :
    edgeSide T u v = S := by
  have inv : ∀ a b, (T.deleteEdges {s(u, v)}).Reachable a b → (a ∈ S ↔ b ∈ S) := by
    intro a b h
    rw [reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Iff.rfl
    | tail _ hbc ih =>
      rw [deleteEdges_adj, Set.mem_singleton_iff] at hbc
      exact ih.trans (hS hbc.1 hbc.2)
  ext x
  constructor
  · intro hx
    exact (inv u x (mem_edgeSide.mp hx)).mp hu
  · intro hx
    by_contra hx'
    have h := (mem_edgeSide_swap hT huv x).mpr hx'
    rw [mem_edgeSide, Sym2.eq_swap] at h
    exact hv ((inv v x h).mpr hx)

end SimpleGraph
