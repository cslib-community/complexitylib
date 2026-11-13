/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.GomoryHu.Existence
public import CslibFrontier.Algorithms.Lean.MaxFlow.Basic
public import CslibFrontier.Foundations.Combinatorics.WeightedCut.MinCutBetween

/-!
# Gomory–Hu trees of weighted undirected graphs

For a weighted multigraph `W : V → V → ℕ` (`Cslib.WeightedCut.IsMultigraph`: symmetric weights,
zero diagonal), the cut function `X ↦ cutWeight W X` is symmetric and submodular, so it has a
Gomory–Hu tree (`Cslib.Algorithms.Lean.GomoryHu.exists_isGomoryHuTree`). This module specializes
the abstract theory to graphs ([GomoryHu1961]; [Schrijver2003], Section 15.4):

* the Gomory–Hu tree is **cut-equivalent**: for each tree edge `uv`, the side of `T - uv`
  containing `u` is a minimum `u`–`v` cut of the graph;
* it is **flow-equivalent**: weighting each tree edge `uv` by `λ(u, v)`, the minimum `s`–`t` cut
  weight `λ(s, t)` (`Cslib.WeightedCut.minCutBetween`) is the least weight of an edge on the `s`–`t`
  path of the tree;
* consequently, the values `λ(s, t)` over all pairs `s ≠ t` take at most `|V| - 1` distinct
  values.

By max-flow min-cut (`Cslib.Algorithms.Lean.MaxFlow.Network.exists_maxFlow_eq_minCut`), `λ(s, t)`
is the value of a maximum `s`–`t` flow in the network with capacities `W`
(`Cslib.Algorithms.Lean.MaxFlow.Network.Flow.IsMaxFlow.value_eq_minCutBetween`), so the Gomory–Hu
tree also encodes all pairwise maximum flow values.

The results are existence statements for natural-number weights. Gusfield's construction of the
tree with `|V| - 1` maximum flow computations, without the contractions of Gomory and Hu
([Gusfield1990]), is in `CslibFrontier.Algorithms.Lean.GomoryHu.Gusfield` (abstract cut oracle) and
`CslibFrontier.Algorithms.Lean.GomoryHu.Construction` (Edmonds–Karp, with running time).

## Main results

* `Cslib.WeightedCut.isSubmodular_cutWeight`: the cut function is submodular.
* `Cslib.WeightedCut.isMinCutBetween_cutWeight_iff`: minimum `s`–`t` cuts of the cut function are
  the sets containing `s`, missing `t`, of weight `λ(s, t)`.
* `Cslib.Algorithms.Lean.GomoryHu.exists_isGomoryHuTree_cutWeight`: the **Gomory–Hu theorem**: every
  weighted multigraph on a nonempty finite vertex set has a cut-equivalent tree.
* `Cslib.Algorithms.Lean.GomoryHu.IsGomoryHuTree.isLeast_minCutBetween`: flow-equivalence of a
  Gomory–Hu tree.
* `Cslib.Algorithms.Lean.GomoryHu.card_image_minCutBetween_le`: at most `|V| - 1` distinct minimum
  cut values.
* `Cslib.Algorithms.Lean.MaxFlow.Network.Flow.IsMaxFlow.value_eq_minCutBetween`: a maximum `s`–`t`
  flow has value `λ(s, t)`.

## References

* [GomoryHu1961]
* [Gusfield1990]
* [Schrijver2003]
-/

public section

namespace Cslib.WeightedCut

open Cslib.Algorithms.Lean.Submodular Cslib.Algorithms.Lean.GomoryHu

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The cut function of a non-negative weight matrix over an ordered additive monoid is
submodular. -/
theorem isSubmodular_cutWeight_of_nonneg {M : Type*} [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] (W : V → V → M) (hW : ∀ u v, 0 ≤ W u v) : IsSubmodular (cutWeight W) :=
  cutWeight_union_add_cutWeight_inter_le_of_nonneg W hW

/-- The cut function of a weight matrix is submodular. -/
theorem isSubmodular_cutWeight (W : V → V → ℕ) : IsSubmodular (cutWeight W) :=
  isSubmodular_cutWeight_of_nonneg W fun _ _ => Nat.zero_le _

/-- The minimum `s`–`t` cuts of the cut function are the sets containing `s` and missing `t`
whose weight is `λ(s, t)`. -/
theorem isMinCutBetween_cutWeight_iff (W : V → V → ℕ) {s t : V} {X : Finset V} :
    IsMinCutBetween (cutWeight W) s t X ↔
      s ∈ X ∧ t ∉ X ∧ cutWeight W X = minCutBetween W s t := by
  constructor
  · intro h
    exact ⟨h.left_mem, h.right_notMem,
      (cutWeight_eq_minCutBetween_iff W h.left_mem h.right_notMem).mpr fun _ => h.le⟩
  · rintro ⟨hs, ht, hX⟩
    exact ⟨hs, ht, (cutWeight_eq_minCutBetween_iff W hs ht).mp hX⟩

end Cslib.WeightedCut

namespace Cslib.Algorithms.Lean.GomoryHu

open Cslib.WeightedCut
open SimpleGraph (edgeSide mem_edgeSide_of_mem_darts)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Gomory–Hu theorem** ([GomoryHu1961]; [Schrijver2003], Section 15.4): every weighted
multigraph `W` on a nonempty finite vertex set has a cut-equivalent tree, a spanning tree `T` on
the vertices in which for every edge `uv`, the side of `T - uv` containing `u` is a minimum `u`–`v`
cut of `W`. The edges of `T` need not be edges of `W`. -/
theorem exists_isGomoryHuTree_cutWeight [Nonempty V] {W : V → V → ℕ} (hW : IsMultigraph W) :
    ∃ T : SimpleGraph V, IsGomoryHuTree (cutWeight W) T :=
  exists_isGomoryHuTree (cutWeight_compl' hW) (isSubmodular_cutWeight W)

/-- **Flow-equivalence of a Gomory–Hu tree** ([GomoryHu1961]): with each tree edge `uv` weighted
by `λ(u, v)`, the minimum `s`–`t` cut weight `λ(s, t)` is the least weight of an edge on the
`s`–`t` path of the tree. -/
theorem IsGomoryHuTree.isLeast_minCutBetween {W : V → V → ℕ} {T : SimpleGraph V}
    (hT : IsGomoryHuTree (cutWeight W) T) {s t : V} (hst : s ≠ t) {p : T.Walk s t}
    (hp : p.IsPath) :
    IsLeast ((fun d : T.Dart => minCutBetween W d.fst d.snd) '' {d | d ∈ p.darts})
      (minCutBetween W s t) := by
  have hside : ∀ d : T.Dart, cutWeight W (edgeSide T d.fst d.snd) = minCutBetween W d.fst d.snd :=
    fun d => ((isMinCutBetween_cutWeight_iff W).mp (hT.isMinCutBetween_edgeSide d.adj)).2.2
  constructor
  · obtain ⟨d, hd, hmin⟩ := hT.exists_isMinCutBetween_of_isPath hst hp
    exact ⟨d, hd, (hside d).symm.trans ((isMinCutBetween_cutWeight_iff W).mp hmin).2.2⟩
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨hs, ht⟩ := mem_edgeSide_of_mem_darts hT.isTree.isAcyclic hp hd
    exact (minCutBetween_le_cutWeight W hs ht).trans_eq (hside d)

/-- An undirected weighted graph on `n` vertices has at most `n - 1` distinct minimum cut values
`λ(s, t)` over pairs of distinct vertices ([GomoryHu1961]). -/
theorem card_image_minCutBetween_le {W : V → V → ℕ} (hW : IsMultigraph W) :
    ((Finset.univ.offDiag : Finset (V × V)).image fun p => minCutBetween W p.1 p.2).card ≤
      Fintype.card V - 1 := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  obtain ⟨T, hT⟩ := exists_isGomoryHuTree_cutWeight hW
  let g : Sym2 V → ℕ := Sym2.lift ⟨fun a b => minCutBetween W a b,
    fun a b => minCutBetween_comm hW a b⟩
  have hsub : ((Finset.univ.offDiag : Finset (V × V)).image fun p => minCutBetween W p.1 p.2) ⊆
      T.edgeFinset.image g := by
    intro k hk
    obtain ⟨⟨s, t⟩, hst, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨p, hp⟩ := (hT.isTree.connected.preconnected s t).exists_isPath
    obtain ⟨⟨d, hd, hdeq⟩, -⟩ := hT.isLeast_minCutBetween (Finset.mem_offDiag.mp hst).2.2 hp
    exact Finset.mem_image.mpr ⟨d.edge, SimpleGraph.mem_edgeFinset.mpr d.edge_mem, hdeq⟩
  have hcard := hT.isTree.card_edgeFinset
  calc _ ≤ (T.edgeFinset.image g).card := Finset.card_le_card hsub
    _ ≤ T.edgeFinset.card := Finset.card_image_le
    _ = Fintype.card V - 1 := by omega

end Cslib.Algorithms.Lean.GomoryHu

namespace Cslib.Algorithms.Lean.MaxFlow

open Cslib.WeightedCut Cslib.Algorithms.Lean.GomoryHu

/-- A minimum cut of the network with capacities `W`, source `s` and sink `t` is a minimum `s`–`t`
cut of the cut function of `W`. -/
theorem Network.IsMinCut.isMinCutBetween {V : Type*} [Fintype V] [DecidableEq V]
    {W : V → V → ℕ} {s t : V} {S : Finset V} (hS : (Network.mk W s t).IsMinCut S) :
    IsMinCutBetween (cutWeight W) s t S :=
  ⟨hS.1.1, hS.1.2, fun Y hs ht => hS.2 Y ⟨hs, ht⟩⟩

/-- **Max-flow min-cut for `λ`.** In the network with capacities `W`, source `s` and sink `t ≠ s`,
a maximum flow has value `λ(s, t)`, the minimum `s`–`t` cut weight of `W`. -/
theorem Network.Flow.IsMaxFlow.value_eq_minCutBetween {V : Type*} [Fintype V] [DecidableEq V]
    {W : V → V → ℕ} {s t : V} (hst : s ≠ t) {f : (Network.mk W s t).Flow} (hf : f.IsMaxFlow) :
    f.value = (minCutBetween W s t : ℤ) := by
  obtain ⟨g, S, hg, hS, hval⟩ := Network.exists_maxFlow_eq_minCut (Network.mk W s t) hst
  rw [le_antisymm (hg f) (hf g), hval]
  congr 1
  exact ((isMinCutBetween_cutWeight_iff W).mp hS.isMinCutBetween).2.2

end Cslib.Algorithms.Lean.MaxFlow
