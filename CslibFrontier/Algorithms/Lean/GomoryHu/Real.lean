/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.GomoryHu.WeightedCut
public import CslibFrontier.Foundations.Combinatorics.WeightedCut.RealCut

/-!
# Gomory–Hu trees of weighted undirected graphs with real capacities

This module specializes the abstract Gomory-Hu theory to graphs with capacities in a linearly
ordered field, proving cut-equivalence and flow-equivalence.

## Main results

* `Cslib.WeightedCut.isMinCutBetween_cutWeight_iff_minRealCutBetween`: minimum cuts are the sets
  attaining `minRealCutBetween`.
* `Cslib.Algorithms.Lean.GomoryHu.exists_isGomoryHuTree_cutWeight_of_symm`: the Gomory–Hu theorem
  for symmetric non-negative weights in a linearly ordered field.
* `Cslib.Algorithms.Lean.GomoryHu.IsGomoryHuTree.isLeast_minRealCutBetween`: flow-equivalence.
* `Cslib.Algorithms.Lean.GomoryHu.card_image_minRealCutBetween_le`: at most
  `|V| - 1` distinct values.
-/

public section

namespace Cslib.WeightedCut

open Cslib.Algorithms.Lean.Submodular Cslib.Algorithms.Lean.GomoryHu

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Field K]
  [LinearOrder K] [IsStrictOrderedRing K]

omit [IsStrictOrderedRing K] in
/-- The minimum `s`–`t` cuts of the cut function are the sets containing `s` and missing `t`
whose weight is `λ(s, t)`. -/
theorem isMinCutBetween_cutWeight_iff_minRealCutBetween (W : V → V → K) {s t : V} {X : Finset V} :
    IsMinCutBetween (cutWeight W) s t X ↔
      s ∈ X ∧ t ∉ X ∧ cutWeight W X = minRealCutBetween W s t := by
  constructor
  · intro h
    refine ⟨h.left_mem, h.right_notMem, ?_⟩
    apply le_antisymm
    · by_cases hst : s = t
      · rcases hst with rfl
        exact (h.right_notMem h.left_mem).elim
      · obtain ⟨Y, hs, ht, hY⟩ := exists_cutWeight_eq_minRealCutBetween W hst
        rw [← hY]
        exact h.le hs ht
    · exact minRealCutBetween_le_cutWeight W h.left_mem h.right_notMem
  · rintro ⟨hs, ht, hX⟩
    refine ⟨hs, ht, fun Y hsY htY => ?_⟩
    rw [hX]
    exact minRealCutBetween_le_cutWeight W hsY htY

end Cslib.WeightedCut

namespace Cslib.Algorithms.Lean.GomoryHu

open Cslib.WeightedCut
open SimpleGraph (edgeSide mem_edgeSide_of_mem_darts)

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Field K]
  [LinearOrder K] [IsStrictOrderedRing K]

/-- **Gomory–Hu theorem** ([GomoryHu1961]; [Schrijver2003], Section 15.4): every weighted
multigraph `W` on a nonempty finite vertex set has a cut-equivalent tree, a spanning tree `T` on
the vertices in which for every edge `uv`, the side of `T - uv` containing `u` is a minimum `u`–`v`
cut of `W`. The edges of `T` need not be edges of `W`. -/
theorem exists_isGomoryHuTree_cutWeight_of_symm [Nonempty V] {W : V → V → K}
    (hWs : ∀ u v, W u v = W v u)
    (hWn : ∀ u v, 0 ≤ W u v) :
    ∃ T : SimpleGraph V, IsGomoryHuTree (cutWeight W) T :=
  exists_isGomoryHuTree (cutWeight_compl_of_symm hWs) (isSubmodular_cutWeight_of_nonneg W hWn)

omit [IsStrictOrderedRing K] in
/-- **Flow-equivalence of a Gomory–Hu tree** ([GomoryHu1961]): with each tree edge `uv` weighted
by `λ(u, v)`, the minimum `s`–`t` cut weight `λ(s, t)` is the least weight of an edge on the
`s`–`t` path of the tree. -/
theorem IsGomoryHuTree.isLeast_minRealCutBetween {W : V → V → K} {T : SimpleGraph V}
    (hT : IsGomoryHuTree (cutWeight W) T) {s t : V} (hst : s ≠ t) {p : T.Walk s t}
    (hp : p.IsPath) :
    IsLeast ((fun d : T.Dart => minRealCutBetween W d.fst d.snd) '' {d | d ∈ p.darts})
      (minRealCutBetween W s t) := by
  have hside : ∀ d : T.Dart, cutWeight W (edgeSide T d.fst d.snd) =
      minRealCutBetween W d.fst d.snd :=
    fun d => ((isMinCutBetween_cutWeight_iff_minRealCutBetween W).mp
      (hT.isMinCutBetween_edgeSide d.adj)).2.2
  constructor
  · obtain ⟨d, hd, hmin⟩ := hT.exists_isMinCutBetween_of_isPath hst hp
    exact ⟨d, hd,
      (hside d).symm.trans ((isMinCutBetween_cutWeight_iff_minRealCutBetween W).mp hmin).2.2⟩
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨hs, ht⟩ := mem_edgeSide_of_mem_darts hT.isTree.isAcyclic hp hd
    exact (minRealCutBetween_le_cutWeight W hs ht).trans_eq (hside d)

/-- An undirected weighted graph on `n` vertices has at most `n - 1` distinct minimum cut values
`λ(s, t)` over pairs of distinct vertices ([GomoryHu1961]). -/
theorem card_image_minRealCutBetween_le {W : V → V → K} (hWs : ∀ u v, W u v = W v u)
    (hWn : ∀ u v, 0 ≤ W u v) :
    ((Finset.univ.offDiag : Finset (V × V)).image fun p => minRealCutBetween W p.1 p.2).card ≤
      Fintype.card V - 1 := by
  classical
  rcases isEmpty_or_nonempty V with hV | hV
  · simp
  obtain ⟨T, hT⟩ := exists_isGomoryHuTree_cutWeight_of_symm hWs hWn
  let g : Sym2 V → K := Sym2.lift ⟨fun a b => minRealCutBetween W a b,
    fun a b => minRealCutBetween_comm hWs a b⟩
  have hsub : ((Finset.univ.offDiag : Finset (V × V)).image fun p => minRealCutBetween W p.1 p.2) ⊆
      T.edgeFinset.image g := by
    intro k hk
    obtain ⟨⟨s, t⟩, hst, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨p, hp⟩ := (hT.isTree.connected.preconnected s t).exists_isPath
    obtain ⟨⟨d, hd, hdeq⟩, -⟩ := hT.isLeast_minRealCutBetween (Finset.mem_offDiag.mp hst).2.2 hp
    exact Finset.mem_image.mpr ⟨d.edge, SimpleGraph.mem_edgeFinset.mpr d.edge_mem, hdeq⟩
  have hcard := hT.isTree.card_edgeFinset
  calc _ ≤ (T.edgeFinset.image g).card := Finset.card_le_card hsub
    _ ≤ T.edgeFinset.card := Finset.card_image_le
    _ = Fintype.card V - 1 := by
      omega


end Cslib.Algorithms.Lean.GomoryHu
