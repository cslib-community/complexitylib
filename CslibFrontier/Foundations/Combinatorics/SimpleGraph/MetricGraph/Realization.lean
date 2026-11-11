/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Realization.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Subdivision
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Maps
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith

/-!
# Euclidean straight-edge realizations of metric graphs

This module constructs an isometric straight-edge realization of any finite connected metric graph
in `EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1))` after subdividing each edge into three
sub-segments. When all original edge weights are rational, every subdivided vertex has rational
coordinates.

## Main definitions

* `SimpleGraph.MetricGraph.realizationPoints`: the finite set of vertices together with two interior
  subdivision points on each original edge, dividing every edge into three sub-segments.
* `SimpleGraph.MetricGraph.realizationSubdivision`: the three-segment subdivision of `W`.
* `SimpleGraph.MetricGraph.realizationMap`: the straight-edge map from
  `MetricGraph (realizationSubdivision W)` into
  `EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1))`.
* `SimpleGraph.MetricGraph.realizationFromGraph`: the composed map from `MetricGraph W` into
  `EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1))`.
* `SimpleGraph.MetricGraph.realizationEuclideanGraph`: the weighted graph on `realizationPoints W`
  whose weights are the Euclidean distances between endpoints of `realizationMap`.

## Main results

* `SimpleGraph.MetricGraph.realizationMap_vertex`,
  `SimpleGraph.MetricGraph.realizationMap_edgePoint`:
  `realizationMap` maps every subdivided edge affinely onto the Euclidean straight line segment
  between its endpoints.
* `SimpleGraph.MetricGraph.realizationMap_edge_dist`,
  `SimpleGraph.MetricGraph.realizationMap_edgePoint_dist`: each subdivided edge is mapped
  isometrically onto its Euclidean segment.
* `SimpleGraph.MetricGraph.realizationMap_isClosedEmbedding`,
  `SimpleGraph.MetricGraph.realizationFromGraph_isClosedEmbedding`: closed topological embeddings
  into Euclidean space.
* `SimpleGraph.MetricGraph.realizationEuclideanEquiv`: isometric equivalence between
  `MetricGraph (realizationEuclideanGraph W)` and `MetricGraph W`.
* `SimpleGraph.MetricGraph.realizationMap_vertex_rational`: rational weights give rational vertex
  coordinates.

## References

* STOC 2027 submission 1056, Appendix C, Lemma C.2 (locator from Issue #4324 context; primary
  manuscript not inspected here).
-/

public section

open scoped unitInterval

namespace SimpleGraph

namespace MetricGraph

universe u

variable {V : Type u}

/-! ### Three-segment geometry and Euclidean vertex coordinates -/

open Classical in
private noncomputable def vertexEquiv [Finite V] : V ≃ Fin (Nat.card V) :=
  let : Fintype V := Fintype.ofFinite V
  Fintype.equivFinOfCardEq Fintype.card_eq_nat_card

open Classical in
private noncomputable def edgeEquiv [Finite V] (W : WeightedGraph V) :
    W.graph.edgeSet ≃ Fin (Nat.card W.graph.edgeSet) :=
  let : Fintype W.graph.edgeSet := Fintype.ofFinite _
  Fintype.equivFinOfCardEq Fintype.card_eq_nat_card

private noncomputable def minEdgeWeight [Finite V] (W : WeightedGraph V) : ℝ :=
  if h : 0 < Nat.card W.graph.edgeSet then
    ((Finset.univ : Finset (Fin (Nat.card W.graph.edgeSet))).image
      fun k => W.weight ((edgeEquiv W).symm k).1).min'
      (Finset.Nonempty.image ⟨⟨0, h⟩, Finset.mem_univ _⟩ _)
  else 1

private theorem exists_minEdgeWeight_eq_weight [Finite V] (W : WeightedGraph V)
    (hpos : 0 < Nat.card W.graph.edgeSet) :
    ∃ e : W.graph.edgeSet, minEdgeWeight W = W.weight e.1 := by
  dsimp only [minEdgeWeight]
  split_ifs
  have hmem : ((Finset.univ : Finset (Fin (Nat.card W.graph.edgeSet))).image
      fun k => W.weight ((edgeEquiv W).symm k).1).min'
      (Finset.Nonempty.image ⟨⟨0, hpos⟩, Finset.mem_univ _⟩ _) ∈
      (Finset.univ : Finset (Fin (Nat.card W.graph.edgeSet))).image
        fun k => W.weight ((edgeEquiv W).symm k).1 := Finset.min'_mem _ _
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hmem
  exact ⟨(edgeEquiv W).symm k, hk.symm⟩

private theorem minEdgeWeight_pos [Finite V] (W : WeightedGraph V) : 0 < minEdgeWeight W := by
  by_cases h : 0 < Nat.card W.graph.edgeSet
  · obtain ⟨e, he⟩ := exists_minEdgeWeight_eq_weight W h
    rw [he]
    simpa only [edgeDartOfSym2_edge] using W.dart_weight_pos (edgeDartOfSym2 e)
  · dsimp only [minEdgeWeight]
    split_ifs
    exact one_pos

private theorem minEdgeWeight_le [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    minEdgeWeight W ≤ W.weight e.1 := by
  classical
  dsimp only [minEdgeWeight]
  have hpos : 0 < Nat.card W.graph.edgeSet := Nat.card_pos_iff.mpr ⟨⟨e⟩, inferInstance⟩
  split_ifs
  refine Finset.min'_le _ _ (Finset.mem_image.mpr ⟨edgeEquiv W e, Finset.mem_univ _, ?_⟩)
  rw [Equiv.symm_apply_apply]

private theorem minEdgeWeight_rational [Finite V] (W : WeightedGraph V)
    (hQ : ∀ e ∈ W.graph.edgeSet, ∃ q : ℚ, W.weight e = q) :
    ∃ q : ℚ, minEdgeWeight W = q := by
  by_cases h : 0 < Nat.card W.graph.edgeSet
  · obtain ⟨e, he⟩ := exists_minEdgeWeight_eq_weight W h
    rw [he]
    exact hQ e.1 e.2
  · dsimp only [minEdgeWeight]
    split_ifs
    exact ⟨1, by norm_num⟩

private noncomputable def vertexSpacing [Finite V] (W : WeightedGraph V) : ℝ :=
  minEdgeWeight W / (2 * ((Nat.card V : ℝ) + 1))

private theorem vertexSpacing_pos [Finite V] (W : WeightedGraph V) : 0 < vertexSpacing W :=
  div_pos (minEdgeWeight_pos W) (by positivity)

private theorem vertexSpacing_rational [Finite V] (W : WeightedGraph V)
    (hQ : ∀ e ∈ W.graph.edgeSet, ∃ q : ℚ, W.weight e = q) :
    ∃ q : ℚ, vertexSpacing W = q := by
  obtain ⟨q, hq⟩ := minEdgeWeight_rational W hQ
  refine ⟨q / (2 * (Nat.card V + 1 : ℚ)), ?_⟩
  dsimp only [vertexSpacing]
  rw [hq]
  push_cast
  rfl

private noncomputable def vertexPos [Finite V] (W : WeightedGraph V) (v : V) :
    EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1)) :=
  (vertexSpacing W * ((vertexEquiv v : ℕ) : ℝ)) • EuclideanSpace.single 0 (1 : ℝ)

private theorem vertexPos_apply_zero [Finite V] (W : WeightedGraph V) (v : V) :
    vertexPos W v 0 = vertexSpacing W * ((vertexEquiv v : ℕ) : ℝ) := by
  rw [vertexPos, PiLp.smul_apply, PiLp.single_eq_same, smul_eq_mul, mul_one]

private theorem vertexPos_apply_succ [Finite V] (W : WeightedGraph V) (v : V)
    (k : Fin (Nat.card W.graph.edgeSet)) :
    vertexPos W v k.succ = 0 := by
  rw [vertexPos, PiLp.smul_apply, PiLp.single_eq_of_ne 2 k.succ_ne_zero, smul_zero]

private theorem dist_vertexPos_eq [Finite V] (W : WeightedGraph V) (u v : V) :
    dist (vertexPos W u) (vertexPos W v) =
      vertexSpacing W * |((vertexEquiv u : ℕ) : ℝ) - (vertexEquiv v : ℕ)| := by
  rw [PiLp.dist_eq_of_L2, Fin.sum_univ_succ]
  have hrest : ∑ k : Fin (Nat.card W.graph.edgeSet),
      dist (vertexPos W u k.succ) (vertexPos W v k.succ) ^ 2 = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [vertexPos_apply_succ, vertexPos_apply_succ, dist_self, zero_pow two_ne_zero]
  rw [hrest, add_zero, Real.sqrt_sq dist_nonneg, Real.dist_eq, vertexPos_apply_zero,
    vertexPos_apply_zero, ← mul_sub, abs_mul, abs_of_pos (vertexSpacing_pos W)]

private theorem dist_vertexPos_pos [Finite V] (W : WeightedGraph V) {u v : V} (hne : u ≠ v) :
    0 < dist (vertexPos W u) (vertexPos W v) := by
  rw [dist_vertexPos_eq]
  refine mul_pos (vertexSpacing_pos W) (abs_pos.mpr (sub_ne_zero.mpr ?_))
  intro heq
  exact hne (vertexEquiv.injective (Fin.ext (by exact_mod_cast heq)))

private theorem dist_vertexPos_lt_weight [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) :
    dist (vertexPos W (edgeDartOfSym2 e).fst) (vertexPos W (edgeDartOfSym2 e).snd) <
      W.weight e.1 := by
  rw [dist_vertexPos_eq]
  have hu : (vertexEquiv (edgeDartOfSym2 e).fst : ℕ) < Nat.card V := Fin.isLt _
  have hv : (vertexEquiv (edgeDartOfSym2 e).snd : ℕ) < Nat.card V := Fin.isLt _
  have habs : |((vertexEquiv (edgeDartOfSym2 e).fst : ℕ) : ℝ) -
      (vertexEquiv (edgeDartOfSym2 e).snd : ℕ)| < (Nat.card V : ℝ) + 1 := by
    rw [abs_lt]
    constructor <;> linarith [show ((vertexEquiv (edgeDartOfSym2 e).fst : ℕ) : ℝ) < Nat.card V
      from by exact_mod_cast hu,
      show ((vertexEquiv (edgeDartOfSym2 e).snd : ℕ) : ℝ) < Nat.card V
      from by exact_mod_cast hv,
      Nat.cast_nonneg (α := ℝ) (vertexEquiv (edgeDartOfSym2 e).fst : ℕ),
      Nat.cast_nonneg (α := ℝ) (vertexEquiv (edgeDartOfSym2 e).snd : ℕ)]
  have hsp : vertexSpacing W * |((vertexEquiv (edgeDartOfSym2 e).fst : ℕ) : ℝ) -
      (vertexEquiv (edgeDartOfSym2 e).snd : ℕ)| < minEdgeWeight W / 2 := by
    have hlt := mul_lt_mul_of_pos_left habs (vertexSpacing_pos W)
    refine hlt.trans_eq ?_
    dsimp only [vertexSpacing]
    have hpos : (Nat.card V : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hle : minEdgeWeight W / 2 < W.weight e.1 := by
    linarith [minEdgeWeight_pos W, minEdgeWeight_le W e]
  exact hsp.trans hle

private noncomputable def edgeChordDist [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) : ℝ :=
  dist (vertexPos W (edgeDartOfSym2 e).fst) (vertexPos W (edgeDartOfSym2 e).snd)

private theorem edgeChordDist_pos [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    0 < edgeChordDist W e :=
  dist_vertexPos_pos W (edgeDartOfSym2 e).fst_ne_snd

private theorem edgeChordDist_lt_weight [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    edgeChordDist W e < W.weight e.1 :=
  dist_vertexPos_lt_weight W e

private noncomputable def edgeLegHeight [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) : ℝ :=
  (W.weight e.1 - edgeChordDist W e) / 2

private theorem edgeLegHeight_pos [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    0 < edgeLegHeight W e := by
  dsimp only [edgeLegHeight]
  linarith [edgeChordDist_lt_weight W e]

private theorem two_mul_legHeight_add_chord [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) :
    2 * edgeLegHeight W e + edgeChordDist W e = W.weight e.1 := by
  dsimp only [edgeLegHeight]
  ring

private noncomputable def ratio1 [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    unitInterval :=
  ⟨edgeLegHeight W e / W.weight e.1,
    div_nonneg (edgeLegHeight_pos W e).le
      (by simpa only [edgeDartOfSym2_edge] using (W.dart_weight_pos (edgeDartOfSym2 e)).le),
    by
      have hw : 0 < W.weight e.1 := by
        simpa only [edgeDartOfSym2_edge] using W.dart_weight_pos (edgeDartOfSym2 e)
      rw [div_le_one hw]
      linarith [edgeLegHeight_pos W e, edgeChordDist_pos W e, two_mul_legHeight_add_chord W e]⟩

private noncomputable def ratio2 [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    unitInterval :=
  ⟨(edgeLegHeight W e + edgeChordDist W e) / W.weight e.1,
    div_nonneg (add_pos (edgeLegHeight_pos W e) (edgeChordDist_pos W e)).le
      (by simpa only [edgeDartOfSym2_edge] using (W.dart_weight_pos (edgeDartOfSym2 e)).le),
    by
      have hw : 0 < W.weight e.1 := by
        simpa only [edgeDartOfSym2_edge] using W.dart_weight_pos (edgeDartOfSym2 e)
      rw [div_le_one hw]
      linarith [edgeLegHeight_pos W e, two_mul_legHeight_add_chord W e]⟩

private theorem ratio1_pos [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    (0 : ℝ) < ratio1 W e := by
  have hw : 0 < W.weight e.1 := by
    simpa only [edgeDartOfSym2_edge] using W.dart_weight_pos (edgeDartOfSym2 e)
  exact div_pos (edgeLegHeight_pos W e) hw

private theorem ratio1_lt_ratio2 [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    (ratio1 W e : ℝ) < ratio2 W e := by
  have hw : 0 < W.weight e.1 := by
    simpa only [edgeDartOfSym2_edge] using W.dart_weight_pos (edgeDartOfSym2 e)
  exact div_lt_div_of_pos_right (by linarith [edgeChordDist_pos W e]) hw

private theorem ratio2_lt_one [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    (ratio2 W e : ℝ) < 1 := by
  have hw : 0 < W.weight e.1 := by
    simpa only [edgeDartOfSym2_edge] using W.dart_weight_pos (edgeDartOfSym2 e)
  rw [show (ratio2 W e : ℝ) = (edgeLegHeight W e + edgeChordDist W e) / W.weight e.1 from rfl,
    div_lt_one hw]
  linarith [edgeLegHeight_pos W e, two_mul_legHeight_add_chord W e]

private noncomputable def bp1 [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    MetricGraph W :=
  edgePoint (edgeDartOfSym2 e) (ratio1 W e)

private noncomputable def bp2 [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    MetricGraph W :=
  edgePoint (edgeDartOfSym2 e) (ratio2 W e)

/-! ### Three-segment subdivision of `W` -/

open Classical in
/-- The finite set of original vertices together with two interior subdivision points per edge
(splitting every edge into three sub-segments). -/
noncomputable def realizationPoints [Finite V] (W : WeightedGraph V) :
    Finset (MetricGraph W) :=
  let : Fintype V := Fintype.ofFinite V
  let : Fintype W.graph.edgeSet := Fintype.ofFinite _
  Finset.univ.image vertex ∪
    Finset.univ.image (bp1 W) ∪
    Finset.univ.image (bp2 W)

theorem vertex_mem_realizationPoints [Finite V] (W : WeightedGraph V) (v : V) :
    vertex v ∈ realizationPoints W := by
  classical
  simp only [realizationPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl ⟨v, rfl⟩)

private theorem bp1_mem_realizationPoints [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) : bp1 W e ∈ realizationPoints W := by
  classical
  simp only [realizationPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨e, rfl⟩)

private theorem bp2_mem_realizationPoints [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) : bp2 W e ∈ realizationPoints W := by
  classical
  simp only [realizationPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨e, rfl⟩

open Classical in
theorem realizationPoints_sdiff_card_le [Finite V] (W : WeightedGraph V) :
    let : Fintype V := Fintype.ofFinite V
    (realizationPoints W \ Finset.univ.image vertex).card ≤
      2 * Nat.card W.graph.edgeSet := by
  intro _
  let : Fintype W.graph.edgeSet := Fintype.ofFinite _
  refine (Finset.card_le_card (t := Finset.univ.image (bp1 W) ∪ Finset.univ.image (bp2 W))
    ?_).trans ?_
  · intro q hq
    simp only [Finset.mem_sdiff, realizationPoints, Finset.mem_union] at hq
    rcases hq.1 with (h1 | h1) | h2
    · exact absurd h1 hq.2
    · exact Finset.mem_union_left _ h1
    · exact Finset.mem_union_right _ h2
  · refine Finset.card_union_le _ _ |>.trans ?_
    have h1 : (Finset.univ.image (bp1 W)).card ≤ Nat.card W.graph.edgeSet := by
      rw [← Fintype.card_eq_nat_card, ← Finset.card_univ]
      exact Finset.card_image_le
    have h2 : (Finset.univ.image (bp2 W)).card ≤ Nat.card W.graph.edgeSet := by
      rw [← Fintype.card_eq_nat_card, ← Finset.card_univ]
      exact Finset.card_image_le
    omega

/-- The three-segment subdivision of `W` used for the Euclidean straight-edge realization. -/
noncomputable def realizationSubdivision [Finite V] (W : WeightedGraph V) :
    WeightedGraph { z : MetricGraph W // z ∈ realizationPoints W } :=
  subdivide W (realizationPoints W) (vertex_mem_realizationPoints W)

private theorem ratio1_lt_one [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    (ratio1 W e : ℝ) < 1 :=
  (ratio1_lt_ratio2 W e).trans (ratio2_lt_one W e)

private theorem ratio2_pos [Finite V] (W : WeightedGraph V) (e : W.graph.edgeSet) :
    (0 : ℝ) < ratio2 W e :=
  (ratio1_pos W e).trans (ratio1_lt_ratio2 W e)

private theorem edgePoint_interior_ne_vertex (W : WeightedGraph V)
    {r : W.graph.edgeSet → unitInterval} (hr0 : ∀ e, (0 : ℝ) < r e) (hr1 : ∀ e, (r e : ℝ) < 1)
    (e : W.graph.edgeSet) (v : V) : edgePoint (edgeDartOfSym2 e) (r e) ≠ vertex v := by
  intro h
  rcases edgePoint_eq_vertex_iff.mp h with ⟨h0, _⟩ | ⟨h1, _⟩
  · exact (hr0 e).ne' (congrArg Subtype.val h0)
  · exact (hr1 e).ne (congrArg Subtype.val h1)

private theorem bp1_ne_bp2 [Finite V] (W : WeightedGraph V) (e₁ e₂ : W.graph.edgeSet) :
    bp1 W e₁ ≠ bp2 W e₂ := by
  intro h
  rcases edgePoint_eq_edgePoint_iff.mp h with
    ⟨h0, _⟩ | ⟨h1, _⟩ | ⟨_, _, _, _, ⟨heq, hreq⟩ | ⟨hsym, _⟩⟩
  · exact (ratio1_pos W e₁).ne' (congrArg Subtype.val h0)
  · exact (ratio1_lt_one W e₁).ne (congrArg Subtype.val h1)
  · have h' := congrArg Dart.edge heq
    rw [edgeDartOfSym2_edge, edgeDartOfSym2_edge] at h'
    have he : e₁ = e₂ := Subtype.ext h'
    subst he
    exact (ratio1_lt_ratio2 W e₁).ne (congrArg Subtype.val hreq)
  · have h' := congrArg Dart.edge hsym
    rw [edgeDartOfSym2_edge, Dart.edge_symm, edgeDartOfSym2_edge] at h'
    have he : e₁ = e₂ := Subtype.ext h'
    subst he
    exact (edgeDartOfSym2 e₁).symm_ne hsym.symm

private theorem edgePoint_interior_injective (W : WeightedGraph V)
    {r : W.graph.edgeSet → unitInterval} (hr0 : ∀ e, (0 : ℝ) < r e) (hr1 : ∀ e, (r e : ℝ) < 1) :
    Function.Injective (fun e : W.graph.edgeSet => edgePoint (edgeDartOfSym2 e) (r e)) := by
  intro e₁ e₂ h
  rcases edgePoint_eq_edgePoint_iff.mp h with
    ⟨h0, _⟩ | ⟨h1, _⟩ | ⟨_, _, _, _, ⟨heq, _⟩ | ⟨hsym, _⟩⟩
  · exact absurd (congrArg Subtype.val h0) (hr0 e₁).ne'
  · exact absurd (congrArg Subtype.val h1) (hr1 e₁).ne
  · have h' := congrArg Dart.edge heq
    rw [edgeDartOfSym2_edge, edgeDartOfSym2_edge] at h'
    exact Subtype.ext h'
  · have h' := congrArg Dart.edge hsym
    rw [edgeDartOfSym2_edge, Dart.edge_symm, edgeDartOfSym2_edge] at h'
    have he : e₁ = e₂ := Subtype.ext h'
    subst he
    exact absurd hsym.symm (edgeDartOfSym2 e₁).symm_ne

private theorem mem_realizationPoints_on_dart_iff [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) (u : unitInterval) :
    edgePoint (edgeDartOfSym2 e) u ∈ realizationPoints W ↔
      u = 0 ∨ u = ratio1 W e ∨ u = ratio2 W e ∨ u = 1 := by
  constructor
  · intro hu
    classical
    simp only [realizationPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hu
    rcases hu with (⟨v, hv⟩ | ⟨e', he'⟩) | ⟨e', he'⟩
    · rcases edgePoint_eq_vertex_iff.mp hv.symm with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr rfl))
    · obtain ⟨rfl, rfl⟩ := (edgePoint_edgeDartOfSym2_eq_iff_of_mem_Ioo
        (ratio1_pos W e') ((ratio1_lt_ratio2 W e').trans (ratio2_lt_one W e'))).mp he'.symm
      exact Or.inr (Or.inl rfl)
    · obtain ⟨rfl, rfl⟩ := (edgePoint_edgeDartOfSym2_eq_iff_of_mem_Ioo
        ((ratio1_pos W e').trans (ratio1_lt_ratio2 W e')) (ratio2_lt_one W e')).mp he'.symm
      exact Or.inr (Or.inr (Or.inl rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · rw [edgePoint_zero]
      exact vertex_mem_realizationPoints W _
    · exact bp1_mem_realizationPoints W e
    · exact bp2_mem_realizationPoints W e
    · rw [edgePoint_one]
      exact vertex_mem_realizationPoints W _

/-! ### Euclidean vertex placement and segment characterization -/

open Classical in
/-- Euclidean coordinates assigned to each vertex of `realizationSubdivision W`. -/
noncomputable def realizationVertexPos [Finite V] (W : WeightedGraph V)
    (x : { z : MetricGraph W // z ∈ realizationPoints W }) :
    EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1)) :=
  if hv : ∃ v : V, vertex v = x.1 then
    vertexPos W (Classical.choose hv)
  else if h1 : ∃ e : W.graph.edgeSet, bp1 W e = x.1 then
    let e := Classical.choose h1
    vertexPos W (edgeDartOfSym2 e).fst +
      (edgeLegHeight W e) • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ)
  else if h2 : ∃ e : W.graph.edgeSet, bp2 W e = x.1 then
    let e := Classical.choose h2
    vertexPos W (edgeDartOfSym2 e).snd +
      (edgeLegHeight W e) • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ)
  else 0

private theorem realizationVertexPos_vertex [Finite V] (W : WeightedGraph V)
    (v : V) (hv : (vertex v : MetricGraph W) ∈ realizationPoints W) :
    realizationVertexPos W ⟨vertex v, hv⟩ = vertexPos W v := by
  classical
  have hex : ∃ u : V, (vertex u : MetricGraph W) = vertex v := ⟨v, rfl⟩
  dsimp only [realizationVertexPos]
  split_ifs
  congr 1
  exact vertex_injective (Classical.choose_spec hex)

private theorem realizationVertexPos_bp1 [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) (hbp : bp1 W e ∈ realizationPoints W) :
    realizationVertexPos W ⟨bp1 W e, hbp⟩ =
      vertexPos W (edgeDartOfSym2 e).fst +
        (edgeLegHeight W e) • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ) := by
  classical
  have hnv : ¬ ∃ v : V, vertex v = bp1 W e := fun ⟨v, hv⟩ =>
    edgePoint_interior_ne_vertex W (ratio1_pos W) (ratio1_lt_one W) e v hv.symm
  have hex : ∃ e' : W.graph.edgeSet, bp1 W e' = bp1 W e := ⟨e, rfl⟩
  dsimp only [realizationVertexPos]
  split_ifs
  rw [edgePoint_interior_injective W (ratio1_pos W) (ratio1_lt_one W) (Classical.choose_spec hex)]

private theorem realizationVertexPos_bp2 [Finite V] (W : WeightedGraph V)
    (e : W.graph.edgeSet) (hbp : bp2 W e ∈ realizationPoints W) :
    realizationVertexPos W ⟨bp2 W e, hbp⟩ =
      vertexPos W (edgeDartOfSym2 e).snd +
        (edgeLegHeight W e) • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ) := by
  classical
  have hnv : ¬ ∃ v : V, vertex v = bp2 W e := fun ⟨v, hv⟩ =>
    edgePoint_interior_ne_vertex W (ratio2_pos W) (ratio2_lt_one W) e v hv.symm
  have hn1 : ¬ ∃ e' : W.graph.edgeSet, bp1 W e' = bp2 W e :=
    fun ⟨e', he'⟩ => bp1_ne_bp2 W e' e he'
  have hex : ∃ e' : W.graph.edgeSet, bp2 W e' = bp2 W e := ⟨e, rfl⟩
  dsimp only [realizationVertexPos]
  split_ifs
  rw [edgePoint_interior_injective W (ratio2_pos W) (ratio2_lt_one W) (Classical.choose_spec hex)]

private theorem realization_forward_dart_cases [Finite V] (W : WeightedGraph V)
    {e : W.graph.edgeSet} {s t : unitInterval} (hst : (s : ℝ) < t)
    (hs : edgePoint (edgeDartOfSym2 e) s ∈ realizationPoints W)
    (ht : edgePoint (edgeDartOfSym2 e) t ∈ realizationPoints W)
    (hno : ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t →
      edgePoint (edgeDartOfSym2 e) r ∉ realizationPoints W) :
    (s = 0 ∧ t = ratio1 W e) ∨
    (s = ratio1 W e ∧ t = ratio2 W e) ∨
    (s = ratio2 W e ∧ t = 1) := by
  have hs' := (mem_realizationPoints_on_dart_iff W e s).mp hs
  have ht' := (mem_realizationPoints_on_dart_iff W e t).mp ht
  have hr1 : 0 < (ratio1 W e : ℝ) := ratio1_pos W e
  have hr12 : (ratio1 W e : ℝ) < ratio2 W e := ratio1_lt_ratio2 W e
  have hr2 : (ratio2 W e : ℝ) < 1 := ratio2_lt_one W e
  rcases hs' with rfl | rfl | rfl | rfl
  · rcases ht' with rfl | rfl | rfl | rfl
    · exact absurd hst (lt_irrefl _)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact absurd (bp1_mem_realizationPoints W e) (hno (ratio1 W e) hr1 hr12)
    · exact absurd (bp1_mem_realizationPoints W e)
        (hno (ratio1 W e) hr1 (hr12.trans hr2))
  · rcases ht' with rfl | rfl | rfl | rfl
    · exact absurd (hr1.trans hst) (lt_irrefl _)
    · exact absurd hst (lt_irrefl _)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact absurd (bp2_mem_realizationPoints W e) (hno (ratio2 W e) hr12 hr2)
  · rcases ht' with rfl | rfl | rfl | rfl
    · exact absurd ((hr1.trans hr12).trans hst) (lt_irrefl _)
    · exact absurd (hr12.trans hst) (lt_irrefl _)
    · exact absurd hst (lt_irrefl _)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · rcases ht' with rfl | rfl | rfl | rfl
    · exact absurd (((hr1.trans hr12).trans hr2).trans hst) (lt_irrefl _)
    · exact absurd ((hr12.trans hr2).trans hst) (lt_irrefl _)
    · exact absurd (hr2.trans hst) (lt_irrefl _)
    · exact absurd hst (lt_irrefl _)

private inductive SubDartSegment [Finite V] (W : WeightedGraph V)
    (d' : (realizationSubdivision W).graph.Dart) : Type u
  | seg1 (e : W.graph.edgeSet) :
      d'.fst.1 = vertex (edgeDartOfSym2 e).fst →
      d'.snd.1 = bp1 W e →
      (realizationSubdivision W).weight d'.edge = edgeLegHeight W e →
      SubDartSegment W d'
  | seg2 (e : W.graph.edgeSet) :
      d'.fst.1 = bp1 W e →
      d'.snd.1 = bp2 W e →
      (realizationSubdivision W).weight d'.edge = edgeChordDist W e →
      SubDartSegment W d'
  | seg3 (e : W.graph.edgeSet) :
      d'.fst.1 = bp2 W e →
      d'.snd.1 = vertex (edgeDartOfSym2 e).snd →
      (realizationSubdivision W).weight d'.edge = edgeLegHeight W e →
      SubDartSegment W d'
  | seg1Symm (e : W.graph.edgeSet) :
      d'.fst.1 = bp1 W e →
      d'.snd.1 = vertex (edgeDartOfSym2 e).fst →
      (realizationSubdivision W).weight d'.edge = edgeLegHeight W e →
      SubDartSegment W d'
  | seg2Symm (e : W.graph.edgeSet) :
      d'.fst.1 = bp2 W e →
      d'.snd.1 = bp1 W e →
      (realizationSubdivision W).weight d'.edge = edgeChordDist W e →
      SubDartSegment W d'
  | seg3Symm (e : W.graph.edgeSet) :
      d'.fst.1 = vertex (edgeDartOfSym2 e).snd →
      d'.snd.1 = bp2 W e →
      (realizationSubdivision W).weight d'.edge = edgeLegHeight W e →
      SubDartSegment W d'

private noncomputable def classifySubDart [Finite V] (W : WeightedGraph V)
    (d' : (realizationSubdivision W).graph.Dart) : SubDartSegment W d' := by
  classical
  let hex := subdivideEquiv_edgePoint (vertex_mem_realizationPoints W) d' 0
  let d := Classical.choose hex
  let h1 := Classical.choose_spec hex
  let s := Classical.choose h1
  let h2 := Classical.choose_spec h1
  let t := Classical.choose h2
  have hspec := Classical.choose_spec h2
  have hst : (s : ℝ) < t := hspec.1
  have hs : edgePoint d s = d'.fst.1 := hspec.2.1
  have ht : edgePoint d t = d'.snd.1 := hspec.2.2.1
  have hno : ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t →
      edgePoint d r ∉ realizationPoints W := hspec.2.2.2.1
  have hw_eq : (realizationSubdivision W).weight d'.edge = ((t : ℝ) - s) * W.weight d.edge :=
    hspec.2.2.2.2.1
  let e : W.graph.edgeSet := ⟨d.edge, d.edge_mem⟩
  have he : d.edge = (edgeDartOfSym2 e).edge := (edgeDartOfSym2_edge e).symm
  have hwe : W.weight e.1 = W.weight d.edge := rfl
  have hwpos : W.weight e.1 ≠ 0 := by
    rw [hwe]
    exact (W.dart_weight_pos d).ne'
  by_cases hd : d = edgeDartOfSym2 e
  · have hst' : (s : ℝ) < t := hst
    have hsB : edgePoint (edgeDartOfSym2 e) s ∈ realizationPoints W := by
      rw [← hd, hs]; exact d'.fst.2
    have htB : edgePoint (edgeDartOfSym2 e) t ∈ realizationPoints W := by
      rw [← hd, ht]; exact d'.snd.2
    have hno' : ∀ r : unitInterval, (s : ℝ) < r → (r : ℝ) < t →
        edgePoint (edgeDartOfSym2 e) r ∉ realizationPoints W := by
      intro r hr1 hr2
      rw [← hd]
      exact hno r hr1 hr2
    have hf := realization_forward_dart_cases W hst' hsB htB hno'
    by_cases h1 : s = 0 ∧ t = ratio1 W e
    · refine SubDartSegment.seg1 e ?_ ?_ ?_
      · rw [← hs, hd, h1.1, edgePoint_zero]
      · rw [← ht, hd, h1.2]; rfl
      · rw [hw_eq, h1.1, h1.2, ← hwe]
        dsimp only [ratio1]
        change (edgeLegHeight W e / W.weight e.1 - 0) * W.weight e.1 = _
        field_simp [hwpos]
        ring
    · by_cases h2 : s = ratio1 W e ∧ t = ratio2 W e
      · refine SubDartSegment.seg2 e ?_ ?_ ?_
        · rw [← hs, hd, h2.1]; rfl
        · rw [← ht, hd, h2.2]; rfl
        · rw [hw_eq, h2.1, h2.2, ← hwe]
          dsimp only [ratio1, ratio2]
          field_simp [hwpos]
          ring
      · have h3 : s = ratio2 W e ∧ t = 1 := by
          rcases hf with c1 | c2 | c3
          · exact absurd c1 h1
          · exact absurd c2 h2
          · exact c3
        refine SubDartSegment.seg3 e ?_ ?_ ?_
        · rw [← hs, hd, h3.1]; rfl
        · rw [← ht, hd, h3.2, edgePoint_one]
        · rw [hw_eq, h3.1, h3.2, ← hwe]
          dsimp only [ratio2]
          change (1 - (edgeLegHeight W e + edgeChordDist W e) / W.weight e.1) *
            W.weight e.1 = edgeLegHeight W e
          have hsum := two_mul_legHeight_add_chord W e
          field_simp [hwpos]
          linarith
  · have hsym : d = (edgeDartOfSym2 e).symm := by
      rcases (dart_edge_eq_iff d (edgeDartOfSym2 e)).mp he with h | h
      · exact absurd h hd
      · exact h
    let s' := unitInterval.symm t
    let t' := unitInterval.symm s
    have hst' : (s' : ℝ) < t' := by
      change 1 - (t : ℝ) < 1 - s
      linarith [hst]
    have hsB : edgePoint (edgeDartOfSym2 e) s' ∈ realizationPoints W := by
      rw [edgePoint_symm', ← hsym, ht]; exact d'.snd.2
    have htB : edgePoint (edgeDartOfSym2 e) t' ∈ realizationPoints W := by
      rw [edgePoint_symm', ← hsym, hs]; exact d'.fst.2
    have hno' : ∀ r : unitInterval, (s' : ℝ) < r → (r : ℝ) < t' →
        edgePoint (edgeDartOfSym2 e) r ∉ realizationPoints W := by
      intro r hr1 hr2
      change 1 - (t : ℝ) < r at hr1
      change (r : ℝ) < 1 - s at hr2
      have hsr : (s : ℝ) < (unitInterval.symm r : ℝ) := by change (s : ℝ) < 1 - r; linarith
      have hrt : (unitInterval.symm r : ℝ) < t := by change 1 - (r : ℝ) < t; linarith
      have h := hno (unitInterval.symm r) hsr hrt
      rwa [hsym, edgePoint_symm] at h
    have hf := realization_forward_dart_cases W hst' hsB htB hno'
    have hs'_eq : (t : ℝ) - s = (t' : ℝ) - s' := by
      change (t : ℝ) - s = (1 - (s : ℝ)) - (1 - t)
      ring
    by_cases h1 : s' = 0 ∧ t' = ratio1 W e
    · refine SubDartSegment.seg1Symm e ?_ ?_ ?_
      · rw [← hs, hsym, ← edgePoint_symm']
        change edgePoint (edgeDartOfSym2 e) t' = _
        rw [h1.2]; rfl
      · rw [← ht, hsym, ← edgePoint_symm']
        change edgePoint (edgeDartOfSym2 e) s' = _
        rw [h1.1, edgePoint_zero]
      · rw [hw_eq, hs'_eq, h1.1, h1.2, ← hwe]
        dsimp only [ratio1]
        change (edgeLegHeight W e / W.weight e.1 - 0) * W.weight e.1 = _
        field_simp [hwpos]
        ring
    · by_cases h2 : s' = ratio1 W e ∧ t' = ratio2 W e
      · refine SubDartSegment.seg2Symm e ?_ ?_ ?_
        · rw [← hs, hsym, ← edgePoint_symm']
          change edgePoint (edgeDartOfSym2 e) t' = _
          rw [h2.2]; rfl
        · rw [← ht, hsym, ← edgePoint_symm']
          change edgePoint (edgeDartOfSym2 e) s' = _
          rw [h2.1]; rfl
        · rw [hw_eq, hs'_eq, h2.1, h2.2, ← hwe]
          dsimp only [ratio1, ratio2]
          field_simp [hwpos]
          ring
      · have h3 : s' = ratio2 W e ∧ t' = 1 := by
          rcases hf with c1 | c2 | c3
          · exact absurd c1 h1
          · exact absurd c2 h2
          · exact c3
        refine SubDartSegment.seg3Symm e ?_ ?_ ?_
        · rw [← hs, hsym, ← edgePoint_symm']
          change edgePoint (edgeDartOfSym2 e) t' = _
          rw [h3.2, edgePoint_one]
        · rw [← ht, hsym, ← edgePoint_symm']
          change edgePoint (edgeDartOfSym2 e) s' = _
          rw [h3.1]; rfl
        · rw [hw_eq, hs'_eq, h3.1, h3.2, ← hwe]
          dsimp only [ratio2]
          change (1 - (edgeLegHeight W e + edgeChordDist W e) / W.weight e.1) *
            W.weight e.1 = edgeLegHeight W e
          have hsum := two_mul_legHeight_add_chord W e
          field_simp [hwpos]
          linarith

/-! ### Straight-edge realization map -/

/-- The straight-edge Euclidean map on `MetricGraph (realizationSubdivision W)` sending every
subdivided vertex to `realizationVertexPos W` and every subdivided edge onto a straight line
segment. -/
noncomputable def realizationMap [Finite V] (W : WeightedGraph V) :
    MetricGraph (realizationSubdivision W) →
      EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1)) :=
  lift (realizationVertexPos W)
    (fun d' r => (1 - (r : ℝ)) • realizationVertexPos W d'.fst +
      (r : ℝ) • realizationVertexPos W d'.snd)
    (fun d' => by rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, one_smul,
      zero_smul, add_zero])
    (fun d' => by rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, zero_smul,
      zero_add, one_smul])
    (fun d' r => by
      change (1 - (1 - (r : ℝ))) • realizationVertexPos W d'.snd +
          (1 - (r : ℝ)) • realizationVertexPos W d'.fst = _
      rw [sub_sub_cancel]
      exact add_comm _ _)

@[simp]
theorem realizationMap_vertex [Finite V] (W : WeightedGraph V)
    (x : { z : MetricGraph W // z ∈ realizationPoints W }) :
    realizationMap W (vertex x) = realizationVertexPos W x :=
  lift_vertex _ _ _ _ _ x

theorem realizationMap_edgePoint [Finite V] (W : WeightedGraph V)
    (d' : (realizationSubdivision W).graph.Dart) (r : unitInterval) :
    realizationMap W (edgePoint d' r) =
      (1 - (r : ℝ)) • realizationMap W (vertex d'.fst) +
        (r : ℝ) • realizationMap W (vertex d'.snd) := by
  simp only [realizationMap, lift_vertex, lift_edgePoint]

theorem realizationMap_edge_dist [Finite V] (W : WeightedGraph V)
    (d' : (realizationSubdivision W).graph.Dart) :
    dist (realizationMap W (vertex d'.fst)) (realizationMap W (vertex d'.snd)) =
      (realizationSubdivision W).weight d'.edge := by
  rw [realizationMap_vertex, realizationMap_vertex]
  have h1 : ∀ (a : { z // z ∈ realizationPoints W }) (b : { z // z ∈ realizationPoints W })
      (v : V) (e : W.graph.edgeSet) (ha : a.1 = vertex v) (hb : b.1 = bp1 W e)
      (hv : v = (edgeDartOfSym2 e).fst),
      dist (realizationVertexPos W a) (realizationVertexPos W b) = edgeLegHeight W e := by
    intro a b v e ha hb hv
    have hae : a = ⟨vertex v, ha ▸ a.2⟩ := Subtype.ext ha
    have hbe : b = ⟨bp1 W e, hb ▸ b.2⟩ := Subtype.ext hb
    rw [hae, hbe, realizationVertexPos_vertex, realizationVertexPos_bp1, hv, dist_eq_norm]
    have hdiff : vertexPos W (edgeDartOfSym2 e).fst -
        (vertexPos W (edgeDartOfSym2 e).fst +
          edgeLegHeight W e • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ)) =
        -(edgeLegHeight W e • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ)) := by
      abel
    rw [hdiff, norm_neg, norm_smul, Real.norm_of_nonneg (edgeLegHeight_pos W e).le,
      PiLp.norm_single, norm_one, mul_one]
  have h2 : ∀ (a b : { z // z ∈ realizationPoints W }) (e : W.graph.edgeSet)
      (ha : a.1 = bp1 W e) (hb : b.1 = bp2 W e),
      dist (realizationVertexPos W a) (realizationVertexPos W b) = edgeChordDist W e := by
    intro a b e ha hb
    have hae : a = ⟨bp1 W e, ha ▸ a.2⟩ := Subtype.ext ha
    have hbe : b = ⟨bp2 W e, hb ▸ b.2⟩ := Subtype.ext hb
    rw [hae, hbe, realizationVertexPos_bp1, realizationVertexPos_bp2, dist_eq_norm]
    have hdiff : (vertexPos W (edgeDartOfSym2 e).fst +
          edgeLegHeight W e • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ)) -
        (vertexPos W (edgeDartOfSym2 e).snd +
          edgeLegHeight W e • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ)) =
        vertexPos W (edgeDartOfSym2 e).fst - vertexPos W (edgeDartOfSym2 e).snd := by
      abel
    rw [hdiff, ← dist_eq_norm]
    rfl
  have h3 : ∀ (a b : { z // z ∈ realizationPoints W }) (e : W.graph.edgeSet)
      (v : V) (ha : a.1 = bp2 W e) (hb : b.1 = vertex v) (hv : v = (edgeDartOfSym2 e).snd),
      dist (realizationVertexPos W a) (realizationVertexPos W b) = edgeLegHeight W e := by
    intro a b e v ha hb hv
    have hae : a = ⟨bp2 W e, ha ▸ a.2⟩ := Subtype.ext ha
    have hbe : b = ⟨vertex v, hb ▸ b.2⟩ := Subtype.ext hb
    rw [hae, hbe, realizationVertexPos_bp2, realizationVertexPos_vertex, hv, dist_eq_norm]
    have hdiff : (vertexPos W (edgeDartOfSym2 e).snd +
          edgeLegHeight W e • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ)) -
        vertexPos W (edgeDartOfSym2 e).snd =
        edgeLegHeight W e • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ) := by
      abel
    rw [hdiff, norm_smul, Real.norm_of_nonneg (edgeLegHeight_pos W e).le,
      PiLp.norm_single, norm_one, mul_one]
  rcases classifySubDart W d' with
    ⟨e, hfst, hsnd, hw⟩ | ⟨e, hfst, hsnd, hw⟩ | ⟨e, hfst, hsnd, hw⟩ |
    ⟨e, hfst, hsnd, hw⟩ | ⟨e, hfst, hsnd, hw⟩ | ⟨e, hfst, hsnd, hw⟩
  · exact (h1 _ _ _ e hfst hsnd rfl).trans hw.symm
  · exact (h2 _ _ e hfst hsnd).trans hw.symm
  · exact (h3 _ _ e _ hfst hsnd rfl).trans hw.symm
  · rw [dist_comm]
    exact (h1 _ _ _ e hsnd hfst rfl).trans hw.symm
  · rw [dist_comm]
    exact (h2 _ _ e hsnd hfst).trans hw.symm
  · rw [dist_comm]
    exact (h3 _ _ e _ hsnd hfst rfl).trans hw.symm

theorem realizationMap_edgePoint_dist [Finite V] (W : WeightedGraph V)
    (d' : (realizationSubdivision W).graph.Dart) (r₁ r₂ : unitInterval) :
    dist (realizationMap W (edgePoint d' r₁)) (realizationMap W (edgePoint d' r₂)) =
      |(r₁ : ℝ) - r₂| * (realizationSubdivision W).weight d'.edge := by
  rw [realizationMap_edgePoint, realizationMap_edgePoint, dist_eq_norm]
  have hdiff : ((1 - (r₁ : ℝ)) • realizationMap W (vertex d'.fst) +
        (r₁ : ℝ) • realizationMap W (vertex d'.snd)) -
      ((1 - (r₂ : ℝ)) • realizationMap W (vertex d'.fst) +
        (r₂ : ℝ) • realizationMap W (vertex d'.snd)) =
      ((r₁ : ℝ) - r₂) •
        (realizationMap W (vertex d'.snd) - realizationMap W (vertex d'.fst)) := by
    module
  rw [hdiff, norm_smul, Real.norm_eq_abs, ← dist_eq_norm, dist_comm,
    realizationMap_edge_dist]

theorem realizationMap_dist_le [Finite V] (W : WeightedGraph V)
    (p q : MetricGraph (realizationSubdivision W)) :
    dist (realizationMap W p) (realizationMap W q) ≤ dist p q :=
  dist_map_le_of_edgePoint_dist_le (realizationMap W)
    (fun d' r₁ r₂ => (realizationMap_edgePoint_dist W d' r₁ r₂).le) p q

theorem continuous_realizationMap [Finite V] (W : WeightedGraph V) :
    Continuous (realizationMap W) :=
  Metric.continuous_iff.mpr fun x ε hε =>
    ⟨ε, hε, fun {y} hy => (realizationMap_dist_le W y x).trans_lt hy⟩

/-! ### Injectivity, closed embedding, induced weighted graph, and rationality -/

private theorem realizationMap_apply_succ_of_vertex [Finite V] (W : WeightedGraph V)
    (v : V) (hv : (vertex v : MetricGraph W) ∈ realizationPoints W)
    (k : Fin (Nat.card W.graph.edgeSet)) :
    realizationMap W (vertex ⟨vertex v, hv⟩) k.succ = 0 := by
  rw [realizationMap_vertex, realizationVertexPos_vertex, vertexPos_apply_succ]

private theorem vertexPos_apply_zero_ne [Finite V] (W : WeightedGraph V) {u v : V}
    (hne : u ≠ v) : vertexPos W u 0 ≠ vertexPos W v 0 := by
  intro heq
  rw [vertexPos_apply_zero, vertexPos_apply_zero] at heq
  have h1 : ((vertexEquiv u : ℕ) : ℝ) = (vertexEquiv v : ℕ) :=
    mul_left_cancel₀ (vertexSpacing_pos W).ne' heq
  exact hne (vertexEquiv.injective (Fin.ext (by exact_mod_cast h1)))

private def RealizationClassified [Finite V] (W : WeightedGraph V)
    (p : MetricGraph (realizationSubdivision W)) : Prop :=
  let z := realizationMap W p
  let q := subdivideEquiv (vertex_mem_realizationPoints W) p
  (∃ v : V, q = vertex v ∧ (∀ k : Fin (Nat.card W.graph.edgeSet), z k.succ = 0) ∧
    z 0 = vertexPos W v 0) ∨
  (∃ (e : W.graph.edgeSet) (u : unitInterval),
    (0 : ℝ) < u ∧ (u : ℝ) < 1 ∧ q = edgePoint (edgeDartOfSym2 e) u ∧
    (∀ k ≠ edgeEquiv W e, z k.succ = 0) ∧
    let x₀ := vertexPos W (edgeDartOfSym2 e).fst 0
    let x₁ := vertexPos W (edgeDartOfSym2 e).snd 0
    let h := edgeLegHeight W e
    let w := W.weight e.1
    (((u : ℝ) ≤ ratio1 W e ∧ z 0 = x₀ ∧ z (Fin.succ (edgeEquiv W e)) = (u : ℝ) * w) ∨
     ((ratio1 W e : ℝ) ≤ u ∧ (u : ℝ) ≤ ratio2 W e ∧
       z (Fin.succ (edgeEquiv W e)) = h ∧
       z 0 = (1 - ((u : ℝ) * w - h) / edgeChordDist W e) * x₀ +
         (((u : ℝ) * w - h) / edgeChordDist W e) * x₁) ∨
     ((ratio2 W e : ℝ) ≤ u ∧ z 0 = x₁ ∧
       z (Fin.succ (edgeEquiv W e)) = (1 - (u : ℝ)) * w)))

private theorem realizationMap_classify [Finite V] (W : WeightedGraph V)
    (p : MetricGraph (realizationSubdivision W)) :
    RealizationClassified W p := by
  have hBpCoords : ∀ (e : W.graph.edgeSet) (v : V) (x : { z // z ∈ realizationPoints W }),
      realizationVertexPos W x =
        vertexPos W v +
          edgeLegHeight W e • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ) →
      (∀ k ≠ edgeEquiv W e, realizationMap W (vertex x) k.succ = 0) ∧
      realizationMap W (vertex x) 0 = vertexPos W v 0 ∧
      realizationMap W (vertex x) (Fin.succ (edgeEquiv W e)) = edgeLegHeight W e := by
    intro e v x hx
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      have hne : Fin.succ k ≠ Fin.succ (edgeEquiv W e) := fun h => hk (Fin.succ_inj.mp h)
      rw [realizationMap_vertex, hx, PiLp.add_apply, PiLp.smul_apply,
        vertexPos_apply_succ, PiLp.single_eq_of_ne 2 hne, smul_zero, zero_add]
    · rw [realizationMap_vertex, hx, PiLp.add_apply, PiLp.smul_apply,
        PiLp.single_eq_of_ne 2 (Fin.succ_ne_zero _).symm, smul_zero, add_zero]
    · rw [realizationMap_vertex, hx, PiLp.add_apply, PiLp.smul_apply,
        vertexPos_apply_succ, PiLp.single_eq_same, smul_eq_mul, mul_one, zero_add]
  have hBp1 : ∀ (e : W.graph.edgeSet) (hmem : bp1 W e ∈ realizationPoints W),
      let z := realizationMap W (vertex ⟨bp1 W e, hmem⟩)
      let q := subdivideEquiv (vertex_mem_realizationPoints W) (vertex ⟨bp1 W e, hmem⟩)
      (0 : ℝ) < ratio1 W e ∧ (ratio1 W e : ℝ) < 1 ∧
      q = edgePoint (edgeDartOfSym2 e) (ratio1 W e) ∧
      (∀ k ≠ edgeEquiv W e, z k.succ = 0) ∧
      (ratio1 W e : ℝ) ≤ ratio1 W e ∧ z 0 = vertexPos W (edgeDartOfSym2 e).fst 0 ∧
      z (Fin.succ (edgeEquiv W e)) = (ratio1 W e : ℝ) * W.weight e.1 := by
    intro e hmem
    have hw : W.weight e.1 ≠ 0 := by
      simpa only [edgeDartOfSym2_edge] using (W.dart_weight_pos (edgeDartOfSym2 e)).ne'
    obtain ⟨hk, h0, hs⟩ := hBpCoords e (edgeDartOfSym2 e).fst _ (realizationVertexPos_bp1 W e hmem)
    refine ⟨ratio1_pos W e, ratio1_lt_one W e, ?_, hk, le_rfl, h0, ?_⟩
    · rw [subdivideEquiv_vertex]; rfl
    · rw [hs]
      dsimp only [ratio1]
      field_simp [hw]
  have hBp2 : ∀ (e : W.graph.edgeSet) (hmem : bp2 W e ∈ realizationPoints W),
      let z := realizationMap W (vertex ⟨bp2 W e, hmem⟩)
      let q := subdivideEquiv (vertex_mem_realizationPoints W) (vertex ⟨bp2 W e, hmem⟩)
      (0 : ℝ) < ratio2 W e ∧ (ratio2 W e : ℝ) < 1 ∧
      q = edgePoint (edgeDartOfSym2 e) (ratio2 W e) ∧
      (∀ k ≠ edgeEquiv W e, z k.succ = 0) ∧
      (ratio2 W e : ℝ) ≤ ratio2 W e ∧ z 0 = vertexPos W (edgeDartOfSym2 e).snd 0 ∧
      z (Fin.succ (edgeEquiv W e)) = (1 - (ratio2 W e : ℝ)) * W.weight e.1 := by
    intro e hmem
    have hw : W.weight e.1 ≠ 0 := by
      simpa only [edgeDartOfSym2_edge] using (W.dart_weight_pos (edgeDartOfSym2 e)).ne'
    obtain ⟨hk, h0, hs⟩ := hBpCoords e (edgeDartOfSym2 e).snd _ (realizationVertexPos_bp2 W e hmem)
    refine ⟨ratio2_pos W e, ratio2_lt_one W e, ?_, hk, le_rfl, h0, ?_⟩
    · rw [subdivideEquiv_vertex]; rfl
    · rw [hs]
      dsimp only [ratio2]
      have hsum := two_mul_legHeight_add_chord W e
      field_simp [hw]
      linarith
  have hVertexCase : ∀ x : { z : MetricGraph W // z ∈ realizationPoints W },
      (∃ v : V, subdivideEquiv (vertex_mem_realizationPoints W) (vertex x) = vertex v ∧
        (∀ k : Fin (Nat.card W.graph.edgeSet), realizationMap W (vertex x) k.succ = 0) ∧
        realizationMap W (vertex x) 0 = vertexPos W v 0) ∨
      (∃ (e : W.graph.edgeSet) (u : unitInterval),
        (0 : ℝ) < u ∧ (u : ℝ) < 1 ∧
        subdivideEquiv (vertex_mem_realizationPoints W) (vertex x) =
          edgePoint (edgeDartOfSym2 e) u ∧
        (∀ k ≠ edgeEquiv W e, realizationMap W (vertex x) k.succ = 0) ∧
        let x₀ := vertexPos W (edgeDartOfSym2 e).fst 0
        let x₁ := vertexPos W (edgeDartOfSym2 e).snd 0
        let h := edgeLegHeight W e
        let w := W.weight e.1
        (((u : ℝ) ≤ ratio1 W e ∧ realizationMap W (vertex x) 0 = x₀ ∧
           realizationMap W (vertex x) (Fin.succ (edgeEquiv W e)) = (u : ℝ) * w) ∨
         ((ratio1 W e : ℝ) ≤ u ∧ (u : ℝ) ≤ ratio2 W e ∧
           realizationMap W (vertex x) (Fin.succ (edgeEquiv W e)) = h ∧
           realizationMap W (vertex x) 0 =
             (1 - ((u : ℝ) * w - h) / edgeChordDist W e) * x₀ +
               (((u : ℝ) * w - h) / edgeChordDist W e) * x₁) ∨
         ((ratio2 W e : ℝ) ≤ u ∧ realizationMap W (vertex x) 0 = x₁ ∧
           realizationMap W (vertex x) (Fin.succ (edgeEquiv W e)) = (1 - (u : ℝ)) * w))) := by
    intro x
    classical
    have hx := x.2
    simp only [realizationPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at hx
    rcases hx with (⟨v, hv⟩ | ⟨e, he⟩) | ⟨e, he⟩
    · have hsub : x = ⟨vertex v, hv ▸ x.2⟩ := Subtype.ext hv.symm
      rw [hsub]
      refine Or.inl ⟨v, by rw [subdivideEquiv_vertex],
        fun k => realizationMap_apply_succ_of_vertex W v _ k,
        by rw [realizationMap_vertex, realizationVertexPos_vertex]⟩
    · have hsub : x = ⟨bp1 W e, he ▸ x.2⟩ := Subtype.ext he.symm
      rw [hsub]
      obtain ⟨h0, h1, hq, hk, hle, hz0, hze⟩ := hBp1 e (he ▸ x.2)
      exact Or.inr ⟨e, ratio1 W e, h0, h1, hq, hk, Or.inl ⟨hle, hz0, hze⟩⟩
    · have hsub : x = ⟨bp2 W e, he ▸ x.2⟩ := Subtype.ext he.symm
      rw [hsub]
      obtain ⟨h0, h1, hq, hk, hle, hz0, hze⟩ := hBp2 e (he ▸ x.2)
      exact Or.inr ⟨e, ratio2 W e, h0, h1, hq, hk, Or.inr (Or.inr ⟨hle, hz0, hze⟩)⟩
  induction p using ind_simple with
  | vertex x => exact hVertexCase x
  | edgePoint d' r =>
    by_cases hr0 : (r : ℝ) = 0
    · have hr' : r = 0 := Subtype.ext hr0
      rw [hr', edgePoint_zero]
      exact hVertexCase d'.fst
    · by_cases hr1 : (r : ℝ) = 1
      · have hr' : r = 1 := Subtype.ext hr1
        rw [hr', edgePoint_one]
        exact hVertexCase d'.snd
      · have hr_pos : (0 : ℝ) < r := lt_of_le_of_ne r.2.1 (Ne.symm hr0)
        have hr_lt : (r : ℝ) < 1 := lt_of_le_of_ne r.2.2 hr1
        obtain ⟨d, s, t, hst, hs, ht, _, _, heq⟩ :=
          subdivideEquiv_edgePoint (vertex_mem_realizationPoints W) d' r
        have hwitness : ∀ {e : W.graph.edgeSet} {s₀ t₀ : unitInterval},
            (s₀ : ℝ) < t₀ →
            edgePoint (edgeDartOfSym2 e) s₀ = d'.fst.1 →
            edgePoint (edgeDartOfSym2 e) t₀ = d'.snd.1 →
            subdivideEquiv (vertex_mem_realizationPoints W) (edgePoint d' r) =
              edgePoint (edgeDartOfSym2 e) ⟨(1 - (r : ℝ)) * s₀ + r * t₀,
                add_nonneg (mul_nonneg (unitInterval.one_sub_nonneg r) s₀.2.1)
                  (mul_nonneg r.2.1 t₀.2.1),
                by nlinarith [r.2.1, r.2.2, s₀.2.2, t₀.2.2]⟩ := by
          intro e s₀ t₀ hst₀ hs₀ ht₀
          obtain ⟨rfl, rfl, rfl⟩ :=
            subAdj_witness_eq hst hst₀ (hs.trans hs₀.symm) (ht.trans ht₀.symm)
          exact heq
        have hwitnessSymm : ∀ {e : W.graph.edgeSet} {s₀ t₀ : unitInterval},
            (s₀ : ℝ) < t₀ →
            edgePoint (edgeDartOfSym2 e) t₀ = d'.fst.1 →
            edgePoint (edgeDartOfSym2 e) s₀ = d'.snd.1 →
            subdivideEquiv (vertex_mem_realizationPoints W) (edgePoint d' r) =
              edgePoint (edgeDartOfSym2 e) ⟨(1 - (r : ℝ)) * t₀ + r * s₀,
                add_nonneg (mul_nonneg (unitInterval.one_sub_nonneg r) t₀.2.1)
                  (mul_nonneg r.2.1 s₀.2.1),
                by nlinarith [r.2.1, r.2.2, s₀.2.2, t₀.2.2]⟩ := by
          intro e s₀ t₀ hst₀ ht₀ hs₀
          have hst' : (unitInterval.symm t₀ : ℝ) < unitInterval.symm s₀ := by
            change 1 - (t₀ : ℝ) < 1 - s₀; linarith
          have hs' : edgePoint (edgeDartOfSym2 e).symm (unitInterval.symm t₀) = d'.fst.1 := by
            rw [edgePoint_symm]; exact ht₀
          have ht' : edgePoint (edgeDartOfSym2 e).symm (unitInterval.symm s₀) = d'.snd.1 := by
            rw [edgePoint_symm]; exact hs₀
          obtain ⟨rfl, rfl, rfl⟩ :=
            subAdj_witness_eq hst hst' (hs.trans hs'.symm) (ht.trans ht'.symm)
          rw [heq, ← edgePoint_symm]
          congr 1
          ext
          change 1 - ((1 - (r : ℝ)) * (1 - (t₀ : ℝ)) + r * (1 - (s₀ : ℝ))) = _
          ring
        have hseg1 : ∀ (e : W.graph.edgeSet) (τ : unitInterval)
            (hτ_pos : (0 : ℝ) < τ) (hτ_lt : (τ : ℝ) < 1)
            (hz : realizationMap W (edgePoint d' r) =
              (1 - (τ : ℝ)) • realizationMap W (vertex ⟨vertex (edgeDartOfSym2 e).fst,
                vertex_mem_realizationPoints W _⟩) +
              (τ : ℝ) • realizationMap W (vertex ⟨bp1 W e, bp1_mem_realizationPoints W e⟩))
            (hq : subdivideEquiv (vertex_mem_realizationPoints W) (edgePoint d' r) =
              edgePoint (edgeDartOfSym2 e) ⟨(τ : ℝ) * ratio1 W e,
                mul_nonneg hτ_pos.le (ratio1_pos W e).le,
                (mul_le_of_le_one_left (ratio1_pos W e).le hτ_lt.le).trans
                  (ratio1 W e).2.2⟩),
            RealizationClassified W (edgePoint d' r) := by
          intro e τ hτ_pos hτ_lt hz hq
          refine Or.inr ⟨e, ⟨(τ : ℝ) * ratio1 W e,
            mul_nonneg hτ_pos.le (ratio1_pos W e).le,
            (mul_le_of_le_one_left (ratio1_pos W e).le hτ_lt.le).trans
              (ratio1 W e).2.2⟩,
            mul_pos hτ_pos (ratio1_pos W e), ?_, hq, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
          · calc (τ : ℝ) * ratio1 W e
                < 1 * ratio1 W e := mul_lt_mul_of_pos_right hτ_lt (ratio1_pos W e)
              _ < 1 := by
                rw [one_mul]
                exact (ratio1_lt_ratio2 W e).trans (ratio2_lt_one W e)
          · intro k hk
            have hne : Fin.succ k ≠ Fin.succ (edgeEquiv W e) := fun h => hk (Fin.succ_inj.mp h)
            rw [hz, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
              realizationMap_vertex, realizationMap_vertex, realizationVertexPos_vertex,
              realizationVertexPos_bp1, vertexPos_apply_succ, PiLp.add_apply, PiLp.smul_apply,
              vertexPos_apply_succ, PiLp.single_eq_of_ne 2 hne, smul_zero, zero_add, mul_zero,
              mul_zero, add_zero]
          · exact mul_le_of_le_one_left (ratio1_pos W e).le hτ_lt.le
          · rw [hz, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
              realizationMap_vertex, realizationMap_vertex, realizationVertexPos_vertex,
              realizationVertexPos_bp1, PiLp.add_apply, PiLp.smul_apply,
              PiLp.single_eq_of_ne 2 (Fin.succ_ne_zero _).symm, smul_zero, add_zero]
            ring
          · rw [hz, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul,
              realizationMap_vertex, realizationMap_vertex, realizationVertexPos_vertex,
              realizationVertexPos_bp1, vertexPos_apply_succ, PiLp.add_apply, PiLp.smul_apply,
              vertexPos_apply_succ, PiLp.single_eq_same, smul_eq_mul, mul_one, zero_add,
              mul_zero, zero_add]
            have hw : W.weight e.1 ≠ 0 := by
              simpa only [edgeDartOfSym2_edge] using (W.dart_weight_pos (edgeDartOfSym2 e)).ne'
            dsimp only [ratio1]
            field_simp [hw]
        have hseg2 : ∀ (e : W.graph.edgeSet)
            (τ : unitInterval) (hτ_pos : (0 : ℝ) < τ) (hτ_lt : (τ : ℝ) < 1)
            (hz : realizationMap W (edgePoint d' r) =
              (1 - (τ : ℝ)) • realizationMap W (vertex ⟨bp1 W e, bp1_mem_realizationPoints W e⟩) +
              (τ : ℝ) • realizationMap W (vertex ⟨bp2 W e, bp2_mem_realizationPoints W e⟩))
            (hq : subdivideEquiv (vertex_mem_realizationPoints W) (edgePoint d' r) =
              edgePoint (edgeDartOfSym2 e) ⟨(1 - (τ : ℝ)) * ratio1 W e + τ * ratio2 W e,
                add_nonneg (mul_nonneg (unitInterval.one_sub_nonneg τ) (ratio1 W e).2.1)
                  (mul_nonneg τ.2.1 (ratio2 W e).2.1),
                by nlinarith [τ.2.1, τ.2.2, (ratio1 W e).2.2, (ratio2 W e).2.2]⟩),
            RealizationClassified W (edgePoint d' r) := by
          intro e τ hτ_pos hτ_lt hz hq
          let u : unitInterval := ⟨(1 - (τ : ℝ)) * ratio1 W e + τ * ratio2 W e,
            add_nonneg (mul_nonneg (unitInterval.one_sub_nonneg τ) (ratio1 W e).2.1)
              (mul_nonneg τ.2.1 (ratio2 W e).2.1),
            by nlinarith [τ.2.1, τ.2.2, (ratio1 W e).2.2, (ratio2 W e).2.2]⟩
          have hr12 := ratio1_lt_ratio2 W e
          have hu_lo : (ratio1 W e : ℝ) ≤ u := by
            change (ratio1 W e : ℝ) ≤ (1 - (τ : ℝ)) * ratio1 W e + τ * ratio2 W e
            nlinarith [τ.2.1]
          have hu_hi : (u : ℝ) ≤ ratio2 W e := by
            change (1 - (τ : ℝ)) * ratio1 W e + τ * ratio2 W e ≤ ratio2 W e
            nlinarith [τ.2.2]
          have h0 : (0 : ℝ) < u := (ratio1_pos W e).trans_le hu_lo
          have h1 : (u : ℝ) < 1 := hu_hi.trans_lt (ratio2_lt_one W e)
          have hw : W.weight e.1 ≠ 0 := by
            simpa only [edgeDartOfSym2_edge] using (W.dart_weight_pos (edgeDartOfSym2 e)).ne'
          have hd0 : edgeChordDist W e ≠ 0 := (edgeChordDist_pos W e).ne'
          have hfrac : ((u : ℝ) * W.weight e.1 - edgeLegHeight W e) / edgeChordDist W e = τ := by
            change (((1 - (τ : ℝ)) * ratio1 W e + τ * ratio2 W e) * W.weight e.1 -
              edgeLegHeight W e) / edgeChordDist W e = τ
            dsimp only [ratio1, ratio2]
            field_simp [hw, hd0]
            ring
          refine Or.inr ⟨e, u, h0, h1, hq, ?_, Or.inr (Or.inl ⟨hu_lo, hu_hi, ?_, ?_⟩)⟩
          · intro k hk
            have hne : Fin.succ k ≠ Fin.succ (edgeEquiv W e) := fun h => hk (Fin.succ_inj.mp h)
            simp only [hz, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
              realizationMap_vertex, realizationVertexPos_bp1, realizationVertexPos_bp2,
              vertexPos_apply_succ, PiLp.single_eq_of_ne 2 hne, mul_zero, add_zero]
          · simp only [hz, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
              realizationMap_vertex, realizationVertexPos_bp1, realizationVertexPos_bp2,
              vertexPos_apply_succ, PiLp.single_eq_same, mul_one, zero_add]
            ring
          · simp only [hz, hfrac, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
              realizationMap_vertex, realizationVertexPos_bp1, realizationVertexPos_bp2,
              PiLp.single_eq_of_ne 2 (Fin.succ_ne_zero _).symm, mul_zero, add_zero]
        have hseg3 : ∀ (e : W.graph.edgeSet)
            (τ : unitInterval) (hτ_pos : (0 : ℝ) < τ) (hτ_lt : (τ : ℝ) < 1)
            (hz : realizationMap W (edgePoint d' r) =
              (1 - (τ : ℝ)) • realizationMap W (vertex ⟨bp2 W e, bp2_mem_realizationPoints W e⟩) +
              (τ : ℝ) • realizationMap W (vertex ⟨vertex (edgeDartOfSym2 e).snd,
                vertex_mem_realizationPoints W _⟩))
            (hq : subdivideEquiv (vertex_mem_realizationPoints W) (edgePoint d' r) =
              edgePoint (edgeDartOfSym2 e) ⟨(1 - (τ : ℝ)) * ratio2 W e + τ,
                add_nonneg (mul_nonneg (unitInterval.one_sub_nonneg τ) (ratio2 W e).2.1) τ.2.1,
                by nlinarith [τ.2.1, τ.2.2, (ratio2 W e).2.2]⟩),
            RealizationClassified W (edgePoint d' r) := by
          intro e τ hτ_pos hτ_lt hz hq
          let u : unitInterval := ⟨(1 - (τ : ℝ)) * ratio2 W e + τ,
            add_nonneg (mul_nonneg (unitInterval.one_sub_nonneg τ) (ratio2 W e).2.1) τ.2.1,
            by nlinarith [τ.2.1, τ.2.2, (ratio2 W e).2.2]⟩
          have hr2 := ratio2_lt_one W e
          have hu_lo : (ratio2 W e : ℝ) ≤ u := by
            change (ratio2 W e : ℝ) ≤ (1 - (τ : ℝ)) * ratio2 W e + τ
            nlinarith [τ.2.1]
          have h0 : (0 : ℝ) < u := ((ratio1_pos W e).trans (ratio1_lt_ratio2 W e)).trans_le hu_lo
          have h1 : (u : ℝ) < 1 := by
            change (1 - (τ : ℝ)) * ratio2 W e + τ < 1
            nlinarith [τ.2.2]
          have hw : W.weight e.1 ≠ 0 := by
            simpa only [edgeDartOfSym2_edge] using (W.dart_weight_pos (edgeDartOfSym2 e)).ne'
          refine Or.inr ⟨e, u, h0, h1, hq, ?_, Or.inr (Or.inr ⟨hu_lo, ?_, ?_⟩)⟩
          · intro k hk
            have hne : Fin.succ k ≠ Fin.succ (edgeEquiv W e) := fun h => hk (Fin.succ_inj.mp h)
            simp only [hz, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
              realizationMap_vertex, realizationVertexPos_bp2, realizationVertexPos_vertex,
              vertexPos_apply_succ, PiLp.single_eq_of_ne 2 hne, mul_zero, add_zero]
          · simp only [hz, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
              realizationMap_vertex, realizationVertexPos_bp2, realizationVertexPos_vertex,
              PiLp.single_eq_of_ne 2 (Fin.succ_ne_zero _).symm, mul_zero, add_zero]
            ring
          · simp only [hz, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
              realizationMap_vertex, realizationVertexPos_bp2, realizationVertexPos_vertex,
              vertexPos_apply_succ, PiLp.single_eq_same, mul_one, zero_add, mul_zero, add_zero]
            dsimp only [u, ratio2]
            have hsum := two_mul_legHeight_add_chord W e
            field_simp [hw]
            rw [← hsum]
            ring
        rcases classifySubDart W d' with
          ⟨e, hfst, hsnd, _⟩ | ⟨e, hfst, hsnd, _⟩ | ⟨e, hfst, hsnd, _⟩ |
          ⟨e, hfst, hsnd, _⟩ | ⟨e, hfst, hsnd, _⟩ | ⟨e, hfst, hsnd, _⟩
        · have hf1 : d'.fst = ⟨vertex (edgeDartOfSym2 e).fst, vertex_mem_realizationPoints W _⟩ :=
            Subtype.ext hfst
          have hs1 : d'.snd = ⟨bp1 W e, bp1_mem_realizationPoints W e⟩ := Subtype.ext hsnd
          refine hseg1 e r hr_pos hr_lt ?_ ?_
          · rw [realizationMap_edgePoint, hf1, hs1]
          · have heq' := hwitness (ratio1_pos W e)
              (by rw [edgePoint_zero, hfst]) hsnd.symm
            convert heq' using 2
            ext
            dsimp only
            change (r : ℝ) * ratio1 W e = (1 - (r : ℝ)) * (0 : ℝ) + r * ratio1 W e
            ring
        · have hf1 : d'.fst = ⟨bp1 W e, bp1_mem_realizationPoints W e⟩ := Subtype.ext hfst
          have hs1 : d'.snd = ⟨bp2 W e, bp2_mem_realizationPoints W e⟩ := Subtype.ext hsnd
          refine hseg2 e r hr_pos hr_lt ?_ ?_
          · rw [realizationMap_edgePoint, hf1, hs1]
          · exact hwitness (ratio1_lt_ratio2 W e) hfst.symm hsnd.symm
        · have hf1 : d'.fst = ⟨bp2 W e, bp2_mem_realizationPoints W e⟩ := Subtype.ext hfst
          have hs1 : d'.snd = ⟨vertex (edgeDartOfSym2 e).snd, vertex_mem_realizationPoints W _⟩ :=
            Subtype.ext hsnd
          refine hseg3 e r hr_pos hr_lt ?_ ?_
          · rw [realizationMap_edgePoint, hf1, hs1]
          · have heq' := hwitness (ratio2_lt_one W e)
              hfst.symm (by rw [edgePoint_one, hsnd])
            convert heq' using 2
            ext
            dsimp only
            change (1 - (r : ℝ)) * ratio2 W e + r = (1 - (r : ℝ)) * ratio2 W e + r * (1 : ℝ)
            ring
        · have hf1 : d'.fst = ⟨bp1 W e, bp1_mem_realizationPoints W e⟩ := Subtype.ext hfst
          have hs1 : d'.snd = ⟨vertex (edgeDartOfSym2 e).fst, vertex_mem_realizationPoints W _⟩ :=
            Subtype.ext hsnd
          let τ := unitInterval.symm r
          have hτ0 : (0 : ℝ) < τ := by change (0 : ℝ) < 1 - r; linarith
          have hτ1 : (τ : ℝ) < 1 := by change 1 - (r : ℝ) < 1; linarith
          refine hseg1 e τ hτ0 hτ1 ?_ ?_
          · have hsub : 1 - (τ : ℝ) = (r : ℝ) := by change 1 - (1 - (r : ℝ)) = r; ring
            rw [realizationMap_edgePoint, hf1, hs1, hsub, add_comm ((1 - (r : ℝ)) • _)]
            rfl
          · have heq' := hwitnessSymm (ratio1_pos W e)
              hfst.symm (by rw [edgePoint_zero, hsnd])
            convert heq' using 2
            ext
            dsimp only [τ]
            rw [unitInterval.coe_symm_eq]
            change (1 - (r : ℝ)) * ratio1 W e = (1 - (r : ℝ)) * ratio1 W e + r * (0 : ℝ)
            ring
        · have hf1 : d'.fst = ⟨bp2 W e, bp2_mem_realizationPoints W e⟩ := Subtype.ext hfst
          have hs1 : d'.snd = ⟨bp1 W e, bp1_mem_realizationPoints W e⟩ := Subtype.ext hsnd
          let τ := unitInterval.symm r
          have hτ0 : (0 : ℝ) < τ := by change (0 : ℝ) < 1 - r; linarith
          have hτ1 : (τ : ℝ) < 1 := by change 1 - (r : ℝ) < 1; linarith
          refine hseg2 e τ hτ0 hτ1 ?_ ?_
          · have hsub : 1 - (τ : ℝ) = (r : ℝ) := by change 1 - (1 - (r : ℝ)) = r; ring
            rw [realizationMap_edgePoint, hf1, hs1, hsub, add_comm ((1 - (r : ℝ)) • _)]
            rfl
          · have heq' := hwitnessSymm (ratio1_lt_ratio2 W e) hfst.symm hsnd.symm
            convert heq' using 2
            ext
            dsimp only [τ]
            rw [unitInterval.coe_symm_eq]
            ring
        · have hf1 : d'.fst = ⟨vertex (edgeDartOfSym2 e).snd, vertex_mem_realizationPoints W _⟩ :=
            Subtype.ext hfst
          have hs1 : d'.snd = ⟨bp2 W e, bp2_mem_realizationPoints W e⟩ := Subtype.ext hsnd
          let τ := unitInterval.symm r
          have hτ0 : (0 : ℝ) < τ := by change (0 : ℝ) < 1 - r; linarith
          have hτ1 : (τ : ℝ) < 1 := by change 1 - (r : ℝ) < 1; linarith
          refine hseg3 e τ hτ0 hτ1 ?_ ?_
          · have hsub : 1 - (τ : ℝ) = (r : ℝ) := by change 1 - (1 - (r : ℝ)) = r; ring
            rw [realizationMap_edgePoint, hf1, hs1, hsub, add_comm ((1 - (r : ℝ)) • _)]
            rfl
          · have heq' := hwitnessSymm (ratio2_lt_one W e)
              (by rw [edgePoint_one, hfst]) hsnd.symm
            convert heq' using 2
            ext
            dsimp only [τ]
            rw [unitInterval.coe_symm_eq]
            change (1 - (1 - (r : ℝ))) * ratio2 W e + (1 - (r : ℝ)) =
              (1 - (r : ℝ)) * (1 : ℝ) + r * ratio2 W e
            ring

theorem realizationMap_injective [Finite V] (W : WeightedGraph V) :
    Function.Injective (realizationMap W) := by
  intro p₁ p₂ hp
  rcases realizationMap_classify W p₁ with
    ⟨v₁, hq₁, hk₁, hz₁⟩ | ⟨e₁, u₁, hu₁0, hu₁1, hq₁, hk₁, hb₁⟩
  · rcases realizationMap_classify W p₂ with
      ⟨v₂, hq₂, _, hz₂⟩ | ⟨e₂, u₂, hu₂0, hu₂1, _, _, hb₂⟩
    · have hv : vertexPos W v₁ 0 = vertexPos W v₂ 0 := by rw [← hz₁, hp, hz₂]
      by_contra hne
      have hv_ne : v₁ ≠ v₂ := fun h =>
        hne ((subdivideEquiv (vertex_mem_realizationPoints W)).injective (by rw [hq₁, hq₂, h]))
      exact vertexPos_apply_zero_ne W hv_ne hv
    · have hze : realizationMap W p₂ (Fin.succ (edgeEquiv W e₂)) = 0 := by
        rw [← hp]; exact hk₁ (edgeEquiv W e₂)
      have hw : 0 < W.weight e₂.1 := by
        simpa only [edgeDartOfSym2_edge] using W.dart_weight_pos (edgeDartOfSym2 e₂)
      rcases hb₂ with ⟨_, _, hval⟩ | ⟨_, _, hval, _⟩ | ⟨_, _, hval⟩
      · exact absurd (hval.symm.trans hze) (mul_pos hu₂0 hw).ne'
      · exact absurd (hval.symm.trans hze) (edgeLegHeight_pos W e₂).ne'
      · exact absurd (hval.symm.trans hze) (mul_pos (sub_pos.mpr hu₂1) hw).ne'
  · rcases realizationMap_classify W p₂ with
      ⟨v₂, _, hk₂, _⟩ | ⟨e₂, u₂, hu₂0, hu₂1, hq₂, hk₂, hb₂⟩
    · have hze : realizationMap W p₁ (Fin.succ (edgeEquiv W e₁)) = 0 := by
        rw [hp]; exact hk₂ (edgeEquiv W e₁)
      have hw : 0 < W.weight e₁.1 := by
        simpa only [edgeDartOfSym2_edge] using W.dart_weight_pos (edgeDartOfSym2 e₁)
      rcases hb₁ with ⟨_, _, hval⟩ | ⟨_, _, hval, _⟩ | ⟨_, _, hval⟩
      · exact absurd (hval.symm.trans hze) (mul_pos hu₁0 hw).ne'
      · exact absurd (hval.symm.trans hze) (edgeLegHeight_pos W e₁).ne'
      · exact absurd (hval.symm.trans hze) (mul_pos (sub_pos.mpr hu₁1) hw).ne'
    · have hw₁ : 0 < W.weight e₁.1 := by
        simpa only [edgeDartOfSym2_edge] using W.dart_weight_pos (edgeDartOfSym2 e₁)
      have hpos₁ : 0 < realizationMap W p₁ (Fin.succ (edgeEquiv W e₁)) := by
        rcases hb₁ with ⟨_, _, hval⟩ | ⟨_, _, hval, _⟩ | ⟨_, _, hval⟩
        · rw [hval]; exact mul_pos hu₁0 hw₁
        · rw [hval]; exact edgeLegHeight_pos W e₁
        · rw [hval]; exact mul_pos (sub_pos.mpr hu₁1) hw₁
      have he : e₁ = e₂ := by
        by_contra hne
        have hzero : realizationMap W p₁ (Fin.succ (edgeEquiv W e₁)) = 0 := by
          rw [hp]
          exact hk₂ (edgeEquiv W e₁) (fun h => hne (edgeEquiv W |>.injective h))
        exact hpos₁.ne' hzero
      subst he
      have hz0 : realizationMap W p₁ 0 = realizationMap W p₂ 0 := congrArg (· 0) hp
      have hze : realizationMap W p₁ (Fin.succ (edgeEquiv W e₁)) =
          realizationMap W p₂ (Fin.succ (edgeEquiv W e₁)) :=
        congrArg (· (Fin.succ (edgeEquiv W e₁))) hp
      have hne01 : vertexPos W (edgeDartOfSym2 e₁).fst 0 ≠
          vertexPos W (edgeDartOfSym2 e₁).snd 0 :=
        vertexPos_apply_zero_ne W (edgeDartOfSym2 e₁).fst_ne_snd
      have hd0 := (edgeChordDist_pos W e₁).ne'
      have h_fst_weight : ∀ (u : unitInterval),
          vertexPos W (edgeDartOfSym2 e₁).fst 0 =
            (1 - ((u : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁) *
                vertexPos W (edgeDartOfSym2 e₁).fst 0 +
              (((u : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁) *
                vertexPos W (edgeDartOfSym2 e₁).snd 0 →
          (u : ℝ) * W.weight e₁.1 = edgeLegHeight W e₁ := by
        intro u hxu
        have hlin : (((u : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁) *
            (vertexPos W (edgeDartOfSym2 e₁).snd 0 -
              vertexPos W (edgeDartOfSym2 e₁).fst 0) = 0 := by linarith
        have hfrac0 := (mul_eq_zero.mp hlin).resolve_right (sub_ne_zero.mpr hne01.symm)
        have := (div_eq_zero_iff.mp hfrac0).resolve_right hd0
        linarith
      have h_snd_weight : ∀ (u : unitInterval),
          vertexPos W (edgeDartOfSym2 e₁).snd 0 =
            (1 - ((u : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁) *
                vertexPos W (edgeDartOfSym2 e₁).fst 0 +
              (((u : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁) *
                vertexPos W (edgeDartOfSym2 e₁).snd 0 →
          (1 - (u : ℝ)) * W.weight e₁.1 = edgeLegHeight W e₁ := by
        intro u hxu
        have hlin :
            (1 - ((u : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁) *
              (vertexPos W (edgeDartOfSym2 e₁).snd 0 -
                vertexPos W (edgeDartOfSym2 e₁).fst 0) = 0 := by linarith
        have hfrac1 := (mul_eq_zero.mp hlin).resolve_right (sub_ne_zero.mpr hne01.symm)
        have hdiv :
            ((u : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁ = 1 := by linarith
        rw [div_eq_one_iff_eq hd0] at hdiv
        have hsum := two_mul_legHeight_add_chord W e₁
        linarith
      have hu_eq : u₁ = u₂ := by
        apply Subtype.ext
        rcases hb₁ with ⟨_, hx01, hze1⟩ | ⟨_, _, hze1, hx01⟩ | ⟨_, hx01, hze1⟩ <;>
          rcases hb₂ with ⟨_, hx02, hze2⟩ | ⟨_, _, hze2, hx02⟩ | ⟨_, hx02, hze2⟩
        · have hm : (u₁ : ℝ) * W.weight e₁.1 = (u₂ : ℝ) * W.weight e₁.1 := by
            rw [← hze1, ← hze2, hze]
          exact mul_right_cancel₀ hw₁.ne' hm
        · have hu2h := h_fst_weight u₂ (hx01.symm.trans (hz0.trans hx02))
          have hm : (u₁ : ℝ) * W.weight e₁.1 = (u₂ : ℝ) * W.weight e₁.1 := by
            rw [← hze1, hze, hze2, hu2h]
          exact mul_right_cancel₀ hw₁.ne' hm
        · exact absurd (hx01.symm.trans (hz0.trans hx02)) hne01
        · have hu1h := h_fst_weight u₁ (hx02.symm.trans (hz0.symm.trans hx01))
          have hm : (u₁ : ℝ) * W.weight e₁.1 = (u₂ : ℝ) * W.weight e₁.1 := by
            rw [hu1h, ← hze1, hze, hze2]
          exact mul_right_cancel₀ hw₁.ne' hm
        · have hx_eq :
              (1 - ((u₁ : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁) *
                vertexPos W (edgeDartOfSym2 e₁).fst 0 +
              (((u₁ : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁) *
                vertexPos W (edgeDartOfSym2 e₁).snd 0 =
              (1 - ((u₂ : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁) *
                vertexPos W (edgeDartOfSym2 e₁).fst 0 +
              (((u₂ : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁) *
                vertexPos W (edgeDartOfSym2 e₁).snd 0 :=
            hx01.symm.trans (hz0.trans hx02)
          have hlin :
              ((((u₁ : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁) -
               (((u₂ : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁)) *
              (vertexPos W (edgeDartOfSym2 e₁).snd 0 -
                vertexPos W (edgeDartOfSym2 e₁).fst 0) = 0 := by linarith
          have hfrac := (mul_eq_zero.mp hlin).resolve_right (sub_ne_zero.mpr hne01.symm)
          have hdiv : ((u₁ : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁ =
              ((u₂ : ℝ) * W.weight e₁.1 - edgeLegHeight W e₁) / edgeChordDist W e₁ := by
            linarith
          have hm : (u₁ : ℝ) * W.weight e₁.1 = (u₂ : ℝ) * W.weight e₁.1 := by
            have := (div_left_inj' hd0).mp hdiv
            linarith
          exact mul_right_cancel₀ hw₁.ne' hm
        · have h1w := h_snd_weight u₁ (hx02.symm.trans (hz0.symm.trans hx01))
          have hm : (1 - (u₁ : ℝ)) * W.weight e₁.1 = (1 - (u₂ : ℝ)) * W.weight e₁.1 := by
            rw [h1w, ← hze1, hze, hze2]
          linarith [mul_right_cancel₀ hw₁.ne' hm]
        · exact absurd (hx02.symm.trans (hz0.symm.trans hx01)) hne01
        · have h2w := h_snd_weight u₂ (hx01.symm.trans (hz0.trans hx02))
          have hm : (1 - (u₁ : ℝ)) * W.weight e₁.1 = (1 - (u₂ : ℝ)) * W.weight e₁.1 := by
            rw [← hze1, hze, hze2, h2w]
          linarith [mul_right_cancel₀ hw₁.ne' hm]
        · have hm : (1 - (u₁ : ℝ)) * W.weight e₁.1 = (1 - (u₂ : ℝ)) * W.weight e₁.1 := by
            rw [← hze1, ← hze2, hze]
          linarith [mul_right_cancel₀ hw₁.ne' hm]
      exact (subdivideEquiv (vertex_mem_realizationPoints W)).injective
        (by rw [hq₁, hq₂, hu_eq])

theorem realizationMap_isClosedEmbedding [Finite V] (W : WeightedGraph V) :
    Topology.IsClosedEmbedding (realizationMap W) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_realizationMap W) (realizationMap_injective W)
    fun _ hs => (hs.isCompact.image (continuous_realizationMap W)).isClosed

/-- The straight-edge Euclidean map on the original metric graph `MetricGraph W`, obtained by
precomposing `realizationMap W` with `(subdivideEquiv (vertex_mem_realizationPoints W)).symm`. -/
noncomputable def realizationFromGraph [Finite V] (W : WeightedGraph V) :
    MetricGraph W → EuclideanSpace ℝ (Fin (Nat.card W.graph.edgeSet + 1)) :=
  fun x => realizationMap W ((subdivideEquiv (vertex_mem_realizationPoints W)).symm x)

theorem realizationFromGraph_dist_le [Finite V] (W : WeightedGraph V) (x y : MetricGraph W) :
    dist (realizationFromGraph W x) (realizationFromGraph W y) ≤ dist x y := by
  dsimp only [realizationFromGraph]
  have h := realizationMap_dist_le W
    ((subdivideEquiv (vertex_mem_realizationPoints W)).symm x)
    ((subdivideEquiv (vertex_mem_realizationPoints W)).symm y)
  exact h.trans_eq ((subdivideEquiv (vertex_mem_realizationPoints W)).symm.isometry.dist_eq x y)

theorem continuous_realizationFromGraph [Finite V] (W : WeightedGraph V) :
    Continuous (realizationFromGraph W) :=
  Metric.continuous_iff.mpr fun x ε hε =>
    ⟨ε, hε, fun {y} hy => (realizationFromGraph_dist_le W y x).trans_lt hy⟩

theorem realizationFromGraph_injective [Finite V] (W : WeightedGraph V) :
    Function.Injective (realizationFromGraph W) :=
  (realizationMap_injective W).comp
    (subdivideEquiv (vertex_mem_realizationPoints W)).symm.injective

theorem realizationFromGraph_isClosedEmbedding [Finite V] (W : WeightedGraph V) :
    Topology.IsClosedEmbedding (realizationFromGraph W) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_realizationFromGraph W) (realizationFromGraph_injective W)
    fun _ hs => (hs.isCompact.image (continuous_realizationFromGraph W)).isClosed

/-- The weighted graph induced by the Euclidean chord lengths of `realizationMap W` on the
subdivided vertex set `realizationPoints W`. -/
noncomputable def realizationEuclideanGraph [Finite V] (W : WeightedGraph V) :
    WeightedGraph { z : MetricGraph W // z ∈ realizationPoints W } where
  graph := (realizationSubdivision W).graph
  weight := Sym2.lift ⟨fun x y => dist (realizationMap W (vertex x)) (realizationMap W (vertex y)),
    fun _ _ => dist_comm _ _⟩
  weight_pos {x y} hadj := by
    let d' : (realizationSubdivision W).graph.Dart := ⟨(x, y), hadj⟩
    change 0 < dist (realizationMap W (vertex d'.fst)) (realizationMap W (vertex d'.snd))
    rw [realizationMap_edge_dist]
    exact (realizationSubdivision W).dart_weight_pos d'
  connected := (realizationSubdivision W).connected

theorem realizationEuclideanGraph_weight_eq [Finite V] (W : WeightedGraph V)
    {e : Sym2 { z : MetricGraph W // z ∈ realizationPoints W }}
    (he : e ∈ (realizationSubdivision W).graph.edgeSet) :
    (realizationEuclideanGraph W).weight e = (realizationSubdivision W).weight e := by
  let d' : (realizationEuclideanGraph W).graph.Dart := edgeDartOfSym2 ⟨e, he⟩
  have heq : d'.edge = e := edgeDartOfSym2_edge ⟨e, he⟩
  rw [← heq]
  exact realizationMap_edge_dist W d'

private noncomputable def realizationSubEquiv [Finite V] (W : WeightedGraph V) :
    MetricGraph (realizationEuclideanGraph W) ≃ᵢ MetricGraph (realizationSubdivision W) := by
  have hwd : ∀ x y : { z : MetricGraph W // z ∈ realizationPoints W },
      vertexDist (realizationEuclideanGraph W).graph (realizationEuclideanGraph W).weight x y =
        vertexDist (realizationSubdivision W).graph (realizationSubdivision W).weight x y := by
    intro x y
    have hwl : ∀ {a b} (p : (realizationSubdivision W).graph.Walk a b),
        walkLength (realizationEuclideanGraph W).weight p =
          walkLength (realizationSubdivision W).weight p := by
      intro a b p
      induction p with
      | nil => rfl
      | cons h _ ih =>
        rw [walkLength_cons, walkLength_cons, ih,
          realizationEuclideanGraph_weight_eq W
            ((realizationSubdivision W).graph.mem_edgeSet.mpr h)]
    refine le_antisymm ?_ ?_
    · obtain ⟨p, -, hp⟩ := exists_isPath_walkLength_eq_vertexDist
        (realizationSubdivision W).weight_nonneg ((realizationSubdivision W).connected x y)
      rw [← hp, ← hwl p]
      exact vertexDist_le (realizationEuclideanGraph W).weight_nonneg p
    · obtain ⟨p, -, hp⟩ := exists_isPath_walkLength_eq_vertexDist
        (realizationEuclideanGraph W).weight_nonneg ((realizationEuclideanGraph W).connected x y)
      have hp' : walkLength (realizationSubdivision W).weight p =
          walkLength (realizationEuclideanGraph W).weight p := (hwl p).symm
      rw [← hp, ← hp']
      exact vertexDist_le (realizationSubdivision W).weight_nonneg p
  let f : MetricGraph (realizationEuclideanGraph W) → MetricGraph (realizationSubdivision W) :=
    lift (W := realizationEuclideanGraph W) (vertex (W := realizationSubdivision W))
      (fun d r => edgePoint (W := realizationSubdivision W) d r)
      (fun d => edgePoint_zero (W := realizationSubdivision W) d)
      (fun d => edgePoint_one (W := realizationSubdivision W) d)
      (fun d r => edgePoint_symm (W := realizationSubdivision W) d r)
  let g : MetricGraph (realizationSubdivision W) → MetricGraph (realizationEuclideanGraph W) :=
    lift (W := realizationSubdivision W) (vertex (W := realizationEuclideanGraph W))
      (fun d r => edgePoint (W := realizationEuclideanGraph W) d r)
      (fun d => edgePoint_zero (W := realizationEuclideanGraph W) d)
      (fun d => edgePoint_one (W := realizationEuclideanGraph W) d)
      (fun d r => edgePoint_symm (W := realizationEuclideanGraph W) d r)
  have hf_vertex : ∀ v, f (vertex v) = vertex v := fun v => lift_vertex _ _ _ _ _ v
  have hf_edge : ∀ (d : (realizationEuclideanGraph W).graph.Dart) (r : unitInterval),
      f (edgePoint d r) =
        edgePoint (W := realizationSubdivision W) ⟨d.1, d.2⟩ r :=
    fun d r => lift_edgePoint _ _ _ _ _ d r
  have hg_vertex : ∀ v, g (vertex v) = vertex v := fun v => lift_vertex _ _ _ _ _ v
  have hg_edge : ∀ (d : (realizationSubdivision W).graph.Dart) (r : unitInterval),
      g (edgePoint d r) =
        edgePoint (W := realizationEuclideanGraph W) ⟨d.1, d.2⟩ r :=
    fun d r => lift_edgePoint _ _ _ _ _ d r
  have hfg : ∀ x, f (g x) = x := fun x => by
    induction x using ind_simple with
    | vertex v => rw [hg_vertex, hf_vertex]
    | edgePoint d r => rw [hg_edge, hf_edge]
  have hgf : ∀ x, g (f x) = x := fun x => by
    induction x using ind_simple with
    | vertex v => rw [hf_vertex, hg_vertex]
    | edgePoint d r => rw [hf_edge, hg_edge]
  have hw_edge : ∀ (d : (realizationEuclideanGraph W).graph.Dart),
      (realizationEuclideanGraph W).weight d.edge =
        (realizationSubdivision W).weight
          (⟨d.1, d.2⟩ : (realizationSubdivision W).graph.Dart).edge :=
    fun d => realizationEuclideanGraph_weight_eq W d.edge_mem
  have hiso : Isometry f := Isometry.of_dist_eq fun x y => by
    induction x using ind_simple with
    | vertex u =>
      induction y using ind_simple with
      | vertex v => rw [hf_vertex, hf_vertex, dist_vertex, dist_vertex, hwd u v]
      | edgePoint d r =>
        rw [hf_vertex, hf_edge, dist_vertex_edgePoint, dist_vertex_edgePoint, hwd, hwd, hw_edge d]
    | edgePoint d₁ r₁ =>
      induction y using ind_simple with
      | vertex v =>
        rw [hf_edge, hf_vertex, dist_edgePoint_vertex, dist_edgePoint_vertex, hwd, hwd, hw_edge d₁]
      | edgePoint d₂ r₂ =>
        rw [hf_edge, hf_edge]
        by_cases he : d₁.edge = d₂.edge
        · rcases (dart_edge_eq_iff d₁ d₂).mp he with rfl | hsym
          · rw [dist_edgePoint_edgePoint_same, dist_edgePoint_edgePoint_same]
            simp only [hwd, hw_edge d₁]
          · subst hsym
            let d₂' : (realizationSubdivision W).graph.Dart := ⟨d₂.1, d₂.2⟩
            have hs_dart :
                (⟨d₂.symm.1, d₂.symm.2⟩ : (realizationSubdivision W).graph.Dart) = d₂'.symm := rfl
            have hws : (realizationEuclideanGraph W).weight d₂.symm.edge =
                (realizationSubdivision W).weight d₂'.symm.edge := hw_edge d₂.symm
            rw [hs_dart, ← edgePoint_symm d₂' r₂, ← edgePoint_symm d₂ r₂,
              dist_edgePoint_edgePoint_same, dist_edgePoint_edgePoint_same]
            simp only [hwd, hws]
            dsimp only [d₂', Dart.symm]
        · let d₁' : (realizationSubdivision W).graph.Dart := ⟨d₁.1, d₁.2⟩
          let d₂' : (realizationSubdivision W).graph.Dart := ⟨d₂.1, d₂.2⟩
          have he' : d₁'.edge ≠ d₂'.edge := he
          rw [dist_edgePoint_edgePoint_of_edge_ne he', dist_edgePoint_edgePoint_of_edge_ne he]
          simp only [hwd, hw_edge d₁, hw_edge d₂]
          dsimp only [d₁', d₂']
  exact IsometryEquiv.mk (Equiv.mk f g hgf hfg) hiso

/-- The metric graph of the Euclidean chord-weighted subdivision is globally isometric to the
original metric graph `MetricGraph W`. -/
noncomputable def realizationEuclideanEquiv [Finite V] (W : WeightedGraph V) :
    MetricGraph (realizationEuclideanGraph W) ≃ᵢ MetricGraph W :=
  (realizationSubEquiv W).trans (subdivideEquiv (vertex_mem_realizationPoints W))

theorem realizationMap_vertex_rational [Finite V] (W : WeightedGraph V)
    (hQ : ∀ e ∈ W.graph.edgeSet, ∃ q : ℚ, W.weight e = q)
    (x : { z : MetricGraph W // z ∈ realizationPoints W })
    (i : Fin (Nat.card W.graph.edgeSet + 1)) :
    ∃ q : ℚ, realizationMap W (vertex x) i = q := by
  classical
  have hvp_rat : ∀ v : V, ∃ q : ℚ, vertexPos W v i = q := by
    intro v
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
    · obtain ⟨q, hq⟩ := vertexSpacing_rational W hQ
      refine ⟨q * (vertexEquiv v : ℕ), ?_⟩
      rw [vertexPos_apply_zero, hq]
      push_cast
      rfl
    · refine ⟨0, ?_⟩
      rw [vertexPos_apply_succ, Rat.cast_zero]
  have hd0_rat : ∀ e : W.graph.edgeSet, ∃ q : ℚ, edgeChordDist W e = q := by
    intro e
    obtain ⟨qs, hqs⟩ := vertexSpacing_rational W hQ
    let a : ℤ := (vertexEquiv (edgeDartOfSym2 e).fst : ℕ)
    let b : ℤ := (vertexEquiv (edgeDartOfSym2 e).snd : ℕ)
    refine ⟨qs * |(a : ℚ) - b|, ?_⟩
    change dist (vertexPos W (edgeDartOfSym2 e).fst) (vertexPos W (edgeDartOfSym2 e).snd) = _
    rw [dist_vertexPos_eq, hqs]
    push_cast [a, b]
    rfl
  have hh_rat : ∀ e : W.graph.edgeSet, ∃ q : ℚ, edgeLegHeight W e = q := by
    intro e
    obtain ⟨qw, hqw⟩ := hQ e.1 e.2
    obtain ⟨qd, hqd⟩ := hd0_rat e
    refine ⟨(qw - qd) / 2, ?_⟩
    dsimp only [edgeLegHeight]
    rw [hqw, hqd]
    push_cast
    rfl
  have h_bp_rat : ∀ (v : V) (e : W.graph.edgeSet) (y : { z // z ∈ realizationPoints W }),
      realizationVertexPos W y =
        vertexPos W v +
          edgeLegHeight W e • EuclideanSpace.single (Fin.succ (edgeEquiv W e)) (1 : ℝ) →
      ∃ q : ℚ, realizationMap W (vertex y) i = q := by
    intro v e y hy
    obtain ⟨q1, hq1⟩ := hvp_rat v
    obtain ⟨qh, hqh⟩ := hh_rat e
    rw [realizationMap_vertex, hy]
    by_cases hi : i = Fin.succ (edgeEquiv W e)
    · subst hi
      refine ⟨q1 + qh, ?_⟩
      rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.single_eq_same, mul_one,
        hq1, hqh, Rat.cast_add]
    · refine ⟨q1, ?_⟩
      rw [PiLp.add_apply, PiLp.smul_apply, PiLp.single_eq_of_ne 2 hi, smul_zero, add_zero, hq1]
  have hx := x.2
  simp only [realizationPoints, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and] at hx
  rcases hx with (⟨v, hv⟩ | ⟨e, he⟩) | ⟨e, he⟩
  · have hsub : x = ⟨vertex v, hv ▸ x.2⟩ := Subtype.ext hv.symm
    rw [hsub, realizationMap_vertex, realizationVertexPos_vertex]
    exact hvp_rat v
  · have hsub : x = ⟨bp1 W e, he ▸ x.2⟩ := Subtype.ext he.symm
    rw [hsub]
    exact h_bp_rat (edgeDartOfSym2 e).fst e _ (realizationVertexPos_bp1 W e _)
  · have hsub : x = ⟨bp2 W e, he ▸ x.2⟩ := Subtype.ext he.symm
    rw [hsub]
    exact h_bp_rat (edgeDartOfSym2 e).snd e _ (realizationVertexPos_bp2 W e _)

end MetricGraph

end SimpleGraph
