/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/CycleDarts.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Cycle
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Darts along a cycle parameterization

This module describes how the arc-length parameterization `circleMap` of a cycle traverses the
darts of the graph, and how a shortest cycle sits inside `MetricGraph W`.

`circleMap_local_dichotomy` says that near every parameter `circleMap` either runs along a cycle
dart or passes a cycle vertex. The results here extend this local picture to whole darts: once
`circleMap` agrees with a dart near one interior parameter, it traverses the whole closed dart.
For a shortest cycle, two cycle vertices are joined along the cycle by a walk realizing their
distance, and leaving the cycle along a non-cycle edge moves away from every nearby cycle point.

## Main results

* `SimpleGraph.Walk.IsCycle.edge_eq_or_eq_of_fst_eq`: a vertex of a cycle meets at most two of
  its edges.
* `SimpleGraph.MetricGraph.circleMap_eq_edgePoint_of_eventually`: if `circleMap` runs along a dart
  near one interior parameter, it runs along the whole dart.
* `SimpleGraph.MetricGraph.circleMap_eq_edgePoint_of_local`,
  `SimpleGraph.MetricGraph.circleMap_eq_edgePoint_of_vertex`: the two cases of
  `circleMap_local_dichotomy` extended to whole darts.
* `SimpleGraph.MetricGraph.IsShortestCycle.exists_walk_dist_eq`: two vertices of a shortest cycle
  are joined by a walk along the cycle whose length is their distance.
* `SimpleGraph.MetricGraph.IsShortestCycle.dist_circleMap_lt_dist_edgePoint`: a point a short way
  along a non-cycle dart at a cycle vertex `v` is farther than `v` from every cycle point near `v`.
-/

public section

open scoped unitInterval Topology

namespace SimpleGraph

universe u

/-- A vertex of a cycle meets at most two of its edges: when two darts out of `v` carry distinct
cycle edges, every cycle edge at `v` is one of them. -/
theorem Walk.IsCycle.edge_eq_or_eq_of_fst_eq {V : Type u} {G : SimpleGraph V} {u : V}
    {c : G.Walk u u} (hc : c.IsCycle) {v : V} {d₁ d₂ d : G.Dart} (h₁ : d₁.fst = v)
    (h₂ : d₂.fst = v) (h : d.fst = v) (h₁₂ : d₁.edge ≠ d₂.edge) (hd₁ : d₁.edge ∈ c.edges)
    (hd₂ : d₂.edge ∈ c.edges) (hd : d.edge ∈ c.edges) : d.edge = d₁.edge ∨ d.edge = d₂.edge := by
  by_contra hne
  push Not at hne
  have hv : v ∈ c.support := h ▸ Walk.fst_mem_support_of_mem_edges c hd
  have hmem : ∀ e : G.Dart, e.fst = v → e.edge ∈ c.edges → e.snd ∈ c.toSubgraph.neighborSet v :=
    fun e he hec => by
      rw [Subgraph.mem_neighborSet, Walk.adj_toSubgraph_iff_mem_edges, ← he]
      exact hec
  have hsnd : ∀ {e e' : G.Dart}, e.fst = v → e'.fst = v → e.edge ≠ e'.edge → e.snd ≠ e'.snd :=
    fun he he' hee' hs =>
      hee' (congrArg Dart.edge (Dart.toProd_injective (Prod.ext (he.trans he'.symm) hs)))
  have h3 : 2 < (c.toSubgraph.neighborSet v).ncard :=
    (Set.two_lt_ncard_iff c.finite_neighborSet_toSubgraph).mpr
      ⟨d₁.snd, d₂.snd, d.snd, hmem d₁ h₁ hd₁, hmem d₂ h₂ hd₂, hmem d h hd, hsnd h₁ h₂ h₁₂,
        hsnd h₁ h (Ne.symm hne.1), hsnd h₂ h (Ne.symm hne.2)⟩
  rw [hc.ncard_neighborSet_toSubgraph_eq_two hv] at h3
  exact lt_irrefl _ h3

namespace MetricGraph

variable {V : Type u} {W : WeightedGraph V}

/-! ### Extending local agreement to whole darts -/

section DartExtension

variable [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀}

/-- If `circleMap hc` runs along the dart `d` at unit speed near one interior parameter `t₀`,
starting from the base parameter `a`, it runs along the whole closed dart:
`circleMap hc (a + t * W.weight d.edge) = edgePoint d t` for every `t : unitInterval`. -/
theorem circleMap_eq_edgePoint_of_eventually (hc : c.IsCycle) {d : W.graph.Dart} {a t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h : ∀ᶠ t in 𝓝 t₀, circleMap hc (a + t * W.weight d.edge) =
      edgePoint d (Set.projIcc 0 1 zero_le_one t)) (t : unitInterval) :
    circleMap hc (a + t * W.weight d.edge) = edgePoint d t := by
  have hw : 0 < W.weight d.edge := W.dart_weight_pos d
  let F : ℝ → MetricGraph W := fun u => circleMap hc (a + u * W.weight d.edge)
  let G : ℝ → MetricGraph W := fun u => edgePoint d (Set.projIcc 0 1 zero_le_one u)
  have hF : Continuous F :=
    (circleMap_continuous hc).comp (continuous_const.add (continuous_id.mul continuous_const))
  have hG : Continuous G := (continuous_edgePoint d).comp continuous_projIcc
  have hG_of_mem : ∀ {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1), G u = edgePoint d ⟨u, hu⟩ :=
    fun hu => by simp only [G, Set.projIcc_of_mem _ hu]
  let E : Set ℝ := Set.Ioo 0 1 ∩ {u | ∀ᶠ x in 𝓝 u, F x = G x}
  have hEopen : IsOpen E := isOpen_Ioo.inter isOpen_setOfPred_eventually_nhds
  have hEcl : closure E ∩ Set.Ioo 0 1 ⊆ E := by
    rintro u ⟨hucl, hu⟩
    by_contra huE
    have hFG : F u = G u :=
      closure_minimal (fun x (hx : x ∈ E) => hx.2.self_of_nhds) (isClosed_eq hF hG) hucl
    rw [hG_of_mem (Set.Ioo_subset_Icc_self hu)] at hFG
    rcases circleMap_local_dichotomy hc (a + u * W.weight d.edge) with
      ⟨d', t', δ', _, ht'0, ht'1, hδ', hmap'⟩ | ⟨v, _, _, _, _, _, _, _, _, _, hv, _, _⟩
    · -- Near `u`, `F` runs along `d'`, so it agrees with `d` either forwards or backwards.
      have hnear : ∀ᶠ x in 𝓝 u, (x - u) * W.weight d.edge ∈ Set.Ioo (-δ') δ' :=
        ((continuous_id.sub continuous_const).mul continuous_const).continuousAt.eventually_mem
          (Ioo_mem_nhds (by simp [hδ']) (by simp [hδ']))
      have hF_near : ∀ x, (x - u) * W.weight d.edge ∈ Set.Ioo (-δ') δ' →
          ∃ (h0 : 0 ≤ t' + (x - u) * W.weight d.edge / W.weight d'.edge)
            (h1 : t' + (x - u) * W.weight d.edge / W.weight d'.edge ≤ 1),
            F x = edgePoint d' ⟨_, h0, h1⟩ := fun x hx => by
        obtain ⟨_, _, h0, h1, hcm⟩ := hmap' _ (Set.Ioo_subset_Icc_self hx)
        refine ⟨h0, h1, ?_⟩
        rw [← hcm]
        change circleMap hc _ = _
        congr 1
        ring
      obtain ⟨_, _, hcm0⟩ := hF_near u (by rw [sub_self, zero_mul]; exact ⟨by linarith, hδ'⟩)
      have heq := hcm0.symm.trans hFG
      simp only [sub_self, zero_mul, zero_div, add_zero] at heq
      rcases edgePoint_eq_edgePoint_iff.mp heq with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, _, h⟩
      · exact absurd (congrArg Subtype.val h) ht'0.ne'
      · exact absurd (congrArg Subtype.val h) ht'1.ne
      rcases h with ⟨rfl, hte⟩ | ⟨rfl, hte⟩
      · -- Forwards: `F` agrees with `G` near `u`.
        have ht' : t' = u := congrArg Subtype.val hte
        refine huE ⟨hu, hnear.mono fun x hx => ?_⟩
        obtain ⟨h0, h1, hcm⟩ := hF_near x hx
        have hx' : t' + (x - u) * W.weight d'.edge / W.weight d'.edge = x := by
          rw [mul_div_cancel_right₀ _ hw.ne', ht']; ring
        rw [hcm, hG_of_mem (hx' ▸ ⟨h0, h1⟩ : x ∈ Set.Icc (0 : ℝ) 1)]
        exact congrArg (edgePoint d') (Subtype.ext hx')
      · -- Backwards: a point `x ≠ u` of `E` near `u` would be its own reflection.
        have ht' : t' = 1 - u := by
          simpa only [unitInterval.coe_symm_eq] using congrArg Subtype.val hte
        obtain ⟨x, hx, hxE⟩ := mem_closure_iff_nhds.mp hucl _ (hnear.and (Ioo_mem_nhds hu.1 hu.2))
        have hxu : x ≠ u := fun hxu => huE (hxu ▸ hxE)
        obtain ⟨h0, h1, hcm⟩ := hF_near x hx.1
        have hFx := hxE.2.self_of_nhds
        rw [hcm, hG_of_mem (Set.Ioo_subset_Icc_self hxE.1), ← edgePoint_symm' d] at hFx
        have hval := congrArg Subtype.val (edgePoint_injective d hFx)
        simp only [unitInterval.coe_symm_eq, Dart.edge_symm, mul_div_cancel_right₀ _ hw.ne',
          ht'] at hval
        exact hxu (by linarith)
    · have heq : edgePoint d ⟨u, _⟩ = vertex v := hFG.symm.trans hv
      rcases edgePoint_eq_vertex_iff.mp heq with ⟨h, _⟩ | ⟨h, _⟩
      · exact absurd (congrArg Subtype.val h) hu.1.ne'
      · exact absurd (congrArg Subtype.val h) hu.2.ne
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ E := by
    refine isPreconnected_Ioo.subset_left_of_subset_union hEopen
      (isOpen_Ioo.sdiff isClosed_closure : IsOpen (Set.Ioo (0 : ℝ) 1 \ closure E))
      (Set.disjoint_left.mpr fun x hx hx' => hx'.2 (subset_closure hx)) (fun x hx => ?_)
      ⟨t₀, ht₀, ht₀, h⟩
    by_cases hxcl : x ∈ closure E
    · exact Or.inl (hEcl ⟨hxcl, hx⟩)
    · exact Or.inr ⟨hx, hxcl⟩
  have hEq : Set.EqOn F G (Set.Icc 0 1) := by
    rw [← closure_Ioo zero_ne_one]
    exact Set.EqOn.closure (fun x hx => (hsub hx).2.self_of_nhds) hF hG
  exact (hEq t.2).trans (by simp only [G, Set.projIcc_val])

/-- The dart case of `circleMap_local_dichotomy` extends to the whole dart: if `circleMap hc` runs
along `d` near the interior parameter `t₀` at `s`, then
`circleMap hc (s + (t - t₀) * W.weight d.edge) = edgePoint d t` for every `t : unitInterval`. -/
theorem circleMap_eq_edgePoint_of_local (hc : c.IsCycle) {d : W.graph.Dart} {s t₀ δ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1) (hδ : 0 < δ)
    (hloc : ∀ r ∈ Set.Icc (-δ) δ,
      ∃ (h0 : 0 ≤ t₀ + r / W.weight d.edge) (h1 : t₀ + r / W.weight d.edge ≤ 1),
        circleMap hc (s + r) = edgePoint d ⟨t₀ + r / W.weight d.edge, h0, h1⟩)
    (t : unitInterval) :
    circleMap hc (s + (t - t₀) * W.weight d.edge) = edgePoint d t := by
  have hw : 0 < W.weight d.edge := W.dart_weight_pos d
  rw [← circleMap_eq_edgePoint_of_eventually hc (a := s - t₀ * W.weight d.edge) ht₀ ?_ t]
  · congr 1; ring
  have hnear : ∀ᶠ x in 𝓝 t₀, (x - t₀) * W.weight d.edge ∈ Set.Ioo (-δ) δ :=
    ((continuous_id.sub continuous_const).mul continuous_const).continuousAt.eventually_mem
      (Ioo_mem_nhds (by simp [hδ]) (by simp [hδ]))
  filter_upwards [hnear] with x hx
  obtain ⟨h0, h1, hcm⟩ := hloc _ (Set.Ioo_subset_Icc_self hx)
  have hx' : t₀ + (x - t₀) * W.weight d.edge / W.weight d.edge = x := by
    rw [mul_div_cancel_right₀ _ hw.ne']; ring
  rw [show s - t₀ * W.weight d.edge + x * W.weight d.edge = s + (x - t₀) * W.weight d.edge by ring,
    hcm, Set.projIcc_of_mem _ (hx' ▸ ⟨h0, h1⟩ : x ∈ Set.Icc (0 : ℝ) 1)]
  exact congrArg (edgePoint d) (Subtype.ext hx')

/-- The vertex case of `circleMap_local_dichotomy` extends to whole darts: if `circleMap hc`
arrives at `s` along `d₁` (traversed backwards) and leaves along `d₂`, it does so along both
whole darts. -/
theorem circleMap_eq_edgePoint_of_vertex (hc : c.IsCycle) {s δ : ℝ} {d₁ d₂ : W.graph.Dart}
    (hδ : 0 < δ)
    (hmap : ∀ r ∈ Set.Ioc 0 δ, r < W.weight d₁.edge ∧ r < W.weight d₂.edge ∧
      ∃ (h10 : 0 ≤ r / W.weight d₁.edge) (h11 : r / W.weight d₁.edge ≤ 1)
        (h20 : 0 ≤ r / W.weight d₂.edge) (h21 : r / W.weight d₂.edge ≤ 1),
        circleMap hc (s - r) = edgePoint d₁ ⟨r / W.weight d₁.edge, h10, h11⟩ ∧
        circleMap hc (s + r) = edgePoint d₂ ⟨r / W.weight d₂.edge, h20, h21⟩) :
    (∀ t : unitInterval, circleMap hc (s - t * W.weight d₁.edge) = edgePoint d₁ t) ∧
    (∀ t : unitInterval, circleMap hc (s + t * W.weight d₂.edge) = edgePoint d₂ t) := by
  have hw₁ : 0 < W.weight d₁.edge := W.dart_weight_pos d₁
  have hw₂ : 0 < W.weight d₂.edge := W.dart_weight_pos d₂
  obtain ⟨hr₁, hr₂, -⟩ := hmap (δ / 2) ⟨by positivity, by linarith⟩
  -- Near the parameter `t₀` with offset `δ / 2`, the offset `g x` stays in `(0, δ)`.
  have hnear : ∀ {g : ℝ → ℝ} {t₀ : ℝ}, Continuous g → g t₀ = δ / 2 →
      ∀ᶠ x in 𝓝 t₀, g x ∈ Set.Ioo 0 δ := fun hg hgt =>
    hg.continuousAt.eventually_mem (Ioo_mem_nhds (by linarith) (by linarith))
  constructor
  · intro t
    have key := circleMap_eq_edgePoint_of_eventually hc (d := d₁.symm) (a := s - W.weight d₁.edge)
      (t₀ := 1 - δ / 2 / W.weight d₁.edge)
      ⟨sub_pos.mpr ((div_lt_one hw₁).mpr hr₁), sub_lt_self 1 (by positivity)⟩ ?_
      (unitInterval.symm t)
    · rw [← edgePoint_symm d₁ t, ← key, Dart.edge_symm, unitInterval.coe_symm_eq]
      congr 1; ring
    filter_upwards [hnear (g := fun x => (1 - x) * W.weight d₁.edge)
      ((continuous_const.sub continuous_id).mul continuous_const)
      (by field_simp; ring)] with x hx
    obtain ⟨hlt, -, h10, h11, -, -, hcm, -⟩ := hmap _ (Set.Ioo_subset_Ioc_self hx)
    have hx' : 1 - (1 - x) * W.weight d₁.edge / W.weight d₁.edge = x := by
      rw [mul_div_cancel_right₀ _ hw₁.ne']; ring
    have hmem : x ∈ Set.Icc (0 : ℝ) 1 := by
      rw [← hx']; exact ⟨sub_nonneg.mpr h11, sub_le_self 1 h10⟩
    rw [Dart.edge_symm, show s - W.weight d₁.edge + x * W.weight d₁.edge =
      s - (1 - x) * W.weight d₁.edge by ring, hcm, ← edgePoint_symm' d₁,
      Set.projIcc_of_mem _ hmem]
    exact congrArg (edgePoint d₁) (Subtype.ext (by simp only [unitInterval.coe_symm_eq]; linarith))
  · refine circleMap_eq_edgePoint_of_eventually hc (a := s) (t₀ := δ / 2 / W.weight d₂.edge)
      ⟨by positivity, (div_lt_one hw₂).mpr hr₂⟩ ?_
    filter_upwards [hnear (g := fun x => x * W.weight d₂.edge)
      (continuous_id.mul continuous_const) (by field_simp)] with x hx
    obtain ⟨-, -, -, -, h20, h21, -, hcm⟩ := hmap _ (Set.Ioo_subset_Ioc_self hx)
    have hx' : x * W.weight d₂.edge / W.weight d₂.edge = x := mul_div_cancel_right₀ _ hw₂.ne'
    rw [hcm, Set.projIcc_of_mem _ (hx' ▸ ⟨h20, h21⟩ : x ∈ Set.Icc (0 : ℝ) 1)]
    exact congrArg (edgePoint d₂) (Subtype.ext hx')

end DartExtension

/-! ### Shortest cycles in the metric graph -/

section ShortestCycle

/-- Two vertices `v`, `x` of a shortest cycle `c` are joined by a walk using only edges of `c`
whose length is their distance in `MetricGraph W`. -/
theorem IsShortestCycle.exists_walk_dist_eq [Finite V] {v₀ : V} {c : W.graph.Walk v₀ v₀}
    (hs : IsShortestCycle W c) {v x : V} (hv : v ∈ c.support) (hx : x ∈ c.support) :
    ∃ p : W.graph.Walk v x,
      p.edges ⊆ c.edges ∧
        walkLength W.weight p = Dist.dist (vertex v : MetricGraph W) (vertex x) := by
  classical
  let L := walkLength W.weight c
  let cv := c.rotate v hv
  have hcv : cv.IsCycle := (c.isCycle_rotate hv).mpr hs.1
  have hperm : cv.edges.Perm c.edges := (c.rotate_edges v hv).perm
  have hLcv : walkLength W.weight cv = L := (hperm.map W.weight).sum_eq
  have hscv : IsShortestCycle W cv := ⟨hcv, fun {u} c' hc' => hLcv.symm ▸ hs.2 c' hc'⟩
  have hxcv : x ∈ cv.support := by
    cases hc_eq : c with
    | nil => exact absurd hs.1.not_nil (by simp [hc_eq])
    | @cons _ b _ hadj_c q_c =>
      have hxt : x ∈ c.support.tail := by
        rw [hc_eq, Walk.support_cons, List.tail_cons]
        rw [hc_eq, Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact Walk.end_mem_support q_c
        · exact hx
      exact List.mem_of_mem_tail ((c.support_rotate v hv).mem_iff.mpr hxt)
  let q₁ : W.graph.Walk v x := cv.takeUntil x hxcv
  let q₂ : W.graph.Walk x v := cv.dropUntil x hxcv
  have happ : q₁.append q₂ = cv := cv.take_spec hxcv
  let ℓ₁ : ℝ := walkLength W.weight q₁
  have hℓ₁_nn : 0 ≤ ℓ₁ := walkLength_nonneg W.weight W.weight_nonneg q₁
  have hℓ₂_nn : 0 ≤ walkLength W.weight q₂ := walkLength_nonneg W.weight W.weight_nonneg q₂
  have hsum : ℓ₁ + walkLength W.weight q₂ = L := by
    have h := congrArg (walkLength W.weight) happ
    rw [walkLength_append, hLcv] at h
    exact h
  have hwp : circleMap hcv ℓ₁ = vertex x := by
    rw [circleMap_eq_walkPoint hcv hℓ₁_nn (hLcv ▸ (by linarith : ℓ₁ ≤ L)), ← happ,
      walkPoint_append_of_le q₁ q₂ le_rfl, walkPoint_ge q₁ le_rfl]
  by_cases hhalf : ℓ₁ ≤ L / 2
  · refine ⟨q₁, fun e he => hperm.mem_iff.mp (Walk.edges_takeUntil_subset_edges cv hxcv he), ?_⟩
    rw [← circleMap_zero hcv, ← hwp]
    have hle : |0 - ℓ₁| ≤ walkLength W.weight cv / 2 := by
      rw [zero_sub, abs_neg, abs_of_nonneg hℓ₁_nn, hLcv]
      exact hhalf
    rw [circleMap_dist_eq_of_le hscv hle, zero_sub, abs_neg, abs_of_nonneg hℓ₁_nn]
  · refine ⟨q₂.reverse, fun e he => ?_, ?_⟩
    · rw [Walk.edges_reverse, List.mem_reverse] at he
      exact hperm.mem_iff.mp (Walk.edges_dropUntil_subset_edges cv hxcv he)
    · rw [walkLength_reverse, ← circleMap_zero hcv, ← hwp]
      have hper : circleMap hcv ℓ₁ = circleMap hcv (ℓ₁ - L) := by
        conv_lhs => rw [show ℓ₁ = (ℓ₁ - L) + (1 : ℤ) * walkLength W.weight cv by
          rw [hLcv]; push_cast; ring]
        exact circleMap_add_int_mul hcv (ℓ₁ - L) 1
      rw [hper]
      have hle : |0 - (ℓ₁ - L)| ≤ walkLength W.weight cv / 2 := by
        rw [zero_sub, neg_sub, abs_of_nonneg (by linarith), hLcv]
        linarith
      rw [circleMap_dist_eq_of_le hscv hle, zero_sub, neg_sub, abs_of_nonneg (by linarith)]
      linarith

/-- A detour that leaves a shortest cycle at `v` along a non-cycle dart `d`, follows a path to `x`
avoiding `v`, and returns to `v` along cycle edges is at least as long as the cycle. -/
private theorem walkLength_le_of_detour {v₀ v x : V} {c : W.graph.Walk v₀ v₀}
    (hs : IsShortestCycle W c) {d : W.graph.Dart} (hd_fst : d.fst = v) (hd_not : d.edge ∉ c.edges)
    (p_d : W.graph.Path d.snd x) (hv_not : v ∉ (p_d : W.graph.Walk d.snd x).support)
    (p_c : W.graph.Walk x v) (hpc_sub : p_c.edges ⊆ c.edges) :
    walkLength W.weight c ≤
      W.weight d.edge + walkLength W.weight (p_d : W.graph.Walk d.snd x) +
        walkLength W.weight p_c := by
  classical
  let q : W.graph.Path d.snd v := ((p_d : W.graph.Walk d.snd x).append p_c).toPath
  have hadj : W.graph.Adj v d.snd := hd_fst ▸ d.adj
  have hedge : s(v, d.snd) = d.edge := by rw [← hd_fst]; rfl
  have hnot_mem : s(v, d.snd) ∉ (q : W.graph.Walk d.snd v).edges := by
    intro hm
    have hm' := Walk.edges_toPath_subset_edges ((p_d : W.graph.Walk d.snd x).append p_c) hm
    rw [Walk.edges_append, List.mem_append, hedge] at hm'
    rcases hm' with hm1 | hm2
    · exact hv_not (hd_fst ▸ Walk.fst_mem_support_of_mem_edges _ hm1)
    · exact hd_not (hpc_sub hm2)
  let cyc : W.graph.Walk v v := Walk.cons hadj (q : W.graph.Walk d.snd v)
  have hle_c : walkLength W.weight c ≤ walkLength W.weight cyc :=
    hs.2 cyc (Path.cons_isCycle q hadj hnot_mem)
  have hq_le : walkLength W.weight (q : W.graph.Walk d.snd v) ≤
      walkLength W.weight (p_d : W.graph.Walk d.snd x) + walkLength W.weight p_c := by
    have h1 := walkLength_bypass_le W.weight W.weight_nonneg
      ((p_d : W.graph.Walk d.snd x).append p_c)
    rw [walkLength_append] at h1
    exact h1
  have hcyc_len : walkLength W.weight cyc =
      W.weight d.edge + walkLength W.weight (q : W.graph.Walk d.snd v) := by
    dsimp only [cyc]
    rw [walkLength_cons, hedge]
  linarith

/-- Leaving a shortest cycle `c` at a vertex `v` along a non-cycle dart `d` moves away from every
cycle point `b = circleMap hs.1 s` that is close to `v`: if `y` lies at offset
`t * W.weight d.edge > 0` strictly inside `d` and `2 * dist v b + t * W.weight d.edge` is less than
the length of `c`, then `dist v b < Dist.dist b y`. -/
theorem IsShortestCycle.dist_circleMap_lt_dist_edgePoint [Finite V] {v₀ : V}
    {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c) {v : V} (hv : v ∈ c.support)
    {d : W.graph.Dart} (hd_fst : d.fst = v) (hd_not : d.edge ∉ c.edges) {s : ℝ}
    (t : unitInterval) (ht0 : 0 < (t : ℝ)) (ht1 : (t : ℝ) * W.weight d.edge < W.weight d.edge)
    (hsum : 2 * Dist.dist (vertex v : MetricGraph W) (circleMap hs.1 s) +
      (t : ℝ) * W.weight d.edge < walkLength W.weight c) :
    Dist.dist (vertex v : MetricGraph W) (circleMap hs.1 s) <
      Dist.dist (circleMap hs.1 s) (edgePoint d t) := by
  classical
  let r := Dist.dist (vertex v : MetricGraph W) (circleMap hs.1 s)
  let r_y := (t : ℝ) * W.weight d.edge
  let w := W.weight d.edge
  let b := circleMap hs.1 s
  by_contra hle
  push Not at hle
  -- Reaching `d.snd` from `b` through a cycle vertex `x` within `off` of `b` would close a cycle
  -- shorter than `c`.
  have check_end : ∀ {x : V}, x ∈ c.support → ∀ off : ℝ, Dist.dist b (vertex x) ≤ off →
      off + vertexDist W.graph W.weight x d.snd + (w - r_y) ≤ r → False := by
    intro x hx off hbx hbound
    have htri : r ≤ off + Dist.dist (vertex v : MetricGraph W) (vertex x) := by
      have := dist_triangle (vertex v : MetricGraph W) (vertex x) b
      rw [_root_.dist_comm (vertex x) b] at this
      dsimp only [r]; linarith
    have hoff : 0 ≤ off := dist_nonneg.trans hbx
    obtain ⟨p_d, hp_d_path, hp_d_len⟩ :=
      exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected d.snd x)
    have hp_d_len' : walkLength W.weight (p_d : W.graph.Walk d.snd x) =
        vertexDist W.graph W.weight x d.snd := by
      rw [hp_d_len, ← dist_vertex, _root_.dist_comm, dist_vertex]
    by_cases hv_mem : v ∈ (p_d : W.graph.Walk d.snd x).support
    · let p_a := (p_d : W.graph.Walk d.snd x).takeUntil v hv_mem
      let p_b := (p_d : W.graph.Walk d.snd x).dropUntil v hv_mem
      have happ := (p_d : W.graph.Walk d.snd x).take_spec hv_mem
      have hlen_ab : walkLength W.weight p_a + walkLength W.weight p_b =
          vertexDist W.graph W.weight x d.snd := by
        rw [← walkLength_append, happ, hp_d_len']
      have hpa_nn : 0 ≤ walkLength W.weight p_a := walkLength_nonneg W.weight W.weight_nonneg p_a
      have hpb_ge : Dist.dist (vertex v : MetricGraph W) (vertex x) ≤ walkLength W.weight p_b := by
        rw [dist_vertex]
        exact vertexDist_le W.weight_nonneg p_b
      have hwr : r_y < w := ht1
      linarith
    · obtain ⟨p_c, hpc_sub, hpc_len⟩ := hs.exists_walk_dist_eq hv hx
      have hcyc_le := walkLength_le_of_detour hs hd_fst hd_not ⟨p_d, hp_d_path⟩ hv_mem
        p_c.reverse (fun e he => by
          rw [Walk.edges_reverse, List.mem_reverse] at he
          exact hpc_sub he)
      rw [walkLength_reverse, hpc_len, hp_d_len'] at hcyc_le
      have htri_vx : Dist.dist (vertex v : MetricGraph W) (vertex x) ≤ r + off := by
        have := dist_triangle (vertex v : MetricGraph W) b (vertex x)
        dsimp only [r]; linarith
      dsimp only [r, r_y, w] at hcyc_le hbound hsum
      linarith
  -- The cycle point `b` lies on some cycle dart.
  obtain ⟨d_b, t_b, hd_b_edges, hcb⟩ : ∃ (d_b : W.graph.Dart) (t_b : unitInterval),
      d_b.edge ∈ c.edges ∧ b = edgePoint d_b t_b := by
    rcases circleMap_local_dichotomy hs.1 s with
      ⟨d_b, t_b', δ_b, hd_b_mem, _, _, hδ_b, hmap_b⟩ |
      ⟨u_b, d_b1, _, _, _, hd_b1_fst, _, _, hd_b1_mem, _, hsb_u, _, _⟩
    · obtain ⟨_, _, h1, h2, hcm_b⟩ := hmap_b 0 ⟨by linarith, hδ_b.le⟩
      exact ⟨d_b, ⟨t_b' + 0 / W.weight d_b.edge, h1, h2⟩,
        List.mem_map.mpr ⟨d_b, hd_b_mem, rfl⟩, by simpa only [add_zero] using hcm_b⟩
    · exact ⟨d_b1, 0, hd_b1_mem, by rw [edgePoint_zero, hd_b1_fst]; exact hsb_u⟩
  have hne : d_b.edge ≠ d.edge := fun he => hd_not (he ▸ hd_b_edges)
  have hdist_by : Dist.dist b (edgePoint d t) =
      min (Dist.dist b (vertex d.fst) + (t : ℝ) * w)
        (Dist.dist b (vertex d.snd) + (1 - (t : ℝ)) * w) := by
    rw [hcb]
    exact dist_edgePoint_eq_min_of_edge_ne hne t_b t
  rw [hd_fst, _root_.dist_comm b (vertex v)] at hdist_by
  have hry_pos : 0 < r_y := mul_pos ht0 (W.dart_weight_pos d)
  have hsnd_le : Dist.dist b (vertex d.snd) + (w - r_y) ≤ r := by
    have h1w : (1 - (t : ℝ)) * w = w - r_y := by dsimp only [r_y, w]; ring
    rcases min_cases (r + (t : ℝ) * w) (Dist.dist b (vertex d.snd) + (1 - (t : ℝ)) * w) with
      ⟨h, -⟩ | ⟨h, -⟩
    · rw [hdist_by, h] at hle; dsimp only [r_y, w] at hry_pos hle; linarith
    · rw [hdist_by, h, h1w] at hle; exact hle
  rw [hcb, dist_edgePoint_vertex] at hsnd_le
  rcases min_cases ((t_b : ℝ) * W.weight d_b.edge + vertexDist W.graph W.weight d_b.fst d.snd)
      ((1 - (t_b : ℝ)) * W.weight d_b.edge + vertexDist W.graph W.weight d_b.snd d.snd) with
    ⟨h, -⟩ | ⟨h, -⟩
  · refine check_end (Walk.fst_mem_support_of_mem_edges c hd_b_edges) _ ?_ (h ▸ hsnd_le)
    rw [hcb, ← edgePoint_zero]
    exact (dist_edgePoint_self_le d_b t_b 0).trans_eq
      (by rw [Set.Icc.coe_zero, sub_zero, abs_of_nonneg t_b.2.1, mul_comm])
  · refine check_end (Walk.snd_mem_support_of_mem_edges c hd_b_edges) _ ?_ (h ▸ hsnd_le)
    rw [hcb, ← edgePoint_one]
    refine (dist_edgePoint_self_le d_b t_b 1).trans_eq ?_
    rw [Set.Icc.coe_one, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr t_b.2.2), mul_comm]

end ShortestCycle

end MetricGraph

end SimpleGraph
