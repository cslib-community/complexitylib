/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Cycle
public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Basic
public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Dictatorship
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Interval
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic.Linarith

/-!
# Schummer–Vohra cycle dictatorship on metric graphs

This module proves the shortest-cycle case of the cycle dictatorship theorem of
[SchummerVohra2002] (Theorem 2, p. 21 of the January 2001 author preprint, which covers every
cycle): any deterministic strategyproof and onto facility-location mechanism on a finite metric
graph `MetricGraph W` acts as a dictatorship on the points of any shortest cycle `c` (without
assuming the range stays in the cycle, and without assuming group strategyproofness). When
`W.graph` is itself isomorphic to a cycle graph `cycleGraph (n + 3)`, every deterministic
strategyproof onto mechanism is globally a dictatorship.

## Main results

* `Cslib.GameTheory.FacilityLocation.exists_cycleDictator_of_isShortestCycle`: cycle dictatorship
  on an explicit shortest cycle `c` ([SchummerVohra2002]).
* `Cslib.GameTheory.FacilityLocation.exists_cycleDictator_of_not_isAcyclic`: any finite cyclic
  metric graph has a shortest cycle on which every strategyproof onto rule is dictatorial.
* `Cslib.GameTheory.FacilityLocation.exists_dictatorship_of_cycleGraph`: on `cycleGraph (n + 3)`,
  every deterministic strategyproof onto rule is a global dictatorship.

## References

* [J. Schummer and R. V. Vohra, *Strategy-proof Location on a Network*][SchummerVohra2002]
-/

public section

namespace Cslib.GameTheory.FacilityLocation

open SimpleGraph SimpleGraph.MetricGraph

section CoalitionAndMerge

private theorem coalition_sp {ι G : Type*} [DecidableEq ι] [MetricSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] {f : (ι → G) → G}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof) (S : Finset ι) (a b : G)
    (x : ι → G) (hx : ∀ i ∈ S, x i = a) :
    dist a (f x) ≤ dist a (f fun i => if i ∈ S then b else x i) := by
  have hsp := (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp
  induction S using Finset.induction_on generalizing x with
  | empty =>
    simp only [Finset.notMem_empty, ↓reduceIte]
    exact le_rfl
  | @insert j T hjT ih =>
    have hxj : x j = a := hx j (Finset.mem_insert_self j T)
    let x' : ι → G := Function.update x j b
    have hx' : ∀ i ∈ T, x' i = a := by
      intro i hi
      have hij : i ≠ j := fun h => hjT (h ▸ hi)
      simpa only [x', Function.update_of_ne hij] using hx i (Finset.mem_insert_of_mem hi)
    have hstep : dist a (f x) ≤ dist a (f x') := by
      simpa only [hxj] using hsp x j b
    have htail : dist a (f x') ≤ dist a (f fun i => if i ∈ T then b else x' i) := ih x' hx'
    have hfun : (fun i => if i ∈ T then b else x' i) =
        (fun i => if i ∈ insert j T then b else x i) := by
      ext i
      by_cases hiT : i ∈ T
      · have hij : i ∈ insert j T := Finset.mem_insert_of_mem hiT
        simp only [hiT, hij, ↓reduceIte]
      · by_cases hij : i = j
        · subst hij
          simp only [hjT, Finset.mem_insert_self, ↓reduceIte, x', Function.update_self]
        · have hin : i ∉ insert j T := by simp [hij, hiT]
          simp only [hiT, hin, ↓reduceIte, x', Function.update_of_ne hij]
    rw [hfun] at htail
    exact hstep.trans htail

private theorem merge_isStrategyProof {ι ι' G : Type*} [Finite ι] [DecidableEq ι]
    [DecidableEq ι'] [MetricSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    {f : (ι → G) → G} (hf_sp : (Mechanism.deterministic f).IsStrategyProof) (g : ι → ι') :
    (Mechanism.deterministic (fun y : ι' → G => f (fun i => y (g i)))).IsStrategyProof := by
  let _ := Fintype.ofFinite ι
  rw [Mechanism.isStrategyProof_deterministic_iff]
  intro y j z
  let S : Finset ι := Finset.univ.filter fun i => g i = j
  let x : ι → G := fun i => y (g i)
  have hx : ∀ i ∈ S, x i = y j := fun i hi => by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [x, hi]
  have hfun : (fun i => Function.update y j z (g i)) = fun i => if i ∈ S then z else x i := by
    ext i
    by_cases hi : g i = j
    · have hiS : i ∈ S := by simp [S, hi]
      simp only [hi, hiS, Function.update_self, ↓reduceIte]
    · have hiS : i ∉ S := by simp [S, hi]
      simp only [hiS, ↓reduceIte, x, Function.update_of_ne hi]
  rw [hfun]
  exact coalition_sp hf_sp S (y j) z x hx

end CoalitionAndMerge

section CycleGeometry

private theorem exists_min_vertex_dist_pos {V : Type*} (W : WeightedGraph V) [Finite V] :
    ∃ vmin : ℝ, 0 < vmin ∧ ∀ u v : V, u ≠ v →
      vmin ≤ dist (vertex u : MetricGraph W) (vertex v) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl _ =>
    refine ⟨1, one_pos, fun u => (IsEmpty.false u).elim⟩
  | inr _ =>
    let _ : Fintype V := Fintype.ofFinite V
    let P := (Finset.univ : Finset (V × V)).filter fun p => p.1 ≠ p.2
    by_cases hP : P.Nonempty
    · refine ⟨P.inf' hP (fun p => dist (vertex p.1 : MetricGraph W) (vertex p.2)), ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact dist_pos.mpr (vertex_inj.ne.mpr hp)
      · intro u v hne
        have huv : (u, v) ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ (u, v), hne⟩
        exact Finset.inf'_le (fun p : V × V => dist (vertex p.1 : MetricGraph W) (vertex p.2)) huv
    · refine ⟨1, one_pos, fun u v hne => ?_⟩
      exfalso
      exact hP ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩⟩

private theorem walk_nodup_edges_at_end {V : Type*} {G : SimpleGraph V} {u v : V}
    (q : G.Walk u v) (hq : q.support.Nodup) :
    ∀ e₁ ∈ q.edges, v ∈ e₁ → ∀ e₂ ∈ q.edges, v ∈ e₂ → e₁ = e₂ := by
  match q with
  | .nil => simp
  | .cons hadj .nil => simp
  | .cons (v := b) hadj (.cons (v := d) hadj2 q'') =>
    have hq_tail : (Walk.cons hadj2 q'').support.Nodup := (List.nodup_cons.mp hq).2
    have hq_not : u ∉ (Walk.cons hadj2 q'').support := (List.nodup_cons.mp hq).1
    have hq'_not : b ∉ q''.support := (List.nodup_cons.mp hq_tail).1
    intro e₁ he₁ hv₁ e₂ he₂ hv₂
    have hac : u ≠ v := fun h => hq_not (h ▸ Walk.end_mem_support (.cons hadj2 q''))
    have hbc : b ≠ v := fun h => hq'_not (h ▸ Walk.end_mem_support q'')
    rw [Walk.edges_cons, List.mem_cons] at he₁ he₂
    rcases he₁ with rfl | he₁
    · rw [Sym2.mem_iff] at hv₁
      rcases hv₁ with h | h
      · exact absurd h.symm hac
      · exact absurd h.symm hbc
    · rcases he₂ with rfl | he₂
      · rw [Sym2.mem_iff] at hv₂
        rcases hv₂ with h | h
        · exact absurd h.symm hac
        · exact absurd h.symm hbc
      · exact walk_nodup_edges_at_end (.cons hadj2 q'') hq_tail e₁ he₁ hv₁ e₂ he₂ hv₂

open Classical in
private theorem edge_not_mem_cycle_of_ne {V : Type*} {G : SimpleGraph V} {v₀ : V}
    {c : G.Walk v₀ v₀} (hc : c.IsCycle) {v : V} (hv : v ∈ c.support)
    {d₁ d₂ d : G.Dart} (hd₁_fst : d₁.fst = v) (hd₂_fst : d₂.fst = v)
    (hd₁₂ : d₁.edge ≠ d₂.edge) (hd₁_mem : d₁.edge ∈ c.edges) (hd₂_mem : d₂.edge ∈ c.edges)
    (hd_fst : d.fst = v) (hnd₁ : d.edge ≠ d₁.edge) (hnd₂ : d.edge ≠ d₂.edge) :
    d.edge ∉ c.edges := by
  let cv := c.rotate v hv
  have hcv : cv.IsCycle := (c.isCycle_rotate hv).mpr hc
  have hperm : cv.edges.Perm c.edges := (c.rotate_edges v hv).perm
  cases hcv_eq : cv with
  | nil => exact absurd hcv.not_nil (by simp [hcv_eq])
  | @cons _ b _ hadj q =>
    have hnodup : q.support.Nodup := by
      have ht := hcv.support_nodup
      rw [hcv_eq, Walk.support_cons, List.tail_cons] at ht
      exact ht
    have h1cv : d₁.edge ∈ cv.edges := hperm.mem_iff.mpr hd₁_mem
    have h2cv : d₂.edge ∈ cv.edges := hperm.mem_iff.mpr hd₂_mem
    have h1v : v ∈ d₁.edge := hd₁_fst ▸ Sym2.mem_mk_left _ _
    have h2v : v ∈ d₂.edge := hd₂_fst ▸ Sym2.mem_mk_left _ _
    have hv_d : v ∈ d.edge := hd_fst ▸ Sym2.mem_mk_left _ _
    rw [hcv_eq, Walk.edges_cons, List.mem_cons] at h1cv h2cv
    intro hdc
    have hcv_d : d.edge ∈ cv.edges := hperm.mem_iff.mpr hdc
    rw [hcv_eq, Walk.edges_cons, List.mem_cons] at hcv_d
    rcases h1cv with h1a | h1b <;> rcases h2cv with h2a | h2b
    · exact hd₁₂ (h1a.trans h2a.symm)
    · rcases hcv_d with hda | hdb
      · exact hnd₁ (hda.trans h1a.symm)
      · exact hnd₂ (walk_nodup_edges_at_end q hnodup d.edge hdb hv_d d₂.edge h2b h2v)
    · rcases hcv_d with hda | hdb
      · exact hnd₂ (hda.trans h2a.symm)
      · exact hnd₁ (walk_nodup_edges_at_end q hnodup d.edge hdb hv_d d₁.edge h1b h1v)
    · exact hd₁₂ (walk_nodup_edges_at_end q hnodup d₁.edge h1b h1v d₂.edge h2b h2v)

open Classical in
private theorem exists_walk_in_cycle_length_eq_dist {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {v x : V} (hv : v ∈ c.support) (hx : x ∈ c.support) :
    ∃ (p : W.graph.Walk v x),
      p.edges ⊆ c.edges ∧ walkLength W.weight p = dist (vertex v : MetricGraph W) (vertex x) := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
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
      have hxt' : x ∈ cv.support.tail := (c.support_rotate v hv).mem_iff.mpr hxt
      exact List.mem_of_mem_tail hxt'
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
  have hℓ₁_le : ℓ₁ ≤ L := by linarith
  have hwp : circleMap hcv ℓ₁ = vertex x := by
    rw [circleMap_eq_walkPoint hcv hℓ₁_nn (hLcv ▸ hℓ₁_le), ← happ,
      walkPoint_append_of_le q₁ q₂ le_rfl, walkPoint_ge q₁ le_rfl]
  by_cases hhalf : ℓ₁ ≤ L / 2
  · refine ⟨q₁, fun e he => hperm.mem_iff.mp (Walk.edges_takeUntil_subset_edges cv hxcv he), ?_⟩
    rw [← circleMap_zero hcv, ← hwp]
    have hle : |0 - ℓ₁| ≤ walkLength W.weight cv / 2 := by
      rw [zero_sub, abs_neg, abs_of_nonneg hℓ₁_nn, hLcv]
      exact hhalf
    rw [circleMap_dist_eq_of_le hscv hle, zero_sub, abs_neg, abs_of_nonneg hℓ₁_nn]
  · have hlt : L / 2 < ℓ₁ := lt_of_not_ge hhalf
    refine ⟨q₂.reverse, fun e he => ?_, ?_⟩
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

open Classical in
private theorem exists_cycle_of_path_concat_cycle_walk {V : Type*} (W : WeightedGraph V)
    {v₀ v x : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {d : W.graph.Dart} (hd_fst : d.fst = v) (hd_not : d.edge ∉ c.edges)
    (p_d : W.graph.Path d.snd x) (hv_not : v ∉ (p_d : W.graph.Walk d.snd x).support)
    (p_c : W.graph.Walk x v) (hpc_sub : p_c.edges ⊆ c.edges) :
    walkLength W.weight c ≤
      W.weight d.edge + walkLength W.weight (p_d : W.graph.Walk d.snd x) +
        walkLength W.weight p_c := by
  let q : W.graph.Path d.snd v := ((p_d : W.graph.Walk d.snd x).append p_c).toPath
  have hadj : W.graph.Adj v d.snd := hd_fst ▸ d.adj
  have hnot_mem : s(v, d.snd) ∉ (q : W.graph.Walk d.snd v).edges := by
    intro hm
    have hm' := Walk.edges_toPath_subset_edges ((p_d : W.graph.Walk d.snd x).append p_c) hm
    rw [Walk.edges_append, List.mem_append] at hm'
    have hedge : s(v, d.snd) = d.edge := by rw [← hd_fst]; rfl
    rw [hedge] at hm'
    rcases hm' with hm1 | hm2
    · exact hv_not (hd_fst ▸ Walk.fst_mem_support_of_mem_edges _ hm1)
    · exact hd_not (hpc_sub hm2)
  let cyc : W.graph.Walk v v := Walk.cons hadj (q : W.graph.Walk d.snd v)
  have hcyc : cyc.IsCycle := Path.cons_isCycle q hadj hnot_mem
  have hle_c : walkLength W.weight c ≤ walkLength W.weight cyc := hs.2 cyc hcyc
  have hq_le : walkLength W.weight (q : W.graph.Walk d.snd v) ≤
      walkLength W.weight (p_d : W.graph.Walk d.snd x) + walkLength W.weight p_c := by
    have h1 : walkLength W.weight ((p_d : W.graph.Walk d.snd x).append p_c).bypass ≤
        walkLength W.weight ((p_d : W.graph.Walk d.snd x).append p_c) :=
      walkLength_bypass_le W.weight W.weight_nonneg _
    rw [walkLength_append] at h1
    exact h1
  have hcyc_len : walkLength W.weight cyc =
      W.weight d.edge + walkLength W.weight (q : W.graph.Walk d.snd v) := by
    dsimp only [cyc]
    rw [walkLength_cons]
    have hwe : W.weight s(v, d.snd) = W.weight d.edge := by rw [← hd_fst]; rfl
    rw [hwe]
  linarith

open Classical in
private theorem dist_third_dart_gt_of_circleMap {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {v : V} (hv : v ∈ c.support)
    {d : W.graph.Dart} (hd_fst : d.fst = v) (hd_not : d.edge ∉ c.edges)
    {s_b : ℝ}
    (t_y : unitInterval) (ht0 : 0 < (t_y : ℝ))
    (hry_lt : (t_y : ℝ) * W.weight d.edge < W.weight d.edge)
    (hsum_lt : 2 * dist (vertex v : MetricGraph W) (circleMap hs.1 s_b) +
      (t_y : ℝ) * W.weight d.edge < walkLength W.weight c) :
    dist (vertex v : MetricGraph W) (circleMap hs.1 s_b) <
      dist (circleMap hs.1 s_b) (edgePoint d t_y) := by
  let L := walkLength W.weight c
  let r := dist (vertex v : MetricGraph W) (circleMap hs.1 s_b)
  let r_y := (t_y : ℝ) * W.weight d.edge
  let w := W.weight d.edge
  let b := circleMap hs.1 s_b
  let y := edgePoint d t_y
  by_contra hle
  push Not at hle
  have check_end : ∀ {x : V} (hx : x ∈ c.support) (off : ℝ),
      0 ≤ off → dist b (vertex x) ≤ off → r ≤ off + dist (vertex v : MetricGraph W) (vertex x) →
      off + vertexDist W.graph W.weight x d.snd + (w - r_y) ≤ r → False := by
    intro x hx off hoff hbx htri hbound
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
      have hpb_ge : dist (vertex v : MetricGraph W) (vertex x) ≤ walkLength W.weight p_b := by
        rw [dist_vertex]
        exact vertexDist_le W.weight_nonneg p_b
      have hwr : r_y < w := hry_lt
      linarith
    · obtain ⟨p_c, hpc_sub, hpc_len⟩ := exists_walk_in_cycle_length_eq_dist W hs hv hx
      have hcyc_le := exists_cycle_of_path_concat_cycle_walk W hs hd_fst hd_not
        ⟨p_d, hp_d_path⟩ hv_mem p_c.reverse (fun e he => by
          rw [Walk.edges_reverse, List.mem_reverse] at he
          exact hpc_sub he)
      rw [walkLength_reverse, hpc_len, hp_d_len'] at hcyc_le
      have htri_vx : dist (vertex v : MetricGraph W) (vertex x) ≤ r + off := by
        calc dist (vertex v : MetricGraph W) (vertex x)
            ≤ dist (vertex v : MetricGraph W) b + dist b (vertex x) := dist_triangle _ _ _
          _ ≤ dist (vertex v : MetricGraph W) b + off := add_le_add le_rfl hbx
          _ = r + off := rfl
      dsimp only [L, r, r_y, w] at hcyc_le hbound hsum_lt
      linarith
  rcases circleMap_local_dichotomy hs.1 s_b with
    ⟨d_b, t_b', δ_b, hd_b_mem, ht0_b, ht1_b, hδ_b, hmap_b⟩ |
    ⟨u_b, d_b1, d_b2, _, hu_b_sup, _, _, _, _, _, hsb_u, _, _⟩
  · have h0b := hmap_b 0 ⟨by linarith, hδ_b.le⟩
    obtain ⟨_, _, h1, h2, hcm_b⟩ := h0b
    have hcb : b = edgePoint d_b ⟨t_b' + 0 / W.weight d_b.edge, h1, h2⟩ := by
      simpa only [add_zero] using hcm_b
    let t_b : unitInterval := ⟨t_b' + 0 / W.weight d_b.edge, h1, h2⟩
    have hd_b_edges : d_b.edge ∈ c.edges := List.mem_map.mpr ⟨d_b, hd_b_mem, rfl⟩
    have hne : d_b.edge ≠ d.edge := fun he => hd_not (he ▸ hd_b_edges)
    have hdist_by : dist b y =
        min (dist b (vertex d.fst) + (t_y : ℝ) * w)
          (dist b (vertex d.snd) + (1 - (t_y : ℝ)) * w) := by
      rw [hcb]
      exact dist_edgePoint_eq_min_of_edge_ne hne t_b t_y
    rw [hd_fst, _root_.dist_comm b (vertex v)] at hdist_by
    have hry_pos : 0 < r_y := mul_pos ht0 (W.dart_weight_pos d)
    have hfst_gt : r < r + (t_y : ℝ) * w := by dsimp only [r_y, w] at hry_pos ⊢; linarith
    have hsnd_le : dist b (vertex d.snd) + (1 - (t_y : ℝ)) * w ≤ r := by
      rcases le_total (r + (t_y : ℝ) * w) (dist b (vertex d.snd) + (1 - (t_y : ℝ)) * w)
          with h | h
      · rw [hdist_by, min_eq_left h] at hle
        linarith
      · rw [hdist_by, min_eq_right h] at hle
        exact hle
    have hdb_e : dist b (vertex d.snd) =
        min ((t_b : ℝ) * W.weight d_b.edge + vertexDist W.graph W.weight d_b.fst d.snd)
          ((1 - (t_b : ℝ)) * W.weight d_b.edge + vertexDist W.graph W.weight d_b.snd d.snd) := by
      rw [hcb]
      exact dist_edgePoint_vertex d_b t_b d.snd
    have hf_sup : d_b.fst ∈ c.support := Walk.fst_mem_support_of_mem_edges c hd_b_edges
    have hs_sup : d_b.snd ∈ c.support := Walk.snd_mem_support_of_mem_edges c hd_b_edges
    have h1w : (1 - (t_y : ℝ)) * w = w - r_y := by dsimp only [r_y, w]; ring
    rw [h1w] at hsnd_le
    rcases le_or_gt ((t_b : ℝ) * W.weight d_b.edge + vertexDist W.graph W.weight d_b.fst d.snd)
        ((1 - (t_b : ℝ)) * W.weight d_b.edge + vertexDist W.graph W.weight d_b.snd d.snd)
        with hm | hm
    · rw [hdb_e, min_eq_left hm] at hsnd_le
      have hbfst : dist b (vertex d_b.fst) ≤ (t_b : ℝ) * W.weight d_b.edge := by
        rw [hcb, dist_edgePoint_vertex]
        refine (min_le_left _ _).trans ?_
        rw [vertexDist_self W.weight_nonneg, add_zero]
      have htri : r ≤ (t_b : ℝ) * W.weight d_b.edge +
          dist (vertex v : MetricGraph W) (vertex d_b.fst) := by
        calc r = dist (vertex v : MetricGraph W) b := rfl
          _ ≤ dist (vertex v : MetricGraph W) (vertex d_b.fst) + dist (vertex d_b.fst) b :=
              dist_triangle _ _ _
          _ = dist (vertex d_b.fst) b + dist (vertex v : MetricGraph W) (vertex d_b.fst) :=
              add_comm _ _
          _ ≤ (t_b : ℝ) * W.weight d_b.edge +
              dist (vertex v : MetricGraph W) (vertex d_b.fst) := by
              rw [_root_.dist_comm (vertex d_b.fst) b]; linarith
      exact check_end hf_sup ((t_b : ℝ) * W.weight d_b.edge)
        (mul_nonneg t_b.2.1 (W.dart_weight_pos d_b).le) hbfst htri hsnd_le
    · rw [hdb_e, min_eq_right hm.le] at hsnd_le
      have hbsnd : dist b (vertex d_b.snd) ≤ (1 - (t_b : ℝ)) * W.weight d_b.edge := by
        rw [hcb, dist_edgePoint_vertex]
        refine (min_le_right _ _).trans ?_
        rw [vertexDist_self W.weight_nonneg, add_zero]
      have htri : r ≤ (1 - (t_b : ℝ)) * W.weight d_b.edge +
          dist (vertex v : MetricGraph W) (vertex d_b.snd) := by
        calc r = dist (vertex v : MetricGraph W) b := rfl
          _ ≤ dist (vertex v : MetricGraph W) (vertex d_b.snd) + dist (vertex d_b.snd) b :=
              dist_triangle _ _ _
          _ = dist (vertex d_b.snd) b + dist (vertex v : MetricGraph W) (vertex d_b.snd) :=
              add_comm _ _
          _ ≤ (1 - (t_b : ℝ)) * W.weight d_b.edge +
              dist (vertex v : MetricGraph W) (vertex d_b.snd) := by
              rw [_root_.dist_comm (vertex d_b.snd) b]; linarith
      exact check_end hs_sup ((1 - (t_b : ℝ)) * W.weight d_b.edge)
        (mul_nonneg (sub_nonneg.mpr t_b.2.2) (W.dart_weight_pos d_b).le) hbsnd htri hsnd_le
  · have hdist_by : dist b y =
        min (W.graph.vertexDist W.weight u_b d.fst + (t_y : ℝ) * w)
          (W.graph.vertexDist W.weight u_b d.snd + (1 - (t_y : ℝ)) * w) := by
      dsimp only [b, y, w]
      rw [hsb_u]
      exact dist_vertex_edgePoint u_b d t_y
    rw [hd_fst, ← dist_vertex, _root_.dist_comm (vertex u_b) (vertex v)] at hdist_by
    have hvu : dist (vertex v : MetricGraph W) (vertex u_b) = r := by
      dsimp only [r]; rw [← hsb_u]
    rw [hvu] at hdist_by
    have hry_pos : 0 < r_y := mul_pos ht0 (W.dart_weight_pos d)
    have h1w : (1 - (t_y : ℝ)) * w = w - r_y := by dsimp only [r_y, w]; ring
    have hsnd_le : vertexDist W.graph W.weight u_b d.snd + (w - r_y) ≤ r := by
      rcases le_total (r + (t_y : ℝ) * w)
          (vertexDist W.graph W.weight u_b d.snd + (1 - (t_y : ℝ)) * w) with h | h
      · rw [hdist_by, min_eq_left h] at hle
        dsimp only [r_y, w] at hry_pos; linarith
      · rw [hdist_by, min_eq_right h] at hle
        linarith [h1w]
    have htri : r ≤ 0 + dist (vertex v : MetricGraph W) (vertex u_b) := by rw [zero_add, hvu]
    have hbu0 : dist b (vertex u_b) ≤ 0 := by dsimp only [b]; rw [hsb_u, _root_.dist_self]
    exact check_end hu_b_sup 0 le_rfl hbu0 htri (by simpa only [zero_add] using hsnd_le)

private theorem edge_param_full {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle)
    {d : W.graph.Dart} {s₀ t₀ : ℝ} (ht0_pos : 0 < t₀) (ht0_lt : t₀ < 1)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hloc : ∀ r ∈ Set.Icc (-δ₀) δ₀,
      ∃ (h0 : 0 ≤ t₀ + r / W.weight d.edge) (h1 : t₀ + r / W.weight d.edge ≤ 1),
        circleMap hc (s₀ + r) = edgePoint d ⟨t₀ + r / W.weight d.edge, h0, h1⟩) :
    ∀ t : ℝ, ∀ (h0 : 0 < t) (h1 : t < 1),
      circleMap hc (s₀ + (t - t₀) * W.weight d.edge) = edgePoint d ⟨t, h0.le, h1.le⟩ := by
  let w := W.weight d.edge
  have hw : 0 < w := W.dart_weight_pos d
  let E : Set ℝ := { t | ∃ (h0 : 0 < t) (h1 : t < 1) (δ : ℝ), 0 < δ ∧
    ∀ u, |u - t| < δ → ∀ (hu0 : 0 < u) (hu1 : u < 1),
      circleMap hc (s₀ + (u - t₀) * w) = edgePoint d ⟨u, hu0.le, hu1.le⟩ }
  have hopenE : IsOpen E := by
    rw [Metric.isOpen_iff]
    rintro t ⟨ht0, ht1, δ, hδ, hE⟩
    refine ⟨min δ (min t (1 - t)), by positivity, fun u hu_ball => ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hu_ball
    have hu0 : 0 < u := by
      linarith [(abs_lt.mp hu_ball).1, min_le_right δ (min t (1 - t)), min_le_left t (1 - t)]
    have hu1 : u < 1 := by
      linarith [(abs_lt.mp hu_ball).2, min_le_right δ (min t (1 - t)), min_le_right t (1 - t)]
    let η := δ - |u - t|
    have hη : 0 < η := sub_pos.mpr (lt_of_lt_of_le hu_ball (min_le_left _ _))
    refine ⟨hu0, hu1, η, hη, fun v hvu hv0 hv1 => hE v ?_ hv0 hv1⟩
    calc |v - t| ≤ |v - u| + |u - t| := abs_sub_le v u t
      _ < η + |u - t| := by linarith
      _ = δ := sub_add_cancel δ |u - t|
  have hclosed_sub : closure E ∩ Set.Ioo (0 : ℝ) 1 ⊆ E := by
    rintro t ⟨ht_cl, ht0, ht1⟩
    have htE : circleMap hc (s₀ + (t - t₀) * w) = edgePoint d ⟨t, ht0.le, ht1.le⟩ := by
      rw [Metric.mem_closure_iff] at ht_cl
      have hcont : Continuous (fun u : ℝ => circleMap hc (s₀ + (u - t₀) * w)) :=
        (circleMap_continuous hc).comp
          (continuous_const.add ((continuous_id.sub continuous_const).mul continuous_const))
      rw [continuous_iff_continuousAt] at hcont
      by_contra hne
      let dgap := dist (circleMap hc (s₀ + (t - t₀) * w)) (edgePoint d ⟨t, ht0.le, ht1.le⟩)
      have hgap : 0 < dgap := dist_pos.mpr hne
      obtain ⟨δ₁, hδ₁, hball⟩ :=
        Metric.continuousAt_iff.mp (hcont t) (dgap / 3) (by linarith)
      obtain ⟨u, huE, hut⟩ :=
        ht_cl (min δ₁ (dgap / (3 * w))) (by positivity)
      rw [Real.dist_eq, abs_sub_comm] at hut
      obtain ⟨hu0, hu1, δu, hδu, hEu⟩ := huE
      have huc := hEu u (by simp [hδu]) hu0 hu1
      have h1 : dist (circleMap hc (s₀ + (u - t₀) * w))
          (circleMap hc (s₀ + (t - t₀) * w)) < dgap / 3 :=
        hball (lt_of_lt_of_le hut (min_le_left _ _))
      have h2 : dist (edgePoint d ⟨u, hu0.le, hu1.le⟩) (edgePoint d ⟨t, ht0.le, ht1.le⟩) <
          dgap / 3 := by
        calc dist (edgePoint d ⟨u, hu0.le, hu1.le⟩) (edgePoint d ⟨t, ht0.le, ht1.le⟩)
            ≤ w * |u - t| := dist_edgePoint_self_le d _ _
          _ < w * (dgap / (3 * w)) :=
              mul_lt_mul_of_pos_left (lt_of_lt_of_le hut (min_le_right _ _)) hw
          _ = dgap / 3 := by field_simp [hw.ne']
      rw [huc] at h1
      have htri := dist_triangle_left (circleMap hc (s₀ + (t - t₀) * w))
        (edgePoint d ⟨t, ht0.le, ht1.le⟩) (edgePoint d ⟨u, hu0.le, hu1.le⟩)
      dsimp only [dgap] at h1 h2
      change dgap ≤ _ at htri
      linarith
    let s₁ := s₀ + (t - t₀) * w
    rcases circleMap_local_dichotomy hc s₁ with
      ⟨d', t', δ', _, ht'0, ht'1, hδ', hmap'⟩ |
      ⟨v, _, _, _, _, _, _, _, _, _, hsv, _, _⟩
    · obtain ⟨_, _, _, _, hcm'⟩ := hmap' 0 ⟨by linarith, hδ'.le⟩
      simp only [add_zero, zero_div] at hcm'
      have heq : edgePoint d' ⟨t', ht'0.le, ht'1.le⟩ =
          edgePoint d ⟨t, ht0.le, ht1.le⟩ := hcm'.symm.trans htE
      rw [edgePoint_eq_edgePoint_iff] at heq
      have hde_cases : (d' = d ∧ t' = t) ∨ (d' = d.symm ∧ t' = 1 - t) := by
        rcases heq with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, _, h⟩
        · have : t' = 0 := congrArg Subtype.val h; linarith
        · have : t' = 1 := congrArg Subtype.val h; linarith
        · rcases h with ⟨rfl, hte⟩ | ⟨rfl, hte⟩
          · left; exact ⟨rfl, congrArg Subtype.val hte⟩
          · right
            exact ⟨rfl, by simpa only [unitInterval.coe_symm_eq] using congrArg Subtype.val hte⟩
      rcases hde_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨ht0, ht1, δ' / w, div_pos hδ' hw, fun u hut hu0 hu1 => ?_⟩
        let r := (u - t') * w
        have hr : r ∈ Set.Icc (-δ') δ' := by
          rw [Set.mem_Icc, ← abs_le, abs_mul, abs_of_pos hw]
          exact (lt_div_iff₀ hw).mp hut |>.le
        obtain ⟨_, _, _, _, hcm_u⟩ := hmap' r hr
        have hs_eq : s₀ + (u - t₀) * w = s₁ + r := by dsimp only [s₁, r]; ring
        rw [hs_eq, hcm_u]
        congr 1
        ext
        dsimp only [r, w]
        field_simp [(W.dart_weight_pos d').ne']
        ring
      · exfalso
        rw [Metric.mem_closure_iff] at ht_cl
        let η := min (δ' / w) (min t (1 - t))
        have hη : 0 < η := by positivity
        obtain ⟨u₀, hu₀E, hu₀t⟩ := ht_cl (η / 2) (by positivity)
        rw [Real.dist_eq, abs_sub_comm] at hu₀t
        obtain ⟨hu₀0, hu₀1, δu₀, hδu₀, hEu₀⟩ := hu₀E
        let s_step := min (δu₀ / 2) (η / 2)
        have hs_step : 0 < s_step := by positivity
        let u := if u₀ = t then t + s_step else u₀
        have hu_ne : u ≠ t := by
          by_cases h : u₀ = t
          · simp [u, h]; linarith
          · simp [u, h]
        have hu0 : 0 < u := by
          by_cases h : u₀ = t
          · simp only [u, h, ↓reduceIte]
            have := min_le_right (δu₀ / 2) (η / 2)
            have := min_le_right (δ' / w) (min t (1 - t))
            have := min_le_left t (1 - t)
            linarith
          · simp [u, h, hu₀0]
        have hu1 : u < 1 := by
          by_cases h : u₀ = t
          · simp only [u, h, ↓reduceIte]
            have h1 : s_step ≤ η / 2 := min_le_right _ _
            have h2 : η ≤ min t (1 - t) := min_le_right _ _
            have h3 : min t (1 - t) ≤ 1 - t := min_le_right _ _
            linarith
          · simp [u, h, hu₀1]
        have hut : |u - t| < η := by
          by_cases h : u₀ = t
          · simp only [u, h, ↓reduceIte, add_sub_cancel_left, abs_of_pos hs_step]
            have : s_step ≤ η / 2 := min_le_right _ _
            linarith
          · simp only [u, h, ↓reduceIte]
            linarith
        have huc1 : circleMap hc (s₀ + (u - t₀) * w) = edgePoint d ⟨u, hu0.le, hu1.le⟩ := by
          by_cases h : u₀ = t
          · refine hEu₀ u ?_ hu0 hu1
            simp only [u, h, ↓reduceIte, add_sub_cancel_left, abs_of_pos hs_step]
            have : s_step ≤ δu₀ / 2 := min_le_left _ _
            linarith
          · simp only [u, h, ↓reduceIte]
            exact hEu₀ u₀ (by simp [hδu₀]) hu₀0 hu₀1
        let r := (u - t) * w
        have hr : r ∈ Set.Icc (-δ') δ' := by
          rw [Set.mem_Icc, ← abs_le, abs_mul, abs_of_pos hw]
          exact (lt_div_iff₀ hw).mp (lt_of_lt_of_le hut (min_le_left _ _)) |>.le
        obtain ⟨_, _, h1', h2', hcm_u⟩ := hmap' r hr
        have hs_eq : s₀ + (u - t₀) * w = s₁ + r := by dsimp only [s₁, r]; ring
        rw [hs_eq, hcm_u] at huc1
        have heq_u := edgePoint_eq_edgePoint_iff.mp huc1
        have hv_eq : 1 - (1 - t + r / w) = u := by
          rcases heq_u with ⟨_, ⟨hu_e, _⟩ | ⟨hu_e, _⟩⟩ | ⟨_, ⟨hu_e, _⟩ | ⟨hu_e, _⟩⟩ |
              ⟨_, _, _, _, h⟩
          · have : u = 0 := congrArg Subtype.val hu_e; linarith
          · have : u = 1 := congrArg Subtype.val hu_e; linarith
          · have : u = 0 := congrArg Subtype.val hu_e; linarith
          · have : u = 1 := congrArg Subtype.val hu_e; linarith
          · rcases h with ⟨hsym, _⟩ | ⟨_, hte⟩
            · exact absurd hsym d.symm_ne
            · have := congrArg Subtype.val hte
              simp only [unitInterval.coe_symm_eq, Dart.edge_symm] at this
              change 1 - t + r / w = 1 - u at this
              linarith
        have hu_t : u = t := by
          dsimp only [r, w] at hv_eq
          field_simp [(W.dart_weight_pos d).ne'] at hv_eq
          linarith
        exact hu_ne hu_t
    · exfalso
      have heq : edgePoint d ⟨t, ht0.le, ht1.le⟩ = vertex v := htE.symm.trans hsv
      rw [edgePoint_eq_vertex_iff] at heq
      rcases heq with ⟨h, _⟩ | ⟨h, _⟩
      · have : t = 0 := congrArg Subtype.val h; linarith
      · have : t = 1 := congrArg Subtype.val h; linarith
  let F : Set ℝ := Set.Ioo (0 : ℝ) 1 \ closure E
  have hopenF : IsOpen F := isOpen_Ioo.sdiff isClosed_closure
  have hdisj : Disjoint E F := Set.disjoint_left.mpr fun t htE ⟨_, hnc⟩ => hnc (subset_closure htE)
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ E ∪ F := fun t ht => by
    by_cases h : t ∈ closure E
    · exact Or.inl (hclosed_sub ⟨h, ht⟩)
    · exact Or.inr ⟨ht, h⟩
  have hne : (Set.Ioo (0 : ℝ) 1 ∩ E).Nonempty := by
    refine ⟨t₀, ⟨ht0_pos, ht0_lt⟩, ht0_pos, ht0_lt, δ₀ / w, div_pos hδ₀ hw, fun u hut _ _ => ?_⟩
    let r := (u - t₀) * w
    have hr : r ∈ Set.Icc (-δ₀) δ₀ := by
      rw [Set.mem_Icc, ← abs_le, abs_mul, abs_of_pos hw]
      exact (lt_div_iff₀ hw).mp hut |>.le
    obtain ⟨h0, h1, hcm⟩ := hloc r hr
    have hs_eq : s₀ + (u - t₀) * w = s₀ + r := rfl
    rw [hs_eq, hcm]
    congr 1
    ext
    dsimp only [r, w]
    field_simp [(W.dart_weight_pos d).ne']
    ring
  have hIoo : Set.Ioo (0 : ℝ) 1 ⊆ E :=
    isPreconnected_Ioo.subset_left_of_subset_union hopenE hopenF hdisj hsub hne
  intro t h0 h1
  obtain ⟨_, _, δ, hδ, hE⟩ := hIoo ⟨h0, h1⟩
  exact hE t (by simp [hδ]) h0 h1

private theorem vertex_param_full {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle)
    {s_v : ℝ} {v : V} {d₁ d₂ : W.graph.Dart}
    (hd₁_fst : d₁.fst = v) (hd₂_fst : d₂.fst = v)
    (hs_v : circleMap hc s_v = vertex v)
    (δ₁ : ℝ) (hδ₁ : 0 < δ₁)
    (hmap : ∀ r ∈ Set.Ioc 0 δ₁, r < W.weight d₁.edge ∧ r < W.weight d₂.edge ∧
      ∃ (h10 : 0 ≤ r / W.weight d₁.edge) (h11 : r / W.weight d₁.edge ≤ 1)
        (h20 : 0 ≤ r / W.weight d₂.edge) (h21 : r / W.weight d₂.edge ≤ 1),
        circleMap hc (s_v - r) = edgePoint d₁ ⟨r / W.weight d₁.edge, h10, h11⟩ ∧
        circleMap hc (s_v + r) = edgePoint d₂ ⟨r / W.weight d₂.edge, h20, h21⟩) :
    (∀ r : ℝ, ∀ (h0 : 0 < r) (hr : r < W.weight d₁.edge),
      circleMap hc (s_v - r) = edgePoint d₁ ⟨r / W.weight d₁.edge,
        div_nonneg h0.le (W.dart_weight_pos d₁).le,
        (div_le_one (W.dart_weight_pos d₁)).mpr hr.le⟩) ∧
    (∀ r : ℝ, ∀ (h0 : 0 < r) (hr : r < W.weight d₂.edge),
      circleMap hc (s_v + r) = edgePoint d₂ ⟨r / W.weight d₂.edge,
        div_nonneg h0.le (W.dart_weight_pos d₂).le,
        (div_le_one (W.dart_weight_pos d₂)).mpr hr.le⟩) := by
  let _ := hd₁_fst
  let _ := hd₂_fst
  let _ := hs_v
  have hw1 : 0 < W.weight d₁.edge := W.dart_weight_pos d₁
  have hw2 : 0 < W.weight d₂.edge := W.dart_weight_pos d₂
  let r₀ := min (δ₁ / 2) (min (W.weight d₁.edge / 2) (W.weight d₂.edge / 2))
  have hr₀_pos : 0 < r₀ := by positivity
  have hr₀_mem : r₀ ∈ Set.Ioc 0 δ₁ := ⟨hr₀_pos, (min_le_left _ _).trans (by linarith)⟩
  obtain ⟨hr1, hr2, h10, h11, h20, h21, hcm1, hcm2⟩ := hmap r₀ hr₀_mem
  refine ⟨fun r h0 hr => ?_, fun r h0 hr => ?_⟩
  · let t₀ := r₀ / W.weight d₁.edge
    have ht₀_pos : 0 < t₀ := div_pos hr₀_pos hw1
    have ht₀_lt : t₀ < 1 := (div_lt_one hw1).mpr hr1
    let t := r / W.weight d₁.edge
    have ht_pos : 0 < t := div_pos h0 hw1
    have ht_lt : t < 1 := (div_lt_one hw1).mpr hr
    let δloc := min (r₀ / 2) ((W.weight d₁.edge - r₀) / 2)
    have hδloc : 0 < δloc := by
      have : r₀ < W.weight d₁.edge := hr1
      positivity
    have hloc1 : ∀ ρ ∈ Set.Icc (-δloc) δloc,
        ∃ (h0' : 0 ≤ (1 - t₀) + ρ / W.weight d₁.symm.edge)
          (h1' : (1 - t₀) + ρ / W.weight d₁.symm.edge ≤ 1),
          circleMap hc ((s_v - r₀) + ρ) =
            edgePoint d₁.symm ⟨(1 - t₀) + ρ / W.weight d₁.symm.edge, h0', h1'⟩ := by
      intro ρ hρ
      have hr'_pos : 0 < r₀ - ρ := by
        linarith [hρ.2, min_le_left (r₀ / 2) ((W.weight d₁.edge - r₀) / 2)]
      have hr'_le : r₀ - ρ ≤ δ₁ := by
        have h1' : r₀ ≤ δ₁ / 2 := min_le_left _ _
        have h2' : -δloc ≤ ρ := hρ.1
        have h3' : δloc ≤ r₀ / 2 := min_le_left _ _
        linarith
      obtain ⟨h10', h11', _, _, hcm', _⟩ := (hmap (r₀ - ρ) ⟨hr'_pos, hr'_le⟩).2.2
      have heq0 : (1 - t₀) + ρ / W.weight d₁.symm.edge = 1 - (r₀ - ρ) / W.weight d₁.edge := by
        simp only [Dart.edge_symm, t₀]
        field_simp [hw1.ne']
        ring
      have h0' : 0 ≤ (1 - t₀) + ρ / W.weight d₁.symm.edge := by linarith
      have h1' : (1 - t₀) + ρ / W.weight d₁.symm.edge ≤ 1 := by linarith
      refine ⟨h0', h1', ?_⟩
      rw [show (s_v - r₀) + ρ = s_v - (r₀ - ρ) by ring, hcm', ← edgePoint_symm d₁]
      congr 1
      ext
      simp only [unitInterval.coe_symm_eq]
      exact heq0.symm
    have hfull := edge_param_full W hc (d := d₁.symm) (s₀ := s_v - r₀)
      (sub_pos.mpr ht₀_lt) (sub_lt_self 1 ht₀_pos) hδloc hloc1 (1 - t) (sub_pos.mpr ht_lt)
      (sub_lt_self 1 ht_pos)
    have hs_eq : s_v - r₀ + (1 - t - (1 - t₀)) * W.weight d₁.symm.edge = s_v - r := by
      simp only [Dart.edge_symm, t, t₀]
      field_simp [hw1.ne']
      ring
    rw [hs_eq] at hfull
    rw [hfull, ← edgePoint_symm d₁]
    congr 1
  · let t₀ := r₀ / W.weight d₂.edge
    have ht₀_pos : 0 < t₀ := div_pos hr₀_pos hw2
    have ht₀_lt : t₀ < 1 := (div_lt_one hw2).mpr hr2
    let t := r / W.weight d₂.edge
    have ht_pos : 0 < t := div_pos h0 hw2
    have ht_lt : t < 1 := (div_lt_one hw2).mpr hr
    let δloc := min (r₀ / 2) ((W.weight d₂.edge - r₀) / 2)
    have hδloc : 0 < δloc := by
      have : r₀ < W.weight d₂.edge := hr2
      positivity
    have hloc2 : ∀ ρ ∈ Set.Icc (-δloc) δloc,
        ∃ (h0' : 0 ≤ t₀ + ρ / W.weight d₂.edge)
          (h1' : t₀ + ρ / W.weight d₂.edge ≤ 1),
          circleMap hc ((s_v + r₀) + ρ) =
            edgePoint d₂ ⟨t₀ + ρ / W.weight d₂.edge, h0', h1'⟩ := by
      intro ρ hρ
      have hr'_pos : 0 < r₀ + ρ := by
        linarith [hρ.1, min_le_left (r₀ / 2) ((W.weight d₂.edge - r₀) / 2)]
      have hr'_le : r₀ + ρ ≤ δ₁ := by
        have h1' : r₀ ≤ δ₁ / 2 := min_le_left _ _
        have h2' : ρ ≤ δloc := hρ.2
        have h3' : δloc ≤ r₀ / 2 := min_le_left _ _
        linarith
      obtain ⟨h10', h11', _, _, _, hcm'⟩ := (hmap (r₀ + ρ) ⟨hr'_pos, hr'_le⟩).2.2
      have h0' : 0 ≤ t₀ + ρ / W.weight d₂.edge := by
        dsimp only [t₀]
        rw [← add_div]
        exact div_nonneg hr'_pos.le hw2.le
      have h1' : t₀ + ρ / W.weight d₂.edge ≤ 1 := by
        dsimp only [t₀]
        rw [← add_div]
        exact (div_le_one hw2).mpr (by linarith [(hmap (r₀ + ρ) ⟨hr'_pos, hr'_le⟩).2.1])
      refine ⟨h0', h1', ?_⟩
      rw [show (s_v + r₀) + ρ = s_v + (r₀ + ρ) by ring, hcm']
      congr 1
      ext
      dsimp only [t₀]
      rw [add_div]
    have hfull := edge_param_full W hc (d := d₂) (s₀ := s_v + r₀) ht₀_pos ht₀_lt hδloc hloc2
      t ht_pos ht_lt
    have hs_eq : s_v + r₀ + (t - t₀) * W.weight d₂.edge = s_v + r := by
      simp only [t, t₀]
      field_simp [hw2.ne']
      ring
    rw [hs_eq] at hfull
    exact hfull

private theorem edge_param_endpoints {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle)
    {d : W.graph.Dart} {s₀ t₀ : ℝ} (ht0_pos : 0 < t₀) (ht0_lt : t₀ < 1)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hloc : ∀ r ∈ Set.Icc (-δ₀) δ₀,
      ∃ (h0 : 0 ≤ t₀ + r / W.weight d.edge) (h1 : t₀ + r / W.weight d.edge ≤ 1),
        circleMap hc (s₀ + r) = edgePoint d ⟨t₀ + r / W.weight d.edge, h0, h1⟩) :
    circleMap hc (s₀ - t₀ * W.weight d.edge) = vertex d.fst ∧
    circleMap hc (s₀ + (1 - t₀) * W.weight d.edge) = vertex d.snd := by
  have hfull := edge_param_full W hc ht0_pos ht0_lt hδ₀ hloc
  let w := W.weight d.edge
  have hw : 0 < w := W.dart_weight_pos d
  have hcont := circleMap_continuous hc
  rw [continuous_iff_continuousAt] at hcont
  refine ⟨eq_of_forall_dist_le fun ε hε => ?_, eq_of_forall_dist_le fun ε hε => ?_⟩
  · obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp
      (hcont (s₀ - t₀ * w)) (ε / 2) (by linarith)
    let t := min (1 / 2 : ℝ) (min (δ / (2 * w)) (ε / (3 * w)))
    have ht0 : 0 < t := by positivity
    have ht1 : t < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hcm := hfull t ht0 ht1
    have hdist1 : dist (circleMap hc (s₀ + (t - t₀) * w)) (circleMap hc (s₀ - t₀ * w)) < ε / 2 := by
      refine hball ?_
      rw [Real.dist_eq]
      have heq : s₀ + (t - t₀) * w - (s₀ - t₀ * w) = t * w := by ring
      rw [heq, abs_of_pos (mul_pos ht0 hw)]
      have : t ≤ δ / (2 * w) := (min_le_right _ _).trans (min_le_left _ _)
      calc t * w ≤ (δ / (2 * w)) * w := mul_le_mul_of_nonneg_right this hw.le
        _ = δ / 2 := by field_simp [hw.ne']
        _ < δ := by linarith
    have hdist2 : dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (vertex d.fst) < ε / 2 := by
      rw [← edgePoint_zero d]
      calc dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (edgePoint d 0)
          ≤ w * |t - 0| := dist_edgePoint_self_le d _ _
        _ = t * w := by rw [sub_zero, abs_of_pos ht0, mul_comm]
        _ ≤ (ε / (3 * w)) * w :=
            mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hw.le
        _ = ε / 3 := by field_simp [hw.ne']
        _ < ε / 2 := by linarith
    rw [hcm] at hdist1
    calc dist (circleMap hc (s₀ - t₀ * w)) (vertex d.fst)
        ≤ dist (circleMap hc (s₀ - t₀ * w)) (edgePoint d ⟨t, ht0.le, ht1.le⟩) +
            dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (vertex d.fst) := dist_triangle _ _ _
      _ ≤ ε / 2 + ε / 2 := by rw [_root_.dist_comm (circleMap hc _)]; linarith
      _ = ε := add_halves ε
  · obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp
      (hcont (s₀ + (1 - t₀) * w)) (ε / 2) (by linarith)
    let η := min (1 / 2 : ℝ) (min (δ / (2 * w)) (ε / (3 * w)))
    have hη0 : 0 < η := by positivity
    let t := 1 - η
    have ht0 : 0 < t := by
      have : η ≤ 1 / 2 := min_le_left _ _
      linarith
    have ht1 : t < 1 := by linarith
    have hcm := hfull t ht0 ht1
    have hdist1 : dist (circleMap hc (s₀ + (t - t₀) * w))
        (circleMap hc (s₀ + (1 - t₀) * w)) < ε / 2 := by
      refine hball ?_
      rw [Real.dist_eq]
      have heq : s₀ + (t - t₀) * w - (s₀ + (1 - t₀) * w) = -(η * w) := by dsimp only [t]; ring
      rw [heq, abs_neg, abs_of_pos (mul_pos hη0 hw)]
      have : η ≤ δ / (2 * w) := (min_le_right _ _).trans (min_le_left _ _)
      calc η * w ≤ (δ / (2 * w)) * w := mul_le_mul_of_nonneg_right this hw.le
        _ = δ / 2 := by field_simp [hw.ne']
        _ < δ := by linarith
    have hdist2 : dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (vertex d.snd) < ε / 2 := by
      rw [← edgePoint_one d]
      calc dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (edgePoint d 1)
          ≤ w * |t - 1| := dist_edgePoint_self_le d _ _
        _ = η * w := by
            have : |t - 1| = η := by dsimp only [t]; rw [show 1 - η - 1 = -η by ring, abs_neg,
              abs_of_pos hη0]
            rw [this, mul_comm]
        _ ≤ (ε / (3 * w)) * w :=
            mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hw.le
        _ = ε / 3 := by field_simp [hw.ne']
        _ < ε / 2 := by linarith
    rw [hcm] at hdist1
    calc dist (circleMap hc (s₀ + (1 - t₀) * w)) (vertex d.snd)
        ≤ dist (circleMap hc (s₀ + (1 - t₀) * w)) (edgePoint d ⟨t, ht0.le, ht1.le⟩) +
            dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (vertex d.snd) := dist_triangle _ _ _
      _ ≤ ε / 2 + ε / 2 := by rw [_root_.dist_comm (circleMap hc _)]; linarith
      _ = ε := add_halves ε

end CycleGeometry

section Fin2CycleDictator

private theorem dist_edgePoint_ray_of_edge_ne {V : Type*} (W : WeightedGraph V) [Finite V]
    {v : V} {d_x d_z : W.graph.Dart} (hx_fst : d_x.fst = v) (hz_fst : d_z.fst = v)
    (hne : d_x.edge ≠ d_z.edge) {wmin vmin δ r_x r_z : ℝ}
    (hwmin : ∀ d : W.graph.Dart, wmin ≤ W.weight d.edge)
    (hvmin : ∀ u w : V, u ≠ w → vmin ≤ dist (vertex u : MetricGraph W) (vertex w))
    (hδ16 : 16 * δ ≤ wmin) (hδv : 16 * δ ≤ vmin)
    (hrx0 : 0 ≤ r_x) (hrx4 : r_x ≤ 4 * δ) (_hrz0 : 0 ≤ r_z) (hrz4 : r_z ≤ 4 * δ)
    (hxt0 : 0 ≤ r_x / W.weight d_x.edge) (hxt1 : r_x / W.weight d_x.edge ≤ 1)
    (hzt0 : 0 ≤ r_z / W.weight d_z.edge) (hzt1 : r_z / W.weight d_z.edge ≤ 1) :
    dist (edgePoint d_x ⟨r_x / W.weight d_x.edge, hxt0, hxt1⟩)
      (edgePoint d_z ⟨r_z / W.weight d_z.edge, hzt0, hzt1⟩) = r_x + r_z := by
  have hwx : 0 < W.weight d_x.edge := W.dart_weight_pos d_x
  have hwz : 0 < W.weight d_z.edge := W.dart_weight_pos d_z
  have hwx_ge : 16 * δ ≤ W.weight d_x.edge := hδ16.trans (hwmin d_x)
  have hwz_ge : 16 * δ ≤ W.weight d_z.edge := hδ16.trans (hwmin d_z)
  rw [dist_edgePoint_edgePoint_of_edge_ne hne]
  simp only []
  have htx : (r_x / W.weight d_x.edge) * W.weight d_x.edge = r_x :=
    div_mul_cancel₀ _ hwx.ne'
  have htz : (r_z / W.weight d_z.edge) * W.weight d_z.edge = r_z :=
    div_mul_cancel₀ _ hwz.ne'
  have h1tx : (1 - r_x / W.weight d_x.edge) * W.weight d_x.edge = W.weight d_x.edge - r_x := by
    rw [sub_mul, one_mul, htx]
  have h1tz : (1 - r_z / W.weight d_z.edge) * W.weight d_z.edge = W.weight d_z.edge - r_z := by
    rw [sub_mul, one_mul, htz]
  rw [htx, htz, h1tx, h1tz, hx_fst, hz_fst, vertexDist_self W.weight_nonneg, add_zero]
  have hv_z : vmin ≤ W.graph.vertexDist W.weight v d_z.snd := by
    rw [← dist_vertex]
    exact hvmin v d_z.snd (hz_fst ▸ d_z.adj.ne)
  have hv_x : vmin ≤ W.graph.vertexDist W.weight d_x.snd v := by
    rw [← dist_vertex]
    exact hvmin d_x.snd v (hx_fst ▸ d_x.adj.ne.symm)
  have hnn : 0 ≤ W.graph.vertexDist W.weight d_x.snd d_z.snd := by
    rw [← dist_vertex]
    exact dist_nonneg
  have h12 : r_x + r_z ≤
      r_x + W.graph.vertexDist W.weight v d_z.snd + (W.weight d_z.edge - r_z) := by
    linarith
  have h34 : W.graph.vertexDist W.weight d_x.snd v + r_z ≥ r_x + r_z := by linarith
  have hterm3 : r_x + r_z ≤
      W.weight d_x.edge - r_x + W.graph.vertexDist W.weight d_x.snd v + r_z := by
    linarith
  have hterm4 : r_x + r_z ≤ W.weight d_x.edge - r_x + W.graph.vertexDist W.weight d_x.snd d_z.snd +
      (W.weight d_z.edge - r_z) := by
    linarith
  rw [min_eq_left h12]
  exact min_eq_left (le_min hterm3 hterm4)

private theorem dist_edgePoint_ray_same {V : Type*} (W : WeightedGraph V) [Finite V]
    {v : V} {d_x : W.graph.Dart} (hx_fst : d_x.fst = v) {wmin vmin δ r_1 r_2 : ℝ}
    (hwmin : ∀ d : W.graph.Dart, wmin ≤ W.weight d.edge)
    (hvmin : ∀ u w : V, u ≠ w → vmin ≤ dist (vertex u : MetricGraph W) (vertex w))
    (hδ16 : 16 * δ ≤ wmin) (hδv : 16 * δ ≤ vmin)
    (hr10 : 0 ≤ r_1) (hr14 : r_1 ≤ 4 * δ) (hr20 : 0 ≤ r_2) (hr24 : r_2 ≤ 4 * δ)
    (h10 : 0 ≤ r_1 / W.weight d_x.edge) (h11 : r_1 / W.weight d_x.edge ≤ 1)
    (h20 : 0 ≤ r_2 / W.weight d_x.edge) (h21 : r_2 / W.weight d_x.edge ≤ 1) :
    dist (edgePoint d_x ⟨r_1 / W.weight d_x.edge, h10, h11⟩)
      (edgePoint d_x ⟨r_2 / W.weight d_x.edge, h20, h21⟩) = |r_1 - r_2| := by
  let _ := hx_fst
  have hwx : 0 < W.weight d_x.edge := W.dart_weight_pos d_x
  have hwx_ge : 16 * δ ≤ W.weight d_x.edge := hδ16.trans (hwmin d_x)
  rw [dist_edgePoint_eq_min_same]
  dsimp only []
  have habs : |r_1 / W.weight d_x.edge - r_2 / W.weight d_x.edge| * W.weight d_x.edge =
      |r_1 - r_2| := by
    rw [← sub_div, abs_div, abs_of_pos hwx, div_mul_cancel₀ _ hwx.ne']
  have hr2w : r_2 / W.weight d_x.edge * W.weight d_x.edge = r_2 := div_mul_cancel₀ _ hwx.ne'
  have h1r2w : (1 - r_2 / W.weight d_x.edge) * W.weight d_x.edge = W.weight d_x.edge - r_2 := by
    rw [sub_mul, one_mul, hr2w]
  rw [habs, hr2w, h1r2w]
  have hd1 : dist (edgePoint d_x ⟨r_1 / W.weight d_x.edge, h10, h11⟩) (vertex d_x.fst) = r_1 := by
    rw [dist_edgePoint_vertex, vertexDist_self W.weight_nonneg, add_zero]
    dsimp only []
    rw [div_mul_cancel₀ _ hwx.ne', sub_mul, one_mul, div_mul_cancel₀ _ hwx.ne']
    have hv : vmin ≤ W.graph.vertexDist W.weight d_x.snd d_x.fst := by
      rw [← dist_vertex]
      exact hvmin d_x.snd d_x.fst d_x.adj.ne.symm
    exact min_eq_left (by linarith)
  rw [hd1]
  have hle2 : |r_1 - r_2| ≤ r_1 + r_2 := by
    rcases le_total r_1 r_2 with h | h
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]; linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith
  have hle3 : |r_1 - r_2| ≤
      dist (edgePoint d_x ⟨r_1 / W.weight d_x.edge, h10, h11⟩) (vertex d_x.snd) +
        (W.weight d_x.edge - r_2) := by
    have hd2_nn : 0 ≤ dist (edgePoint d_x ⟨r_1 / W.weight d_x.edge, h10, h11⟩) (vertex d_x.snd) :=
      dist_nonneg
    have habs_le : |r_1 - r_2| ≤ 4 * δ := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    linarith
  exact min_eq_left (le_min hle2 hle3)

private theorem half_step_third_dart_bound {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v : V} {d_a d_b d : W.graph.Dart}
    (ha_fst : d_a.fst = v) (hb_fst : d_b.fst = v) (hd_fst : d.fst = v)
    (hab : d_a.edge ≠ d_b.edge) (had : d_a.edge ≠ d.edge) (hbd : d_b.edge ≠ d.edge)
    {wmin vmin δ r_y r_a r_b : ℝ}
    (hwmin : ∀ d' : W.graph.Dart, wmin ≤ W.weight d'.edge)
    (hvmin : ∀ u w : V, u ≠ w → vmin ≤ dist (vertex u : MetricGraph W) (vertex w))
    (hδ16 : 16 * δ ≤ wmin) (hδv : 16 * δ ≤ vmin)
    (hry_pos : 0 < r_y) (hry_le : r_y ≤ δ)
    (hra_le : r_a ≤ δ) (hry_ra : r_y ≤ r_a)
    (hrb_le : r_b ≤ δ) (hry_rb : r_y ≤ r_b)
    (ha0 : 0 ≤ r_a / W.weight d_a.edge) (ha1 : r_a / W.weight d_a.edge ≤ 1)
    (hb0 : 0 ≤ r_b / W.weight d_b.edge) (hb1 : r_b / W.weight d_b.edge ≤ 1)
    (hd0 : 0 ≤ r_y / W.weight d.edge) (hd1 : r_y / W.weight d.edge ≤ 1)
    (ha'0 : 0 ≤ (3 / 4 * r_y) / W.weight d_a.edge)
    (ha'1 : (3 / 4 * r_y) / W.weight d_a.edge ≤ 1)
    (hb'0 : 0 ≤ (3 / 4 * r_y) / W.weight d_b.edge)
    (hb'1 : (3 / 4 * r_y) / W.weight d_b.edge ≤ 1)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam_b' : f ![edgePoint d_b ⟨(3 / 4 * r_y) / W.weight d_b.edge, hb'0, hb'1⟩,
        edgePoint d_b ⟨(3 / 4 * r_y) / W.weight d_b.edge, hb'0, hb'1⟩] =
      edgePoint d_b ⟨(3 / 4 * r_y) / W.weight d_b.edge, hb'0, hb'1⟩)
    (hy_eq : f ![edgePoint d_a ⟨r_a / W.weight d_a.edge, ha0, ha1⟩,
        edgePoint d_b ⟨r_b / W.weight d_b.edge, hb0, hb1⟩] =
      edgePoint d ⟨r_y / W.weight d.edge, hd0, hd1⟩) :
    dist (edgePoint d_a ⟨(3 / 4 * r_y) / W.weight d_a.edge, ha'0, ha'1⟩)
      (f ![edgePoint d_a ⟨(3 / 4 * r_y) / W.weight d_a.edge, ha'0, ha'1⟩,
        edgePoint d_b ⟨(3 / 4 * r_y) / W.weight d_b.edge, hb'0, hb'1⟩]) ≤
      1 / 4 * r_y := by
  have hsp := (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp
  let r' := 3 / 4 * r_y
  let a := edgePoint d_a ⟨r_a / W.weight d_a.edge, ha0, ha1⟩
  let b := edgePoint d_b ⟨r_b / W.weight d_b.edge, hb0, hb1⟩
  let y := edgePoint d ⟨r_y / W.weight d.edge, hd0, hd1⟩
  let a' := edgePoint d_a ⟨r' / W.weight d_a.edge, ha'0, ha'1⟩
  let b' := edgePoint d_b ⟨r' / W.weight d_b.edge, hb'0, hb'1⟩
  let y₂ := f ![a, b']
  let y' := f ![a', b']
  have hδ_pos : 0 < δ := hry_pos.trans_le hry_le
  have hby : dist b y = r_b + r_y :=
    dist_edgePoint_ray_of_edge_ne W hb_fst hd_fst hbd hwmin hvmin hδ16 hδv
      (hry_pos.le.trans hry_rb) (by linarith) hry_pos.le (by linarith) hb0 hb1 hd0 hd1
  have hb'y : dist b' y = r' + r_y :=
    dist_edgePoint_ray_of_edge_ne W hb_fst hd_fst hbd hwmin hvmin hδ16 hδv
      (by linarith) (by linarith) hry_pos.le (by linarith) hb'0 hb'1 hd0 hd1
  have hbb' : dist b b' = r_b - r' := by
    rw [dist_edgePoint_ray_same W hb_fst hwmin hvmin hδ16 hδv (hry_pos.le.trans hry_rb)
      (by linarith) (by linarith) (by linarith) hb0 hb1 hb'0 hb'1,
      abs_of_nonneg (by linarith)]
  have hsp_b : dist b y ≤ dist b y₂ := by
    have h := hsp ![a, b] 1 b'
    rw [hy_eq] at h
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Function.update_self,
      show Function.update ![a, b] 1 b' = ![a, b'] by ext i; fin_cases i <;> rfl] using h
  have hsp_b' : dist b' y₂ ≤ dist b' y := by
    have h := hsp ![a, b'] 1 b
    rw [show Function.update ![a, b'] 1 b = ![a, b] by ext i; fin_cases i <;> rfl, hy_eq] at h
    exact h
  have htri_b := dist_triangle b b' y₂
  have hby2 : dist b y₂ = r_b + r_y := by linarith
  have hb'y2 : dist b' y₂ = r' + r_y := by linarith
  have hvy2_le : dist (vertex v : MetricGraph W) y₂ ≤ 5 / 2 * r_y := by
    have hvb' : dist (vertex v : MetricGraph W) b' = r' := by
      have hw := W.dart_weight_pos d_b
      have hwx_ge : 16 * δ ≤ W.weight d_b.edge := hδ16.trans (hwmin d_b)
      dsimp only [b']
      rw [dist_vertex_edgePoint, hb_fst, vertexDist_self W.weight_nonneg, zero_add,
        div_mul_cancel₀ _ hw.ne', sub_mul, one_mul, div_mul_cancel₀ _ hw.ne']
      have hv : vmin ≤ W.graph.vertexDist W.weight v d_b.snd := by
        rw [← dist_vertex]; exact hvmin v d_b.snd (hb_fst ▸ d_b.adj.ne)
      exact min_eq_left (by dsimp only [r']; linarith)
    calc dist (vertex v : MetricGraph W) y₂
        ≤ dist (vertex v : MetricGraph W) b' + dist b' y₂ := dist_triangle _ _ _
      _ = r' + (r' + r_y) := by rw [hvb', hb'y2]
      _ = 5 / 2 * r_y := by dsimp only [r']; ring
  have hvy2_lt : dist (vertex v : MetricGraph W) y₂ ≤ 3 * δ := by linarith
  have hlocate : ∀ {p : MetricGraph W}, dist (vertex v : MetricGraph W) p ≤ 3 * δ →
      p = vertex v ∨ ∃ (d' : W.graph.Dart) (t' : unitInterval),
        d'.fst = v ∧ 0 < (t' : ℝ) ∧ (t' : ℝ) < 1 ∧ p = edgePoint d' t' ∧
        dist (vertex v : MetricGraph W) p = (t' : ℝ) * W.weight d'.edge := by
    intro p
    induction p using MetricGraph.ind with
    | vertex u =>
      intro hu
      by_cases huv : u = v
      · left; rw [huv]
      · exfalso; have := hvmin v u (Ne.symm huv); linarith
    | edgePoint d' t' ht0 ht1 =>
      intro hp
      right
      have hev : d'.fst = v ∨ d'.snd = v := by
        by_contra hnone
        push Not at hnone
        have h1 : vmin ≤ W.graph.vertexDist W.weight v d'.fst := by
          rw [← dist_vertex]; exact hvmin v d'.fst (Ne.symm hnone.1)
        have h2 : vmin ≤ W.graph.vertexDist W.weight v d'.snd := by
          rw [← dist_vertex]; exact hvmin v d'.snd (Ne.symm hnone.2)
        rw [dist_vertex_edgePoint] at hp
        have hw' := W.dart_weight_pos d'
        have ht0w : 0 ≤ (t' : ℝ) * W.weight d'.edge := mul_nonneg ht0.le hw'.le
        have ht1w : 0 ≤ (1 - (t' : ℝ)) * W.weight d'.edge :=
          mul_nonneg (sub_nonneg.mpr t'.2.2) hw'.le
        rcases le_total (W.graph.vertexDist W.weight v d'.fst + (t' : ℝ) * W.weight d'.edge)
            (W.graph.vertexDist W.weight v d'.snd + (1 - (t' : ℝ)) * W.weight d'.edge) with hm | hm
        · rw [min_eq_left hm] at hp; linarith
        · rw [min_eq_right hm] at hp; linarith
      have h_at_fst : ∀ {d'' : W.graph.Dart} {t'' : unitInterval},
          d''.fst = v → 0 < (t'' : ℝ) → (t'' : ℝ) < 1 →
          dist (vertex v : MetricGraph W) (edgePoint d'' t'') ≤ 3 * δ →
          dist (vertex v : MetricGraph W) (edgePoint d'' t'') = (t'' : ℝ) * W.weight d''.edge := by
        intro d'' t'' hfst _ _ hdp
        rw [dist_vertex_edgePoint, hfst, vertexDist_self W.weight_nonneg, zero_add] at hdp ⊢
        have hv : vmin ≤ W.graph.vertexDist W.weight v d''.snd := by
          rw [← dist_vertex]; exact hvmin v d''.snd (hfst ▸ d''.adj.ne)
        have hge : vmin ≤ W.graph.vertexDist W.weight v d''.snd +
            (1 - (t'' : ℝ)) * W.weight d''.edge := by
          linarith [mul_nonneg (sub_nonneg.mpr t''.2.2) (W.dart_weight_pos d'').le]
        rcases le_total ((t'' : ℝ) * W.weight d''.edge)
            (W.graph.vertexDist W.weight v d''.snd + (1 - (t'' : ℝ)) * W.weight d''.edge)
            with hle | hge'
        · exact min_eq_left hle
        · exfalso; rw [min_eq_right hge'] at hdp; linarith
      rcases hev with hfst | hsnd
      · exact ⟨d', t', hfst, ht0, ht1, rfl, h_at_fst hfst ht0 ht1 hp⟩
      · have hdp' : dist (vertex v : MetricGraph W) (edgePoint d'.symm (unitInterval.symm t')) ≤
            3 * δ := by
          rwa [edgePoint_symm]
        refine ⟨d'.symm, unitInterval.symm t', hsnd, sub_pos.mpr ht1, sub_lt_self 1 ht0,
          (edgePoint_symm d' t').symm, ?_⟩
        rw [← edgePoint_symm d' t']
        exact h_at_fst hsnd (sub_pos.mpr ht1) (sub_lt_self 1 ht0) hdp'
  rcases hlocate hvy2_lt with hv_eq | ⟨d₂, t₂, hd₂_fst, ht20, ht21, hy2_eq, hvy2_eq⟩
  · exfalso
    rw [hv_eq, _root_.dist_comm, dist_vertex_edgePoint, hb_fst, vertexDist_self W.weight_nonneg,
      zero_add] at hb'y2
    have hwx := W.dart_weight_pos d_b
    have hlt : r' + r_y ≤ (r' / W.weight d_b.edge) * W.weight d_b.edge :=
      hb'y2.symm.trans_le (min_le_left _ _)
    rw [div_mul_cancel₀ _ hwx.ne'] at hlt
    dsimp only [r'] at hlt
    linarith
  have hry2_le : dist (vertex v : MetricGraph W) y₂ ≤ 3 * δ := hvy2_lt
  let r₂ := (t₂ : ℝ) * W.weight d₂.edge
  have hr2_eq : r₂ = dist (vertex v : MetricGraph W) y₂ := hvy2_eq.symm
  have hr2_bound : r₂ ≤ 3 * δ := hr2_eq ▸ hry2_le
  have hd2_ne_db : d₂.edge ≠ d_b.edge := by
    intro heq
    have hd_or := (dart_edge_eq_iff d₂ d_b).mp heq
    have hd2_eq : d₂ = d_b := hd_or.resolve_right fun hsym => by
      have : d_b.fst = d_b.snd := by rw [hb_fst, ← hd₂_fst, hsym]; rfl
      exact d_b.adj.ne this
    subst hd2_eq
    have hw := W.dart_weight_pos d₂
    have ht2_val : (t₂ : ℝ) = r₂ / W.weight d₂.edge := (eq_div_iff hw.ne').mpr rfl
    have h16d : 16 * δ ≤ W.weight d₂.edge := hδ16.trans (hwmin d₂)
    have hbb'_y : dist b' y₂ = |r' - r₂| := by
      rw [hy2_eq]
      have h10 : 0 ≤ r₂ / W.weight d₂.edge := div_nonneg (hr2_eq ▸ dist_nonneg) hw.le
      have h11 : r₂ / W.weight d₂.edge ≤ 1 := (div_le_one hw).mpr (by linarith)
      have := dist_edgePoint_ray_same W hb_fst hwmin hvmin hδ16 hδv (by linarith) (by linarith)
        (hr2_eq ▸ dist_nonneg) (by linarith) hb'0 hb'1 h10 h11
      have heq_t : t₂ = ⟨r₂ / W.weight d₂.edge, h10, h11⟩ := by ext; exact ht2_val
      rw [heq_t]
      exact this
    rw [hb'y2] at hbb'_y
    have hr2_s : r₂ = 2 * r' + r_y := by
      rcases le_or_gt r' r₂ with h | h
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)] at hbb'_y
        dsimp only [r'] at hbb'_y ⊢
        linarith
      · rw [abs_of_nonneg (sub_nonneg.mpr h.le)] at hbb'_y
        exfalso
        have hnn : 0 ≤ r₂ := hr2_eq ▸ dist_nonneg
        dsimp only [r'] at hbb'_y
        linarith
    have hby_val : dist b y₂ = |r_b - r₂| := by
      rw [hy2_eq]
      have h10 : 0 ≤ r₂ / W.weight d₂.edge := div_nonneg (hr2_eq ▸ dist_nonneg) hw.le
      have h11 : r₂ / W.weight d₂.edge ≤ 1 := (div_le_one hw).mpr (by linarith)
      have := dist_edgePoint_ray_same W hb_fst hwmin hvmin hδ16 hδv (hry_pos.le.trans hry_rb)
        (by linarith) (hr2_eq ▸ dist_nonneg) (by linarith) hb0 hb1 h10 h11
      have heq_t : t₂ = ⟨r₂ / W.weight d₂.edge, h10, h11⟩ := by ext; exact ht2_val
      rw [heq_t]
      exact this
    rw [hby2] at hby_val
    rcases abs_cases (r_b - r₂) with ⟨hpos, _⟩ | ⟨hneg, _⟩
    · rw [hpos] at hby_val; dsimp only [r'] at hr2_s; linarith
    · rw [hneg] at hby_val; dsimp only [r'] at hr2_s; linarith
  have hr2_is_ry : r₂ = r_y := by
    have hw := W.dart_weight_pos d₂
    have ht2_val : (t₂ : ℝ) = r₂ / W.weight d₂.edge := (eq_div_iff hw.ne').mpr rfl
    have h16d : 16 * δ ≤ W.weight d₂.edge := hδ16.trans (hwmin d₂)
    have h10 : 0 ≤ r₂ / W.weight d₂.edge := div_nonneg (hr2_eq ▸ dist_nonneg) hw.le
    have h11 : r₂ / W.weight d₂.edge ≤ 1 := (div_le_one hw).mpr (by linarith)
    have hb'y_calc : dist b' y₂ = r' + r₂ := by
      rw [hy2_eq]
      have heq_t : t₂ = ⟨r₂ / W.weight d₂.edge, h10, h11⟩ := by ext; exact ht2_val
      rw [heq_t]
      exact dist_edgePoint_ray_of_edge_ne W hb_fst hd₂_fst hd2_ne_db.symm hwmin hvmin
        hδ16 hδv (by linarith) (by linarith) (hr2_eq ▸ dist_nonneg) (by linarith)
        hb'0 hb'1 h10 h11
    linarith
  by_cases hd2_eq_da : d₂.edge = d_a.edge
  · have hd2_da : d₂ = d_a := ((dart_edge_eq_iff d₂ d_a).mp hd2_eq_da).resolve_right fun hsym => by
      have : d_a.fst = d_a.snd := by rw [ha_fst, ← hd₂_fst, hsym]; rfl
      exact d_a.adj.ne this
    subst hd2_da
    have hw := W.dart_weight_pos d₂
    have ht2_val : (t₂ : ℝ) = r_y / W.weight d₂.edge := by
      rw [← hr2_is_ry]; exact (eq_div_iff hw.ne').mpr rfl
    have ha'y2 : dist a' y₂ = 1 / 4 * r_y := by
      rw [hy2_eq]
      have h10 : 0 ≤ r_y / W.weight d₂.edge := div_nonneg hry_pos.le hw.le
      have h11 : r_y / W.weight d₂.edge ≤ 1 :=
        (div_le_one hw).mpr (by linarith [hδ16.trans (hwmin d₂)])
      have heq_t : t₂ = ⟨r_y / W.weight d₂.edge, h10, h11⟩ := by ext; exact ht2_val
      rw [heq_t]
      have := dist_edgePoint_ray_same W ha_fst hwmin hvmin hδ16 hδv (by linarith) (by linarith)
        hry_pos.le (by linarith) ha'0 ha'1 h10 h11
      rw [this, abs_sub_comm, abs_of_nonneg (by linarith)]
      ring
    have hsp_a' : dist a' y' ≤ dist a' y₂ := by
      have h := hsp ![a', b'] 0 a
      rw [show Function.update ![a', b'] 0 a = ![a, b'] by ext i; fin_cases i <;> rfl] at h
      simpa only [Matrix.cons_val_zero] using h
    linarith
  · exfalso
    have hw := W.dart_weight_pos d₂
    have ht2_val : (t₂ : ℝ) = r_y / W.weight d₂.edge := by
      rw [← hr2_is_ry]; exact (eq_div_iff hw.ne').mpr rfl
    have hay2 : dist a y₂ = r_a + r_y := by
      rw [hy2_eq]
      have h10 : 0 ≤ r_y / W.weight d₂.edge := div_nonneg hry_pos.le hw.le
      have h11 : r_y / W.weight d₂.edge ≤ 1 :=
        (div_le_one hw).mpr (by linarith [hδ16.trans (hwmin d₂)])
      have heq_t : t₂ = ⟨r_y / W.weight d₂.edge, h10, h11⟩ := by ext; exact ht2_val
      rw [heq_t]
      exact dist_edgePoint_ray_of_edge_ne W ha_fst hd₂_fst (Ne.symm hd2_eq_da) hwmin hvmin hδ16 hδv
        (hry_pos.le.trans hry_ra) (by linarith) hry_pos.le (by linarith) ha0 ha1 h10 h11
    have haa' : dist a a' = r_a - r' := by
      rw [dist_edgePoint_ray_same W ha_fst hwmin hvmin hδ16 hδv (hry_pos.le.trans hry_ra)
        (by linarith) (by linarith) (by linarith) ha0 ha1 ha'0 ha'1,
        abs_of_nonneg (by linarith)]
    have ha'b' : dist a' b' = 3 / 2 * r_y := by
      rw [dist_edgePoint_ray_of_edge_ne W ha_fst hb_fst hab hwmin hvmin hδ16 hδv
        (by linarith) (by linarith) (by linarith) (by linarith) ha'0 ha'1 hb'0 hb'1]
      ring
    have hsp_a : dist a y₂ ≤ dist a y' := by
      have h := hsp ![a, b'] 0 a'
      rw [show Function.update ![a, b'] 0 a' = ![a', b'] by ext i; fin_cases i <;> rfl] at h
      simpa only [Matrix.cons_val_zero] using h
    have hsp_a'_b' : dist a' y' ≤ dist a' b' := by
      have h := hsp ![a', b'] 0 b'
      rw [show Function.update ![a', b'] 0 b' = ![b', b'] by ext i; fin_cases i <;> rfl,
        hf_unam_b'] at h
      simpa only [Matrix.cons_val_zero] using h
    have htri := dist_triangle a a' y'
    dsimp only [r'] at haa' ha'b'
    linarith

private theorem dist_third_dart_signed {V : Type*} (W : WeightedGraph V) [Finite V]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hc : c.IsCycle)
    {s₀ : ℝ} {v : V} {d₁ d₂ d : W.graph.Dart}
    (hd₁_fst : d₁.fst = v) (hd₂_fst : d₂.fst = v) (hd_fst : d.fst = v)
    (hd₁_ne : d₁.edge ≠ d.edge) (hd₂_ne : d₂.edge ≠ d.edge)
    {wmin vmin δ δ₁ : ℝ} (hwmin : ∀ d' : W.graph.Dart, wmin ≤ W.weight d'.edge)
    (hvmin : ∀ u w : V, u ≠ w → vmin ≤ dist (vertex u : MetricGraph W) (vertex w))
    (hδ0 : 0 < δ) (hδδ₁ : δ ≤ δ₁) (hδ16 : 16 * δ ≤ wmin) (hδv : 16 * δ ≤ vmin)
    (hs₀_v : circleMap hc s₀ = vertex v)
    (hmap : ∀ r ∈ Set.Ioc 0 δ₁, r < W.weight d₁.edge ∧ r < W.weight d₂.edge ∧
      ∃ (h10 : 0 ≤ r / W.weight d₁.edge) (h11 : r / W.weight d₁.edge ≤ 1)
        (h20 : 0 ≤ r / W.weight d₂.edge) (h21 : r / W.weight d₂.edge ≤ 1),
        circleMap hc (s₀ - r) = edgePoint d₁ ⟨r / W.weight d₁.edge, h10, h11⟩ ∧
        circleMap hc (s₀ + r) = edgePoint d₂ ⟨r / W.weight d₂.edge, h20, h21⟩)
    {s r_y : ℝ} (hs : s ∈ Set.Icc (-δ) δ) (hry0 : 0 < r_y) (hry3 : r_y ≤ 3 * δ)
    (hd0 : 0 ≤ r_y / W.weight d.edge) (hd1 : r_y / W.weight d.edge ≤ 1) :
    dist (circleMap hc (s₀ + s)) (edgePoint d ⟨r_y / W.weight d.edge, hd0, hd1⟩) = |s| + r_y := by
  let _ := hδ0
  rcases lt_trichotomy s 0 with hs_neg | rfl | hs_pos
  · have hmem : -s ∈ Set.Ioc 0 δ₁ := ⟨neg_pos.mpr hs_neg, by linarith [hs.1, hδδ₁]⟩
    obtain ⟨_, _, h10, h11, _, _, hcm1, _⟩ := hmap (-s) hmem
    rw [show s₀ + s = s₀ - (-s) by ring, hcm1,
      dist_edgePoint_ray_of_edge_ne W hd₁_fst hd_fst hd₁_ne hwmin hvmin hδ16 hδv
        (neg_pos.mpr hs_neg).le (by linarith [hs.1]) hry0.le (by linarith) h10 h11 hd0 hd1,
      abs_of_neg hs_neg]
  · rw [add_zero, hs₀_v, dist_vertex_edgePoint, hd_fst, vertexDist_self W.weight_nonneg, zero_add,
      div_mul_cancel₀ _ (W.dart_weight_pos d).ne', sub_mul, one_mul,
      div_mul_cancel₀ _ (W.dart_weight_pos d).ne', abs_zero, zero_add]
    have hv : vmin ≤ W.graph.vertexDist W.weight v d.snd := by
      rw [← dist_vertex]; exact hvmin v d.snd (hd_fst ▸ d.adj.ne)
    have hge : 16 * δ ≤ W.weight d.edge := hδ16.trans (hwmin d)
    exact min_eq_left (by linarith)
  · have hmem : s ∈ Set.Ioc 0 δ₁ := ⟨hs_pos, by linarith [hs.2, hδδ₁]⟩
    obtain ⟨_, _, _, _, h20, h21, _, hcm2⟩ := hmap s hmem
    rw [hcm2, dist_edgePoint_ray_of_edge_ne W hd₂_fst hd_fst hd₂_ne hwmin hvmin hδ16 hδv
      hs_pos.le (by linarith [hs.2]) hry0.le (by linarith) h20 h21 hd0 hd1, abs_of_pos hs_pos]

private theorem local_invariance_circle {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p)
    (s₀ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ walkLength W.weight c / 16 ∧
      ∀ sa ∈ Set.Icc (-δ) δ, ∀ sb ∈ Set.Icc (-δ) δ,
        f ![circleMap hs.1 (s₀ + sa), circleMap hs.1 (s₀ + sb)] ∈
          (fun r => circleMap hs.1 (s₀ + r)) '' Set.Icc (-δ) δ := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  have hsp := (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp
  obtain ⟨wmin, hwmin_pos, hwmin⟩ := exists_min_dart_weight (c.firstDart hs.1.not_nil)
  obtain ⟨vmin, hvmin_pos, hvmin⟩ := exists_min_vertex_dist_pos W
  have between_of_abs_le : ∀ {sa sb r δ : ℝ}, sa ∈ Set.Icc (-δ) δ → sb ∈ Set.Icc (-δ) δ →
      |r - sa| ≤ |sb - sa| → |r - sb| ≤ |sa - sb| → r ∈ Set.Icc (-δ) δ := by
    intro sa sb r δ hsa hsb h1 h2
    rw [abs_le] at h1 h2
    rcases le_total sa sb with hab | hba
    · rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h1
      rw [abs_sub_comm sa sb, abs_of_nonneg (sub_nonneg.mpr hab)] at h2
      exact ⟨by linarith [hsa.1], by linarith [hsb.2]⟩
    · rw [abs_sub_comm sb sa, abs_of_nonneg (sub_nonneg.mpr hba)] at h1
      rw [abs_of_nonneg (sub_nonneg.mpr hba)] at h2
      exact ⟨by linarith [hsb.1], by linarith [hsa.2]⟩
  rcases circleMap_local_dichotomy hs.1 s₀ with
    ⟨d, t, δ₁, _, ht0, ht1, hδ₁, hmap⟩ |
    ⟨v, d₁, d₂, δ₁, _, hd₁_fst, hd₂_fst, hd₁₂, _, _, hs₀_v, hδ₁, hmap⟩
  · let ε₁ := min (t * W.weight d.edge) ((1 - t) * W.weight d.edge)
    have hw := W.dart_weight_pos d
    have hε₁ : 0 < ε₁ := by positivity
    let δ := min (L / 16) (min (δ₁ / 4) (ε₁ / 4))
    have hδ_pos : 0 < δ := by positivity
    have hδL : δ ≤ L / 16 := min_le_left _ _
    have h3δ₁ : 3 * δ ≤ δ₁ := by
      have h : δ ≤ δ₁ / 4 := (min_le_right (L / 16) _).trans (min_le_left (δ₁ / 4) (ε₁ / 4))
      linarith
    have hδδ₁ : δ ≤ δ₁ := by linarith
    have hδε₁ : 4 * δ ≤ ε₁ := by
      have h : δ ≤ ε₁ / 4 := (min_le_right (L / 16) _).trans (min_le_right (δ₁ / 4) (ε₁ / 4))
      linarith
    refine ⟨δ, hδ_pos, hδL, fun sa hsa sb hsb => ?_⟩
    let a := circleMap hs.1 (s₀ + sa)
    let b := circleMap hs.1 (s₀ + sb)
    let y := f ![a, b]
    have hda_y : dist a y ≤ dist a b := by
      have h := hsp ![a, b] 0 b
      rw [show Function.update ![a, b] 0 b = ![b, b] by ext i; fin_cases i <;> rfl,
        show ![b, b] = fun _ => b by ext i; fin_cases i <;> rfl, hf_unam b ⟨s₀ + sb, rfl⟩] at h
      simpa only [Matrix.cons_val_zero] using h
    have hdb_y : dist b y ≤ dist b a := by
      have h := hsp ![a, b] 1 a
      rw [show Function.update ![a, b] 1 a = ![a, a] by ext i; fin_cases i <;> rfl,
        show ![a, a] = fun _ => a by ext i; fin_cases i <;> rfl, hf_unam a ⟨s₀ + sa, rfl⟩] at h
      exact h
    have hdab : dist a b = |sa - sb| := by
      have hle_ab : |(s₀ + sa) - (s₀ + sb)| ≤ walkLength W.weight c / 2 := by
        have h1 : |sa| ≤ δ := abs_le.mpr hsa
        have h2 : |sb| ≤ δ := abs_le.mpr hsb
        have hsub := abs_sub (s₀ + sa) (s₀ + sb)
        dsimp only [L] at hδL
        linarith [show |(s₀ + sa) - (s₀ + sb)| = |sa - sb| by ring_nf, abs_sub sa sb]
      rw [circleMap_dist_eq_of_le hs hle_ab, show s₀ + sa - (s₀ + sb) = sa - sb by ring]
    have hdsa : dist (circleMap hs.1 s₀) a = |sa| := by
      refine (circleMap_dist_eq_of_le hs ?_).trans (by ring_nf; rw [abs_neg])
      have : |sa| ≤ δ := abs_le.mpr hsa
      dsimp only [L] at hδL
      linarith [show |s₀ - (s₀ + sa)| = |sa| by rw [sub_add_cancel_left, abs_neg]]
    have hdy_3 : dist (circleMap hs.1 s₀) y ≤ 3 * δ := by
      calc dist (circleMap hs.1 s₀) y ≤ dist (circleMap hs.1 s₀) a + dist a y := dist_triangle _ _ _
        _ ≤ |sa| + |sa - sb| := add_le_add hdsa.le (hdab ▸ hda_y)
        _ ≤ δ + (|sa| + |sb|) := by linarith [abs_le.mpr hsa, abs_sub sa sb]
        _ ≤ 3 * δ := by linarith [abs_le.mpr hsa, abs_le.mpr hsb]
    have h0 := hmap 0 ⟨by linarith, hδ₁.le⟩
    obtain ⟨_, _, h0a, h0b, hcm0⟩ := h0
    have hcm0' : circleMap hs.1 s₀ = edgePoint d ⟨t, ht0.le, ht1.le⟩ := by
      simpa only [add_zero, zero_div] using hcm0
    have hdy_lt : dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) y < ε₁ := by
      rw [← hcm0']; linarith
    rw [hcm0'] at hdy_3
    have hy_on : ∃ r_y ∈ Set.Icc (-δ₁) δ₁, y = circleMap hs.1 (s₀ + r_y) ∧ |r_y| ≤ 3 * δ := by
      revert hdy_lt hdy_3
      induction y using MetricGraph.ind with
      | vertex u =>
        intro hlt _
        exfalso
        rw [_root_.dist_comm, dist_vertex_edgePoint] at hlt
        have h1 : ε₁ ≤ W.graph.vertexDist W.weight u d.fst + t * W.weight d.edge := by
          have : 0 ≤ W.graph.vertexDist W.weight u d.fst := by rw [← dist_vertex]; exact dist_nonneg
          linarith [min_le_left (t * W.weight d.edge) ((1 - t) * W.weight d.edge)]
        have h2 : ε₁ ≤ W.graph.vertexDist W.weight u d.snd + (1 - t) * W.weight d.edge := by
          have : 0 ≤ W.graph.vertexDist W.weight u d.snd := by rw [← dist_vertex]; exact dist_nonneg
          linarith [min_le_right (t * W.weight d.edge) ((1 - t) * W.weight d.edge)]
        linarith [le_min h1 h2]
      | edgePoint d' t' ht'0 ht'1 =>
        intro hlt h3
        have hde : d'.edge = d.edge := by
          by_contra hne
          rw [dist_edgePoint_eq_min_of_edge_ne (Ne.symm hne) ⟨t, ht0.le, ht1.le⟩ t'] at hlt
          have hv1 : ε₁ ≤ dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (vertex d'.fst) := by
            rw [_root_.dist_comm, dist_vertex_edgePoint]
            have h1 : 0 ≤ W.graph.vertexDist W.weight d'.fst d.fst := by
              rw [← dist_vertex]; exact dist_nonneg
            have h2 : 0 ≤ W.graph.vertexDist W.weight d'.fst d.snd := by
              rw [← dist_vertex]; exact dist_nonneg
            have hl := min_le_left (t * W.weight d.edge) ((1 - t) * W.weight d.edge)
            have hr := min_le_right (t * W.weight d.edge) ((1 - t) * W.weight d.edge)
            exact le_min (by linarith) (by linarith)
          have hv2 : ε₁ ≤ dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (vertex d'.snd) := by
            rw [_root_.dist_comm, dist_vertex_edgePoint]
            have h1 : 0 ≤ W.graph.vertexDist W.weight d'.snd d.fst := by
              rw [← dist_vertex]; exact dist_nonneg
            have h2 : 0 ≤ W.graph.vertexDist W.weight d'.snd d.snd := by
              rw [← dist_vertex]; exact dist_nonneg
            have hl := min_le_left (t * W.weight d.edge) ((1 - t) * W.weight d.edge)
            have hr := min_le_right (t * W.weight d.edge) ((1 - t) * W.weight d.edge)
            exact le_min (by linarith) (by linarith)
          have hw' := (W.dart_weight_pos d').le
          have hm1 : 0 ≤ (t' : ℝ) * W.weight d'.edge := mul_nonneg ht'0.le hw'
          have hm2 : 0 ≤ (1 - (t' : ℝ)) * W.weight d'.edge :=
            mul_nonneg (sub_nonneg.mpr ht'1.le) hw'
          linarith [le_min (add_le_add hv1 hm1) (add_le_add hv2 hm2)]
        have hswap : ∃ u' : unitInterval, edgePoint d' t' = edgePoint d u' := by
          rcases (dart_edge_eq_iff d' d).mp hde with rfl | rfl
          · exact ⟨t', rfl⟩
          · exact ⟨unitInterval.symm t', by
              simpa only [unitInterval.symm_symm] using edgePoint_symm d (unitInterval.symm t')⟩
        obtain ⟨u', hu'⟩ := hswap
        rw [hu'] at hlt h3 ⊢
        have hdm := dist_edgePoint_eq_min_same d ⟨t, ht0.le, ht1.le⟩ u'
        have hle_lt : dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (edgePoint d u') < ε₁ := by
          linarith
        have hterm2 : ε₁ ≤ dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (vertex d.fst) +
            (u' : ℝ) * W.weight d.edge := by
          rw [_root_.dist_comm (edgePoint d ⟨t, ht0.le, ht1.le⟩), dist_vertex_edgePoint,
            vertexDist_self W.weight_nonneg, zero_add, min_add]
          have h1 : 0 ≤ W.graph.vertexDist W.weight d.fst d.snd := by
            rw [← dist_vertex]; exact dist_nonneg
          have huw : 0 ≤ (u' : ℝ) * W.weight d.edge := mul_nonneg u'.2.1 hw.le
          have hl := min_le_left (t * W.weight d.edge) ((1 - t) * W.weight d.edge)
          have hr := min_le_right (t * W.weight d.edge) ((1 - t) * W.weight d.edge)
          exact le_min (by linarith) (by linarith)
        have hterm3 : ε₁ ≤ dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (vertex d.snd) +
            (1 - (u' : ℝ)) * W.weight d.edge := by
          rw [_root_.dist_comm (edgePoint d ⟨t, ht0.le, ht1.le⟩), dist_vertex_edgePoint,
            vertexDist_self W.weight_nonneg, zero_add, min_add]
          have h1 : 0 ≤ W.graph.vertexDist W.weight d.snd d.fst := by
            rw [← dist_vertex]; exact dist_nonneg
          have huw : 0 ≤ (1 - (u' : ℝ)) * W.weight d.edge :=
            mul_nonneg (sub_nonneg.mpr u'.2.2) hw.le
          have hl := min_le_left (t * W.weight d.edge) ((1 - t) * W.weight d.edge)
          have hr := min_le_right (t * W.weight d.edge) ((1 - t) * W.weight d.edge)
          exact le_min (by linarith) (by linarith)
        have hdeq : dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (edgePoint d u') =
            |t - (u' : ℝ)| * W.weight d.edge := by
          have hdm_lt : min (|t - (u' : ℝ)| * W.weight d.edge)
              (min (dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (vertex d.fst) +
                  (u' : ℝ) * W.weight d.edge)
                (dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (vertex d.snd) +
                  (1 - (u' : ℝ)) * W.weight d.edge)) < ε₁ := by
            simpa only [hdm] using hle_lt
          have hmin_ge := le_min hterm2 hterm3
          rcases min_lt_iff.mp hdm_lt with ha_lt | hbc_lt
          · rw [hdm]; exact min_eq_left (ha_lt.le.trans hmin_ge)
          · exact absurd hbc_lt hmin_ge.not_gt
        let r_y := ((u' : ℝ) - t) * W.weight d.edge
        have habs_ry : |r_y| ≤ 3 * δ := by
          dsimp only [r_y]
          rw [abs_mul, abs_of_pos hw, abs_sub_comm]
          linarith [hdeq, h3]
        have hry_mem : r_y ∈ Set.Icc (-δ₁) δ₁ := by
          rw [Set.mem_Icc, ← abs_le]
          linarith [h3δ₁]
        obtain ⟨_, _, h1', h2', hcm_r⟩ := hmap r_y hry_mem
        refine ⟨r_y, hry_mem, ?_, habs_ry⟩
        rw [hcm_r]
        congr 1
        ext
        dsimp only [r_y]
        field_simp [hw.ne']
        ring
    obtain ⟨r_y, _, hy_eq, habs_ry⟩ := hy_on
    have hday_abs : dist a y = |r_y - sa| := by
      rw [hy_eq]
      refine (circleMap_dist_eq_of_le hs ?_).trans ?_
      · have h1 := abs_le.mpr hsa
        have h2 := abs_sub sa r_y
        dsimp only [L] at hδL
        linarith [show |(s₀ + sa) - (s₀ + r_y)| = |sa - r_y| by ring_nf]
      · rw [show s₀ + sa - (s₀ + r_y) = -(r_y - sa) by ring, abs_neg]
    have hdby_abs : dist b y = |r_y - sb| := by
      rw [hy_eq]
      refine (circleMap_dist_eq_of_le hs ?_).trans ?_
      · have h1 := abs_le.mpr hsb
        have h2 := abs_sub sb r_y
        dsimp only [L] at hδL
        linarith [show |(s₀ + sb) - (s₀ + r_y)| = |sb - r_y| by ring_nf]
      · rw [show s₀ + sb - (s₀ + r_y) = -(r_y - sb) by ring, abs_neg]
    rw [hday_abs, hdab, abs_sub_comm sa sb] at hda_y
    rw [hdby_abs, _root_.dist_comm b a, hdab] at hdb_y
    exact ⟨r_y, between_of_abs_le hsa hsb hda_y hdb_y, hy_eq.symm⟩
  · let δ := min (L / 16) (min (δ₁ / 4) (min (wmin / 16) (vmin / 16)))
    have hδ_pos : 0 < δ := by positivity
    have hδL : δ ≤ L / 16 := min_le_left _ _
    have hδδ₁ : 4 * δ ≤ δ₁ := by
      have : δ ≤ δ₁ / 4 := (min_le_right (L / 16) _).trans (min_le_left (δ₁ / 4) _)
      linarith
    have hδ16 : 16 * δ ≤ wmin := by
      have : δ ≤ wmin / 16 :=
        (min_le_right (L / 16) _).trans
          ((min_le_right (δ₁ / 4) _).trans (min_le_left (wmin / 16) _))
      linarith
    have hδv : 16 * δ ≤ vmin := by
      have : δ ≤ vmin / 16 :=
        (min_le_right (L / 16) _).trans
          ((min_le_right (δ₁ / 4) _).trans (min_le_right (wmin / 16) _))
      linarith
    refine ⟨δ, hδ_pos, hδL, fun sa hsa sb hsb => ?_⟩
    let a := circleMap hs.1 (s₀ + sa)
    let b := circleMap hs.1 (s₀ + sb)
    let y := f ![a, b]
    have hda_y : dist a y ≤ dist a b := by
      have h := hsp ![a, b] 0 b
      rw [show Function.update ![a, b] 0 b = ![b, b] by ext i; fin_cases i <;> rfl,
        show ![b, b] = fun _ => b by ext i; fin_cases i <;> rfl, hf_unam b ⟨s₀ + sb, rfl⟩] at h
      simpa only [Matrix.cons_val_zero] using h
    have hdb_y : dist b y ≤ dist b a := by
      have h := hsp ![a, b] 1 a
      rw [show Function.update ![a, b] 1 a = ![a, a] by ext i; fin_cases i <;> rfl,
        show ![a, a] = fun _ => a by ext i; fin_cases i <;> rfl, hf_unam a ⟨s₀ + sa, rfl⟩] at h
      exact h
    have hdab : dist a b = |sa - sb| := by
      have hle_ab : |(s₀ + sa) - (s₀ + sb)| ≤ walkLength W.weight c / 2 := by
        have h1 := abs_le.mpr hsa
        have h2 := abs_le.mpr hsb
        have h3 := abs_sub sa sb
        dsimp only [L] at hδL
        linarith [show |(s₀ + sa) - (s₀ + sb)| = |sa - sb| by ring_nf]
      rw [circleMap_dist_eq_of_le hs hle_ab, show s₀ + sa - (s₀ + sb) = sa - sb by ring]
    have hdsa : dist (vertex v : MetricGraph W) a = |sa| := by
      rw [← hs₀_v]
      refine (circleMap_dist_eq_of_le hs ?_).trans (by ring_nf; rw [abs_neg])
      have : |sa| ≤ δ := abs_le.mpr hsa
      dsimp only [L] at hδL
      linarith [show |s₀ - (s₀ + sa)| = |sa| by rw [sub_add_cancel_left, abs_neg]]
    have hvy_3 : dist (vertex v : MetricGraph W) y ≤ 3 * δ := by
      calc dist (vertex v : MetricGraph W) y ≤ dist (vertex v : MetricGraph W) a + dist a y :=
            dist_triangle _ _ _
        _ ≤ |sa| + |sa - sb| := add_le_add hdsa.le (hdab ▸ hda_y)
        _ ≤ 3 * δ := by linarith [abs_le.mpr hsa, abs_le.mpr hsb, abs_sub sa sb]
    have hy_not_far : y = vertex v ∨ ∃ (d : W.graph.Dart) (t : unitInterval),
        d.fst = v ∧ 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ y = edgePoint d t ∧
        dist (vertex v : MetricGraph W) y = (t : ℝ) * W.weight d.edge := by
      revert hvy_3
      induction y using MetricGraph.ind with
      | vertex u =>
        intro hu
        by_cases huv : u = v
        · left; rw [huv]
        · exfalso; have := hvmin v u (Ne.symm huv); linarith
      | edgePoint d' t' ht0 ht1 =>
        intro hp
        right
        have hev : d'.fst = v ∨ d'.snd = v := by
          by_contra hnone
          push Not at hnone
          have h1 : vmin ≤ W.graph.vertexDist W.weight v d'.fst := by
            rw [← dist_vertex]; exact hvmin v d'.fst (Ne.symm hnone.1)
          have h2 : vmin ≤ W.graph.vertexDist W.weight v d'.snd := by
            rw [← dist_vertex]; exact hvmin v d'.snd (Ne.symm hnone.2)
          rw [dist_vertex_edgePoint] at hp
          have hw' := W.dart_weight_pos d'
          have := mul_nonneg ht0.le hw'.le
          have := mul_nonneg (sub_nonneg.mpr t'.2.2) hw'.le
          rcases le_total (W.graph.vertexDist W.weight v d'.fst + (t' : ℝ) * W.weight d'.edge)
              (W.graph.vertexDist W.weight v d'.snd + (1 - (t' : ℝ)) * W.weight d'.edge)
              with hm | hm
          · rw [min_eq_left hm] at hp; linarith
          · rw [min_eq_right hm] at hp; linarith
        have h_at_fst : ∀ {d'' : W.graph.Dart} {t'' : unitInterval},
            d''.fst = v → 0 < (t'' : ℝ) → (t'' : ℝ) < 1 →
            dist (vertex v : MetricGraph W) (edgePoint d'' t'') ≤ 3 * δ →
            dist (vertex v : MetricGraph W) (edgePoint d'' t'') =
              (t'' : ℝ) * W.weight d''.edge := by
          intro d'' t'' hfst _ _ hdp
          rw [dist_vertex_edgePoint, hfst, vertexDist_self W.weight_nonneg, zero_add] at hdp ⊢
          have hv : vmin ≤ W.graph.vertexDist W.weight v d''.snd := by
            rw [← dist_vertex]; exact hvmin v d''.snd (hfst ▸ d''.adj.ne)
          have hge : vmin ≤ W.graph.vertexDist W.weight v d''.snd +
              (1 - (t'' : ℝ)) * W.weight d''.edge :=
            by linarith [mul_nonneg (sub_nonneg.mpr t''.2.2) (W.dart_weight_pos d'').le]
          rcases le_total ((t'' : ℝ) * W.weight d''.edge)
              (W.graph.vertexDist W.weight v d''.snd + (1 - (t'' : ℝ)) * W.weight d''.edge)
              with hle | hge'
          · exact min_eq_left hle
          · exfalso; rw [min_eq_right hge'] at hdp; linarith
        rcases hev with hfst | hsnd
        · exact ⟨d', t', hfst, ht0, ht1, rfl, h_at_fst hfst ht0 ht1 hp⟩
        · have hdp' : dist (vertex v : MetricGraph W)
              (edgePoint d'.symm (unitInterval.symm t')) ≤ 3 * δ := by
            rwa [edgePoint_symm]
          refine ⟨d'.symm, unitInterval.symm t', hsnd, sub_pos.mpr ht1, sub_lt_self 1 ht0,
            (edgePoint_symm d' t').symm, ?_⟩
          rw [← edgePoint_symm d' t']
          exact h_at_fst hsnd (sub_pos.mpr ht1) (sub_lt_self 1 ht0) hdp'
    rcases hy_not_far with hv_eq | ⟨d, t, hd_fst, ht0, ht1, hy_eq, hvy_eq⟩
    · have h0_mem : (0 : ℝ) ∈ Set.Icc (-δ) δ := ⟨by linarith, hδ_pos.le⟩
      refine ⟨0, h0_mem, ?_⟩
      dsimp only
      rw [add_zero, hs₀_v, ← hv_eq]
    · let r_y := (t : ℝ) * W.weight d.edge
      have hry_pos : 0 < r_y := mul_pos ht0 (W.dart_weight_pos d)
      have hry_3 : r_y ≤ 3 * δ := by dsimp only [r_y]; rw [← hvy_eq]; exact hvy_3
      have hy_on_circle : ∃ r_y' : ℝ, |r_y'| = r_y ∧ y = circleMap hs.1 (s₀ + r_y') := by
        by_cases h1 : d.edge = d₁.edge
        · have hd_eq : d = d₁ := ((dart_edge_eq_iff d d₁).mp h1).resolve_right fun hsym => by
            have : d₁.fst = d₁.snd := by rw [hd₁_fst, ← hd_fst, hsym]; rfl
            exact d₁.adj.ne this
          subst hd_eq
          have hry_mem : r_y ∈ Set.Ioc 0 δ₁ := ⟨hry_pos, by linarith⟩
          obtain ⟨_, _, h10, h11, _, _, hcm1, _⟩ := hmap r_y hry_mem
          refine ⟨-r_y, by rw [abs_neg, abs_of_pos hry_pos], ?_⟩
          rw [show s₀ + (-r_y) = s₀ - r_y by ring, hcm1, hy_eq]
          congr 1; ext; simp [r_y, mul_div_cancel_right₀ _ (W.dart_weight_pos d).ne']
        · by_cases h2 : d.edge = d₂.edge
          · have hd_eq : d = d₂ := ((dart_edge_eq_iff d d₂).mp h2).resolve_right fun hsym => by
              have : d₂.fst = d₂.snd := by rw [hd₂_fst, ← hd_fst, hsym]; rfl
              exact d₂.adj.ne this
            subst hd_eq
            have hry_mem : r_y ∈ Set.Ioc 0 δ₁ := ⟨hry_pos, by linarith⟩
            obtain ⟨_, _, _, _, h20, h21, _, hcm2⟩ := hmap r_y hry_mem
            refine ⟨r_y, abs_of_pos hry_pos, ?_⟩
            rw [hcm2, hy_eq]
            congr 1; ext; simp [r_y, mul_div_cancel_right₀ _ (W.dart_weight_pos d).ne']
          · exfalso
            have hw := W.dart_weight_pos d
            have htd0 : 0 ≤ r_y / W.weight d.edge := div_nonneg hry_pos.le hw.le
            have htd1 : r_y / W.weight d.edge ≤ 1 :=
              (div_le_one hw).mpr (by linarith [hδ16.trans (hwmin d)])
            have ht_eq : t = ⟨r_y / W.weight d.edge, htd0, htd1⟩ := by
              ext; simp [r_y, mul_div_cancel_right₀ _ hw.ne']
            rw [ht_eq] at hy_eq
            have hday_eq : dist a y = |sa| + r_y := by
              rw [hy_eq]
              exact dist_third_dart_signed W hs.1 hd₁_fst hd₂_fst hd_fst (Ne.symm h1) (Ne.symm h2)
                hwmin hvmin hδ_pos (by linarith) hδ16 hδv hs₀_v hmap hsa hry_pos hry_3 htd0 htd1
            have hdby_eq : dist b y = |sb| + r_y := by
              rw [hy_eq]
              exact dist_third_dart_signed W hs.1 hd₁_fst hd₂_fst hd_fst (Ne.symm h1) (Ne.symm h2)
                hwmin hvmin hδ_pos (by linarith) hδ16 hδv hs₀_v hmap hsb hry_pos hry_3 htd0 htd1
            rw [hday_eq, hdab] at hda_y
            rw [hdby_eq, _root_.dist_comm b a, hdab] at hdb_y
            have hops : (sa < 0 ∧ 0 < sb) ∨ (sb < 0 ∧ 0 < sa) := by
              rcases le_or_gt 0 sa with hsa0 | hsa0 <;> rcases le_or_gt 0 sb with hsb0 | hsb0
              · rw [abs_of_nonneg hsa0] at hda_y; rw [abs_of_nonneg hsb0] at hdb_y
                rcases le_total sa sb with h | h
                · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)] at hda_y hdb_y; linarith
                · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hda_y hdb_y; linarith
              · exact Or.inr ⟨hsb0, hsa0.lt_of_ne' fun h => by
                  subst h; rw [zero_sub, abs_neg, abs_of_neg hsb0] at hdb_y; linarith⟩
              · exact Or.inl ⟨hsa0, hsb0.lt_of_ne' fun h => by
                  subst h; rw [sub_zero, abs_of_neg hsa0] at hda_y; linarith⟩
              · rw [abs_of_neg hsa0] at hda_y; rw [abs_of_neg hsb0] at hdb_y
                rcases le_total sa sb with h | h
                · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)] at hda_y hdb_y; linarith
                · rw [abs_of_nonneg (sub_nonneg.mpr h)] at hda_y hdb_y; linarith
            have hry_le_abs : r_y ≤ |sa| ∧ r_y ≤ |sb| := by
              rcases hops with ⟨ha_n, hb_p⟩ | ⟨hb_n, ha_p⟩
              · rw [abs_of_neg ha_n] at hda_y; rw [abs_of_pos hb_p] at hdb_y
                rw [abs_of_neg (by linarith)] at hda_y hdb_y
                exact ⟨by rw [abs_of_neg ha_n]; linarith, by rw [abs_of_pos hb_p]; linarith⟩
              · rw [abs_of_pos ha_p] at hda_y; rw [abs_of_neg hb_n] at hdb_y
                rw [abs_of_pos (by linarith)] at hda_y hdb_y
                exact ⟨by rw [abs_of_pos ha_p]; linarith, by rw [abs_of_neg hb_n]; linarith⟩
            have hry_le_δ : r_y ≤ δ := hry_le_abs.1.trans (abs_le.mpr hsa)
            let r' := 3 / 4 * r_y
            have hr'_pos : 0 < r' := by positivity
            have hr'_le : r' ≤ δ := by dsimp only [r']; linarith
            have hd₁_w : 16 * δ ≤ W.weight d₁.edge := hδ16.trans (hwmin d₁)
            have hd₂_w : 16 * δ ≤ W.weight d₂.edge := hδ16.trans (hwmin d₂)
            let f_sw : (Fin 2 → MetricGraph W) → MetricGraph W := fun z => f ![z 1, z 0]
            have hf_sw_eq : f_sw = fun z : Fin 2 → MetricGraph W => f (fun i => z (![1, 0] i)) := by
              funext z; exact congrArg f (by ext i; fin_cases i <;> rfl)
            have f_swap_unam : ∀ p ∈ Set.range (circleMap hs.1), f_sw (fun _ => p) = p :=
              fun p hp => by
                have heq : ![p, p] = fun _ => p := by ext i; fin_cases i <;> rfl
                dsimp only [f_sw]; rw [heq]; exact hf_unam p hp
            have hsp_swap : (Mechanism.deterministic f_sw).IsStrategyProof := by
              rw [hf_sw_eq]
              exact merge_isStrategyProof hf_sp ![1, 0]
            rcases hops with ⟨ha_n, hb_p⟩ | ⟨hb_n, ha_p⟩
            · let r_a := -sa
              let r_b := sb
              have hra_mem : r_a ∈ Set.Ioc 0 δ₁ := ⟨neg_pos.mpr ha_n, by linarith [hsa.1]⟩
              have hrb_mem : r_b ∈ Set.Ioc 0 δ₁ := ⟨hb_p, by linarith [hsb.2]⟩
              have hr'_mem : r' ∈ Set.Ioc 0 δ₁ := ⟨hr'_pos, by linarith⟩
              obtain ⟨_, _, ha0, ha1, _, _, ha_cm, _⟩ := hmap r_a hra_mem
              obtain ⟨_, _, _, _, hb0, hb1, _, hb_cm⟩ := hmap r_b hrb_mem
              obtain ⟨_, _, ha'0, ha'1, hb'0, hb'1, ha'_cm, hb'_cm⟩ := hmap r' hr'_mem
              have hy_eq' : f ![edgePoint d₁ ⟨r_a / W.weight d₁.edge, ha0, ha1⟩,
                  edgePoint d₂ ⟨r_b / W.weight d₂.edge, hb0, hb1⟩] =
                  edgePoint d ⟨r_y / W.weight d.edge, htd0, htd1⟩ := by
                rw [← ha_cm, ← hb_cm, show s₀ - r_a = s₀ + sa by ring,
                  show s₀ + r_b = s₀ + sb by rfl]
                dsimp only [y, a, b] at hy_eq
                exact hy_eq
              have hb1' : dist (edgePoint d₁ ⟨r' / W.weight d₁.edge, ha'0, ha'1⟩)
                  (f ![edgePoint d₁ ⟨r' / W.weight d₁.edge, ha'0, ha'1⟩,
                    edgePoint d₂ ⟨r' / W.weight d₂.edge, hb'0, hb'1⟩]) ≤ 1 / 4 * r_y :=
                half_step_third_dart_bound W hd₁_fst hd₂_fst hd_fst hd₁₂ (Ne.symm h1) (Ne.symm h2)
                  hwmin hvmin hδ16 hδv hry_pos hry_le_δ (by linarith [hsa.1])
                  (by linarith [hry_le_abs.1, abs_of_neg ha_n]) (by linarith [hsb.2])
                  (by linarith [hry_le_abs.2, abs_of_pos hb_p]) ha0 ha1 hb0 hb1 htd0 htd1
                  ha'0 ha'1 hb'0 hb'1 hf_sp
                  (by
                    rw [← hb'_cm, show ![circleMap hs.1 (s₀ + r'), circleMap hs.1 (s₀ + r')] =
                        fun _ => circleMap hs.1 (s₀ + r') by ext i; fin_cases i <;> rfl]
                    exact hf_unam _ ⟨_, rfl⟩)
                  hy_eq'
              have hy_eq'' : f_sw
                  ![edgePoint d₂ ⟨r_b / W.weight d₂.edge, hb0, hb1⟩,
                    edgePoint d₁ ⟨r_a / W.weight d₁.edge, ha0, ha1⟩] =
                  edgePoint d ⟨r_y / W.weight d.edge, htd0, htd1⟩ := by
                dsimp only [f_sw]; exact hy_eq'
              have hb2' : dist (edgePoint d₂ ⟨r' / W.weight d₂.edge, hb'0, hb'1⟩)
                  (f ![edgePoint d₁ ⟨r' / W.weight d₁.edge, ha'0, ha'1⟩,
                    edgePoint d₂ ⟨r' / W.weight d₂.edge, hb'0, hb'1⟩]) ≤ 1 / 4 * r_y := by
                have := half_step_third_dart_bound W hd₂_fst hd₁_fst hd_fst hd₁₂.symm (Ne.symm h2)
                  (Ne.symm h1) hwmin hvmin hδ16 hδv hry_pos hry_le_δ (by linarith [hsb.2])
                  (by linarith [hry_le_abs.2, abs_of_pos hb_p]) (by linarith [hsa.1])
                  (by linarith [hry_le_abs.1, abs_of_neg ha_n]) hb0 hb1 ha0 ha1 htd0 htd1
                  hb'0 hb'1 ha'0 ha'1 hsp_swap
                  (by rw [← ha'_cm]; exact f_swap_unam _ ⟨_, rfl⟩)
                  hy_eq''
                exact this
              have hdist_ab' : dist (edgePoint d₁ ⟨r' / W.weight d₁.edge, ha'0, ha'1⟩)
                  (edgePoint d₂ ⟨r' / W.weight d₂.edge, hb'0, hb'1⟩) = 3 / 2 * r_y := by
                rw [dist_edgePoint_ray_of_edge_ne W hd₁_fst hd₂_fst hd₁₂ hwmin hvmin hδ16 hδv
                  hr'_pos.le (by linarith) hr'_pos.le (by linarith) ha'0 ha'1 hb'0 hb'1]
                dsimp only [r']; ring
              have htri := dist_triangle
                (edgePoint d₁ ⟨r' / W.weight d₁.edge, ha'0, ha'1⟩)
                (f ![edgePoint d₁ ⟨r' / W.weight d₁.edge, ha'0, ha'1⟩,
                  edgePoint d₂ ⟨r' / W.weight d₂.edge, hb'0, hb'1⟩])
                (edgePoint d₂ ⟨r' / W.weight d₂.edge, hb'0, hb'1⟩)
              rw [_root_.dist_comm] at hb2'
              linarith
            · let r_a := sa
              let r_b := -sb
              have hra_mem : r_a ∈ Set.Ioc 0 δ₁ := ⟨ha_p, by linarith [hsa.2]⟩
              have hrb_mem : r_b ∈ Set.Ioc 0 δ₁ := ⟨neg_pos.mpr hb_n, by linarith [hsb.1]⟩
              have hr'_mem : r' ∈ Set.Ioc 0 δ₁ := ⟨hr'_pos, by linarith⟩
              obtain ⟨_, _, _, _, ha0, ha1, _, ha_cm⟩ := hmap r_a hra_mem
              obtain ⟨_, _, hb0, hb1, _, _, hb_cm, _⟩ := hmap r_b hrb_mem
              obtain ⟨_, _, hb'0, hb'1, ha'0, ha'1, hb'_cm, ha'_cm⟩ := hmap r' hr'_mem
              have hy_eq' : f ![edgePoint d₂ ⟨r_a / W.weight d₂.edge, ha0, ha1⟩,
                  edgePoint d₁ ⟨r_b / W.weight d₁.edge, hb0, hb1⟩] =
                  edgePoint d ⟨r_y / W.weight d.edge, htd0, htd1⟩ := by
                rw [← ha_cm, ← hb_cm, show s₀ + r_a = s₀ + sa by rfl,
                  show s₀ - r_b = s₀ + sb by ring]
                dsimp only [y, a, b] at hy_eq
                exact hy_eq
              have hb1' : dist (edgePoint d₂ ⟨r' / W.weight d₂.edge, ha'0, ha'1⟩)
                  (f ![edgePoint d₂ ⟨r' / W.weight d₂.edge, ha'0, ha'1⟩,
                    edgePoint d₁ ⟨r' / W.weight d₁.edge, hb'0, hb'1⟩]) ≤ 1 / 4 * r_y :=
                half_step_third_dart_bound W hd₂_fst hd₁_fst hd_fst hd₁₂.symm (Ne.symm h2)
                  (Ne.symm h1) hwmin hvmin hδ16 hδv hry_pos hry_le_δ (by linarith [hsa.2])
                  (by linarith [hry_le_abs.1, abs_of_pos ha_p]) (by linarith [hsb.1])
                  (by linarith [hry_le_abs.2, abs_of_neg hb_n]) ha0 ha1 hb0 hb1 htd0 htd1
                  ha'0 ha'1 hb'0 hb'1 hf_sp
                  (by
                    rw [← hb'_cm, show ![circleMap hs.1 (s₀ - r'), circleMap hs.1 (s₀ - r')] =
                        fun _ => circleMap hs.1 (s₀ - r') by ext i; fin_cases i <;> rfl]
                    exact hf_unam _ ⟨_, rfl⟩)
                  hy_eq'
              have hy_eq'' : f_sw
                  ![edgePoint d₁ ⟨r_b / W.weight d₁.edge, hb0, hb1⟩,
                    edgePoint d₂ ⟨r_a / W.weight d₂.edge, ha0, ha1⟩] =
                  edgePoint d ⟨r_y / W.weight d.edge, htd0, htd1⟩ := by
                dsimp only [f_sw]; exact hy_eq'
              have hb2' : dist (edgePoint d₁ ⟨r' / W.weight d₁.edge, hb'0, hb'1⟩)
                  (f ![edgePoint d₂ ⟨r' / W.weight d₂.edge, ha'0, ha'1⟩,
                    edgePoint d₁ ⟨r' / W.weight d₁.edge, hb'0, hb'1⟩]) ≤ 1 / 4 * r_y := by
                have := half_step_third_dart_bound W hd₁_fst hd₂_fst hd_fst hd₁₂ (Ne.symm h1)
                  (Ne.symm h2) hwmin hvmin hδ16 hδv hry_pos hry_le_δ (by linarith [hsb.1])
                  (by linarith [hry_le_abs.2, abs_of_neg hb_n]) (by linarith [hsa.2])
                  (by linarith [hry_le_abs.1, abs_of_pos ha_p]) hb0 hb1 ha0 ha1 htd0 htd1
                  hb'0 hb'1 ha'0 ha'1 hsp_swap
                  (by rw [← ha'_cm]; exact f_swap_unam _ ⟨_, rfl⟩)
                  hy_eq''
                exact this
              have hdist_ab' : dist (edgePoint d₂ ⟨r' / W.weight d₂.edge, ha'0, ha'1⟩)
                  (edgePoint d₁ ⟨r' / W.weight d₁.edge, hb'0, hb'1⟩) = 3 / 2 * r_y := by
                rw [dist_edgePoint_ray_of_edge_ne W hd₂_fst hd₁_fst hd₁₂.symm hwmin hvmin hδ16 hδv
                  hr'_pos.le (by linarith) hr'_pos.le (by linarith) ha'0 ha'1 hb'0 hb'1]
                dsimp only [r']; ring
              have htri := dist_triangle
                (edgePoint d₂ ⟨r' / W.weight d₂.edge, ha'0, ha'1⟩)
                (f ![edgePoint d₂ ⟨r' / W.weight d₂.edge, ha'0, ha'1⟩,
                  edgePoint d₁ ⟨r' / W.weight d₁.edge, hb'0, hb'1⟩])
                (edgePoint d₁ ⟨r' / W.weight d₁.edge, hb'0, hb'1⟩)
              rw [_root_.dist_comm] at hb2'
              linarith
      obtain ⟨r_y', habs_ry', hy_cm⟩ := hy_on_circle
      have hday_abs : dist a y = |r_y' - sa| := by
        rw [hy_cm]
        refine (circleMap_dist_eq_of_le hs ?_).trans ?_
        · have h1 := abs_le.mpr hsa
          have h2 := abs_sub sa r_y'
          rw [habs_ry'] at h2
          dsimp only [L] at hδL
          linarith [show |(s₀ + sa) - (s₀ + r_y')| = |sa - r_y'| by ring_nf]
        · rw [show s₀ + sa - (s₀ + r_y') = -(r_y' - sa) by ring, abs_neg]
      have hdby_abs : dist b y = |r_y' - sb| := by
        rw [hy_cm]
        refine (circleMap_dist_eq_of_le hs ?_).trans ?_
        · have h1 := abs_le.mpr hsb
          have h2 := abs_sub sb r_y'
          rw [habs_ry'] at h2
          dsimp only [L] at hδL
          linarith [show |(s₀ + sb) - (s₀ + r_y')| = |sb - r_y'| by ring_nf]
        · rw [show s₀ + sb - (s₀ + r_y') = -(r_y' - sb) by ring, abs_neg]
      rw [hday_abs, hdab, abs_sub_comm sa sb] at hda_y
      rw [hdby_abs, _root_.dist_comm b a, hdab] at hdb_y
      exact ⟨r_y', between_of_abs_le hsa hsb hda_y hdb_y, hy_cm.symm⟩

private theorem local_moulin_circle {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p)
    (s₀ : ℝ) :
    ∃ δ α₀ : ℝ, 0 < δ ∧ δ ≤ walkLength W.weight c / 16 ∧
      α₀ ∈ Set.Icc (s₀ - δ) (s₀ + δ) ∧
      ∀ u v : ℝ, u ∈ Set.Icc (s₀ - δ) (s₀ + δ) → v ∈ Set.Icc (s₀ - δ) (s₀ + δ) → u ≤ v →
        f ![circleMap hs.1 u, circleMap hs.1 v] = circleMap hs.1 (min (max α₀ u) v) := by
  obtain ⟨δ, hδ_pos, hδL, hinv⟩ := local_invariance_circle W hs hf_sp hf_unam s₀
  let φ : Set.Icc (0 : ℝ) (2 * δ) → MetricGraph W := fun t => circleMap hs.1 (s₀ - δ + (t : ℝ))
  have hφ : Isometry φ := by
    rw [isometry_iff_dist_eq]
    intro t₁ t₂
    dsimp only [φ]
    rw [Subtype.dist_eq, Real.dist_eq]
    have hle_L : |(s₀ - δ + (t₁ : ℝ)) - (s₀ - δ + (t₂ : ℝ))| ≤ walkLength W.weight c / 2 := by
      have hsub : (s₀ - δ + (t₁ : ℝ)) - (s₀ - δ + (t₂ : ℝ)) = (t₁ : ℝ) - (t₂ : ℝ) := by ring
      rw [hsub]
      have h11 := t₁.2.1
      have h12 := t₁.2.2
      have h21 := t₂.2.1
      have h22 := t₂.2.2
      have habs : |(t₁ : ℝ) - (t₂ : ℝ)| ≤ 2 * δ := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      linarith [hδL, walkLength_pos_of_not_nil hs.1.not_nil]
    rw [circleMap_dist_eq_of_le hs hle_L,
      show (s₀ - δ + (t₁ : ℝ)) - (s₀ - δ + (t₂ : ℝ)) = (t₁ : ℝ) - (t₂ : ℝ) by ring]
  have hrange : ∀ x : Fin 2 → MetricGraph W,
      (∀ i, x i ∈ Set.range φ) → f x ∈ Set.range φ := by
    intro x hx
    obtain ⟨⟨t0, ht0⟩, h0⟩ := hx 0
    obtain ⟨⟨t1, ht1⟩, h1⟩ := hx 1
    have h0' : x 0 = circleMap hs.1 (s₀ + (t0 - δ)) := by
      dsimp only [φ] at h0
      rw [← h0]
      congr 1; ring
    have h1' : x 1 = circleMap hs.1 (s₀ + (t1 - δ)) := by
      dsimp only [φ] at h1
      rw [← h1]
      congr 1; ring
    have hx_eq : x = ![circleMap hs.1 (s₀ + (t0 - δ)), circleMap hs.1 (s₀ + (t1 - δ))] := by
      ext i; fin_cases i <;> assumption
    rw [hx_eq]
    obtain ⟨r, hr, hreq⟩ := hinv (t0 - δ) ⟨by linarith [ht0.1], by linarith [ht0.2]⟩
      (t1 - δ) ⟨by linarith [ht1.1], by linarith [ht1.2]⟩
    refine ⟨⟨r + δ, by linarith [hr.1], by linarith [hr.2]⟩, ?_⟩
    dsimp only [φ]
    rw [← hreq]
    congr 1; ring
  have honto : ∀ y ∈ Set.range φ,
      ∃ x : Fin 2 → MetricGraph W, (∀ i, x i ∈ Set.range φ) ∧ f x = y := by
    intro y hy
    refine ⟨fun _ => y, fun _ => hy, hf_unam y ?_⟩
    obtain ⟨t, rfl⟩ := hy
    exact ⟨_, rfl⟩
  obtain ⟨E, hE⟩ := moulinScheme_of_isometry (by linarith) φ hφ hf_sp hrange honto
  refine ⟨δ, s₀ - δ + E.alpha {0}, hδ_pos, hδL,
    ⟨by linarith [(E.mem_Icc {0}).1], by linarith [(E.mem_Icc {0}).2]⟩, fun u v hu hv huv => ?_⟩
  let tu : Set.Icc (0 : ℝ) (2 * δ) := ⟨u - (s₀ - δ), by linarith [hu.1], by linarith [hu.2]⟩
  let tv : Set.Icc (0 : ℝ) (2 * δ) := ⟨v - (s₀ - δ), by linarith [hv.1], by linarith [hv.2]⟩
  have hev := hE ![tu, tv]
  have hcm : (fun i => φ (![tu, tv] i)) = ![circleMap hs.1 u, circleMap hs.1 v] := by
    ext i
    fin_cases i
    · change circleMap hs.1 (s₀ - δ + (u - (s₀ - δ))) = circleMap hs.1 u
      congr 1; ring
    · change circleMap hs.1 (s₀ - δ + (v - (s₀ - δ))) = circleMap hs.1 v
      congr 1; ring
  rw [hcm] at hev
  rw [hev]
  have hm := moulinScheme_finTwo_eq E ![tu, tv]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hm
  have hmaxv : max (E.alpha {1}) (tv : ℝ) ≥ (tv : ℝ) := le_max_right _ _
  have hmax_uv : max (tu : ℝ) (tv : ℝ) = (tv : ℝ) :=
    max_eq_right (by dsimp only [tu, tv]; linarith)
  have hminv : min (max (E.alpha {1}) (tv : ℝ)) (max (tu : ℝ) (tv : ℝ)) = (tv : ℝ) := by
    rw [hmax_uv, min_eq_right hmaxv]
  rw [hminv] at hm
  dsimp only [φ]
  congr 1
  rw [hm]
  dsimp only [tu, tv]
  have h1 : s₀ - δ + max (E.alpha {0}) (u - (s₀ - δ)) = max (s₀ - δ + E.alpha {0}) u := by
    rcases le_total (E.alpha {0}) (u - (s₀ - δ)) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]
  rw [← h1]
  rcases le_total (max (E.alpha {0}) (u - (s₀ - δ))) (v - (s₀ - δ)) with h | h
  · rw [min_eq_left h, min_eq_left (by linarith)]
  · rw [min_eq_right h, min_eq_right (by linarith)]; ring

private theorem orientation_dichotomy_circle {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ((∀ u r : ℝ, 0 ≤ r → r ≤ δ₀ →
          f ![circleMap hs.1 u, circleMap hs.1 (u + r)] = circleMap hs.1 u) ∨
       (∀ u r : ℝ, 0 ≤ r → r ≤ δ₀ →
          f ![circleMap hs.1 u, circleMap hs.1 (u + r)] = circleMap hs.1 (u + r))) := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  let R_left : Set ℝ := { s | ∃ η > 0, ∀ u v : ℝ, s - η < u → u ≤ v → v < s + η →
    f ![circleMap hs.1 u, circleMap hs.1 v] = circleMap hs.1 u }
  let R_right : Set ℝ := { s | ∃ η > 0, ∀ u v : ℝ, s - η < u → u ≤ v → v < s + η →
    f ![circleMap hs.1 u, circleMap hs.1 v] = circleMap hs.1 v }
  have hopen_l : IsOpen R_left := by
    rw [Metric.isOpen_iff]
    rintro s ⟨η, hη, hs_l⟩
    refine ⟨η / 2, by linarith, fun t ht => ⟨η / 2, by linarith, fun u v hu huv hv => ?_⟩⟩
    rw [Metric.mem_ball, Real.dist_eq] at ht
    exact hs_l u v (by linarith [(abs_lt.mp ht).1]) huv (by linarith [(abs_lt.mp ht).2])
  have hopen_r : IsOpen R_right := by
    rw [Metric.isOpen_iff]
    rintro s ⟨η, hη, hs_r⟩
    refine ⟨η / 2, by linarith, fun t ht => ⟨η / 2, by linarith, fun u v hu huv hv => ?_⟩⟩
    rw [Metric.mem_ball, Real.dist_eq] at ht
    exact hs_r u v (by linarith [(abs_lt.mp ht).1]) huv (by linarith [(abs_lt.mp ht).2])
  have hdisj : Disjoint R_left R_right := by
    rw [Set.disjoint_left]
    rintro s ⟨η₁, hη₁, hl⟩ ⟨η₂, hη₂, hr⟩
    let η := min η₁ η₂
    have hη : 0 < η := lt_min hη₁ hη₂
    let ε := min (η / 2) (L / 4)
    have hε : 0 < ε := by positivity
    have h1 := hl s (s + ε) (by linarith [min_le_left η₁ η₂]) (by linarith)
      (by linarith [min_le_left η₁ η₂, min_le_left (η / 2) (L / 4)])
    have h2 := hr s (s + ε) (by linarith [min_le_right η₁ η₂]) (by linarith)
      (by linarith [min_le_right η₁ η₂, min_le_left (η / 2) (L / 4)])
    have heq := h1.symm.trans h2
    have hd : dist (circleMap hs.1 s) (circleMap hs.1 (s + ε)) = ε := by
      refine (circleMap_dist_eq_of_le hs ?_).trans ?_
      · rw [sub_add_cancel_left, abs_neg, abs_of_pos hε]
        linarith [min_le_right (η / 2) (L / 4)]
      · rw [sub_add_cancel_left, abs_neg, abs_of_pos hε]
    rw [heq, _root_.dist_self] at hd
    linarith
  have hper_l : ∀ s : ℝ, s ∈ R_left → s + L ∈ R_left := by
    rintro s ⟨η, hη, hl⟩
    refine ⟨η, hη, fun u v hu huv hv => ?_⟩
    have hper_u : circleMap hs.1 u = circleMap hs.1 (u - L) := by
      conv_lhs => rw [show u = (u - L) + L by ring]
      exact circleMap_periodic hs.1 (u - L)
    have hper_v : circleMap hs.1 v = circleMap hs.1 (v - L) := by
      conv_lhs => rw [show v = (v - L) + L by ring]
      exact circleMap_periodic hs.1 (v - L)
    rw [hper_u, hper_v]
    exact hl (u - L) (v - L) (by linarith) (by linarith) (by linarith)
  have hper_r : ∀ s : ℝ, s ∈ R_right → s + L ∈ R_right := by
    rintro s ⟨η, hη, hr⟩
    refine ⟨η, hη, fun u v hu huv hv => ?_⟩
    have hper_u : circleMap hs.1 u = circleMap hs.1 (u - L) := by
      conv_lhs => rw [show u = (u - L) + L by ring]
      exact circleMap_periodic hs.1 (u - L)
    have hper_v : circleMap hs.1 v = circleMap hs.1 (v - L) := by
      conv_lhs => rw [show v = (v - L) + L by ring]
      exact circleMap_periodic hs.1 (v - L)
    rw [hper_u, hper_v]
    exact hr (u - L) (v - L) (by linarith) (by linarith) (by linarith)
  have hlocal_classify : ∀ s : ℝ,
      s ∈ R_left ∨ s ∈ R_right ∨
        ∃ δ > 0, Set.Ioo (s - δ) s ⊆ R_right ∧ Set.Ioo s (s + δ) ⊆ R_left := by
    intro s
    obtain ⟨δ, α₀, hδ_pos, _, hα, hm⟩ := local_moulin_circle W hs hf_sp hf_unam s
    rcases lt_trichotomy α₀ s with hlt | rfl | hgt
    · left
      refine ⟨min δ (s - α₀), by positivity, fun u v hu huv hv => ?_⟩
      have huI : u ∈ Set.Icc (s - δ) (s + δ) :=
        ⟨by linarith [min_le_left δ (s - α₀)], by linarith [min_le_left δ (s - α₀)]⟩
      have hvI : v ∈ Set.Icc (s - δ) (s + δ) :=
        ⟨by linarith [min_le_left δ (s - α₀)], by linarith [min_le_left δ (s - α₀)]⟩
      have hαu : α₀ ≤ u := by linarith [min_le_right δ (s - α₀)]
      rw [hm u v huI hvI huv, max_eq_right hαu, min_eq_left huv]
    · right; right
      refine ⟨δ, hδ_pos, fun t ht => ?_, fun t ht => ?_⟩
      · refine ⟨min (α₀ - t) (t - (α₀ - δ)), lt_min (sub_pos.mpr ht.2) (sub_pos.mpr ht.1),
            fun u v hu huv hv => ?_⟩
        have huI : u ∈ Set.Icc (α₀ - δ) (α₀ + δ) :=
          ⟨by linarith [min_le_right (α₀ - t) (t - (α₀ - δ))],
            by linarith [min_le_left (α₀ - t) (t - (α₀ - δ))]⟩
        have hvI : v ∈ Set.Icc (α₀ - δ) (α₀ + δ) :=
          ⟨by linarith [min_le_right (α₀ - t) (t - (α₀ - δ))],
            by linarith [min_le_left (α₀ - t) (t - (α₀ - δ))]⟩
        have hvα : v ≤ α₀ := by linarith [min_le_left (α₀ - t) (t - (α₀ - δ))]
        rw [hm u v huI hvI huv, max_eq_left (huv.trans hvα), min_eq_right hvα]
      · refine ⟨min (t - α₀) (α₀ + δ - t), lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2),
            fun u v hu huv hv => ?_⟩
        have huI : u ∈ Set.Icc (α₀ - δ) (α₀ + δ) :=
          ⟨by linarith [min_le_left (t - α₀) (α₀ + δ - t), ht.1],
            by linarith [min_le_right (t - α₀) (α₀ + δ - t)]⟩
        have hvI : v ∈ Set.Icc (α₀ - δ) (α₀ + δ) :=
          ⟨by linarith [min_le_left (t - α₀) (α₀ + δ - t), ht.1],
            by linarith [min_le_right (t - α₀) (α₀ + δ - t)]⟩
        have hαu : α₀ ≤ u := by linarith [min_le_left (t - α₀) (α₀ + δ - t)]
        rw [hm u v huI hvI huv, max_eq_right hαu, min_eq_left huv]
    · right; left
      refine ⟨min δ (α₀ - s), by positivity, fun u v hu huv hv => ?_⟩
      have huI : u ∈ Set.Icc (s - δ) (s + δ) :=
        ⟨by linarith [min_le_left δ (α₀ - s)], by linarith [min_le_left δ (α₀ - s)]⟩
      have hvI : v ∈ Set.Icc (s - δ) (s + δ) :=
        ⟨by linarith [min_le_left δ (α₀ - s)], by linarith [min_le_left δ (α₀ - s)]⟩
      have hvα : v ≤ α₀ := by linarith [min_le_right δ (α₀ - s)]
      rw [hm u v huI hvI huv, max_eq_left (huv.trans hvα), min_eq_right hvα]
  have hcover : R_left ∪ R_right = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro s₀
    by_contra hnot
    have hs₀_nl : s₀ ∉ R_left := fun h => hnot (Or.inl h)
    have hs₀_nr : s₀ ∉ R_right := fun h => hnot (Or.inr h)
    rcases hlocal_classify s₀ with hl | hr | ⟨δ₀, hδ₀, hIoo_r, hIoo_l⟩
    · exact hs₀_nl hl
    · exact hs₀_nr hr
    · let S_l : Set ℝ := { t | s₀ < t ∧ Set.Ioo s₀ t ⊆ R_left }
      have hSl_ne : S_l.Nonempty := ⟨s₀ + δ₀, by linarith, hIoo_l⟩
      have hSl_bdd : BddAbove S_l := by
        refine ⟨s₀ + L, fun t ⟨ht_gt, ht_sub⟩ => ?_⟩
        by_contra hgt
        push Not at hgt
        have hpt : s₀ + L - min (δ₀ / 2) (L / 2) ∈ Set.Ioo s₀ t ∩ R_right := by
          have hx_gt : s₀ < s₀ + L - min (δ₀ / 2) (L / 2) := by
            linarith [min_le_right (δ₀ / 2) (L / 2)]
          have hx_lt : s₀ + L - min (δ₀ / 2) (L / 2) < t := by
            have hmin_pos : 0 < min (δ₀ / 2) (L / 2) := by positivity
            linarith
          have hsub_mem : (s₀ + L - min (δ₀ / 2) (L / 2)) - L ∈ Set.Ioo (s₀ - δ₀) s₀ := by
            have hmin_pos : 0 < min (δ₀ / 2) (L / 2) := by positivity
            exact ⟨by linarith [min_le_left (δ₀ / 2) (L / 2)], by linarith⟩
          have hr1 := hIoo_r hsub_mem
          have hper := hper_r _ hr1
          refine ⟨⟨hx_gt, hx_lt⟩, ?_⟩
          simpa only [sub_add_cancel] using hper
        exact Set.disjoint_left.mp hdisj (ht_sub hpt.1) hpt.2
      let c₁ := sSup S_l
      have hc₁_gt : s₀ < c₁ := by
        have := le_csSup hSl_bdd ⟨by linarith, hIoo_l⟩
        linarith
      have hc₁_sub : Set.Ioo s₀ c₁ ⊆ R_left := by
        intro x ⟨hx1, hx2⟩
        obtain ⟨t, ⟨_, htsub⟩, hxt⟩ := exists_lt_of_lt_csSup hSl_ne hx2
        exact htsub ⟨hx1, hxt⟩
      have hc₁_nl : c₁ ∉ R_left := by
        intro hc₁_in
        obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hopen_l c₁ hc₁_in
        have hmem : c₁ + η / 2 ∈ S_l := by
          refine ⟨by linarith, fun x ⟨hx1, hx2⟩ => ?_⟩
          rcases lt_or_ge x c₁ with h | h
          · exact hc₁_sub ⟨hx1, h⟩
          · refine hball ?_
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            exact ⟨by linarith, by linarith⟩
        linarith [le_csSup hSl_bdd hmem]
      rcases hlocal_classify c₁ with hl | hr | ⟨δ₁, hδ₁, hIoo_r1, _⟩
      · exact hc₁_nl hl
      · obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hopen_r c₁ hr
        let x := max (s₀ + (c₁ - s₀) / 2) (c₁ - η / 2)
        have hx1 : x ∈ Set.Ioo s₀ c₁ :=
          ⟨by linarith [le_max_left (s₀ + (c₁ - s₀) / 2) (c₁ - η / 2)],
            max_lt_iff.mpr ⟨by linarith, by linarith⟩⟩
        have hx2 : x ∈ R_right := by
          refine hball ?_
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          exact ⟨by linarith [le_max_right (s₀ + (c₁ - s₀) / 2) (c₁ - η / 2)], by linarith [hx1.2]⟩
        exact Set.disjoint_left.mp hdisj (hc₁_sub hx1) hx2
      · let x := max (s₀ + (c₁ - s₀) / 2) (c₁ - δ₁ / 2)
        have hx1 : x ∈ Set.Ioo s₀ c₁ :=
          ⟨by linarith [le_max_left (s₀ + (c₁ - s₀) / 2) (c₁ - δ₁ / 2)],
            max_lt_iff.mpr ⟨by linarith, by linarith⟩⟩
        have hx2 : x ∈ R_right :=
          hIoo_r1 ⟨by linarith [le_max_right (s₀ + (c₁ - s₀) / 2) (c₁ - δ₁ / 2)], hx1.2⟩
        exact Set.disjoint_left.mp hdisj (hc₁_sub hx1) hx2
  have hpre : IsPreconnected (Set.univ : Set ℝ) := PreconnectedSpace.isPreconnected_univ
  have hcomp : Set.univ ⊆ R_left ∨ Set.univ ⊆ R_right := by
    by_cases h0 : (0 : ℝ) ∈ R_left
    · left
      exact hpre.subset_left_of_subset_union hopen_l hopen_r hdisj
        (fun x _ => by rw [hcover]; trivial) ⟨0, Set.mem_univ _, h0⟩
    · right
      have h0r : (0 : ℝ) ∈ R_right := by
        have : (0 : ℝ) ∈ R_left ∪ R_right := by rw [hcover]; trivial
        exact this.resolve_left h0
      exact hpre.subset_left_of_subset_union hopen_r hopen_l hdisj.symm
        (fun x _ => by rw [Set.union_comm, hcover]; trivial) ⟨0, Set.mem_univ _, h0r⟩
  have compact_step : ∀ (g : ℝ → ℝ → Prop),
      (∀ s ∈ Set.Icc 0 L, ∃ η > 0, ∀ u v : ℝ, s - η < u → u ≤ v → v < s + η → g u v) →
      (∀ (u v : ℝ) (m : ℤ), g u v → g (u + (m : ℝ) * L) (v + (m : ℝ) * L)) →
      ∃ δ₀ > 0, ∀ u r : ℝ, 0 ≤ r → r ≤ δ₀ → g u (u + r) := by
    intro g hg hg_per
    have hcov : Set.Icc 0 L ⊆ ⋃ (s : Set.Icc 0 L),
        Metric.ball (s : ℝ) ((hg s s.2).choose / 2) := by
      intro s hs_mem
      rw [Set.mem_iUnion]
      refine ⟨⟨s, hs_mem⟩, Metric.mem_ball_self (by linarith [(hg s hs_mem).choose_spec.1])⟩
    obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover
      (fun s : Set.Icc 0 L => Metric.ball (s : ℝ) ((hg s s.2).choose / 2))
      (fun _ => Metric.isOpen_ball) hcov
    have ht_ne : t.Nonempty := by
      by_contra hte
      rw [Finset.not_nonempty_iff_eq_empty] at hte
      have h0 : (0 : ℝ) ∈ Set.Icc 0 L := ⟨le_rfl, hL.le⟩
      have := ht h0
      simp [hte] at this
    let δ₀ := t.inf' ht_ne fun s => (hg s s.2).choose / 2
    have hδ₀ : 0 < δ₀ := by
      rw [Finset.lt_inf'_iff]
      intro s _
      linarith [(hg s s.2).choose_spec.1]
    refine ⟨δ₀, hδ₀, fun u r hr0 hrδ => ?_⟩
    let k : ℤ := ⌊u / L⌋
    let u' := u - (k : ℝ) * L
    have hu'0 : 0 ≤ u' := by
      have := Int.floor_le (u / L)
      nlinarith [div_mul_cancel₀ u hL.ne']
    have hu'L : u' ≤ L := by
      have := Int.lt_floor_add_one (u / L)
      nlinarith [div_mul_cancel₀ u hL.ne']
    have hu'_mem := ht ⟨hu'0, hu'L⟩
    simp only [Set.mem_iUnion, exists_prop, Metric.mem_ball, Real.dist_eq] at hu'_mem
    obtain ⟨s, hs_mem, hdist⟩ := hu'_mem
    let ηs := (hg s s.2).choose
    have hηs : ∀ x y : ℝ, (s : ℝ) - ηs < x → x ≤ y → y < (s : ℝ) + ηs → g x y :=
      (hg s s.2).choose_spec.2
    have hδs : δ₀ ≤ ηs / 2 := Finset.inf'_le (fun s : Set.Icc 0 L => (hg s s.2).choose / 2) hs_mem
    have hg_u' : g u' (u' + r) := by
      refine hηs u' (u' + r) (by linarith [(abs_lt.mp hdist).1]) (by linarith)
        (by linarith [(abs_lt.mp hdist).2, hδs])
    have hu_eq : u' + (k : ℝ) * L = u := by dsimp only [u']; ring
    have hur_eq : (u' + r) + (k : ℝ) * L = u + r := by dsimp only [u']; ring
    rw [← hur_eq, ← hu_eq]
    exact hg_per u' (u' + r) k hg_u'
  rcases hcomp with h_all_l | h_all_r
  · obtain ⟨δ₀, hδ₀, hstep⟩ := compact_step
      (fun u v => f ![circleMap hs.1 u, circleMap hs.1 v] = circleMap hs.1 u)
      (fun s _ => h_all_l (Set.mem_univ s))
      (fun u v m h => by
        simpa only [L, circleMap_add_int_mul hs.1 u m, circleMap_add_int_mul hs.1 v m] using h)
    exact ⟨δ₀, hδ₀, Or.inl hstep⟩
  · obtain ⟨δ₀, hδ₀, hstep⟩ := compact_step
      (fun u v => f ![circleMap hs.1 u, circleMap hs.1 v] = circleMap hs.1 v)
      (fun s _ => h_all_r (Set.mem_univ s))
      (fun u v m h => by
        simpa only [L, circleMap_add_int_mul hs.1 u m, circleMap_add_int_mul hs.1 v m] using h)
    exact ⟨δ₀, hδ₀, Or.inr hstep⟩

private theorem extend_dir_half {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p)
    {σ δ₀ : ℝ} (hσ : σ = 1 ∨ σ = -1) (hδ₀ : 0 < δ₀)
    (hloc : ∀ u r : ℝ, 0 ≤ r → r ≤ δ₀ →
      f ![circleMap hs.1 u, circleMap hs.1 (u + σ * r)] = circleMap hs.1 u) :
    ∀ u r : ℝ, 0 ≤ r → r < walkLength W.weight c / 2 →
      f ![circleMap hs.1 u, circleMap hs.1 (u + σ * r)] = circleMap hs.1 u := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  have hσ_abs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ_sq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  let hsp := (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp
  let S : Set ℝ := { r | r ∈ Set.Ico 0 (L / 2) ∧ ∀ r' ∈ Set.Icc 0 r, ∀ s : ℝ,
    f ![circleMap hs.1 s, circleMap hs.1 (s + σ * r')] = circleMap hs.1 s }
  have hS_ne : S.Nonempty := ⟨0, ⟨le_rfl, by positivity⟩, fun r' hr' s => by
    have : r' = 0 := le_antisymm hr'.2 hr'.1
    subst this
    simpa only [mul_zero, add_zero] using hloc s 0 le_rfl hδ₀.le⟩
  have hS_bdd : BddAbove S := ⟨L / 2, fun r hr => hr.1.2.le⟩
  let R := sSup S
  have hR_pos : 0 < R := by
    let r₀ := min (δ₀ / 2) (L / 4)
    have hr₀_pos : 0 < r₀ := by positivity
    have hr₀_mem : r₀ ∈ S := ⟨⟨hr₀_pos.le, by linarith [min_le_right (δ₀ / 2) (L / 4)]⟩,
      fun r' hr' s => hloc s r' hr'.1 (hr'.2.trans (by linarith [min_le_left (δ₀ / 2) (L / 4)]))⟩
    exact hr₀_pos.trans_le (le_csSup hS_bdd hr₀_mem)
  have hR_le : R ≤ L / 2 := csSup_le hS_ne fun r hr => hr.1.2.le
  have hR_lt_holds : ∀ r' ∈ Set.Ico 0 R, ∀ s : ℝ,
      f ![circleMap hs.1 s, circleMap hs.1 (s + σ * r')] = circleMap hs.1 s := by
    intro r' hr' s
    obtain ⟨r₁, hr₁, hlt⟩ := exists_lt_of_lt_csSup hS_ne hr'.2
    exact hr₁.2 r' ⟨hr'.1, hlt.le⟩ s
  have hR_holds : ∀ s : ℝ,
      f ![circleMap hs.1 s, circleMap hs.1 (s + σ * R)] = circleMap hs.1 s := by
    intro s
    refine eq_of_forall_dist_le fun ε hε => ?_
    let δ := min (ε / 2) (R / 2)
    have hδ : 0 < δ := by positivity
    obtain ⟨r₁, hr₁, hlt⟩ := exists_lt_of_lt_csSup hS_ne (by linarith : R - δ < R)
    let a := circleMap hs.1 s
    let a' := circleMap hs.1 (s + σ * (R - r₁))
    let b := circleMap hs.1 (s + σ * R)
    have hr₁_le : r₁ ≤ R := le_csSup hS_bdd hr₁
    have hfa' : f ![a', b] = a' := by
      have heq : (s + σ * (R - r₁)) + σ * r₁ = s + σ * R := by ring
      dsimp only [b]
      rw [← heq]
      exact hr₁.2 r₁ ⟨hr₁.1.1, le_rfl⟩ (s + σ * (R - r₁))
    have hsp_a := hsp ![a, b] 0 a'
    rw [show Function.update ![a, b] 0 a' = ![a', b] by ext i; fin_cases i <;> rfl, hfa'] at hsp_a
    simp only [Matrix.cons_val_zero] at hsp_a
    have hdaa' : dist a a' = R - r₁ := by
      refine (circleMap_dist_eq_of_le hs ?_).trans ?_
      · rw [sub_add_cancel_left, abs_neg, abs_mul, hσ_abs, one_mul,
          abs_of_nonneg (sub_nonneg.mpr hr₁_le)]
        linarith [hr₁.1.1]
      · rw [sub_add_cancel_left, abs_neg, abs_mul, hσ_abs, one_mul,
          abs_of_nonneg (sub_nonneg.mpr hr₁_le)]
    have hδ_le : R - r₁ ≤ ε / 2 := by linarith [min_le_left (ε / 2) (R / 2)]
    rw [_root_.dist_comm]
    exact hsp_a.trans (hdaa'.le.trans (hδ_le.trans (by linarith)))
  have hR_Icc : ∀ r' ∈ Set.Icc 0 R, ∀ s : ℝ,
      f ![circleMap hs.1 s, circleMap hs.1 (s + σ * r')] = circleMap hs.1 s := by
    intro r' hr' s
    rcases eq_or_lt_of_le hr'.2 with rfl | hlt
    · exact hR_holds s
    · exact hR_lt_holds r' ⟨hr'.1, hlt⟩ s
  by_contra hlt_all
  have hR_lt : R < L / 2 := by
    rcases lt_or_eq_of_le hR_le with h | hR_eq
    · exact h
    · exfalso
      apply hlt_all
      intro u r hr0 hrL
      exact hR_lt_holds r ⟨hr0, hR_eq ▸ hrL⟩ u
  obtain ⟨wmin, hwmin_pos, hwmin⟩ := exists_min_dart_weight (c.firstDart hs.1.not_nil)
  obtain ⟨vmin, hvmin_pos, hvmin⟩ := exists_min_vertex_dist_pos W
  let η := min (R / 4) (min (δ₀ / 4) (min (wmin / 8) (min (vmin / 8) ((L / 2 - R) / 8))))
  have hη_pos : 0 < η := by positivity
  have hη1 : η ≤ min (δ₀ / 4) (min (wmin / 8) (min (vmin / 8) ((L / 2 - R) / 8))) :=
    min_le_right _ _
  have hη2 : η ≤ min (wmin / 8) (min (vmin / 8) ((L / 2 - R) / 8)) :=
    hη1.trans (min_le_right _ _)
  have hη3 : η ≤ min (vmin / 8) ((L / 2 - R) / 8) := hη2.trans (min_le_right _ _)
  have hη_R : η ≤ R / 4 := min_le_left _ _
  have hη_δ₀ : η ≤ δ₀ / 4 := hη1.trans (min_le_left _ _)
  have hη_w : 8 * η ≤ wmin := by linarith [hη2.trans (min_le_left _ _)]
  have hη_v : 8 * η ≤ vmin := by linarith [hη3.trans (min_le_left _ _)]
  have hη_L : 8 * η ≤ L / 2 - R := by linarith [hη3.trans (min_le_right _ _)]
  have hstep_η_core : ∀ η' ∈ Set.Icc 0 η, ∀ s : ℝ,
      (∃ v : V, circleMap hs.1 s = vertex v) ∨
        (∀ s_v : ℝ, ∀ v : V, circleMap hs.1 s_v = vertex v →
          ∀ r' ∈ Set.Icc 0 η, f ![circleMap hs.1 s_v, circleMap hs.1 (s_v + σ * (R + r'))] =
            circleMap hs.1 s_v) →
      f ![circleMap hs.1 s, circleMap hs.1 (s + σ * (R + η'))] = circleMap hs.1 s := by
    intro η' hη' s hcase_mode
    let r := R + η'
    have hr_lt : r < L / 2 := by dsimp only [r]; linarith [hη'.2]
    let a := circleMap hs.1 s
    let b := circleMap hs.1 (s + σ * r)
    let b₀ := circleMap hs.1 (s + σ * R)
    let a₁ := circleMap hs.1 (s + σ * η')
    let y := f ![a, b]
    have hfa1 : f ![a₁, b] = a₁ := by
      have heq : (s + σ * η') + σ * R = s + σ * r := by dsimp only [r]; ring
      dsimp only [b]
      rw [← heq]
      exact hR_holds (s + σ * η')
    have hfb₀ : f ![a, b₀] = a := hR_holds s
    have hdaa1 : dist a a₁ = η' := by
      refine (circleMap_dist_eq_of_le hs ?_).trans ?_
      · rw [sub_add_cancel_left, abs_neg, abs_mul, hσ_abs, one_mul, abs_of_nonneg hη'.1]
        linarith [hη'.2]
      · rw [sub_add_cancel_left, abs_neg, abs_mul, hσ_abs, one_mul, abs_of_nonneg hη'.1]
    have hday_le : dist a y ≤ η' := by
      have h := hsp ![a, b] 0 a₁
      rw [show Function.update ![a, b] 0 a₁ = ![a₁, b] by ext i; fin_cases i <;> rfl, hfa1] at h
      simp only [Matrix.cons_val_zero] at h
      exact h.trans hdaa1.le
    have hdab : dist a b = r := by
      refine (circleMap_dist_eq_of_le hs ?_).trans ?_
      · rw [sub_add_cancel_left, abs_neg, abs_mul, hσ_abs, one_mul,
          abs_of_nonneg (by dsimp only [r]; linarith [hη'.1])]
        linarith
      · rw [sub_add_cancel_left, abs_neg, abs_mul, hσ_abs, one_mul,
          abs_of_nonneg (by dsimp only [r]; linarith [hη'.1])]
    have hdby_le : dist b y ≤ r := by
      have h := hsp ![a, b] 1 a
      rw [show Function.update ![a, b] 1 a = ![a, a] by ext i; fin_cases i <;> rfl,
        show ![a, a] = fun _ => a by ext i; fin_cases i <;> rfl, hf_unam a ⟨s, rfl⟩] at h
      have hb_le : dist b (f ![a, b]) ≤ dist b a := h
      rw [_root_.dist_comm b a] at hb_le
      exact hb_le.trans hdab.le
    have hdb0a : dist b₀ a = R := by
      rw [_root_.dist_comm]
      refine (circleMap_dist_eq_of_le hs ?_).trans ?_
      · rw [sub_add_cancel_left, abs_neg, abs_mul, hσ_abs, one_mul, abs_of_nonneg hR_pos.le]
        dsimp only [L] at hR_le
        exact hR_le
      · rw [sub_add_cancel_left, abs_neg, abs_mul, hσ_abs, one_mul, abs_of_nonneg hR_pos.le]
    have hdb0y_ge : R ≤ dist b₀ y := by
      have h := hsp ![a, b₀] 1 b
      rw [show Function.update ![a, b₀] 1 b = ![a, b] by ext i; fin_cases i <;> rfl, hfb₀] at h
      simp only [Matrix.cons_val_one] at h
      exact hdb0a.symm.trans_le h
    have kill_circle_shift : ∀ (y₀ : MetricGraph W),
        dist b y₀ ≤ r → R ≤ dist b₀ y₀ →
        ∀ {ρ : ℝ}, |ρ| ≤ 2 * η → y₀ = circleMap hs.1 (s + ρ) → y₀ = a := by
      intro y₀ hdby₀ hdb0y₀ ρ hρ hy_cm
      rcases lt_trichotomy (σ * ρ) 0 with hneg | hzero | hpos
      · exfalso
        have hby_eq : dist b y₀ = r + |ρ| := by
          rw [hy_cm]
          have hsub : (s + σ * r) - (s + ρ) = σ * (r - σ * ρ) := by
            calc (s + σ * r) - (s + ρ) = σ * r - ρ := by ring
              _ = σ * r - (σ * σ) * ρ := by rw [hσ_sq, one_mul]
              _ = σ * (r - σ * ρ) := by ring
          have hpos_val : 0 < r - σ * ρ := by dsimp only [r]; linarith [hη'.1]
          have hle_L : |(s + σ * r) - (s + ρ)| ≤ walkLength W.weight c / 2 := by
            rw [hsub, abs_mul, hσ_abs, one_mul, abs_of_pos hpos_val]
            have h1 : |σ * ρ| ≤ 2 * η := by rw [abs_mul, hσ_abs, one_mul]; exact hρ
            dsimp only [r, L] at hη_L ⊢
            linarith [(abs_le.mp h1).1, hη'.2]
          rw [circleMap_dist_eq_of_le hs hle_L, hsub, abs_mul, hσ_abs, one_mul,
            abs_of_pos hpos_val]
          have h_abs_eq : |ρ| = -(σ * ρ) := by
            have := abs_of_neg hneg
            rw [abs_mul, hσ_abs, one_mul] at this
            exact this
          linarith
        have hgt0 : 0 < |ρ| := abs_pos.mpr fun h0 => by rw [h0, mul_zero] at hneg; linarith
        linarith
      · have : ρ = 0 := by
          have := congrArg (σ * ·) hzero
          rw [← mul_assoc, hσ_sq, one_mul, mul_zero] at this
          exact this
        rw [this, add_zero] at hy_cm
        exact hy_cm
      · exfalso
        have hb0y_eq : dist b₀ y₀ = R - |ρ| := by
          rw [hy_cm]
          have hsub : (s + σ * R) - (s + ρ) = σ * (R - σ * ρ) := by
            calc (s + σ * R) - (s + ρ) = σ * R - ρ := by ring
              _ = σ * R - (σ * σ) * ρ := by rw [hσ_sq, one_mul]
              _ = σ * (R - σ * ρ) := by ring
          have h1 : |σ * ρ| ≤ 2 * η := by rw [abs_mul, hσ_abs, one_mul]; exact hρ
          have hpos_val : 0 < R - σ * ρ := by linarith [(abs_le.mp h1).2]
          have hle_L : |(s + σ * R) - (s + ρ)| ≤ walkLength W.weight c / 2 := by
            rw [hsub, abs_mul, hσ_abs, one_mul, abs_of_pos hpos_val]
            dsimp only [L] at hR_le
            linarith
          rw [circleMap_dist_eq_of_le hs hle_L, hsub, abs_mul, hσ_abs, one_mul,
            abs_of_pos hpos_val]
          have h_abs_eq : |ρ| = σ * ρ := by
            have := abs_of_pos hpos
            rw [abs_mul, hσ_abs, one_mul] at this
            exact this
          linarith
        have hgt0 : 0 < |ρ| := abs_pos.mpr fun h0 => by rw [h0, mul_zero] at hpos; linarith
        linarith
    rcases circleMap_local_dichotomy hs.1 s with
      ⟨d, t, δ₁, hd_mem, ht0, ht1, hδ₁, hmap⟩ |
      ⟨v, d₁, d₂, δ₁, hv_sup, hd₁_fst, hd₂_fst, hd₁₂, hd₁_mem, hd₂_mem, hs_v, hδ₁, hmap⟩
    · have hvert : ∀ s_v : ℝ, ∀ v : V, circleMap hs.1 s_v = vertex v →
          ∀ r' ∈ Set.Icc 0 η, f ![circleMap hs.1 s_v, circleMap hs.1 (s_v + σ * (R + r'))] =
            circleMap hs.1 s_v := by
        rcases hcase_mode with ⟨v', hv'⟩ | hv_all
        · exfalso
          obtain ⟨_, _, _, _, hcm0⟩ := hmap 0 ⟨by linarith, hδ₁.le⟩
          simp only [add_zero, zero_div] at hcm0
          have heq : edgePoint d ⟨t, ht0.le, ht1.le⟩ = vertex v' := hcm0.symm.trans hv'
          rw [edgePoint_eq_vertex_iff] at heq
          rcases heq with ⟨h, _⟩ | ⟨h, _⟩
          · have : t = 0 := congrArg Subtype.val h; linarith
          · have : t = 1 := congrArg Subtype.val h; linarith
        · exact hv_all
      have hw := W.dart_weight_pos d
      have hfull := edge_param_full W hs.1 ht0 ht1 hδ₁ (fun r' hr' => by
        obtain ⟨_, _, h0, h1, hcm⟩ := hmap r' hr'; exact ⟨h0, h1, hcm⟩)
      have hend := edge_param_endpoints W hs.1 ht0 ht1 hδ₁ (fun r' hr' => by
        obtain ⟨_, _, h0, h1, hcm⟩ := hmap r' hr'; exact ⟨h0, h1, hcm⟩)
      obtain ⟨_, _, h0t, h1t, hcm0⟩ := hmap 0 ⟨by linarith, hδ₁.le⟩
      have hcm0' : a = edgePoint d ⟨t, by simpa only [zero_div, add_zero] using h0t,
          by simpa only [zero_div, add_zero] using h1t⟩ := by
        simpa only [add_zero, zero_div] using hcm0
      have ha_ep : a = edgePoint d ⟨t, ht0.le, ht1.le⟩ := hcm0'
      have hy_orig : f ![a, b] = y := rfl
      change y = a
      have hday_η : dist a y ≤ η' := hday_le
      have hdby_η : dist b y ≤ r := hdby_le
      have hdb0y_η : R ≤ dist b₀ y := hdb0y_ge
      revert hy_orig hday_η hdby_η hdb0y_η
      induction y using MetricGraph.ind with
      | vertex u =>
        intro _ hdu hdby_v hdb0y_v
        rw [ha_ep, _root_.dist_comm, dist_vertex_edgePoint] at hdu
        dsimp only at hdu
        have hu_end : u = d.fst ∨ u = d.snd := by
          by_contra hne
          push Not at hne
          have h1 : vmin ≤ W.graph.vertexDist W.weight u d.fst := by
            rw [← dist_vertex]; exact hvmin u d.fst hne.1
          have h2 : vmin ≤ W.graph.vertexDist W.weight u d.snd := by
            rw [← dist_vertex]; exact hvmin u d.snd hne.2
          have := mul_nonneg ht0.le hw.le
          have := mul_nonneg (sub_nonneg.mpr ht1.le) hw.le
          rcases le_total (W.graph.vertexDist W.weight u d.fst + t * W.weight d.edge)
              (W.graph.vertexDist W.weight u d.snd + (1 - t) * W.weight d.edge) with hm | hm
          · rw [min_eq_left hm] at hdu; linarith [hη'.2]
          · rw [min_eq_right hm] at hdu; linarith [hη'.2]
        rcases hu_end with rfl | rfl
        · have hv1 : vmin ≤ W.graph.vertexDist W.weight d.fst d.snd := by
            rw [← dist_vertex]; exact hvmin d.fst d.snd d.adj.ne
          rw [vertexDist_self W.weight_nonneg, zero_add] at hdu
          rcases le_total (t * W.weight d.edge)
              (W.graph.vertexDist W.weight d.fst d.snd + (1 - t) * W.weight d.edge) with hm | hm
          · rw [min_eq_left hm] at hdu
            have hcm_end := hend.1
            have hy_cm : vertex d.fst = circleMap hs.1 (s + (-(t * W.weight d.edge))) := by
              rw [← hcm_end]; ring_nf
            exact kill_circle_shift (vertex d.fst) hdby_v hdb0y_v (ρ := -(t * W.weight d.edge))
              (by rw [abs_neg, abs_of_pos (mul_pos ht0 hw)]; linarith [hη'.2, hη_pos.le, hdu])
              hy_cm
          · rw [min_eq_right hm] at hdu
            exfalso
            have := mul_nonneg (sub_nonneg.mpr ht1.le) hw.le
            linarith [hη'.2]
        · have hv1 : vmin ≤ W.graph.vertexDist W.weight d.snd d.fst := by
            rw [← dist_vertex]; exact hvmin d.snd d.fst d.adj.ne.symm
          rw [vertexDist_self W.weight_nonneg, zero_add] at hdu
          rcases le_total (W.graph.vertexDist W.weight d.snd d.fst + t * W.weight d.edge)
              ((1 - t) * W.weight d.edge) with hm | hm
          · rw [min_eq_left hm] at hdu
            exfalso
            have := mul_nonneg ht0.le hw.le
            linarith [hη'.2]
          · rw [min_eq_right hm] at hdu
            have hcm_end := hend.2
            have hy_cm : vertex d.snd = circleMap hs.1 (s + (1 - t) * W.weight d.edge) :=
              hcm_end.symm
            exact kill_circle_shift (vertex d.snd) hdby_v hdb0y_v (ρ := (1 - t) * W.weight d.edge)
              (by
                rw [abs_of_pos (mul_pos (sub_pos.mpr ht1) hw)]
                linarith [hη'.2, hη_pos.le, hdu])
              hy_cm
      | edgePoint d' t' ht'0 ht'1 =>
        intro hy_orig hdu hdby_ep hdb0y_ep
        by_cases hde : d'.edge = d.edge
        · have hswap : ∃ u' : unitInterval, 0 < (u' : ℝ) ∧ (u' : ℝ) < 1 ∧
              edgePoint d' t' = edgePoint d u' := by
            rcases (dart_edge_eq_iff d' d).mp hde with rfl | rfl
            · exact ⟨t', ht'0, ht'1, rfl⟩
            · exact ⟨unitInterval.symm t', sub_pos.mpr ht'1, sub_lt_self 1 ht'0, by
                simpa only [unitInterval.symm_symm] using edgePoint_symm d (unitInterval.symm t')⟩
          obtain ⟨u', hu'0, hu'1, hu'_eq⟩ := hswap
          let ρ := ((u' : ℝ) - t) * W.weight d.edge
          have heq_cm : edgePoint d' t' = circleMap hs.1 (s + ρ) := by
            rw [hu'_eq]
            exact (hfull (u' : ℝ) hu'0 hu'1).symm
          have hd_cd : dist a (edgePoint d' t') = circleDist L s (s + ρ) := by
            rw [heq_cm]
            exact circleMap_dist_eq_circleDist hs s (s + ρ)
          have hρ_lt : |ρ| < L := by
            have hdL : W.weight d.edge ≤ L := by
              dsimp only [L, walkLength]
              refine List.single_le_sum (fun x hx => ?_) _
                (List.mem_map.mpr ⟨d.edge, List.mem_map.mpr ⟨d, hd_mem, rfl⟩, rfl⟩)
              obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
              obtain ⟨d₀, _, rfl⟩ := List.mem_map.mp he
              exact W.weight_nonneg d₀.adj
            have habsu : |(u' : ℝ) - t| < 1 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
            dsimp only [ρ]
            rw [abs_mul, abs_of_pos hw]
            calc |(u' : ℝ) - t| * W.weight d.edge < 1 * W.weight d.edge :=
                  mul_lt_mul_of_pos_right habsu hw
              _ = W.weight d.edge := one_mul _
              _ ≤ L := hdL
          obtain ⟨k, hk⟩ := exists_eq_add_int_mul_dist hL s (s + ρ)
          have hρk : |ρ + (k : ℝ) * L| ≤ η' := by
            have hk_eq : |s - (s + ρ + (k : ℝ) * L)| = |ρ + (k : ℝ) * L| := by
              rw [show s - (s + ρ + (k : ℝ) * L) = -(ρ + (k : ℝ) * L) by ring, abs_neg]
            rw [← hk_eq, hk, ← hd_cd]
            exact hdu
          have hcm_k : edgePoint d' t' = circleMap hs.1 (s + (ρ + (k : ℝ) * L)) := by
            rw [heq_cm, show s + (ρ + (k : ℝ) * L) = (s + ρ) + (k : ℝ) * L by ring,
              circleMap_add_int_mul hs.1]
          exact kill_circle_shift (edgePoint d' t') hdby_ep hdb0y_ep (ρ := ρ + (k : ℝ) * L)
            (by linarith [hρk, hη'.2, hη_pos.le]) hcm_k
        · exfalso
          have hdist_diff : dist (edgePoint d ⟨t, ht0.le, ht1.le⟩) (edgePoint d' t') ≤ η' :=
            ha_ep ▸ hdu
          rw [dist_edgePoint_edgePoint_of_edge_ne (Ne.symm hde)] at hdist_diff
          have hwe1 : W.weight d.edge ≥ wmin := hwmin d
          have hwe2 : W.weight d'.edge ≥ wmin := hwmin d'
          have off_at : f ![a, b] = edgePoint d' t' →
              ∀ (v : V) (off_a : ℝ) (s_v : ℝ),
              (v = d.fst ∧ off_a = t * W.weight d.edge ∧ s_v = s - off_a) ∨
              (v = d.snd ∧ off_a = (1 - t) * W.weight d.edge ∧ s_v = s + off_a) →
              ∀ (d'' : W.graph.Dart) (t'' : unitInterval),
                d''.fst = v → d''.edge = d'.edge → 0 < (t'' : ℝ) → (t'' : ℝ) < 1 →
                edgePoint d'' t'' = edgePoint d' t' →
                off_a + (t'' : ℝ) * W.weight d''.edge ≤ η' → False := by
            intro hy_pt v off_a s_v hvs d'' t'' hd''_fst hd''_ed ht''0 ht''1 hd''_eq hoff_sum
            have hv_cm : circleMap hs.1 s_v = vertex v := by
              rcases hvs with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
              · exact hend.1
              · exact hend.2
            have hv_pos : 0 < off_a := by
              rcases hvs with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩
              · exact mul_pos ht0 hw
              · exact mul_pos (sub_pos.mpr ht1) hw
            have hv_sup : v ∈ c.support := by
              have hed : d.edge ∈ c.edges := List.mem_map.mpr ⟨d, hd_mem, rfl⟩
              rcases hvs with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩
              · exact Walk.fst_mem_support_of_mem_edges c hed
              · exact Walk.snd_mem_support_of_mem_edges c hed
            let r_y := (t'' : ℝ) * W.weight d''.edge
            have hry_pos : 0 < r_y := mul_pos ht''0 (W.dart_weight_pos d'')
            have hsv_diff : s_v = s + off_a ∨ s_v = s - off_a := by
              rcases hvs with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
              · right; rfl
              · left; rfl
            have hs_v_case : s_v - s = σ * off_a ∨ s_v - s = -(σ * off_a) := by
              rcases hσ with rfl | rfl <;> rcases hsv_diff with h | h <;> rw [h]
              · left; ring
              · right; ring
              · right; ring
              · left; ring
            rcases hs_v_case with hdir | hdir
            · have hs_v_eq : s + σ * off_a = s_v := by linarith
              have hb_eq : b = circleMap hs.1 (s_v + σ * (r - off_a)) := by
                dsimp only [b]
                congr 1
                rw [← hs_v_eq]
                ring
              have hr_off_ge : 0 ≤ r - off_a := by dsimp only [r]; linarith [hη'.1, hη'.2]
              have hfb_v : f ![vertex v, b] = vertex v := by
                rw [← hv_cm, hb_eq]
                rcases le_or_gt (r - off_a) R with hle | hgt
                · exact hR_Icc (r - off_a) ⟨hr_off_ge, hle⟩ s_v
                · have hsub_mem : r - off_a - R ∈ Set.Icc 0 η := by
                    dsimp only [r] at hgt ⊢
                    exact ⟨by linarith, by linarith [hη'.2]⟩
                  have := hvert s_v v hv_cm (r - off_a - R) hsub_mem
                  rw [show R + (r - off_a - R) = r - off_a by ring] at this
                  exact this
              have hsp_v := hsp ![a, b] 0 (vertex v)
              have hupd_v : Function.update ![a, b] 0 (vertex v) = ![vertex v, b] := by
                ext i; fin_cases i <;> rfl
              rw [hupd_v, hfb_v] at hsp_v
              simp only [Matrix.cons_val_zero] at hsp_v
              have hda_v : dist a (vertex v : MetricGraph W) = off_a := by
                rw [← hv_cm]
                refine (circleMap_dist_eq_of_le hs ?_).trans ?_
                · rw [show s - s_v = -(σ * off_a) by linarith, abs_neg, abs_mul, hσ_abs, one_mul,
                    abs_of_pos hv_pos]
                  linarith [hη'.2]
                · rw [show s - s_v = -(σ * off_a) by linarith, abs_neg, abs_mul, hσ_abs, one_mul,
                    abs_of_pos hv_pos]
              have hda_y_eq : dist a (edgePoint d'' t'') = off_a + r_y := by
                have hdn : d.edge ≠ d''.edge := fun h => hde (hd''_ed ▸ h.symm)
                have hdt0 : 0 ≤ off_a / W.weight d.edge := div_nonneg hv_pos.le hw.le
                have hdt1 : off_a / W.weight d.edge ≤ 1 := by
                  rw [div_le_one hw]; linarith [hη'.2, hwmin d]
                have htt0 : 0 ≤ r_y / W.weight d''.edge :=
                  div_nonneg hry_pos.le (W.dart_weight_pos d'').le
                have htt1 : r_y / W.weight d''.edge ≤ 1 := by
                  rw [div_le_one (W.dart_weight_pos d'')]; linarith [hη'.2, hwmin d'']
                rw [ha_ep, dist_edgePoint_edgePoint_of_edge_ne hdn]
                rcases hvs with ⟨hv_d, hoff_d, _⟩ | ⟨hv_d, hoff_d, _⟩
                · subst hv_d
                  have h12 : t * W.weight d.edge + W.graph.vertexDist W.weight d.fst d''.snd +
                      (1 - (t'' : ℝ)) * W.weight d''.edge ≥ off_a + r_y := by
                    have hv_s : vmin ≤ W.graph.vertexDist W.weight d.fst d''.snd := by
                      rw [← dist_vertex]; exact hvmin d.fst d''.snd (hd''_fst ▸ d''.adj.ne)
                    have := mul_nonneg (sub_nonneg.mpr ht''1.le) (W.dart_weight_pos d'').le
                    linarith [hη'.2]
                  have h34 : (1 - t) * W.weight d.edge + W.graph.vertexDist W.weight d.snd d''.fst +
                      (t'' : ℝ) * W.weight d''.edge ≥ off_a + r_y := by
                    have hv_s : vmin ≤ W.graph.vertexDist W.weight d.snd d''.fst := by
                      rw [← dist_vertex]; exact hvmin d.snd d''.fst (hd''_fst ▸ d.adj.ne.symm)
                    have := mul_nonneg (sub_nonneg.mpr ht1.le) hw.le
                    linarith [hη'.2]
                  have h34b : (1 - t) * W.weight d.edge +
                      W.graph.vertexDist W.weight d.snd d''.snd +
                      (1 - (t'' : ℝ)) * W.weight d''.edge ≥ off_a + r_y := by
                    have hnn : 0 ≤ W.graph.vertexDist W.weight d.snd d''.snd := by
                      rw [← dist_vertex]; exact dist_nonneg
                    have h1w : (1 - t) * W.weight d.edge ≥ W.weight d.edge - off_a := by linarith
                    have h2w : (1 - (t'' : ℝ)) * W.weight d''.edge = W.weight d''.edge - r_y := by
                      dsimp only [r_y]; ring
                    linarith [hη'.2, hwmin d, hwmin d'']
                  rw [hd''_fst, vertexDist_self W.weight_nonneg, add_zero]
                  rw [hd''_fst] at h34
                  dsimp only
                  have he1 : t * W.weight d.edge + (t'' : ℝ) * W.weight d''.edge = off_a + r_y := by
                    dsimp only [r_y]; rw [hoff_d]
                  have hAB : min (t * W.weight d.edge + (t'' : ℝ) * W.weight d''.edge)
                      (t * W.weight d.edge + W.graph.vertexDist W.weight d.fst d''.snd +
                        (1 - (t'' : ℝ)) * W.weight d''.edge) =
                      t * W.weight d.edge + (t'' : ℝ) * W.weight d''.edge :=
                    min_eq_left (by linarith)
                  have hAC : t * W.weight d.edge + (t'' : ℝ) * W.weight d''.edge ≤
                      (1 - t) * W.weight d.edge + W.graph.vertexDist W.weight d.snd d.fst +
                        (t'' : ℝ) * W.weight d''.edge :=
                    he1.trans_le h34
                  have hAD : t * W.weight d.edge + (t'' : ℝ) * W.weight d''.edge ≤
                      (1 - t) * W.weight d.edge + W.graph.vertexDist W.weight d.snd d''.snd +
                        (1 - (t'' : ℝ)) * W.weight d''.edge :=
                    he1.trans_le h34b
                  rw [hAB, min_eq_left (le_min hAC hAD), he1]
                · subst hv_d
                  have h12 : t * W.weight d.edge + W.graph.vertexDist W.weight d.fst d''.fst +
                      (t'' : ℝ) * W.weight d''.edge ≥ off_a + r_y := by
                    have hv_s : vmin ≤ W.graph.vertexDist W.weight d.fst d''.fst := by
                      rw [← dist_vertex]; exact hvmin d.fst d''.fst (hd''_fst ▸ d.adj.ne)
                    have := mul_nonneg ht0.le hw.le
                    linarith [hη'.2]
                  have h12b : t * W.weight d.edge + W.graph.vertexDist W.weight d.fst d''.snd +
                      (1 - (t'' : ℝ)) * W.weight d''.edge ≥ off_a + r_y := by
                    have hnn : 0 ≤ W.graph.vertexDist W.weight d.fst d''.snd := by
                      rw [← dist_vertex]; exact dist_nonneg
                    have h1w : t * W.weight d.edge = W.weight d.edge - off_a := by linarith
                    have h2w : (1 - (t'' : ℝ)) * W.weight d''.edge = W.weight d''.edge - r_y := by
                      dsimp only [r_y]; ring
                    linarith [hη'.2, hwmin d, hwmin d'']
                  have h34 : (1 - t) * W.weight d.edge + W.graph.vertexDist W.weight d.snd d''.snd +
                      (1 - (t'' : ℝ)) * W.weight d''.edge ≥ off_a + r_y := by
                    have hv_s : vmin ≤ W.graph.vertexDist W.weight d.snd d''.snd := by
                      rw [← dist_vertex]; exact hvmin d.snd d''.snd (hd''_fst ▸ d''.adj.ne)
                    have := mul_nonneg (sub_nonneg.mpr ht''1.le) (W.dart_weight_pos d'').le
                    linarith [hη'.2]
                  rw [hd''_fst, vertexDist_self W.weight_nonneg, add_zero]
                  rw [hd''_fst] at h12
                  dsimp only
                  have he2 : (1 - t) * W.weight d.edge + (t'' : ℝ) * W.weight d''.edge =
                      off_a + r_y := by
                    dsimp only [r_y]; rw [hoff_d]
                  have hCD : min ((1 - t) * W.weight d.edge + (t'' : ℝ) * W.weight d''.edge)
                      ((1 - t) * W.weight d.edge + W.graph.vertexDist W.weight d.snd d''.snd +
                        (1 - (t'' : ℝ)) * W.weight d''.edge) =
                      (1 - t) * W.weight d.edge + (t'' : ℝ) * W.weight d''.edge :=
                    min_eq_left (by linarith)
                  have hCA : (1 - t) * W.weight d.edge + (t'' : ℝ) * W.weight d''.edge ≤
                      t * W.weight d.edge + W.graph.vertexDist W.weight d.fst d.snd +
                        (t'' : ℝ) * W.weight d''.edge :=
                    he2.trans_le h12
                  have hCB : (1 - t) * W.weight d.edge + (t'' : ℝ) * W.weight d''.edge ≤
                      t * W.weight d.edge + W.graph.vertexDist W.weight d.fst d''.snd +
                        (1 - (t'' : ℝ)) * W.weight d''.edge :=
                    he2.trans_le h12b
                  rw [hCD, min_eq_right (le_min hCA hCB), he2]
              rw [hy_pt, ← hd''_eq] at hsp_v
              linarith
            · have hs_eq : s = s_v + σ * off_a := by linarith
              have hb_eq : b = circleMap hs.1 (s_v + σ * (off_a + r)) := by
                dsimp only [b]; rw [hs_eq]; congr 1; ring
              have hr_sum_lt : off_a + r < L / 2 := by dsimp only [r]; linarith [hη'.2]
              have hbv_eq : dist (vertex v : MetricGraph W) b = off_a + r := by
                rw [← hv_cm, hb_eq]
                refine (circleMap_dist_eq_of_le hs ?_).trans ?_
                · rw [sub_add_cancel_left, abs_neg, abs_mul, hσ_abs, one_mul,
                    abs_of_pos (by dsimp only [r]; linarith [hη'.1])]
                  linarith
                · rw [sub_add_cancel_left, abs_neg, abs_mul, hσ_abs, one_mul,
                    abs_of_pos (by dsimp only [r]; linarith [hη'.1])]
              rcases circleMap_local_dichotomy hs.1 s_v with
                ⟨d_x, t_x, _, _, ht_x0, ht_x1, hδ_x, hmap_x⟩ |
                ⟨v', d₁', d₂', δ₁', hv'_sup, hd₁'_fst, hd₂'_fst, hd₁₂', hd₁'_mem, hd₂'_mem,
                  hs_v', hδ₁', hmap_x⟩
              · exfalso
                obtain ⟨_, _, _, _, hcm_x⟩ := hmap_x 0 ⟨by linarith, hδ_x.le⟩
                simp only [add_zero, zero_div] at hcm_x
                have heq := hcm_x.symm.trans hv_cm
                rw [edgePoint_eq_vertex_iff] at heq
                rcases heq with ⟨h, _⟩ | ⟨h, _⟩
                · have : t_x = 0 := congrArg Subtype.val h; linarith
                · have : t_x = 1 := congrArg Subtype.val h; linarith
              · have hv_eq : v' = v := vertex_inj.mp (hs_v'.symm.trans hv_cm)
                have hv'_eq : (vertex v' : MetricGraph W) = vertex v := hs_v'.symm.trans hv_cm
                have hfull_v' := vertex_param_full W hs.1 hd₁'_fst hd₂'_fst hs_v' δ₁' hδ₁' hmap_x
                by_cases h1 : d''.edge = d₁'.edge
                · have hd''_eq_d1 : d'' = d₁' :=
                    ((dart_edge_eq_iff d'' d₁').mp h1).resolve_right fun hsym => by
                      have : d₁'.fst = d₁'.snd := by
                        rw [hd₁'_fst, hv_eq, ← hd''_fst, hsym]; rfl
                      exact d₁'.adj.ne this
                  have hy_cm : edgePoint d' t' = circleMap hs.1 (s_v - r_y) := by
                    have hcm1 := hfull_v'.1 r_y hry_pos (by linarith [hη'.2, hwmin d₁'])
                    rw [← hd''_eq_d1] at hcm1
                    rw [← hd''_eq, hcm1]
                    congr 1; ext; simp [r_y, mul_div_cancel_right₀ _ (W.dart_weight_pos d'').ne']
                  have hσ_eq : σ = 1 := by
                    rcases hσ with rfl | rfl
                    · rfl
                    · exfalso
                      have ha1 := hfull_v'.1 off_a hv_pos (by linarith [hη'.2, hwmin d₁'])
                      rw [show s_v - off_a = s by rw [hs_eq]; ring] at ha1
                      change a = _ at ha1
                      rw [ha_ep, edgePoint_eq_edgePoint_iff] at ha1
                      have hd_d1 : d.edge = d₁'.edge := by
                        rcases ha1 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, _, h⟩
                        · have : t = 0 := congrArg Subtype.val h; linarith
                        · have : t = 1 := congrArg Subtype.val h; linarith
                        · rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
                      exact hde (hd''_ed.symm.trans (h1.trans hd_d1.symm))
                  have hkill := kill_circle_shift (edgePoint d' t') hdby_ep hdb0y_ep
                    (ρ := -(off_a + r_y))
                    (by rw [abs_neg, abs_of_pos (by linarith)]; linarith [hη'.2])
                    (by rw [hy_cm, hs_eq, hσ_eq]; ring_nf)
                  have hd_zero : a = edgePoint d'' t'' := hkill.symm.trans hd''_eq.symm
                  rw [ha_ep, edgePoint_eq_edgePoint_iff] at hd_zero
                  rcases hd_zero with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, _, h⟩
                  · have : t = 0 := congrArg Subtype.val h; linarith
                  · have : t = 1 := congrArg Subtype.val h; linarith
                  · rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
                    · exact hde hd''_ed.symm
                    · exact hde (by simpa [Dart.edge_symm] using hd''_ed.symm)
                · by_cases h2 : d''.edge = d₂'.edge
                  · have hd''_eq_d2 : d'' = d₂' :=
                      ((dart_edge_eq_iff d'' d₂').mp h2).resolve_right fun hsym => by
                        have : d₂'.fst = d₂'.snd := by
                          rw [hd₂'_fst, hv_eq, ← hd''_fst, hsym]; rfl
                        exact d₂'.adj.ne this
                    have hy_cm : edgePoint d' t' = circleMap hs.1 (s_v + r_y) := by
                      have hcm2 := hfull_v'.2 r_y hry_pos (by linarith [hη'.2, hwmin d₂'])
                      rw [← hd''_eq_d2] at hcm2
                      rw [← hd''_eq, hcm2]
                      congr 1; ext; simp [r_y, mul_div_cancel_right₀ _ (W.dart_weight_pos d'').ne']
                    have hσ_eq : σ = -1 := by
                      rcases hσ with rfl | rfl
                      · exfalso
                        have ha2 := hfull_v'.2 off_a hv_pos (by linarith [hη'.2, hwmin d₂'])
                        rw [show s_v + off_a = s by rw [hs_eq]; ring] at ha2
                        change a = _ at ha2
                        rw [ha_ep, edgePoint_eq_edgePoint_iff] at ha2
                        have hd_d2 : d.edge = d₂'.edge := by
                          rcases ha2 with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, _, h⟩
                          · have : t = 0 := congrArg Subtype.val h; linarith
                          · have : t = 1 := congrArg Subtype.val h; linarith
                          · rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
                        exact hde (hd''_ed.symm.trans (h2.trans hd_d2.symm))
                      · rfl
                    have hkill := kill_circle_shift (edgePoint d' t') hdby_ep hdb0y_ep
                      (ρ := off_a + r_y)
                      (by rw [abs_of_pos (by linarith)]; linarith [hη'.2])
                      (by rw [hy_cm, hs_eq, hσ_eq]; ring_nf)
                    have hd_zero : a = edgePoint d'' t'' := hkill.symm.trans hd''_eq.symm
                    rw [ha_ep, edgePoint_eq_edgePoint_iff] at hd_zero
                    rcases hd_zero with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, _, _, h⟩
                    · have : t = 0 := congrArg Subtype.val h; linarith
                    · have : t = 1 := congrArg Subtype.val h; linarith
                    · rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
                      · exact hde hd''_ed.symm
                      · exact hde (by simpa [Dart.edge_symm] using hd''_ed.symm)
                  · have hd''_not : d''.edge ∉ c.edges :=
                      edge_not_mem_cycle_of_ne hs.1 hv'_sup hd₁'_fst hd₂'_fst hd₁₂'
                        hd₁'_mem hd₂'_mem (hd''_fst.trans hv_eq.symm) h1 h2
                    have hsum_lt : 2 * dist (vertex v' : MetricGraph W) b + r_y < L := by
                      rw [hv'_eq, hbv_eq]; dsimp only [r, L] at hη_L ⊢; linarith [hη'.2]
                    have hgt := dist_third_dart_gt_of_circleMap W hs hv'_sup
                      (hd''_fst.trans hv_eq.symm) hd''_not t'' ht''0
                      (by linarith [hη'.2, hwmin d'']) hsum_lt
                    rw [hv'_eq, hbv_eq, hd''_eq] at hgt
                    dsimp only [b] at hdby_ep
                    linarith
          have htw1 : 0 ≤ t * W.weight d.edge := mul_nonneg ht0.le hw.le
          have htw2 : 0 ≤ (1 - t) * W.weight d.edge := mul_nonneg (sub_nonneg.mpr ht1.le) hw.le
          have htw3 : 0 ≤ (t' : ℝ) * W.weight d'.edge :=
            mul_nonneg ht'0.le (W.dart_weight_pos d').le
          have htw4 : 0 ≤ (1 - (t' : ℝ)) * W.weight d'.edge :=
            mul_nonneg (sub_nonneg.mpr ht'1.le) (W.dart_weight_pos d').le
          rw [min_le_iff, min_le_iff, min_le_iff] at hdist_diff
          rcases hdist_diff with (h | h) | (h | h)
          · have hv_eq : d.fst = d'.fst := by
              by_contra hne
              have hv := hvmin d.fst d'.fst hne
              rw [dist_vertex] at hv
              linarith [hη'.2]
            have h0v : W.graph.vertexDist W.weight d.fst d'.fst = 0 := by
              rw [hv_eq, vertexDist_self W.weight_nonneg]
            rw [h0v, add_zero] at h
            exact off_at hy_orig d.fst (t * W.weight d.edge) (s - t * W.weight d.edge)
              (Or.inl ⟨rfl, rfl, rfl⟩) d' t' hv_eq.symm rfl ht'0 ht'1 rfl h
          · have hv_eq : d.fst = d'.snd := by
              by_contra hne
              have hv := hvmin d.fst d'.snd hne
              rw [dist_vertex] at hv
              linarith [hη'.2]
            have h0v : W.graph.vertexDist W.weight d.fst d'.snd = 0 := by
              rw [hv_eq, vertexDist_self W.weight_nonneg]
            rw [h0v, add_zero] at h
            refine off_at hy_orig d.fst (t * W.weight d.edge) (s - t * W.weight d.edge)
              (Or.inl ⟨rfl, rfl, rfl⟩) d'.symm (unitInterval.symm t') hv_eq.symm (by simp)
              (sub_pos.mpr ht'1) (sub_lt_self 1 ht'0) (edgePoint_symm d' t') ?_
            simpa [unitInterval.coe_symm_eq, Dart.edge_symm] using h
          · have hv_eq : d.snd = d'.fst := by
              by_contra hne
              have hv := hvmin d.snd d'.fst hne
              rw [dist_vertex] at hv
              linarith [hη'.2]
            have h0v : W.graph.vertexDist W.weight d.snd d'.fst = 0 := by
              rw [hv_eq, vertexDist_self W.weight_nonneg]
            rw [h0v, add_zero] at h
            exact off_at hy_orig d.snd ((1 - t) * W.weight d.edge) (s + (1 - t) * W.weight d.edge)
              (Or.inr ⟨rfl, rfl, rfl⟩) d' t' hv_eq.symm rfl ht'0 ht'1 rfl h
          · have hv_eq : d.snd = d'.snd := by
              by_contra hne
              have hv := hvmin d.snd d'.snd hne
              rw [dist_vertex] at hv
              linarith [hη'.2]
            have h0v : W.graph.vertexDist W.weight d.snd d'.snd = 0 := by
              rw [hv_eq, vertexDist_self W.weight_nonneg]
            rw [h0v, add_zero] at h
            refine off_at hy_orig d.snd ((1 - t) * W.weight d.edge) (s + (1 - t) * W.weight d.edge)
              (Or.inr ⟨rfl, rfl, rfl⟩) d'.symm (unitInterval.symm t') hv_eq.symm (by simp)
              (sub_pos.mpr ht'1) (sub_lt_self 1 ht'0) (edgePoint_symm d' t') ?_
            simpa [unitInterval.coe_symm_eq, Dart.edge_symm] using h
    · have hy_close : dist (vertex v : MetricGraph W) y ≤ η := by
        rw [← hs_v]; exact hday_le.trans hη'.2
      have hfull_v := vertex_param_full W hs.1 hd₁_fst hd₂_fst hs_v δ₁ hδ₁ hmap
      change y = a
      have hdby_η : dist b y ≤ r := hdby_le
      have hdb0y_η : R ≤ dist b₀ y := hdb0y_ge
      revert hy_close hdby_η hdb0y_η
      induction y using MetricGraph.ind with
      | vertex u =>
        intro hu _ _
        by_cases huv : u = v
        · dsimp only [a]; rw [huv, hs_v]
        · exfalso; have := hvmin v u (Ne.symm huv); linarith
      | edgePoint d t ht0 ht1 =>
        intro hp hdby_ep hdb0y_ep
        have hev : d.fst = v ∨ d.snd = v := by
          by_contra hnone
          push Not at hnone
          have h1 : vmin ≤ W.graph.vertexDist W.weight v d.fst := by
            rw [← dist_vertex]; exact hvmin v d.fst (Ne.symm hnone.1)
          have h2 : vmin ≤ W.graph.vertexDist W.weight v d.snd := by
            rw [← dist_vertex]; exact hvmin v d.snd (Ne.symm hnone.2)
          rw [dist_vertex_edgePoint] at hp
          rcases le_total (W.graph.vertexDist W.weight v d.fst + (t : ℝ) * W.weight d.edge)
              (W.graph.vertexDist W.weight v d.snd + (1 - (t : ℝ)) * W.weight d.edge) with hm | hm
          · rw [min_eq_left hm] at hp; linarith [mul_nonneg ht0.le (W.dart_weight_pos d).le]
          · rw [min_eq_right hm] at hp
            linarith [mul_nonneg (sub_nonneg.mpr ht1.le) (W.dart_weight_pos d).le]
        have h_at_fst : ∀ {d' : W.graph.Dart} {t' : unitInterval},
            d'.fst = v → 0 < (t' : ℝ) → (t' : ℝ) < 1 →
            dist (vertex v : MetricGraph W) (edgePoint d' t') ≤ η →
            dist b (edgePoint d' t') ≤ r → R ≤ dist b₀ (edgePoint d' t') → False := by
          intro d' t' hd'_fst ht'0 ht'1 hd'p hdby_p hdb0y_p
          rw [dist_vertex_edgePoint, hd'_fst, vertexDist_self W.weight_nonneg, zero_add] at hd'p
          have hv : vmin ≤ W.graph.vertexDist W.weight v d'.snd := by
            rw [← dist_vertex]; exact hvmin v d'.snd (hd'_fst ▸ d'.adj.ne)
          have hge : vmin ≤ W.graph.vertexDist W.weight v d'.snd +
              (1 - (t' : ℝ)) * W.weight d'.edge := by
            linarith [mul_nonneg (sub_nonneg.mpr ht'1.le) (W.dart_weight_pos d').le]
          have hmin_eq : min ((t' : ℝ) * W.weight d'.edge)
              (W.graph.vertexDist W.weight v d'.snd + (1 - (t' : ℝ)) * W.weight d'.edge) =
              (t' : ℝ) * W.weight d'.edge := by
            rcases le_total ((t' : ℝ) * W.weight d'.edge)
                (W.graph.vertexDist W.weight v d'.snd + (1 - (t' : ℝ)) * W.weight d'.edge)
                with hle | hge'
            · exact min_eq_left hle
            · exfalso; rw [min_eq_right hge'] at hd'p; linarith
          rw [hmin_eq] at hd'p
          let r_y := (t' : ℝ) * W.weight d'.edge
          have hry_pos : 0 < r_y := mul_pos ht'0 (W.dart_weight_pos d')
          have hry_le : r_y ≤ η := hd'p
          have hry_wmin : r_y < wmin := by linarith
          by_cases h1 : d'.edge = d₁.edge
          · have hd'_eq : d' = d₁ := ((dart_edge_eq_iff d' d₁).mp h1).resolve_right fun hsym => by
              have : d₁.fst = d₁.snd := by rw [hd₁_fst, ← hd'_fst, hsym]; rfl
              exact d₁.adj.ne this
            subst hd'_eq
            have hcm1 := hfull_v.1 r_y hry_pos (hry_wmin.trans_le (hwmin d'))
            have heq_pt : edgePoint d' t' = circleMap hs.1 (s - r_y) := by
              rw [hcm1]
              congr 1; ext; simp [r_y, mul_div_cancel_right₀ _ (W.dart_weight_pos d').ne']
            have h_res := kill_circle_shift (edgePoint d' t') hdby_p hdb0y_p (ρ := -r_y)
              (by rw [abs_neg, abs_of_pos hry_pos]; linarith)
              (by simpa only [show s + (-r_y) = s - r_y by ring] using heq_pt)
            have hd_vy : dist (vertex v : MetricGraph W) (edgePoint d' t') = r_y := by
              rw [heq_pt, ← hs_v]
              refine (circleMap_dist_eq_of_le hs ?_).trans ?_
              · rw [show s - (s - r_y) = r_y by ring, abs_of_pos hry_pos]; linarith
              · rw [show s - (s - r_y) = r_y by ring, abs_of_pos hry_pos]
            dsimp only [a] at h_res
            rw [h_res, hs_v, _root_.dist_self] at hd_vy
            linarith
          · by_cases h2 : d'.edge = d₂.edge
            · have hd'_eq : d' = d₂ := ((dart_edge_eq_iff d' d₂).mp h2).resolve_right fun hsym => by
                have : d₂.fst = d₂.snd := by rw [hd₂_fst, ← hd'_fst, hsym]; rfl
                exact d₂.adj.ne this
              subst hd'_eq
              have hcm2 := hfull_v.2 r_y hry_pos (hry_wmin.trans_le (hwmin d'))
              have heq_pt : edgePoint d' t' = circleMap hs.1 (s + r_y) := by
                rw [hcm2]
                congr 1; ext; simp [r_y, mul_div_cancel_right₀ _ (W.dart_weight_pos d').ne']
              have h_res := kill_circle_shift (edgePoint d' t') hdby_p hdb0y_p (ρ := r_y)
                (by rw [abs_of_pos hry_pos]; linarith) heq_pt
              have hd_vy : dist (vertex v : MetricGraph W) (edgePoint d' t') = r_y := by
                rw [heq_pt, ← hs_v]
                refine (circleMap_dist_eq_of_le hs ?_).trans ?_
                · rw [sub_add_cancel_left, abs_neg, abs_of_pos hry_pos]; linarith
                · rw [sub_add_cancel_left, abs_neg, abs_of_pos hry_pos]
              dsimp only [a] at h_res
              rw [h_res, hs_v, _root_.dist_self] at hd_vy
              linarith
            · have hd'_not : d'.edge ∉ c.edges :=
                edge_not_mem_cycle_of_ne hs.1 hv_sup hd₁_fst hd₂_fst hd₁₂ hd₁_mem hd₂_mem
                  hd'_fst h1 h2
              have hbv : dist (vertex v : MetricGraph W) b = r := by
                rw [← hs_v]; exact hdab
              have hsum_lt : 2 * dist (vertex v : MetricGraph W) b + r_y < L := by
                rw [hbv]; dsimp only [r, L] at hη_L hR_lt ⊢
                linarith [hη'.2, hη_pos, hry_le, hη_L]
              have hgt := dist_third_dart_gt_of_circleMap W hs hv_sup hd'_fst hd'_not t' ht'0
                (hry_wmin.trans_le (hwmin d')) hsum_lt
              rw [hbv] at hgt
              exact absurd hdby_p hgt.not_ge
        exfalso
        rcases hev with hfst | hsnd
        · exact h_at_fst hfst ht0 ht1 hp hdby_ep hdb0y_ep
        · rw [← edgePoint_symm d t] at hp hdby_ep hdb0y_ep
          exact h_at_fst hsnd (sub_pos.mpr ht1) (sub_lt_self 1 ht0) hp hdby_ep hdb0y_ep
  have hvert_done : ∀ s_v : ℝ, ∀ v : V, circleMap hs.1 s_v = vertex v →
      ∀ r' ∈ Set.Icc 0 η,
        f ![circleMap hs.1 s_v, circleMap hs.1 (s_v + σ * (R + r'))] = circleMap hs.1 s_v :=
    fun s_v v hsv r' hr' => hstep_η_core r' hr' s_v (Or.inl ⟨v, hsv⟩)
  have hmem : R + η ∈ S := by
    refine ⟨⟨by linarith only [hR_pos, hη_pos], by linarith only [hη_pos, hη_L]⟩,
      fun r' hr' s => ?_⟩
    rcases le_or_gt r' R with hle | hgt
    · exact hR_Icc r' ⟨hr'.1, hle⟩ s
    · have h := hstep_η_core (r' - R) ⟨by linarith only [hgt], by linarith only [hr'.2]⟩
        s (Or.inr hvert_done)
      rw [show R + (r' - R) = r' by ring] at h
      exact h
  have hle_sup := le_csSup hS_bdd hmem
  linarith only [hη_pos, hle_sup]

private theorem finTwo_cycleDictator_of_half {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {g : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hg_sp : (Mechanism.deterministic g).IsStrategyProof)
    (hpos : ∀ u r : ℝ, 0 ≤ r → r < walkLength W.weight c / 2 →
      g ![circleMap hs.1 u, circleMap hs.1 (u + r)] = circleMap hs.1 u)
    (hneg : ∀ u r : ℝ, 0 ≤ r → r < walkLength W.weight c / 2 →
      g ![circleMap hs.1 u, circleMap hs.1 (u - r)] = circleMap hs.1 u) :
    ∀ a ∈ Set.range (circleMap hs.1), ∀ b ∈ Set.range (circleMap hs.1),
      g ![a, b] = a := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  intro a ha b hb
  obtain ⟨sa, rfl⟩ := ha
  obtain ⟨sb, rfl⟩ := hb
  let k : ℤ := ⌈(sb - sa) / L - 1 / 2⌉
  let r := (sb - sa) - (k : ℝ) * L
  have hr_lo : -L / 2 < r := by
    have hceil := Int.ceil_lt_add_one ((sb - sa) / L - 1 / 2)
    have hmul : (k : ℝ) * L < ((sb - sa) / L - 1 / 2 + 1) * L := by
      dsimp only [k]
      exact mul_lt_mul_of_pos_right hceil hL
    have hdiv : ((sb - sa) / L - 1 / 2 + 1) * L = (sb - sa) + L / 2 := by
      field_simp [hL.ne']; ring
    dsimp only [r]
    linarith
  have hr_hi : r ≤ L / 2 := by
    have hceil := Int.le_ceil ((sb - sa) / L - 1 / 2)
    have hmul : ((sb - sa) / L - 1 / 2) * L ≤ (k : ℝ) * L := by
      dsimp only [k]
      exact mul_le_mul_of_nonneg_right hceil hL.le
    have hdiv : ((sb - sa) / L - 1 / 2) * L = (sb - sa) - L / 2 := by
      field_simp [hL.ne']
    dsimp only [r]
    linarith
  have hsb_eq : circleMap hs.1 sb = circleMap hs.1 (sa + r) := by
    rw [show sb = (sa + r) + (k : ℝ) * L by dsimp only [r]; ring, circleMap_add_int_mul hs.1]
  rw [hsb_eq]
  rcases lt_or_eq_of_le hr_hi with hlt | heq
  · rcases le_or_gt 0 r with hr0 | hrn
    · exact hpos sa r hr0 hlt
    · rw [show sa + r = sa - (-r) by ring]
      exact hneg sa (-r) (neg_pos.mpr hrn).le (by linarith)
  · rw [heq]
    refine eq_of_forall_dist_le fun ε hε => ?_
    let ε' := min (ε / 2) (L / 4)
    have hε' : 0 < ε' := by positivity
    let a' := circleMap hs.1 (sa + ε')
    have ha'b : g ![a', circleMap hs.1 (sa + L / 2)] = a' := by
      rw [show sa + L / 2 = (sa + ε') + (L / 2 - ε') by ring]
      exact hpos (sa + ε') (L / 2 - ε') (by linarith [min_le_right (ε / 2) (L / 4)])
        (by linarith)
    have hgsp := (Mechanism.isStrategyProof_deterministic_iff g).mp hg_sp
    have hsp0 := hgsp ![circleMap hs.1 sa, circleMap hs.1 (sa + L / 2)] 0 a'
    have hupd : Function.update ![circleMap hs.1 sa, circleMap hs.1 (sa + L / 2)] 0 a' =
        ![a', circleMap hs.1 (sa + L / 2)] := by
      ext i; fin_cases i <;> rfl
    rw [hupd, ha'b] at hsp0
    simp only [Matrix.cons_val_zero] at hsp0
    have hdaa' : dist (circleMap hs.1 sa) a' = ε' := by
      refine (circleMap_dist_eq_of_le hs ?_).trans ?_
      · rw [sub_add_cancel_left, abs_neg, abs_of_pos hε']; linarith [min_le_right (ε / 2) (L / 4)]
      · rw [sub_add_cancel_left, abs_neg, abs_of_pos hε']
    have hε_le : ε' ≤ ε := (min_le_left _ _).trans (by linarith)
    rw [_root_.dist_comm]
    exact hsp0.trans (hdaa'.le.trans hε_le)

private theorem finTwo_cycleDictator_pos_contra {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {g : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hg_sp : (Mechanism.deterministic g).IsStrategyProof)
    (h1 : ∀ u r : ℝ, 0 ≤ r → r < walkLength W.weight c / 2 →
      g ![circleMap hs.1 u, circleMap hs.1 (u + r)] = circleMap hs.1 u)
    (h2 : ∀ u r : ℝ, 0 ≤ r → r < walkLength W.weight c / 2 →
      g ![circleMap hs.1 (u + r), circleMap hs.1 u] = circleMap hs.1 u) : False := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  let ε := L / 8
  have hε : 0 < ε := by positivity
  have hfirst := h1 0 (L / 2 - ε) (by dsimp only [ε]; linarith) (by dsimp only [ε]; linarith)
  rw [zero_add] at hfirst
  have hsecond : g ![circleMap hs.1 0, circleMap hs.1 (L / 2 + ε)] =
      circleMap hs.1 (L / 2 + ε) := by
    have hper : circleMap hs.1 0 = circleMap hs.1 ((L / 2 + ε) + (L / 2 - ε)) := by
      rw [show (L / 2 + ε) + (L / 2 - ε) = 0 + L by ring, circleMap_periodic hs.1 0]
    rw [hper]
    exact h2 (L / 2 + ε) (L / 2 - ε) (by dsimp only [ε]; linarith) (by dsimp only [ε]; linarith)
  have hgsp := (Mechanism.isStrategyProof_deterministic_iff g).mp hg_sp
  have hsp1 := hgsp ![circleMap hs.1 0, circleMap hs.1 (L / 2 - ε)] 1 (circleMap hs.1 (L / 2 + ε))
  have hupd : Function.update ![circleMap hs.1 0, circleMap hs.1 (L / 2 - ε)] 1
      (circleMap hs.1 (L / 2 + ε)) = ![circleMap hs.1 0, circleMap hs.1 (L / 2 + ε)] := by
    ext i; fin_cases i <;> rfl
  rw [hupd, hfirst, hsecond] at hsp1
  change dist (circleMap hs.1 (L / 2 - ε)) (circleMap hs.1 0) ≤
    dist (circleMap hs.1 (L / 2 - ε)) (circleMap hs.1 (L / 2 + ε)) at hsp1
  have hd1 : dist (circleMap hs.1 (L / 2 - ε)) (circleMap hs.1 0) = L / 2 - ε := by
    refine (circleMap_dist_eq_of_le hs ?_).trans ?_
    · rw [sub_zero, abs_of_pos (by dsimp only [ε]; linarith)]; dsimp only [ε]; linarith
    · rw [sub_zero, abs_of_pos (by dsimp only [ε]; linarith)]
  have hd2 : dist (circleMap hs.1 (L / 2 - ε)) (circleMap hs.1 (L / 2 + ε)) = 2 * ε := by
    refine (circleMap_dist_eq_of_le hs ?_).trans ?_
    · rw [show (L / 2 - ε) - (L / 2 + ε) = -(2 * ε) by ring, abs_neg,
        abs_of_pos (by positivity)]; dsimp only [ε]; linarith
    · rw [show (L / 2 - ε) - (L / 2 + ε) = -(2 * ε) by ring, abs_neg, abs_of_pos (by positivity)]
  dsimp only [ε] at hd1 hd2
  linarith

private theorem finTwo_cycleDictator_neg_contra {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (h1' : ∀ u r : ℝ, 0 ≤ r → r < walkLength W.weight c / 2 →
      f ![circleMap hs.1 u, circleMap hs.1 (u - r)] = circleMap hs.1 u)
    (h2' : ∀ u r : ℝ, 0 ≤ r → r < walkLength W.weight c / 2 →
      f ![circleMap hs.1 (u - r), circleMap hs.1 u] = circleMap hs.1 u) : False := by
  let L := walkLength W.weight c
  have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
  let ε := L / 8
  have hε : 0 < ε := by positivity
  have ha1 := h1' 0 (L / 2 - ε) (by dsimp only [ε]; linarith) (by dsimp only [ε]; linarith)
  rw [zero_sub] at ha1
  have ha2 : f ![circleMap hs.1 0, circleMap hs.1 (-(L / 2 + ε))] =
      circleMap hs.1 (-(L / 2 + ε)) := by
    have hper : circleMap hs.1 0 = circleMap hs.1 ((-(L / 2 + ε)) - (L / 2 - ε)) := by
      rw [show (-(L / 2 + ε)) - (L / 2 - ε) = 0 + (-1 : ℤ) * L by push_cast; ring,
        circleMap_add_int_mul hs.1]
    rw [hper]
    exact h2' (-(L / 2 + ε)) (L / 2 - ε) (by dsimp only [ε]; linarith) (by dsimp only [ε]; linarith)
  have hfsp := (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp
  have hsp1 := hfsp ![circleMap hs.1 0, circleMap hs.1 (-(L / 2 - ε))] 1
    (circleMap hs.1 (-(L / 2 + ε)))
  have hupd : Function.update ![circleMap hs.1 0, circleMap hs.1 (-(L / 2 - ε))] 1
      (circleMap hs.1 (-(L / 2 + ε))) = ![circleMap hs.1 0, circleMap hs.1 (-(L / 2 + ε))] := by
    ext i; fin_cases i <;> rfl
  rw [hupd, ha1, ha2] at hsp1
  change dist (circleMap hs.1 (-(L / 2 - ε))) (circleMap hs.1 0) ≤
    dist (circleMap hs.1 (-(L / 2 - ε))) (circleMap hs.1 (-(L / 2 + ε))) at hsp1
  have hd1 : dist (circleMap hs.1 (-(L / 2 - ε))) (circleMap hs.1 0) = L / 2 - ε := by
    refine (circleMap_dist_eq_of_le hs ?_).trans ?_
    · rw [sub_zero, abs_neg, abs_of_pos (by dsimp only [ε]; linarith)]; dsimp only [ε]; linarith
    · rw [sub_zero, abs_neg, abs_of_pos (by dsimp only [ε]; linarith)]
  have hd2 : dist (circleMap hs.1 (-(L / 2 - ε))) (circleMap hs.1 (-(L / 2 + ε))) = 2 * ε := by
    refine (circleMap_dist_eq_of_le hs ?_).trans ?_
    · rw [show -(L / 2 - ε) - -(L / 2 + ε) = 2 * ε by ring, abs_of_pos (by positivity)]
      dsimp only [ε]; linarith
    · rw [show -(L / 2 - ε) - -(L / 2 + ε) = 2 * ε by ring, abs_of_pos (by positivity)]
  dsimp only [ε] at hd1 hd2
  linarith

private theorem finTwo_cycleDictator {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {f : (Fin 2 → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_unam : ∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p) :
    ∃ k : Fin 2, ∀ a ∈ Set.range (circleMap hs.1), ∀ b ∈ Set.range (circleMap hs.1),
      f ![a, b] = ![a, b] k := by
  let f_swap : (Fin 2 → MetricGraph W) → MetricGraph W := fun x => f ![x 1, x 0]
  have hf_swap_eq : f_swap = fun x : Fin 2 → MetricGraph W => f (fun i => x (![1, 0] i)) := by
    funext x; exact congrArg f (by ext i; fin_cases i <;> rfl)
  have hsp_swap : (Mechanism.deterministic f_swap).IsStrategyProof := by
    rw [hf_swap_eq]
    exact merge_isStrategyProof hf_sp ![1, 0]
  have hunam_swap : ∀ p ∈ Set.range (circleMap hs.1), f_swap (fun _ => p) = p := by
    intro p hp
    dsimp only [f_swap]
    have : ![p, p] = fun _ => p := by ext i; fin_cases i <;> rfl
    rw [this]; exact hf_unam p hp
  obtain ⟨δ₁, hδ₁, hor1⟩ := orientation_dichotomy_circle W hs hf_sp hf_unam
  obtain ⟨δ₂, hδ₂, hor2⟩ := orientation_dichotomy_circle W hs hsp_swap hunam_swap
  rcases hor1 with hl1 | hr1 <;> rcases hor2 with hl2 | hr2
  · exfalso
    have he1 := extend_dir_half W hs hf_sp hf_unam (Or.inl rfl) hδ₁
      (fun u r h1 h2 => by rw [one_mul]; exact hl1 u r h1 h2)
    have he2 := extend_dir_half W hs hsp_swap hunam_swap (Or.inl rfl) hδ₂
      (fun u r h1 h2 => by rw [one_mul]; exact hl2 u r h1 h2)
    refine finTwo_cycleDictator_pos_contra W hs hf_sp
      (fun u r h1 h2 => by simpa only [one_mul] using he1 u r h1 h2)
      (fun u r h1 h2 => ?_)
    have h2' := he2 u r h1 h2
    rw [one_mul] at h2'
    dsimp only [f_swap] at h2'
    rw [show ![![circleMap hs.1 u, circleMap hs.1 (u + r)] 1,
        ![circleMap hs.1 u, circleMap hs.1 (u + r)] 0] =
        ![circleMap hs.1 (u + r), circleMap hs.1 u] by ext i; fin_cases i <;> rfl] at h2'
    exact h2'
  · refine ⟨0, finTwo_cycleDictator_of_half W hs hf_sp ?_ ?_⟩
    · have he1 := extend_dir_half W hs hf_sp hf_unam (Or.inl rfl) hδ₁
        (fun u r h1 h2 => by rw [one_mul]; exact hl1 u r h1 h2)
      intro u r h1 h2; simpa only [one_mul] using he1 u r h1 h2
    · have he2 := extend_dir_half W hs hf_sp hf_unam (Or.inr rfl) hδ₂
        (fun u r h1 h2 => by
          rw [show u + (-1) * r = u - r by ring]
          have h2' := hr2 (u - r) r h1 h2
          dsimp only [f_swap] at h2'
          rw [sub_add_cancel] at h2'
          rw [show ![![circleMap hs.1 (u - r), circleMap hs.1 u] 1,
              ![circleMap hs.1 (u - r), circleMap hs.1 u] 0] =
              ![circleMap hs.1 u, circleMap hs.1 (u - r)] by ext i; fin_cases i <;> rfl] at h2'
          exact h2')
      intro u r h1 h2
      have h2' := he2 u r h1 h2
      rwa [show u + (-1) * r = u - r by ring] at h2'
  · refine ⟨1, fun a ha b hb => ?_⟩
    have hdict := finTwo_cycleDictator_of_half W hs hsp_swap ?_ ?_ b hb a ha
    · dsimp only [f_swap] at hdict
      rw [show ![![b, a] 1, ![b, a] 0] = ![a, b] by ext i; fin_cases i <;> rfl] at hdict
      exact hdict
    · have he2 := extend_dir_half W hs hsp_swap hunam_swap (Or.inl rfl) hδ₂
        (fun u r h1 h2 => by rw [one_mul]; exact hl2 u r h1 h2)
      intro u r h1 h2
      have h2' := he2 u r h1 h2
      rwa [one_mul] at h2'
    · have he1 := extend_dir_half W hs hsp_swap hunam_swap (Or.inr rfl) hδ₁
        (fun u r h1 h2 => by
          rw [show u + (-1) * r = u - r by ring]
          dsimp only [f_swap]
          have hpair : ![circleMap hs.1 (u - r), circleMap hs.1 u] =
              ![![circleMap hs.1 u, circleMap hs.1 (u - r)] 1,
                ![circleMap hs.1 u, circleMap hs.1 (u - r)] 0] := by
            ext i; fin_cases i <;> rfl
          rw [← hpair]
          have h1' := hr1 (u - r) r h1 h2
          rwa [sub_add_cancel] at h1')
      intro u r h1 h2
      have h1' := he1 u r h1 h2
      rwa [show u + (-1) * r = u - r by ring] at h1'
  · exfalso
    have he1 := extend_dir_half W hs hf_sp hf_unam (Or.inr rfl) hδ₂
      (fun u r h1 h2 => by
        rw [show u + (-1) * r = u - r by ring]
        have h2' := hr2 (u - r) r h1 h2
        dsimp only [f_swap] at h2'
        rw [sub_add_cancel] at h2'
        rw [show ![![circleMap hs.1 (u - r), circleMap hs.1 u] 1,
            ![circleMap hs.1 (u - r), circleMap hs.1 u] 0] =
            ![circleMap hs.1 u, circleMap hs.1 (u - r)] by ext i; fin_cases i <;> rfl] at h2'
        exact h2')
    have he2 := extend_dir_half W hs hsp_swap hunam_swap (Or.inr rfl) hδ₁
      (fun u r h1 h2 => by
        rw [show u + (-1) * r = u - r by ring]
        dsimp only [f_swap]
        have hpair : ![circleMap hs.1 (u - r), circleMap hs.1 u] =
            ![![circleMap hs.1 u, circleMap hs.1 (u - r)] 1,
              ![circleMap hs.1 u, circleMap hs.1 (u - r)] 0] := by
          ext i; fin_cases i <;> rfl
        rw [← hpair]
        have h1' := hr1 (u - r) r h1 h2
        rwa [sub_add_cancel] at h1')
    refine finTwo_cycleDictator_neg_contra W hs hf_sp
      (fun u r h1 h2 => by
        have h1' := he1 u r h1 h2
        rwa [show u + (-1) * r = u - r by ring] at h1')
      (fun u r h1 h2 => ?_)
    have h2' := he2 u r h1 h2
    rw [show u + (-1) * r = u - r by ring] at h2'
    dsimp only [f_swap] at h2'
    rw [show ![![circleMap hs.1 u, circleMap hs.1 (u - r)] 1,
        ![circleMap hs.1 u, circleMap hs.1 (u - r)] 0] =
        ![circleMap hs.1 (u - r), circleMap hs.1 u] by ext i; fin_cases i <;> rfl] at h2'
    exact h2'

end Fin2CycleDictator

section CycleDictator

private theorem cycleDictator_of_unanimous_aux {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c) :
    ∀ n : ℕ, ∀ {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι],
      Fintype.card ι = n →
      ∀ {f : (ι → MetricGraph W) → MetricGraph W},
        (Mechanism.deterministic f).IsStrategyProof →
        (∀ p ∈ Set.range (circleMap hs.1), f (fun _ => p) = p) →
        ∃ i₀ : ι, ∀ x : ι → MetricGraph W,
          (∀ i, x i ∈ Set.range (circleMap hs.1)) → f x = x i₀ := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro ι _ _ _ hcard f hf_sp hf_unam
    let C := Set.range (circleMap hs.1)
    let L := walkLength W.weight c
    have hL : 0 < L := walkLength_pos_of_not_nil hs.1.not_nil
    have htwo_pts : ∃ p₀ p₁ : MetricGraph W, p₀ ∈ C ∧ p₁ ∈ C ∧ p₀ ≠ p₁ := by
      refine ⟨circleMap hs.1 0, circleMap hs.1 (L / 4), ⟨0, rfl⟩, ⟨L / 4, rfl⟩, fun h => ?_⟩
      have hd : dist (circleMap hs.1 0) (circleMap hs.1 (L / 4)) = L / 4 := by
        refine (circleMap_dist_eq_of_le hs ?_).trans ?_
        · rw [zero_sub, abs_neg, abs_of_pos (by positivity)]; linarith
        · rw [zero_sub, abs_neg, abs_of_pos (by positivity)]
      rw [h, _root_.dist_self] at hd
      linarith
    obtain ⟨p₀, p₁, hp₀, hp₁, hp₀₁⟩ := htwo_pts
    let U : Set (Finset ι) := { S | ∀ a ∈ C, ∀ b ∈ C,
      f (fun i => if i ∈ S then a else b) = a }
    have hU_mem_compl : ∀ S : Finset ι, S ∈ U ∨ Sᶜ ∈ U := by
      intro S
      let g : (Fin 2 → MetricGraph W) → MetricGraph W :=
        fun y => f (fun i => if i ∈ S then y 0 else y 1)
      let sel : ι → Fin 2 := fun i => if i ∈ S then 0 else 1
      have hg_eq : g = fun y => f (fun i => y (sel i)) := by
        funext y; exact congrArg f (by ext i; dsimp only [sel]; split_ifs <;> rfl)
      have hg_sp : (Mechanism.deterministic g).IsStrategyProof := by
        rw [hg_eq]
        exact merge_isStrategyProof hf_sp sel
      have hg_unam : ∀ p ∈ C, g (fun _ => p) = p := by
        intro p hp
        dsimp only [g]
        have : (fun i : ι => if i ∈ S then p else p) = fun _ => p := by ext; split_ifs <;> rfl
        rw [this]; exact hf_unam p hp
      obtain ⟨k, hk⟩ := finTwo_cycleDictator W hs hg_sp hg_unam
      fin_cases k
      · left; intro a ha b hb
        have h1 := hk a ha b hb
        dsimp only [g] at h1
        rwa [show (fun i => if i ∈ S then (![a, b] : Fin 2 → MetricGraph W) 0 else ![a, b] 1) =
            fun i => if i ∈ S then a else b by ext i; split_ifs <;> rfl] at h1
      · right; intro a ha b hb
        have hfun : (fun i => if i ∈ Sᶜ then a else b) = (fun i => if i ∈ S then b else a) := by
          ext i; by_cases hi : i ∈ S <;> simp [hi]
        rw [hfun]
        have h2 := hk b hb a ha
        dsimp only [g] at h2
        rwa [show (fun i => if i ∈ S then (![b, a] : Fin 2 → MetricGraph W) 0 else ![b, a] 1) =
            fun i => if i ∈ S then b else a by ext i; split_ifs <;> rfl] at h2
    have hU_disj : ∀ S₁ S₂ : Finset ι, Disjoint S₁ S₂ → S₁ ∈ U → S₂ ∈ U → False := by
      intro S₁ S₂ hdisj h1 h2
      let x := fun i => if i ∈ S₂ then p₁ else p₀
      let x' := fun i => if i ∈ S₁ then p₀ else p₁
      let P₃ := (S₁ ∪ S₂)ᶜ
      have hfx : f x = p₁ := h2 p₁ hp₁ p₀ hp₀
      have hfx' : f x' = p₀ := h1 p₀ hp₀ p₁ hp₁
      have hP₃ : ∀ i ∈ P₃, x i = p₀ := by
        intro i hi
        simp only [P₃, Finset.mem_compl, Finset.mem_union, not_or] at hi
        simp [x, hi.2]
      have hx'_eq : (fun i => if i ∈ P₃ then p₁ else x i) = x' := by
        ext i
        by_cases hi1 : i ∈ S₁
        · have hni2 : i ∉ S₂ := Finset.disjoint_left.mp hdisj hi1
          have hni3 : i ∉ P₃ := by simp [P₃, hi1]
          simp [x, x', hi1, hni2, hni3]
        · by_cases hi2 : i ∈ S₂
          · have hni3 : i ∉ P₃ := by simp [P₃, hi2]
            simp [x, x', hi1, hi2, hni3]
          · have hi3 : i ∈ P₃ := by simp [P₃, hi1, hi2]
            simp [x, x', hi1, hi3]
      have hcoal := coalition_sp hf_sp P₃ p₀ p₁ x hP₃
      rw [hx'_eq, hfx, hfx', _root_.dist_self] at hcoal
      exact hp₀₁ (dist_eq_zero.mp (le_antisymm hcoal dist_nonneg))
    have hU_mono : ∀ {A B : Finset ι}, A ⊆ B → A ∈ U → B ∈ U := by
      intro A B hAB hA
      rcases hU_mem_compl B with hB | hBc
      · exact hB
      · exfalso
        exact hU_disj A Bᶜ
          (Finset.disjoint_left.mpr fun i hi1 hic => (Finset.mem_compl.mp hic) (hAB hi1))
          hA hBc
    have hU_inter : ∀ S₁ S₂ : Finset ι, S₁ ∈ U → S₂ ∈ U → S₁ ∩ S₂ ∈ U := by
      intro S₁ S₂ h1 h2 a ha b hb
      let P₂ := S₁ \ S₂
      let P₃ := S₁ ∩ S₂
      let g : (Fin 2 → MetricGraph W) → MetricGraph W :=
        fun y => f (fun i => if i ∈ P₂ then y 0 else if i ∈ P₃ then y 1 else b)
      have hg_sp : (Mechanism.deterministic g).IsStrategyProof := by
        rw [Mechanism.isStrategyProof_deterministic_iff]
        intro y j z
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) j with rfl | rfl
        · let x : ι → MetricGraph W :=
            fun i => if i ∈ P₂ then y 0 else if i ∈ P₃ then y 1 else b
          have hx : ∀ i ∈ P₂, x i = y 0 := fun i hi => by simp [x, hi]
          have hfun : (fun i => if i ∈ P₂ then Function.update y 0 z 0 else
              if i ∈ P₃ then Function.update y 0 z 1 else b) =
              (fun i => if i ∈ P₂ then z else x i) := by
            ext i; by_cases hi : i ∈ P₂ <;> simp [x, hi]
          dsimp only [g]
          rw [hfun]
          exact coalition_sp hf_sp P₂ (y 0) z x hx
        · let x : ι → MetricGraph W :=
            fun i => if i ∈ P₂ then y 0 else if i ∈ P₃ then y 1 else b
          have hx : ∀ i ∈ P₃, x i = y 1 := fun i hi => by
            have hni2 : i ∉ P₂ := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hi).2
            simp [x, hi, hni2]
          have hfun : (fun i => if i ∈ P₂ then Function.update y 1 z 0 else
              if i ∈ P₃ then Function.update y 1 z 1 else b) =
              (fun i => if i ∈ P₃ then z else x i) := by
            ext i
            by_cases hi2 : i ∈ P₂
            · have hni3 : i ∉ P₃ := fun h => (Finset.mem_sdiff.mp hi2).2 (Finset.mem_inter.mp h).2
              simp [x, hi2, hni3]
            · by_cases hi3 : i ∈ P₃ <;> simp [x, hi2, hi3]
          dsimp only [g]
          rw [hfun]
          exact coalition_sp hf_sp P₃ (y 1) z x hx
      have hg_unam : ∀ p ∈ C, g (fun _ => p) = p := by
        intro p hp
        dsimp only [g]
        have hfun : (fun i => if i ∈ P₂ then p else if i ∈ P₃ then p else b) =
            (fun i => if i ∈ S₁ then p else b) := by
          ext i
          by_cases hi1 : i ∈ S₁
          · by_cases hi2 : i ∈ S₂ <;> simp [P₂, P₃, hi1, hi2]
          · simp [P₂, P₃, hi1]
        rw [hfun]
        exact h1 p hp b hb
      obtain ⟨k, hk⟩ := finTwo_cycleDictator W hs hg_sp hg_unam
      fin_cases k
      · exfalso
        have hex_c' : ∃ c' ∈ C, c' ≠ b := by
          by_cases he : p₀ = b
          · exact ⟨p₁, hp₁, he ▸ hp₀₁.symm⟩
          · exact ⟨p₀, hp₀, he⟩
        obtain ⟨c', hc', hne⟩ := hex_c'
        have h1' := hk c' hc' b hb
        have hP₂c : P₂ᶜ ∈ U := by
          refine hU_mono ?_ h2
          intro i hi2
          simp [P₂, hi2]
        have hfun : (fun i => if i ∈ P₂ then (![c', b] : Fin 2 → MetricGraph W) 0 else
            if i ∈ P₃ then ![c', b] 1 else b) =
            (fun i => if i ∈ P₂ᶜ then b else c') := by
          ext i; by_cases hi : i ∈ P₂ <;> simp [hi]
        dsimp only [g] at h1'
        rw [hfun, hP₂c b hb c' hc'] at h1'
        exact hne h1'.symm
      · have h2' := hk b hb a ha
        have hfun : (fun i => if i ∈ P₂ then (![b, a] : Fin 2 → MetricGraph W) 0 else
            if i ∈ P₃ then ![b, a] 1 else b) =
            (fun i => if i ∈ S₁ ∩ S₂ then a else b) := by
          ext i
          by_cases hi1 : i ∈ S₁ <;> by_cases hi2 : i ∈ S₂ <;> simp [P₂, P₃, hi1, hi2]
        dsimp only [g] at h2'
        rw [hfun] at h2'
        exact h2'
    have hU_univ : (Finset.univ : Finset ι) ∈ U := by
      intro a ha b _
      have : (fun i : ι => if i ∈ (Finset.univ : Finset ι) then a else b) = fun _ => a := by
        ext; simp
      rw [this]; exact hf_unam a ha
    have hU_empty : (∅ : Finset ι) ∉ U := by
      intro h
      have := h p₀ hp₀ p₁ hp₁
      simp only [Finset.notMem_empty, ↓reduceIte] at this
      rw [hf_unam p₁ hp₁] at this
      exact hp₀₁ this.symm
    have hex_singleton : ∃ i₀ : ι, ({i₀} : Finset ι) ∈ U := by
      let _ : DecidablePred (· ∈ U) := Classical.decPred _
      let F : Finset (Finset ι) := Finset.univ.filter fun S => S ∈ U
      have hF_ne : F.Nonempty := ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU_univ⟩⟩
      obtain ⟨S₀, hS₀_mem, hS₀_min⟩ := F.exists_min_image Finset.card hF_ne
      have hS₀_in : S₀ ∈ U := (Finset.mem_filter.mp hS₀_mem).2
      have hS₀_ne : S₀.Nonempty := by
        by_contra hne
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        exact hU_empty (hne ▸ hS₀_in)
      obtain ⟨i₀, hi₀⟩ := hS₀_ne
      rcases hU_mem_compl {i₀} with hi | hic
      · exact ⟨i₀, hi⟩
      · exfalso
        have hinter : S₀ ∩ ({i₀} : Finset ι)ᶜ ∈ U := hU_inter S₀ {i₀}ᶜ hS₀_in hic
        have hinter_F : S₀ ∩ ({i₀} : Finset ι)ᶜ ∈ F :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinter⟩
        have hlt : (S₀ ∩ ({i₀} : Finset ι)ᶜ).card < S₀.card := by
          refine Finset.card_lt_card ⟨Finset.inter_subset_left, ?_⟩
          intro hsub
          have := hsub hi₀
          simp at this
        linarith [hS₀_min _ hinter_F]
    obtain ⟨i₀, hi₀_U⟩ := hex_singleton
    refine ⟨i₀, ?_⟩
    rcases lt_trichotomy n 2 with hn_lt | rfl | hn_gt
    · have hn1 : n = 1 := by
        have hpos : 0 < n := hcard ▸ Fintype.card_pos
        omega
      intro x hx
      have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      have hx_const : x = fun _ => x i₀ := funext fun i => congrArg x (Subsingleton.elim i i₀)
      rw [hx_const]
      exact hf_unam (x i₀) (hx i₀)
    · let e : ι ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
      let f2 : (Fin 2 → MetricGraph W) → MetricGraph W := fun y => f (fun i => y (e i))
      have hf2_sp : (Mechanism.deterministic f2).IsStrategyProof :=
        merge_isStrategyProof hf_sp e
      have hf2_unam : ∀ p ∈ C, f2 (fun _ => p) = p := fun p hp => hf_unam p hp
      obtain ⟨k, hk⟩ := finTwo_cycleDictator W hs hf2_sp hf2_unam
      have hk_eq : k = e i₀ := by
        by_contra hne
        let y : Fin 2 → MetricGraph W := fun j => if j = e i₀ then p₁ else p₀
        have hy_e : (fun i => y (e i)) = fun i => if i = i₀ then p₁ else p₀ := by
          ext i
          simp only [y, e.injective.eq_iff]
        have hf2y_l : f2 y = p₁ := by
          dsimp only [f2]
          rw [hy_e]
          simpa only [Finset.mem_singleton] using hi₀_U p₁ hp₁ p₀ hp₀
        have hf2y_r : f2 y = y k := by
          have h0 : y 0 ∈ Set.range (circleMap hs.1) := by
            dsimp only [y]
            split_ifs <;> assumption
          have h1 : y 1 ∈ Set.range (circleMap hs.1) := by
            dsimp only [y]
            split_ifs <;> assumption
          have hval := hk (y 0) h0 (y 1) h1
          rw [show ![y 0, y 1] = y by
            ext i; fin_cases i <;> rfl] at hval
          exact hval
        have hyk : y k = p₀ := by
          dsimp only [y]
          by_cases h_eq : k = e i₀
          · exact absurd h_eq hne
          · simp [h_eq]
        exact hp₀₁ (hf2y_l.symm.trans (hf2y_r.trans hyk) |>.symm)
      intro x hx
      have hvec : (![x (e.symm 0), x (e.symm 1)] : Fin 2 → MetricGraph W) =
          fun z => x (e.symm z) := by
        ext z; fin_cases z <;> rfl
      have hval := hk (x (e.symm 0)) (hx _) (x (e.symm 1)) (hx _)
      dsimp only [f2] at hval
      rw [hvec, hk_eq] at hval
      simpa only [Equiv.symm_apply_apply] using hval
    · have hagree : ∀ {j₁ j₂ : ι} (_ : j₁ ≠ j₂) (x : ι → MetricGraph W),
          (∀ i, x i ∈ C) → x j₁ = x j₂ → f x = x i₀ := by
        intro j₁ j₂ hne x hx hx12
        let ι' := { i : ι // i ≠ j₂ }
        have : Nonempty ι' := ⟨⟨j₁, hne⟩⟩
        let m : ι → ι' := fun i => if h : i = j₂ then ⟨j₁, hne⟩ else ⟨i, h⟩
        let f' : (ι' → MetricGraph W) → MetricGraph W := fun y => f (fun i => y (m i))
        have hf'_sp : (Mechanism.deterministic f').IsStrategyProof :=
          merge_isStrategyProof hf_sp m
        have hf'_unam : ∀ p ∈ C, f' (fun _ => p) = p := fun p hp => hf_unam p hp
        have hcard' : Fintype.card ι' = n - 1 := by simp [ι', hcard]
        have hn_lt : n - 1 < n := by omega
        obtain ⟨k', hk'⟩ := ih (n - 1) hn_lt hcard' hf'_sp hf'_unam
        have hk'_eq : k' = m i₀ := by
          by_contra hk'_ne
          let y : ι' → MetricGraph W := fun i' => if i' = m i₀ then p₁ else p₀
          have hyC : ∀ i', y i' ∈ C := fun i' => by dsimp only [y]; split_ifs <;> assumption
          have h1 := hk' y hyC
          have hne_y : y k' = p₀ := by
            dsimp only [y]
            by_cases h : k' = m i₀
            · exact absurd h hk'_ne
            · simp [h]
          have hm_sub : {i₀} ⊆ Finset.univ.filter (fun i => m i = m i₀) := by
            intro i hi
            rw [Finset.mem_singleton] at hi
            subst hi
            simp
          have hm_U : Finset.univ.filter (fun i => m i = m i₀) ∈ U := hU_mono hm_sub hi₀_U
          have hfun_y : (fun i => y (m i)) =
              (fun i => if i ∈ Finset.univ.filter (fun i => m i = m i₀) then p₁ else p₀) := by
            ext i; simp [y]
          dsimp only [f'] at h1
          rw [hfun_y, hm_U p₁ hp₁ p₀ hp₀, hne_y] at h1
          exact hp₀₁ h1.symm
        let y : ι' → MetricGraph W := fun i' => x i'.1
        have hyC : ∀ i', y i' ∈ C := fun i' => hx i'.1
        have hval := hk' y hyC
        have hfun_x : (fun i => y (m i)) = x := by
          ext i
          by_cases h : i = j₂
          · subst h; simp [m, y, hx12]
          · simp [m, y, h]
        have hxm : y (m i₀) = x i₀ := by
          by_cases h : i₀ = j₂
          · subst h; simp [m, y, hx12]
          · simp [m, y, h]
        dsimp only [f'] at hval
        rw [hfun_x, hk'_eq, hxm] at hval
        exact hval
      intro x hx
      have hcard_erase : 2 ≤ (Finset.univ.erase i₀).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, hcard]
        omega
      obtain ⟨j₁, hj₁_mem, j₂, hj₂_mem, hj₁₂⟩ := Finset.one_lt_card.mp (by omega : 1 <
        (Finset.univ.erase i₀).card)
      have hj₁_ne : j₁ ≠ i₀ := Finset.ne_of_mem_erase hj₁_mem
      have hj₂_ne : j₂ ≠ i₀ := Finset.ne_of_mem_erase hj₂_mem
      let h : (Fin 2 → MetricGraph W) → MetricGraph W :=
        fun z => f (fun i => if i = i₀ then z 0 else if i = j₁ then z 1 else x i)
      have hh_sp : (Mechanism.deterministic h).IsStrategyProof := by
        rw [Mechanism.isStrategyProof_deterministic_iff]
        intro y j z
        rcases (by decide : ∀ x : Fin 2, x = 0 ∨ x = 1) j with rfl | rfl
        · let x' := fun i => if i = i₀ then y 0 else if i = j₁ then y 1 else x i
          have hfun : (fun i => if i = i₀ then Function.update y 0 z 0 else
              if i = j₁ then Function.update y 0 z 1 else x i) = Function.update x' i₀ z := by
            ext i
            dsimp only [x']
            by_cases hi0 : i = i₀
            · subst hi0; simp [Function.update]
            · by_cases hi1 : i = j₁
              · subst hi1; simp [hi0, Function.update]
              · simp [hi0, hi1, Function.update]
          dsimp only [h]
          rw [hfun]
          have hsp := (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp x' i₀ z
          simpa only [x', ↓reduceIte] using hsp
        · let x' := fun i => if i = i₀ then y 0 else if i = j₁ then y 1 else x i
          have hfun : (fun i => if i = i₀ then Function.update y 1 z 0 else
              if i = j₁ then Function.update y 1 z 1 else x i) = Function.update x' j₁ z := by
            ext i
            dsimp only [x']
            by_cases hi0 : i = i₀
            · subst hi0; simp [hj₁_ne.symm, Function.update]
            · by_cases hi1 : i = j₁
              · subst hi1; simp [hi0, Function.update]
              · simp [hi0, hi1, Function.update]
          dsimp only [h]
          rw [hfun]
          have hsp := (Mechanism.isStrategyProof_deterministic_iff f).mp hf_sp x' j₁ z
          simpa only [x', hj₁_ne, ↓reduceIte] using hsp
      have hh_unam : ∀ p ∈ C, h (fun _ => p) = p := by
        intro p hp
        dsimp only [h]
        have hval := hagree hj₁_ne.symm
          (fun i => if i = i₀ then p else if i = j₁ then p else x i)
          (fun i => by split_ifs <;> first | exact hp | exact hx i)
          (by simp [hj₁_ne])
        simpa only [↓reduceIte] using hval
      obtain ⟨k, hk⟩ := finTwo_cycleDictator W hs hh_sp hh_unam
      fin_cases k
      · have hval := hk (x i₀) (hx i₀) (x j₁) (hx j₁)
        have hfun : (fun i => if i = i₀ then (![x i₀, x j₁] : Fin 2 → MetricGraph W) 0 else
            if i = j₁ then ![x i₀, x j₁] 1 else x i) = x := by
          ext i; by_cases hi0 : i = i₀ <;> by_cases hi1 : i = j₁ <;> simp_all
        dsimp only [h] at hval
        rw [hfun] at hval
        exact hval
      · exfalso
        let a := x j₂
        have ha : a ∈ C := hx j₂
        have hex_b : ∃ b ∈ C, b ≠ a := by
          by_cases he : a = p₀
          · exact ⟨p₁, hp₁, he ▸ hp₀₁.symm⟩
          · exact ⟨p₀, hp₀, Ne.symm he⟩
        obtain ⟨b, hb, hab⟩ := hex_b
        have hval := hk a ha b hb
        have hagree_val : h ![a, b] = a := by
          dsimp only [h]
          change (f fun i => if i = i₀ then a else if i = j₁ then b else x i) = a
          have hval' := hagree hj₂_ne.symm
            (fun i => if i = i₀ then a else if i = j₁ then b else x i)
            (fun i => by split_ifs <;> first | exact ha | exact hb | exact hx i)
            (by dsimp only [a]; simp [hj₂_ne, hj₁₂.symm])
          simpa only [↓reduceIte] using hval'
        exact hab (hval.symm.trans hagree_val)

/-- **Schummer–Vohra cycle dictatorship** on shortest cycles ([SchummerVohra2002], Theorem 2,
for shortest cycles): every deterministic strategyproof
and onto facility-location mechanism on a finite metric graph `MetricGraph W` acts as a
dictatorship on the points of any shortest cycle `c` (without assuming the image on `C^ι` lies in
`C`, and without assuming group strategyproofness). -/
theorem exists_cycleDictator_of_isShortestCycle {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {v₀ : V} {c : W.graph.Walk v₀ v₀} (hs : IsShortestCycle W c)
    {ι : Type*} [Finite ι] [Nonempty ι] [DecidableEq ι]
    {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f) :
    ∃ i₀ : ι, ∀ x : ι → MetricGraph W,
      (∀ i, x i ∈ Set.range (circleMap hs.1)) → f x = x i₀ :=
  let _ := Fintype.ofFinite ι
  cycleDictator_of_unanimous_aux W hs (Fintype.card ι) rfl hf_sp
    (fun p _ => unanimous_of_surjective_isStrategyProof hf_sp hf_onto p)

/-- On any finite non-acyclic metric graph `MetricGraph W`, there exists a shortest cycle `c`
on which every deterministic strategyproof onto mechanism acts as a dictatorship. -/
theorem exists_cycleDictator_of_not_isAcyclic {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    (hc : ¬ W.graph.IsAcyclic)
    {ι : Type*} [Finite ι] [Nonempty ι] [DecidableEq ι]
    {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f) :
    ∃ (v₀ : V) (c : W.graph.Walk v₀ v₀) (hs : IsShortestCycle W c) (i₀ : ι),
      ∀ x : ι → MetricGraph W, (∀ i, x i ∈ Set.range (circleMap hs.1)) → f x = x i₀ := by
  obtain ⟨v₀, c, hs⟩ := exists_isShortestCycle (W := W) hc
  obtain ⟨i₀, hi₀⟩ := exists_cycleDictator_of_isShortestCycle W hs hf_sp hf_onto
  exact ⟨v₀, c, hs, i₀, hi₀⟩

/-- Every deterministic strategyproof onto facility-location mechanism on a finite cycle graph
`cycleGraph (n + 3)` is a global dictatorship. -/
theorem exists_dictatorship_of_cycleGraph {V : Type*} (W : WeightedGraph V) [Finite V]
    [MeasurableSpace (MetricGraph W)] [OpensMeasurableSpace (MetricGraph W)]
    {n : ℕ} (e : W.graph ≃g SimpleGraph.cycleGraph (n + 3))
    {ι : Type*} [Finite ι] [Nonempty ι] [DecidableEq ι]
    {f : (ι → MetricGraph W) → MetricGraph W}
    (hf_sp : (Mechanism.deterministic f).IsStrategyProof)
    (hf_onto : Function.Surjective f) :
    ∃ i₀ : ι, ∀ x : ι → MetricGraph W, f x = x i₀ := by
  have hc_W : ((SimpleGraph.cycleGraph.cycle n).map e.symm.toHom).IsCycle :=
    SimpleGraph.cycleGraph.isCycle_cycle.map e.symm.injective
  have hna : ¬ W.graph.IsAcyclic := fun h => h _ hc_W
  obtain ⟨v₀, c, hs⟩ := exists_isShortestCycle (W := W) hna
  obtain ⟨i₀, hi₀⟩ := exists_cycleDictator_of_isShortestCycle W hs hf_sp hf_onto
  have hsurj := circleMap_surjective_of_cycleGraph e hs.1
  exact ⟨i₀, fun x => hi₀ x fun i => hsurj (x i)⟩

end CycleDictator

end Cslib.GameTheory.FacilityLocation
