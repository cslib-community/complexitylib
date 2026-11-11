/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Basic
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Bipartite
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Geodesic
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Maps
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Realization
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Subdivision
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for continuous metric graphs

Concrete checks on asymmetric triangles (`Fin 3`), geodesics and metric intervals, subdivisions
and breakpoint counts, 3-segment Euclidean straight-edge realizations with rational coordinates,
non-bipartite non-affineness vs. bipartite equal-length affineness (`C_4`), and midpoint
subdivision of `C_3`.
-/

set_option linter.privateModule false
namespace CslibFrontierTests.MetricGraph

open SimpleGraph (MetricGraph)
open SimpleGraph.MetricGraph
open scoped unitInterval

private noncomputable def halfPt : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
private noncomputable def quarterPt : unitInterval := ⟨1 / 4, by norm_num, by norm_num⟩
private noncomputable def threeQuarterPt : unitInterval := ⟨3 / 4, by norm_num, by norm_num⟩

private theorem top_fin3_connected : (⊤ : SimpleGraph (Fin 3)).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact SimpleGraph.Reachable.refl 0
  · exact SimpleGraph.Adj.reachable (by decide)
  · exact SimpleGraph.Adj.reachable (by decide)

/-! ### Asymmetric triangle on `Fin 3` -/

private def asymWeightFun (e : Sym2 (Fin 3)) : ℝ :=
  if e = s(0, 1) then 10 else 1

private theorem asymWeightFun_ge_one (e : Sym2 (Fin 3)) : 1 ≤ asymWeightFun e := by
  dsimp only [asymWeightFun]
  split_ifs <;> norm_num

private noncomputable def asymTri : SimpleGraph.WeightedGraph (Fin 3) where
  graph := ⊤
  weight := asymWeightFun
  weight_pos _ _ _ := lt_of_lt_of_le zero_lt_one (asymWeightFun_ge_one _)
  connected := top_fin3_connected

private theorem asymWeightFun_of_ne {e : Sym2 (Fin 3)} (h : e ≠ s(0, 1)) :
    asymWeightFun e = 1 := by
  dsimp only [asymWeightFun]
  split_ifs with he
  · exact absurd he h
  · rfl

private theorem asymTri_adj {u v : Fin 3} (h : u ≠ v) : asymTri.graph.Adj u v := h

private theorem asymTri_walkLength_ge_one {u v : Fin 3} (hne : u ≠ v)
    (p : asymTri.graph.Walk u v) : 1 ≤ SimpleGraph.walkLength asymTri.weight p := by
  cases p with
  | nil => exact absurd rfl hne
  | cons hadj q =>
    rename_i v'
    rw [SimpleGraph.walkLength_cons]
    have hq := SimpleGraph.walkLength_nonneg asymTri.weight asymTri.weight_nonneg q
    have hw : 1 ≤ asymTri.weight s(u, v') := asymWeightFun_ge_one s(u, v')
    linarith

private theorem asymTri_vd_02 :
    SimpleGraph.vertexDist asymTri.graph asymTri.weight 0 2 = 1 := by
  refine le_antisymm ?_ ?_
  · refine (SimpleGraph.vertexDist_adj_le asymTri.weight_nonneg
      (asymTri_adj (by decide))).trans_eq ?_
    exact asymWeightFun_of_ne (e := s(0, 2)) (by decide)
  · obtain ⟨p, -, hp⟩ := SimpleGraph.exists_isPath_walkLength_eq_vertexDist
      asymTri.weight_nonneg (asymTri.connected 0 2)
    rw [← hp]
    exact asymTri_walkLength_ge_one (by decide) p

private theorem asymTri_vd_12 :
    SimpleGraph.vertexDist asymTri.graph asymTri.weight 1 2 = 1 := by
  refine le_antisymm ?_ ?_
  · refine (SimpleGraph.vertexDist_adj_le asymTri.weight_nonneg
      (asymTri_adj (by decide))).trans_eq ?_
    exact asymWeightFun_of_ne (e := s(1, 2)) (by decide)
  · obtain ⟨p, -, hp⟩ := SimpleGraph.exists_isPath_walkLength_eq_vertexDist
      asymTri.weight_nonneg (asymTri.connected 1 2)
    rw [← hp]
    exact asymTri_walkLength_ge_one (by decide) p

private theorem asymTri_vd_01 :
    SimpleGraph.vertexDist asymTri.graph asymTri.weight 0 1 = 2 := by
  refine le_antisymm ?_ ?_
  · let p02 : asymTri.graph.Walk 0 2 := SimpleGraph.Adj.toWalk (asymTri_adj (by decide))
    let p21 : asymTri.graph.Walk 2 1 := SimpleGraph.Adj.toWalk (asymTri_adj (by decide))
    refine (SimpleGraph.vertexDist_le asymTri.weight_nonneg (p02.append p21)).trans_eq ?_
    rw [SimpleGraph.walkLength_append, SimpleGraph.walkLength_toWalk,
      SimpleGraph.walkLength_toWalk]
    change asymWeightFun s(0, 2) + asymWeightFun s(2, 1) = 2
    rw [asymWeightFun_of_ne (e := s(0, 2)) (by decide),
      asymWeightFun_of_ne (e := s(2, 1)) (by decide)]
    norm_num
  · obtain ⟨p, -, hp⟩ := SimpleGraph.exists_isPath_walkLength_eq_vertexDist
      asymTri.weight_nonneg (asymTri.connected 0 1)
    rw [← hp]
    cases p with
    | cons hadj q =>
      rename_i w
      rw [SimpleGraph.walkLength_cons]
      have hw_cases : w.val = 0 ∨ w.val = 1 ∨ w.val = 2 := by omega
      rcases hw_cases with hw0 | hw1 | hw2
      · have : w = 0 := Fin.ext hw0
        subst this
        exact absurd rfl hadj.ne
      · have : w = 1 := Fin.ext hw1
        subst this
        have hw : asymTri.weight s(0, 1) = 10 := by
          change asymWeightFun s(0, 1) = 10
          simp [asymWeightFun]
        have hq := SimpleGraph.walkLength_nonneg asymTri.weight asymTri.weight_nonneg q
        linarith
      · have : w = 2 := Fin.ext hw2
        subst this
        have hw : asymTri.weight s(0, 2) = 1 := asymWeightFun_of_ne (e := s(0, 2)) (by decide)
        have hq := asymTri_walkLength_ge_one (by decide : (2 : Fin 3) ≠ 1) q
        linarith

private noncomputable def asymDart01 : asymTri.graph.Dart :=
  ⟨(0, 1), asymTri_adj (by decide)⟩

private theorem asymDart01_weight : asymTri.weight asymDart01.edge = 10 := by
  change asymWeightFun s(0, 1) = 10
  simp [asymWeightFun]

/-- Shortest vertex distance in `asymTri` takes the 2-edge detour `0 → 2 → 1` of length `2 < 10`. -/
example : dist (vertex 0 : MetricGraph asymTri) (vertex 1) = 2 := by
  rw [dist_vertex, asymTri_vd_01]

/-- Midpoint along the heavy edge `(0, 1)` sits at distance `5` from vertex `0` and `6` from
vertex `2`. -/
example : dist (vertex 0 : MetricGraph asymTri) (edgePoint asymDart01 halfPt) = 5 ∧
    dist (vertex 2 : MetricGraph asymTri) (edgePoint asymDart01 halfPt) = 6 := by
  constructor
  · rw [dist_vertex_edgePoint, asymDart01_weight]
    change min (SimpleGraph.vertexDist asymTri.graph asymTri.weight 0 0 + (1 / 2 : ℝ) * 10)
      (SimpleGraph.vertexDist asymTri.graph asymTri.weight 0 1 +
        (1 - (1 / 2 : ℝ)) * 10) = 5
    rw [SimpleGraph.vertexDist_self asymTri.weight_nonneg, asymTri_vd_01]
    norm_num
  · rw [dist_vertex_edgePoint, asymDart01_weight]
    change min (SimpleGraph.vertexDist asymTri.graph asymTri.weight 2 0 + (1 / 2 : ℝ) * 10)
      (SimpleGraph.vertexDist asymTri.graph asymTri.weight 2 1 +
        (1 - (1 / 2 : ℝ)) * 10) = 6
    rw [SimpleGraph.vertexDist_comm 2 0, asymTri_vd_02, SimpleGraph.vertexDist_comm 2 1,
      asymTri_vd_12]
    norm_num

/-- Points at `1/4` and `3/4` along the heavy edge stay at direct distance `5` rather than
detouring `2.5 + 2 + 2.5 = 7` via vertex `2`. -/
example : dist (edgePoint asymDart01 quarterPt : MetricGraph asymTri)
    (edgePoint asymDart01 threeQuarterPt) = 5 := by
  rw [dist_edgePoint_edgePoint_same, asymDart01_weight]
  dsimp only [asymDart01]
  rw [SimpleGraph.vertexDist_self asymTri.weight_nonneg,
    SimpleGraph.vertexDist_self asymTri.weight_nonneg,
    asymTri_vd_01, SimpleGraph.vertexDist_comm 1 0, asymTri_vd_01]
  dsimp only [quarterPt, threeQuarterPt]
  norm_num

/-- Vertex `2` lies on a shortest path from `0` to `1` (realized by a unit-speed geodesic), while
the midpoint of the heavy edge `(0, 1)` does not. -/
example : (vertex 2 : MetricGraph asymTri) ∈ interval (vertex 0) (vertex 1) ∧
    (∃ γ : ℝ → MetricGraph asymTri, IsGeodesic (vertex 0) (vertex 1) γ ∧ γ 1 = vertex 2) ∧
    (edgePoint asymDart01 halfPt : MetricGraph asymTri) ∉ interval (vertex 0) (vertex 1) := by
  have hv02 : dist (vertex 0 : MetricGraph asymTri) (vertex 2) = 1 := by
    rw [dist_vertex, asymTri_vd_02]
  have hv21 : dist (vertex 2 : MetricGraph asymTri) (vertex 1) = 1 := by
    rw [dist_vertex, SimpleGraph.vertexDist_comm, asymTri_vd_12]
  have hv01 : dist (vertex 0 : MetricGraph asymTri) (vertex 1) = 2 := by
    rw [dist_vertex, asymTri_vd_01]
  have hmem : (vertex 2 : MetricGraph asymTri) ∈ interval (vertex 0) (vertex 1) := by
    rw [mem_interval_iff, hv02, hv21, hv01]
    norm_num
  refine ⟨hmem, ?_, ?_⟩
  · obtain ⟨γ, hγ, hγ1⟩ := exists_isGeodesic_through_of_mem_interval hmem
    rw [hv02] at hγ1
    exact ⟨γ, hγ, hγ1⟩
  · rw [mem_interval_iff, dist_vertex_edgePoint, dist_edgePoint_vertex, asymDart01_weight,
      hv01]
    change ¬ min (SimpleGraph.vertexDist asymTri.graph asymTri.weight 0 0 + (1 / 2 : ℝ) * 10)
        (SimpleGraph.vertexDist asymTri.graph asymTri.weight 0 1 + (1 - (1 / 2 : ℝ)) * 10) +
      min ((1 / 2 : ℝ) * 10 + SimpleGraph.vertexDist asymTri.graph asymTri.weight 0 1)
        ((1 - (1 / 2 : ℝ)) * 10 + SimpleGraph.vertexDist asymTri.graph asymTri.weight 1 1) = 2
    rw [SimpleGraph.vertexDist_self asymTri.weight_nonneg,
      SimpleGraph.vertexDist_self asymTri.weight_nonneg, asymTri_vd_01]
    norm_num

/-- `CompactSpace` and `PathConnectedSpace` instances infer cleanly for `MetricGraph asymTri`. -/
example : CompactSpace (MetricGraph asymTri) ∧ PathConnectedSpace (MetricGraph asymTri) :=
  ⟨inferInstance, inferInstance⟩

/-! ### Non-bipartite kink on `C_3`, bipartite equal-length `C_4`, and midpoint subdivision -/

private noncomputable def constTri : SimpleGraph.WeightedGraph (Fin 3) :=
  equalLength (⊤ : SimpleGraph (Fin 3)) top_fin3_connected 2 (by norm_num)

private theorem constTri_adj {u v : Fin 3} (h : u ≠ v) : constTri.graph.Adj u v := h

private theorem top_fin3_dist_01 : (⊤ : SimpleGraph (Fin 3)).dist 0 1 = 1 := by
  have hle : (⊤ : SimpleGraph (Fin 3)).dist 0 1 ≤ 1 :=
    (SimpleGraph.dist_le
      (SimpleGraph.Adj.toWalk (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 0 1))).trans_eq rfl
  have hne : (⊤ : SimpleGraph (Fin 3)).dist 0 1 ≠ 0 := by
    intro h
    have heq := (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h).resolve_right
      (fun hn => hn (top_fin3_connected 0 1))
    exact absurd heq (by decide)
  omega

private theorem top_fin3_dist_02 : (⊤ : SimpleGraph (Fin 3)).dist 0 2 = 1 := by
  have hle : (⊤ : SimpleGraph (Fin 3)).dist 0 2 ≤ 1 :=
    (SimpleGraph.dist_le
      (SimpleGraph.Adj.toWalk (by decide : (⊤ : SimpleGraph (Fin 3)).Adj 0 2))).trans_eq rfl
  have hne : (⊤ : SimpleGraph (Fin 3)).dist 0 2 ≠ 0 := by
    intro h
    have heq := (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h).resolve_right
      (fun hn => hn (top_fin3_connected 0 2))
    exact absurd heq (by decide)
  omega

/-- On the equal-length non-bipartite triangle `constTri` (`ℓ = 2`), the distance from vertex `0`
to the midpoint of edge `(1, 2)` is `3`, strictly above the affine interpolation `2`. -/
example :
    let d12 : constTri.graph.Dart := ⟨(1, 2), constTri_adj (by decide)⟩
    dist (vertex 0 : MetricGraph constTri) (edgePoint d12 halfPt) = 3 ∧
    (1 - (halfPt : ℝ)) * dist (vertex 0 : MetricGraph constTri) (vertex 1) +
      (halfPt : ℝ) * dist (vertex 0 : MetricGraph constTri) (vertex 2) = 2 := by
  intro d12
  have h01 : dist (vertex 0 : MetricGraph constTri) (vertex 1) = 2 := by
    rw [dist_vertex_eq_of_const_weight (ℓ := 2) (by norm_num) (fun _ _ => rfl)]
    change (2 : ℝ) * ((⊤ : SimpleGraph (Fin 3)).dist 0 1 : ℕ) = 2
    rw [top_fin3_dist_01]
    norm_num
  have h02 : dist (vertex 0 : MetricGraph constTri) (vertex 2) = 2 := by
    rw [dist_vertex_eq_of_const_weight (ℓ := 2) (by norm_num) (fun _ _ => rfl)]
    change (2 : ℝ) * ((⊤ : SimpleGraph (Fin 3)).dist 0 2 : ℕ) = 2
    rw [top_fin3_dist_02]
    norm_num
  constructor
  · rw [dist_vertex_edgePoint]
    have hvd01 : SimpleGraph.vertexDist constTri.graph constTri.weight 0 1 = 2 := by
      simpa only [dist_vertex] using h01
    have hvd02 : SimpleGraph.vertexDist constTri.graph constTri.weight 0 2 = 2 := by
      simpa only [dist_vertex] using h02
    have hw : constTri.weight d12.edge = 2 := rfl
    change min (SimpleGraph.vertexDist constTri.graph constTri.weight 0 1 + (1 / 2 : ℝ) * _)
      (SimpleGraph.vertexDist constTri.graph constTri.weight 0 2 + (1 - (1 / 2 : ℝ)) * _) = 3
    rw [hvd01, hvd02, hw]
    norm_num
  · rw [h01, h02]
    change (1 - (1 / 2 : ℝ)) * 2 + (1 / 2 : ℝ) * 2 = 2
    norm_num

private def c4Graph : SimpleGraph (Fin 4) where
  Adj u v := (u.val + 1) % 4 = v.val ∨ (v.val + 1) % 4 = u.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun u h => by fin_cases u <;> simp at h⟩

private theorem c4Graph_connected : c4Graph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact SimpleGraph.Reachable.refl 0
  · exact SimpleGraph.Adj.reachable (Or.inl rfl)
  · exact (SimpleGraph.Adj.reachable (Or.inl rfl : c4Graph.Adj 0 1)).trans
      (SimpleGraph.Adj.reachable (Or.inl rfl : c4Graph.Adj 1 2))
  · exact SimpleGraph.Adj.reachable (Or.inr rfl)

private theorem c4Graph_isBipartite : c4Graph.IsBipartite := by
  refine SimpleGraph.IsBipartiteWith.isBipartite
    (s := { x : Fin 4 | x.val % 2 = 0 }) (t := { x : Fin 4 | x.val % 2 = 1 }) ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro x hx0 hx1
    fin_cases x <;> simp at hx0 hx1
  · intro u v hadj
    fin_cases u <;> fin_cases v <;> simp [c4Graph] at hadj <;> decide

private theorem c4Graph_dist_02 : c4Graph.dist 0 2 = 2 := by
  have hle : c4Graph.dist 0 2 ≤ 2 := by
    have h01 : c4Graph.Adj 0 1 := Or.inl rfl
    have h12 : c4Graph.Adj 1 2 := Or.inl rfl
    exact (c4Graph.dist_le (SimpleGraph.Walk.cons h01 h12.toWalk)).trans_eq rfl
  have hlt : 1 < c4Graph.dist 0 2 := by
    obtain ⟨p, hp⟩ := c4Graph_connected.exists_walk_length_eq_dist 0 2
    rw [← hp]
    cases p with
    | cons h1 q =>
      cases q with
      | nil => exact absurd h1 (by dsimp only [c4Graph]; decide)
      | cons _ _ => simp only [SimpleGraph.Walk.length_cons]; omega
  omega

private theorem c4Graph_dist_03 : c4Graph.dist 0 3 = 1 := by
  have hle : c4Graph.dist 0 3 ≤ 1 :=
    c4Graph.dist_le (SimpleGraph.Adj.toWalk (Or.inr rfl : c4Graph.Adj 0 3))
  have hne : c4Graph.dist 0 3 ≠ 0 := by
    intro h
    have heq := (SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h).resolve_right
      (fun hn => hn (c4Graph_connected 0 3))
    exact absurd heq (by decide)
  omega

/-- On the bipartite equal-length graph `C_4` (`ℓ = 3`), distances from vertex `0` differ by `3`
across edge `2 ~ 3` and interpolate affinely along `(2, 3)` without any subdivision. -/
example :
    let W := equalLength c4Graph c4Graph_connected 3 (by norm_num)
    let d23 : c4Graph.Dart := ⟨(2, 3), Or.inl rfl⟩
    |dist (vertex 0 : MetricGraph W) (vertex 2) - dist (vertex 0 : MetricGraph W) (vertex 3)| = 3 ∧
    dist (vertex 0 : MetricGraph W) (edgePoint d23 halfPt) =
      (1 - (halfPt : ℝ)) * dist (vertex 0 : MetricGraph W) (vertex 2) +
        (halfPt : ℝ) * dist (vertex 0 : MetricGraph W) (vertex 3) ∧
    dist (vertex 0 : MetricGraph W) (edgePoint d23 halfPt) = 9 / 2 := by
  intro W d23
  have hadj : W.graph.Adj 2 3 := Or.inl rfl
  refine ⟨bipartite_dist_vertex_adj_diff c4Graph_isBipartite (by norm_num)
      (fun _ _ => rfl) 0 hadj,
    bipartite_equalLength_dist_edgePoint_affine c4Graph_isBipartite c4Graph_connected
      (by norm_num) 0 d23 halfPt, ?_⟩
  rw [bipartite_equalLength_dist_edgePoint_affine c4Graph_isBipartite c4Graph_connected
    (by norm_num) 0 d23 halfPt,
    dist_vertex_eq_of_const_weight (ℓ := 3) (by norm_num) (fun _ _ => rfl),
    dist_vertex_eq_of_const_weight (ℓ := 3) (by norm_num) (fun _ _ => rfl)]
  change (1 - (halfPt : ℝ)) * (3 * (c4Graph.dist 0 2 : ℕ)) +
    (halfPt : ℝ) * (3 * (c4Graph.dist 0 3 : ℕ)) = 9 / 2
  rw [c4Graph_dist_02, c4Graph_dist_03]
  change (1 - (1 / 2 : ℝ)) * (3 * (2 : ℕ)) + (1 / 2 : ℝ) * (3 * (1 : ℕ)) = 9 / 2
  norm_num

/-- Midpoint subdivision turns the non-bipartite triangle `constTri` (`ℓ = 2`) into a bipartite
graph of uniform edge weight `1` where distances from every subdivided vertex are affine on every
subdivided edge. -/
example (t₀ : { z : MetricGraph constTri // z ∈ midpointPoints constTri })
    (d' : (midpointSubdivision constTri).graph.Dart) (s : unitInterval) :
    (midpointSubdivision constTri).graph.IsBipartite ∧
    (midpointSubdivision constTri).weight d'.edge = 1 ∧
    dist (vertex t₀ : MetricGraph (midpointSubdivision constTri)) (edgePoint d' s) =
      (1 - (s : ℝ)) *
          dist (vertex t₀ : MetricGraph (midpointSubdivision constTri)) (vertex d'.fst) +
        (s : ℝ) *
          dist (vertex t₀ : MetricGraph (midpointSubdivision constTri)) (vertex d'.snd) := by
  refine ⟨midpointSubdivision_isBipartite constTri, ?_,
    midpointSubdivision_dist_edgePoint_affine (ℓ := 2) (by norm_num) (fun _ _ => rfl) t₀ d' s⟩
  have hw := midpointSubdivision_weight_eq (W := constTri) (ℓ := 2) (fun _ _ => rfl) d'.edge_mem
  linarith

/-! ### Breakpoint subdivisions and 3-segment Euclidean straight-edge realizations -/

private theorem nat_card_fin3_edges_le : Nat.card asymTri.graph.edgeSet ≤ 3 := by
  classical
  let f : asymTri.graph.edgeSet → Fin 3 := fun e =>
    if e.1 = s(0, 1) then 0 else if e.1 = s(0, 2) then 1 else 2
  have hinj : Function.Injective f := by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ heq
    have h1 : e₁ = s(0, 1) ∨ e₁ = s(0, 2) ∨ e₁ = s(1, 2) := by
      induction e₁ using Sym2.ind with
      | _ a b =>
        fin_cases a <;> fin_cases b <;>
          (simp only [asymTri, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at he₁
           first | exact False.elim (he₁ rfl) | decide)
    have h2 : e₂ = s(0, 1) ∨ e₂ = s(0, 2) ∨ e₂ = s(1, 2) := by
      induction e₂ using Sym2.ind with
      | _ a b =>
        fin_cases a <;> fin_cases b <;>
          (simp only [asymTri, SimpleGraph.mem_edgeSet, SimpleGraph.top_adj] at he₂
           first | exact False.elim (he₂ rfl) | decide)
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      dsimp only [f] at heq <;> simp_all
  rw [← Fintype.card_eq_nat_card]
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hinj

open Classical in
/-- Breakpoint subdivision for `vertex 0` in `asymTri` adds at most `9` interior points and
makes `dist (vertex 0)` affine on every subdivided edge. -/
example :
    let B := pointBreakpoints asymTri (vertex 0)
    (B \ Finset.univ.image vertex).card ≤ 9 ∧
    ∀ (d' : (subdivide asymTri B (vertex_mem_pointBreakpoints asymTri (vertex 0))).graph.Dart)
      (τ : unitInterval),
      dist (vertex 0 : MetricGraph asymTri)
          (subdivideEquiv (vertex_mem_pointBreakpoints asymTri (vertex 0)) (edgePoint d' τ)) =
        (1 - (τ : ℝ)) * dist (vertex 0 : MetricGraph asymTri)
            (subdivideEquiv (vertex_mem_pointBreakpoints asymTri (vertex 0)) (vertex d'.fst)) +
          (τ : ℝ) * dist (vertex 0 : MetricGraph asymTri)
            (subdivideEquiv (vertex_mem_pointBreakpoints asymTri (vertex 0)) (vertex d'.snd)) := by
  intro B
  refine ⟨?_, ?_⟩
  · have hle : (B \ Finset.univ.image vertex).card ≤ 3 * Nat.card asymTri.graph.edgeSet := by
      convert pointBreakpoints_sdiff_card_le asymTri (vertex 0)
    have hc : Nat.card asymTri.graph.edgeSet ≤ 3 := nat_card_fin3_edges_le
    omega
  · intro d' τ
    exact dist_subdivide_edgePoint_affine (vertex_mem_pointBreakpoints asymTri (vertex 0))
      Finset.Subset.rfl d' τ

private theorem asymTri_rational : ∀ e ∈ asymTri.graph.edgeSet, ∃ q : ℚ, asymTri.weight e = q := by
  intro e _
  change ∃ q : ℚ, asymWeightFun e = q
  dsimp only [asymWeightFun]
  split_ifs
  · exact ⟨10, by norm_num⟩
  · exact ⟨1, by norm_num⟩

open Classical in
/-- The 3-segment Euclidean straight-edge realization of `asymTri` adds at most `6` interior
subdivision vertices, gives a closed embedding with rational vertex coordinates, and induces a
globally isometric weighted graph. -/
example (x y : MetricGraph (realizationEuclideanGraph asymTri)) :
    (realizationPoints asymTri \ Finset.univ.image vertex).card ≤ 6 ∧
    Topology.IsClosedEmbedding (realizationFromGraph asymTri) ∧
    dist (realizationEuclideanEquiv asymTri x) (realizationEuclideanEquiv asymTri y) =
      dist x y ∧
    (∀ (z : { p : MetricGraph asymTri // p ∈ realizationPoints asymTri })
      (i : Fin (Nat.card asymTri.graph.edgeSet + 1)),
      ∃ q : ℚ, realizationMap asymTri (vertex z) i = q) := by
  refine ⟨?_, realizationFromGraph_isClosedEmbedding asymTri,
    (realizationEuclideanEquiv asymTri).isometry.dist_eq x y, ?_⟩
  · have hle :
        (realizationPoints asymTri \ Finset.univ.image vertex).card ≤
          2 * Nat.card asymTri.graph.edgeSet := by
      convert realizationPoints_sdiff_card_le asymTri
    have hc : Nat.card asymTri.graph.edgeSet ≤ 3 := nat_card_fin3_edges_le
    omega
  · exact fun z i => realizationMap_vertex_rational asymTri asymTri_rational z i

/-- Direct client of `dist_map_le_of_edgePoint_dist_le`: checking non-expansiveness along each
dart suffices to deduce global `1`-Lipschitzness on `MetricGraph asymTri`. -/
example (p q : MetricGraph asymTri) :
    dist (dist (vertex 0 : MetricGraph asymTri) p) (dist (vertex 0 : MetricGraph asymTri) q) ≤
      dist p q := by
  refine dist_map_le_of_edgePoint_dist_le (fun x => dist (vertex 0 : MetricGraph asymTri) x)
    (fun d s t => ?_) p q
  rw [Real.dist_eq, dist_comm (vertex 0 : MetricGraph asymTri) (edgePoint d s),
    dist_comm (vertex 0 : MetricGraph asymTri) (edgePoint d t)]
  exact (abs_dist_sub_le (edgePoint d s) (edgePoint d t) (vertex 0)).trans
    ((dist_edgePoint_self_le d s t).trans_eq (mul_comm _ _))

end CslibFrontierTests.MetricGraph
