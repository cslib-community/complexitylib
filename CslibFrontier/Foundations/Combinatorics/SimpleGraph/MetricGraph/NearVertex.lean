/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Basic
import Mathlib.Tactic.Linarith

/-!
# Points near a vertex of a metric graph

A point `p` of `MetricGraph W` that is closer to a vertex `v` than every other vertex is, is either
`v` itself or an interior point of an edge at `v`, and its distance from `v` is its offset along
that edge. The hypotheses only compare `dist (vertex v) p` with the distances from `v` to the other
vertices, so they follow both from a uniform lower bound on the distances between distinct vertices
(`exists_pos_le_dist_vertex`) and from a bound below every edge weight.

## Main results

* `SimpleGraph.MetricGraph.fst_eq_or_snd_eq_of_dist_vertex_edgePoint_lt`: an edge point closer to
  `v` than every other vertex lies on an edge at `v`.
* `SimpleGraph.MetricGraph.dist_vertex_edgePoint_of_fst_eq`,
  `SimpleGraph.MetricGraph.dist_vertex_edgePoint_of_snd_eq`: the distance from an endpoint of an
  edge to a point on it, when that point is closer than the other endpoint.
* `SimpleGraph.MetricGraph.eq_vertex_or_edgePoint_of_dist_vertex_lt`: a point closer to `v` than
  every other vertex is `v` or an interior point of a dart out of `v`, at distance its offset.
-/

public section

namespace SimpleGraph.MetricGraph

variable {V : Type*} {W : WeightedGraph V} [Finite V]

/-- An edge point closer to `v` than every other vertex lies on an edge at `v`. -/
theorem fst_eq_or_snd_eq_of_dist_vertex_edgePoint_lt {v : V} {d : W.graph.Dart}
    {t : unitInterval}
    (h : ∀ u, u ≠ v → dist (vertex v : MetricGraph W) (edgePoint d t) <
      dist (vertex v : MetricGraph W) (vertex u)) :
    d.fst = v ∨ d.snd = v := by
  by_contra hne
  push Not at hne
  have h₁ := h d.fst hne.1
  have h₂ := h d.snd hne.2
  rw [dist_vertex, dist_vertex_edgePoint] at h₁ h₂
  rcases min_choice (vertexDist W.graph W.weight v d.fst + (t : ℝ) * W.weight d.edge)
      (vertexDist W.graph W.weight v d.snd + (1 - (t : ℝ)) * W.weight d.edge) with hm | hm <;>
    rw [hm] at h₁ h₂
  · linarith [mul_nonneg t.2.1 (W.dart_weight_nonneg d)]
  · linarith [mul_nonneg (sub_nonneg.mpr t.2.2) (W.dart_weight_nonneg d)]

/-- A point on a dart out of `v` that is closer to `v` than the other endpoint is at distance its
offset along the dart. -/
theorem dist_vertex_edgePoint_of_fst_eq {v : V} {d : W.graph.Dart} {t : unitInterval}
    (hfst : d.fst = v)
    (h : dist (vertex v : MetricGraph W) (edgePoint d t) <
      dist (vertex v : MetricGraph W) (vertex d.snd)) :
    dist (vertex v : MetricGraph W) (edgePoint d t) = (t : ℝ) * W.weight d.edge := by
  rw [dist_vertex] at h
  rw [dist_vertex_edgePoint, hfst, vertexDist_self W.weight_nonneg, zero_add] at h ⊢
  refine min_eq_left (le_of_not_gt fun hlt => ?_)
  rw [min_eq_right hlt.le] at h
  linarith [mul_nonneg (sub_nonneg.mpr t.2.2) (W.dart_weight_nonneg d)]

/-- A point on a dart into `v` that is closer to `v` than the other endpoint is at distance its
offset from the end of the dart. -/
theorem dist_vertex_edgePoint_of_snd_eq {v : V} {d : W.graph.Dart} {t : unitInterval}
    (hsnd : d.snd = v)
    (h : dist (vertex v : MetricGraph W) (edgePoint d t) <
      dist (vertex v : MetricGraph W) (vertex d.fst)) :
    dist (vertex v : MetricGraph W) (edgePoint d t) = (1 - (t : ℝ)) * W.weight d.edge := by
  rw [← edgePoint_symm d t] at h ⊢
  rw [dist_vertex_edgePoint_of_fst_eq (d := d.symm) hsnd h, unitInterval.coe_symm_eq,
    Dart.edge_symm]

/-- A point closer to `v` than every other vertex is `v` itself or an interior point of a dart out
of `v`, at distance its offset along the dart. -/
theorem eq_vertex_or_edgePoint_of_dist_vertex_lt {v : V} {p : MetricGraph W}
    (h : ∀ u, u ≠ v →
      dist (vertex v : MetricGraph W) p < dist (vertex v : MetricGraph W) (vertex u)) :
    p = vertex v ∨ ∃ (d : W.graph.Dart) (t : unitInterval),
      d.fst = v ∧ 0 < (t : ℝ) ∧ (t : ℝ) < 1 ∧ p = edgePoint d t ∧
        dist (vertex v : MetricGraph W) p = (t : ℝ) * W.weight d.edge := by
  induction p using ind with
  | vertex u =>
    by_cases huv : u = v
    · left; rw [huv]
    · exact absurd (h u huv) (lt_irrefl _)
  | edgePoint d t ht0 ht1 =>
    right
    rcases fst_eq_or_snd_eq_of_dist_vertex_edgePoint_lt h with hfst | hsnd
    · exact ⟨d, t, hfst, ht0, ht1, rfl,
        dist_vertex_edgePoint_of_fst_eq hfst (h _ fun h' => d.adj.ne (hfst.trans h'.symm))⟩
    · rw [← edgePoint_symm d t] at h ⊢
      exact ⟨d.symm, unitInterval.symm t, hsnd, sub_pos.mpr ht1, sub_lt_self 1 ht0, rfl,
        dist_vertex_edgePoint_of_fst_eq (d := d.symm) hsnd
          (h _ fun h' => d.adj.ne (h'.trans hsnd.symm))⟩

end SimpleGraph.MetricGraph
