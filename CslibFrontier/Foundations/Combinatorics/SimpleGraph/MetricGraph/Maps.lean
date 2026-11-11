/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/MetricGraph/Maps.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.MetricGraph.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Non-expansive maps out of metric graphs

A map `f : MetricGraph W → α` from a finite metric graph into a pseudometric space is globally
`1`-Lipschitz as soon as it is `1`-Lipschitz along every individual edge segment.

## Main results

* `SimpleGraph.MetricGraph.dist_map_le_of_edgePoint_dist_le`:
  `dist (f p) (f q) ≤ dist p q` whenever
  `dist (f (edgePoint d s)) (f (edgePoint d t)) ≤ |(s : ℝ) - t| * W.weight d.edge` on every dart.
-/

public section

open scoped unitInterval

namespace SimpleGraph

namespace MetricGraph

variable {V : Type*} {α : Type*} [PseudoMetricSpace α]

/-- Any map from a finite metric graph into a pseudometric space that is `1`-Lipschitz along
every edge segment is globally `1`-Lipschitz (`dist (f p) (f q) ≤ dist p q`). -/
theorem dist_map_le_of_edgePoint_dist_le [Finite V] {W : WeightedGraph V}
    (f : MetricGraph W → α)
    (hdart : ∀ (d : W.graph.Dart) (s t : unitInterval),
      dist (f (edgePoint d s)) (f (edgePoint d t)) ≤ |(s : ℝ) - t| * W.weight d.edge)
    (p q : MetricGraph W) :
    dist (f p) (f q) ≤ dist p q := by
  have hend : ∀ (d : W.graph.Dart) (r : unitInterval),
      dist (f (edgePoint d r)) (f (vertex d.fst)) ≤ (r : ℝ) * W.weight d.edge ∧
      dist (f (edgePoint d r)) (f (vertex d.snd)) ≤ (1 - (r : ℝ)) * W.weight d.edge := by
    intro d r
    constructor
    · rw [← edgePoint_zero d]
      refine (hdart d r 0).trans_eq ?_
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, abs_of_nonneg r.2.1]
    · rw [← edgePoint_one d]
      refine (hdart d r 1).trans_eq ?_
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, abs_sub_comm,
        abs_of_nonneg (unitInterval.one_sub_nonneg r)]
  have hwalk : ∀ {u v : V} (w : W.graph.Walk u v),
      dist (f (vertex u)) (f (vertex v)) ≤ walkLength W.weight w := by
    intro u v w
    induction w with
    | nil =>
      rw [dist_self]
      simp only [walkLength_nil, le_refl]
    | @cons u v x hadj w' ih =>
      let d : W.graph.Dart := ⟨(u, v), hadj⟩
      have hstep : dist (f (vertex u)) (f (vertex v)) ≤ W.weight s(u, v) := by
        rw [← edgePoint_zero d, ← edgePoint_one d]
        refine (hdart d 0 1).trans_eq ?_
        rw [show ((0 : unitInterval) : ℝ) = 0 from rfl,
          show ((1 : unitInterval) : ℝ) = 1 from rfl, zero_sub, abs_neg, abs_one, one_mul]
        rfl
      rw [walkLength_cons]
      exact (dist_triangle _ (f (vertex v)) _).trans (add_le_add hstep ih)
  have hvertex : ∀ u v : V,
      dist (f (vertex u)) (f (vertex v)) ≤ dist (vertex u : MetricGraph W) (vertex v) := by
    intro u v
    rw [dist_vertex]
    obtain ⟨w, -, hw⟩ := exists_isPath_walkLength_eq_vertexDist W.weight_nonneg (W.connected u v)
    rw [← hw]
    exact hwalk w
  have hvia : ∀ (d₁ : W.graph.Dart) (r₁ : unitInterval)
      (d₂ : W.graph.Dart) (r₂ : unitInterval),
      dist (f (edgePoint d₁ r₁)) (f (edgePoint d₂ r₂)) ≤
        min
          (min ((r₁ : ℝ) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.fst d₂.fst +
                  (r₂ : ℝ) * W.weight d₂.edge)
               ((r₁ : ℝ) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.fst d₂.snd +
                  (1 - (r₂ : ℝ)) * W.weight d₂.edge))
          (min ((1 - (r₁ : ℝ)) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.snd d₂.fst +
                  (r₂ : ℝ) * W.weight d₂.edge)
               ((1 - (r₁ : ℝ)) * W.weight d₁.edge + vertexDist W.graph W.weight d₁.snd d₂.snd +
                  (1 - (r₂ : ℝ)) * W.weight d₂.edge)) := by
    intro d₁ r₁ d₂ r₂
    obtain ⟨h10, h11⟩ := hend d₁ r₁
    obtain ⟨h20, h21⟩ := hend d₂ r₂
    have step : ∀ a b : V,
        dist (f (edgePoint d₁ r₁)) (f (edgePoint d₂ r₂)) ≤
          dist (f (edgePoint d₁ r₁)) (f (vertex a)) +
          vertexDist W.graph W.weight a b +
          dist (f (edgePoint d₂ r₂)) (f (vertex b)) := by
      intro a b
      have hv := (hvertex a b).trans_eq (dist_vertex _ _)
      have htri := dist_triangle4 (f (edgePoint d₁ r₁))
        (f (vertex a)) (f (vertex b)) (f (edgePoint d₂ r₂))
      rw [dist_comm (f (vertex b))] at htri
      linarith
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_) <;>
      linarith [step d₁.fst d₂.fst, step d₁.fst d₂.snd,
        step d₁.snd d₂.fst, step d₁.snd d₂.snd]
  induction p using ind_simple with
  | vertex x =>
    induction q using ind_simple with
    | vertex y => exact hvertex x y
    | edgePoint d r =>
      rw [dist_vertex_edgePoint]
      obtain ⟨h0, h1⟩ := hend d r
      rw [dist_comm] at h0 h1
      have hv0 := (hvertex x d.fst).trans_eq (dist_vertex _ _)
      have hv1 := (hvertex x d.snd).trans_eq (dist_vertex _ _)
      refine le_min ?_ ?_ <;> linarith [
        dist_triangle (f (vertex x)) (f (vertex d.fst)) (f (edgePoint d r)),
        dist_triangle (f (vertex x)) (f (vertex d.snd)) (f (edgePoint d r))]
  | edgePoint d₁ r₁ =>
    induction q using ind_simple with
    | vertex y =>
      rw [dist_edgePoint_vertex]
      obtain ⟨h0, h1⟩ := hend d₁ r₁
      have hv0 := (hvertex d₁.fst y).trans_eq (dist_vertex _ _)
      have hv1 := (hvertex d₁.snd y).trans_eq (dist_vertex _ _)
      refine le_min ?_ ?_ <;> linarith [
        dist_triangle (f (edgePoint d₁ r₁)) (f (vertex d₁.fst)) (f (vertex y)),
        dist_triangle (f (edgePoint d₁ r₁)) (f (vertex d₁.snd)) (f (vertex y))]
    | edgePoint d₂ r₂ =>
      by_cases he : d₁.edge = d₂.edge
      · rcases (dart_edge_eq_iff d₁ d₂).mp he with rfl | hsym
        · rw [dist_edgePoint_edgePoint_same]
          exact le_min (hdart d₁ r₁ r₂) (hvia d₁ r₁ d₁ r₂)
        · subst hsym
          rw [← edgePoint_symm d₂ r₂, dist_edgePoint_edgePoint_same]
          exact le_min (hdart d₂.symm r₁ (unitInterval.symm r₂))
            (hvia d₂.symm r₁ d₂.symm (unitInterval.symm r₂))
      · rw [dist_edgePoint_edgePoint_of_edge_ne he]
        exact hvia d₁ r₁ d₂ r₂

end MetricGraph

end SimpleGraph
