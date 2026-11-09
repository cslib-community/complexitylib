/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Restriction
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeContraction
public import CslibFrontier.Foundations.Geometry.Polygonal.Join
public import CslibFrontier.Foundations.Geometry.Polygonal.Segment
import Mathlib.Data.List.GetD

/-!
# Actual routes for restoring a contracted nonloop edge

Each retained edge keeps its exterior route and receives a new straight segment at
each end incident to either restored endpoint. The two ends are treated independently:
an old source edge between the endpoints is reopened from both ends of its target loop.
The selected last edge is an actual one-segment connector. This module constructs the
route data and proves endpoints; embedding and rotation order require the local split.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

/-- The retained edge occurrence after contracting a last nonloop edge. -/
@[expose] def contractedIndex (G : Graph) (u v : ℕ) :
    Fin G.2.length ≃ Fin (contractLastEdgeGraph G u v).2.length :=
  finCongr (by simp [contractLastEdgeGraph, Graph.relabel])

/-- Both endpoint occurrences retain their tag and undergo the prescribed name update. -/
theorem vertex_contractedIndex (G : Graph) (u v : ℕ) (i : Fin G.2.length) (b : Bool) :
    Dart.vertex (G := contractLastEdgeGraph G u v) (contractedIndex G u v i, b) =
      Function.update id u v (Dart.vertex (G := G) (i, b)) :=
  Dart.vertex_relabelEquiv G (Function.update id u v) (i, b)

/-- Coordinates of the two restored names; all other names retain their old coordinates. -/
@[expose] def restoredVertex {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (a b : ℂ) (w : ℕ) : ℂ :=
  if w = u then a else if w = v then b else D.vertex w

/-- Attach a first spoke precisely when its original source end is restored. -/
@[expose] noncomputable def restoreFirst (u v w : ℕ) (a b : ℂ) (p : Route) : Route :=
  if w = u then Route.prepend a p else if w = v then Route.prepend b p else p

/-- Attach a last spoke independently of the first end, including for target loops. -/
@[expose] noncomputable def restoreLast (u v w : ℕ) (a b : ℂ) (p : Route) : Route :=
  if w = u then p.append a else if w = v then p.append b else p

/-- Number of new segments attached at one original endpoint occurrence. -/
@[expose] def attachmentCount (u v w : ℕ) : ℕ := if w = u ∨ w = v then 1 else 0

/-- A first restoration adds exactly one segment at an affected endpoint. -/
theorem segments_restoreFirst (u v w : ℕ) (a b : ℂ) (p : Route) :
    (restoreFirst u v w a b p).segments = p.segments + attachmentCount u v w := by
  unfold restoreFirst attachmentCount
  split_ifs <;> simp_all

/-- A last restoration adds exactly one segment at an affected endpoint. -/
theorem segments_restoreLast (u v w : ℕ) (a b : ℂ) (p : Route) :
    (restoreLast u v w a b p).segments = p.segments + attachmentCount u v w := by
  unfold restoreLast attachmentCount
  split_ifs <;> simp_all

/-- A restored endpoint remains strictly inside the replacement ball. -/
theorem restoredVertex_mem_ball {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    {ρ : ℝ} {a b : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ)
    (hb : b ∈ Metric.ball (D.vertex v) ρ) (w : ℕ) (hw : w = u ∨ w = v) :
    D.restoredVertex a b w ∈ Metric.ball (D.vertex v) ρ := by
  rcases hw with rfl | rfl
  · simpa only [restoredVertex, ↓reduceIte] using ha
  · simpa only [restoredVertex, ite_eq_right huv.symm, ↓reduceIte] using hb

/-- At an affected endpoint, first restoration is exactly one prepend. -/
theorem restoreFirst_eq_prepend {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    (w : ℕ) (hw : w = u ∨ w = v) (a b : ℂ) (p : Route) :
    restoreFirst u v w a b p = Route.prepend (D.restoredVertex a b w) p := by
  rcases hw with rfl | rfl
  · simp only [restoreFirst, restoredVertex, ↓reduceIte]
  · simp only [restoreFirst, restoredVertex, ite_eq_right huv.symm, ↓reduceIte]

/-- At an affected endpoint, last restoration is exactly one append. -/
theorem restoreLast_eq_append {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    (w : ℕ) (hw : w = u ∨ w = v) (a b : ℂ) (p : Route) :
    restoreLast u v w a b p = p.append (D.restoredVertex a b w) := by
  rcases hw with rfl | rfl
  · simp only [restoreLast, restoredVertex, ↓reduceIte]
  · simp only [restoreLast, restoredVertex, ite_eq_right huv.symm, ↓reduceIte]

/-- An unaffected first endpoint retains the entire route data. -/
theorem restoreFirst_eq_self (u v w : ℕ) (hw : ¬(w = u ∨ w = v)) (a b : ℂ) (p : Route) :
    restoreFirst u v w a b p = p := by
  simp only [restoreFirst, ite_eq_right (fun h => hw (Or.inl h)),
    ite_eq_right (fun h => hw (Or.inr h))]

/-- An unaffected last endpoint retains the entire route data. -/
theorem restoreLast_eq_self (u v w : ℕ) (hw : ¬(w = u ∨ w = v)) (a b : ℂ) (p : Route) :
    restoreLast u v w a b p = p := by
  simp only [restoreLast, ite_eq_right (fun h => hw (Or.inl h)),
    ite_eq_right (fun h => hw (Or.inr h))]

/-- Exterior retained route with its two original source endpoint occurrences restored. -/
@[expose] noncomputable def restoredRoute {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (ρ : ℝ) (a b : ℂ)
    (e : Fin G.2.length) : Route :=
  restoreLast u v (Dart.vertex (e, true)) a b
    (restoreFirst u v (Dart.vertex (e, false)) a b
      (D.outsideRoute v ρ (contractedIndex G u v e)))

/-- The two restored end occurrences contribute their new segments independently. -/
theorem segments_restoredRoute {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (ρ : ℝ) (a b : ℂ)
    (e : Fin G.2.length) :
    (D.restoredRoute ρ a b e).segments =
      (D.outsideRoute v ρ (contractedIndex G u v e)).segments +
        attachmentCount u v (Dart.vertex (e, false)) +
        attachmentCount u v (Dart.vertex (e, true)) := by
  rw [restoredRoute, segments_restoreLast, segments_restoreFirst]

/-- A first attachment sets its start and retains its finish. -/
theorem endpoint_restoreFirst (u v w : ℕ) (a b : ℂ) (p : Route) (side : Bool) :
    (restoreFirst u v w a b p).endpoint side =
      if side then p.finish else if w = u then a else if w = v then b else p.start := by
  unfold restoreFirst
  by_cases hu : w = u
  · rw [ite_eq_left hu]
    simpa only [hu, ↓reduceIte] using Route.endpoint_prepend a p side
  · rw [ite_eq_right hu]
    by_cases hv : w = v
    · rw [ite_eq_left hv]
      simpa only [ite_eq_right hu, ite_eq_left hv] using Route.endpoint_prepend b p side
    · rw [ite_eq_right hv]
      simp only [hu, hv, ↓reduceIte, Route.endpoint]

/-- A last attachment retains its start and sets its finish. -/
theorem endpoint_restoreLast (u v w : ℕ) (a b : ℂ) (p : Route) (side : Bool) :
    (restoreLast u v w a b p).endpoint side =
      if side then (if w = u then a else if w = v then b else p.finish) else p.start := by
  unfold restoreLast
  by_cases hu : w = u
  · rw [ite_eq_left hu]
    simpa only [hu, ↓reduceIte] using Route.endpoint_append p a side
  · rw [ite_eq_right hu]
    by_cases hv : w = v
    · rw [ite_eq_left hv]
      simpa only [ite_eq_right hu, ite_eq_left hv] using Route.endpoint_append p b side
    · rw [ite_eq_right hv]
      simp only [hu, hv, ↓reduceIte, Route.endpoint]

/-- The restored exterior piece has exactly the two named source endpoints. -/
theorem endpoint_restoredRoute {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (ρ : ℝ) (a b : ℂ)
    (e : Fin G.2.length) (side : Bool) :
    (D.restoredRoute ρ a b e).endpoint side = D.restoredVertex a b (Dart.vertex (e, side)) := by
  have hfirst (p : Route) : (restoreFirst u v (Dart.vertex (e, false)) a b p).start =
      if Dart.vertex (e, false) = u then a else
        if Dart.vertex (e, false) = v then b else p.start :=
    endpoint_restoreFirst u v (Dart.vertex (e, false)) a b p false
  have hlast (p : Route) : (restoreFirst u v (Dart.vertex (e, false)) a b p).finish =
      p.finish := endpoint_restoreFirst u v (Dart.vertex (e, false)) a b p true
  have houtside (side : Bool) := D.endpoint_outsideRoute v ρ (contractedIndex G u v e) side
  simp only [vertex_contractedIndex] at houtside
  cases side
  · rw [restoredRoute, endpoint_restoreLast]
    change (restoreFirst u v (Dart.vertex (e, false)) a b
      (D.outsideRoute v ρ (contractedIndex G u v e))).start = _
    rw [hfirst]
    by_cases hu : Dart.vertex (e, false) = u
    · simp [hu, restoredVertex]
    · by_cases hv : Dart.vertex (e, false) = v
      · simp [hv, restoredVertex]
      · have h := houtside false
        simp only [Function.update_of_ne hu, id_eq, ite_eq_right hv, Route.endpoint,
          Bool.false_eq_true, ↓reduceIte] at h
        simpa only [restoredVertex, ite_eq_right hu, ite_eq_right hv] using h
  · rw [restoredRoute, endpoint_restoreLast]
    simp only [↓reduceIte, hlast]
    by_cases hu : Dart.vertex (e, true) = u
    · simp [hu, restoredVertex]
    · by_cases hv : Dart.vertex (e, true) = v
      · simp [hv, restoredVertex]
      · have h := houtside true
        simp only [Function.update_of_ne hu, id_eq, ite_eq_right hv, Route.endpoint,
          ↓reduceIte] at h
        simpa only [restoredVertex, ite_eq_right hu, ite_eq_right hv] using h

/-- Restore the actual source graph's route data. Retained edge indices use their old
exterior pieces; the last selected edge is the straight connector from `a` to `b`.
This constructor does not assert nonintersection or clockwise realization. -/
@[expose] noncomputable def restoration {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    (ρ : ℝ) (a b : ℂ) : PolygonalDrawing (lastEdgeGraph G u v) where
  vertex := D.restoredVertex a b
  route e := if h : e.val < G.2.length then D.restoredRoute ρ a b ⟨e.val, h⟩
    else Route.line a b
  endpoint_eq e side := by
    split_ifs with hi
    · rw [D.endpoint_restoredRoute]
      congr 1
      have he : (e, side) = retainedLastEdgeDart G u v (⟨e.val, hi⟩, side) := by
        apply Prod.ext
        · apply Fin.ext
          rfl
        · rfl
      rw [he, vertex_retainedLastEdgeDart]
    · have hlast : e.val = G.2.length := by
        have he := e.isLt
        simp only [lastEdgeGraph, List.length_append, List.length_singleton] at he
        omega
      have he : (e, side) = lastEdgeDart G u v side := by
        apply Prod.ext
        · apply Fin.ext
          cases side <;> exact hlast
        · cases side <;> rfl
      rw [he, vertex_lastEdgeDart]
      cases side <;> simp [Route.endpoint, restoredVertex, huv.symm]

end Cslib.Complexity.Graph.PolygonalDrawing
