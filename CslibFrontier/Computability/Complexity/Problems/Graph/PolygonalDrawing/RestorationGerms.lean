/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Restoration
public import CslibFrontier.Foundations.Geometry.Polygonal.CutGerms

/-!
# Literal outgoing germs of restored routes

Affected ends point from the corresponding new center to their own cut port. Unaffected
ends retain their old argument, including when cutting the opposite end changes the
length of a one-segment route. The selected edge keeps its ordered connector direction.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

private theorem germ_restoreLast_false (u v w : ℕ) (a b : ℂ) (p : Route) :
    (restoreLast u v w a b p).germ false = p.germ false := by
  unfold restoreLast
  split_ifs <;> simp only [Route.germ_append, Bool.false_eq_true, ↓reduceIte]

private theorem germ_restoreFirst_true (u v w : ℕ) (a b : ℂ) (p : Route) :
    (restoreFirst u v w a b p).germ true = p.germ true := by
  unfold restoreFirst
  split_ifs <;> simp only [Route.germ_prepend, ↓reduceIte]

/-- Each restored incident end has its own actual straight spoke as outgoing germ. -/
theorem germ_restoredRoute_active {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    (ρ : ℝ) (a b : ℂ) (e : Fin G.2.length) (side : Bool)
    (hactive : Dart.vertex (G := G) (e, side) = u ∨ Dart.vertex (e, side) = v) :
    (D.restoredRoute ρ a b e).germ side = D.cutPort ρ (contractedIndex G u v e, side) -
      D.restoredVertex a b (Dart.vertex (G := G) (e, side)) := by
  have htarget : Dart.vertex (contractedIndex G u v e, side) = v := by
    apply (contractionLift_vertex_eq_iff G u v _).mpr
    simpa only [contractionLift_vertex_contractedIndex] using hactive
  have hport := D.endpoint_outsideRoute v ρ (contractedIndex G u v e) side
  rw [ite_eq_left htarget] at hport
  cases side
  · rw [restoredRoute, germ_restoreLast_false, D.restoreFirst_eq_prepend huv _ hactive,
      Route.germ_prepend]
    simpa only [Route.endpoint, Bool.false_eq_true, ↓reduceIte] using congrArg
      (fun z => z - D.restoredVertex a b (Dart.vertex (G := G) (e, false))) hport
  · rw [restoredRoute, D.restoreLast_eq_append huv _ hactive, Route.germ_append]
    simp only [↓reduceIte]
    have hfinish := endpoint_restoreFirst u v (Dart.vertex (G := G) (e, false)) a b
      (D.outsideRoute v ρ (contractedIndex G u v e)) true
    simp only [Route.endpoint, ↓reduceIte] at hfinish hport
    rw [hfinish, hport]

/-- An unaffected end retains the outgoing germ of its exterior piece. -/
theorem germ_restoredRoute_inactive {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (ρ : ℝ) (a b : ℂ)
    (e : Fin G.2.length) (side : Bool)
    (hinactive : ¬(Dart.vertex (G := G) (e, side) = u ∨ Dart.vertex (e, side) = v)) :
    (D.restoredRoute ρ a b e).germ side =
      (D.outsideRoute v ρ (contractedIndex G u v e)).germ side := by
  cases side
  · rw [restoredRoute, germ_restoreLast_false, restoreFirst_eq_self _ _ _ hinactive]
  · rw [restoredRoute, restoreLast_eq_self _ _ _ hinactive, germ_restoreFirst_true]

/-- Every exterior cut preserves the literal outgoing direction of the old actual route. -/
theorem IsEmbedding.arg_germ_outsideRoute {H : Graph} {D : PolygonalDrawing H}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart H, d.vertex = v → 3 * ρ < ‖D.germ d‖)
    (e : Fin H.2.length) (side : Bool) :
    ((D.outsideRoute v ρ e).germ side).arg = (D.germ (e, side)).arg := by
  have h₀ := hD.restrictionTime_mem v hρ hlen (e, false)
  have h₁ := hD.restrictionTime_mem v hρ hlen (e, true)
  exact (D.route e).arg_germ_cutEnds h₀.1 h₁.1 (by linarith [h₀.2, h₁.2]) side

/-- A retained actual source dart has exactly its attached route's outgoing germ. -/
theorem germ_restoration_retained {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    (ρ : ℝ) (a b : ℂ) (d : Dart G) :
    (D.restoration huv ρ a b).germ (retainedLastEdgeDart G u v d) =
      (D.restoredRoute ρ a b d.1).germ d.2 := by
  rcases d with ⟨e, side⟩
  change ((D.restoration huv ρ a b).route (retainedLastEdgeDart G u v (e, false)).1).germ side = _
  rw [route_restoration_retained]

/-- The selected actual source dart has the exact oriented connector germ. -/
theorem germ_restoration_last {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    (ρ : ℝ) (a b : ℂ) (side : Bool) :
    (D.restoration huv ρ a b).germ (lastEdgeDart G u v side) =
      if side then a - b else b - a := by
  have hedge : (lastEdgeDart G u v side).1 = (lastEdgeDart G u v false).1 := by
    cases side <;> rfl
  have htag : (lastEdgeDart G u v side).2 = side := by cases side <;> rfl
  change ((D.restoration huv ρ a b).route (lastEdgeDart G u v side).1).germ
    (lastEdgeDart G u v side).2 = _
  rw [hedge, htag, route_restoration_last, Route.germ_line]

/-- A lifted contracted end at either restored vertex has its own literal spoke germ. -/
theorem germ_restoration_lift_active {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    (ρ : ℝ) (a b : ℂ) (d : Dart (contractLastEdgeGraph G u v)) (hd : d.vertex = v) :
    (D.restoration huv ρ a b).germ (contractionLift G u v d) =
      D.cutPort ρ d - D.restoredVertex a b (contractionLift G u v d).vertex := by
  obtain ⟨⟨e, side⟩, rfl⟩ := (Dart.relabelEquiv G (Function.update id u v)).surjective d
  rw [contractionLift_relabelEquiv, germ_restoration_retained, vertex_retainedLastEdgeDart]
  apply D.germ_restoredRoute_active huv
  have h := (contractionLift_vertex_eq_iff G u v _).mp hd
  simpa only [contractionLift_relabelEquiv, vertex_retainedLastEdgeDart] using h

/-- At an unchanged vertex, a lifted end retains its old literal geometric direction. -/
theorem IsEmbedding.direction_restoration_lift_inactive {G : Graph} {u v : ℕ}
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)} (hD : D.IsEmbedding) (huv : u ≠ v)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hlen : ∀ d : Dart (contractLastEdgeGraph G u v), d.vertex = v → 3 * ρ < ‖D.germ d‖)
    (a b : ℂ) (d : Dart (contractLastEdgeGraph G u v)) (hd : d.vertex ≠ v) :
    (D.restoration huv ρ a b).direction (contractionLift G u v d) = D.direction d := by
  have hinactive : ¬((contractionLift G u v d).vertex = u ∨
      (contractionLift G u v d).vertex = v) := fun h =>
    hd ((contractionLift_vertex_eq_iff G u v d).mpr h)
  obtain ⟨⟨e, side⟩, rfl⟩ := (Dart.relabelEquiv G (Function.update id u v)).surjective d
  simp only [contractionLift_relabelEquiv, vertex_retainedLastEdgeDart] at hinactive
  simp only [direction]
  rw [contractionLift_relabelEquiv, germ_restoration_retained,
    D.germ_restoredRoute_inactive ρ a b e side hinactive,
    hD.arg_germ_outsideRoute v hρ hlen]
  rfl

end Cslib.Complexity.Graph.PolygonalDrawing
