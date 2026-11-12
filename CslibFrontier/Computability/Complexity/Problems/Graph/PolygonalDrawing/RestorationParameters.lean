/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationRoutes
public import CslibFrontier.Foundations.Geometry.Polygonal.AttachmentParameters

/-!
# Parameter classification for restored graph routes

Every parameter belongs either to the unchanged exterior piece, the new first spoke,
or the new last spoke. Exact global positions distinguish the two end occurrences even
for a restored loop. No simplicity or geometric provider is needed for these data laws.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

/-- Classify every actual parameter of a restored retained edge, recording its global
position and retaining both independently attached end occurrences. -/
theorem restoredRoute_eval_cases {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    (ρ : ℝ) (a b : ℂ) (e : Fin G.2.length)
    (i : Fin (D.restoredRoute ρ a b e).segments) (t : ℝ) :
    let p := D.outsideRoute v ρ (contractedIndex G u v e)
    let w₀ := Dart.vertex (G := G) (e, false)
    let w₁ := Dart.vertex (G := G) (e, true)
    (∃ j : Fin p.segments, (D.restoredRoute ρ a b e).eval i t = p.eval j t ∧
      (D.restoredRoute ρ a b e).position i t = (attachmentCount u v w₀ : ℝ) + p.position j t) ∨
    ((w₀ = u ∨ w₀ = v) ∧
      (D.restoredRoute ρ a b e).eval i t = AffineMap.lineMap (D.restoredVertex a b w₀)
        (D.cutPort ρ (contractedIndex G u v e, false)) t ∧
      (D.restoredRoute ρ a b e).position i t = t) ∨
    ((w₁ = u ∨ w₁ = v) ∧
      (D.restoredRoute ρ a b e).eval i t = AffineMap.lineMap
        (D.cutPort ρ (contractedIndex G u v e, true)) (D.restoredVertex a b w₁) t ∧
      (D.restoredRoute ρ a b e).position i t =
        (p.segments : ℝ) + (attachmentCount u v w₀ : ℝ) + t) := by
  let p := D.outsideRoute v ρ (contractedIndex G u v e)
  let w₀ := Dart.vertex (G := G) (e, false)
  let w₁ := Dart.vertex (G := G) (e, true)
  let C := D.restoredVertex a b
  let T (q : Route) : Prop := ∀ (i : Fin q.segments) (t : ℝ),
    (∃ j : Fin p.segments, q.eval i t = p.eval j t ∧
      q.position i t = (attachmentCount u v w₀ : ℝ) + p.position j t) ∨
    ((w₀ = u ∨ w₀ = v) ∧ q.eval i t = AffineMap.lineMap (C w₀)
      (D.cutPort ρ (contractedIndex G u v e, false)) t ∧ q.position i t = t) ∨
    ((w₁ = u ∨ w₁ = v) ∧ q.eval i t = AffineMap.lineMap
      (D.cutPort ρ (contractedIndex G u v e, true)) (C w₁) t ∧
      q.position i t = (p.segments : ℝ) + (attachmentCount u v w₀ : ℝ) + t)
  have hport (side : Bool) (h : Dart.vertex (G := G) (e, side) = u ∨
      Dart.vertex (G := G) (e, side) = v) :
      p.endpoint side = D.cutPort ρ (contractedIndex G u v e, side) := by
    have hv : Dart.vertex (contractedIndex G u v e, side) = v := by
      rw [vertex_contractedIndex]
      rcases h with h | h <;> simp [h, Function.update_apply]
    simpa only [hv, ↓reduceIte] using
      D.endpoint_outsideRoute v ρ (contractedIndex G u v e) side
  have hT : T (D.restoredRoute ρ a b e) := by
    by_cases h₀ : w₀ = u ∨ w₀ = v
    · have hc₀ : attachmentCount u v w₀ = 1 := ite_eq_left h₀
      have hp₀ : p.start = D.cutPort ρ (contractedIndex G u v e, false) := hport false h₀
      by_cases h₁ : w₁ = u ∨ w₁ = v
      · have hp₁ : p.finish = D.cutPort ρ (contractedIndex G u v e, true) := hport true h₁
        have hroute : D.restoredRoute ρ a b e = (Route.prepend (C w₀) p).append (C w₁) := by
          rw [restoredRoute, D.restoreLast_eq_append huv _ h₁,
            D.restoreFirst_eq_prepend huv _ h₀]
        apply (congrArg T hroute).mpr
        intro i t
        rcases Route.attach_eval_cases (C w₀) p (C w₁) i t with
          ⟨j, heval, hpos⟩ | ⟨heval, hpos⟩ | ⟨heval, hpos⟩
        · exact Or.inl ⟨j, heval, by simpa only [hc₀, Nat.cast_one] using hpos⟩
        · exact Or.inr (Or.inl ⟨h₀, by simpa only [hp₀] using heval, hpos⟩)
        · exact Or.inr (Or.inr ⟨h₁, by simpa only [hp₁] using heval,
            by simpa only [hc₀, Nat.cast_one] using hpos⟩)
      · have hroute : D.restoredRoute ρ a b e = Route.prepend (C w₀) p := by
          rw [restoredRoute, restoreLast_eq_self _ _ _ h₁, D.restoreFirst_eq_prepend huv _ h₀]
        apply (congrArg T hroute).mpr
        intro i t
        rcases Route.prepend_eval_cases (C w₀) p i t with ⟨j, heval, hpos⟩ | ⟨heval, hpos⟩
        · exact Or.inl ⟨j, heval, by simpa only [hc₀, Nat.cast_one] using hpos⟩
        · exact Or.inr (Or.inl ⟨h₀, by simpa only [hp₀] using heval, hpos⟩)
    · have hc₀ : attachmentCount u v w₀ = 0 := ite_eq_right h₀
      by_cases h₁ : w₁ = u ∨ w₁ = v
      · have hp₁ : p.finish = D.cutPort ρ (contractedIndex G u v e, true) := hport true h₁
        have hroute : D.restoredRoute ρ a b e = p.append (C w₁) := by
          rw [restoredRoute, D.restoreLast_eq_append huv _ h₁, restoreFirst_eq_self _ _ _ h₀]
        apply (congrArg T hroute).mpr
        intro i t
        rcases Route.append_eval_cases p (C w₁) i t with ⟨j, heval, hpos⟩ | ⟨heval, hpos⟩
        · exact Or.inl ⟨j, heval, by simpa only [hc₀, Nat.cast_zero, zero_add] using hpos⟩
        · exact Or.inr (Or.inr ⟨h₁, by simpa only [hp₁] using heval,
            by simpa only [hc₀, Nat.cast_zero, add_zero] using hpos⟩)
      · have hroute : D.restoredRoute ρ a b e = p := by
          rw [restoredRoute, restoreLast_eq_self _ _ _ h₁, restoreFirst_eq_self _ _ _ h₀]
        apply (congrArg T hroute).mpr
        intro i t
        exact Or.inl ⟨i, rfl, by simp only [hc₀, Nat.cast_zero, zero_add]⟩
  exact hT i t

/-- An unchanged exterior endpoint retains its exact original end tag in the
restored route. Positive attachments at the other end are counted explicitly. -/
theorem restoredRoute_atEnd_of_exterior {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (ρ : ℝ) (a b : ℂ)
    (e : Fin G.2.length) (i : Fin (D.restoredRoute ρ a b e).segments)
    (j : Fin (D.outsideRoute v ρ (contractedIndex G u v e)).segments) (t : ℝ) (side : Bool)
    (hpos : (D.restoredRoute ρ a b e).position i t =
      (attachmentCount u v (Dart.vertex (G := G) (e, false)) : ℝ) +
        (D.outsideRoute v ρ (contractedIndex G u v e)).position j t)
    (hat : (D.outsideRoute v ρ (contractedIndex G u v e)).AtEnd j t side)
    (hunchanged : ¬(Dart.vertex (G := G) (e, side) = u ∨ Dart.vertex (e, side) = v)) :
    (D.restoredRoute ρ a b e).AtEnd i t side := by
  cases side
  · have hc : attachmentCount u v (Dart.vertex (G := G) (e, false)) = 0 :=
      ite_eq_right hunchanged
    change (D.restoredRoute ρ a b e).position i t = 0
    change (D.outsideRoute v ρ (contractedIndex G u v e)).position j t = 0 at hat
    rw [hpos, hc, Nat.cast_zero, zero_add, hat]
  · have hc : attachmentCount u v (Dart.vertex (G := G) (e, true)) = 0 :=
      ite_eq_right hunchanged
    change (D.restoredRoute ρ a b e).position i t = (D.restoredRoute ρ a b e).segments
    change (D.outsideRoute v ρ (contractedIndex G u v e)).position j t =
      (D.outsideRoute v ρ (contractedIndex G u v e)).segments at hat
    rw [hpos, hat, segments_restoredRoute, hc]
    push_cast
    ring

/-- The initial spoke's zero parameter is the restored first end. -/
theorem restoredRoute_atEnd_first {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (ρ : ℝ) (a b : ℂ)
    (e : Fin G.2.length) (i : Fin (D.restoredRoute ρ a b e).segments) {t : ℝ}
    (hpos : (D.restoredRoute ρ a b e).position i t = t) (ht : t = 0) :
    (D.restoredRoute ρ a b e).AtEnd i t false := by
  change (D.restoredRoute ρ a b e).position i t = 0
  exact hpos.trans ht

/-- The final spoke's unit parameter is the restored last end. -/
theorem restoredRoute_atEnd_last {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (ρ : ℝ) (a b : ℂ)
    (e : Fin G.2.length) (i : Fin (D.restoredRoute ρ a b e).segments) {t : ℝ}
    (hactive : Dart.vertex (G := G) (e, true) = u ∨ Dart.vertex (e, true) = v)
    (hpos : (D.restoredRoute ρ a b e).position i t =
      ((D.outsideRoute v ρ (contractedIndex G u v e)).segments : ℝ) +
        (attachmentCount u v (Dart.vertex (G := G) (e, false)) : ℝ) + t)
    (ht : t = 1) : (D.restoredRoute ρ a b e).AtEnd i t true := by
  have hc : attachmentCount u v (Dart.vertex (G := G) (e, true)) = 1 := ite_eq_left hactive
  change (D.restoredRoute ρ a b e).position i t = (D.restoredRoute ρ a b e).segments
  rw [hpos, ht, segments_restoredRoute, hc]
  push_cast
  rfl

/-- A parameter lies on the exterior piece or on one outward-oriented split spoke.
The zero outward parameter retains the corresponding actual source end. -/
theorem restoredRoute_trace_cases {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    (ρ : ℝ) (a b : ℂ) (e : Fin G.2.length)
    (i : Fin (D.restoredRoute ρ a b e).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (∃ j : Fin (D.outsideRoute v ρ (contractedIndex G u v e)).segments,
      (D.restoredRoute ρ a b e).eval i t =
        (D.outsideRoute v ρ (contractedIndex G u v e)).eval j t ∧
      (D.restoredRoute ρ a b e).position i t =
        (attachmentCount u v (Dart.vertex (G := G) (e, false)) : ℝ) +
          (D.outsideRoute v ρ (contractedIndex G u v e)).position j t) ∨
    (∃ (side : Bool) (s : ℝ), s ∈ Set.Icc 0 1 ∧
      (Dart.vertex (G := G) (e, side) = u ∨ Dart.vertex (e, side) = v) ∧
      (D.restoredRoute ρ a b e).eval i t =
        AffineMap.lineMap (D.restoredVertex a b (Dart.vertex (G := G) (e, side)))
          (D.cutPort ρ (contractedIndex G u v e, side)) s ∧
      (s = 0 → (D.restoredRoute ρ a b e).AtEnd i t side)) := by
  rcases D.restoredRoute_eval_cases huv ρ a b e i t with
    hold | ⟨hactive, heval, hpos⟩ | ⟨hactive, heval, hpos⟩
  · exact Or.inl hold
  · exact Or.inr ⟨false, t, ht, hactive, heval,
      D.restoredRoute_atEnd_first ρ a b e i hpos⟩
  · refine Or.inr ⟨true, 1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩,
      hactive, ?_, ?_⟩
    · rw [AffineMap.lineMap_apply_one_sub]
      exact heval
    · intro hs
      exact D.restoredRoute_atEnd_last ρ a b e i hactive hpos (by linarith)

end Cslib.Complexity.Graph.PolygonalDrawing
