/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationContacts

/-!
# Simplicity of restored edge routes

Each edge receives zero, one or two new spokes according to its two separate original
endpoint occurrences. All real segment contacts are checked. In particular a retained
target loop can become an open source edge, or close again at one new source center.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

/-- Separated local fans reattach every retained edge as a continuously simple route.
The exterior contact hypotheses are obtained from the old embedding's restriction. -/
theorem IsEmbedding.restoredRoute_simple {G : Graph} {u v : ℕ}
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)} (hD : D.IsEmbedding) (huv : u ≠ v)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsimple : ∀ e, (D.outsideRoute v ρ e).IsSimple)
    (hcut : ∀ e (i : Fin (D.outsideRoute v ρ e).segments) (t : ℝ), t ∈ Set.Icc 0 1 →
      (D.outsideRoute v ρ e).eval i t ∈ Metric.closedBall (D.vertex v) ρ →
        ∃ side, (D.outsideRoute v ρ e).AtEnd i t side ∧ Dart.vertex (e, side) = v ∧
          (D.outsideRoute v ρ e).eval i t = D.cutPort ρ (e, side))
    {a b : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ) (hb : b ∈ Metric.ball (D.vertex v) ρ)
    (f : ℂ →ᵃ[ℝ] ℝ) (hsep : f b < f a)
    (hpa : ∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
      (contractionLift G u v d.val).vertex = u → f a < f (D.cutPort ρ d.val))
    (hpb : ∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
      (contractionLift G u v d.val).vertex = v → f (D.cutPort ρ d.val) < f b)
    (e : Fin G.2.length) : (D.restoredRoute ρ a b e).IsSimple := by
  let w₀ := Dart.vertex (G := G) (e, false)
  let w₁ := Dart.vertex (G := G) (e, true)
  let j := contractedIndex G u v e
  let p := D.outsideRoute v ρ j
  let C := D.restoredVertex a b
  have hvertex (side : Bool) : (contractionLift G u v (j, side)).vertex =
      Dart.vertex (G := G) (e, side) := by
    exact contractionLift_vertex_contractedIndex G u v e side
  have htarget (side : Bool) (h : Dart.vertex (G := G) (e, side) = u ∨
      Dart.vertex (G := G) (e, side) = v) : Dart.vertex (j, side) = v := by
    apply (contractionLift_vertex_eq_iff G u v (j, side)).mpr
    simpa only [hvertex] using h
  have hball (w : ℕ) (hw : w = u ∨ w = v) : C w ∈ Metric.ball (D.vertex v) ρ :=
    D.restoredVertex_mem_ball huv ha hb w hw
  have hfirst (w : ℕ) (hw : w = u ∨ w = v) (p : Route) :
      restoreFirst u v w a b p = Route.prepend (C w) p :=
    D.restoreFirst_eq_prepend huv w hw a b p
  have hlast (w : ℕ) (hw : w = u ∨ w = v) (p : Route) :
      restoreLast u v w a b p = p.append (C w) :=
    D.restoreLast_eq_append huv w hw a b p
  have hfirst_none (w : ℕ) (hw : ¬(w = u ∨ w = v)) (p : Route) :
      restoreFirst u v w a b p = p := restoreFirst_eq_self u v w hw a b p
  have hlast_none (w : ℕ) (hw : ¬(w = u ∨ w = v)) (p : Route) :
      restoreLast u v w a b p = p := restoreLast_eq_self u v w hw a b p
  change (restoreLast u v w₁ a b (restoreFirst u v w₀ a b p)).IsSimple
  by_cases h₀ : w₀ = u ∨ w₀ = v
  · by_cases h₁ : w₁ = u ∨ w₁ = v
    · rw [hlast w₁ h₁, hfirst w₀ h₀]
      apply hD.attach_outsideRoute_simple v hρ hcut (hball w₀ h₀) (hball w₁ h₁) j
        (htarget false h₀) (htarget true h₁) (hsimple j)
      intro s t hs ht heq
      have hne : (⟨(j, false), htarget false h₀⟩ :
          {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}) ≠
          ⟨(j, true), htarget true h₁⟩ := fun h =>
        Bool.false_ne_true (congrArg (fun d => d.val.2) h)
      apply hD.split_spoke_contact hρ ha hb f hsep hpa hpb
        ⟨(j, false), htarget false h₀⟩ ⟨(j, true), htarget true h₁⟩ hne hs ht
      simpa only [hvertex] using heq
    · rw [hlast_none w₁ h₁, hfirst w₀ h₀]
      exact hD.prepend_outsideRoute_simple v hρ hcut (hball w₀ h₀) j
        (htarget false h₀) (hsimple j)
  · by_cases h₁ : w₁ = u ∨ w₁ = v
    · rw [hlast w₁ h₁, hfirst_none w₀ h₀]
      exact hD.append_outsideRoute_simple v hρ hcut (hball w₁ h₁) j
        (htarget true h₁) (hsimple j)
    · rw [hlast_none w₁ h₁, hfirst_none w₀ h₀]
      exact hsimple j

end Cslib.Complexity.Graph.PolygonalDrawing
