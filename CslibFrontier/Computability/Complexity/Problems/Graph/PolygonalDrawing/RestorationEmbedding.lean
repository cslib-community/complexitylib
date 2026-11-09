/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationSimplicity
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationParameters
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Geometric embedding conditions for nonloop restoration

The two new centers stay inside the old isolated neighborhood; all other declared
points retain their old coordinates outside it. Duplicate declarations and unused
isolated names are retained by membership throughout.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

/-- Only the two restored source names can have their new points in the old closed
replacement neighborhood. Unchanged declared isolates stay outside it. -/
theorem restoredVertex_active_of_mem_closedBall {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) {ρ : ℝ}
    (hpoints : ∀ w ∈ (contractLastEdgeGraph G u v).1,
      D.vertex w ∈ Metric.closedBall (D.vertex v) ρ → w = v)
    (a b : ℂ) (w : ℕ) (hw : w ∈ G.1)
    (hin : D.restoredVertex a b w ∈ Metric.closedBall (D.vertex v) ρ) : w = u ∨ w = v := by
  by_contra hn
  have hwu : w ≠ u := fun h => hn (Or.inl h)
  have hwv : w ≠ v := fun h => hn (Or.inr h)
  have hdecl : w ∈ (contractLastEdgeGraph G u v).1 := by
    have h := List.mem_map_of_mem (f := Function.update id u v) hw
    simpa only [contractLastEdgeGraph, Graph.relabel, Function.update_of_ne hwu, id_eq] using h
  simp only [restoredVertex, ite_eq_right hwu, ite_eq_right hwv] at hin
  exact hwv (hpoints w hdecl hin)

/-- The restored coordinates separate all original declared names, including isolates
and repeated declarations. No enumeration of the ambient natural-number names is used. -/
theorem IsEmbedding.restoredVertex_injective {G : Graph} {u v : ℕ}
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)} (hD : D.IsEmbedding) (huv : u ≠ v)
    {ρ : ℝ} (hpoints : ∀ w ∈ (contractLastEdgeGraph G u v).1,
      D.vertex w ∈ Metric.closedBall (D.vertex v) ρ → w = v)
    {a b : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ) (hb : b ∈ Metric.ball (D.vertex v) ρ)
    (hab : a ≠ b) : Set.InjOn (D.restoredVertex a b) {w | w ∈ G.1} := by
  have hdecl (w : ℕ) (hw : w ∈ G.1) (hwu : w ≠ u) :
      w ∈ (contractLastEdgeGraph G u v).1 := by
    have h := List.mem_map_of_mem (f := Function.update id u v) hw
    simpa only [contractLastEdgeGraph, Graph.relabel, Function.update_of_ne hwu, id_eq] using h
  have hactive (w : ℕ) (hw : w ∈ G.1)
      (hin : D.restoredVertex a b w ∈ Metric.ball (D.vertex v) ρ) : w = u ∨ w = v := by
    exact D.restoredVertex_active_of_mem_closedBall hpoints a b w hw
      (Metric.ball_subset_closedBall hin)
  intro x hx y hy heq
  by_cases hx' : x = u ∨ x = v
  · have hy' : y = u ∨ y = v := hactive y hy
      (heq ▸ D.restoredVertex_mem_ball huv ha hb x hx')
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · rfl
    · have h : a = b := by
        simpa only [restoredVertex, ite_eq_right huv.symm, ↓reduceIte] using heq
      exact False.elim (hab h)
    · have h : b = a := by
        simpa only [restoredVertex, ite_eq_right huv.symm, ↓reduceIte] using heq
      exact False.elim (hab h.symm)
    · rfl
  · have hy' : ¬(y = u ∨ y = v) := by
      intro hy'
      exact hx' (hactive x hx (heq.symm ▸ D.restoredVertex_mem_ball huv ha hb y hy'))
    have hxu : x ≠ u := fun h => hx' (Or.inl h)
    have hxv : x ≠ v := fun h => hx' (Or.inr h)
    have hyu : y ≠ u := fun h => hy' (Or.inl h)
    have hyv : y ≠ v := fun h => hy' (Or.inr h)
    simp only [restoredVertex, ite_eq_right hxu, ite_eq_right hxv,
      ite_eq_right hyu, ite_eq_right hyv] at heq
    exact hD.vertices_injective (hdecl x hx hxu) (hdecl y hy hyu) heq

/-- A declared source vertex on a restored retained route occurs only at its own
original end. This includes unused names and loops, with all real parameters checked. -/
theorem IsEmbedding.restoredRoute_vertex_contacts {G : Graph} {u v : ℕ}
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)} (hD : D.IsEmbedding) (huv : u ≠ v)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hpoints : ∀ w ∈ (contractLastEdgeGraph G u v).1,
      D.vertex w ∈ Metric.closedBall (D.vertex v) ρ → w = v)
    (hlen : ∀ d : Dart (contractLastEdgeGraph G u v), d.vertex = v → 3 * ρ < ‖D.germ d‖)
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
    (e : Fin G.2.length) (i : Fin (D.restoredRoute ρ a b e).segments) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) (w : ℕ) (hw : w ∈ G.1)
    (heq : (D.restoredRoute ρ a b e).eval i t = D.restoredVertex a b w) :
    ∃ side, (D.restoredRoute ρ a b e).AtEnd i t side ∧ Dart.vertex (G := G) (e, side) = w := by
  let j := contractedIndex G u v e
  have hvertex (side : Bool) : (contractionLift G u v (j, side)).vertex =
      Dart.vertex (G := G) (e, side) := by
    exact contractionLift_vertex_contractedIndex G u v e side
  have htarget (side : Bool) (h : Dart.vertex (G := G) (e, side) = u ∨
      Dart.vertex (G := G) (e, side) = v) : Dart.vertex (j, side) = v := by
    apply (contractionLift_vertex_eq_iff G u v (j, side)).mpr
    simpa only [hvertex] using h
  have hball (side : Bool) (h : Dart.vertex (G := G) (e, side) = u ∨
      Dart.vertex (G := G) (e, side) = v) {s : ℝ} (hs : s ∈ Set.Icc 0 1) :
      AffineMap.lineMap (D.restoredVertex a b (Dart.vertex (G := G) (e, side)))
        (D.cutPort ρ (j, side)) s ∈ Metric.closedBall (D.vertex v) ρ := by
    have hp : D.cutPort ρ (j, side) ∈ Metric.sphere (D.vertex v) ρ := by
      rw [Metric.mem_sphere]
      simpa only [htarget side h] using hD.dist_cutPort hρ.le (j, side)
    exact (convex_closedBall (D.vertex v) ρ).lineMap_mem
      (Metric.ball_subset_closedBall (D.restoredVertex_mem_ball huv ha hb _ h))
      (Metric.sphere_subset_closedBall hp) hs
  rcases D.restoredRoute_eval_cases huv ρ a b e i t with
    ⟨k, heval, hpos⟩ | ⟨hactive, heval, hpos⟩ | ⟨hactive, heval, hpos⟩
  · have hEq : (D.outsideRoute v ρ j).eval k t = D.restoredVertex a b w := heval.symm.trans heq
    by_cases hw' : w = u ∨ w = v
    · exact False.elim (hD.outsideRoute_not_mem_ball v hρ hcut j k ht
        (hEq.symm ▸ D.restoredVertex_mem_ball huv ha hb w hw'))
    · have hwu : w ≠ u := fun h => hw' (Or.inl h)
      have hwv : w ≠ v := fun h => hw' (Or.inr h)
      have hdecl : w ∈ (contractLastEdgeGraph G u v).1 := by
        have h := List.mem_map_of_mem (f := Function.update id u v) hw
        simpa only [contractLastEdgeGraph, Graph.relabel, Function.update_of_ne hwu, id_eq] using h
      have hOld : (D.outsideRoute v ρ j).eval k t = D.vertex w := by
        simpa only [restoredVertex, ite_eq_right hwu, ite_eq_right hwv] using hEq
      obtain ⟨side, hat, hv⟩ := hD.outsideRoute_vertex_contacts v hρ hlen j k ht w hdecl hOld
      have hupdate : Function.update id u v (Dart.vertex (G := G) (e, side)) = w := by
        simpa only [j, vertex_contractedIndex] using hv
      have hsource : Dart.vertex (G := G) (e, side) = w := by
        by_cases h : Dart.vertex (G := G) (e, side) = u
        · rw [h, Function.update_self] at hupdate
          exact False.elim (hwv hupdate.symm)
        · simpa only [Function.update_of_ne h, id_eq] using hupdate
      have hunchanged : ¬(Dart.vertex (G := G) (e, side) = u ∨ Dart.vertex (e, side) = v) := by
        rintro (h | h)
        · exact hwu (hsource.symm.trans h)
        · exact hwv (hsource.symm.trans h)
      exact ⟨side, D.restoredRoute_atEnd_of_exterior ρ a b e i k t side hpos hat hunchanged,
        hsource⟩
  · have hEq := heval.symm.trans heq
    have hw' := D.restoredVertex_active_of_mem_closedBall hpoints a b w hw
      (hEq ▸ hball false hactive ht)
    have hspoke : AffineMap.lineMap
        (D.restoredVertex a b (contractionLift G u v (j, false)).vertex)
        (D.cutPort ρ (j, false)) t = D.restoredVertex a b w := by
      simpa only [hvertex] using hEq
    obtain ⟨ht0, hsource⟩ := D.split_spoke_vertex_contact huv ρ a b f hsep hpa hpb
      ⟨(j, false), htarget false hactive⟩ w hw' ht hspoke
    exact ⟨false, D.restoredRoute_atEnd_first ρ a b e i hpos ht0,
      by simpa only [hvertex] using hsource⟩
  · have hEq : AffineMap.lineMap (D.restoredVertex a b (Dart.vertex (G := G) (e, true)))
        (D.cutPort ρ (j, true)) (1 - t) = D.restoredVertex a b w := by
      rw [AffineMap.lineMap_apply_one_sub]
      exact heval.symm.trans heq
    have ht' : 1 - t ∈ Set.Icc 0 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hw' := D.restoredVertex_active_of_mem_closedBall hpoints a b w hw
      (hEq ▸ hball true hactive ht')
    have hspoke : AffineMap.lineMap
        (D.restoredVertex a b (contractionLift G u v (j, true)).vertex)
        (D.cutPort ρ (j, true)) (1 - t) = D.restoredVertex a b w := by
      simpa only [hvertex] using hEq
    obtain ⟨ht0, hsource⟩ := D.split_spoke_vertex_contact huv ρ a b f hsep hpa hpb
      ⟨(j, true), htarget true hactive⟩ w hw' ht' hspoke
    exact ⟨true, D.restoredRoute_atEnd_last ρ a b e i hactive hpos (by linarith),
      by simpa only [hvertex] using hsource⟩

end Cslib.Complexity.Graph.PolygonalDrawing
