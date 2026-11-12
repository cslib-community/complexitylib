/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.RestorationEmbedding
public import CslibFrontier.Foundations.Geometry.Polygonal.LineEnds
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Contacts between distinct restored edge occurrences

Exterior pieces inherit their old contacts away from the split vertex. New spokes
meet only at their assigned source centers, and the connector meets them only at
its corresponding original ends. All statements quantify over real segment parameters.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

/-- Distinct retained restored edges meet only at their original common ends.
The two occurrences of a contracted loop remain independent throughout. -/
theorem IsEmbedding.restoredRoute_edge_contacts {G : Graph} {u v : ℕ}
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)} (hD : D.IsEmbedding) (huv : u ≠ v)
    {ρ : ℝ} (hρ : 0 < ρ)
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
    (e g : Fin G.2.length) (heg : e ≠ g)
    (i : Fin (D.restoredRoute ρ a b e).segments) (j : Fin (D.restoredRoute ρ a b g).segments)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : (D.restoredRoute ρ a b e).eval i s = (D.restoredRoute ρ a b g).eval j t) :
    ∃ side tag, (D.restoredRoute ρ a b e).AtEnd i s side ∧
      (D.restoredRoute ρ a b g).AtEnd j t tag ∧
        Dart.vertex (G := G) (e, side) = Dart.vertex (G := G) (g, tag) := by
  have hedge : contractedIndex G u v e ≠ contractedIndex G u v g :=
    fun h => heg ((contractedIndex G u v).injective h)
  have htarget (e : Fin G.2.length) (side : Bool)
      (h : Dart.vertex (G := G) (e, side) = u ∨ Dart.vertex (e, side) = v) :
      Dart.vertex (contractedIndex G u v e, side) = v := by
    apply (contractionLift_vertex_eq_iff G u v _).mpr
    simpa only [contractionLift_vertex_contractedIndex] using h
  have hmixed (e g : Fin G.2.length) (hne : e ≠ g) (side : Bool)
      (hactive : Dart.vertex (G := G) (e, side) = u ∨ Dart.vertex (e, side) = v)
      (k : Fin (D.outsideRoute v ρ (contractedIndex G u v g)).segments)
      {σ τ : ℝ} (hσ : σ ∈ Set.Icc 0 1) (hτ : τ ∈ Set.Icc 0 1)
      (hEq : AffineMap.lineMap (D.restoredVertex a b (Dart.vertex (G := G) (e, side)))
        (D.cutPort ρ (contractedIndex G u v e, side)) σ =
          (D.outsideRoute v ρ (contractedIndex G u v g)).eval k τ) : False := by
    obtain ⟨_, tag, hdart, _⟩ := hD.spoke_outsideRoute_contact v hρ hcut
      (D.restoredVertex_mem_ball huv ha hb _ hactive) _ (htarget e side hactive) _ k hσ hτ hEq
    exact hne ((contractedIndex G u v).injective (congrArg Prod.fst hdart))
  rcases D.restoredRoute_trace_cases huv ρ a b e i hs with
    ⟨k, heval, hpos⟩ | ⟨side, σ, hσ, hactive, heval, hat⟩
  · rcases D.restoredRoute_trace_cases huv ρ a b g j ht with
      ⟨l, hgeval, hgpos⟩ | ⟨tag, τ, hτ, hgactive, hgeval, _⟩
    · have hEq := heval.symm.trans (heq.trans hgeval)
      obtain ⟨side, tag, hat, hgat, hv⟩ :=
        hD.outsideRoute_edge_contacts v hρ hlen _ _ hedge k l hs ht hEq
      have hvne : Dart.vertex (contractedIndex G u v e, side) ≠ v := by
        intro hv'
        have hgv := hv.symm.trans hv'
        have hport := (D.outsideRoute v ρ (contractedIndex G u v e)).at_eq_endpoint k hs side hat
        have hgport := (D.outsideRoute v ρ (contractedIndex G u v g)).at_eq_endpoint l ht tag hgat
        rw [D.endpoint_outsideRoute, ite_eq_left hv'] at hport
        rw [D.endpoint_outsideRoute, ite_eq_left hgv] at hgport
        have hp := hport.symm.trans (hEq.trans hgport)
        exact hedge (congrArg Prod.fst (hD.cutPort_injective hρ _ _ hv hp))
      have hinactive (e : Fin G.2.length) (side : Bool)
          (hn : Dart.vertex (contractedIndex G u v e, side) ≠ v) :
          ¬(Dart.vertex (G := G) (e, side) = u ∨ Dart.vertex (e, side) = v) :=
        fun h => hn (htarget e side h)
      have heactive := hinactive e side hvne
      have hgactive := hinactive g tag (fun h => hvne (hv.trans h))
      have hupdate (e : Fin G.2.length) (side : Bool)
          (hn : ¬(Dart.vertex (G := G) (e, side) = u ∨ Dart.vertex (e, side) = v)) :
          Dart.vertex (contractedIndex G u v e, side) = Dart.vertex (G := G) (e, side) := by
        rw [vertex_contractedIndex, Function.update_of_ne (fun h => hn (Or.inl h))]
        rfl
      exact ⟨side, tag, D.restoredRoute_atEnd_of_exterior ρ a b e i k s side hpos hat heactive,
        D.restoredRoute_atEnd_of_exterior ρ a b g j l t tag hgpos hgat hgactive,
        (hupdate e side heactive).symm.trans (hv.trans (hupdate g tag hgactive))⟩
    · exact False.elim (hmixed g e heg.symm tag hgactive k hτ hs
        (hgeval.symm.trans (heq.symm.trans heval)))
  · rcases D.restoredRoute_trace_cases huv ρ a b g j ht with
      ⟨l, hgeval, _⟩ | ⟨tag, τ, hτ, hgactive, hgeval, hgat⟩
    · exact False.elim (hmixed e g heg side hactive l hσ ht
        (heval.symm.trans (heq.trans hgeval)))
    · let d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v} :=
        ⟨(contractedIndex G u v e, side), htarget e side hactive⟩
      let c : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v} :=
        ⟨(contractedIndex G u v g, tag), htarget g tag hgactive⟩
      have hdc : d ≠ c := fun h => hedge (congrArg (fun d => d.val.1) h)
      have hEq : AffineMap.lineMap (D.restoredVertex a b (contractionLift G u v d.val).vertex)
          (D.cutPort ρ d.val) σ =
          AffineMap.lineMap (D.restoredVertex a b (contractionLift G u v c.val).vertex)
            (D.cutPort ρ c.val) τ := by
        simpa only [d, c, contractionLift_vertex_contractedIndex] using
          heval.symm.trans (heq.trans hgeval)
      obtain ⟨hσ0, hτ0⟩ := hD.split_spoke_contact hρ ha hb f hsep hpa hpb d c hdc hσ hτ hEq
      have hvertex : (contractionLift G u v c.val).vertex = Dart.vertex (G := G) (e, side) := by
        have hc : AffineMap.lineMap (D.restoredVertex a b (contractionLift G u v c.val).vertex)
            (D.cutPort ρ c.val) τ = D.restoredVertex a b (Dart.vertex (G := G) (e, side)) := by
          have h := hEq.symm
          simpa only [hσ0, AffineMap.lineMap_apply_zero, d,
            contractionLift_vertex_contractedIndex] using h
        exact (D.split_spoke_vertex_contact huv ρ a b f hsep hpa hpb c _ hactive hτ hc).2
      exact ⟨side, tag, hat hσ0, hgat hτ0, by
        simpa only [c, contractionLift_vertex_contractedIndex] using hvertex.symm⟩

/-- The selected connector meets a retained restored edge only at its corresponding
original endpoint. It never touches the unchanged exterior pieces. -/
theorem IsEmbedding.restoredRoute_connector_contacts {G : Graph} {u v : ℕ}
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)} (hD : D.IsEmbedding) (huv : u ≠ v)
    {ρ : ℝ} (hρ : 0 < ρ)
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
    (e : Fin G.2.length) (i : Fin (D.restoredRoute ρ a b e).segments)
    (j : Fin (Route.line a b).segments) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : (D.restoredRoute ρ a b e).eval i s = (Route.line a b).eval j t) :
    ∃ side tag, (D.restoredRoute ρ a b e).AtEnd i s side ∧
      (Route.line a b).AtEnd j t tag ∧ Dart.vertex (G := G) (e, side) = if tag then v else u := by
  rw [Route.eval_line] at heq
  rcases D.restoredRoute_trace_cases huv ρ a b e i hs with
    ⟨k, heval, _⟩ | ⟨side, σ, hσ, hactive, heval, hat⟩
  · have hin := (convex_ball (D.vertex v) ρ).lineMap_mem ha hb ht
    exact False.elim (hD.outsideRoute_not_mem_ball v hρ hcut _ k hs
      ((heval.symm.trans heq).symm ▸ hin))
  · have hv : Dart.vertex (contractedIndex G u v e, side) = v := by
      apply (contractionLift_vertex_eq_iff G u v _).mpr
      simpa only [contractionLift_vertex_contractedIndex] using hactive
    let d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v} :=
      ⟨(contractedIndex G u v e, side), hv⟩
    have hEq : AffineMap.lineMap (D.restoredVertex a b (contractionLift G u v d.val).vertex)
        (D.cutPort ρ d.val) σ = AffineMap.lineMap a b t := by
      simpa only [d, contractionLift_vertex_contractedIndex] using heval.symm.trans heq
    obtain ⟨hσ0, hu | hv⟩ := D.split_spoke_connector_contact ρ a b f hsep hpa hpb d hσ ht hEq
    · exact ⟨side, false, hat hσ0, (Route.atEnd_line_iff a b j t false).mpr hu.2, by
        simpa only [d, contractionLift_vertex_contractedIndex, Bool.false_eq_true,
          ↓reduceIte] using hu.1⟩
    · exact ⟨side, true, hat hσ0, (Route.atEnd_line_iff a b j t true).mpr hv.2, by
        simpa only [d, contractionLift_vertex_contractedIndex, ↓reduceIte] using hv.1⟩

/-- A declared point on the new connector is exactly one of its original named ends. -/
theorem connector_vertex_contacts {G : Graph} {u v : ℕ}
    (D : PolygonalDrawing (contractLastEdgeGraph G u v)) (huv : u ≠ v)
    {ρ : ℝ} (hpoints : ∀ w ∈ (contractLastEdgeGraph G u v).1,
      D.vertex w ∈ Metric.closedBall (D.vertex v) ρ → w = v)
    {a b : ℂ} (ha : a ∈ Metric.ball (D.vertex v) ρ) (hb : b ∈ Metric.ball (D.vertex v) ρ)
    (hab : a ≠ b) (i : Fin (Route.line a b).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (w : ℕ) (hw : w ∈ G.1) (heq : (Route.line a b).eval i t = D.restoredVertex a b w) :
    ∃ side, (Route.line a b).AtEnd i t side ∧ (if side then v else u) = w := by
  rw [Route.eval_line] at heq
  have hin := (convex_closedBall (D.vertex v) ρ).lineMap_mem
    (Metric.ball_subset_closedBall ha) (Metric.ball_subset_closedBall hb) ht
  rcases D.restoredVertex_active_of_mem_closedBall hpoints a b w hw (heq ▸ hin) with hwu | hwv
  · have ht0 : t = 0 := by
      apply AffineMap.lineMap_injective ℝ hab
      have h := heq.trans (congrArg (D.restoredVertex a b) hwu)
      simpa only [restoredVertex, ↓reduceIte, AffineMap.lineMap_apply_zero] using h
    exact ⟨false, (Route.atEnd_line_iff a b i t false).mpr ht0, hwu.symm⟩
  · have ht1 : t = 1 := by
      apply AffineMap.lineMap_injective ℝ hab
      have h := heq.trans (congrArg (D.restoredVertex a b) hwv)
      simpa only [restoredVertex, ite_eq_right huv.symm, ↓reduceIte,
        AffineMap.lineMap_apply_one] using h
    exact ⟨true, (Route.atEnd_line_iff a b i t true).mpr ht1, hwv.symm⟩

end Cslib.Complexity.Graph.PolygonalDrawing
