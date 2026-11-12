/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SplitOrder
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.SplitBlocks
public import CslibFrontier.Foundations.Geometry.Polygonal.FiniteAngleOrder
public import CslibFrontier.Foundations.Geometry.Polygonal.CircleConnector

/-!
# Automatic local split layout from an actual contracted realization

Literal contraction block coordinates determine an open turn of actual germ angles,
with the prescribed source insertion slot retained. No separator, drawing patch or
geometric order provider is an input.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal RotationSystem

/-- An arbitrary actual contracted realization supplies real angular representatives
in the exact reverse order of the two literal source blocks. The cut lies in their
specified insertion gap. The empty contracted star is included. -/
theorem Realizes.exists_contraction_angle_lift {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)}
    (hR : D.Realizes (r.contractLastEdge huv)) :
    ∃ cut : ℝ, ∃ L : Real.Angle → ℝ,
      (∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
        L (D.direction d.val) ∈ Set.Ioo cut (cut + 2 * Real.pi)) ∧
      (∀ φ, (L φ : Real.Angle) = φ) ∧
      (∀ a b : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
        L (D.direction a.val) < L (D.direction b.val) ↔
          (r.contractionRank b).val < (r.contractionRank a).val) := by
  let N := (Function.minimalPeriod r.rotate (lastEdgeDart G u v true) - 1) +
    (Function.minimalPeriod r.rotate (lastEdgeDart G u v false) - 1)
  cases hN : N with
  | zero =>
    have hempty (d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}) : False := by
      have h := (r.contractionRank d).isLt
      change (r.contractionRank d).val < N at h
      omega
    exact ⟨0, Real.Angle.toReal, fun d => (hempty d).elim,
      Real.Angle.coe_toReal, fun a _ => (hempty a).elim⟩
  | succ n =>
    let e := (r.contractionRankEquiv huv).trans (finCongr hN)
    let dir : Fin (n + 1) → Real.Angle := fun i => D.direction (e.symm i).val
    have hrank (i : Fin (n + 1)) : (r.contractionRank (e.symm i)).val = i.val :=
      congrArg Fin.val (e.apply_symm_apply i)
    have hinj : Function.Injective dir := by
      intro i j heq
      have hvertex : (e.symm i).val.vertex = (e.symm j).val.vertex :=
        (e.symm i).property.trans (e.symm j).property.symm
      have hd := hR.directions_injective (e.symm i).val (e.symm j).val hvertex heq
      exact e.symm.injective (Subtype.ext hd)
    have horder : ∀ i j : Fin (n + 1), i ≠ Fin.last n → j ≠ Fin.last n → i ≠ j →
        (sbtw (dir (Fin.last n)) (dir i) (dir j) ↔ j.val < i.val) := by
      intro i j hi hj hij
      have hni : i.val < n := by
        have hval : i.val ≠ n := fun h => hi (Fin.ext h)
        omega
      have hnj : j.val < n := by
        have hval : j.val ≠ n := fun h => hj (Fin.ext h)
        omega
      have hne (i j : Fin (n + 1)) (hij : i ≠ j) : (e.symm i).val ≠ (e.symm j).val :=
        fun h => hij (e.symm.injective (Subtype.ext h))
      have h := hR.clockwise (e.symm j).val (e.symm i).val (e.symm (Fin.last n)).val
        ((e.symm j).property.trans (e.symm i).property.symm)
        ((e.symm i).property.trans (e.symm (Fin.last n)).property.symm)
        (hne j i hij.symm) (hne i _ hi) (hne j _ hj)
      rw [r.mem_rotationInterval_contractLastEdge_iff_ranks huv
        (e.symm j) (e.symm i) (e.symm (Fin.last n))
        (fun h => hij.symm (e.symm.injective h))
        (fun h => hi (e.symm.injective h)) (fun h => hj (e.symm.injective h)),
        hrank, hrank, hrank, Fin.val_last] at h
      exact h.trans (by omega)
    obtain ⟨cut, L, hmem, hcoe, hlt⟩ := exists_reverse_ordered_angle_lift n dir hinj horder
    refine ⟨cut, L, ?_, hcoe, ?_⟩
    · intro d
      simpa only [dir, e.symm_apply_apply] using hmem (e d)
    · intro a b
      have h := hlt (e a) (e b)
      simpa only [dir, e.symm_apply_apply, ← hrank] using h

/-- An actual contracted embedding supplies its own two separated fans and connector
in the exact source insertion slots. No geometric split data are premises. The cut
circle may have any positive radius; a restriction radius is chosen separately. -/
theorem Realizes.exists_contraction_split {G : Graph} {u v : ℕ}
    (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v)
    {D : PolygonalDrawing (contractLastEdgeGraph G u v)} (hD : D.IsEmbedding)
    (hR : D.Realizes (r.contractLastEdge huv)) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ a ∈ Metric.ball (D.vertex v) ρ, ∃ b ∈ Metric.ball (D.vertex v) ρ,
      ∃ f : ℂ →ᵃ[ℝ] ℝ, f b < f a ∧
      (∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
        (contractionLift G u v d.val).vertex = u → f a < f (D.cutPort ρ d.val)) ∧
      (∀ d : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
        (contractionLift G u v d.val).vertex = v → f (D.cutPort ρ d.val) < f b) ∧
      (∀ x y : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
        (contractionLift G u v x.val).vertex = u →
        (contractionLift G u v y.val).vertex = u → x ≠ y →
        (sbtw ((b - a).arg : Real.Angle) ((D.cutPort ρ x.val - a).arg : Real.Angle)
          ((D.cutPort ρ y.val - a).arg : Real.Angle) ↔
        r.rotationDistance (lastEdgeDart G u v false) (contractionLift G u v y.val) <
          r.rotationDistance (lastEdgeDart G u v false) (contractionLift G u v x.val))) ∧
      (∀ x y : {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v},
        (contractionLift G u v x.val).vertex = v →
        (contractionLift G u v y.val).vertex = v → x ≠ y →
        (sbtw ((a - b).arg : Real.Angle) ((D.cutPort ρ x.val - b).arg : Real.Angle)
          ((D.cutPort ρ y.val - b).arg : Real.Angle) ↔
        r.rotationDistance (lastEdgeDart G u v true) (contractionLift G u v y.val) <
          r.rotationDistance (lastEdgeDart G u v true) (contractionLift G u v x.val))) := by
  classical
  let I := {d : Dart (contractLastEdgeGraph G u v) // d.vertex = v}
  let P : I → ℂ := fun d => D.cutPort ρ d.val
  let U : Finset I := Finset.univ.filter fun d => (contractionLift G u v d.val).vertex = u
  let V : Finset I := Finset.univ.filter fun d => (contractionLift G u v d.val).vertex = v
  let A := U.image P
  let B := V.image P
  obtain ⟨cut, L, hmem, hcoe, hlt⟩ := hR.exists_contraction_angle_lift r huv
  let θ : ℂ → ℝ := fun x => L ((x - D.vertex v).arg : Real.Angle)
  have hangle (d : I) : ((P d - D.vertex v).arg : Real.Angle) = D.direction d.val := by
    have h := congrArg (fun t : ℝ => (t : Real.Angle)) (hD.arg_cutPort_sub hρ d.val)
    simpa only [d.property, direction] using h
  have hθ (d : I) : θ (P d) = L (D.direction d.val) := congrArg L (hangle d)
  have hsphere (d : I) : P d ∈ Metric.sphere (D.vertex v) ρ := by
    rw [Metric.mem_sphere]
    simpa only [d.property] using hD.dist_cutPort hρ.le d.val
  have hports (S : Finset I) (x : ℂ) (hx : x ∈ S.image P) :
      x ∈ Metric.sphere (D.vertex v) ρ ∧ θ x ∈ Set.Ioo cut (cut + 2 * Real.pi) ∧
      ((x - D.vertex v).arg : Real.Angle) = (θ x : Real.Angle) := by
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hsphere d, (hθ d).symm ▸ hmem d, (hcoe _).symm⟩
  have hAB : ∀ x ∈ A, ∀ y ∈ B, θ x < θ y := by
    intro x hx y hy
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
    have hdu : (contractionLift G u v d.val).vertex = u := (Finset.mem_filter.mp hd).2
    have hev : (contractionLift G u v e.val).vertex = v := (Finset.mem_filter.mp he).2
    rw [hθ, hθ, hlt]
    have hdv : (contractionLift G u v d.val).vertex ≠ v := fun h => huv (hdu.symm.trans h)
    rw [r.val_contractionRank, r.val_contractionRank, ite_eq_left hev, ite_eq_right hdv]
    have hpos := r.rotationDistance_pos_of_ne (lastEdgeDart G u v false)
      (contractionLift G u v d.val) (by simpa using hdu.symm)
      (contractionLift_ne_lastEdgeDart G u v d.val false)
    have hpose := r.rotationDistance_pos_of_ne (lastEdgeDart G u v true)
      (contractionLift G u v e.val) (by simpa using hev.symm)
      (contractionLift_ne_lastEdgeDart G u v e.val true)
    have hbound := r.rotationDistance_lt_period (a := lastEdgeDart G u v true)
      (b := contractionLift G u v e.val) (by simpa using hev.symm)
    omega
  obtain ⟨a, ha, b, hb, f, hsep, hpa, hpb, horderA, horderB⟩ :=
    exists_split_fans_of_finite_blocks hρ A B θ cut (hports U) (hports V) hAB
  have hUA (d : I) (hd : (contractionLift G u v d.val).vertex = u) : P d ∈ A :=
    Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩, rfl⟩
  have hVB (d : I) (hd : (contractionLift G u v d.val).vertex = v) : P d ∈ B :=
    Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩, rfl⟩
  have hne (x y : I) (hxy : x ≠ y) : P x ≠ P y := fun h =>
    hxy (Subtype.ext (hD.cutPort_injective hρ x.val y.val
      (x.property.trans y.property.symm) h))
  refine ⟨a, ha, b, hb, f, hsep, fun d hd => hpa _ (hUA d hd),
    fun d hd => hpb _ (hVB d hd), ?_, ?_⟩
  · intro x y hxu hyu hxy
    have h := horderA (P x) (hUA x hxu) (P y) (hUA y hyu) (hne x y hxy)
    rw [hθ, hθ, hlt] at h
    exact h.trans (r.contractionRank_lt_iff_sourceDistance_lt huv y x false
      (by simpa only [vertex_lastEdgeDart, Bool.false_eq_true, ↓reduceIte] using hyu)
      (by simpa only [vertex_lastEdgeDart, Bool.false_eq_true, ↓reduceIte] using hxu))
  · intro x y hxv hyv hxy
    have h := horderB (P x) (hVB x hxv) (P y) (hVB y hyv) (hne x y hxy)
    rw [hθ, hθ, hlt] at h
    exact h.trans (r.contractionRank_lt_iff_sourceDistance_lt huv y x true
      (by simpa only [vertex_lastEdgeDart, ↓reduceIte] using hyv)
      (by simpa only [vertex_lastEdgeDart, ↓reduceIte] using hxv))

end Cslib.Complexity.Graph.PolygonalDrawing
