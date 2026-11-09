/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Restriction
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Basic
public import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitOrder

/-!
# Clockwise order of cut ports after moving their center

An interior fan to common-radius cut ports retains the exact clockwise order of the
original drawing. Both ends of a loop and all indexed parallel occurrences remain distinct.
The center can move anywhere in the open cut ball, without a semicircle restriction on
the old ports. This does not construct a separator or restore a contracted edge.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

/-- A new fan center strictly inside the cut circle differs from every boundary port. -/
theorem IsEmbedding.cutPort_sub_ne_zero {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    {x : ℂ} (hx : x ∈ Metric.ball (D.vertex v) ρ) (d : Dart G) (hd : d.vertex = v) :
    D.cutPort ρ d - x ≠ 0 := by
  have hp : D.cutPort ρ d ∈ Metric.sphere (D.vertex v) ρ := by
    rw [Metric.mem_sphere, ← hd]
    exact hD.dist_cutPort hρ.le d
  intro heq
  have hmem : D.cutPort ρ d ∈ Metric.ball (D.vertex v) ρ :=
    (sub_eq_zero.mp heq).symm ▸ hx
  exact Set.disjoint_left.mp Metric.sphere_disjoint_ball hp hmem

/-- Distinct retained darts still have distinct outgoing directions at any new interior
fan center, including the two separate ends of an old loop. -/
theorem IsEmbedding.cutPort_direction_injective {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    {x : ℂ} (hx : x ∈ Metric.ball (D.vertex v) ρ) (a b : Dart G)
    (ha : a.vertex = v) (hb : b.vertex = v)
    (heq : ((D.cutPort ρ a - x).arg : Real.Angle) =
      ((D.cutPort ρ b - x).arg : Real.Angle)) : a = b := by
  have hport (d : Dart G) (hd : d.vertex = v) :
      D.cutPort ρ d ∈ Metric.sphere (D.vertex v) ρ := by
    rw [Metric.mem_sphere, ← hd]
    exact hD.dist_cutPort hρ.le d
  exact hD.cutPort_injective hρ a b (ha.trans hb.symm)
    (Polygonal.arg_sub_injective_on_sphere hx (hport a ha) (hport b hb) heq)

/-- Replacing a vertex by any interior fan center preserves the literal clockwise order
of its retained port triples. Connector insertion and separation into two blocks require
additional geometric work and are not asserted by this theorem. -/
theorem Realizes.cutPort_clockwise {G : Graph} {D : PolygonalDrawing G}
    {r : RotationSystem G} (hR : D.Realizes r) (hD : D.IsEmbedding)
    (v : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {x : ℂ} (hx : x ∈ Metric.ball (D.vertex v) ρ)
    (a b c : Dart G) (ha : a.vertex = v) (hb : b.vertex = v) (hc : c.vertex = v)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw ((D.cutPort ρ c - x).arg : Real.Angle) ((D.cutPort ρ b - x).arg : Real.Angle)
      ((D.cutPort ρ a - x).arg : Real.Angle) ↔ b ∈ r.rotationInterval a c := by
  have hport (d : Dart G) (hd : d.vertex = v) :
      D.cutPort ρ d ∈ Metric.sphere (D.vertex v) ρ := by
    rw [Metric.mem_sphere, ← hd]
    exact hD.dist_cutPort hρ.le d
  have hne (d e : Dart G) (hd : d.vertex = v) (he : e.vertex = v) (hne : d ≠ e) :
      D.cutPort ρ d ≠ D.cutPort ρ e :=
    fun h => hne (hD.cutPort_injective hρ d e (hd.trans he.symm) h)
  have horder := Polygonal.sbtw_arg_sub_iff_of_mem_ball hx (Metric.mem_ball_self hρ)
    (hport c hc) (hport b hb) (hport a ha) (hne c b hc hb hbc.symm)
    (hne b a hb ha hab.symm) (hne c a hc ha hac.symm)
  have harg (d : Dart G) (hd : d.vertex = v) :
      ((D.cutPort ρ d - D.vertex v).arg : Real.Angle) = D.direction d := by
    rw [← hd, hD.arg_cutPort_sub hρ]
    rfl
  rw [harg c hc, harg b hb, harg a ha] at horder
  exact horder.trans (hR.clockwise a b c (ha.trans hb.symm) (hb.trans hc.symm) hab hbc hac)

end Cslib.Complexity.Graph.PolygonalDrawing
