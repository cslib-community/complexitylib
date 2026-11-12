/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.SplitOrder
import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.Star
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Bouquet
import CslibFrontier.Foundations.Geometry.Polygonal.LocalSplitFan
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
Actual real-parameter cuts, round-boundary fans spanning more than a semicircle before
moving their center, and restrictions of genuine star and bouquet embeddings. These are
local geometry tests, not nonloop restoration or general forward-realization instances.
-/

namespace CslibFrontierTests.PolygonalRestriction

open Cslib Cslib.Polygonal Cslib.Complexity Cslib.Complexity.Graph

-- Independent unequal cuts on the same one-segment edge retain [2, 15/2].
example : ((Route.line 0 10).cutEnds (1 / 5) (1 / 4)).IsSimple :=
  (Route.isSimple_line (by norm_num)).cutEnds (by norm_num) (by norm_num) (by norm_num)

example (u : ℝ) : ((Route.line 0 10).cutEnds (1 / 5) (1 / 4)).eval 0 u =
    ((2 + (11 / 2 : ℝ) * u : ℝ) : ℂ) := by
  calc
    _ = (Route.line 0 10).eval 0 ((Route.line 0 10).cutTime (1 / 5) (1 / 4) 0 u) :=
      Route.eval_cutEnds (Route.line 0 10) (1 / 5) (1 / 4) 0 u
    _ = _ := by
      rw [Route.eval_line]
      apply Complex.ext <;>
        norm_num [Route.cutTime, Route.cutLower, Route.cutUpper, Route.line, Route.segments,
          AffineMap.lineMap_apply_module, Complex.smul_re, Complex.smul_im]; ring

-- A one-end cut leaves the other endpoint exactly unchanged.
example : ((Route.line 0 10).cutEnds (1 / 5) 0).endpoint true = 10 := by
  rw [Route.endpoint_cutEnds]
  norm_num [Route.eval_line, Route.endTime]

-- Cutting a genuine high-degree nonloop star supplies its own exterior separation.
example (n : ℕ) : ∃ ρ > 0, ∀ e, ((PolygonalDrawing.star n).outsideRoute n ρ e).IsSimple := by
  obtain ⟨ρ, hρ, _, hsimple, _⟩ := (PolygonalDrawing.star_isEmbedding n).exists_restriction n
    (by simp [RotationSystem.starGraph])
  exact ⟨ρ, hρ, hsimple⟩

private abbrev big : ℕ := 2 ^ 250

private abbrev listed : Graph :=
  ([big, 7, big, 12, 12], [(big, big), (big, big), (7, 7)])

private def certificate : Graph.RotationCertificate := ⟨[1, 2, 3, 0, 5, 4]⟩

private noncomputable def rotation : RotationSystem listed :=
  Graph.RotationCertificate.decode listed certificate (by decide +kernel)

private theorem genus : rotation.NumericalGenusZero :=
  (Graph.RotationCertificate.verifyEuler_eq_true_iff (G := listed) (c := certificate)
    (by decide +kernel)).mp (by decide +kernel)

private noncomputable def drawing : PolygonalDrawing listed :=
  PolygonalDrawing.bouquet rotation (by decide +kernel)

private theorem embedded : drawing.IsEmbedding :=
  PolygonalDrawing.bouquet_isEmbedding rotation (by decide +kernel) genus (by decide +kernel)

private theorem realized : drawing.Realizes rotation :=
  PolygonalDrawing.bouquet_realizes rotation (by decide +kernel)

-- Both ends of a genuine closed route are cut separately into distinct boundary ports.
-- Sparse names, duplicate declarations, a second loop, and a disconnected isolate remain.
example : ∃ ρ > 0, (drawing.outsideRoute big ρ 0).IsSimple ∧
    (drawing.outsideRoute big ρ 0).start ≠ (drawing.outsideRoute big ρ 0).finish := by
  obtain ⟨ρ, hρ, _, hs, _⟩ := embedded.exists_restriction big (by simp)
  refine ⟨ρ, hρ, hs 0, ?_⟩
  change (drawing.outsideRoute big ρ 0).endpoint false ≠
    (drawing.outsideRoute big ρ 0).endpoint true
  rw [PolygonalDrawing.endpoint_outsideRoute, PolygonalDrawing.endpoint_outsideRoute]
  have hv0 : Dart.vertex (G := listed) (0, false) = big := rfl
  have hv1 : Dart.vertex (G := listed) (0, true) = big := rfl
  rw [ite_eq_left hv0, ite_eq_left hv1]
  intro heq
  have hd := embedded.cutPort_injective hρ (0, false) (0, true) (hv0.trans hv1.symm) heq
  exact Bool.false_ne_true (congrArg Prod.snd hd)

-- The nullary star also admits a restriction radius with no invented edge ends.
example : ∃ ρ > 0, ∀ e, ((PolygonalDrawing.star 0).outsideRoute 0 ρ e).IsSimple := by
  obtain ⟨ρ, hρ, _, hs, _⟩ := (PolygonalDrawing.star_isEmbedding 0).exists_restriction 0
    (by decide)
  exact ⟨ρ, hρ, hs⟩

example : ∃ ρ > 0, drawing.vertex big ∉ Metric.closedBall (drawing.vertex 12) ρ := by
  obtain ⟨ρ, hρ, hvertices, _⟩ := embedded.exists_restriction 12 (by simp)
  refine ⟨ρ, hρ, fun hz => ?_⟩
  have h := hvertices big (by simp) hz
  have hne : big ≠ 12 := by decide +kernel
  exact hne h

-- A genuinely moved center retains the supplied literal clockwise order of old ports.
example : ∃ ρ > 0,
    let x := drawing.vertex big + ((ρ / 2 : ℝ) : ℂ)
    sbtw ((drawing.cutPort ρ (1, false) - x).arg : Real.Angle)
      ((drawing.cutPort ρ (0, true) - x).arg : Real.Angle)
      ((drawing.cutPort ρ (0, false) - x).arg : Real.Angle) := by
  obtain ⟨ρ, hρ, _⟩ := embedded.exists_restriction big (by simp)
  refine ⟨ρ, hρ, ?_⟩
  have hx : drawing.vertex big + ((ρ / 2 : ℝ) : ℂ) ∈ Metric.ball (drawing.vertex big) ρ := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    linarith
  apply (realized.cutPort_clockwise embedded big hρ hx (0, false) (0, true) (1, false)
    rfl rfl rfl (by decide) (by decide) (by decide)).mpr
  have hd : rotation.rotationDistance (0, false) (1, false) = 2 := by
    apply rotation.rotationDistance_eq _ _ (by decide +kernel) 2 (by decide +kernel)
    intro k hk
    interval_cases k <;> decide +kernel
  unfold RotationSystem.rotationInterval
  rw [hd]
  decide +kernel

private def ports : Fin 3 → ℂ := ![(-5 : ℂ), (⟨3, 4⟩ : ℂ), (⟨3, -4⟩ : ℂ)]

private theorem ports_on_circle (i : Fin 3) : ports i ∈ Metric.sphere 0 5 := by
  fin_cases i <;>
    norm_num [ports, Metric.mem_sphere, dist_eq_norm, Complex.norm_def, Complex.normSq]
  all_goals exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)

private theorem moved_inside : (7 / 2 : ℂ) ∈ Metric.ball 0 5 := by
  norm_num [Metric.mem_ball, dist_eq_norm, Complex.norm_def, Complex.normSq]

private theorem original_order :
    sbtw ((ports 1).arg : Real.Angle) ((ports 0).arg : Real.Angle)
      ((ports 2).arg : Real.Angle) := by
  have hneg : (ports 2).arg < 0 := Complex.arg_neg_iff.mpr (by norm_num [ports])
  have hnonneg : 0 ≤ (ports 1).arg := Complex.arg_nonneg_iff.mpr (by norm_num [ports])
  have hlt : (ports 1).arg < Real.pi := Complex.arg_lt_pi_iff.mpr (by norm_num [ports])
  have hpi : (ports 0).arg = Real.pi := Complex.arg_eq_pi_iff.mpr (by norm_num [ports])
  have hspan : (ports 0).arg - (ports 2).arg < 2 * Real.pi := by
    rw [hpi]
    linarith [Complex.neg_pi_lt_arg (ports 2)]
  exact (sbtw_angle_of_lt_of_span_lt (hneg.trans_le hnonneg) (hlt.trans_eq hpi.symm)
    hspan).cyclic_left

private theorem moved_order :
    sbtw ((ports 1 - (7 / 2 : ℂ)).arg : Real.Angle)
      ((ports 0 - (7 / 2 : ℂ)).arg : Real.Angle)
      ((ports 2 - (7 / 2 : ℂ)).arg : Real.Angle) := by
  have horder := sbtw_arg_sub_iff_of_mem_ball (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 5))
    moved_inside (ports_on_circle 1) (ports_on_circle 0) (ports_on_circle 2)
    (by norm_num [ports, Complex.ext_iff]) (by norm_num [ports, Complex.ext_iff])
    (by norm_num [ports, Complex.ext_iff])
  apply horder.mp
  simpa using original_order

example : ¬sbtw ((ports 2 - (7 / 2 : ℂ)).arg : Real.Angle)
    ((ports 0 - (7 / 2 : ℂ)).arg : Real.Angle)
    ((ports 1 - (7 / 2 : ℂ)).arg : Real.Angle) := moved_order.not_sbtw

-- The three ports cover an arc greater than pi around the old center 0.
-- The moved center still yields a nonintersecting fan for every pair of distinct ports.
example (i j : Fin 3) (hij : i ≠ j) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : AffineMap.lineMap (7 / 2 : ℂ) (ports i) s =
      AffineMap.lineMap (7 / 2 : ℂ) (ports j) t) : s = 0 ∧ t = 0 := by
  apply fan_contact moved_inside (ports_on_circle i) (ports_on_circle j) _ hs ht heq
  have hinj : Function.Injective ports := by
    intro i j h
    fin_cases i <;> fin_cases j
    all_goals
      first
      | rfl
      | (exfalso
         have hcoords := congrArg (fun z : ℂ => (z.re, z.im)) h
         norm_num [ports, Prod.mk.injEq] at hcoords)
  exact fun h => hij (hinj h)

private def separatingCoordinate : ℂ →ᵃ[ℝ] ℝ := -Complex.reLm.toAffineMap

-- The opposite spoke and connector also avoid the whole major-arc fan.
example (i : Fin 3) {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    AffineMap.lineMap (7 / 2 : ℂ) (ports i) s ≠ AffineMap.lineMap (9 / 2 : ℂ) 5 t := by
  apply split_spokes_ne separatingCoordinate (by norm_num [separatingCoordinate])
    _ (by norm_num [separatingCoordinate]) hs ht
  fin_cases i <;> norm_num [separatingCoordinate, ports]

example (i : Fin 3) {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : AffineMap.lineMap (7 / 2 : ℂ) (ports i) s =
      AffineMap.lineMap (7 / 2 : ℂ) (9 / 2 : ℂ) t) : s = 0 ∧ t = 0 := by
  apply split_connector_contact separatingCoordinate (by norm_num [separatingCoordinate])
    _ hs ht heq
  fin_cases i <;> norm_num [separatingCoordinate, ports]

end CslibFrontierTests.PolygonalRestriction
