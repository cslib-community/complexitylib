/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import CslibFrontier.Foundations.Geometry.Polygonal.Germs

/-!
# Distinct outgoing geometric rays in a polygonal embedding

Distinct incident darts of a genuine polygonal embedding have distinct outgoing ray
directions. The proof constructs a small common point when the arguments are equal, then
uses the actual segment contact conditions. The same-edge case treats the two ends of a
loop using route simplicity. There is no degree bound or local-disk assumption.

## Main results

* `Cslib.Complexity.Graph.PolygonalDrawing.IsEmbedding.directions_injective`.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open Polygonal

/-- A polygonal embedding has different outgoing rays at distinct incident darts,
including the two ends of a loop. This follows from segment geometry, not from rotation data. -/
theorem IsEmbedding.directions_injective {G : Graph} {D : PolygonalDrawing G}
    (hD : D.IsEmbedding) (a b : Dart G) (hv : a.vertex = b.vertex)
    (harg : D.direction a = D.direction b) : a = b := by
  by_contra hab
  have harg' : (D.germ a).arg = (D.germ b).arg := Complex.arg_coe_angle_eq_iff.mp harg
  obtain ⟨s, hs, t, ht, hst⟩ := exists_small_smul_eq_of_arg_eq
    (hD.germ_ne_zero a) (hD.germ_ne_zero b) harg' (by norm_num : (0 : ℝ) < 1 / 3)
  have hs' : s ∈ Set.Ioo 0 1 := ⟨hs.1, lt_trans hs.2 (by norm_num)⟩
  have ht' : t ∈ Set.Ioo 0 1 := ⟨ht.1, lt_trans ht.2 (by norm_num)⟩
  have hpoint :
      (D.route a.1).eval ((D.route a.1).endSegment a.2) (Route.endTime a.2 s) =
      (D.route b.1).eval ((D.route b.1).endSegment b.2) (Route.endTime b.2 t) := by
    rw [Route.eval_near_end, Route.eval_near_end, D.endpoint_eq, D.endpoint_eq]
    exact congrArg₂ (· + ·) (congrArg D.vertex hv) hst
  by_cases hedge : a.1 = b.1
  · rcases a with ⟨e, ba⟩
    rcases b with ⟨f, bb⟩
    change e = f at hedge
    subst f
    obtain heq | ⟨ha, -⟩ | ⟨ha, -⟩ := hD.simple e _ _ _ _
      (Route.endTime_mem ba ⟨hs'.1.le, hs'.2.le⟩)
      (Route.endTime_mem bb ⟨ht'.1.le, ht'.2.le⟩) hpoint
    · rw [Route.position_near_end, Route.position_near_end] at heq
      have hn : (1 : ℝ) ≤ (D.route e).segments := by
        exact_mod_cast Nat.le_add_left 1 (D.route e).bends
      cases ba <;> cases bb <;> simp only [Bool.false_eq_true, ↓reduceIte] at heq
      · exact hab rfl
      · linarith [hs.2, ht.2]
      · linarith [hs.2, ht.2]
      · exact hab rfl
    · exact (D.route e).not_atEnd_near_end ba false hs' ha
    · exact (D.route e).not_atEnd_near_end ba true hs' ha
  · obtain ⟨ba, _, ha, _, _⟩ := hD.edge_contacts a.1 b.1 hedge _ _ _ _
      (Route.endTime_mem a.2 ⟨hs'.1.le, hs'.2.le⟩)
      (Route.endTime_mem b.2 ⟨ht'.1.le, ht'.2.le⟩) hpoint
    exact (D.route a.1).not_atEnd_near_end a.2 ba hs' ha

end Cslib.Complexity.Graph.PolygonalDrawing
