/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Realization.Basic

/-!
# Empty geometric sectors of a literal clockwise realization

The inverse rotation successor is the next counterclockwise outgoing germ. The open
sector between these germs contains no other incident germ, at every finite degree.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

/-- Literal clockwise realization makes the inverse-rotation sector empty. -/
theorem Realizes.not_sbtw_inverse_rotate {G : Graph} {D : PolygonalDrawing G}
    {r : RotationSystem G} (hR : D.Realizes r) (d e : Dart G)
    (hvertex : e.vertex = d.vertex) (hed : e ≠ d) (heprev : e ≠ r.rotate.symm d) :
    ¬sbtw (D.direction d) (D.direction e) (D.direction (r.rotate.symm d)) := by
  classical
  let a := r.rotate.symm d
  have hrotate : r.rotate a = d := r.rotate.apply_symm_apply d
  have hav : a.vertex = d.vertex := by rw [← hrotate, r.vertex_rotate]
  by_cases had : a = d
  · rw [show r.rotate.symm d = d from had]
    exact sbtw_irrefl_left_right
  have hdist : r.rotationDistance a d = 1 := by
    apply r.rotationDistance_eq a d hav 1
    · simpa only [pow_one] using hrotate
    · intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simpa only [pow_zero, Equiv.Perm.one_apply] using had
  have hinterval : r.rotationInterval a d = {d} := by
    simp [RotationSystem.rotationInterval, hdist, hrotate]
  intro h
  have hmem := (hR.clockwise a e d (hav.trans hvertex.symm) hvertex
    (Ne.symm heprev) hed had).mp h
  rw [hinterval, Finset.mem_singleton] at hmem
  exact hed hmem

end Cslib.Complexity.Graph.PolygonalDrawing
