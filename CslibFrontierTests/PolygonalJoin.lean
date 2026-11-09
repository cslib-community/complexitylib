/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

import CslibFrontier.Foundations.Geometry.Polygonal.Join
import CslibFrontier.Foundations.Geometry.Polygonal.Segment
import Mathlib.Tactic.FinCases

/-!
One-point route joins tested at all real segment parameters. A prepend followed by an
append constructs an actual simple triangular loop. Extending that already closed loop,
adding a zero-length segment, and retracing an old segment are rejected.
-/

namespace CslibFrontierTests.PolygonalJoin

open Cslib.Polygonal

private def elbow : Route := Route.prepend 0 (Route.line 1 Complex.I)

private theorem elbow_simple : elbow.IsSimple := by
  apply (Route.isSimple_line (by intro h; have := congrArg Complex.re h; norm_num at this)).prepend
    (by norm_num)
  intro j s t hs ht heq
  rw [Route.eval_line] at heq
  have hr := congrArg Complex.re heq
  have hi := congrArg Complex.im heq
  norm_num [AffineMap.lineMap_apply_module, Complex.smul_re, Complex.smul_im] at hr hi
  left
  refine ⟨by linarith, ?_⟩
  have hj : j = 0 := Subsingleton.elim (α := Fin 1) _ _
  simp [Route.AtEnd, Route.position, hj, show t = 0 by linarith]

private def triangle : Route := elbow.append 0

private theorem triangle_simple : triangle.IsSimple := by
  apply elbow_simple.append (by change Complex.I ≠ 0; exact Complex.I_ne_zero)
  intro i s t hs ht heq
  fin_cases i
  · change AffineMap.lineMap (0 : ℂ) 1 s = AffineMap.lineMap Complex.I 0 t at heq
    have hr := congrArg Complex.re heq
    have hi := congrArg Complex.im heq
    norm_num [AffineMap.lineMap_apply_module, Complex.smul_re, Complex.smul_im] at hr hi
    right
    refine ⟨?_, by linarith⟩
    simp [Route.AtEnd, Route.position, show s = 0 by linarith]
  · change AffineMap.lineMap (1 : ℂ) Complex.I s = AffineMap.lineMap Complex.I 0 t at heq
    have hr := congrArg Complex.re heq
    have hi := congrArg Complex.im heq
    norm_num [AffineMap.lineMap_apply_module, Complex.smul_re, Complex.smul_im] at hr hi
    left
    refine ⟨?_, by linarith⟩
    norm_num [Route.AtEnd, Route.position, elbow, Route.segments, Route.prepend, Route.line]
    linarith

-- Each operation adds exactly one segment; an actual closed loop needs three here.
example : triangle.segments = 3 := rfl

example : triangle.start = triangle.finish := rfl

example : triangle.IsSimple := triangle_simple

-- The original middle segment and both new end germs keep their exact orientations.
example (t : ℝ) : elbow.eval (1 : Fin 2) t = AffineMap.lineMap 1 Complex.I t := by
  exact (Route.eval_prepend_succ 0 (Route.line 1 Complex.I) 0 t).trans (Route.eval_line _ _ _ _)

example : triangle.germ false = 1 ∧ triangle.germ true = Complex.I := by
  change (1 : ℂ) - 0 = 1 ∧ Complex.I - 0 = Complex.I
  simp

-- Closed old routes cannot be silently interpreted as simple tails or prefixes.
example (a : ℂ) : ¬(Route.prepend a triangle).IsSimple := by
  intro h
  exact h.prepend_start_ne_finish rfl

example (b : ℂ) : ¬(triangle.append b).IsSimple := by
  intro h
  exact h.append_start_ne_finish rfl

example : ¬(Route.prepend 1 (Route.line 1 Complex.I)).IsSimple := by
  intro h
  exact h.prepend_ne rfl

example : ¬((Route.line 1 Complex.I).append Complex.I).IsSimple := by
  intro h
  exact h.append_ne rfl

-- Returning along a positive-length part of an existing segment is also invalid.
example : ¬(Route.prepend (1 : ℂ) (Route.line 0 2)).IsSimple := by
  intro h
  have hsame := h 0 1 (1 / 2) (1 / 4) (by constructor <;> norm_num)
    (by constructor <;> norm_num) (by
      change AffineMap.lineMap (1 : ℂ) 0 (1 / 2 : ℝ) =
        AffineMap.lineMap (0 : ℂ) 2 (1 / 4 : ℝ)
      apply Complex.ext <;> norm_num [AffineMap.lineMap_apply_module])
  rcases hsame with h | ⟨h, _⟩ | ⟨h, _⟩ <;>
    norm_num [Route.position, Route.AtEnd, Route.segments, Route.prepend, Route.line] at h

end CslibFrontierTests.PolygonalJoin
