/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.PolygonalDrawing
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Star
public import Complexity.Foundations.Geometry.Polygonal.Segment

/-!
# Genuine polygonal embeddings of stars of arbitrary degree

The center is at zero and leaf `i` is at `(i+1,1)`. Every edge is its actual straight
segment. The segment-intersection proof has no degree restriction and includes the nullary
star. This module proves embedding; clockwise realization is a separate order statement.

## Main results

* `Cslib.Complexity.Graph.PolygonalDrawing.star_isEmbedding`: arbitrary-arity geometric stars.
-/

public section

namespace Cslib.Complexity.Graph.PolygonalDrawing

open RotationSystem Polygonal

/-- The center at zero, and the `i`-th leaf at `(i+1,1)`. -/
@[expose] def starPoint (n v : ℕ) : ℂ := if v = n then 0 else ⟨(v : ℝ) + 1, 1⟩

/-- The explicit straight-segment drawing of the existing indexed star of any arity. -/
@[expose] def star (n : ℕ) : PolygonalDrawing (starGraph n) where
  vertex := starPoint n
  route := fun e => Route.line ⟨(e.val : ℝ) + 1, 1⟩ 0
  endpoint_eq := by
    intro e b
    let i : Fin n := ⟨e.val, by simpa [starGraph] using e.isLt⟩
    have he : (e, b) = starDartEquiv n (i, b) := rfl
    rw [he, vertex_starDartEquiv]
    cases b
    · have hi : i.val ≠ n := Nat.ne_of_lt i.isLt
      simp [Route.endpoint, starPoint, hi, i]
    · simp [Route.endpoint, starPoint]

private theorem star_eval (n : ℕ) (e : Fin (starGraph n).2.length)
    (i : Fin ((star n).route e).segments) (t : ℝ) :
    ((star n).route e).eval i t = (1 - t) • (⟨(e.val : ℝ) + 1, 1⟩ : ℂ) := by
  have hi : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
  subst i
  change AffineMap.lineMap _ (0 : ℂ) t = _
  rw [AffineMap.lineMap_apply_module, smul_zero, add_zero]
  rfl

private theorem star_endpoint (n : ℕ) (e : Fin (starGraph n).2.length) (b : Bool) :
    Dart.vertex (G := starGraph n) (e, b) = if b then n else e.val := by
  let i : Fin n := ⟨e.val, by simpa [starGraph] using e.isLt⟩
  exact vertex_starDartEquiv i b

/-- The actual straight-segment star drawing is an embedding for every finite arity.
Distinct edges meet only at their center, including when the degree is greater than four. -/
theorem star_isEmbedding (n : ℕ) : (star n).IsEmbedding where
  vertices_injective := by
    intro u _ v _ h
    change starPoint n u = starPoint n v at h
    by_cases hu : u = n <;> by_cases hv : v = n
    · exact hu.trans hv.symm
    · have hi := congrArg Complex.im h
      simp [starPoint, hu, hv] at hi
    · have hi := congrArg Complex.im h
      simp [starPoint, hu, hv] at hi
    · have hr := congrArg Complex.re h
      simp only [starPoint, hu, hv, ↓reduceIte, add_left_inj] at hr
      exact_mod_cast hr
  simple := by
    intro e
    apply Route.isSimple_line
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
  vertex_contacts := by
    intro e i t _ v _ h
    rw [star_eval] at h
    change (1 - t) • (⟨(e.val : ℝ) + 1, 1⟩ : ℂ) = starPoint n v at h
    have hi := congrArg Complex.im h
    have hr := congrArg Complex.re h
    have hi0 : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
    by_cases hv : v = n
    · have ht : t = 1 := by
        simp only [starPoint, hv, ↓reduceIte, Complex.smul_im, smul_eq_mul, mul_one,
          Complex.zero_im] at hi
        linarith
      refine ⟨true, ?_, ?_⟩
      · simp [Route.AtEnd, Route.position, star, Route.line, hi0, ht]
      · simpa only [star_endpoint, ↓reduceIte] using hv.symm
    · have ht : t = 0 := by
        simp only [starPoint, hv, ↓reduceIte, Complex.smul_im, smul_eq_mul, mul_one] at hi
        linarith
      have he : e.val = v := by
        simp only [ht, sub_zero, one_smul, starPoint, hv, ↓reduceIte,
          add_left_inj] at hr
        exact_mod_cast hr
      refine ⟨false, ?_, ?_⟩
      · simp [Route.AtEnd, Route.position, hi0, ht]
      · simpa only [star_endpoint, Bool.false_eq_true, ↓reduceIte] using he
  edge_contacts := by
    intro e f hef i j s t _ _ h
    rw [star_eval, star_eval] at h
    have hi := congrArg Complex.im h
    have hr := congrArg Complex.re h
    simp only [Complex.smul_im, smul_eq_mul, mul_one] at hi
    have hst : s = t := by linarith
    simp only [Complex.smul_re, smul_eq_mul, ← hst] at hr
    have hprod : (1 - s) * ((e.val : ℝ) - (f.val : ℝ)) = 0 := by nlinarith
    have hs : s = 1 := by
      rcases mul_eq_zero.mp hprod with h | h
      · linarith
      · exact False.elim (hef (Fin.ext (by exact_mod_cast sub_eq_zero.mp h)))
    have hi0 : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
    have hj0 : j.val = 0 := by have := j.isLt; change j.val < 1 at this; omega
    refine ⟨true, true, ?_, ?_, ?_⟩
    · simp [Route.AtEnd, Route.position, star, Route.line, hi0, hs]
    · simp [Route.AtEnd, Route.position, star, Route.line, hj0, ← hst, hs]
    · simp only [star_endpoint, ↓reduceIte]

end Cslib.Complexity.Graph.PolygonalDrawing
