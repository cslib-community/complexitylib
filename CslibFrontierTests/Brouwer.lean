/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Analysis.Brouwer
import CslibFrontier.Foundations.Analysis.Brouwer.Simplex

/-! Brouwer's fixed-point theorem on the cube and the weak approximation for Lipschitz maps. The
file applies them to concrete maps and gives a translation without fixed points, showing that the
hypothesis that `f` maps the cube into itself is needed. Brouwer's theorem for products of
simplices, applied to the rotation of a triangle, finds its barycentre. -/

namespace CslibFrontierTests.Brouwer

open Set Cslib.Brouwer

/-- Halving the distance to the centre of the square `[0, 1] ^ 2`. -/
private noncomputable def halve (x : Fin 2 → ℝ) : Fin 2 → ℝ := fun i => (x i + 1 / 2) / 2

private theorem halve_mapsTo : MapsTo halve (Icc 0 1) (Icc 0 1) := fun x hx =>
  ⟨fun i => by have := hx.1 i; simp only [halve, Pi.zero_apply] at this ⊢; linarith,
    fun i => by have := hx.2 i; simp only [halve, Pi.one_apply] at this ⊢; linarith⟩

private theorem halve_lipschitz : LipschitzOnWith (1 / 2) halve (Icc 0 1) :=
  LipschitzOnWith.of_dist_le_mul fun x _ y _ => by
    refine (dist_pi_le_iff (by positivity)).mpr fun i => ?_
    have := dist_le_pi_dist x y i
    simp only [halve, Real.dist_eq] at this ⊢
    rw [show (x i + 1 / 2) / 2 - (y i + 1 / 2) / 2 = (x i - y i) / 2 by ring, abs_div,
      abs_two]
    push_cast
    linarith

-- A weak `3 / (2 N)`-approximate fixed point on the grid `p / N`.
example (N : ℕ) (hN : 0 < N) : ∃ p : Fin 2 → ℕ, (∀ i, p i ≤ N) ∧
    dist (halve fun i => (p i : ℝ) / N) (fun i => (p i : ℝ) / N) ≤ ((1 / 2 : NNReal) + 1) / N :=
  exists_dist_le_of_lipschitzOnWith halve_mapsTo halve_lipschitz hN

-- An exact fixed point, here the centre.
example : ∃ x ∈ Icc (0 : Fin 2 → ℝ) 1, Function.IsFixedPt halve x :=
  exists_isFixedPt_cube halve_mapsTo halve_lipschitz.continuousOn

-- The colouring induced by `halve` satisfies the Sperner boundary condition.
example : Cslib.Sperner.IsHypergridSperner (fun _ => 4) (coloring halve 4) :=
  isHypergridSperner_coloring halve_mapsTo (by decide)

-- Brouwer in dimension zero: the cube is a point.
example (f : (Fin 0 → ℝ) → Fin 0 → ℝ) : ∃ x ∈ Icc (0 : Fin 0 → ℝ) 1, Function.IsFixedPt f x :=
  exists_isFixedPt_cube (fun _ _ => ⟨fun i => i.elim0, fun i => i.elim0⟩)
    (continuousOn_of_forall_continuousAt fun _ _ => (continuous_of_discreteTopology).continuousAt)

/-! ### The cube must be mapped into itself -/

/-- Translation by `1`, which moves the cube off itself. -/
private def shift (x : Fin 1 → ℝ) : Fin 1 → ℝ := fun i => x i + 1

example : ¬MapsTo shift (Icc 0 1) (Icc 0 1) := fun h => by
  have := (h (⟨zero_le_one, le_rfl⟩ : (1 : Fin 1 → ℝ) ∈ Icc 0 1)).2 0
  simp only [shift, Pi.one_apply] at this
  linarith

example : ContinuousOn shift (Icc 0 1) :=
  (continuous_pi fun i => (continuous_apply i).add continuous_const).continuousOn

example : ∀ x, ¬Function.IsFixedPt shift x := fun x h => by
  have := congrFun h 0
  simp only [shift] at this
  linarith

/-! ### Products of simplices -/

/-- Rotating the vertices of the triangle `{p : Fin 3 → ℝ | p ≥ 0, ∑ p = 1}`, as a product of one
simplex. -/
private def rotate (p : Unit → Fin 3 → ℝ) : Unit → Fin 3 → ℝ := fun u k => p u (k + 1)

-- The only fixed point of the rotation is the barycentre, so Brouwer's theorem finds it.
example : ∃ p : Unit → Fin 3 → ℝ, p () = fun _ => 1 / 3 := by
  obtain ⟨p, hp, hfix⟩ := exists_isFixedPt_pi_simplex (f := rotate)
    (fun p hp u => ⟨fun k => (hp u).1 (k + 1),
      (Equiv.sum_comp (Equiv.addRight (1 : Fin 3)) (p u)).trans (hp u).2⟩)
    (continuous_pi fun u => continuous_pi fun k =>
      (continuous_apply (k + 1)).comp (continuous_apply u)).continuousOn
  have h : ∀ k, p () k = p () (k + 1) := fun k => (congrFun (congrFun hfix ()) k).symm
  have hsum := (hp ()).2
  rw [Fin.sum_univ_three] at hsum
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
    show (2 : Fin 3) + 1 = 0 from rfl] at h0 h1 h2
  refine ⟨p, funext fun k => ?_⟩
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith

end CslibFrontierTests.Brouwer
