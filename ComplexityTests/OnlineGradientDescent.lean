/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Analysis.Convex.FirstOrder
import Complexity.MachineLearning.OnlineLearning.OnlineGradientDescent

/-! Checks for online gradient descent on `K = [-1, 1] ⊆ ℝ`: concrete metric projections and
iterates, maps that are not Pythagorean projections, the first-order convexity bridges on `x ^ 2`,
and instances of the regret bounds of Hazan Theorems 3.1 and 3.3 and Zinkevich Theorem 1 for
linear and quadratic losses, showing that their hypotheses are satisfiable. -/

namespace ComplexityTests.OnlineGradientDescent

open Finset Real Set Cslib Cslib.MachineLearning.OnlineLearning.OCO
open scoped RealInnerProductSpace

/-- The decision set `[-1, 1]`. -/
abbrev K : Set ℝ := Icc (-1) 1

theorem K_nonempty : K.Nonempty := ⟨0, by norm_num⟩

theorem K_isComplete : IsComplete K := isClosed_Icc.isComplete

theorem K_convex : Convex ℝ K := convex_Icc _ _

theorem real_inner (a b : ℝ) : ⟪a, b⟫ = a * b := by
  rw [RCLike.inner_apply, conj_trivial, mul_comm]

theorem K_diam : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ 2 := fun x hx y hy => by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem K_proj : IsPythagoreanProjection K (metricProjection K) :=
  isPythagoreanProjection_metricProjection K_nonempty K_isComplete K_convex

/-! ### Metric projection and iterates -/

/-- The projection of `2` onto `[-1, 1]` is `1`. -/
example : metricProjection K 2 = 1 := by
  rw [metricProjection_eq_iff K_nonempty K_isComplete K_convex (by norm_num)]
  intro z hz
  rw [real_inner]
  linarith [hz.2]

/-- Points of `[-1, 1]` are fixed. -/
example : metricProjection K (1 / 2) = 1 / 2 :=
  metricProjection_eq_self K_nonempty K_isComplete K_convex (by norm_num)

/-- With constant gradient `1` and step size `1` from `0`, the first iterate is `Π (-1) = -1`. -/
example : ogd (metricProjection K) (fun _ => 1) (fun _ _ => 1) 0 1 = -1 := by
  simp only [ogd_succ, ogd_zero, one_smul, zero_sub]
  exact metricProjection_eq_self K_nonempty K_isComplete K_convex (by norm_num)

/-- The identity does not map into `[-1, 1]`. -/
example : ¬ IsPythagoreanProjection K id := fun h => by
  have := h.mem 2
  norm_num at this

/-- A constant map into `[-1, 1]` violates the Pythagorean inequality. -/
example : ¬ IsPythagoreanProjection K (fun _ => -1) := fun h => by
  have := h.norm_sub_le 1 1 (by norm_num)
  norm_num at this

/-- The bound `∑ t < T + 1, 1 / √(t + 1) ≤ 2 √(T + 1) - 1` is tight at `T = 0`. -/
example : ∑ t ∈ range 1, 1 / √((t : ℝ) + 1) = 2 * √((0 : ℕ) + 1) - 1 := by
  norm_num

/-! ### First-order convexity bridges -/

/-- The tangent line of `x ^ 2` at `x` lies below the parabola. -/
example (x y : ℝ) : x ^ 2 + ⟪2 * x, y - x⟫ ≤ y ^ 2 := by
  have hd : HasGradientAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).hasGradientAt'
  exact (Even.convexOn_pow even_two).add_inner_le_of_hasGradientAt (mem_univ x) (mem_univ y) hd

/-- `x ^ 2` is `2`-strongly convex, and the strongly convex first-order bound holds for it (with
equality). -/
example (x y : ℝ) : x ^ 2 + ⟪2 * x, y - x⟫ + 2 / 2 * ‖y - x‖ ^ 2 ≤ y ^ 2 := by
  have hd : HasGradientAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).hasGradientAt'
  have hsc : StrongConvexOn univ 2 fun x : ℝ => x ^ 2 := by
    refine strongConvexOn_iff_convex.mpr ?_
    have e : (fun x : ℝ => x ^ 2 - 2 / 2 * ‖x‖ ^ 2) = fun _ => 0 := by
      funext x
      rw [Real.norm_eq_abs, sq_abs]
      ring
    rw [e]
    exact convexOn_const 0 convex_univ
  exact hsc.add_inner_add_le_of_hasGradientAt (mem_univ x) (mem_univ y) hd

/-! ### Regret bounds -/

/-- Linear losses `c t * x` with `|c t| ≤ 1`: Hazan's Theorem 3.1 with `D = 2`, `G = 1`. -/
example (c : ℕ → ℝ) (hc : ∀ t, |c t| ≤ 1) {u : ℝ} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (c t * ogd (metricProjection K) (fun t => 2 / (1 * √((t : ℝ) + 1)))
        (fun t _ => c t) 0 t - c t * u) ≤ 3 / 2 * 1 * 2 * √(T : ℝ) :=
  ogd_regret_le_three_halves (f := fun t x => c t * x) K_proj (by norm_num) two_pos one_pos
    K_diam (fun t _ _ => by rw [Real.norm_eq_abs]; exact hc t)
    (fun t x _ y _ => le_of_eq (by rw [real_inner]; ring)) hu T

/-- The same losses with Zinkevich's step sizes `1 / √(t + 1)`. -/
example (c : ℕ → ℝ) (hc : ∀ t, |c t| ≤ 1) {u : ℝ} (hu : u ∈ K) {T : ℕ} (hT : 0 < T) :
    ∑ t ∈ range T, (c t * ogd (metricProjection K) (fun t => 1 / √((t : ℝ) + 1))
        (fun t _ => c t) 0 t - c t * u) ≤ 2 ^ 2 * √(T : ℝ) / 2 + (√(T : ℝ) - 1 / 2) * 1 ^ 2 :=
  ogd_regret_le_zinkevich (f := fun t x => c t * x) K_proj (by norm_num) K_diam
    (fun t _ _ => by rw [Real.norm_eq_abs]; exact hc t)
    (fun t x _ y _ => le_of_eq (by rw [real_inner]; ring)) hu hT

/-- Quadratic losses `(x - c t) ^ 2 / 2` with `c t ∈ [-1, 1]` are `1`-strongly convex with
gradients `x - c t` of norm at most `2` on `K`: Hazan's Theorem 3.3 with `α = 1`, `G = 2`. -/
example (c : ℕ → ℝ) (hc : ∀ t, c t ∈ K) {u : ℝ} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, ((ogd (metricProjection K) (fun t => 1 / (1 * ((t : ℝ) + 1)))
        (fun t x => x - c t) 0 t - c t) ^ 2 / 2 - (u - c t) ^ 2 / 2) ≤
      2 ^ 2 / (2 * 1) * (1 + log T) :=
  ogd_regret_le_log (f := fun t x => (x - c t) ^ 2 / 2) K_proj (by norm_num) one_pos
    (fun t x hx => K_diam x hx (c t) (hc t))
    (fun t x _ y _ => le_of_eq (by rw [real_inner, Real.norm_eq_abs, sq_abs]; ring)) hu T

/-- The strongly convex hypotheses of the last example bound the diameter of `K` by
`2 G / α = 4`. -/
example (c : ℝ) (hc : c ∈ K) {x y : ℝ} (hx : x ∈ K) (hy : y ∈ K) : ‖x - y‖ ≤ 2 * 2 / 1 :=
  norm_sub_le_of_strongConvex (f := fun x => (x - c) ^ 2 / 2) (g := fun x => x - c) one_pos
    (fun x hx => K_diam x hx c hc)
    (fun x _ y _ => le_of_eq (by rw [real_inner, Real.norm_eq_abs, sq_abs]; ring)) hx hy

end ComplexityTests.OnlineGradientDescent
