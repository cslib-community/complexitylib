/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.OnlineLearning.FTRL

/-! Checks for follow the regularized leader on `K = [-1, 1] ⊆ ℝ`. They cover quadratic growth and
strong convexity of the Euclidean regularizer, a concrete FTRL run (lazy projection with the
losses `y ↦ y`), a sequence that is not an FTRL run, uniqueness and existence, and instances of
the strongly convex, tuned, linearized and lazy-projection regret bounds, showing that their
hypotheses are satisfiable. -/

namespace CslibFrontierTests.FTRL

open Finset Real Set Cslib Cslib.MachineLearning.OnlineLearning.OCO
open scoped RealInnerProductSpace

/-- The decision set `[-1, 1]`. -/
abbrev K : Set ℝ := Icc (-1) 1

theorem K_nonempty : K.Nonempty := ⟨0, by norm_num⟩

theorem K_isComplete : IsComplete K := isClosed_Icc.isComplete

theorem K_convex : Convex ℝ K := convex_Icc _ _

theorem real_inner (a b : ℝ) : ⟪a, b⟫ = a * b := by
  rw [RCLike.inner_apply, conj_trivial, mul_comm]

/-! ### Strong convexity -/

/-- `y ^ 2 = 2 / 2 * ‖y - 0‖ ^ 2` is `2`-strongly convex. -/
theorem strongConvexOn_sq : StrongConvexOn K 2 fun y : ℝ => y ^ 2 := by
  convert strongConvexOn_mul_norm_sub_sq K_convex 2 (0 : ℝ) using 1
  funext y
  rw [sub_zero, Real.norm_eq_abs, sq_abs]
  ring

/-- Quadratic growth of `y ^ 2` at its minimizer `0`. -/
example {y : ℝ} (hy : y ∈ K) : (0 : ℝ) ^ 2 + 2 / 2 * ‖y - 0‖ ^ 2 ≤ y ^ 2 :=
  strongConvexOn_sq.add_le_of_isMinOn (by norm_num)
    (isMinOn_iff.mpr fun y _ => by nlinarith [sq_nonneg y]) hy

/-- The stability bound for `y ^ 2` perturbed by `y ↦ y` (`L = 1`): at most `1 / 4`. -/
example {y : ℝ} (hy : y ∈ K) : (0 : ℝ) ^ 2 + 0 - (y ^ 2 + y) ≤ 1 ^ 2 / (2 * 2) :=
  strongConvexOn_sq.sub_le_of_isMinOn two_pos (by norm_num)
    (isMinOn_iff.mpr fun y _ => by nlinarith [sq_nonneg y]) hy (ℓ := fun y => y)
    (by rw [one_mul, zero_sub, norm_neg]; exact neg_le_abs y)

/-- A linear function is not `1`-strongly convex. -/
example : ¬ StrongConvexOn K 1 fun y : ℝ => y := fun h => by
  have := h.2 (show (-1 : ℝ) ∈ K by norm_num) (show (1 : ℝ) ∈ K by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  norm_num at this

/-! ### A concrete FTRL run -/

/-- The Euclidean regularizer `‖y - 0‖ ^ 2 / (2 η)` with `η = 1`. -/
noncomputable abbrev ψ : ℝ → ℝ := fun y => ‖y - 0‖ ^ 2 / (2 * 1)

/-- The linear losses `y ↦ ⟪1, y⟫ = y`. -/
noncomputable abbrev ℓ : ℕ → ℝ → ℝ := fun _ y => ⟪(1 : ℝ), y⟫

/-- The lazy-projection run `x t = Π_K (0 - ∑ s < t, 1) = Π_K (-t)`. -/
noncomputable abbrev xrun : ℕ → ℝ := fun t =>
  metricProjection K (0 - (1 : ℝ) • ∑ _s ∈ range t, (1 : ℝ))

theorem hψ : StrongConvexOn K 1 ψ := by
  convert strongConvexOn_mul_norm_sub_sq K_convex 1 (0 : ℝ) using 1
  funext y
  ring

theorem hℓ (t : ℕ) : ConvexOn ℝ K (ℓ t) := by
  convert convexOn_id K_convex using 1
  funext y
  change ⟪(1 : ℝ), y⟫ = y
  rw [real_inner, one_mul]

theorem isFTRL_xrun : IsFTRL K ψ ℓ xrun :=
  (isFTRL_euclidean_iff (x₀ := 0) K_nonempty K_isComplete K_convex one_pos (fun _ => 1) xrun).mpr
    fun _ => rfl

/-- The first point is the minimizer `0` of the regularizer. -/
example : xrun 0 = 0 := by
  simp only [xrun, range_zero, sum_empty, smul_zero, sub_zero]
  exact metricProjection_eq_self K_isComplete K_convex (by norm_num)

/-- After one loss `y ↦ y`, FTRL plays `-1`, the minimizer of `y ^ 2 / 2 + y` on `[-1, 1]`. -/
example : xrun 1 = -1 := by
  simp only [xrun, range_one, sum_singleton, one_smul, zero_sub]
  exact metricProjection_eq_self K_isComplete K_convex (by norm_num)

/-- Staying at `0` is not an FTRL run: after the loss `y ↦ y`, `-1` has a smaller objective. -/
example : ¬ IsFTRL K ψ ℓ fun _ => 0 := fun h => by
  have := h.objective_le 1 (u := -1) (by norm_num)
  simp only [ftrlObjective_succ, ftrlObjective_zero, ψ, ℓ, real_inner] at this
  norm_num at this

/-- With a strongly convex regularizer and convex losses, `xrun` is the only FTRL run. -/
example {x : ℕ → ℝ} (hx : IsFTRL K ψ ℓ x) : x = xrun :=
  hx.unique isFTRL_xrun hψ one_pos hℓ

/-- The regret equality holds for every sequence. -/
example (u : ℝ) (T : ℕ) := ftrl_regret_eq ψ ℓ (fun _ => 0) u T

/-! ### Regret bounds -/

/-- The strongly convex regret bound applies to the run: regret at most `ψ u - ψ (x 0) + T / 2`. -/
example {u : ℝ} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (ℓ t (xrun t) - ℓ t u) ≤
      ψ u - ψ (xrun 0) + ∑ _t ∈ range T, (1 : ℝ) ^ 2 / (2 * 1) :=
  isFTRL_xrun.regret_le hψ one_pos hℓ (L := fun _ => 1)
    (fun t y _ => by simp only [ℓ, real_inner, one_mul]; exact le_norm_self _) hu T

/-- Be the leader for the run. -/
example {u : ℝ} (hu : u ∈ K) (T : ℕ) :
    ψ (xrun 0) + ∑ t ∈ range T, ℓ t (xrun (t + 1)) ≤ ψ u + ∑ t ∈ range T, ℓ t u :=
  isFTRL_xrun.add_sum_le hu T

/-- The tuned bound is nonvacuous: with `R y = y ^ 2 / 2` (`1`-strongly convex, oscillation at
most `1 = D ^ 2` on `K`) and the losses `y ↦ y`, an FTRL run exists and has regret at most
`√(2 T)` against every `u ∈ K`. -/
example {T : ℕ} (hT : 0 < T) :
    ∃ x : ℕ → ℝ, ∀ u ∈ K, ∑ t ∈ range T, (x t - u) ≤ 1 * 1 * √(2 * T / 1) := by
  obtain ⟨x, hx⟩ := exists_isFTRL (K := K)
    (ψ := fun y => y ^ 2 / 2 / (1 / 1 * √(2 * 1 / T))) (ℓ := fun _ y => y) isCompact_Icc
    K_nonempty (by fun_prop) (fun _ => by fun_prop)
  have hR : StrongConvexOn K 1 fun y : ℝ => y ^ 2 / 2 := by
    convert strongConvexOn_mul_norm_sub_sq K_convex 1 (0 : ℝ) using 1
    funext y
    rw [sub_zero, Real.norm_eq_abs, sq_abs]
    ring
  refine ⟨x, fun u hu => ?_⟩
  exact hx.regret_le_sqrt (R := fun y => y ^ 2 / 2) (σ := 1) (D := 1) (L := 1) one_pos one_pos
    one_pos hT hR (fun y hy z _ => by nlinarith [hy.1, hy.2, sq_nonneg z])
    (fun _ => convexOn_id K_convex) (fun t y _ => by simp only [one_mul]; exact le_norm_self _) hu

/-- FTRL with linearized losses for `f t y = y ^ 2`, whose derivative at `x t` is
`y ↦ 2 x t y`: any run on the linearized losses has the strongly convex regret bound. -/
example {x : ℕ → ℝ} (hx : IsFTRL K ψ (fun t y => ((2 * x t) • ContinuousLinearMap.id ℝ ℝ) y) x)
    {u : ℝ} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (x t ^ 2 - u ^ 2) ≤
      ψ u - ψ (x 0) + ∑ t ∈ range T, ‖(2 * x t) • ContinuousLinearMap.id ℝ ℝ‖ ^ 2 / (2 * 1) :=
  hx.regret_le_of_subgradient (f := fun _ y => y ^ 2) hψ one_pos
    (fun t y _ => by
      simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
      nlinarith [sq_nonneg (y - x t)]) hu T

/-! ### Lazy projected online gradient descent -/

/-- With constant gradient `1` and `η = 1` from `0`, lazy OGD first plays `0`, then `Π (-1) = -1`.
-/
example : lazyOGD K 1 (fun _ _ => 1) 0 1 = -1 := by
  rw [lazyOGD_def, lazyOGDState_succ, lazyOGDState_zero, one_smul, zero_sub]
  exact metricProjection_eq_self K_isComplete K_convex (by norm_num)

/-- Lazy OGD on the quadratic losses `y ^ 2` with gradients `2 x` chosen at the played points. -/
example {u : ℝ} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (lazyOGD K 1 (fun _ x => 2 * x) 0 t ^ 2 - u ^ 2) ≤
      ‖u - 0‖ ^ 2 / (2 * 1) + 1 / 2 * ∑ t ∈ range T, ‖2 * lazyOGD K 1 (fun _ x => 2 * x) 0 t‖ ^ 2 :=
  lazyOGD_regret_le (f := fun _ y => y ^ 2) K_nonempty K_isComplete K_convex one_pos
    (fun _ x _ y _ => by simp only [real_inner]; nlinarith [sq_nonneg (y - x)]) hu T

/-- The tuned bound `G D √T` for the losses `y ↦ y` with `G = D = 1`. -/
example {u : ℝ} (hu : u ∈ K) {T : ℕ} (hT : 0 < T) :
    ∑ t ∈ range T, (lazyOGD K (1 / (1 * √(T : ℝ))) (fun _ _ => 1) 0 t - u) ≤ 1 * 1 * √(T : ℝ) :=
  lazyOGD_regret_le_fixed (f := fun _ x => x) K_nonempty K_isComplete K_convex one_pos one_pos
    (fun _ _ _ => by norm_num) (fun _ x _ y _ => by simp only [real_inner]; linarith) hu
    (by rw [sub_zero, Real.norm_eq_abs, abs_le]; exact ⟨hu.1, hu.2⟩) hT

end CslibFrontierTests.FTRL
