/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Analysis.InnerProductSpace.MetricProjection
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Online gradient descent

In *online convex optimization* [Zinkevich2003, Hazan2022] a learner repeatedly plays a point
`x t` of a convex set `K` in a real inner product space, after which an adversary reveals a convex
loss `f t : E → ℝ`. The regret against a comparator `u ∈ K` after `T` rounds is
`∑ t < T, (f t (x t) - f t u)`. *Online gradient descent* (`ogd`) [Hazan2022, Algorithm 8] (the
*greedy projection* algorithm of [Zinkevich2003, Algorithm 1]) steps against a subgradient and
projects back onto `K`:

  `x 0 = x₀`, `x (t + 1) = Π_K (x t - η t • grad t (x t))`.

Rounds are indexed from `0`, so the step size `η t` here is the source's `η_{t+1}`. The
subgradient oracle `grad : ℕ → E → E` is an arbitrary function of the round and the query point,
and the losses `f t` are arbitrary. Since OGD is deterministic, an adversary that adapts to the
learner's past points selects nothing it could not have fixed in advance, so these bounds cover
adaptive adversaries. Every bound holds for each comparator `u ∈ K`; taking the maximum over
`u` gives the regret `Regret_T` of [Hazan2022, §3.1].

The projection is any map `proj` satisfying the Pythagorean inequality
`‖proj y - z‖ ≤ ‖y - z‖` for `z ∈ K` and landing in `K` (`IsPythagoreanProjection`). The metric
projection onto a nonempty complete convex set is one
(`isPythagoreanProjection_metricProjection`, [Hazan2022, Theorem 2.1]). The losses enter through
the subgradient inequality `f t x + ⟪grad t x, y - x⟫ ≤ f t y` for `x y ∈ K`, the definition of
convexity with subgradients in [Hazan2022, §2.1]. For differentiable convex losses with
gradients it follows from `ConvexOn.add_inner_le_of_hasGradientAt`. The strongly convex form
`f t x + ⟪grad t x, y - x⟫ + α / 2 * ‖y - x‖ ^ 2 ≤ f t y` follows likewise from
`StrongConvexOn.add_inner_add_le_of_hasGradientAt` (or the `HasGradientWithinAt` variants,
which allow boundary points). `D` bounds the diameter of `K` and `G` the subgradient norms on
`K`.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.OCO.IsPythagoreanProjection`: maps into `K` satisfying
  the Pythagorean inequality.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd`: the iterates of online gradient descent.

## Main results

* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_sum_inner_le`: for nonincreasing positive step
  sizes, `∑ t ≤ T, ⟪grad t (x t), x t - u⟫ ≤ D ^ 2 / (2 η T) + ∑ t ≤ T, η t ‖grad t (x t)‖ ^ 2 / 2`.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_regret_le_three_halves`: with step sizes
  `D / (G √(t + 1))`, regret at most `3 / 2 * G * D * √T` [Hazan2022, Theorem 3.1].
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_regret_le_zinkevich`: with step sizes
  `1 / √(t + 1)`, regret at most `D ^ 2 √T / 2 + (√T - 1 / 2) G ^ 2` [Zinkevich2003, Theorem 1].
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_regret_le_fixed`: with the constant step size
  `D / (G √T)` for a known horizon `T`, regret at most `G * D * √T`.
* `Cslib.MachineLearning.OnlineLearning.OCO.ogd_regret_le_log`: for `α`-strongly convex losses
  and step sizes `1 / (α (t + 1))`, regret at most `G ^ 2 / (2 α) * (1 + log T)`
  [Hazan2022, Theorem 3.3].
* `Cslib.MachineLearning.OnlineLearning.OCO.norm_sub_le_of_strongConvex`: the strongly convex
  hypotheses force `diam K ≤ 2 G / α`.

## References

* [E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed.][Hazan2022]
* [M. Zinkevich, *Online Convex Programming and Generalized Infinitesimal Gradient
  Ascent*][Zinkevich2003]
-/

public section

open Finset Real
open scoped RealInnerProductSpace

namespace Cslib.MachineLearning.OnlineLearning.OCO

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `proj` maps into `K` and satisfies the Pythagorean inequality `‖proj y - z‖ ≤ ‖y - z‖` for
every `z ∈ K`, the only properties of the projection used by online gradient descent. -/
structure IsPythagoreanProjection (K : Set E) (proj : E → E) : Prop where
  mem : ∀ y, proj y ∈ K
  norm_sub_le : ∀ y, ∀ z ∈ K, ‖proj y - z‖ ≤ ‖y - z‖

/-- The metric projection onto a nonempty complete convex set satisfies the Pythagorean inequality
[Hazan2022, Theorem 2.1]. -/
theorem isPythagoreanProjection_metricProjection {K : Set E} (hne : K.Nonempty)
    (hc : IsComplete K) (hK : Convex ℝ K) : IsPythagoreanProjection K (metricProjection K) :=
  ⟨metricProjection_mem hne hc hK, fun y _ hz => norm_metricProjection_sub_le hne hc hK y hz⟩

omit [InnerProductSpace ℝ E] in
/-- Unconstrained gradient descent: the identity is a Pythagorean projection onto the whole
space. Since `Set.univ` has no finite diameter (unless `E` is trivial), and the strongly convex
hypotheses force a finite diameter (`norm_sub_le_of_strongConvex`), only the per-step bound
`ogd_two_mul_inner_le` applies to it nontrivially. -/
theorem isPythagoreanProjection_id : IsPythagoreanProjection (Set.univ : Set E) id :=
  ⟨fun _ => Set.mem_univ _, fun _ _ _ => le_rfl⟩

/-- The iterates of online gradient descent [Hazan2022, Algorithm 8] with projection `proj`, step
sizes `η`, subgradient oracle `grad` and starting point `x₀`:
`x (t + 1) = proj (x t - η t • grad t (x t))`. -/
noncomputable def ogd (proj : E → E) (η : ℕ → ℝ) (grad : ℕ → E → E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | t + 1 => proj (ogd proj η grad x₀ t - η t • grad t (ogd proj η grad x₀ t))

variable {K : Set E} {proj : E → E} {η : ℕ → ℝ} {grad : ℕ → E → E} {x₀ : E}

@[simp] theorem ogd_zero : ogd proj η grad x₀ 0 = x₀ := by
  rw [ogd]

theorem ogd_succ (t : ℕ) :
    ogd proj η grad x₀ (t + 1) =
      proj (ogd proj η grad x₀ t - η t • grad t (ogd proj η grad x₀ t)) := by
  rw [ogd]

theorem ogd_mem (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K) (t : ℕ) :
    ogd proj η grad x₀ t ∈ K := by
  cases t with
  | zero => rwa [ogd_zero]
  | succ t => rw [ogd_succ]; exact hP.mem _

/-- One step of online gradient descent against a comparator `u ∈ K`:
`2 ⟪g, x t - u⟫ ≤ (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / η t + η t ‖g‖ ^ 2` with
`g = grad t (x t)` [Hazan2022, proof of Theorem 3.1]. -/
theorem ogd_two_mul_inner_le (hP : IsPythagoreanProjection K proj) {u : E} (hu : u ∈ K) (t : ℕ)
    (hη : 0 < η t) :
    2 * ⟪grad t (ogd proj η grad x₀ t), ogd proj η grad x₀ t - u⟫ ≤
      (‖ogd proj η grad x₀ t - u‖ ^ 2 - ‖ogd proj η grad x₀ (t + 1) - u‖ ^ 2) / η t +
        η t * ‖grad t (ogd proj η grad x₀ t)‖ ^ 2 := by
  set x := ogd proj η grad x₀ t
  set g := grad t x
  have hstep : ‖ogd proj η grad x₀ (t + 1) - u‖ ^ 2 ≤ ‖x - η t • g - u‖ ^ 2 := by
    rw [ogd_succ]
    exact pow_le_pow_left₀ (norm_nonneg _) (hP.norm_sub_le _ u hu) 2
  have hexp : ‖x - η t • g - u‖ ^ 2 =
      ‖x - u‖ ^ 2 - 2 * η t * ⟪g, x - u⟫ + η t ^ 2 * ‖g‖ ^ 2 := by
    rw [show x - η t • g - u = (x - u) - η t • g by abel, norm_sub_sq_real, norm_smul,
      real_inner_smul_right, real_inner_comm, Real.norm_eq_abs, abs_of_pos hη]
    ring
  rw [div_add' _ _ _ hη.ne', le_div_iff₀ hη]
  nlinarith

/-- The generic bound for online gradient descent with positive nonincreasing step sizes on a set
of diameter at most `D`: against every `u ∈ K`,
`∑ t ≤ T, ⟪grad t (x t), x t - u⟫ ≤ D ^ 2 / (2 η T) + (∑ t ≤ T, η t ‖grad t (x t)‖ ^ 2) / 2`
[Hazan2022, proof of Theorem 3.1]. -/
theorem ogd_sum_inner_le (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K) {D : ℝ}
    (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hη : ∀ t, 0 < η t) (hanti : Antitone η)
    {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range (T + 1), ⟪grad t (ogd proj η grad x₀ t), ogd proj η grad x₀ t - u⟫ ≤
      D ^ 2 / (2 * η T) +
        (∑ t ∈ range (T + 1), η t * ‖grad t (ogd proj η grad x₀ t)‖ ^ 2) / 2 := by
  have hd : ∀ t, ‖ogd proj η grad x₀ t - u‖ ^ 2 ≤ D ^ 2 := fun t =>
    pow_le_pow_left₀ (norm_nonneg _) (hD _ (ogd_mem hP hx₀ t) _ hu) 2
  -- Telescoping, keeping the final distance term.
  have key : ∀ T : ℕ, 2 * ∑ t ∈ range (T + 1),
      ⟪grad t (ogd proj η grad x₀ t), ogd proj η grad x₀ t - u⟫ ≤
      D ^ 2 / η T - ‖ogd proj η grad x₀ (T + 1) - u‖ ^ 2 / η T +
        ∑ t ∈ range (T + 1), η t * ‖grad t (ogd proj η grad x₀ t)‖ ^ 2 := by
    intro T
    induction T with
    | zero =>
      have h := ogd_two_mul_inner_le (x₀ := x₀) (grad := grad) hP hu 0 (hη 0)
      simp only [zero_add, range_one, sum_singleton]
      have : (‖ogd proj η grad x₀ 0 - u‖ ^ 2 - ‖ogd proj η grad x₀ 1 - u‖ ^ 2) / η 0 ≤
          D ^ 2 / η 0 - ‖ogd proj η grad x₀ 1 - u‖ ^ 2 / η 0 := by
        rw [← sub_div]
        exact div_le_div_of_nonneg_right (by linarith [hd 0]) (hη 0).le
      linarith
    | succ T ih =>
      have h := ogd_two_mul_inner_le (x₀ := x₀) (grad := grad) hP hu (T + 1) (hη (T + 1))
      have hinv : 1 / η T ≤ 1 / η (T + 1) :=
        one_div_le_one_div_of_le (hη _) (hanti (Nat.le_succ T))
      rw [sum_range_succ, sum_range_succ (fun t => η t * _)]
      set a := ‖ogd proj η grad x₀ (T + 1) - u‖ ^ 2
      set a' := ‖ogd proj η grad x₀ (T + 1 + 1) - u‖ ^ 2
      have hcomb : D ^ 2 / η T - a / η T + (a - a') / η (T + 1) ≤
          D ^ 2 / η (T + 1) - a' / η (T + 1) := by
        have e1 : D ^ 2 / η T - a / η T = (D ^ 2 - a) * (1 / η T) := by ring
        have e2 : (a - a') / η (T + 1) = a * (1 / η (T + 1)) - a' / η (T + 1) := by ring
        have e3 : D ^ 2 / η (T + 1) = D ^ 2 * (1 / η (T + 1)) := by ring
        rw [e1, e2, e3]
        nlinarith [mul_le_mul_of_nonneg_left hinv (sub_nonneg.mpr (hd (T + 1)))]
      linarith
  have h := key T
  have hpos : 0 ≤ ‖ogd proj η grad x₀ (T + 1) - u‖ ^ 2 / η T :=
    div_nonneg (sq_nonneg _) (hη T).le
  have hηT := hη T
  rw [div_add_div _ _ (by positivity) two_ne_zero, le_div_iff₀ (by positivity)]
  have : D ^ 2 / η T * (2 * η T) = 2 * D ^ 2 := by field_simp
  nlinarith

/-- `∑ t < T + 1, 1 / √(t + 1) ≤ 2 √(T + 1) - 1`. -/
theorem sum_range_one_div_sqrt_succ_le (T : ℕ) :
    ∑ t ∈ range (T + 1), 1 / √((t : ℝ) + 1) ≤ 2 * √((T : ℝ) + 1) - 1 := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    rw [sum_range_succ]
    have hr := sqrt_nonneg ((T : ℝ) + 1)
    set r := √((T : ℝ) + 1)
    set s := √(((T + 1 : ℕ) : ℝ) + 1) with hsdef
    have hr2 : r ^ 2 = (T : ℝ) + 1 := sq_sqrt (by positivity)
    have hs2 : s ^ 2 = r ^ 2 + 1 := by
      rw [hsdef, sq_sqrt (by positivity), hr2]
      push_cast
      ring
    have hs : 0 < s := sqrt_pos.mpr (by positivity)
    have hstep : 1 / s ≤ 2 * (s - r) := by
      rw [div_le_iff₀ hs]
      nlinarith [sq_nonneg (s - r)]
    linarith

/-- Regret through subgradients: for any points `x t ∈ K` and any `u ∈ K`, the subgradient
inequality bounds `∑ t < T, (f t (x t) - f t u)` by `∑ t < T, ⟪grad t (x t), x t - u⟫`. -/
theorem sum_sub_le_sum_inner {f : ℕ → E → ℝ}
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y) {x : ℕ → E}
    (hx : ∀ t, x t ∈ K) {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ ∑ t ∈ range T, ⟪grad t (x t), x t - u⟫ :=
  sum_le_sum fun t _ => by
    have h := hsub t (x t) (hx t) u hu
    rw [← neg_sub (x t) u, inner_neg_right] at h
    linarith

/-- Online gradient descent with step sizes `c / √(t + 1)`: the linearized regret over `T + 1`
rounds is at most `D ^ 2 / (2 c) √(T + 1) + c G ^ 2 (√(T + 1) - 1 / 2)`. -/
theorem ogd_sum_inner_le_sqrt (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K)
    {D G c : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D) (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hc : 0 < c) {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range (T + 1), ⟪grad t (ogd proj (fun t => c / √((t : ℝ) + 1)) grad x₀ t),
        ogd proj (fun t => c / √((t : ℝ) + 1)) grad x₀ t - u⟫ ≤
      D ^ 2 / (2 * c) * √((T : ℝ) + 1) + c * G ^ 2 * (√((T : ℝ) + 1) - 1 / 2) := by
  set η : ℕ → ℝ := fun t => c / √((t : ℝ) + 1) with hηdef
  have hη : ∀ t, 0 < η t := fun t => div_pos hc (sqrt_pos.mpr (by positivity))
  have hanti : Antitone η := by
    intro a b hab
    simp only [hηdef]
    gcongr
  have h := ogd_sum_inner_le (grad := grad) hP hx₀ hD hη hanti hu T
  have h1 : D ^ 2 / (2 * η T) = D ^ 2 / (2 * c) * √((T : ℝ) + 1) := by
    simp only [hηdef]
    field_simp
  have h2 : ∑ t ∈ range (T + 1), η t * ‖grad t (ogd proj η grad x₀ t)‖ ^ 2 ≤
      c * G ^ 2 * ∑ t ∈ range (T + 1), 1 / √((t : ℝ) + 1) := by
    rw [mul_sum]
    refine sum_le_sum fun t _ => ?_
    have hg2 : ‖grad t (ogd proj η grad x₀ t)‖ ^ 2 ≤ G ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hG t _ (ogd_mem hP hx₀ t)) 2
    calc η t * ‖grad t (ogd proj η grad x₀ t)‖ ^ 2 ≤ η t * G ^ 2 :=
          mul_le_mul_of_nonneg_left hg2 (hη t).le
      _ = c * G ^ 2 * (1 / √((t : ℝ) + 1)) := by simp only [hηdef]; ring
  have h3 := sum_range_one_div_sqrt_succ_le T
  have hcG : 0 ≤ c * G ^ 2 := by positivity
  rw [h1] at h
  nlinarith [mul_le_mul_of_nonneg_left h3 hcG]

/-- **Regret of online gradient descent** [Hazan2022, Theorem 3.1]: for losses satisfying the
subgradient inequality with subgradients of norm at most `G` on a set of diameter at most `D`, the
step sizes `D / (G √(t + 1))` give regret at most `3 / 2 * G * D * √T` against every `u ∈ K`. -/
theorem ogd_regret_le_three_halves {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj)
    (hx₀ : x₀ ∈ K) {D G : ℝ} (hD0 : 0 < D) (hG0 : 0 < G) (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y) {u : E} (hu : u ∈ K)
    (T : ℕ) :
    ∑ t ∈ range T, (f t (ogd proj (fun t => D / (G * √((t : ℝ) + 1))) grad x₀ t) - f t u) ≤
      3 / 2 * G * D * √(T : ℝ) := by
  have heta : (fun t : ℕ => D / (G * √((t : ℝ) + 1))) =
      fun t : ℕ => D / G / √((t : ℝ) + 1) := by
    funext t
    rw [div_div]
  rw [heta]
  refine (sum_sub_le_sum_inner hsub (ogd_mem hP hx₀) hu T).trans ?_
  rcases T with _ | T
  · simp only [range_zero, sum_empty, Nat.cast_zero, sqrt_zero, mul_zero, le_refl]
  · have h := ogd_sum_inner_le_sqrt (grad := grad) hP hx₀ hD hG (div_pos hD0 hG0) hu T
    have e : D ^ 2 / (2 * (D / G)) * √((T : ℝ) + 1) +
        D / G * G ^ 2 * (√((T : ℝ) + 1) - 1 / 2) =
        3 / 2 * G * D * √((T : ℝ) + 1) - G * D / 2 := by
      field_simp
      ring
    push_cast
    nlinarith [mul_pos hG0 hD0]

/-- **Zinkevich's regret bound** [Zinkevich2003, Theorem 1]: with step sizes `1 / √(t + 1)`, the
regret after `T ≥ 1` rounds is at most `D ^ 2 √T / 2 + (√T - 1 / 2) G ^ 2`. -/
theorem ogd_regret_le_zinkevich {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj)
    (hx₀ : x₀ ∈ K) {D G : ℝ} (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y) {u : E} (hu : u ∈ K)
    {T : ℕ} (hT : 0 < T) :
    ∑ t ∈ range T, (f t (ogd proj (fun t => 1 / √((t : ℝ) + 1)) grad x₀ t) - f t u) ≤
      D ^ 2 * √(T : ℝ) / 2 + (√(T : ℝ) - 1 / 2) * G ^ 2 := by
  obtain ⟨T, rfl⟩ := Nat.exists_eq_add_of_lt hT
  rw [zero_add]
  refine (sum_sub_le_sum_inner hsub (ogd_mem hP hx₀) hu _).trans ?_
  have h := ogd_sum_inner_le_sqrt (grad := grad) hP hx₀ hD hG one_pos hu T
  push_cast
  linarith

/-- **Fixed step size**: for a known horizon `T ≥ 1`, the constant step size `D / (G √T)` gives
regret at most `G * D * √T`. -/
theorem ogd_regret_le_fixed {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj)
    (hx₀ : x₀ ∈ K) {D G : ℝ} (hD0 : 0 < D) (hG0 : 0 < G) (hD : ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ D)
    (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y) {u : E} (hu : u ∈ K)
    {T : ℕ} (hT : 0 < T) :
    ∑ t ∈ range T, (f t (ogd proj (fun _ => D / (G * √(T : ℝ))) grad x₀ t) - f t u) ≤
      G * D * √(T : ℝ) := by
  refine (sum_sub_le_sum_inner hsub (ogd_mem hP hx₀) hu T).trans ?_
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hs : 0 < √(T : ℝ) := sqrt_pos.mpr hTr
  set c := D / (G * √(T : ℝ)) with hcdef
  have hc : 0 < c := div_pos hD0 (mul_pos hG0 hs)
  obtain ⟨T', hT'⟩ := Nat.exists_eq_add_of_lt hT
  rw [zero_add] at hT'
  have h := ogd_sum_inner_le (grad := grad) (η := fun _ => c) hP hx₀ hD (fun _ => hc)
    (fun _ _ _ => le_rfl) hu T'
  rw [← hT'] at h
  have h2 : ∑ t ∈ range T, c * ‖grad t (ogd proj (fun _ => c) grad x₀ t)‖ ^ 2 ≤
      T * (c * G ^ 2) := by
    calc ∑ t ∈ range T, c * ‖grad t (ogd proj (fun _ => c) grad x₀ t)‖ ^ 2
        ≤ ∑ t ∈ range T, c * G ^ 2 := sum_le_sum fun t _ =>
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (hG t _ (ogd_mem hP hx₀ t)) 2) hc.le
      _ = T * (c * G ^ 2) := by simp only [sum_const, card_range, nsmul_eq_mul]
  have e1 : D ^ 2 / (2 * c) = G * D * √(T : ℝ) / 2 := by
    rw [hcdef]
    field_simp
  have e2 : (T : ℝ) * (c * G ^ 2) = G * D * √(T : ℝ) := by
    calc (T : ℝ) * (c * G ^ 2) =
          (√(T : ℝ) * √(T : ℝ)) * (D / (G * √(T : ℝ)) * G ^ 2) := by
          rw [mul_self_sqrt hTr.le]
      _ = G * D * √(T : ℝ) := by field_simp
  rw [e1] at h
  linarith

/-- The strongly convex hypotheses bound the diameter: if `f` satisfies
`f x + ⟪g x, y - x⟫ + α / 2 * ‖y - x‖ ^ 2 ≤ f y` on `K` with `α > 0` and `‖g x‖ ≤ G` on `K`,
then `‖x - y‖ ≤ 2 G / α` for `x y ∈ K`. -/
theorem norm_sub_le_of_strongConvex {f : E → ℝ} {g : E → E} {G α : ℝ} (hα : 0 < α)
    (hG : ∀ x ∈ K, ‖g x‖ ≤ G)
    (hsc : ∀ x ∈ K, ∀ y ∈ K, f x + ⟪g x, y - x⟫ + α / 2 * ‖y - x‖ ^ 2 ≤ f y)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) : ‖x - y‖ ≤ 2 * G / α := by
  have h1 := hsc x hx y hy
  have h2 := hsc y hy x hx
  rw [norm_sub_rev y x] at h1
  -- `α ‖x - y‖ ^ 2 ≤ -⟪g x, y - x⟫ - ⟪g y, x - y⟫ ≤ 2 G ‖x - y‖`
  have hlow : ∀ z ∈ K, ∀ w : E, -(G * ‖w‖) ≤ ⟪g z, w⟫ := fun z hz w =>
    (neg_le_neg (mul_le_mul_of_nonneg_right (hG z hz) (norm_nonneg w))).trans
      (abs_le.mp (abs_real_inner_le_norm (g z) w)).1
  have hcx := hlow x hx (y - x)
  have hcy := hlow y hy (x - y)
  rw [norm_sub_rev y x] at hcx
  have hsq : α * ‖x - y‖ ^ 2 ≤ 2 * G * ‖x - y‖ := by linarith
  rw [le_div_iff₀ hα]
  rcases (norm_nonneg (x - y)).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    have := (norm_nonneg (g x)).trans (hG x hx)
    linarith
  · nlinarith

/-- **Logarithmic regret for strongly convex losses** [Hazan2022, Theorem 3.3]: if every loss
satisfies `f t x + ⟪grad t x, y - x⟫ + α / 2 * ‖y - x‖ ^ 2 ≤ f t y` on `K` with `α > 0` and the
subgradients have norm at most `G` on `K`, the step sizes `1 / (α (t + 1))` give regret at most
`G ^ 2 / (2 α) * (1 + log T)` against every `u ∈ K`. No separate diameter hypothesis is assumed
(these hypotheses already force `‖x - y‖ ≤ 2 G / α` on `K`, `norm_sub_le_of_strongConvex`). -/
theorem ogd_regret_le_log {f : ℕ → E → ℝ} (hP : IsPythagoreanProjection K proj) (hx₀ : x₀ ∈ K)
    {G α : ℝ} (hα : 0 < α) (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsc : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ + α / 2 * ‖y - x‖ ^ 2 ≤ f t y)
    {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (ogd proj (fun t => 1 / (α * ((t : ℝ) + 1))) grad x₀ t) - f t u) ≤
      G ^ 2 / (2 * α) * (1 + log T) := by
  set η : ℕ → ℝ := fun t => 1 / (α * ((t : ℝ) + 1)) with hηdef
  set x := ogd proj η grad x₀
  have hη : ∀ t, 0 < η t := fun t => by simp only [hηdef]; positivity
  have step : ∀ t : ℕ, 2 * (f t (x t) - f t u) ≤
      α * t * ‖x t - u‖ ^ 2 - α * (t + 1) * ‖x (t + 1) - u‖ ^ 2 +
        G ^ 2 / α * (1 / (t + 1)) := by
    intro t
    have h1 := ogd_two_mul_inner_le (x₀ := x₀) (grad := grad) hP hu t (hη t)
    have h2 := hsc t (x t) (ogd_mem hP hx₀ t) u hu
    rw [← neg_sub (x t) u, inner_neg_right, norm_neg] at h2
    have hg := pow_le_pow_left₀ (norm_nonneg _) (hG t (x t) (ogd_mem hP hx₀ t)) 2
    have e1 : (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / η t =
        α * (t + 1) * (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) := by
      simp only [hηdef]
      field_simp
    have e2 : η t * ‖grad t (x t)‖ ^ 2 ≤ G ^ 2 / α * (1 / (t + 1)) := by
      calc η t * ‖grad t (x t)‖ ^ 2 ≤ η t * G ^ 2 := mul_le_mul_of_nonneg_left hg (hη t).le
        _ = G ^ 2 / α * (1 / (t + 1)) := by simp only [hηdef]; field_simp
    rw [e1] at h1
    nlinarith
  have tele : ∀ T : ℕ, 2 * ∑ t ∈ range T, (f t (x t) - f t u) ≤
      -(α * T * ‖x T - u‖ ^ 2) + G ^ 2 / α * ∑ t ∈ range T, 1 / ((t : ℝ) + 1) := by
    intro T
    induction T with
    | zero => simp only [range_zero, sum_empty, mul_zero, Nat.cast_zero, zero_mul, neg_zero,
        add_zero, le_refl]
    | succ T ih =>
      rw [sum_range_succ, sum_range_succ, mul_add, mul_add]
      have := step T
      push_cast
      linarith
  have hH : ∑ t ∈ range T, 1 / ((t : ℝ) + 1) ≤ 1 + log T := by
    have h := harmonic_le_one_add_log T
    have e : ((harmonic T : ℚ) : ℝ) = ∑ t ∈ range T, 1 / ((t : ℝ) + 1) := by
      rw [harmonic]
      push_cast
      simp only [one_div]
    rw [← e]
    exact_mod_cast h
  have hT := tele T
  have hnn : 0 ≤ α * T * ‖x T - u‖ ^ 2 := by positivity
  have hGα : 0 ≤ G ^ 2 / α := by positivity
  have := mul_le_mul_of_nonneg_left hH hGα
  have e : G ^ 2 / (2 * α) * (1 + log T) = G ^ 2 / α * (1 + log T) / 2 := by ring
  rw [e]
  linarith

end Cslib.MachineLearning.OnlineLearning.OCO
