/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.Convex.FirstOrder
public import Complexity.Foundations.Analysis.Convex.Strong
public import Complexity.Foundations.Analysis.InnerProductSpace.MetricProjection
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Follow the regularized leader

In online convex optimization a learner plays a point `x t` of a set `K` and then suffers the loss
`ℓ t (x t)`. *Follow the regularized leader* (FTRL) [Orabona2019, Algorithm 7.1]
[Hazan2022, Algorithm 13] plays a minimizer over `K` of a fixed regularizer `ψ` plus the losses
seen so far:

  `x t ∈ argmin_{y ∈ K} ftrlObjective ψ ℓ t y`,  `ftrlObjective ψ ℓ t y = ψ y + ∑ s < t, ℓ s y`.

`IsFTRL K ψ ℓ x` states this for every round. Rounds are indexed from `0`, so `x t` and `ℓ t` are
the source's `x_{t+1}` and `ℓ_{t+1}`, and the regularizer is constant over time (the source's
`ψ_t = ψ`). Minimizers need not be unique, so `IsFTRL` describes a family of runs. They exist
when `K` is compact and nonempty and `ψ` and the losses are continuous on `K`
(`exists_isFTRL`), and the run is unique when `ψ` is `μ`-strongly convex with `μ > 0` and the losses
are convex (`IsFTRL.unique`). `IsFTRL` constrains the realized sequence pointwise, and `x t`
depends only on `ℓ 0, …, ℓ (t - 1)`, so every bound below also holds when an adaptive adversary
chooses `ℓ t` after seeing `x 0, …, x t`. `lazyOGD` constructs such a run explicitly for adaptively
chosen gradients.

The analysis follows [Orabona2019, §7]. The regret equality `ftrl_regret_eq`
[Orabona2019, Lemma 7.1] holds for every sequence. With the minimality of `x T` it gives the
"be the leader" bound `IsFTRL.regret_le_add_sum_sub` [Hazan2022, Lemma 5.3], which bounds the
regret by `ψ u - ψ (x 0)` plus the per-round *stability* terms `ℓ t (x t) - ℓ t (x (t + 1))`.
When `ψ` is `μ`-strongly convex on `K` with `μ > 0` (Mathlib's `StrongConvexOn`, for the ambient
norm; `StrongConvexOn K 0 ψ` is plain convexity, and the bound fails for `μ = 0`) and the losses
are convex with `ℓ t (x t) - ℓ t y ≤ L t * ‖x t - y‖` on `K`, the stability bound for strongly
convex minimizers (`StrongConvexOn.sub_le_of_isMinOn`, the argument of
[Orabona2019, Lemma 7.8]) gives `IsFTRL.regret_le`: for every `u ∈ K`,

  `∑ t < T, (ℓ t (x t) - ℓ t u) ≤ ψ u - ψ (x 0) + ∑ t < T, L t ^ 2 / (2 μ)`.

The norm is the ambient one, so the same statement covers strong convexity with respect to `ℓ¹`,
`ℓ²` or any other norm; `L t` plays the role of the dual norm `‖g t‖⋆` of a subgradient. With
`ψ = R / η` for a `σ`-strongly convex `R` (`σ, η > 0`) this is the constant-learning-rate case of
[Orabona2019, Corollary 7.9] (`IsFTRL.regret_le_div`). If moreover `σ, D, L > 0`, `T ≥ 1`,
`R y - R z ≤ D ^ 2` on `K` and `L t = L`, tuning `η` gives `D L √(2T / σ)`
(`IsFTRL.regret_le_sqrt`). *FTRL with linearized losses* [Orabona2019, §7.3] runs FTRL on the
linear losses `y ↦ g t y` given by subgradients `g t` of convex losses `f t` at `x t`; its regret
on `f` obeys the same bound with `L t = ‖g t‖` (`IsFTRL.regret_le_of_subgradient`, and
`IsFTRL.regret_le_of_hasFDerivWithinAt` for differentiable losses).

In a real inner product space, for a nonempty complete convex `K` and `η > 0`, with the Euclidean
regularizer `‖y - x₀‖ ^ 2 / (2 η)` and linear losses `y ↦ ⟪g t, y⟫`, the FTRL iterate is the
metric projection of `x₀ - η ∑ s < t, g s` onto `K` (`isFTRL_euclidean_iff`). This is lazy
projected online gradient descent, or dual averaging [Hazan2022, §5.4.1]. `lazyOGD` runs it with
gradients `grad t (x t)` chosen at the played points. If they satisfy the subgradient inequality
`f t x + ⟪grad t x, y - x⟫ ≤ f t y` on `K`, `lazyOGD_regret_le` bounds its regret by
`‖u - x₀‖ ^ 2 / (2 η) + η / 2 ∑ t < T, ‖grad t (x t)‖ ^ 2`. If moreover `D, G > 0`,
`‖grad t x‖ ≤ G` on `K`, `‖u - x₀‖ ≤ D` and `T ≥ 1`, then `η = D / (G √T)` gives `G D √T`
(`lazyOGD_regret_le_fixed`), the bound of `ogd_regret_le_fixed` for the agile (greedy-projection)
variant.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.OCO.ftrlObjective`: the regularized cumulative loss
  `ψ y + ∑ s < t, ℓ s y`.
* `Cslib.MachineLearning.OnlineLearning.OCO.IsFTRL`: every `x t` minimizes `ftrlObjective ψ ℓ t`
  over `K`.
* `Cslib.MachineLearning.OnlineLearning.OCO.lazyOGD`: lazy projected online gradient descent.

## Main results

* `Cslib.MachineLearning.OnlineLearning.OCO.ftrl_regret_eq`: the FTRL regret equality
  [Orabona2019, Lemma 7.1].
* `Cslib.MachineLearning.OnlineLearning.OCO.IsFTRL.add_sum_le`: the "be the leader" inequality
  [Hazan2022, Lemma 5.4]; `IsFTRL.regret_le_add_sum_sub` is [Hazan2022, Lemma 5.3].
* `Cslib.MachineLearning.OnlineLearning.OCO.IsFTRL.regret_le`: the regret bound for a strongly
  convex regularizer; `IsFTRL.regret_le_div` and `IsFTRL.regret_le_sqrt` are the learning-rate
  forms [Orabona2019, Corollary 7.9].
* `Cslib.MachineLearning.OnlineLearning.OCO.IsFTRL.regret_le_of_subgradient`: FTRL with
  linearized losses [Orabona2019, §7.3].
* `Cslib.MachineLearning.OnlineLearning.OCO.exists_isFTRL`, `IsFTRL.unique`: existence and
  uniqueness.
* `Cslib.MachineLearning.OnlineLearning.OCO.isFTRL_euclidean_iff`: Euclidean FTRL with linear
  losses is lazy projection [Hazan2022, §5.4.1].
* `Cslib.MachineLearning.OnlineLearning.OCO.lazyOGD_regret_le`,
  `Cslib.MachineLearning.OnlineLearning.OCO.lazyOGD_regret_le_fixed`: regret of lazy projected
  online gradient descent.

## References

* [E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed.][Hazan2022]
* [F. Orabona, *A Modern Introduction to Online Learning*][Orabona2019]
-/

public section

open Finset Real Set
open scoped RealInnerProductSpace

namespace Cslib.MachineLearning.OnlineLearning.OCO

section General

variable {E : Type*}

/-- The FTRL objective at round `t`: the regularizer plus the losses of the rounds before `t`. -/
noncomputable def ftrlObjective (ψ : E → ℝ) (ℓ : ℕ → E → ℝ) (t : ℕ) (y : E) : ℝ :=
  ψ y + ∑ s ∈ range t, ℓ s y

theorem ftrlObjective_def (ψ : E → ℝ) (ℓ : ℕ → E → ℝ) (t : ℕ) (y : E) :
    ftrlObjective ψ ℓ t y = ψ y + ∑ s ∈ range t, ℓ s y := by
  rw [ftrlObjective]

@[simp] theorem ftrlObjective_zero (ψ : E → ℝ) (ℓ : ℕ → E → ℝ) (y : E) :
    ftrlObjective ψ ℓ 0 y = ψ y := by
  rw [ftrlObjective_def, range_zero, sum_empty, add_zero]

theorem ftrlObjective_succ (ψ : E → ℝ) (ℓ : ℕ → E → ℝ) (t : ℕ) (y : E) :
    ftrlObjective ψ ℓ (t + 1) y = ftrlObjective ψ ℓ t y + ℓ t y := by
  rw [ftrlObjective_def, ftrlObjective_def, sum_range_succ, add_assoc]

/-- `x` is a run of follow the regularized leader on `K` with regularizer `ψ` and losses `ℓ`
[Orabona2019, Algorithm 7.1]: every `x t` lies in `K` and minimizes `ψ + ∑ s < t, ℓ s` there. -/
structure IsFTRL (K : Set E) (ψ : E → ℝ) (ℓ : ℕ → E → ℝ) (x : ℕ → E) : Prop where
  mem : ∀ t, x t ∈ K
  isMinOn : ∀ t, IsMinOn (ftrlObjective ψ ℓ t) K (x t)

variable {K : Set E} {ψ : E → ℝ} {ℓ : ℕ → E → ℝ} {x : ℕ → E}

theorem IsFTRL.objective_le (h : IsFTRL K ψ ℓ x) (t : ℕ) {u : E} (hu : u ∈ K) :
    ftrlObjective ψ ℓ t (x t) ≤ ftrlObjective ψ ℓ t u :=
  h.isMinOn t hu

/-- **The FTRL regret equality** [Orabona2019, Lemma 7.1], for a constant regularizer. It holds
for every sequence `x` and comparator `u`; FTRL makes the last two terms `F T (x T) - F T u`
nonpositive for `u ∈ K`, where `F = ftrlObjective ψ ℓ`. -/
theorem ftrl_regret_eq (ψ : E → ℝ) (ℓ : ℕ → E → ℝ) (x : ℕ → E) (u : E) (T : ℕ) :
    ∑ t ∈ range T, (ℓ t (x t) - ℓ t u) =
      ψ u - ψ (x 0) +
        ∑ t ∈ range T, (ftrlObjective ψ ℓ t (x t) - ftrlObjective ψ ℓ (t + 1) (x (t + 1)) +
          ℓ t (x t)) +
        (ftrlObjective ψ ℓ T (x T) - ftrlObjective ψ ℓ T u) := by
  induction T with
  | zero => simp only [range_zero, sum_empty, ftrlObjective_zero]; ring
  | succ T ih =>
    rw [sum_range_succ (fun t => ℓ t (x t) - ℓ t u), ih,
      sum_range_succ (fun t => ftrlObjective ψ ℓ t (x t) -
        ftrlObjective ψ ℓ (t + 1) (x (t + 1)) + ℓ t (x t)),
      ftrlObjective_succ ψ ℓ T u]
    ring

/-- **Be the leader** [Hazan2022, Lemma 5.4]: playing each round's minimizer one round early
does at least as well as every fixed `u ∈ K`, regularizer included. -/
theorem IsFTRL.add_sum_le (h : IsFTRL K ψ ℓ x) {u : E} (hu : u ∈ K) (T : ℕ) :
    ψ (x 0) + ∑ t ∈ range T, ℓ t (x (t + 1)) ≤ ψ u + ∑ t ∈ range T, ℓ t u := by
  induction T generalizing u with
  | zero =>
    have h0 := h.objective_le 0 hu
    simp only [ftrlObjective_zero] at h0
    simp only [range_zero, sum_empty, add_zero, h0]
  | succ T ih =>
    have h1 := ih (h.mem (T + 1))
    have h2 := h.objective_le (T + 1) hu
    rw [ftrlObjective_def, ftrlObjective_def, sum_range_succ, sum_range_succ] at h2
    rw [sum_range_succ, sum_range_succ]
    linarith

/-- **Regret is at most stability** [Hazan2022, Lemma 5.3]: the regret of FTRL against `u ∈ K` is
at most `ψ u - ψ (x 0)` plus the stability terms `ℓ t (x t) - ℓ t (x (t + 1))`. -/
theorem IsFTRL.regret_le_add_sum_sub (h : IsFTRL K ψ ℓ x) {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (ℓ t (x t) - ℓ t u) ≤
      ψ u - ψ (x 0) + ∑ t ∈ range T, (ℓ t (x t) - ℓ t (x (t + 1))) := by
  have := h.add_sum_le hu T
  rw [sum_sub_distrib, sum_sub_distrib]
  linarith

/-- **Existence of FTRL runs**: on a compact nonempty `K`, with a regularizer and losses continuous
on `K`, every round's objective has a minimizer on `K`. -/
theorem exists_isFTRL [TopologicalSpace E] (hK : IsCompact K) (hne : K.Nonempty)
    (hψ : ContinuousOn ψ K) (hℓ : ∀ t, ContinuousOn (ℓ t) K) : ∃ x, IsFTRL K ψ ℓ x := by
  have hmin : ∀ t, ∃ y ∈ K, IsMinOn (ftrlObjective ψ ℓ t) K y := fun t =>
    hK.exists_isMinOn hne (hψ.add (continuousOn_finsetSum _ fun s _ => hℓ s))
  choose x hx hxmin using hmin
  exact ⟨x, hx, hxmin⟩

end General

section StronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {ψ : E → ℝ}
  {ℓ : ℕ → E → ℝ} {x : ℕ → E} {μ : ℝ}

/-- The FTRL objective inherits the strong convexity of the regularizer. -/
theorem strongConvexOn_ftrlObjective (hψ : StrongConvexOn K μ ψ)
    (hℓ : ∀ t, ConvexOn ℝ K (ℓ t)) (t : ℕ) : StrongConvexOn K μ (ftrlObjective ψ ℓ t) := by
  induction t with
  | zero =>
    convert hψ using 1
    funext y
    exact ftrlObjective_zero ψ ℓ y
  | succ t ih =>
    have := ih.add_convexOn (hℓ t)
    convert this using 1
    funext y
    rw [ftrlObjective_succ, Pi.add_apply]

/-- With a `μ`-strongly convex regularizer (`μ > 0`) and convex losses, the FTRL run is unique. -/
theorem IsFTRL.unique {x' : ℕ → E} (h : IsFTRL K ψ ℓ x) (h' : IsFTRL K ψ ℓ x')
    (hψ : StrongConvexOn K μ ψ) (hμ : 0 < μ) (hℓ : ∀ t, ConvexOn ℝ K (ℓ t)) : x = x' :=
  funext fun t => ((strongConvexOn_ftrlObjective hψ hℓ t).strictConvexOn hμ).eq_of_isMinOn
    (h.isMinOn t) (h'.isMinOn t) (h.mem t) (h'.mem t)

/-- **Stability of FTRL** (compare [Orabona2019, Lemma 7.8]): with a `μ`-strongly convex
regularizer and convex losses, if `ℓ t (x t) - ℓ t y ≤ L * ‖x t - y‖` for `y ∈ K`, then the
stability term of round `t` in the regret equality is at most `L ^ 2 / (2 μ)`. -/
theorem IsFTRL.stability_le (h : IsFTRL K ψ ℓ x) (hψ : StrongConvexOn K μ ψ) (hμ : 0 < μ)
    (hℓ : ∀ t, ConvexOn ℝ K (ℓ t)) {t : ℕ} {L : ℝ}
    (hL : ∀ y ∈ K, ℓ t (x t) - ℓ t y ≤ L * ‖x t - y‖) :
    ftrlObjective ψ ℓ t (x t) - ftrlObjective ψ ℓ (t + 1) (x (t + 1)) + ℓ t (x t) ≤
      L ^ 2 / (2 * μ) := by
  have := (strongConvexOn_ftrlObjective hψ hℓ t).sub_le_of_isMinOn hμ (h.mem t) (h.isMinOn t)
    (h.mem (t + 1)) (ℓ := ℓ t) (hL _ (h.mem (t + 1)))
  rw [ftrlObjective_succ]
  linarith

/-- **Regret of FTRL with a strongly convex regularizer** ([Orabona2019, Lemmas 7.1 and 7.8];
compare [Hazan2022, Theorem 5.2]). If `ψ` is `μ`-strongly convex on `K` with `μ > 0`, the losses
are convex on `K` and `ℓ t (x t) - ℓ t y ≤ L t * ‖x t - y‖` for `y ∈ K` (for instance, `ℓ t` is
`L t`-Lipschitz on `K`), then the regret against every `u ∈ K` is at most
`ψ u - ψ (x 0) + ∑ t < T, L t ^ 2 / (2 μ)`. -/
theorem IsFTRL.regret_le (h : IsFTRL K ψ ℓ x) (hψ : StrongConvexOn K μ ψ) (hμ : 0 < μ)
    (hℓ : ∀ t, ConvexOn ℝ K (ℓ t)) {L : ℕ → ℝ}
    (hL : ∀ t, ∀ y ∈ K, ℓ t (x t) - ℓ t y ≤ L t * ‖x t - y‖) {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (ℓ t (x t) - ℓ t u) ≤
      ψ u - ψ (x 0) + ∑ t ∈ range T, L t ^ 2 / (2 * μ) := by
  rw [ftrl_regret_eq ψ ℓ x u T]
  have hstab : ∑ t ∈ range T, (ftrlObjective ψ ℓ t (x t) -
      ftrlObjective ψ ℓ (t + 1) (x (t + 1)) + ℓ t (x t)) ≤ ∑ t ∈ range T, L t ^ 2 / (2 * μ) :=
    sum_le_sum fun t _ => h.stability_le hψ hμ hℓ (hL t)
  have hlast := h.objective_le T hu
  linarith

/-- **Constant learning rate** ([Orabona2019, Corollary 7.9] with `η_t = η`): FTRL with the
regularizer `R / η`, for a `σ`-strongly convex `R` with `σ, η > 0`, has regret at most
`(R u - R (x 0)) / η + η / (2 σ) ∑ t < T, L t ^ 2` against every `u ∈ K`. Since `x 0` minimizes
`R` on `K`, `R u - R (x 0) = R u - min_K R`. -/
theorem IsFTRL.regret_le_div {R : E → ℝ} {η σ : ℝ} (h : IsFTRL K (fun y => R y / η) ℓ x)
    (hR : StrongConvexOn K σ R) (hσ : 0 < σ) (hη : 0 < η) (hℓ : ∀ t, ConvexOn ℝ K (ℓ t))
    {L : ℕ → ℝ} (hL : ∀ t, ∀ y ∈ K, ℓ t (x t) - ℓ t y ≤ L t * ‖x t - y‖) {u : E} (hu : u ∈ K)
    (T : ℕ) :
    ∑ t ∈ range T, (ℓ t (x t) - ℓ t u) ≤
      (R u - R (x 0)) / η + η / (2 * σ) * ∑ t ∈ range T, L t ^ 2 := by
  have hscale : StrongConvexOn K (η⁻¹ * σ) fun y => R y / η := by
    convert hR.smul (inv_nonneg.mpr hη.le) using 1
    funext y
    rw [smul_eq_mul, div_eq_inv_mul]
  have hb := h.regret_le hscale (mul_pos (inv_pos.mpr hη) hσ) hℓ hL hu T
  have e : ∑ t ∈ range T, L t ^ 2 / (2 * (η⁻¹ * σ)) = η / (2 * σ) * ∑ t ∈ range T, L t ^ 2 := by
    rw [mul_sum]
    refine sum_congr rfl fun t _ => ?_
    field_simp
  rw [e] at hb
  rw [sub_div]
  exact hb

/-- **Tuned learning rate.** If `R` is `σ`-strongly convex on `K` with `R y - R z ≤ D ^ 2` for
`y z ∈ K`, the losses are convex and `ℓ t (x t) - ℓ t y ≤ L * ‖x t - y‖` on `K`, then FTRL with
regularizer `R / η` for `η = D / L * √(2 σ / T)` has regret at most `D L √(2 T / σ)` over
`T ≥ 1` rounds against every `u ∈ K`. -/
theorem IsFTRL.regret_le_sqrt {R : E → ℝ} {σ D L : ℝ} {T : ℕ} (hσ : 0 < σ) (hD : 0 < D)
    (hL0 : 0 < L) (hT : 0 < T)
    (h : IsFTRL K (fun y => R y / (D / L * √(2 * σ / T))) ℓ x) (hR : StrongConvexOn K σ R)
    (hRD : ∀ y ∈ K, ∀ z ∈ K, R y - R z ≤ D ^ 2) (hℓ : ∀ t, ConvexOn ℝ K (ℓ t))
    (hL : ∀ t, ∀ y ∈ K, ℓ t (x t) - ℓ t y ≤ L * ‖x t - y‖) {u : E} (hu : u ∈ K) :
    ∑ t ∈ range T, (ℓ t (x t) - ℓ t u) ≤ D * L * √(2 * T / σ) := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  set s := √(2 * σ / T) with hs
  have hs0 : 0 < s := sqrt_pos.mpr (by positivity)
  have hss : s * s = 2 * σ / T := mul_self_sqrt (by positivity)
  have hη : 0 < D / L * s := by positivity
  have hb := h.regret_le_div hR hσ hη hℓ (L := fun _ => L) hL hu T
  have hD2 := hRD u hu (x 0) (h.mem 0)
  simp only [sum_const, card_range, nsmul_eq_mul] at hb
  -- `√(2 T / σ) = 2 / s`, since `s * √(2 T / σ) = √4 = 2`.
  have hsq : √(2 * T / σ) = 2 / s := by
    rw [eq_div_iff hs0.ne', hs, ← sqrt_mul (by positivity)]
    have : 2 * (T : ℝ) / σ * (2 * σ / T) = 2 ^ 2 := by field_simp
    rw [this, sqrt_sq (by norm_num)]
  have e1 : (R u - R (x 0)) / (D / L * s) ≤ D * L / s := by
    rw [div_le_div_iff₀ hη hs0]
    have : (R u - R (x 0)) * s ≤ D ^ 2 * s := mul_le_mul_of_nonneg_right hD2 hs0.le
    calc (R u - R (x 0)) * s ≤ D ^ 2 * s := this
      _ = D * L * (D / L * s) := by field_simp
  have e2 : D / L * s / (2 * σ) * (T * L ^ 2) = D * L / s := by
    rw [eq_div_iff hs0.ne']
    calc D / L * s / (2 * σ) * (T * L ^ 2) * s = D * L * T * (s * s) / (2 * σ) := by
          field_simp
      _ = D * L := by rw [hss]; field_simp
  rw [hsq]
  have : D * L * (2 / s) = D * L / s + D * L / s := by ring
  linarith

/-- **FTRL with linearized losses** [Orabona2019, §7.3]: run FTRL on the linear losses given by
subgradients `g t` of convex losses `f t` at the played points, i.e.
`f t (x t) + g t (y - x t) ≤ f t y` for `y ∈ K`. With a `μ`-strongly convex regularizer, the
regret on the losses `f t` against every `u ∈ K` is at most
`ψ u - ψ (x 0) + ∑ t < T, ‖g t‖ ^ 2 / (2 μ)`, with the operator norm (dual norm) `‖g t‖`. The
`g t` may depend on `x t`, so this covers gradients revealed at the played points. -/
theorem IsFTRL.regret_le_of_subgradient {f : ℕ → E → ℝ} {g : ℕ → E →L[ℝ] ℝ}
    (h : IsFTRL K ψ (fun t y => g t y) x) (hψ : StrongConvexOn K μ ψ) (hμ : 0 < μ)
    (hsub : ∀ t, ∀ y ∈ K, f t (x t) + g t (y - x t) ≤ f t y) {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤ ψ u - ψ (x 0) + ∑ t ∈ range T, ‖g t‖ ^ 2 / (2 * μ) := by
  have hb := h.regret_le hψ hμ (fun t => (g t).toLinearMap.convexOn hψ.1) (L := fun t => ‖g t‖)
    (fun t y _ => by
      rw [← map_sub]
      exact (le_norm_self _).trans ((g t).le_opNorm _)) hu T
  refine le_trans (sum_le_sum fun t _ => ?_) hb
  have := hsub t u hu
  rw [map_sub] at this
  linarith

/-- FTRL with linearized losses for convex losses `f t` differentiable within `K` at the played
points, with derivatives `f' t` (`IsFTRL.regret_le_of_subgradient` with `g t = f' t`). -/
theorem IsFTRL.regret_le_of_hasFDerivWithinAt {f : ℕ → E → ℝ} {f' : ℕ → E →L[ℝ] ℝ}
    (h : IsFTRL K ψ (fun t y => f' t y) x) (hψ : StrongConvexOn K μ ψ) (hμ : 0 < μ)
    (hf : ∀ t, ConvexOn ℝ K (f t)) (hd : ∀ t, HasFDerivWithinAt (f t) (f' t) K (x t))
    {u : E} (hu : u ∈ K) (T : ℕ) :
    ∑ t ∈ range T, (f t (x t) - f t u) ≤
      ψ u - ψ (x 0) + ∑ t ∈ range T, ‖f' t‖ ^ 2 / (2 * μ) :=
  h.regret_le_of_subgradient hψ hμ
    (fun t _ hy => (hf t).add_le_of_hasFDerivWithinAt (h.mem t) hy (hd t)) hu T

end StronglyConvex

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E} {η : ℝ}
  {x₀ : E}

/-- The Euclidean FTRL objective with linear losses is, up to a constant, a scaled squared
distance to `x₀ - η ∑ s < t, g s`. -/
private theorem ftrlObjective_euclidean (hη : 0 < η) (g : ℕ → E) (t : ℕ) (y : E) :
    ftrlObjective (fun y => ‖y - x₀‖ ^ 2 / (2 * η)) (fun s y => ⟪g s, y⟫) t y =
      ‖y - (x₀ - η • ∑ s ∈ range t, g s)‖ ^ 2 / (2 * η) +
        (⟪∑ s ∈ range t, g s, x₀⟫ - η / 2 * ‖∑ s ∈ range t, g s‖ ^ 2) := by
  rw [ftrlObjective_def, ← sum_inner]
  set G := ∑ s ∈ range t, g s
  rw [sub_sub_eq_add_sub, add_sub_right_comm, norm_add_sq_real, inner_smul_right, norm_smul,
    mul_pow, norm_of_nonneg hη.le, inner_sub_left, real_inner_comm G y, real_inner_comm G x₀]
  field_simp
  ring

/-- **Euclidean FTRL is lazy projection** [Hazan2022, §5.4.1]: with the regularizer
`‖y - x₀‖ ^ 2 / (2 η)` and linear losses `y ↦ ⟪g t, y⟫`, a sequence is an FTRL run on a nonempty
complete convex `K` iff each `x t` is the metric projection of `x₀ - η ∑ s < t, g s` onto `K`. -/
theorem isFTRL_euclidean_iff (hne : K.Nonempty) (hc : IsComplete K) (hK : Convex ℝ K)
    (hη : 0 < η) (g : ℕ → E) (x : ℕ → E) :
    IsFTRL K (fun y => ‖y - x₀‖ ^ 2 / (2 * η)) (fun t y => ⟪g t, y⟫) x ↔
      ∀ t, x t = metricProjection K (x₀ - η • ∑ s ∈ range t, g s) := by
  have key : ∀ t, ∀ z ∈ K, IsMinOn (ftrlObjective (fun y => ‖y - x₀‖ ^ 2 / (2 * η))
      (fun s y => ⟪g s, y⟫) t) K z ↔
      ∀ w ∈ K, ‖x₀ - η • ∑ s ∈ range t, g s - z‖ ≤ ‖x₀ - η • ∑ s ∈ range t, g s - w‖ := by
    intro t z _
    simp only [isMinOn_iff, ftrlObjective_euclidean hη, add_le_add_iff_right]
    refine forall₂_congr fun w _ => ?_
    rw [div_le_div_iff_of_pos_right (by positivity), norm_sub_rev z, norm_sub_rev w,
      sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  constructor
  · intro h t
    exact ((metricProjection_eq_iff_forall_norm_le hne hc hK (h.mem t)).mpr
      ((key t (x t) (h.mem t)).mp (h.isMinOn t))).symm
  · intro h
    have hmem : ∀ t, x t ∈ K := fun t => by
      rw [h t]
      exact metricProjection_mem hne hc hK _
    refine ⟨hmem, fun t => (key t (x t) (hmem t)).mpr ?_⟩
    exact (metricProjection_eq_iff_forall_norm_le hne hc hK (hmem t)).mp (h t).symm

/-- The unprojected state of lazy projected online gradient descent: `y 0 = x₀` and
`y (t + 1) = y t - η • grad t (Π_K (y t))`. -/
noncomputable def lazyOGDState (K : Set E) (η : ℝ) (grad : ℕ → E → E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | t + 1 =>
    lazyOGDState K η grad x₀ t - η • grad t (metricProjection K (lazyOGDState K η grad x₀ t))

/-- **Lazy projected online gradient descent** [Hazan2022, §5.4.1]: play the metric projection
onto `K` of the unprojected state, which accumulates the gradients revealed at the played points.
-/
noncomputable def lazyOGD (K : Set E) (η : ℝ) (grad : ℕ → E → E) (x₀ : E) (t : ℕ) : E :=
  metricProjection K (lazyOGDState K η grad x₀ t)

variable {grad : ℕ → E → E}

@[simp] theorem lazyOGDState_zero : lazyOGDState K η grad x₀ 0 = x₀ := by
  rw [lazyOGDState]

theorem lazyOGDState_succ (t : ℕ) :
    lazyOGDState K η grad x₀ (t + 1) =
      lazyOGDState K η grad x₀ t - η • grad t (lazyOGD K η grad x₀ t) := by
  rw [lazyOGDState, lazyOGD]

theorem lazyOGD_def (t : ℕ) :
    lazyOGD K η grad x₀ t = metricProjection K (lazyOGDState K η grad x₀ t) := by
  rw [lazyOGD]

/-- The unprojected state is `x₀` minus `η` times the sum of the gradients revealed so far. -/
theorem lazyOGDState_eq (t : ℕ) :
    lazyOGDState K η grad x₀ t = x₀ - η • ∑ s ∈ range t, grad s (lazyOGD K η grad x₀ s) := by
  induction t with
  | zero => rw [lazyOGDState_zero, range_zero, sum_empty, smul_zero, sub_zero]
  | succ t ih => rw [lazyOGDState_succ, ih, sum_range_succ, smul_add, sub_sub]

/-- Lazy projected online gradient descent is FTRL with the Euclidean regularizer
`‖y - x₀‖ ^ 2 / (2 η)` on the linear losses `y ↦ ⟪grad t (x t), y⟫` given by the gradients at the
played points. -/
theorem isFTRL_lazyOGD (hne : K.Nonempty) (hc : IsComplete K) (hK : Convex ℝ K) (hη : 0 < η) :
    IsFTRL K (fun y => ‖y - x₀‖ ^ 2 / (2 * η))
      (fun t y => ⟪grad t (lazyOGD K η grad x₀ t), y⟫) (lazyOGD K η grad x₀) :=
  (isFTRL_euclidean_iff hne hc hK hη _ _).mpr fun t => by rw [lazyOGD_def, lazyOGDState_eq]

theorem lazyOGD_mem (hne : K.Nonempty) (hc : IsComplete K) (hK : Convex ℝ K) (t : ℕ) :
    lazyOGD K η grad x₀ t ∈ K :=
  metricProjection_mem hne hc hK _

/-- **Regret of lazy projected online gradient descent.** If the gradients satisfy the subgradient
inequality `f t x + ⟪grad t x, y - x⟫ ≤ f t y` on `K`, then for every `η > 0` the regret against
every `u ∈ K` is at most `‖u - x₀‖ ^ 2 / (2 η) + η / 2 * ∑ t < T, ‖grad t (x t)‖ ^ 2`. This is the
Euclidean case of `IsFTRL.regret_le` (strong convexity `1 / η`, `L t = ‖grad t (x t)‖`). -/
theorem lazyOGD_regret_le {f : ℕ → E → ℝ} (hne : K.Nonempty) (hc : IsComplete K)
    (hK : Convex ℝ K) (hη : 0 < η)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y) {u : E} (hu : u ∈ K)
    (T : ℕ) :
    ∑ t ∈ range T, (f t (lazyOGD K η grad x₀ t) - f t u) ≤
      ‖u - x₀‖ ^ 2 / (2 * η) +
        η / 2 * ∑ t ∈ range T, ‖grad t (lazyOGD K η grad x₀ t)‖ ^ 2 := by
  set x := lazyOGD K η grad x₀
  have hψ : StrongConvexOn K η⁻¹ fun y => ‖y - x₀‖ ^ 2 / (2 * η) := by
    convert strongConvexOn_mul_norm_sub_sq hK η⁻¹ x₀ using 1
    funext y
    field_simp
  have hb := (isFTRL_lazyOGD (grad := grad) (x₀ := x₀) hne hc hK hη).regret_le hψ
    (inv_pos.mpr hη) (fun t => (innerₛₗ ℝ _).convexOn hK) (L := fun t => ‖grad t (x t)‖)
    (fun t y _ => by
      rw [← inner_sub_right]
      exact real_inner_le_norm _ _) hu T
  refine le_trans (sum_le_sum fun t _ => ?_) (hb.trans ?_)
  · have := hsub t (x t) (lazyOGD_mem hne hc hK t) u hu
    rw [inner_sub_right] at this
    linarith
  · have e : ∑ t ∈ range T, ‖grad t (x t)‖ ^ 2 / (2 * η⁻¹) =
        η / 2 * ∑ t ∈ range T, ‖grad t (x t)‖ ^ 2 := by
      rw [mul_sum]
      refine sum_congr rfl fun t _ => ?_
      field_simp
    have h0 : 0 ≤ ‖x 0 - x₀‖ ^ 2 / (2 * η) := by positivity
    rw [e]
    linarith

/-- **Tuned lazy projected online gradient descent**: if the gradients satisfy the subgradient
inequality `f t x + ⟪grad t x, y - x⟫ ≤ f t y` and have norm at most `G` on `K`, `‖u - x₀‖ ≤ D`
and `D, G > 0`, the constant step size `η = D / (G √T)` gives regret at most `G D √T` over
`T ≥ 1` rounds (compare the `2 G D √T` of [Hazan2022, §5.4.1], and `ogd_regret_le_fixed` for
the agile variant). -/
theorem lazyOGD_regret_le_fixed {f : ℕ → E → ℝ} (hne : K.Nonempty) (hc : IsComplete K)
    (hK : Convex ℝ K) {D G : ℝ} (hD0 : 0 < D) (hG0 : 0 < G) (hG : ∀ t, ∀ x ∈ K, ‖grad t x‖ ≤ G)
    (hsub : ∀ t, ∀ x ∈ K, ∀ y ∈ K, f t x + ⟪grad t x, y - x⟫ ≤ f t y) {u : E} (hu : u ∈ K)
    (hD : ‖u - x₀‖ ≤ D) {T : ℕ} (hT : 0 < T) :
    ∑ t ∈ range T, (f t (lazyOGD K (D / (G * √(T : ℝ))) grad x₀ t) - f t u) ≤
      G * D * √(T : ℝ) := by
  have hTr : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hsT : 0 < √(T : ℝ) := sqrt_pos.mpr hTr
  set c := D / (G * √(T : ℝ)) with hcdef
  have hc0 : 0 < c := by positivity
  have h := lazyOGD_regret_le (x₀ := x₀) hne hc hK hc0 hsub hu T
  have hgs : ∑ t ∈ range T, ‖grad t (lazyOGD K c grad x₀ t)‖ ^ 2 ≤ T * G ^ 2 := by
    calc ∑ t ∈ range T, ‖grad t (lazyOGD K c grad x₀ t)‖ ^ 2 ≤ ∑ _t ∈ range T, G ^ 2 :=
          sum_le_sum fun t _ =>
            pow_le_pow_left₀ (norm_nonneg _) (hG t _ (lazyOGD_mem hne hc hK t)) 2
      _ = T * G ^ 2 := by rw [sum_const, card_range, nsmul_eq_mul]
  have hD2 : ‖u - x₀‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hD 2
  have e1 : ‖u - x₀‖ ^ 2 / (2 * c) ≤ G * D * √(T : ℝ) / 2 := by
    calc ‖u - x₀‖ ^ 2 / (2 * c) ≤ D ^ 2 / (2 * c) := by gcongr
      _ = G * D * √(T : ℝ) / 2 := by rw [hcdef]; field_simp
  have e2 : c / 2 * (T * G ^ 2) = G * D * √(T : ℝ) / 2 := by
    calc c / 2 * (T * G ^ 2) =
          (√(T : ℝ) * √(T : ℝ)) * (D / (G * √(T : ℝ)) * G ^ 2) / 2 := by
          rw [mul_self_sqrt hTr.le, hcdef]; ring
      _ = G * D * √(T : ℝ) / 2 := by field_simp
  have e3 : c / 2 * ∑ t ∈ range T, ‖grad t (lazyOGD K c grad x₀ t)‖ ^ 2 ≤ c / 2 * (T * G ^ 2) :=
    mul_le_mul_of_nonneg_left hgs (by positivity)
  linarith

end Euclidean

end Cslib.MachineLearning.OnlineLearning.OCO
