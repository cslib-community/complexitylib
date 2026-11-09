/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Smooth
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# No-regret dynamics and the price of anarchy

In repeated play of a cost-minimization game, round `t` produces a distribution `σ t` on profiles.
Player `i` has *regret at most `R i`* after `T` rounds if, for every fixed strategy `a`, its total
expected cost `∑ t < T, E_{σ t}[cost i]` exceeds the total expected cost
`∑ t < T, E_{s ∼ σ t}[cost i (update s i a)]` of always playing `a` by at most `R i`
([Roughgarden2013CS364A], Lecture 17, Definition 1.2 and §3). Thus `R i` bounds the *total*
regret, whereas Definition 1.2 measures *time-averaged* regret: the source's `ε` in
Proposition 3.1 and its `R_i` in Corollary 3.3 correspond to `R i / T` here. The time average
`timeAverage σ T = (1/T) ∑ t < T, σ t` of the distributions is then a coarse correlated equilibrium
up to the additive slack `R i / T` ([Roughgarden2013CS364A], Lecture 17, Proposition 3.1). With the
robust price of anarchy of smooth games (`CostGame.IsSmooth.expected_socialCost_le_of_forall_le`),
the total expected social cost of `T` rounds in a `(λ, μ)`-smooth game with `μ < 1` is at most
`(T λ socialCost s' + ∑ i, R i) / (1 - μ)` for every profile `s'` ([Roughgarden2013CS364A],
Lecture 17, Corollary 3.3; [Roughgarden2015], Theorem 3.3 and Remark 3.4, inequality (25)).

The source states Corollary 3.3 for the time average and leaves its proof as an exercise. We
prove the equivalent bound for totals, which also covers `T = 0`, and the time-average form for
`0 < T`.

These statements hold for arbitrary sequences of distributions, not only product distributions.
For the multiplicative-update dynamics, in which every player runs Hedge, see
`CslibFrontier.GameTheory.Strategic.Hedge`.

## Main definitions

* `Cslib.GameTheory.timeAverage`: the time average `(1/T) ∑ t < T, σ t`.

## Main results

* `Cslib.GameTheory.timeAverage_sum`: expectations under the time average are time averages of
  expectations.
* `Cslib.GameTheory.CostGame.timeAverage_le_add` ([Roughgarden2013CS364A], Lecture 17,
  Proposition 3.1): with regret at most `R i`, the time average is a coarse correlated equilibrium
  up to the slack `R i / T`.
* `Cslib.GameTheory.CostGame.IsSmooth.sum_expected_socialCost_le` ([Roughgarden2013CS364A],
  Lecture 17, Corollary 3.3): the total expected social cost of no-regret play in a smooth game.
* `Cslib.GameTheory.CostGame.IsSmooth.timeAverage_expected_socialCost_le`: the same bound for the
  time average.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [T. Roughgarden, *Intrinsic robustness of the price of anarchy*][Roughgarden2015]
-/

public section

namespace Cslib.GameTheory

open Finset

variable {X : Type*}

private theorem sum_smul_sum_weights (c : ℝ) (σ : ℕ → Convexity.StdSimplex ℝ X) (T : ℕ)
    (f : X → ℝ) :
    (c • ∑ t ∈ range T, (σ t).weights).sum (fun x w => w * f x)
      = c * ∑ t ∈ range T, (σ t).weights.sum (fun x w => w * f x) := by
  rw [Finsupp.sum_smul_index' (fun _ => zero_mul _), ← Finsupp.sum_finsetSum_index
    (fun _ => by rw [smul_zero, zero_mul]) (fun _ _ _ => by rw [smul_add, add_mul]), mul_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr fun x _ => by rw [smul_eq_mul, mul_assoc]

/-- The **time average** `(1/T) ∑ t < T, σ t` of the distributions `σ 0, …, σ (T - 1)`, for
`0 < T` ([Roughgarden2013CS364A], Lecture 17, Proposition 3.1). -/
noncomputable def timeAverage (σ : ℕ → Convexity.StdSimplex ℝ X) (T : ℕ) (hT : 0 < T) :
    Convexity.StdSimplex ℝ X where
  weights := (T : ℝ)⁻¹ • ∑ t ∈ range T, (σ t).weights
  nonneg x := by
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.smul_apply, Finsupp.finsetSum_apply,
      smul_eq_mul]
    exact mul_nonneg (by positivity) (sum_nonneg fun t _ => (σ t).nonneg x)
  total := by
    have h := sum_smul_sum_weights (T : ℝ)⁻¹ σ T (fun _ => 1)
    simp only [mul_one] at h
    rw [h]
    simp only [Convexity.StdSimplex.total, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast hT.ne')

/-- Expectations under the time average are the time averages of the expectations. -/
theorem timeAverage_sum (σ : ℕ → Convexity.StdSimplex ℝ X) {T : ℕ} (hT : 0 < T) (f : X → ℝ) :
    (timeAverage σ T hT).weights.sum (fun x w => w * f x)
      = (∑ t ∈ range T, (σ t).weights.sum (fun x w => w * f x)) / T := by
  rw [div_eq_inv_mul]
  exact sum_smul_sum_weights _ σ T f

namespace CostGame

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] {G : CostGame ι S}

/-- **No-regret play yields approximate coarse correlated equilibria** ([Roughgarden2013CS364A],
Lecture 17, Proposition 3.1): if after `T` rounds player `i` has total regret at most `R i` with
respect to every fixed strategy, then the time average of the distributions satisfies the coarse
correlated equilibrium inequalities up to the additive slack `R i / T`, the time-averaged regret
that the source calls `ε`. -/
theorem timeAverage_le_add {σ : ℕ → Convexity.StdSimplex ℝ (∀ i, S i)} {T : ℕ} (hT : 0 < T)
    {R : ι → ℝ}
    (hR : ∀ i (a : S i), ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.cost i s)
      ≤ ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.cost i (Function.update s i a)) + R i)
    (i : ι) (a : S i) :
    (timeAverage σ T hT).weights.sum (fun s w => w * G.cost i s)
      ≤ (timeAverage σ T hT).weights.sum (fun s w => w * G.cost i (Function.update s i a))
        + R i / T := by
  rw [timeAverage_sum, timeAverage_sum, ← add_div]
  exact div_le_div_of_nonneg_right (hR i a) (by positivity)

variable [Fintype ι]

/-- **The robust price of anarchy of no-regret play**, time-average form
([Roughgarden2013CS364A], Lecture 17, Corollary 3.3): if `G` is `(λ, μ)`-smooth with `μ < 1` and
after `T > 0` rounds player `i` has total regret at most `R i`, then the expected social cost under
the time average of the distributions is at most `(λ socialCost s' + ∑ i, R i / T) / (1 - μ)` for
every profile `s'`. The time-averaged regrets `R i / T` are the source's `R_i`. -/
theorem IsSmooth.timeAverage_expected_socialCost_le {lam μ : ℝ} (hG : G.IsSmooth lam μ)
    (hμ : μ < 1) {σ : ℕ → Convexity.StdSimplex ℝ (∀ i, S i)} {T : ℕ} (hT : 0 < T) {R : ι → ℝ}
    (hR : ∀ i (a : S i), ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.cost i s)
      ≤ ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.cost i (Function.update s i a)) + R i)
    (s' : ∀ i, S i) :
    (timeAverage σ T hT).weights.sum (fun s w => w * G.socialCost s)
      ≤ (lam * G.socialCost s' + ∑ i, R i / T) / (1 - μ) :=
  hG.expected_socialCost_le_of_forall_le hμ (timeAverage_le_add hT hR) s'

/-- **The robust price of anarchy of no-regret play**, total form ([Roughgarden2013CS364A],
Lecture 17, Corollary 3.3; [Roughgarden2015], Theorem 3.3 and Remark 3.4, inequality (25)): if `G`
is `(λ, μ)`-smooth with `μ < 1` and after `T` rounds player `i` has total regret at most `R i`,
then the total expected social cost of the `T` rounds is at most
`(T λ socialCost s' + ∑ i, R i) / (1 - μ)` for every profile `s'`. Dividing by `T > 0` gives the
source's time-averaged statement with `R_i = R i / T`. -/
theorem IsSmooth.sum_expected_socialCost_le {lam μ : ℝ} (hG : G.IsSmooth lam μ) (hμ : μ < 1)
    {σ : ℕ → Convexity.StdSimplex ℝ (∀ i, S i)} {T : ℕ} {R : ι → ℝ}
    (hR : ∀ i (a : S i), ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.cost i s)
      ≤ ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.cost i (Function.update s i a)) + R i)
    (s' : ∀ i, S i) :
    ∑ t ∈ range T, (σ t).weights.sum (fun s w => w * G.socialCost s)
      ≤ (T * lam * G.socialCost s' + ∑ i, R i) / (1 - μ) := by
  have h1μ : 0 < 1 - μ := by linarith
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · have hR0 : ∀ i, 0 ≤ R i := fun i => by
      simpa only [range_zero, sum_empty, zero_add] using hR i (s' i)
    simp only [range_zero, sum_empty, Nat.cast_zero, zero_mul, zero_add]
    exact div_nonneg (sum_nonneg fun i _ => hR0 i) h1μ.le
  · have h := hG.timeAverage_expected_socialCost_le hμ hT hR s'
    rw [timeAverage_sum, ← sum_div] at h
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    rw [div_le_iff₀ hT'] at h
    refine h.trans (le_of_eq ?_)
    field_simp

end CostGame

end Cslib.GameTheory
