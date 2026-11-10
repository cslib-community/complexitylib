/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.BoundedDegree
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Gaussian
public import CslibFrontier.Computability.Circuit.Frontier.AverageCase
public import CslibFrontier.Computability.Circuit.Frontier.LowerBound

/-!
# Frontier lower bounds for fan-in two

The frontier lower bound for fan-in two (`Cslib.Circuits.Frontier.eventually_lt_innerSize`) is
conditional on the layout hypothesis `LayoutBound 3 A`, and gives `s > (1 + 1/A - ε) n`. Two
layout bounds remove the hypothesis:

* median edge-score layouts give `A = 2p` with `p = (3 / (2π)) arccos ((1 + 2√2)/4)`
  (`Cslib.Circuits.Frontier.layoutBound_gaussian`), so `1 + 1/A = L`;
* vertex-score layouts give `A = 1/3` (`Cslib.Circuits.Frontier.layoutBound_one_third`), so
  `1 + 1/A = 4`.

Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a finite alphabet `U` with at least two
symbols, with `log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all
large `n`, every circuit of fan-in at most two deciding `S_n`, over any basis and interpretation
on `U`, has more than

* `(L - ε) n` inner gates, with `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5624977`
  (`Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_innerSize`);
* `(114/25 - ε) n = (4.56 - ε) n` inner gates, since `L ≥ 114/25`
  (`Cslib.Circuits.Frontier.eventually_114_div_25_sub_mul_lt_innerSize`);
* `(4 - ε) n` inner gates (`Cslib.Circuits.Frontier.eventually_four_sub_mul_lt_innerSize`).

Gates of arity zero, the constants, are not counted. The hypotheses are those of
`Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize`: the bounds apply to every family
of dense rectangle-free sets, and to a particular family once it is shown to be one.

The same three coefficients hold for the bundled worst-case claim `CircuitLowerBound` and for the
average-case claim `AverageCaseBound`: circuits of fan-in two with at most `(L - ε) n` inner gates
agree with a set of bias at most `b_n` on large rectangles on at most a
`1/2 + b_n + exp (-γ n)` fraction of the inputs.

## Main results

* `Cslib.Circuits.Frontier.eventually_gaussian_sub_mul_lt_innerSize`: `s > (L - ε) n`.
* `Cslib.Circuits.Frontier.eventually_114_div_25_sub_mul_lt_innerSize`: `s > (114/25 - ε) n`.
* `Cslib.Circuits.Frontier.eventually_four_sub_mul_lt_innerSize`: `s > (4 - ε) n`.
* `Cslib.Circuits.Frontier.circuitLowerBound_gaussian`, `circuitLowerBound_114_div_25`,
  `circuitLowerBound_four`: the bundled worst-case claims.
* `Cslib.Circuits.Frontier.averageCaseBound_gaussian`, `averageCaseBound_114_div_25`,
  `averageCaseBound_four`: the average-case claims.
-/

public section

namespace Cslib.Circuits.Frontier

open Filter Asymptotics Real

universe u v

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **The Gaussian frontier lower bound for fan-in two.** Let `S_n ⊆ U^n` be `K_n`-rectangle-free
sets over a finite alphabet `U` with at least two symbols, with `log K_n = o(n)` and
`n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`, every circuit of fan-in
at most two deciding `S_n`, over any basis and interpretation on `U`, has more than `(L - ε) n`
inner gates, where `L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem eventually_gaussian_sub_mul_lt_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (1 + π / (3 * arccos ((1 + 2 * √2) / 4)) - ε) * n < c.innerSize := by
  have h := eventually_lt_innerSize (mul_pos two_pos Gaussian.gaussianCoefficient_pos)
    layoutBound_gaussian hSK hε
  rwa [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h

/-- **The `(4.56 - ε) n` frontier lower bound for fan-in two.** Under the hypotheses of
`eventually_gaussian_sub_mul_lt_innerSize`, for every `ε > 0` and all large `n`, every circuit of
fan-in at most two deciding `S_n`, over any basis and interpretation on `U`, has more than
`(114/25 - ε) n` inner gates. -/
theorem eventually_114_div_25_sub_mul_lt_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (114 / 25 - ε) * n < c.innerSize := by
  filter_upwards [eventually_gaussian_sub_mul_lt_innerSize.{u, v} hSK hε] with n hn
  intro σ I Acc c hfan hS
  refine lt_of_le_of_lt ?_ (hn σ I Acc c hfan hS)
  exact mul_le_mul_of_nonneg_right (by linarith [Gaussian.circuitCoefficient_ge_456])
    (Nat.cast_nonneg n)

/-- **The `(4 - ε) n` frontier lower bound for fan-in two.** Under the hypotheses of
`eventually_gaussian_sub_mul_lt_innerSize`, for every `ε > 0` and all large `n`, every circuit of
fan-in at most two deciding `S_n`, over any basis and interpretation on `U`, has more than
`(4 - ε) n` inner gates. The layout bound is that of Gaussian vertex scores. -/
theorem eventually_four_sub_mul_lt_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (4 - ε) * n < c.innerSize := by
  have h := eventually_lt_innerSize (by norm_num) layoutBound_one_third hSK hε
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at h

/-! ### The bundled claims -/

/-- **Circuits of fan-in two need `(L - ε) n` gates**, by median edge-score layouts, where
`L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem circuitLowerBound_gaussian :
    CircuitLowerBound.{u, v} (1 + π / (3 * arccos ((1 + 2 * √2) / 4))) := by
  have h := circuitLowerBound_of_layoutBound.{u, v}
    (mul_pos two_pos Gaussian.gaussianCoefficient_pos) layoutBound_gaussian
  rwa [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h

/-- **Circuits of fan-in two need `(4.56 - ε) n` gates**: the Gaussian coefficient is at least
`114/25`. -/
theorem circuitLowerBound_114_div_25 : CircuitLowerBound.{u, v} (114 / 25) :=
  circuitLowerBound_gaussian.mono Gaussian.circuitCoefficient_ge_456

/-- **Circuits of fan-in two need `(4 - ε) n` gates**, by Gaussian vertex-score layouts. -/
theorem circuitLowerBound_four : CircuitLowerBound.{u, v} 4 := by
  have h := circuitLowerBound_of_layoutBound.{u, v} (by norm_num) layoutBound_one_third
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at h

/-- **Circuits of fan-in two below `(L - ε) n` gates barely beat guessing** on sets of small bias
on large rectangles, by median edge-score layouts, where
`L = 1 + π / (3 arccos ((1 + 2√2)/4)) ≈ 4.5625`. -/
theorem averageCaseBound_gaussian :
    AverageCaseBound.{u, v} (1 + π / (3 * arccos ((1 + 2 * √2) / 4))) := by
  have h := averageCaseBound_of_layoutBound.{u, v}
    (mul_pos two_pos Gaussian.gaussianCoefficient_pos) layoutBound_gaussian
  rwa [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h

/-- **Circuits of fan-in two below `(4.56 - ε) n` gates barely beat guessing**: the Gaussian
coefficient is at least `114/25`. -/
theorem averageCaseBound_114_div_25 : AverageCaseBound.{u, v} (114 / 25) :=
  averageCaseBound_gaussian.mono Gaussian.circuitCoefficient_ge_456

/-- **Circuits of fan-in two below `(4 - ε) n` gates barely beat guessing**, by Gaussian
vertex-score layouts. -/
theorem averageCaseBound_four : AverageCaseBound.{u, v} 4 := by
  have h := averageCaseBound_of_layoutBound.{u, v} (by norm_num) layoutBound_one_third
  rwa [show (1 : ℝ) + 1 / (1 / 3) = 4 by norm_num] at h

end Cslib.Circuits.Frontier
