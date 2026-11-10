/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.AverageCase
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.General
public import CslibFrontier.Computability.Circuit.Frontier.LowerBound

/-!
# Unconditional frontier lower bounds

The frontier lower bound (`Cslib.Circuits.Frontier.eventually_lt_mul_innerSize`) is conditional
on the layout hypothesis `LayoutBound (r + 1) A`. Spanning trees prove it with coefficient
`A = 1` in every degree (`Cslib.Circuits.Frontier.layoutBound_one`), which removes the
hypothesis.

Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a finite alphabet `U` with at least two
symbols, with `log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`. Then for every fan-in `r ≥ 2`,
every `ε > 0` and all large `n`, every circuit of fan-in at most `r` deciding `S_n`, over any
basis and interpretation on `U`, has `s` inner gates with

`(r - 1) s > (2 - ε) n`.

For fan-in two this reads `s > (2 - ε) n` (`circuitLowerBound_two`). Gates of arity zero, the
constants, are not counted.

The same layouts give the average-case bound with coefficient two (`averageCaseBound_two`): if
`S_n` has bias at most `b_n` on rectangles with both sides of size at least `K_n`, where
`log K_n = o(n)`, then every circuit of fan-in at most two with at most `(2 - ε) n` inner gates
agrees with `S_n` on at most a `1/2 + b_n + exp (-γ n)` fraction of the inputs, for a `γ > 0`
depending only on `ε`.

## Main results

* `Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_innerSize`: `(r - 1) s > (2 - ε) n` for
  every fan-in `r`.
* `Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize`: `s > (2 - ε) n` for fan-in two.
* `Cslib.Circuits.Frontier.circuitLowerBound_two`: the same, as the bundled claim
  `CircuitLowerBound 2`.
* `Cslib.Circuits.Frontier.averageCaseBound_two`: the average-case claim `AverageCaseBound 2`.
-/

public section

namespace Cslib.Circuits.Frontier

open Filter Asymptotics

universe u v

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **The unconditional frontier lower bound.** Let `r ≥ 2`, and let `S_n ⊆ U^n` be
`K_n`-rectangle-free sets over a finite alphabet `U` with at least two symbols, with
`log K_n = o(n)` and `n log |U| - log |S_n| = o(n)`. Then for every `ε > 0` and all large `n`,
every circuit of fan-in at most `r` deciding `S_n`, over any basis and interpretation on `U`, has
`s` inner gates with `(r - 1) s > (2 - ε) n`. -/
theorem eventually_two_sub_mul_lt_mul_innerSize {r : ℕ} (hr : 2 ≤ r)
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        (2 - ε) * n < (r - 1) * c.innerSize := by
  simpa only [div_one, one_add_one_eq_two] using
    eventually_lt_mul_innerSize hr one_pos (layoutBound_one (r + 1)) hSK hε

/-- **The unconditional frontier lower bound for fan-in two.** Under the hypotheses of
`eventually_two_sub_mul_lt_mul_innerSize`, for every `ε > 0` and all large `n`, every circuit of
fan-in at most two deciding `S_n`, over any basis and interpretation on `U`, has more than
`(2 - ε) n` inner gates. -/
theorem eventually_two_sub_mul_lt_innerSize
    (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        (2 - ε) * n < c.innerSize := by
  simpa only [div_one, one_add_one_eq_two] using
    eventually_lt_innerSize one_pos (layoutBound_one 3) hSK hε

/-- **The unconditional worst-case claim with coefficient two**: circuits of fan-in at most two
deciding dense `K_n`-rectangle-free sets with `log K_n = o(n)` need more than `(2 - ε) n` inner
gates. -/
theorem circuitLowerBound_two : CircuitLowerBound.{u, v} 2 := by
  simpa only [div_one, one_add_one_eq_two] using
    circuitLowerBound_of_layoutBound.{u, v} one_pos (layoutBound_one 3)

/-- **The unconditional average-case claim with coefficient two**: for every `ε > 0` there is a
`γ > 0` such that every circuit of fan-in at most two with at most `(2 - ε) n` inner gates agrees
with a set of bias at most `b_n` on rectangles with sides of size at least `K_n`,
`log K_n = o(n)`, on at most a `1/2 + b_n + exp (-γ n)` fraction of the inputs. -/
theorem averageCaseBound_two : AverageCaseBound.{u, v} 2 := by
  simpa only [div_one, one_add_one_eq_two] using
    averageCaseBound_of_layoutBound.{u, v} one_pos (layoutBound_one 3)

end Cslib.Circuits.Frontier
