/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF

/-!
# Markov chains on discrete state spaces

A Markov chain `P : MarkovChain S` is a transition kernel `S → PMF S`: `P x` is the law of the
next state from `x`, and `P x y` is the transition probability. Chains on a fixed state space form
a monoid under composition of kernels, `(P * Q) x = (P x).bind Q`, so `P ^ t` is the `t`-step
kernel and `pow_add` gives the Chapman–Kolmogorov equations.

A distribution `π` is *stationary* if `π.bind P = π` (`π = πP`, [LevinPeres2017], (1.14)),
and `P` is *reversible* with respect to `π` if it satisfies detailed balance
`π x * P x y = π y * P y x` ([LevinPeres2017], (1.29)). Detailed balance implies
stationarity ([LevinPeres2017], Proposition 1.20).

The kernel representation reuses the library's `PMF` and statistical-distance APIs directly.
Mathlib's measure-theoretic `ProbabilityTheory.Kernel.Invariant` and
`ProbabilityTheory.Kernel.IsReversible` are the measurable-space analogues of `IsStationary` and
`IsReversible`; no finiteness of `S` is assumed here.

## Main definitions

* `Cslib.Probability.MarkovChain`: a transition kernel on a discrete state space.
* `Cslib.Probability.MarkovChain.IsStationary`: `π.bind P = π`.
* `Cslib.Probability.MarkovChain.IsReversible`: detailed balance.

## Main results

* `Cslib.Probability.MarkovChain.pow_add_apply`: Chapman–Kolmogorov.
* `Cslib.Probability.MarkovChain.IsStationary.pow`: a stationary law is stationary for `P ^ t`.
* `Cslib.Probability.MarkovChain.IsStationary.mul`: a stationary law is stationary for `P₁ * P₂`.
* `Cslib.Probability.MarkovChain.IsReversible.isStationary`: detailed balance implies
  stationarity.

## References

* [LevinPeres2017], Chapter 1.
-/

public section

open scoped ENNReal

namespace Cslib.Probability

/-- A Markov chain on a discrete state space `S`, given by its transition kernel. -/
structure MarkovChain (S : Type*) where
  /-- The law of the next state from the current state. -/
  step : S → PMF S

namespace MarkovChain

variable {S : Type*}

instance : CoeFun (MarkovChain S) fun _ => S → PMF S := ⟨step⟩

@[ext] theorem ext {P Q : MarkovChain S} (h : ∀ x, P x = Q x) : P = Q := by
  cases P
  cases Q
  congr
  exact funext h

/-- Composition of kernels: first `P`, then `Q`. -/
noncomputable instance : Monoid (MarkovChain S) where
  mul P Q := ⟨fun x => (P x).bind Q⟩
  one := ⟨PMF.pure⟩
  mul_assoc P Q R := by
    ext1 x
    exact PMF.bind_bind _ _ _
  one_mul P := by
    ext1 x
    exact PMF.pure_bind _ _
  mul_one P := by
    ext1 x
    exact PMF.bind_pure _

@[simp] theorem mul_apply (P Q : MarkovChain S) (x : S) : (P * Q) x = (P x).bind Q := rfl

@[simp] theorem one_apply (x : S) : (1 : MarkovChain S) x = PMF.pure x := rfl

theorem pow_succ_apply (P : MarkovChain S) (t : ℕ) (x : S) :
    (P ^ (t + 1)) x = ((P ^ t) x).bind P := by
  rw [pow_succ, mul_apply]

theorem pow_succ_apply' (P : MarkovChain S) (t : ℕ) (x : S) :
    (P ^ (t + 1)) x = (P x).bind (P ^ t) := by
  rw [pow_succ', mul_apply]

/-- Chapman–Kolmogorov: `P^{s+t}(x, ·) = Σ_y P^s(x, y) P^t(y, ·)`. -/
theorem pow_add_apply (P : MarkovChain S) (s t : ℕ) (x : S) :
    (P ^ (s + t)) x = ((P ^ s) x).bind (P ^ t) := by
  rw [pow_add, mul_apply]

/-- `π` is a stationary distribution of `P`: `π = πP` ([LevinPeres2017], (1.14)). -/
@[expose] def IsStationary (P : MarkovChain S) (π : PMF S) : Prop := π.bind P = π

/-- `P` is reversible with respect to `π`, i.e. satisfies the detailed balance equations
([LevinPeres2017], (1.29)). -/
@[expose] def IsReversible (P : MarkovChain S) (π : PMF S) : Prop :=
  ∀ x y, π x * P x y = π y * P y x

/-- A stationary distribution of `P` is invariant under `P ^ t`. -/
theorem IsStationary.bind_pow {P : MarkovChain S} {π : PMF S} (h : P.IsStationary π) (t : ℕ) :
    π.bind (P ^ t) = π := by
  induction t with
  | zero => exact PMF.bind_pure π
  | succ t ih =>
    calc π.bind (P ^ (t + 1)) = π.bind (fun x => ((P ^ t) x).bind P) :=
          congrArg π.bind (funext fun x => pow_succ_apply P t x)
      _ = (π.bind (P ^ t)).bind P := (PMF.bind_bind _ _ _).symm
      _ = π := by rw [ih]; exact h

/-- A stationary distribution of `P` is a stationary distribution of `P ^ t`. -/
theorem IsStationary.pow {P : MarkovChain S} {π : PMF S} (h : P.IsStationary π) (t : ℕ) :
    (P ^ t).IsStationary π :=
  h.bind_pow t

/-- Stationarity is preserved under chain composition (`P₁ * P₂`). -/
theorem IsStationary.mul {P₁ P₂ : MarkovChain S} {π : PMF S} (h₁ : P₁.IsStationary π)
    (h₂ : P₂.IsStationary π) : (P₁ * P₂).IsStationary π := by
  change π.bind (fun x => (P₁ x).bind P₂) = π
  rw [← PMF.bind_bind, h₁, h₂]

/-- **Detailed balance implies stationarity** ([LevinPeres2017], Proposition 1.20). -/
theorem IsReversible.isStationary {P : MarkovChain S} {π : PMF S} (h : P.IsReversible π) :
    P.IsStationary π := by
  ext y
  rw [PMF.bind_apply]
  calc ∑' x, π x * P x y = ∑' x, π y * P y x := tsum_congr fun x => h x y
    _ = π y := by rw [ENNReal.tsum_mul_left, (P y).tsum_coe, mul_one]

end MarkovChain

end Cslib.Probability
