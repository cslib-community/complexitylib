/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Basic
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Smooth games and the robust price of anarchy

Roughgarden's smoothness framework [Roughgarden2015] bounds the inefficiency of equilibria of a
cost-minimization game by a single inequality about pairs of profiles. A game is
`(λ, μ)`-smooth ([Roughgarden2015], Definition 2.1) if for all profiles `s` and `s'`,
`∑ i, cost i (update s i (s' i)) ≤ λ * socialCost s' + μ * socialCost s`.
If `μ < 1`, the social cost of every pure Nash equilibrium is at most `λ / (1 - μ)` times the
social cost of every profile ([Roughgarden2015], derivation (3)–(5)), and the same bound holds for
the expected social cost of every coarse correlated equilibrium ([Roughgarden2015], Theorem 3.2).

A coarse correlated equilibrium is a probability distribution `σ` on profiles under which no
player can lower its expected cost by committing in advance to a fixed strategy `a`
([Roughgarden2015], (15)). We use finitely supported distributions, the points of the standard
simplex `Convexity.StdSimplex ℝ (∀ i, S i)`, so expectations are finite sums.

## Main definitions

* `Cslib.GameTheory.CostGame.IsSmooth`: `(λ, μ)`-smoothness; the parameter `λ` is called `lam`
  because `λ` is a Lean keyword.
* `Cslib.GameTheory.CostGame.IsCoarseCorrelatedEquilibrium`: coarse correlated equilibria.

## Main results

* `Cslib.GameTheory.CostGame.IsSmooth.socialCost_le_of_isPureNash`: in a `(λ, μ)`-smooth game
  with `μ < 1`, every pure Nash equilibrium `s` satisfies
  `socialCost s ≤ λ / (1 - μ) * socialCost s'` for every profile `s'`.
* `Cslib.GameTheory.CostGame.IsSmooth.expected_socialCost_le_of_forall_le`: the bound for
  distributions that are coarse correlated equilibria up to an additive slack `ε i` for player
  `i`, giving `E[socialCost] ≤ (λ * socialCost s' + ∑ i, ε i) / (1 - μ)`. This is the static
  content of the no-regret bound of [Roughgarden2015], Theorem 3.3, whose empirical
  distributions have additive slack equal to the players' average regrets.
* `Cslib.GameTheory.CostGame.IsSmooth.expected_socialCost_le` ([Roughgarden2015], Theorem 3.2,
  for coarse correlated equilibria): the case of zero slack.
* `Cslib.GameTheory.CostGame.IsPureNash.isCoarseCorrelatedEquilibrium`: a pure Nash equilibrium
  is a coarse correlated equilibrium as a point mass.

## References

* [Roughgarden2015]
-/

public section

namespace Cslib.GameTheory.CostGame

variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] [Fintype ι] (G : CostGame ι S)

/-- `G` is **`(λ, μ)`-smooth** ([Roughgarden2015], Definition 2.1) with `λ = lam`: for all
profiles `s` and `s'`, the total cost of the unilateral deviations from `s` to `s'` is at most
`lam * socialCost s' + μ * socialCost s`. Unlike the source, the definition imposes no sign
conditions on `lam` and `μ`; the price-of-anarchy bounds below assume only `μ < 1`. -/
@[expose] def IsSmooth (lam μ : ℝ) : Prop :=
  ∀ s s' : ∀ i, S i,
    ∑ i, G.cost i (Function.update s i (s' i)) ≤ lam * G.socialCost s' + μ * G.socialCost s

/-- A finitely supported distribution `σ` on profiles is a **coarse correlated equilibrium**
([Roughgarden2015], (15)): for every player `i` and strategy `a`, the expected cost of `i` under
`σ` is at most its expected cost when it plays `a` while the others play according to `σ`. -/
@[expose] def IsCoarseCorrelatedEquilibrium (σ : Convexity.StdSimplex ℝ (∀ i, S i)) : Prop :=
  ∀ i (a : S i), σ.weights.sum (fun s w => w * G.cost i s)
    ≤ σ.weights.sum (fun s w => w * G.cost i (Function.update s i a))

variable {G}

/-- **The price of anarchy of pure Nash equilibria in smooth games** ([Roughgarden2015],
(3)–(5)): if `G` is `(λ, μ)`-smooth with `μ < 1` and `s` is a pure Nash equilibrium, then
`socialCost s ≤ λ / (1 - μ) * socialCost s'` for every profile `s'`. -/
theorem IsSmooth.socialCost_le_of_isPureNash {lam μ : ℝ} (hG : G.IsSmooth lam μ) (hμ : μ < 1)
    {s : ∀ i, S i} (hs : G.IsPureNash s) (s' : ∀ i, S i) :
    G.socialCost s ≤ lam / (1 - μ) * G.socialCost s' := by
  have h1 : G.socialCost s ≤ ∑ i, G.cost i (Function.update s i (s' i)) :=
    Finset.sum_le_sum fun i _ => hs i (s' i)
  have h2 := hG s s'
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith

/-- **The robust price of anarchy with additive slack**: if `G` is `(λ, μ)`-smooth with `μ < 1`
and the distribution `σ` satisfies the coarse correlated equilibrium inequalities up to an
additive error `ε i` for each player `i`, then the expected social cost under `σ` is at most
`(λ * socialCost s' + ∑ i, ε i) / (1 - μ)` for every profile `s'`. With `ε i` the average regret
of player `i`, this is the static form of [Roughgarden2015], Theorem 3.3. -/
theorem IsSmooth.expected_socialCost_le_of_forall_le {lam μ : ℝ} (hG : G.IsSmooth lam μ)
    (hμ : μ < 1) {σ : Convexity.StdSimplex ℝ (∀ i, S i)} {ε : ι → ℝ}
    (hσ : ∀ i (a : S i), σ.weights.sum (fun s w => w * G.cost i s)
      ≤ σ.weights.sum (fun s w => w * G.cost i (Function.update s i a)) + ε i)
    (s' : ∀ i, S i) :
    σ.weights.sum (fun s w => w * G.socialCost s)
      ≤ (lam * G.socialCost s' + ∑ i, ε i) / (1 - μ) := by
  simp only [Finsupp.sum] at hσ ⊢
  have htot : ∑ s ∈ σ.weights.support, σ.weights s = 1 := σ.total
  have h1 : ∑ s ∈ σ.weights.support, σ.weights s * G.socialCost s
      ≤ ∑ s ∈ σ.weights.support, σ.weights s * ∑ i, G.cost i (Function.update s i (s' i))
        + ∑ i, ε i := by
    simp only [socialCost, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (s := σ.weights.support), ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => hσ i (s' i)
  have h2 : ∑ s ∈ σ.weights.support, σ.weights s * ∑ i, G.cost i (Function.update s i (s' i))
      ≤ ∑ s ∈ σ.weights.support, σ.weights s * (lam * G.socialCost s' + μ * G.socialCost s) :=
    Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (hG s s') (Convexity.StdSimplex.weights_nonneg s)
  have h3 : ∑ s ∈ σ.weights.support, σ.weights s * (lam * G.socialCost s' + μ * G.socialCost s)
      = lam * G.socialCost s' + μ * ∑ s ∈ σ.weights.support, σ.weights s * G.socialCost s := by
    have : ∀ s ∈ σ.weights.support, σ.weights s * (lam * G.socialCost s' + μ * G.socialCost s)
        = lam * G.socialCost s' * σ.weights s + μ * (σ.weights s * G.socialCost s) :=
      fun _ _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      htot, mul_one]
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- **The robust price of anarchy for coarse correlated equilibria** ([Roughgarden2015],
Theorem 3.2): if `G` is `(λ, μ)`-smooth with `μ < 1` and `σ` is a coarse correlated equilibrium,
then the expected social cost under `σ` is at most `λ / (1 - μ)` times the social cost of every
profile `s'`. -/
theorem IsSmooth.expected_socialCost_le {lam μ : ℝ} (hG : G.IsSmooth lam μ) (hμ : μ < 1)
    {σ : Convexity.StdSimplex ℝ (∀ i, S i)} (hσ : G.IsCoarseCorrelatedEquilibrium σ)
    (s' : ∀ i, S i) :
    σ.weights.sum (fun s w => w * G.socialCost s) ≤ lam / (1 - μ) * G.socialCost s' := by
  have h := hG.expected_socialCost_le_of_forall_le hμ (ε := fun _ => 0)
    (fun i a => by simpa only [add_zero] using hσ i a) s'
  rwa [Finset.sum_const_zero, add_zero, ← div_mul_eq_mul_div] at h

omit [Fintype ι] in
/-- A pure Nash equilibrium, viewed as a point mass, is a coarse correlated equilibrium. -/
theorem IsPureNash.isCoarseCorrelatedEquilibrium {s : ∀ i, S i} (hs : G.IsPureNash s) :
    G.IsCoarseCorrelatedEquilibrium (Convexity.StdSimplex.single s) := by
  intro i a
  simp only [Convexity.StdSimplex.weights_single, Finsupp.sum_single_index, zero_mul, one_mul]
  exact hs i a

end Cslib.GameTheory.CostGame
