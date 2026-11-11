/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Online.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Randomized online strategies against an oblivious adversary

This file adds randomized strategies to the online model of
`Complexity.DataStructure.Online.Basic`, for the **oblivious adversary**, which fixes the whole
request sequence before the strategy's coins are tossed. Against such an adversary a randomized
online strategy can be viewed as a probability distribution over deterministic online strategies:
drawing all coins up front and then running the resulting deterministic strategy gives the same
costs as tossing coins online, because the requests do not depend on the outcomes. This is the
standard mixed-strategy view of randomized online algorithms against oblivious adversaries; see
[Borodin and El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998] for a
textbook treatment.

A `RandStrategy` is a `PMF`, so it covers only **discrete (countably supported) mixtures** of
deterministic strategies. Nothing is lost for ski rental
(`Complexity.DataStructure.Online.SkiRental`), where every deterministic strategy acts as a
rent-then-buy threshold in `ℕ ∪ {∞}`, so every randomized algorithm induces a countably supported
law. Algorithms that toss fresh independent
coins at unboundedly many steps, such as the marking algorithm for paging, generally induce a
non-atomic law on `DetStrategy P`. They need a behavioural or bounded-horizon variant of this
model.

A `RandStrategy P` is a `PMF (DetStrategy P)`. Its expected cost on a request sequence is
`∑' A, μ A * A.cost s₀ reqs` in `ℝ≥0∞` (`RandStrategy.expectedCost`), and `(c, b)`-competitiveness
(`RandStrategy.IsCompetitive`) asks for `E[ALG] ≤ c * OPT + b` against every valid offline schedule,
with `c b : ℝ≥0∞` so that irrational ratios such as `e / (e - 1)` can be stated. Point masses
recover the deterministic notions (`RandStrategy.expectedCost_pure`,
`RandStrategy.isCompetitive_pure_iff`).

Lower bounds use the easy direction of Yao's principle [Yao1977]
(`RandStrategy.exists_le_mul_expectedCost`): if, under a distribution `ν` on request sequences,
every deterministic strategy has mean cost at least the mean of a benchmark `g`, then every
randomized strategy has a single request sequence on which its expected cost is at least `g`. The
general averaging lemmas of `Complexity.Probability.Minimax` bound some outcome *above* by a mean;
this one needs a sequence on which the expected cost is at least the benchmark, which is why it is
proved here.

Adaptive adversaries, which choose each request after seeing the strategy's earlier actions, are
not modelled.

## Main definitions

* `Cslib.DataStructure.Online.RandStrategy`: randomized online strategies, as distributions over
  deterministic strategies.
* `RandStrategy.expectedCost`: expected online cost on a fixed request sequence.
* `RandStrategy.IsCompetitiveFrom`, `RandStrategy.IsCompetitive`: competitiveness in expectation
  against an oblivious adversary, with `ℝ≥0∞` ratio and additive constant.

## Main results

* `RandStrategy.expectedCost_pure`, `RandStrategy.isCompetitive_pure_iff`: deterministic strategies
  as point masses.
* `RandStrategy.expectedCost_map`: expected cost of a strategy drawn through a parametrization.
* `RandStrategy.exists_le_mul_expectedCost`: the easy direction of Yao's principle for online
  lower bounds.

## References

* [A. Borodin and R. El-Yaniv, *Online Computation and Competitive Analysis*][BorodinElYaniv1998]
* [A. C.-C. Yao, *Probabilistic computations: toward a unified measure of complexity*][Yao1977]
-/

open scoped ENNReal

public section

namespace Cslib.DataStructure.Online

/-- A randomized online strategy for `P` against an oblivious adversary: a discrete (countably
supported) probability distribution over deterministic online strategies, all of whose coins are
drawn before the first request. -/
abbrev RandStrategy (P : Problem) : Type 1 := PMF (DetStrategy P)

namespace RandStrategy

variable {P : Problem}

/-- Expected online cost of the randomized strategy `μ` from initial configuration `s₀` on the
request sequence `reqs`, which the oblivious adversary fixes before the coins are drawn. -/
@[expose]
noncomputable def expectedCost (μ : RandStrategy P) (s₀ : P.State) (reqs : List P.Req) : ℝ≥0∞ :=
  ∑' A, μ A * (A.cost s₀ reqs : ℝ≥0∞)

/-- `μ` is `(c, b)`-competitive from `s₀` against an oblivious adversary when its expected cost on
every request sequence is at most `c` times any valid offline schedule's cost from `s₀`, plus
`b`. -/
@[expose]
def IsCompetitiveFrom (μ : RandStrategy P) (s₀ : P.State) (c b : ℝ≥0∞) : Prop :=
  ∀ reqs offStates, P.ValidSchedule s₀ reqs offStates →
    expectedCost μ s₀ reqs ≤ c * P.scheduleCost s₀ reqs offStates + b

/-- `μ` is `(c, b)`-competitive against an oblivious adversary when it is `(c, b)`-competitive from
every admissible initial state. -/
@[expose]
def IsCompetitive (μ : RandStrategy P) (c b : ℝ≥0∞) : Prop :=
  ∀ s₀, P.ValidInit s₀ → IsCompetitiveFrom μ s₀ c b

/-- A deterministic strategy, as a point mass, has its deterministic cost as expected cost. -/
@[simp]
theorem expectedCost_pure (A : DetStrategy P) (s₀ : P.State) (reqs : List P.Req) :
    expectedCost (PMF.pure A) s₀ reqs = A.cost s₀ reqs := by
  rw [expectedCost, tsum_eq_single A]
  · rw [PMF.pure_apply_self, one_mul]
  · intro A' hA'
    rw [PMF.pure_apply_of_ne _ _ hA', zero_mul]

/-- For natural coefficients, the point mass at `A` is `(c, b)`-competitive exactly when `A` is. -/
theorem isCompetitive_pure_iff (A : DetStrategy P) (c b : ℕ) :
    IsCompetitive (PMF.pure A) c b ↔ A.IsCompetitive c b := by
  have key : ∀ x y : ℕ, ((x : ℝ≥0∞) ≤ c * y + b) ↔ x ≤ c * y + b := fun x y => by norm_cast
  simp only [IsCompetitive, IsCompetitiveFrom, DetStrategy.IsCompetitive,
    DetStrategy.IsCompetitiveFrom, expectedCost_pure, key]

/-- Monotonicity of `IsCompetitive` in the ratio and the additive constant. -/
theorem IsCompetitive.mono {μ : RandStrategy P} {c₁ c₂ b₁ b₂ : ℝ≥0∞} (hc : c₁ ≤ c₂)
    (hb : b₁ ≤ b₂) (h : IsCompetitive μ c₁ b₁) : IsCompetitive μ c₂ b₂ :=
  fun s₀ hs₀ reqs offStates hv => (h s₀ hs₀ reqs offStates hv).trans (by gcongr)

/-- Expected cost of a strategy `f a` drawn by first sampling the parameter `a` from `ν`. -/
theorem expectedCost_map {α : Type*} (ν : PMF α) (f : α → DetStrategy P) (s₀ : P.State)
    (reqs : List P.Req) :
    expectedCost (ν.map f) s₀ reqs = ∑' a, ν a * ((f a).cost s₀ reqs : ℝ≥0∞) := by
  simp only [expectedCost, PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (f a)]
  · rw [ite_eq_left rfl]
  · intro A hA
    rw [ite_eq_right hA, zero_mul]

/-- **The easy direction of Yao's principle** [Yao1977] for online lower bounds against an
oblivious adversary. Let `ν` be a distribution on indices `i`, each naming a request sequence
`reqs i` with a benchmark `g i` (typically a multiple of the offline optimum on `reqs i`). If the
`ν`-mean of `g` is finite and at most `b` times the `ν`-mean cost of **every deterministic**
strategy, then every randomized strategy `μ` has an index `i` that `ν` can produce with
`g i ≤ b * E_μ[cost on reqs i]`. -/
theorem exists_le_mul_expectedCost {ι : Type*} (ν : PMF ι) (s₀ : P.State)
    (reqs : ι → List P.Req) (g : ι → ℝ≥0∞) (b : ℝ≥0∞) (hg : ∑' i, ν i * g i ≠ ∞)
    (h : ∀ A : DetStrategy P, ∑' i, ν i * g i ≤ b * ∑' i, ν i * (A.cost s₀ (reqs i) : ℝ≥0∞))
    (μ : RandStrategy P) : ∃ i ∈ ν.support, g i ≤ b * expectedCost μ s₀ (reqs i) := by
  by_contra! hlt
  -- averaging the hypothesis over `μ` bounds the `ν`-mean of `g` by the mean expected cost
  have h1 : ∑' i, ν i * g i ≤ b * ∑' i, ν i * expectedCost μ s₀ (reqs i) :=
    calc ∑' i, ν i * g i = ∑' A, μ A * ∑' i, ν i * g i := by
          rw [ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]
      _ ≤ ∑' A, μ A * (b * ∑' i, ν i * (A.cost s₀ (reqs i) : ℝ≥0∞)) :=
          tsum_le_tsum fun A => by gcongr; exact h A
      _ = b * ∑' i, ν i * expectedCost μ s₀ (reqs i) := by
          simp only [expectedCost, ← ENNReal.tsum_mul_left]
          rw [tsum_comm]
          exact tsum_congr fun i => tsum_congr fun A => by ring
  -- while the pointwise failure on the support makes it strictly larger
  obtain ⟨i₀, hi₀⟩ := ν.support_nonempty
  have hle : ∀ i, ν i * (b * expectedCost μ s₀ (reqs i)) ≤ ν i * g i := fun i => by
    by_cases hi : i ∈ ν.support
    · gcongr
      exact (hlt i hi).le
    · rw [(PMF.apply_eq_zero_iff ν i).mpr hi, zero_mul, zero_mul]
  have h2 : ∑' i, ν i * (b * expectedCost μ s₀ (reqs i)) < ∑' i, ν i * g i :=
    ENNReal.tsum_lt_tsum (ne_top_of_le_ne_top hg (tsum_le_tsum hle)) hle
      (ENNReal.mul_lt_mul_right ((PMF.mem_support_iff ν i₀).mp hi₀) (PMF.apply_ne_top ν i₀)
        (hlt i₀ hi₀))
  have h3 : ∑' i, ν i * (b * expectedCost μ s₀ (reqs i)) =
      b * ∑' i, ν i * expectedCost μ s₀ (reqs i) := by
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun i => by ring
  rw [h3] at h2
  exact absurd h1 (not_le.mpr h2)

end RandStrategy

end Cslib.DataStructure.Online
