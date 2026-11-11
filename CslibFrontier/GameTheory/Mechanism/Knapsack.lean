/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.CriticalBid

/-!
# Knapsack auctions

In a knapsack auction ([Roughgarden2013CS364A], Lecture 4, §1.1) bidder `i` has a publicly known
size `wᵢ` and a private valuation, and the seller has a capacity `W`; the feasible allocations are
the 0-1 vectors `x` with `∑ᵢ wᵢ xᵢ ≤ W`. `k`-unit auctions are the case `wᵢ = 1`, `W = k`.

The welfare-maximizing allocation rule (Lecture 4, (1)) is monotone, so by Myerson's Lemma it is
implementable, and its DSIC payments are critical bids (Lecture 4, §1.3). No claim is made about
computing it: the underlying Knapsack problem is NP-hard (Lecture 4, §1.4).

## Main definitions

* `SingleParameter.knapsackFeasible`: the 0-1 vectors `x` with `∑ᵢ wᵢ xᵢ ≤ W`.

## Main results

* `SingleParameter.IsWelfareMaximizing.criticalBidMechanism_isDSIC`,
  `SingleParameter.IsWelfareMaximizing.criticalBidMechanism_isIR`: in an environment with 0-1
  feasible allocations, every welfare-maximizing rule is DSIC and individually rational with
  critical-bid payments, which equal Myerson's payments
  (`SingleParameter.IsWelfareMaximizing.criticalBid_mul_eq_myersonPayment`).
* `SingleParameter.exists_knapsack_isWelfareMaximizing`: for every nonnegative capacity there is a
  welfare-maximizing knapsack allocation rule, which then has these properties.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [T. Roughgarden, *Twenty Lectures on Algorithmic Game Theory*][Roughgarden2016]
-/

public section

namespace Cslib.GameTheory.SingleParameter

variable {ι : Type*} [Fintype ι]

section Binary

variable {X : Set (ι → ℝ)} {x : (ι → ℝ) → ι → ℝ}

/-- A welfare-maximizing rule over 0-1 feasible allocations is a 0-1 rule. -/
theorem IsWelfareMaximizing.isBinary (hx : IsWelfareMaximizing X x)
    (hX : ∀ y ∈ X, ∀ i, y i = 0 ∨ y i = 1) : IsBinary x :=
  fun b hb i => hX _ (hx b hb).1 i

variable [DecidableEq ι]

/-- With 0-1 feasible allocations, a welfare-maximizing rule with critical-bid payments is DSIC
([Roughgarden2013CS364A], Lecture 4, §1.2–1.3). -/
theorem IsWelfareMaximizing.criticalBidMechanism_isDSIC (hx : IsWelfareMaximizing X x)
    (hX : ∀ y ∈ X, ∀ i, y i = 0 ∨ y i = 1) : (criticalBidMechanism x).IsDSIC :=
  SingleParameter.criticalBidMechanism_isDSIC hx.isMonotone (hx.isBinary hX)

/-- With 0-1 feasible allocations, a welfare-maximizing rule with critical-bid payments is
individually rational. -/
theorem IsWelfareMaximizing.criticalBidMechanism_isIR (hx : IsWelfareMaximizing X x)
    (hX : ∀ y ∈ X, ∀ i, y i = 0 ∨ y i = 1) : (criticalBidMechanism x).IsIR :=
  SingleParameter.criticalBidMechanism_isIR (hx.isBinary hX)

/-- With 0-1 feasible allocations, the critical-bid payments of a welfare-maximizing rule are
Myerson's payments. -/
theorem IsWelfareMaximizing.criticalBid_mul_eq_myersonPayment (hx : IsWelfareMaximizing X x)
    (hX : ∀ y ∈ X, ∀ i, y i = 0 ∨ y i = 1) {b : ι → ℝ} (hb : 0 ≤ b) (i : ι) :
    criticalBid x b i * x b i = myersonPayment x b i :=
  SingleParameter.criticalBid_mul_eq_myersonPayment hx.isMonotone (hx.isBinary hX) hb i

end Binary

/-- The feasible set of a knapsack auction with sizes `w` and capacity `W`: 0-1 allocation
vectors `x` with `∑ᵢ wᵢ xᵢ ≤ W` ([Roughgarden2013CS364A], Lecture 4, §1.1). -/
@[expose] def knapsackFeasible (w : ι → ℝ) (W : ℝ) : Set (ι → ℝ) :=
  {y | (∀ i, y i = 0 ∨ y i = 1) ∧ ∑ i, w i * y i ≤ W}

theorem knapsackFeasible_finite (w : ι → ℝ) (W : ℝ) : (knapsackFeasible w W).Finite := by
  refine (Set.Finite.pi (t := fun _ : ι => ({0, 1} : Set ℝ)) fun _ =>
    (Set.finite_singleton _).insert _).subset fun y hy => ?_
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, forall_const]
  exact hy.1

theorem zero_mem_knapsackFeasible (w : ι → ℝ) {W : ℝ} (hW : 0 ≤ W) :
    (0 : ι → ℝ) ∈ knapsackFeasible w W :=
  ⟨fun _ => Or.inl rfl, by simpa only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] using hW⟩

/-- **Knapsack auctions** ([Roughgarden2013CS364A], Lecture 4, §1.2–1.3): for every capacity
`W ≥ 0` some allocation rule maximizes the reported welfare over the knapsack-feasible
allocations, and with critical-bid payments (which are Myerson's payments) it is DSIC and
individually rational. -/
theorem exists_knapsack_isWelfareMaximizing [DecidableEq ι] (w : ι → ℝ) {W : ℝ} (hW : 0 ≤ W) :
    ∃ x, IsWelfareMaximizing (knapsackFeasible w W) x ∧ (criticalBidMechanism x).IsDSIC ∧
      (criticalBidMechanism x).IsIR ∧
      ∀ b, 0 ≤ b → ∀ i, criticalBid x b i * x b i = myersonPayment x b i := by
  obtain ⟨x, hx⟩ := exists_isWelfareMaximizing (knapsackFeasible_finite w W)
    ⟨0, zero_mem_knapsackFeasible w hW⟩
  have hX : ∀ y ∈ knapsackFeasible w W, ∀ i, y i = 0 ∨ y i = 1 := fun _ hy => hy.1
  exact ⟨x, hx, hx.criticalBidMechanism_isDSIC hX, hx.criticalBidMechanism_isIR hX,
    fun _ hb i => hx.criticalBid_mul_eq_myersonPayment hX hb i⟩

end Cslib.GameTheory.SingleParameter
