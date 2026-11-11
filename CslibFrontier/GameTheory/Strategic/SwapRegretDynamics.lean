/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Strategic.Correlated
public import CslibFrontier.GameTheory.Strategic.NoRegret
public import CslibFrontier.MachineLearning.OnlineLearning.SwapRegret
import CslibFrontier.Foundations.Analysis.SpecialFunctions.Sqrt

/-!
# Swap regret dynamics

If every player in a finite game runs an online learning algorithm with vanishing swap regret,
the time average of the product distributions converges to a correlated equilibrium
([Roughgarden2013CS364A], Lecture 18, Proposition 1.3; [BlumMansour2007], Theorem 3).
Specifically, if player `i` has total swap regret at most `R i` over `T` rounds, the time average
is an `(R i / T)`-approximate correlated equilibrium
(`timeAverage_productDist_isApproxCorrelatedEquilibrium`).

We instantiate this with the coupled multi-player Blum–Mansour dynamics (`blumMansourDynamics G T`)
using Hedge copies with the horizon-tuned learning rate `η_i = √(m_i ln m_i / T)` for a fixed
known horizon `T > 0`, where `m_i = |S i| ≥ 2` and `T ≥ m_i ln m_i`. Because each player's
mixed strategy in round `t` depends only on its expected cost vectors `deviationCost` from rounds
`< t`, the coupled trajectory is constructed by well-founded recursion on `t`, and satisfies the
online Blum–Mansour learner identity (`blumMansourDynamics_eq_blumMansourProb`). When game costs
lie in `[-1, 1]`, the time average over the first `T` rounds is a
`2 √(m_i ln m_i / T)`-approximate correlated equilibrium
(`blumMansour_isApproxCorrelatedEquilibrium`). This is a fixed-horizon, expected-cost,
full-information analysis, not sampled play, last-iterate convergence, or a running-time bound.

## Main definitions

* `Cslib.GameTheory.CostGame.blumMansourDynamics`: coupled multi-player Blum–Mansour dynamics
  tuned for a fixed horizon `T`.

## Main results

* `Cslib.GameTheory.CostGame.timeAverage_productDist_isApproxCorrelatedEquilibrium`: bounded swap
  regret implies the time average of product distributions is an approximate correlated equilibrium.
* `Cslib.GameTheory.CostGame.blumMansourDynamics_eq_blumMansourProb`: each player runs the
  single-learner Blum–Mansour algorithm against its realized expected-cost sequence.
* `Cslib.GameTheory.CostGame.blumMansourDynamics_nonneg`: the dynamics remain nonnegative.
* `Cslib.GameTheory.CostGame.sum_blumMansourDynamics`: each player's weights sum to `1`.
* `Cslib.GameTheory.CostGame.blumMansour_isApproxCorrelatedEquilibrium`: coupled Blum–Mansour
  dynamics yield a `2 √(m_i ln m_i / T)`-approximate correlated equilibrium.

## References

* [A. Blum and Y. Mansour, *From External to Internal Regret*][BlumMansour2007]
* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
-/

public section

namespace Cslib.GameTheory.CostGame

open Finset Real Function Cslib.MachineLearning.OnlineLearning.Experts

set_option linter.unusedDecidableInType false
variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] [Fintype ι] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (S i)] (G : CostGame ι S)

/-- **No-swap-regret play yields approximate correlated equilibria** ([Roughgarden2013CS364A],
Lecture 18, Proposition 1.3; [BlumMansour2007], Theorem 3): if after `T > 0` rounds player `i` has
total swap regret at most `R i` with respect to every switching function, then the time average of
the product distributions is an approximate correlated equilibrium up to the additive slack
`R i / T`. -/
theorem timeAverage_productDist_isApproxCorrelatedEquilibrium
    {p : ℕ → ∀ i, S i → ℝ} {T : ℕ} (hT : 0 < T)
    (h_nonneg : ∀ t i c, 0 ≤ p t i c) (h_sum : ∀ t i, ∑ c, p t i c = 1)
    {R : ι → ℝ}
    (hR : ∀ i (δ : S i → S i),
      ∑ t ∈ range T, ∑ a, p t i a * G.deviationCost (p t) i a
        ≤ ∑ t ∈ range T, ∑ a, p t i a * G.deviationCost (p t) i (δ a) + R i) :
    G.IsApproxCorrelatedEquilibrium (fun i => R i / T)
      (timeAverage (fun t => productDist (h_nonneg t) (h_sum t)) T hT) := by
  classical
  apply isApproxCorrelatedEquilibrium_iff.mpr
  intro i δ
  have hL : (∑ a, (timeAverage (fun t => productDist (h_nonneg t) (h_sum t)) T hT).weights.sum
      (fun s w => w * if s i = a then G.cost i s else 0)) =
      (∑ t ∈ range T, ∑ a, p t i a * G.deviationCost (p t) i a) / (T : ℝ) := by
    rw [sum_comm, sum_div]
    refine sum_congr rfl fun a _ => ?_
    rw [timeAverage_sum _ hT]
    refine congrArg (fun x => x / (T : ℝ)) ?_
    refine sum_congr rfl fun t _ => ?_
    have h_prod := productDist_sum (h_nonneg t) (h_sum t)
      (fun s => if s i = a then G.cost i s else 0)
    rw [h_prod]
    have h_ite := sum_ite_productWeight G (p t) (h_sum t i) a a
    have h_eq : (∑ s, productWeight (p t) s * if s i = a then G.cost i s else 0) =
        ∑ s, productWeight (p t) s * if s i = a then G.cost i (update s i a) else 0 := by
      refine sum_congr rfl fun s _ => ?_
      split_ifs with hs
      · rw [← hs, update_eq_self]
      · rfl
    rw [h_eq, h_ite]
  have hR_eq : (∑ a, (timeAverage (fun t => productDist (h_nonneg t) (h_sum t)) T hT).weights.sum
      (fun s w => w * if s i = a then G.cost i (update s i (δ a)) else 0)) =
      (∑ t ∈ range T, ∑ a, p t i a * G.deviationCost (p t) i (δ a)) / (T : ℝ) := by
    rw [sum_comm, sum_div]
    refine sum_congr rfl fun a _ => ?_
    rw [timeAverage_sum _ hT]
    refine congrArg (fun x => x / (T : ℝ)) ?_
    refine sum_congr rfl fun t _ => ?_
    have h_prod := productDist_sum (h_nonneg t) (h_sum t)
      (fun s => if s i = a then G.cost i (update s i (δ a)) else 0)
    rw [h_prod]
    exact sum_ite_productWeight G (p t) (h_sum t i) a (δ a)
  rw [hL, hR_eq, ← add_div]
  exact div_le_div_of_nonneg_right (hR i δ) (Nat.cast_nonneg T)

/-- The coupled multi-player **Blum–Mansour dynamics** for a fixed finite horizon `T`: in round `t`,
each player `i` plays the single-learner Blum–Mansour distribution with Hedge copies tuned for `T`
against the sequence of its realized expected cost vectors from rounds `< t`. -/
noncomputable def blumMansourDynamics (G : CostGame ι S) (T : ℕ) : ℕ → ∀ i, S i → ℝ :=
  WellFounded.fix Nat.lt_wfRel.wf fun t p i =>
    blumMansourProb √(Fintype.card (S i) * log (Fintype.card (S i)) / T)
      (fun s c => if _h : s < t then G.deviationCost (p s _h) i c else 0) t

private theorem blumMansourDynamics_eq (G : CostGame ι S) (T t : ℕ) (i : ι) :
    blumMansourDynamics G T t i =
      blumMansourProb √(Fintype.card (S i) * log (Fintype.card (S i)) / T)
        (fun s c => if _h : s < t then G.deviationCost (blumMansourDynamics G T s) i c else 0)
        t := by
  rw [blumMansourDynamics, WellFounded.fix_eq]

/-- Each player `i` in `blumMansourDynamics G T` runs the single-learner Blum–Mansour algorithm
against its realized expected-cost sequence `s c ↦ G.deviationCost (blumMansourDynamics G T s) i c`.
-/
theorem blumMansourDynamics_eq_blumMansourProb (G : CostGame ι S) (T t : ℕ) (i : ι) :
    blumMansourDynamics G T t i =
      blumMansourProb √(Fintype.card (S i) * log (Fintype.card (S i)) / T)
        (fun s c => G.deviationCost (blumMansourDynamics G T s) i c) t := by
  rw [blumMansourDynamics_eq]
  refine blumMansourProb_congr fun s hs => ?_
  ext c
  simp only [hs, dite_eq_left]

variable [∀ i, Nonempty (S i)]

/-- Every weight produced by `blumMansourDynamics` is nonnegative. -/
theorem blumMansourDynamics_nonneg (G : CostGame ι S) (T t : ℕ) (i : ι) (a : S i) :
    0 ≤ blumMansourDynamics G T t i a := by
  rw [blumMansourDynamics_eq_blumMansourProb]
  exact blumMansourProb_nonneg _ _ _ _

/-- In every round, each player's strategy in `blumMansourDynamics` sums to `1`. -/
theorem sum_blumMansourDynamics (G : CostGame ι S) (T t : ℕ) (i : ι) :
    ∑ a, blumMansourDynamics G T t i a = 1 := by
  simp only [blumMansourDynamics_eq_blumMansourProb, sum_blumMansourProb]

/-- **Blum–Mansour swap-regret dynamics yield approximate correlated equilibria**
([Roughgarden2013CS364A], Lecture 18, Proposition 1.3; [BlumMansour2007], Theorem 3 and
Corollary 7): for a finite game with costs in `[-1, 1]`, at least `2` strategies per player, and
horizon `T > 0` satisfying `m_i ln m_i ≤ T` for every player `i`, the time average of the first
`T` rounds of `blumMansourDynamics G T` is a `2 √(m_i ln m_i / T)`-approximate correlated
equilibrium. -/
theorem blumMansour_isApproxCorrelatedEquilibrium
    {T : ℕ} (hT : 0 < T)
    (hn : ∀ i, 2 ≤ Fintype.card (S i))
    (hT_bound : ∀ i, (Fintype.card (S i) : ℝ) * log (Fintype.card (S i)) ≤ T)
    (hc : ∀ i s, |G.cost i s| ≤ 1) :
    G.IsApproxCorrelatedEquilibrium
      (fun i => 2 * √(Fintype.card (S i) * log (Fintype.card (S i)) / T))
      (timeAverage
        (fun t => productDist (blumMansourDynamics_nonneg G T t) (sum_blumMansourDynamics G T t))
        T hT) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h_eq : (fun i => 2 * √(Fintype.card (S i) * log (Fintype.card (S i)) / T)) =
      fun i => (2 * √(T * (Fintype.card (S i) * log (Fintype.card (S i))))) / T := by
    ext i
    rw [mul_div_assoc (2 : ℝ), Real.sqrt_mul_div_self hT']
  rw [h_eq]
  refine timeAverage_productDist_isApproxCorrelatedEquilibrium G hT
    (blumMansourDynamics_nonneg G T) (sum_blumMansourDynamics G T) fun i δ => ?_
  have h_cost : ∀ s < T, ∀ a, |G.deviationCost (blumMansourDynamics G T s) i a| ≤ 1 :=
    fun s _ a => G.abs_deviationCost_le (blumMansourDynamics_nonneg G T s)
      (sum_blumMansourDynamics G T s) (hc i) a
  simpa only [blumMansourDynamics_eq_blumMansourProb] using
    blumMansour_swap_regret_le_sqrt (hn i) (hT_bound i) h_cost δ

end Cslib.GameTheory.CostGame
