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

/-!
# Swap regret dynamics

If every player in a finite game runs an online learning algorithm with vanishing swap regret,
the time average of the product distributions converges to a correlated equilibrium
([Roughgarden2013CS364A], Lecture 18, Proposition 1.3). Specifically, if player `i` has total swap
regret at most `R i` over `T` rounds, the time average is an `(R i / T)`-approximate correlated
equilibrium.

We instantiate this with the Blum–Mansour reduction using Hedge copies. If every player uses this
algorithm tuned for a known horizon `T`, the time average converges to a correlated equilibrium at
a rate of `O(√(m log m / T))`, where `m` is the number of strategies.

## Main results

* `Cslib.GameTheory.CostGame.timeAverage_productDist_isApproxCorrelatedEquilibrium`: bounded swap
  regret implies the time average is an approximate correlated equilibrium.
* `Cslib.GameTheory.CostGame.blumMansour_isApproxCorrelatedEquilibrium`: swap regret dynamics
  converge at rate `O(√(m log m / T))`.

## References

* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
-/

public section

namespace Cslib.GameTheory.CostGame

open Finset Real Function Cslib.MachineLearning.OnlineLearning.Experts

set_option linter.unusedDecidableInType false
variable {ι : Type*} {S : ι → Type*} [DecidableEq ι] [Fintype ι] [∀ i, DecidableEq (S i)]
  [∀ i, Fintype (S i)] (G : CostGame ι S)

/-- **No-swap-regret play yields approximate correlated equilibria** ([Roughgarden2013CS364A],
Lecture 18, Proposition 1.3): if after `T` rounds player `i` has total swap regret at most `R i`
with respect to every switching function, then the time average of the product distributions is an
approximate correlated equilibrium up to the additive slack `R i / T`. -/
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



theorem blumMansour_isApproxCorrelatedEquilibrium
    {p : ℕ → ∀ i, S i → ℝ} {T : ℕ} (hT : 0 < T)
    (h_nonneg : ∀ t i c, 0 ≤ p t i c) (h_sum : ∀ t i, ∑ c, p t i c = 1)
    (hn : ∀ i, 2 ≤ Fintype.card (S i))
    (hT_bound : ∀ i, (Fintype.card (S i) : ℝ) * log (Fintype.card (S i)) ≤ T)
    (h_cost : ∀ t < T, ∀ i a, |G.deviationCost (p t) i a| ≤ 1)
    (h_p : ∀ t i a, p t i a = blumMansourProb √(Fintype.card (S i) * log (Fintype.card (S i)) / T)
      (fun s c => G.deviationCost (p s) i c) t a) :
    G.IsApproxCorrelatedEquilibrium
      (fun i => 2 * √(Fintype.card (S i) * log (Fintype.card (S i)) / T))
      (timeAverage (fun t => productDist (h_nonneg t) (h_sum t)) T hT) := by
  have h_bound : ∀ i, (2 * √(T * (Fintype.card (S i) * log (Fintype.card (S i))))) / T =
      2 * √(Fintype.card (S i) * log (Fintype.card (S i)) / T) := by
    intro i
    have hX_nonneg : 0 ≤ (Fintype.card (S i) : ℝ) * log (Fintype.card (S i)) :=
      mul_nonneg (Nat.cast_nonneg _) (log_nonneg (by exact_mod_cast one_le_two.trans (hn i)))
    calc (2 * √(T * (Fintype.card (S i) * log (Fintype.card (S i))))) / T
      _ = 2 * (√(T : ℝ) * √((Fintype.card (S i) : ℝ) * log (Fintype.card (S i)))) / T := by
        rw [Real.sqrt_mul (Nat.cast_nonneg T)]
      _ = 2 * ((√(T : ℝ) / T) * √((Fintype.card (S i) : ℝ) * log (Fintype.card (S i)))) := by ring
      _ = 2 * ((1 / √(T : ℝ)) * √((Fintype.card (S i) : ℝ) * log (Fintype.card (S i)))) := by
        rw [Real.sqrt_div_self']
      _ = 2 * (√((Fintype.card (S i) : ℝ) * log (Fintype.card (S i))) / √(T : ℝ)) := by ring
      _ = 2 * √((Fintype.card (S i) * log (Fintype.card (S i))) / T) := by
        rw [← Real.sqrt_div hX_nonneg]
  have h_eq : (fun i => 2 * √(Fintype.card (S i) * log (Fintype.card (S i)) / T)) =
      fun i => (2 * √(T * (Fintype.card (S i) * log (Fintype.card (S i))))) / T := by
    ext i
    rw [← h_bound i]
  rw [h_eq]
  apply timeAverage_productDist_isApproxCorrelatedEquilibrium G hT h_nonneg h_sum
  intro i δ
  have := blumMansour_swap_regret_le_sqrt (hn i) (hT_bound i) (fun s hs a => h_cost s hs i a) δ
  have h_sum_eq1 : ∑ t ∈ range T, ∑ a, p t i a * G.deviationCost (p t) i a =
      ∑ t ∈ range T, ∑ a, blumMansourProb √(Fintype.card (S i) * log (Fintype.card (S i)) / T)
      (fun s c => G.deviationCost (p s) i c) t a * G.deviationCost (p t) i a := by
    refine sum_congr rfl fun t _ => sum_congr rfl fun a _ => ?_
    rw [h_p t i a]
  have h_sum_eq2 : ∑ t ∈ range T, ∑ a, p t i a * G.deviationCost (p t) i (δ a) =
      ∑ t ∈ range T, ∑ a, blumMansourProb √(Fintype.card (S i) * log (Fintype.card (S i)) / T)
      (fun s c => G.deviationCost (p s) i c) t a * G.deviationCost (p t) i (δ a) := by
    refine sum_congr rfl fun t _ => sum_congr rfl fun a _ => ?_
    rw [h_p t i a]
  rw [h_sum_eq1, h_sum_eq2]
  exact this
end Cslib.GameTheory.CostGame
