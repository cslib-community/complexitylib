/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Stochastic
public import CslibFrontier.MachineLearning.OnlineLearning.Hedge
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Swap regret and the Blum–Mansour reduction

A learner that plays the distribution `p t` against the losses `ℓ t` has *swap regret* at most `R`
if, for every *swapping function* `δ : ι → ι`,
`∑ t, ∑ i, p t i * ℓ t i ≤ ∑ t, ∑ i, p t i * ℓ t (δ i) + R`: replacing every play of `i` by
`δ i` saves at most `R` ([BlumMansour2007], §2; [Roughgarden2013CS364A], Lecture 18,
Definition 1.2). Constant swapping functions recover external regret, the benchmark of
`hedge_regret_le`; swap regret is stronger, and it is the notion whose dynamics converge to
correlated rather than coarse correlated equilibria ([BlumMansour2007], Theorem 3).

Blum and Mansour reduce swap regret to external regret ([BlumMansour2007], §3;
[Roughgarden2013CS364A], Lecture 18, Theorem 2.1). Run one external-regret algorithm per expert.
In round `t`, copy `j` proposes a distribution, the row `q t j` of a matrix `q t`. The learner
plays a stationary vector `p t ᵥ* q t = p t` and charges copy `j` the scaled losses
`p t j * ℓ t`. Stationarity makes the learner's loss the sum of the losses the copies see, and
copy `j`'s external regret against expert `δ j` covers the deviation `j ↦ δ j`. So the swap
regret is at most the sum of the copies' regrets (`swap_regret_le_sum_regret`,
[BlumMansour2007], Theorem 5). The theorem assumes only stationarity and the copies' regret
bounds, so it applies to any external-regret algorithms.

With Hedge copies (`blumMansourWeight`) and the stationary vectors `Matrix.stationaryVec`, the
learner (`blumMansourProb`) has swap regret at most `η T + n ln n / η` for losses in `[-1, 1]`
(`blumMansour_swap_regret_le`). Copy `j`'s second-order term is at most `η ∑ t, p t j`, so the
second-order terms of all copies sum to at most `η T`. The learning rate `η = √(n ln n / T)` gives
swap regret at most `2 √(T n ln n)` once `T ≥ n ln n` (`blumMansour_swap_regret_le_sqrt`), the
`O(√(T N log N))` bound of [BlumMansour2007], Corollary 7.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.Experts.blumMansourWeight`: the weights of the Hedge
  copies.
* `Cslib.MachineLearning.OnlineLearning.Experts.blumMansourMatrix`: the copies' distributions,
  as the rows of a row-stochastic matrix.
* `Cslib.MachineLearning.OnlineLearning.Experts.blumMansourProb`: the learner's distribution, a
  stationary vector of `blumMansourMatrix`.
* `Cslib.MachineLearning.OnlineLearning.Experts.blumMansourLoss`: the scaled losses each copy
  sees.

## Main results

* `Cslib.MachineLearning.OnlineLearning.Experts.swap_regret_le_sum_regret`: the Blum–Mansour
  reduction for arbitrary copies ([BlumMansour2007], Theorem 5).
* `Cslib.MachineLearning.OnlineLearning.Experts.blumMansourProb_congr`: the learner is online.
* `Cslib.MachineLearning.OnlineLearning.Experts.blumMansour_swap_regret_le`: swap regret with
  Hedge copies.
* `Cslib.MachineLearning.OnlineLearning.Experts.blumMansour_swap_regret_le_sqrt`: swap regret
  `2 √(T n ln n)` with the tuned learning rate ([BlumMansour2007], Corollary 7).

## References

* [A. Blum, Y. Mansour, *From External to Internal Regret*][BlumMansour2007]
* [T. Roughgarden, *CS364A: Algorithmic Game Theory*][Roughgarden2013CS364A]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.Experts

open Finset Matrix Real

variable {ι : Type*} [Fintype ι]

/-- **The Blum–Mansour reduction** [BlumMansour2007, Theorem 5]. Let the learner play `p t`, a
stationary vector of the matrix `q t` whose row `j` is the distribution of copy `j`, and let copy
`j` see the losses `p t j * ℓ t`. If copy `j` has regret at most `R j` against every expert, then
the learner has swap regret at most `∑ j, R j`: for every swapping function `δ`,
`∑ t, ⟨p t, ℓ t⟩ ≤ ∑ t, ∑ i, p t i * ℓ t (δ i) + ∑ j, R j`. -/
theorem swap_regret_le_sum_regret {p : ℕ → ι → ℝ} {q : ℕ → Matrix ι ι ℝ} {ℓ : ℕ → ι → ℝ}
    {T : ℕ} {R : ι → ℝ} (hp : ∀ t, p t ᵥ* q t = p t)
    (hR : ∀ j k, ∑ t ∈ range T, ∑ i, q t j i * (p t j * ℓ t i) ≤
      ∑ t ∈ range T, p t j * ℓ t k + R j) (δ : ι → ι) :
    ∑ t ∈ range T, ∑ i, p t i * ℓ t i ≤ ∑ t ∈ range T, ∑ i, p t i * ℓ t (δ i) + ∑ j, R j := by
  have key : ∀ t, ∑ j, ∑ i, q t j i * (p t j * ℓ t i) = ∑ i, p t i * ℓ t i := fun t => by
    conv_rhs => rw [← hp t]
    simp only [vecMul_apply_eq_sum, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  calc ∑ t ∈ range T, ∑ i, p t i * ℓ t i
      = ∑ t ∈ range T, ∑ j, ∑ i, q t j i * (p t j * ℓ t i) :=
        sum_congr rfl fun t _ => (key t).symm
    _ = ∑ j, ∑ t ∈ range T, ∑ i, q t j i * (p t j * ℓ t i) := sum_comm
    _ ≤ ∑ j, (∑ t ∈ range T, p t j * ℓ t (δ j) + R j) := sum_le_sum fun j _ => hR j (δ j)
    _ = ∑ t ∈ range T, ∑ i, p t i * ℓ t (δ i) + ∑ j, R j := by rw [sum_add_distrib, sum_comm]

/-! ### Hedge copies -/

variable [DecidableEq ι]

/-- The weights of the Hedge copies in the Blum–Mansour algorithm with learning rate `η`:
`blumMansourWeight η ℓ t j i` is the weight that copy `j` gives expert `i` in round `t`. Copy
`j` sees the losses `ℓ t` scaled by the learner's probability of `j`, the `j`-th entry of a
stationary vector of the copies' normalized weights. -/
noncomputable def blumMansourWeight (η : ℝ) (ℓ : ℕ → ι → ℝ) : ℕ → ι → ι → ℝ
  | 0 => fun _ _ => 1
  | t + 1 => fun j i => blumMansourWeight η ℓ t j i *
      hedgeFactor η (stationaryVec (of fun j' i' =>
        blumMansourWeight η ℓ t j' i' / ∑ k, blumMansourWeight η ℓ t j' k) j * ℓ t i)

/-- The copies' distributions in round `t`: row `j` is the normalized weights of copy `j`. -/
noncomputable def blumMansourMatrix (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) : Matrix ι ι ℝ :=
  of fun j i => blumMansourWeight η ℓ t j i / ∑ k, blumMansourWeight η ℓ t j k

/-- The distribution of the Blum–Mansour learner in round `t`: the chosen stationary vector of
`blumMansourMatrix`. -/
noncomputable def blumMansourProb (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) : ι → ℝ :=
  stationaryVec (blumMansourMatrix η ℓ t)

/-- The losses copy `j` sees: the loss vector `ℓ t` scaled by the learner's probability of `j`. -/
noncomputable def blumMansourLoss (η : ℝ) (ℓ : ℕ → ι → ℝ) (j : ι) (t : ℕ) (i : ι) : ℝ :=
  blumMansourProb η ℓ t j * ℓ t i

variable {η : ℝ} {ℓ : ℕ → ι → ℝ} {T : ℕ}

/-- Copy `j` sees the loss `ℓ t i` of expert `i` scaled by the learner's probability of `j`. -/
theorem blumMansourLoss_apply (η : ℝ) (ℓ : ℕ → ι → ℝ) (j : ι) (t : ℕ) (i : ι) :
    blumMansourLoss η ℓ j t i = blumMansourProb η ℓ t j * ℓ t i := by
  rw [blumMansourLoss]

/-- Every copy starts with weight `1` on every expert. -/
@[simp] theorem blumMansourWeight_zero (η : ℝ) (ℓ : ℕ → ι → ℝ) (j i : ι) :
    blumMansourWeight η ℓ 0 j i = 1 := by
  rw [blumMansourWeight]

/-- Copy `j` multiplies the weight of expert `i` by the Hedge factor of its scaled loss. -/
theorem blumMansourWeight_succ (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (j i : ι) :
    blumMansourWeight η ℓ (t + 1) j i =
      blumMansourWeight η ℓ t j i * hedgeFactor η (blumMansourProb η ℓ t j * ℓ t i) := by
  rw [blumMansourWeight, blumMansourProb, blumMansourMatrix]

/-- Copy `j` is Hedge run on the losses `blumMansourLoss η ℓ j`. -/
theorem blumMansourWeight_eq_weight (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (j : ι) :
    blumMansourWeight η ℓ t j = weight (hedgeFactor η) (blumMansourLoss η ℓ j) t := by
  induction t with
  | zero =>
    funext i
    rw [weight_zero, blumMansourWeight_zero]
  | succ t ih =>
    funext i
    rw [weight_succ, ← ih, blumMansourWeight_succ, blumMansourLoss_apply]

/-- Row `j` of `blumMansourMatrix` is the distribution of Hedge on the losses copy `j` sees. -/
theorem blumMansourMatrix_eq_prob (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (j : ι) :
    blumMansourMatrix η ℓ t j = prob (hedgeFactor η) (blumMansourLoss η ℓ j) t := by
  funext i
  simp only [blumMansourMatrix, of_apply, prob, potential, blumMansourWeight_eq_weight]

/-- The copies' distributions form a row-stochastic matrix. -/
theorem blumMansourMatrix_mem_rowStochastic [Nonempty ι] (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    blumMansourMatrix η ℓ t ∈ rowStochastic ℝ ι := by
  have hφ : ∀ j, ∀ s < t, ∀ i, 0 < hedgeFactor η (blumMansourLoss η ℓ j s i) :=
    fun _ _ _ _ => by rw [hedgeFactor_apply]; exact exp_pos _
  refine mem_rowStochastic_iff_sum.2 ⟨fun j i => ?_, fun j => ?_⟩
  · rw [blumMansourMatrix_eq_prob]
    exact prob_nonneg (hφ j) i
  · rw [blumMansourMatrix_eq_prob]
    exact sum_prob (hφ j)

/-- The learner's probabilities are nonnegative. -/
theorem blumMansourProb_nonneg [Nonempty ι] (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    0 ≤ blumMansourProb η ℓ t i :=
  stationaryVec_nonneg (blumMansourMatrix_mem_rowStochastic η ℓ t) i

/-- The learner plays a probability distribution. -/
theorem sum_blumMansourProb [Nonempty ι] (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    ∑ i, blumMansourProb η ℓ t i = 1 :=
  sum_stationaryVec (blumMansourMatrix_mem_rowStochastic η ℓ t)

/-- The learner's probabilities are at most `1`. -/
theorem blumMansourProb_le_one [Nonempty ι] (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    blumMansourProb η ℓ t i ≤ 1 :=
  (single_le_sum (fun j _ => blumMansourProb_nonneg η ℓ t j) (mem_univ i)).trans_eq
    (sum_blumMansourProb η ℓ t)

/-- The learner's distribution is stationary for the copies' distributions. -/
theorem blumMansourProb_vecMul [Nonempty ι] (η : ℝ) (ℓ : ℕ → ι → ℝ) (t : ℕ) :
    blumMansourProb η ℓ t ᵥ* blumMansourMatrix η ℓ t = blumMansourProb η ℓ t :=
  stationaryVec_vecMul (blumMansourMatrix_mem_rowStochastic η ℓ t)

/-- The copies' weights in round `t` depend only on the losses before round `t`. -/
theorem blumMansourWeight_congr {ℓ' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t, ℓ s = ℓ' s) :
    blumMansourWeight η ℓ t = blumMansourWeight η ℓ' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext j i
    rw [blumMansourWeight_succ, blumMansourWeight_succ, blumMansourProb, blumMansourProb,
      blumMansourMatrix, blumMansourMatrix, ih fun s hs => h s (by omega), h t (by omega)]

/-- The learner's distribution in round `t` depends only on the losses before round `t`: the
Blum–Mansour learner is an online algorithm. -/
theorem blumMansourProb_congr {ℓ' : ℕ → ι → ℝ} {t : ℕ} (h : ∀ s < t, ℓ s = ℓ' s) :
    blumMansourProb η ℓ t = blumMansourProb η ℓ' t := by
  rw [blumMansourProb, blumMansourProb, blumMansourMatrix, blumMansourMatrix,
    blumMansourWeight_congr h]

/-- **Swap regret of the Blum–Mansour algorithm with Hedge copies**: for losses in `[-1, 1]`
and `0 < η ≤ 1`, for every swapping function `δ`,
`∑ t, ⟨p t, ℓ t⟩ ≤ ∑ t, ∑ i, p t i * ℓ t (δ i) + η T + n ln n / η`. -/
theorem blumMansour_swap_regret_le [Nonempty ι] (hη : 0 < η) (hη' : η ≤ 1)
    (hℓ : ∀ s < T, ∀ i, |ℓ s i| ≤ 1) (δ : ι → ι) :
    ∑ t ∈ range T, ∑ i, blumMansourProb η ℓ t i * ℓ t i ≤
      ∑ t ∈ range T, ∑ i, blumMansourProb η ℓ t i * ℓ t (δ i) +
        (η * T + Fintype.card ι * log (Fintype.card ι) / η) := by
  refine (swap_regret_le_sum_regret (q := blumMansourMatrix η ℓ)
    (R := fun j => η * ∑ t ∈ range T, blumMansourProb η ℓ t j + log (Fintype.card ι) / η)
    (blumMansourProb_vecMul η ℓ) (fun j k => ?_) δ).trans ?_
  · have hℓj : ∀ s < T, ∀ i, |blumMansourLoss η ℓ j s i| ≤ 1 := fun s hs i => by
      rw [blumMansourLoss_apply, abs_mul, abs_of_nonneg (blumMansourProb_nonneg η ℓ s j)]
      exact (mul_le_mul (blumMansourProb_le_one η ℓ s j) (hℓ s hs i) (abs_nonneg _)
        zero_le_one).trans_eq (one_mul 1)
    have h := hedge_regret_le hη hη' hℓj k
    have hsq : ∑ t ∈ range T, ∑ i, prob (hedgeFactor η) (blumMansourLoss η ℓ j) t i *
        blumMansourLoss η ℓ j t i ^ 2 ≤ ∑ t ∈ range T, blumMansourProb η ℓ t j :=
      sum_le_sum fun t ht => by
        have hφ : ∀ s < t, ∀ i, 0 < hedgeFactor η (blumMansourLoss η ℓ j s i) :=
          fun _ _ _ => by rw [hedgeFactor_apply]; exact exp_pos _
        have hp0 := blumMansourProb_nonneg η ℓ t j
        have hp1 := blumMansourProb_le_one η ℓ t j
        calc ∑ i, prob (hedgeFactor η) (blumMansourLoss η ℓ j) t i * blumMansourLoss η ℓ j t i ^ 2
            ≤ ∑ i, prob (hedgeFactor η) (blumMansourLoss η ℓ j) t i * blumMansourProb η ℓ t j :=
              sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (by
                have h2 : ℓ t i ^ 2 ≤ 1 := by
                  rw [← sq_abs]
                  nlinarith [abs_nonneg (ℓ t i), hℓ t (mem_range.mp ht) i]
                rw [blumMansourLoss_apply, mul_pow]
                nlinarith [mul_nonneg hp0 (sub_nonneg.2 hp1),
                  mul_nonneg (sq_nonneg (blumMansourProb η ℓ t j)) (sub_nonneg.2 h2)])
                (prob_nonneg hφ i)
          _ = blumMansourProb η ℓ t j := by rw [← sum_mul, sum_prob hφ, one_mul]
    simp only [← blumMansourMatrix_eq_prob, blumMansourLoss_apply] at h hsq
    linarith [mul_le_mul_of_nonneg_left hsq hη.le]
  · have hT : ∑ j, ∑ t ∈ range T, blumMansourProb η ℓ t j = T := by
      rw [sum_comm]
      simp only [sum_blumMansourProb, sum_const, card_range, nsmul_eq_mul, mul_one]
    have hR : ∑ j, (η * ∑ t ∈ range T, blumMansourProb η ℓ t j + log (Fintype.card ι) / η) =
        η * T + Fintype.card ι * log (Fintype.card ι) / η := by
      rw [sum_add_distrib, ← mul_sum, hT, sum_const, card_univ, nsmul_eq_mul, mul_div_assoc]
    linarith [hR]

/-- **Tuned swap regret of the Blum–Mansour algorithm** [BlumMansour2007, Corollary 7]: for
`n ≥ 2` experts, losses in `[-1, 1]` and `T ≥ n ln n` rounds, Hedge copies with learning rate
`η = √(n ln n / T)` give swap regret at most `2 √(T n ln n)`. -/
theorem blumMansour_swap_regret_le_sqrt (hn : 2 ≤ Fintype.card ι)
    (hT : Fintype.card ι * log (Fintype.card ι) ≤ T) (hℓ : ∀ s < T, ∀ i, |ℓ s i| ≤ 1)
    (δ : ι → ι) :
    ∑ t ∈ range T, ∑ i,
        blumMansourProb √(Fintype.card ι * log (Fintype.card ι) / T) ℓ t i * ℓ t i ≤
      ∑ t ∈ range T, ∑ i,
          blumMansourProb √(Fintype.card ι * log (Fintype.card ι) / T) ℓ t i * ℓ t (δ i) +
        2 * √(T * (Fintype.card ι * log (Fintype.card ι))) := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hL : (0 : ℝ) < Fintype.card ι * log (Fintype.card ι) :=
    mul_pos (Nat.cast_pos.2 (by omega)) (log_pos (by exact_mod_cast hn))
  have hT0 : (0 : ℝ) < T := hL.trans_le hT
  have hη : 0 < √(Fintype.card ι * log (Fintype.card ι) / T) := sqrt_pos.mpr (div_pos hL hT0)
  have hη' : √(Fintype.card ι * log (Fintype.card ι) / T) ≤ 1 :=
    calc √(Fintype.card ι * log (Fintype.card ι) / T) ≤ √1 :=
          sqrt_le_sqrt (by rw [div_le_one hT0]; exact hT)
      _ = 1 := sqrt_one
  refine (blumMansour_swap_regret_le hη hη' hℓ δ).trans_eq ?_
  rw [sqrt_div_mul_add_div_sqrt_div hL hT0]

end Cslib.MachineLearning.OnlineLearning.Experts
