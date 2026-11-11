/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.Finset.Median
public import CslibFrontier.MachineLearning.Replicable.Basic
public import CslibFrontier.MachineLearning.Replicable.Composition
public import CslibFrontier.MachineLearning.Replicable.Rounding
public import CslibFrontier.Probability.Collision
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.MachineLearning.Replicable.BiasEstimation
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Markov
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Union

/-!
# Amplification of accuracy and replicability

This module formalizes confidence and replicability amplification theorems for shared-seed
replicable algorithms [ImpagliazzoLeiPitassiSorrell2022]:

* **Confidence amplification**: repeating an algorithm `2 * (r + 1)` times with independent shared
  seeds and taking `majorityVote` (for `Bool` outputs) or `medianOfRuns` (for `ℝ` outputs via
  `Cslib.median`) reduces failure probability from `β₀ ≤ 1 / 2` to `(4 * β₀ * (1 - β₀)) ^ (r + 1)`
  while scaling the disagreement parameter by `2 * (r + 1)`.
* **Finite-domain amplification (`amplifyFinite`)**: when the output space `α` is finite (`M = |α|`)
  and linearly ordered, any algorithm (with no replicability guarantee at all) whose failure
  probability satisfies `β₀ < 1 / (M + 1)` can be amplified to arbitrary `(ρ, β)` with **strong**
  (distribution-free) `ρ`-replicability by estimating empirical frequencies over `k` independent
  runs and thresholding against a single shared random threshold `i : Fin N`.
* **General-domain replicability amplification (`amplifyReplicability`)**:
  for any `[DecidableEq α]`, any algorithm that is weakly (or strongly) `ρ₀`-replicable with
  `ρ₀ < 1 / 2` can be amplified to arbitrary `ρ > 0` by sampling `T` candidate seeds, estimating
  collision rates and strict majorities, and picking the first candidate seed whose empirical
  collision rate crosses a single shared random threshold `i : Fin N`. When the input algorithm
  also has sufficiently small initial error `β₀ = O(β / T)` (with `β₀ / (a - δ)` union-bounded
  across the `T` candidate seeds by Markov's inequality in `isAccurateFor_amplifyReplicability`
  and `exists_amplifyReplicability_accurate`), `amplifyReplicability` also achieves `(good, β)`
  accuracy; unlike `amplifyFinite`, `pickFirstThresholded` does not assume `β₀ < 1 / (|α| + 1)`
  and therefore preserves small initial error rather than amplifying error from `≈ 1 / 2`.

## Main definitions

* `Cslib.MachineLearning.Replicable.majorityVote`: `Bool` confidence amplification.
* `Cslib.MachineLearning.Replicable.medianOfRuns`: `ℝ` confidence amplification via `Cslib.median`.
* `Cslib.MachineLearning.Replicable.amplifyFinite`: finite-domain heavy-hitter amplification.
* `Cslib.MachineLearning.Replicable.amplifyReplicability`: general-domain collision-threshold
  replicability amplification.

## Main results

* `Cslib.MachineLearning.Replicable.majorityVote_accurate`,
  `Cslib.MachineLearning.Replicable.majorityVote_replicable`,
  `Cslib.MachineLearning.Replicable.exists_majorityVote`: boolean majority amplification.
* `Cslib.MachineLearning.Replicable.medianOfRuns_accurate`,
  `Cslib.MachineLearning.Replicable.medianOfRuns_replicable`,
  `Cslib.MachineLearning.Replicable.exists_medianOfRuns`: median-of-runs amplification.
* `Cslib.MachineLearning.Replicable.isReplicable_amplifyFinite`,
  `Cslib.MachineLearning.Replicable.isAccurateFor_amplifyFinite`,
  `Cslib.MachineLearning.Replicable.exists_amplifyFinite`: finite-domain amplification from
  `β₀ < 1 / (|α| + 1)` to arbitrary strong `ρ` and accuracy `β`.
* `Cslib.MachineLearning.Replicable.disagreeProb_amplifyReplicability_le`,
  `Cslib.MachineLearning.Replicable.isAccurateFor_amplifyReplicability`,
  `Cslib.MachineLearning.Replicable.exists_amplifyReplicability`,
  `Cslib.MachineLearning.Replicable.exists_amplifyReplicability_accurate`: amplifying
  `ρ₀ < 1 / 2` to arbitrary `ρ > 0` over any `[DecidableEq α]`, with preserved accuracy under
  `O(β / T)` initial error.

## References

* [Impagliazzo, Lei, Pitassi, Sorrell (STOC 2022)][ImpagliazzoLeiPitassiSorrell2022],
  *Reproducibility in Learning* (paper PDF not directly inspected in this formalization;
  definitions and finite/general amplification theorems are formalized directly in Lean).
-/

public section

namespace Cslib.MachineLearning.Replicable

universe u v w

open scoped ENNReal

section Helpers

private theorem exists_heavy_of_le_tsum_sq {α : Type*} (p : PMF α) {c : ℝ}
    (hle : c ≤ Probability.PMF.collisionProbability p) : ∃ a, c ≤ (p a).toReal := by
  by_contra hnone
  push Not at hnone
  have htsum1 : ∑' a, (p a).toReal = 1 := Probability.PMF.tsum_toReal p
  have hex : ∃ a₀, 0 < (p a₀).toReal := by
    by_contra hzero
    push Not at hzero
    have hall : ∀ a, (p a).toReal = 0 := fun a => le_antisymm (hzero a) ENNReal.toReal_nonneg
    simp [hall] at htsum1
  obtain ⟨a₀, ha₀⟩ := hex
  have hle_pt : ∀ a, (p a).toReal ^ 2 ≤ c * (p a).toReal := fun a => by
    have hlt := hnone a
    have hnn : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
    nlinarith
  have hlt_a₀ : (p a₀).toReal ^ 2 < c * (p a₀).toReal := by
    have hlt := hnone a₀
    nlinarith
  have hlt_sum : Probability.PMF.collisionProbability p < ∑' a, c * (p a).toReal :=
    (Probability.PMF.summable_collision p).tsum_lt_tsum hle_pt hlt_a₀
      ((Probability.PMF.summable_toReal p).mul_left c)
  rw [tsum_mul_left, htsum1, mul_one] at hlt_sum
  linarith

private theorem four_mul_one_sub_lt_one {β₀ : ℝ} (hnn : 0 ≤ β₀) (hlt : β₀ < 1 / 2) :
    0 ≤ 4 * β₀ * (1 - β₀) ∧ 4 * β₀ * (1 - β₀) < 1 := by
  refine ⟨by nlinarith, ?_⟩
  have hpos : 0 < 1 - 2 * β₀ := by linarith
  nlinarith [sq_pos_of_pos hpos]

private theorem exp_decay_exists (M : ℝ) {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 0 < k ∧ M * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2)) ≤ ε := by
  let B : ℝ := max (2 * M) 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let t : ℝ := Real.log (B / ε) / (2 * δ ^ 2)
  obtain ⟨k, hk⟩ := exists_nat_gt (max t 0)
  have hkpos : 0 < k := by
    exact_mod_cast lt_of_le_of_lt (le_max_right t 0) hk
  refine ⟨k, hkpos, ?_⟩
  have hkt : t < (k : ℝ) := lt_of_le_of_lt (le_max_left t 0) hk
  have harg : Real.log (B / ε) < 2 * (k : ℝ) * δ ^ 2 := by
    have h2 : 0 < 2 * δ ^ 2 := by positivity
    calc Real.log (B / ε) = t * (2 * δ ^ 2) := by
          dsimp only [t]
          field_simp [h2.ne']
      _ < (k : ℝ) * (2 * δ ^ 2) := mul_lt_mul_of_pos_right hkt h2
      _ = 2 * (k : ℝ) * δ ^ 2 := by ring
  have hexp : Real.exp (-2 * (k : ℝ) * δ ^ 2) ≤ ε / B := by
    rw [show -2 * (k : ℝ) * δ ^ 2 = -(2 * (k : ℝ) * δ ^ 2) by ring, Real.exp_neg, inv_eq_one_div,
      one_div_le (Real.exp_pos _) (div_pos hε hB), one_div_div]
    calc B / ε = Real.exp (Real.log (B / ε)) := (Real.exp_log (div_pos hB hε)).symm
      _ ≤ Real.exp (2 * (k : ℝ) * δ ^ 2) := Real.exp_le_exp.mpr harg.le
  calc M * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2))
      = (2 * M) * Real.exp (-2 * (k : ℝ) * δ ^ 2) := by ring
    _ ≤ B * (ε / B) :=
        mul_le_mul (le_max_left _ _) hexp (Real.exp_pos _).le hB.le
    _ = ε := mul_div_cancel₀ ε hB.ne'

private theorem iid_bad_coord_le {γ : Type*} (q_marg : PMF γ) (bad : γ → Bool) {β₀ : ℝ}
    (hq : ((q_marg.map bad) true).toReal ≤ β₀) (hβ₀ : β₀ ≤ 1 / 2)
    (t : ℕ) {S : Set (Fin (2 * t) → γ)}
    (hsub : S ⊆ (fun v j => bad (v j)) ⁻¹'
      {w : Fin (2 * t) → Bool | t ≤ (Finset.univ.filter fun j => w j = true).card}) :
    ((Probability.PMF.iid q_marg (2 * t)).toOuterMeasure S).toReal ≤
      (4 * β₀ * (1 - β₀)) ^ t := by
  calc ((Probability.PMF.iid q_marg (2 * t)).toOuterMeasure S).toReal
      ≤ ((Probability.PMF.iid q_marg (2 * t)).toOuterMeasure
          ((fun v j => bad (v j)) ⁻¹'
            {w : Fin (2 * t) → Bool | t ≤ (Finset.univ.filter fun j => w j = true).card})).toReal :=
        Probability.PMF.toOuterMeasure_toReal_mono _ hsub
    _ = ((Probability.PMF.iid (q_marg.map bad) (2 * t)).toOuterMeasure
          {w : Fin (2 * t) → Bool | t ≤ (Finset.univ.filter fun j => w j = true).card}).toReal := by
        rw [← PMF.toOuterMeasure_map_apply, (Probability.PMF.iid_map q_marg bad (2 * t)).symm]
    _ ≤ (4 * β₀ * (1 - β₀)) ^ t := Probability.PMF.iid_card_ge_le hq hβ₀ t

end Helpers

/-! ### Confidence amplification: majority vote and median-of-runs -/

section ConfidenceAmplification

variable {X : Type u} {Ω : Type v} {m : ℕ}

/-- Run a Boolean algorithm `2 * (r + 1)` times on disjoint blocks with independent shared seeds
and return the majority bit (breaking ties toward `true`). -/
@[expose] noncomputable def majorityVote (A : Algorithm X Ω Bool m) (r : ℕ) :
    Algorithm X (Fin (2 * (r + 1)) → Ω) Bool (2 * (r + 1) * m) :=
  (A.replicate (2 * (r + 1))).map fun v =>
    decide (r + 1 ≤ (Finset.univ.filter fun j => v j = true).card)

theorem majorityVote_replicable {A : Algorithm X Ω Bool m} {𝒟 : Set (PMF X)} {ρ : ℝ}
    (h : IsReplicableFor A 𝒟 ρ) (r : ℕ) :
    IsReplicableFor (majorityVote A r) 𝒟 ((2 * (r + 1) : ℕ) * ρ) :=
  (h.replicate (k := 2 * (r + 1))).map _

theorem majorityVote_accurate {A : Algorithm X Ω Bool m} {𝒟 : Set (PMF X)}
    {target : PMF X → Bool} {β₀ : ℝ} (hacc : IsAccurateFor A 𝒟 (fun D => {target D}) β₀)
    (hβ₀ : β₀ ≤ 1 / 2) (r : ℕ) :
    IsAccurateFor (majorityVote A r) 𝒟 (fun D => {target D}) ((4 * β₀ * (1 - β₀)) ^ (r + 1)) := by
  intro D hD
  let q : PMF Bool := (A.marginal D).map (fun b => decide (b ≠ target D))
  have hq : (q true).toReal ≤ β₀ := by
    calc (q true).toReal
        = (q.toOuterMeasure {true}).toReal := by rw [PMF.toOuterMeasure_apply_singleton]
      _ = ((A.marginal D).toOuterMeasure {b | b ≠ target D}).toReal := by
          rw [PMF.toOuterMeasure_map_apply]
          congr 2
          ext b
          simp
      _ = ((A.marginal D).toOuterMeasure ({target D} : Set Bool)ᶜ).toReal := rfl
      _ ≤ β₀ := hacc D hD
  have hmarg : (majorityVote A r).marginal D =
      (Probability.PMF.iid (A.marginal D) (2 * (r + 1))).map fun v =>
        decide (r + 1 ≤ (Finset.univ.filter fun j => v j = true).card) := by
    rw [majorityVote, Algorithm.marginal_map, Algorithm.marginal_replicate]
  rw [hmarg, PMF.toOuterMeasure_map_apply]
  have hsub :
      (fun v : Fin (2 * (r + 1)) → Bool =>
        decide (r + 1 ≤ (Finset.univ.filter fun j => v j = true).card)) ⁻¹'
        ({target D} : Set Bool)ᶜ ⊆
      (fun v : Fin (2 * (r + 1)) → Bool => fun j => decide (v j ≠ target D)) ⁻¹'
        {w : Fin (2 * (r + 1)) → Bool |
          r + 1 ≤ (Finset.univ.filter fun j => w j = true).card} := by
    intro v hv
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_ofPred_eq] at hv ⊢
    cases ht : target D
    · simp only [ht, ne_eq, decide_eq_true_eq, Bool.not_eq_false] at hv ⊢
      exact hv
    · simp only [ht, ne_eq, decide_eq_true_eq, Bool.not_eq_true] at hv ⊢
      have hpart :
          (Finset.univ.filter fun j : Fin (2 * (r + 1)) => v j = true).card +
            (Finset.univ.filter fun j : Fin (2 * (r + 1)) => v j = false).card =
          2 * (r + 1) := by
        rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
        calc ∑ j : Fin (2 * (r + 1)), ((if v j = true then 1 else 0) +
                (if v j = false then 1 else 0))
            = ∑ _j : Fin (2 * (r + 1)), 1 :=
              Finset.sum_congr rfl fun j _ => by cases v j <;> simp
          _ = 2 * (r + 1) := by simp
      omega
  exact iid_bad_coord_le (A.marginal D) (fun b => decide (b ≠ target D)) hq hβ₀ (r + 1) hsub

/-- For any Boolean algorithm with error `β₀ < 1 / 2` and any target `β > 0`, taking the majority
of `2 * (r + 1)` independent repetitions achieves failure probability at most `β`. -/
theorem exists_majorityVote {A : Algorithm X Ω Bool m} {𝒟 : Set (PMF X)}
    {target : PMF X → Bool} {β₀ β : ℝ} (hacc : IsAccurateFor A 𝒟 (fun D => {target D}) β₀)
    (hβ₀_nonneg : 0 ≤ β₀) (hβ₀ : β₀ < 1 / 2) (hβ : 0 < β) :
    ∃ r : ℕ, IsAccurateFor (majorityVote A r) 𝒟 (fun D => {target D}) β := by
  obtain ⟨hbase0, hbase1⟩ := four_mul_one_sub_lt_one hβ₀_nonneg hβ₀
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hβ hbase1
  have hle : (4 * β₀ * (1 - β₀)) ^ (r + 1) ≤ β :=
    (pow_le_pow_of_le_one hbase0 hbase1.le (Nat.le_succ r)).trans hr.le
  exact ⟨r, (majorityVote_accurate hacc hβ₀.le r).mono hle⟩

/-- Run a real-valued algorithm `2 * (r + 1)` times on disjoint blocks with independent shared
seeds and output `Cslib.median`. -/
@[expose] noncomputable def medianOfRuns (A : Algorithm X Ω ℝ m) (r : ℕ) :
    Algorithm X (Fin (2 * (r + 1)) → Ω) ℝ (2 * (r + 1) * m) :=
  (A.replicate (2 * (r + 1))).map Cslib.median

theorem medianOfRuns_replicable {A : Algorithm X Ω ℝ m} {𝒟 : Set (PMF X)} {ρ : ℝ}
    (h : IsReplicableFor A 𝒟 ρ) (r : ℕ) :
    IsReplicableFor (medianOfRuns A r) 𝒟 ((2 * (r + 1) : ℕ) * ρ) :=
  (h.replicate (k := 2 * (r + 1))).map _

theorem medianOfRuns_accurate {A : Algorithm X Ω ℝ m} {𝒟 : Set (PMF X)}
    {target : PMF X → ℝ} {ε β₀ : ℝ} (hacc : EstimatesFor A 𝒟 target ε β₀) (hβ₀ : β₀ ≤ 1 / 2)
    (r : ℕ) :
    EstimatesFor (medianOfRuns A r) 𝒟 target ε ((4 * β₀ * (1 - β₀)) ^ (r + 1)) := by
  intro D hD
  let q : PMF Bool := (A.marginal D).map (fun y => decide (ε < |y - target D|))
  have hq : (q true).toReal ≤ β₀ := by
    calc (q true).toReal
        = (q.toOuterMeasure {true}).toReal := by rw [PMF.toOuterMeasure_apply_singleton]
      _ = ((A.marginal D).toOuterMeasure {y | ε < |y - target D|}).toReal := by
          rw [PMF.toOuterMeasure_map_apply]
          congr 2
          ext y
          simp
      _ = ((A.marginal D).toOuterMeasure ({y | |y - target D| ≤ ε})ᶜ).toReal := by
          congr 2
          ext y
          simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
      _ ≤ β₀ := hacc D hD
  have hmarg : (medianOfRuns A r).marginal D =
      (Probability.PMF.iid (A.marginal D) (2 * (r + 1))).map Cslib.median := by
    rw [medianOfRuns, Algorithm.marginal_map, Algorithm.marginal_replicate]
  rw [hmarg, PMF.toOuterMeasure_map_apply]
  have hsub :
      Cslib.median ⁻¹' ({y | |y - target D| ≤ ε})ᶜ ⊆
      (fun v : Fin (2 * (r + 1)) → ℝ => fun j => decide (ε < |v j - target D|)) ⁻¹'
        {w : Fin (2 * (r + 1)) → Bool |
          r + 1 ≤ (Finset.univ.filter fun j => w j = true).card} := by
    intro v hv
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le,
      decide_eq_true_eq] at hv ⊢
    have hnot : ¬ Fintype.card (Fin (2 * (r + 1))) <
        2 * (Finset.univ.filter fun j : Fin (2 * (r + 1)) => |v j - target D| ≤ ε).card := by
      intro hlt
      exact absurd (Cslib.abs_median_sub_le hlt) (not_le.mpr hv)
    rw [Fintype.card_fin, not_lt] at hnot
    have hpart :
        (Finset.univ.filter fun j : Fin (2 * (r + 1)) => |v j - target D| ≤ ε).card +
          (Finset.univ.filter fun j : Fin (2 * (r + 1)) => ¬ |v j - target D| ≤ ε).card =
        2 * (r + 1) := by
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
      calc ∑ j : Fin (2 * (r + 1)), ((if |v j - target D| ≤ ε then 1 else 0) +
              (if ¬ |v j - target D| ≤ ε then 1 else 0))
          = ∑ _j : Fin (2 * (r + 1)), 1 :=
            Finset.sum_congr rfl fun j _ => by by_cases h : |v j - target D| ≤ ε <;> simp [h]
        _ = 2 * (r + 1) := by simp
    have heq : (Finset.univ.filter fun j : Fin (2 * (r + 1)) => ε < |v j - target D|) =
        Finset.univ.filter fun j : Fin (2 * (r + 1)) => ¬ |v j - target D| ≤ ε := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    rw [heq]
    omega
  exact iid_bad_coord_le (A.marginal D) (fun y => decide (ε < |y - target D|)) hq hβ₀ (r + 1) hsub

/-- For any real estimator within `ε` except with probability `β₀ < 1 / 2` and any `β > 0`,
`medianOfRuns` achieves `(ε, β)` estimation accuracy. -/
theorem exists_medianOfRuns {A : Algorithm X Ω ℝ m} {𝒟 : Set (PMF X)}
    {target : PMF X → ℝ} {ε β₀ β : ℝ} (hacc : EstimatesFor A 𝒟 target ε β₀)
    (hβ₀_nonneg : 0 ≤ β₀) (hβ₀ : β₀ < 1 / 2) (hβ : 0 < β) :
    ∃ r : ℕ, EstimatesFor (medianOfRuns A r) 𝒟 target ε β := by
  obtain ⟨hbase0, hbase1⟩ := four_mul_one_sub_lt_one hβ₀_nonneg hβ₀
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hβ hbase1
  have hle : (4 * β₀ * (1 - β₀)) ^ (r + 1) ≤ β :=
    (pow_le_pow_of_le_one hbase0 hbase1.le (Nat.le_succ r)).trans hr.le
  exact ⟨r, (medianOfRuns_accurate hacc hβ₀.le r).mono le_rfl hle⟩

end ConfidenceAmplification

/-! ### Finite-domain heavy-hitter amplification -/

section FiniteDomainAmplification

variable {X : Type u} {Ω : Type v} {α : Type w} {m : ℕ}

/-- Empirical frequency of `y : α` in a tuple `v : Fin k → α`. -/
@[expose] noncomputable def empFreq [DecidableEq α] (k : ℕ) (v : Fin k → α) (y : α) : ℝ :=
  ((Finset.univ.filter fun j : Fin k => v j = y).card : ℝ) / k

/-- Least element of `α` whose empirical frequency crosses `thresholdValue a b N i`, falling back
to `Finset.univ.min'` if none qualifies. -/
@[expose] noncomputable def pickThresholded [Fintype α] [Nonempty α] [LinearOrder α]
    (a b : ℝ) (N k : ℕ) (i : Fin N) (v : Fin k → α) : α :=
  let cand := Finset.univ.filter fun y : α => thresholdRound a b N i (empFreq k v y) = true
  if h : cand.Nonempty then cand.min' h else Finset.univ.min' Finset.univ_nonempty

/-- Finite-domain heavy-hitter amplification: runs `A` independently with fresh internal seeds on
`k` disjoint `m`-sample blocks, shares a single threshold `i : Fin N` across `[a, b)`, and
outputs the least element whose empirical frequency crosses `thresholdValue a b N i`. -/
@[expose] noncomputable def amplifyFinite [Fintype α] [Nonempty α] [LinearOrder α]
    (A : Algorithm X Ω α m) (a b : ℝ) (k N : ℕ) [NeZero N] :
    Algorithm X (Fin N) α (k * m) where
  seed := Probability.PMF.uniformOfFintype (Fin N)
  run S i :=
    (pmfPiFin fun j : Fin k => A.output (BitString.block (m := k) (k := m) S j)).map fun v =>
      pickThresholded a b N k i v

private theorem iid_splitBlocks_output_eq_iid (A : Algorithm X Ω α m) (D : PMF X) (k : ℕ) :
    ((Probability.PMF.iid D (k * m)).bind fun S =>
      pmfPiFin fun j => A.output (BitString.block (m := k) (k := m) S j)) =
      Probability.PMF.iid (A.marginal D) k := by
  have hm := (PMF.bind_map (Probability.PMF.iid D (k * m))
    (BitString.block (α := X) (m := k) (k := m))
    fun B => pmfPiFin fun j => A.output (B j)).symm
  dsimp only [Function.comp_def] at hm
  rw [hm, iid_map_block, ← pmfPiFin_const, pmfPiFin_bind]
  exact pmfPiFin_const (A.marginal D) k

private theorem marginal_amplifyFinite [Fintype α] [Nonempty α] [LinearOrder α]
    (A : Algorithm X Ω α m) (a b : ℝ) (k N : ℕ) [NeZero N] (D : PMF X) :
    (amplifyFinite A a b k N).marginal D =
      (Probability.PMF.uniformOfFintype (Fin N)).bind fun i =>
        (Probability.PMF.iid (A.marginal D) k).map fun v => pickThresholded a b N k i v := by
  rw [Algorithm.marginal_eq_seed_bind]
  refine congrArg (PMF.bind (Probability.PMF.uniformOfFintype (Fin N))) (funext fun i => ?_)
  dsimp only [amplifyFinite]
  rw [← PMF.map_bind]
  exact congrArg (PMF.map _) (iid_splitBlocks_output_eq_iid A D k)

private theorem pairedOutput_amplifyFinite [Fintype α] [Nonempty α] [LinearOrder α]
    (A : Algorithm X Ω α m) (a b : ℝ) (k N : ℕ) [NeZero N] (D : PMF X) :
    (amplifyFinite A a b k N).pairedOutput D =
      (Probability.PMF.uniformOfFintype (Fin N)).bind fun i =>
        (Probability.PMF.iid (A.marginal D) k).bind fun v₁ =>
          (Probability.PMF.iid (A.marginal D) k).map fun v₂ =>
            (pickThresholded a b N k i v₁, pickThresholded a b N k i v₂) := by
  simp only [Algorithm.pairedOutput, amplifyFinite]
  refine congrArg (PMF.bind (Probability.PMF.uniformOfFintype (Fin N))) (funext fun i => ?_)
  have hinner := iid_splitBlocks_output_eq_iid A D k
  have hmap :
      ((Probability.PMF.iid D (k * m)).bind fun S =>
        (pmfPiFin fun j =>
          A.output (BitString.block (m := k) (k := m) S j)).map (pickThresholded a b N k i)) =
      (Probability.PMF.iid (A.marginal D) k).map (pickThresholded a b N k i) := by
    rw [← PMF.map_bind, hinner]
  calc ((Probability.PMF.iid D (k * m)).bind fun S₁ =>
          (Probability.PMF.iid D (k * m)).bind fun S₂ =>
            ((pmfPiFin fun j => A.output (BitString.block (m := k) (k := m) S₁ j)).map
              (pickThresholded a b N k i)).bind fun y₁ =>
              ((pmfPiFin fun j => A.output (BitString.block (m := k) (k := m) S₂ j)).map
                (pickThresholded a b N k i)).map fun y₂ => (y₁, y₂))
      = (Probability.PMF.iid D (k * m)).bind fun S₁ =>
          ((pmfPiFin fun j => A.output (BitString.block (m := k) (k := m) S₁ j)).map
            (pickThresholded a b N k i)).bind fun y₁ =>
            ((Probability.PMF.iid D (k * m)).bind fun S₂ =>
              (pmfPiFin fun j => A.output (BitString.block (m := k) (k := m) S₂ j)).map
                (pickThresholded a b N k i)).map fun y₂ => (y₁, y₂) := by
        refine congrArg (PMF.bind (Probability.PMF.iid D (k * m))) (funext fun S₁ => ?_)
        rw [PMF.bind_comm]
        refine congrArg (PMF.bind _) (funext fun y₁ => ?_)
        exact (PMF.map_bind _ _ _).symm
    _ = ((Probability.PMF.iid D (k * m)).bind fun S₁ =>
          (pmfPiFin fun j => A.output (BitString.block (m := k) (k := m) S₁ j)).map
            (pickThresholded a b N k i)).bind fun y₁ =>
          ((Probability.PMF.iid (A.marginal D) k).map
            (pickThresholded a b N k i)).map fun y₂ => (y₁, y₂) := by
        rw [← PMF.bind_bind]
        simp_rw [hmap]
    _ = (Probability.PMF.iid (A.marginal D) k).bind fun v₁ =>
          (Probability.PMF.iid (A.marginal D) k).map fun v₂ =>
            (pickThresholded a b N k i v₁, pickThresholded a b N k i v₂) := by
        rw [hmap, PMF.bind_map]
        dsimp only [Function.comp_def]
        refine congrArg (PMF.bind (Probability.PMF.iid (A.marginal D) k)) (funext fun v₁ => ?_)
        rw [PMF.map_comp]
        rfl

private theorem empFreq_concentrates [Finite α] [DecidableEq α] (q : PMF α) (k : ℕ) [NeZero k]
    {δ : ℝ} (hδ : 0 ≤ δ) (y : α) :
    ((Probability.PMF.iid q k).toOuterMeasure
      {v : Fin k → α | δ < |empFreq k v y - (q y).toReal|}).toReal ≤
      2 * Real.exp (-2 * (k : ℝ) * δ ^ 2) := by
  let _ : Fintype α := Fintype.ofFinite α
  let f : α → ℝ := fun z => if z = y then 1 else 0
  have hf : ∀ z ∈ q.support, f z ∈ Set.Icc (0 : ℝ) 1 := fun z _ => by
    dsimp only [f]
    split_ifs <;> simp
  have hconc := boundedMean_concentrates q f hf k hδ
  have hfreq : ∀ v : Fin k → α, empFreq k v y = empiricalMean f v := fun v => by
    simp only [empFreq, empiricalMean, Finset.card_filter, Nat.cast_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only [f]
    split_ifs <;> simp
  have hexp : (q y).toReal = distExpectation q f := by
    simp [distExpectation, f]
  have heq :
      {v : Fin k → α | δ < |empFreq k v y - (q y).toReal|} =
        {v : Fin k → α | δ < |empiricalMean f v - distExpectation q f|} := by
    ext v
    simp only [Set.mem_ofPred_eq, hfreq, hexp]
  rw [heq]
  refine hconc.trans_eq ?_
  have hmax : max ((1 : ℝ) - 0) 1 = 1 := by norm_num
  rw [hmax, one_pow, div_one]

private theorem empFreq_all_concentrates [Fintype α] [DecidableEq α] (q : PMF α) (k : ℕ)
    [NeZero k] {δ : ℝ} (hδ : 0 ≤ δ) :
    ((Probability.PMF.iid q k).toOuterMeasure
      {v : Fin k → α | ∃ y : α, δ < |empFreq k v y - (q y).toReal|}).toReal ≤
      (Fintype.card α : ℝ) * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2)) := by
  have hunion :
      {v : Fin k → α | ∃ y : α, δ < |empFreq k v y - (q y).toReal|} =
      ⋃ y ∈ (Finset.univ : Finset α), {v : Fin k → α | δ < |empFreq k v y - (q y).toReal|} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_univ, exists_true_left]
  rw [hunion]
  have hreal := Probability.PMF.toOuterMeasure_toReal_biUnion_finset_le
    (Probability.PMF.iid q k) Finset.univ
    (fun y => {v : Fin k → α | δ < |empFreq k v y - (q y).toReal|})
  refine hreal.trans ?_
  calc ∑ y : α, ((Probability.PMF.iid q k).toOuterMeasure
          {v : Fin k → α | δ < |empFreq k v y - (q y).toReal|}).toReal
      ≤ ∑ _y : α, (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2)) :=
        Finset.sum_le_sum fun y _ => empFreq_concentrates q k hδ y
    _ = (Fintype.card α : ℝ) * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2)) := by
        simp [Finset.sum_const, nsmul_eq_mul]

/-- **Strong replicability of `amplifyFinite`**: for any `a < b`, `k, N ≥ 1`, and `δ ≥ 0`,
`amplifyFinite A a b k N` is strongly `ρ`-replicable over **all** distributions `D : PMF X` with
`ρ = 2 * |α| * (2 * exp(-2 * k * δ^2)) + |α| * (2 * δ / (b - a) + 1 / N)`. -/
theorem isReplicable_amplifyFinite [Fintype α] [Nonempty α] [LinearOrder α]
    (A : Algorithm X Ω α m) {a b δ : ℝ} (hab : a < b) (hδ : 0 ≤ δ) (k N : ℕ)
    [NeZero k] [NeZero N] :
    IsReplicable (amplifyFinite A a b k N)
      (2 * ((Fintype.card α : ℝ) * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2))) +
        (Fintype.card α : ℝ) * (2 * δ / (b - a) + 1 / N)) := by
  intro D _
  have hcomm :
      (amplifyFinite A a b k N).pairedOutput D =
        (Probability.PMF.iid (A.marginal D) k).bind fun v₁ =>
          (Probability.PMF.iid (A.marginal D) k).bind fun v₂ =>
            (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
              (pickThresholded a b N k i v₁, pickThresholded a b N k i v₂) := by
    rw [pairedOutput_amplifyFinite, PMF.bind_comm]
    refine congrArg (PMF.bind (Probability.PMF.iid (A.marginal D) k)) (funext fun v₁ => ?_)
    exact PMF.bind_comm _ _ _
  rw [Algorithm.disagreeProb, hcomm]
  let err : ℝ := (Fintype.card α : ℝ) * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2))
  let seedErr : ℝ := (Fintype.card α : ℝ) * (2 * δ / (b - a) + 1 / N)
  let good : Set (Fin k → α) := {v | ∀ y : α, |empFreq k v y - (A.marginal D y).toReal| ≤ δ}
  have herr_nn : 0 ≤ err := by positivity
  have hseed_nn : 0 ≤ seedErr := by
    have hba : 0 < b - a := sub_pos.mpr hab
    positivity
  have hgoodc : ((Probability.PMF.iid (A.marginal D) k).toOuterMeasure goodᶜ).toReal ≤ err := by
    have heq : goodᶜ =
        {v : Fin k → α | ∃ y : α, δ < |empFreq k v y - (A.marginal D y).toReal|} := by
      ext v
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le, good]
    rw [heq]
    exact empFreq_all_concentrates (A.marginal D) k hδ
  have hinner :
      ∀ v₁ ∈ good,
        (((Probability.PMF.iid (A.marginal D) k).bind fun v₂ =>
          (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
            (pickThresholded a b N k i v₁, pickThresholded a b N k i v₂)).toOuterMeasure
          {p : α × α | p.1 ≠ p.2}).toReal ≤ err + seedErr := by
    intro v₁ hv₁
    refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ good _ hseed_nn ?_).trans
      (add_le_add hgoodc le_rfl)
    intro v₂ _ hv₂
    rw [PMF.toOuterMeasure_map_apply]
    have hpre :
        (fun i : Fin N => (pickThresholded a b N k i v₁, pickThresholded a b N k i v₂)) ⁻¹'
          {p : α × α | p.1 ≠ p.2} ⊆
        ⋃ y ∈ (Finset.univ : Finset α),
          {i : Fin N | thresholdRound a b N i (empFreq k v₁ y) ≠
            thresholdRound a b N i (empFreq k v₂ y)} := by
      intro i hi
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, ne_eq, Set.mem_iUnion, Finset.mem_univ,
        exists_true_left] at hi ⊢
      by_contra hnone
      push Not at hnone
      have hcand :
          (Finset.univ.filter fun y : α => thresholdRound a b N i (empFreq k v₁ y) = true) =
          (Finset.univ.filter fun y : α => thresholdRound a b N i (empFreq k v₂ y) = true) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnone y]
      have hsame : pickThresholded a b N k i v₁ = pickThresholded a b N k i v₂ := by
        dsimp only [pickThresholded]
        simp only [hcand]
      exact hi hsame
    have hmono := Probability.PMF.toOuterMeasure_toReal_mono
      (Probability.PMF.uniformOfFintype (Fin N)) hpre
    have hunionR := Probability.PMF.toOuterMeasure_toReal_biUnion_finset_le
      (Probability.PMF.uniformOfFintype (Fin N)) Finset.univ
      (fun y => {i : Fin N | thresholdRound a b N i (empFreq k v₁ y) ≠
        thresholdRound a b N i (empFreq k v₂ y)})
    refine (hmono.trans hunionR).trans ?_
    calc ∑ y : α, ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure
            {i : Fin N | thresholdRound a b N i (empFreq k v₁ y) ≠
              thresholdRound a b N i (empFreq k v₂ y)}).toReal
        ≤ ∑ y : α, (2 * δ / (b - a) + 1 / N) := by
          refine Finset.sum_le_sum fun y _ => ?_
          have hdist : |empFreq k v₁ y - empFreq k v₂ y| ≤ 2 * δ := by
            have h1 := hv₁ y
            have h2 := hv₂ y
            rw [abs_sub_comm] at h2
            calc |empFreq k v₁ y - empFreq k v₂ y|
                = |(empFreq k v₁ y - (A.marginal D y).toReal) +
                    ((A.marginal D y).toReal - empFreq k v₂ y)| := by ring_nf
              _ ≤ |empFreq k v₁ y - (A.marginal D y).toReal| +
                    |(A.marginal D y).toReal - empFreq k v₂ y| := abs_add_le _ _
              _ ≤ δ + δ := add_le_add h1 h2
              _ = 2 * δ := by ring
          refine (thresholdRound_disagree_le hab (empFreq k v₁ y) (empFreq k v₂ y)).trans ?_
          have hba : 0 < b - a := sub_pos.mpr hab
          gcongr
      _ = seedErr := by
          dsimp only [seedErr]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have houter := Probability.PMF.toOuterMeasure_bind_failure_toReal_le
    (Probability.PMF.iid (A.marginal D) k)
    (fun v₁ => (Probability.PMF.iid (A.marginal D) k).bind fun v₂ =>
      (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
        (pickThresholded a b N k i v₁, pickThresholded a b N k i v₂))
    good {p : α × α | p.1 ≠ p.2} (add_nonneg herr_nn hseed_nn)
    (fun v₁ _ hv₁ => hinner v₁ hv₁)
  calc (((Probability.PMF.iid (A.marginal D) k).bind fun v₁ =>
          (Probability.PMF.iid (A.marginal D) k).bind fun v₂ =>
            (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
              (pickThresholded a b N k i v₁, pickThresholded a b N k i v₂)).toOuterMeasure
        {p : α × α | p.1 ≠ p.2}).toReal
      ≤ ((Probability.PMF.iid (A.marginal D) k).toOuterMeasure goodᶜ).toReal +
          (err + seedErr) := houter
    _ ≤ err + (err + seedErr) := add_le_add hgoodc le_rfl
    _ = 2 * err + seedErr := by ring

/-- **Accuracy of `amplifyFinite`**: if `A` errs with probability at most `β₀ < 1 / (|α| + 1)`
on `𝒟` and the threshold window `[a, b)` satisfies `β₀ + δ < a ≤ b ≤ (1 - β₀) / |α| - δ`, then
`amplifyFinite A a b k N` errs on `𝒟` with probability at most
`|α| * (2 * exp (-2 * k * δ^2))`. -/
theorem isAccurateFor_amplifyFinite [Fintype α] [Nonempty α] [LinearOrder α]
    (A : Algorithm X Ω α m) {𝒟 : Set (PMF X)} {good : PMF X → Set α} {β₀ a b δ : ℝ}
    (hacc : IsAccurateFor A 𝒟 good β₀) (hab : a ≤ b) (hδ : 0 ≤ δ)
    (ha : β₀ + δ < a) (hb : b ≤ (1 - β₀) / Fintype.card α - δ)
    (k N : ℕ) [NeZero k] [NeZero N] :
    IsAccurateFor (amplifyFinite A a b k N) 𝒟 good
      ((Fintype.card α : ℝ) * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2))) := by
  classical
  intro D hD
  let M : ℝ := Fintype.card α
  have hM : 0 < M := Nat.cast_pos.mpr Fintype.card_pos
  have hgood_prob : 1 - β₀ ≤ ((A.marginal D).toOuterMeasure (good D)).toReal :=
    (isAccurateFor_iff_prob_good.mp hacc) D hD
  have hsum_good : ((A.marginal D).toOuterMeasure (good D)).toReal =
      ∑ y : α, if y ∈ good D then (A.marginal D y).toReal else 0 :=
    Probability.PMF.toOuterMeasure_apply_toReal (A.marginal D) (good D)
  have hβ₀_lt_div : β₀ < (1 - β₀) / M := by linarith
  have hβ₀_nn : 0 ≤ β₀ := ENNReal.toReal_nonneg.trans (hacc D hD)
  have hdiv_pos : 0 < (1 - β₀) / M := by linarith
  have hex_heavy : ∃ y₀ ∈ good D, (1 - β₀) / M ≤ (A.marginal D y₀).toReal := by
    by_contra hnone
    push Not at hnone
    have hsum_lt : (∑ y : α, if y ∈ good D then (A.marginal D y).toReal else 0) <
        ∑ _y : α, (1 - β₀) / M := by
      refine Finset.sum_lt_sum ?_ ⟨Classical.arbitrary α, Finset.mem_univ _, ?_⟩
      · intro y _
        split_ifs with hy
        · exact (hnone y hy).le
        · exact hdiv_pos.le
      · split_ifs with hy
        · exact hnone (Classical.arbitrary α) hy
        · exact hdiv_pos
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hM.ne'] at hsum_lt
    linarith
  obtain ⟨y₀, hy₀, hy₀_mass⟩ := hex_heavy
  have hbad_mass : ∀ y ∉ good D, (A.marginal D y).toReal ≤ β₀ := fun y hy => by
    calc (A.marginal D y).toReal
        = ((A.marginal D).toOuterMeasure {y}).toReal := by rw [PMF.toOuterMeasure_apply_singleton]
      _ ≤ ((A.marginal D).toOuterMeasure (good D)ᶜ).toReal :=
          Probability.PMF.toOuterMeasure_toReal_mono _ (Set.singleton_subset_iff.mpr hy)
      _ ≤ β₀ := hacc D hD
  rw [marginal_amplifyFinite]
  have herr_nn : 0 ≤ (Fintype.card α : ℝ) * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2)) := by
    positivity
  refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ Set.univ _ herr_nn
    fun i _ _ => ?_).trans_eq (by simp)
  rw [PMF.toOuterMeasure_map_apply]
  have hsub :
      (fun v => pickThresholded a b N k i v) ⁻¹' (good D)ᶜ ⊆
      {v : Fin k → α | ∃ y : α, δ < |empFreq k v y - (A.marginal D y).toReal|} := by
    intro v hv
    by_contra hconc
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_lt]
      at hv hconc
    have hbad_freq : ∀ y ∉ good D,
        thresholdRound a b N i (empFreq k v y) = false := fun y hy => by
      have h1 : empFreq k v y ≤ (A.marginal D y).toReal + δ := by
        linarith [(abs_sub_le_iff.mp (hconc y)).1]
      have hlt : empFreq k v y < a := by linarith [hbad_mass y hy]
      exact thresholdRound_false_of_lt_left hab i hlt
    have hy₀_pass : thresholdRound a b N i (empFreq k v y₀) = true := by
      have h2 : (A.marginal D y₀).toReal - δ ≤ empFreq k v y₀ := by
        linarith [(abs_sub_le_iff.mp (hconc y₀)).2]
      exact thresholdRound_true_of_right_le hab i (by linarith)
    let cand := Finset.univ.filter fun y : α => thresholdRound a b N i (empFreq k v y) = true
    have hcand : cand.Nonempty := ⟨y₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy₀_pass⟩⟩
    have hpick : pickThresholded a b N k i v = cand.min' hcand := by
      dsimp only [pickThresholded]
      split_ifs with h'
      · rfl
      · exact absurd hcand h'
    have hmem : pickThresholded a b N k i v ∈ cand := hpick ▸ Finset.min'_mem cand hcand
    rw [Finset.mem_filter] at hmem
    have hmem_good : pickThresholded a b N k i v ∈ good D := by
      by_contra hnot
      exact absurd hmem.2 (by rw [hbad_freq _ hnot]; decide)
    exact hv hmem_good
  exact (Probability.PMF.toOuterMeasure_toReal_mono _ hsub).trans
    (empFreq_all_concentrates (A.marginal D) k hδ)

/-- **Finite-domain amplification theorem** [ImpagliazzoLeiPitassiSorrell2022]: for any finite
nonempty linearly ordered output type `α`, if `A` achieves error `β₀ < 1 / (|α| + 1)` on `𝒟`
(with no replicability assumption at all on `A`), then for any target `ρ > 0` and `β > 0`, there
exist thresholds `a, b : ℝ` and `k, N ≥ 1` such that `amplifyFinite A a b k N` is **strongly
`ρ`-replicable** and `(good, β)`-accurate on `𝒟`. -/
theorem exists_amplifyFinite [Fintype α] [Nonempty α] [LinearOrder α]
    (A : Algorithm X Ω α m) {𝒟 : Set (PMF X)} {good : PMF X → Set α} {β₀ ρ β : ℝ}
    (hacc : IsAccurateFor A 𝒟 good β₀) (_hβ₀_nonneg : 0 ≤ β₀)
    (hβ₀ : β₀ < 1 / ((Fintype.card α : ℝ) + 1)) (hρ : 0 < ρ) (hβ : 0 < β) :
    ∃ (a b : ℝ) (k N : ℕ) (_ : NeZero k) (_ : NeZero N),
      IsReplicable (amplifyFinite A a b k N) ρ ∧
      IsAccurateFor (amplifyFinite A a b k N) 𝒟 good β := by
  let M : ℝ := Fintype.card α
  have hM : 0 < M := Nat.cast_pos.mpr Fintype.card_pos
  have hgap : 0 < (1 - β₀) / M - β₀ := by
    have hmul : β₀ * (M + 1) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at hβ₀
    rw [sub_pos, lt_div_iff₀ hM]
    linarith
  let Δ : ℝ := ((1 - β₀) / M - β₀) / 4
  have hΔ : 0 < Δ := by positivity
  let a : ℝ := β₀ + Δ
  let b : ℝ := (1 - β₀) / M - Δ
  have hab : a < b := by dsimp only [a, b, Δ]; linarith
  have hba : 0 < b - a := sub_pos.mpr hab
  let δ : ℝ := min (Δ / 2) ((ρ / (4 * M)) * (b - a))
  have hδ : 0 < δ := by
    apply lt_min (by positivity)
    exact mul_pos (div_pos hρ (by positivity)) hba
  have ha_bound : β₀ + δ < a := by
    have : δ ≤ Δ / 2 := min_le_left _ _
    dsimp only [a]
    linarith
  have hb_bound : b ≤ (1 - β₀) / M - δ := by
    have : δ ≤ Δ / 2 := min_le_left _ _
    dsimp only [b]
    linarith
  obtain ⟨N, hN_gt⟩ := exists_nat_gt (4 * M / ρ)
  have hNpos : 0 < N := by
    have : 0 < 4 * M / ρ := by positivity
    exact_mod_cast this.trans hN_gt
  have hN_inst : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  have hN_bound : M / N ≤ ρ / 4 := by
    have hN' : 4 * M / ρ < (N : ℝ) := hN_gt
    have hmul : 4 * M < (N : ℝ) * ρ := (div_lt_iff₀ hρ).mp hN'
    have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
    rw [div_le_div_iff₀ hNR (by norm_num : (0 : ℝ) < 4)]
    linarith
  let eps : ℝ := min (ρ / 8) β
  have heps : 0 < eps := lt_min (by positivity) hβ
  obtain ⟨k, hkpos, hk_bound⟩ := exp_decay_exists M hδ heps
  have hk_inst : NeZero k := ⟨Nat.ne_of_gt hkpos⟩
  refine ⟨a, b, k, N, hk_inst, hN_inst, ?_, ?_⟩
  · refine (isReplicable_amplifyFinite A hab hδ.le k N).mono ?_
    have h1 : M * (2 * Real.exp (-2 * (k : ℝ) * δ ^ 2)) ≤ ρ / 8 :=
      hk_bound.trans (min_le_left _ _)
    have h2 : M * (2 * δ / (b - a)) ≤ ρ / 2 := by
      have hle : δ ≤ (ρ / (4 * M)) * (b - a) := min_le_right _ _
      calc M * (2 * δ / (b - a))
          ≤ M * (2 * ((ρ / (4 * M)) * (b - a)) / (b - a)) := by gcongr
        _ = ρ / 2 := by field_simp [hM.ne', hba.ne']; ring
    have h3 : M * (2 * δ / (b - a) + 1 / N) = M * (2 * δ / (b - a)) + M / N := by ring
    dsimp only [M] at h1 h2 h3 hN_bound
    linarith
  · exact (isAccurateFor_amplifyFinite A hacc hab.le hδ.le ha_bound hb_bound k N).mono
      (hk_bound.trans (min_le_right _ _))

end FiniteDomainAmplification

/-! ### General-domain replicability amplification (`DecidableEq α`, `ρ₀ < 1 / 2`) -/

section GeneralDomainAmplification

variable {X : Type u} {Ω : Type v} {α : Type w} {m : ℕ}

/-- Pick a candidate from `v : Fin k → α` appearing strictly more than `k / 2` times, or
`fallback` if no strict majority exists. -/
@[expose] def strictMajorityCandidate {k : ℕ} [DecidableEq α] (v : Fin k → α)
    (fallback : α) : α :=
  let cands := Finset.univ.filter fun j : Fin k =>
    k < 2 * (Finset.univ.filter fun j' => v j' = v j).card
  if h : cands.Nonempty then v (cands.min' h) else fallback

theorem strictMajorityCandidate_eq_of_lt_two_mul {k : ℕ} [DecidableEq α] (v : Fin k → α)
    (fallback y : α)
    (hy : k < 2 * (Finset.univ.filter fun j : Fin k => v j = y).card) :
    strictMajorityCandidate v fallback = y := by
  have hex : ∃ j : Fin k, v j = y := by
    have hcard : 0 < (Finset.univ.filter fun j : Fin k => v j = y).card := by omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
    exact ⟨j, (Finset.mem_filter.mp hj).2⟩
  obtain ⟨j₀, hj₀⟩ := hex
  let cands := Finset.univ.filter fun j : Fin k =>
    k < 2 * (Finset.univ.filter fun j' => v j' = v j).card
  have hj₀_mem : j₀ ∈ cands := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hj₀] using hy⟩
  have hne_cands : cands.Nonempty := ⟨j₀, hj₀_mem⟩
  have hpick : strictMajorityCandidate v fallback = v (cands.min' hne_cands) := by
    dsimp only [strictMajorityCandidate]
    split_ifs with h'
    · rfl
    · exact absurd hne_cands h'
  rw [hpick]
  let j := cands.min' hne_cands
  have hj_mem : j ∈ cands := Finset.min'_mem cands hne_cands
  have hj_cond : k < 2 * (Finset.univ.filter fun j' => v j' = v j).card :=
    (Finset.mem_filter.mp hj_mem).2
  by_contra hne
  have hdisj : Disjoint (Finset.univ.filter fun j' => v j' = v j)
      (Finset.univ.filter fun j' => v j' = y) := by
    rw [Finset.disjoint_filter]
    intro a _ h1 h2
    exact hne (h1.symm.trans h2)
  have hsum := Finset.card_union_of_disjoint hdisj
  have hle : (Finset.univ.filter (fun j' => v j' = v j) ∪
      Finset.univ.filter fun j' => v j' = y).card ≤ Fintype.card (Fin k) :=
    Finset.card_le_univ _
  rw [Fintype.card_fin] at hle
  omega

/-- Output distribution of `A` on `D` conditioned on a fixed seed `r`. -/
@[expose] noncomputable def seedOutput (A : Algorithm X Ω α m) (D : PMF X) (r : Ω) : PMF α :=
  (Probability.PMF.iid D m).bind fun S => A.run S r

/-- Collision probability of `A` on `D` at shared seed `r`:
`Probability.PMF.collisionProbability (seedOutput A D r)`. -/
noncomputable abbrev seedColl (A : Algorithm X Ω α m) (D : PMF X) (r : Ω) : ℝ :=
  Probability.PMF.collisionProbability (seedOutput A D r)

private theorem seedColl_nonneg (A : Algorithm X Ω α m) (D : PMF X) (r : Ω) :
    0 ≤ seedColl A D r :=
  Probability.PMF.collisionProbability_nonneg (seedOutput A D r)

private theorem seedColl_le_one (A : Algorithm X Ω α m) (D : PMF X) (r : Ω) :
    seedColl A D r ≤ 1 :=
  Probability.PMF.collisionProbability_le_one (seedOutput A D r)

private theorem seedColl_eq_collBool_true [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X)
    (r : Ω) :
    (((seedOutput A D r).bind fun y₁ =>
      (seedOutput A D r).map fun y₂ => decide (y₁ = y₂)) true).toReal =
      seedColl A D r :=
  (Probability.PMF.collisionProbability_eq_probability (seedOutput A D r)).symm

private theorem agreeProb_eq_tsum_seedColl (A : Algorithm X Ω α m) (D : PMF X) :
    A.agreeProb D = ∑' r : Ω, (A.seed r).toReal * seedColl A D r := by
  classical
  have hcomm (r : Ω) :
      ((Probability.PMF.iid D m).bind fun S₁ =>
        (Probability.PMF.iid D m).bind fun S₂ =>
          (A.run S₁ r).bind fun y₁ => (A.run S₂ r).map fun y₂ => (y₁, y₂)) =
      (seedOutput A D r).bind fun y₁ => (seedOutput A D r).map fun y₂ => (y₁, y₂) := by
    simp only [seedOutput, PMF.bind_bind]
    refine congrArg (PMF.bind (Probability.PMF.iid D m)) (funext fun S₁ => ?_)
    rw [PMF.bind_comm]
    refine congrArg (PMF.bind (A.run S₁ r)) (funext fun y₁ => ?_)
    exact (PMF.map_bind _ _ _).symm
  have hpair :
      A.pairedOutput D =
        A.seed.bind fun r =>
          (seedOutput A D r).bind fun y₁ => (seedOutput A D r).map fun y₂ => (y₁, y₂) := by
    simp only [Algorithm.pairedOutput]
    exact congrArg (PMF.bind A.seed) (funext hcomm)
  have hinner (r : Ω) :
      (((seedOutput A D r).bind fun y₁ =>
        (seedOutput A D r).map fun y₂ => (y₁, y₂)).toOuterMeasure
        {p : α × α | p.1 = p.2}).toReal = seedColl A D r := by
    rw [PMF.toOuterMeasure_bind_apply, ENNReal.tsum_toReal_eq]
    · refine tsum_congr fun y₁ => ?_
      rw [ENNReal.toReal_mul, PMF.toOuterMeasure_map_apply]
      have hset : (fun y₂ : α => (y₁, y₂)) ⁻¹' {p : α × α | p.1 = p.2} = {y₁} := by
        ext y₂
        simp [eq_comm]
      rw [hset, PMF.toOuterMeasure_apply_singleton, sq]
    · intro y₁
      exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (Probability.PMF.toOuterMeasure_ne_top _ _)
  rw [Algorithm.agreeProb, hpair, PMF.toOuterMeasure_bind_apply, ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun r => ?_
    rw [ENNReal.toReal_mul, hinner r]
  · intro r
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (Probability.PMF.toOuterMeasure_ne_top _ _)

private theorem pmf_markov_ge_toReal_le {Ω : Type*} (p : PMF Ω) (f : Ω → ℝ) {c μ : ℝ}
    (hc : 0 < c) (hf_nn : ∀ r, 0 ≤ f r) (hf_le : ∀ r, f r ≤ 1)
    (hsum : ∑' r, (p r).toReal * f r ≤ μ) :
    (p.toOuterMeasure {r | c ≤ f r}).toReal ≤ μ / c := by
  have hmarkov := Probability.PMF.mul_toOuterMeasure_le_tsum p
    (fun r => ENNReal.ofReal (f r)) (ENNReal.ofReal c)
  have hset : {r | ENNReal.ofReal c ≤ ENNReal.ofReal (f r)} = {r | c ≤ f r} := by
    ext r
    simp only [Set.mem_ofPred_eq, ENNReal.ofReal_le_ofReal_iff (hf_nn r)]
  rw [hset] at hmarkov
  have htsum_top : (∑' r, p r * ENNReal.ofReal (f r)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∑' r, p r * ENNReal.ofReal (f r)
        ≤ ∑' r, p r :=
          tsum_le_tsum fun r => mul_le_of_le_one_right' (ENNReal.ofReal_le_one.mpr (hf_le r))
      _ = 1 := p.tsum_coe
  have hreal := ENNReal.toReal_mono htsum_top hmarkov
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, ENNReal.tsum_toReal_eq] at hreal
  · have hconv : ∑' r, (p r * ENNReal.ofReal (f r)).toReal = ∑' r, (p r).toReal * f r := by
      refine tsum_congr fun r => ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf_nn r)]
    rw [hconv] at hreal
    exact (le_div_iff₀ hc).mpr (mul_comm c _ ▸ hreal.trans hsum)
  · intro r
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top

private theorem seed_markov_coll_lt (A : Algorithm X Ω α m) (D : PMF X) {c : ℝ} (hc : c < 1) :
    (A.seed.toOuterMeasure {r : Ω | seedColl A D r < c}).toReal ≤
      A.disagreeProb D / (1 - c) := by
  have h1c : 0 < 1 - c := sub_pos.mpr hc
  have hsum_agree : Summable fun r : Ω => (A.seed r).toReal * seedColl A D r :=
    (Probability.PMF.summable_toReal A.seed).of_nonneg_of_le
      (fun r => mul_nonneg ENNReal.toReal_nonneg (seedColl_nonneg A D r))
      (fun r => mul_le_of_le_one_right ENNReal.toReal_nonneg (seedColl_le_one A D r))
  have hdisagree :
      ∑' r : Ω, (A.seed r).toReal * (1 - seedColl A D r) ≤ A.disagreeProb D := by
    rw [Algorithm.disagreeProb_eq_one_sub_agreeProb, agreeProb_eq_tsum_seedColl]
    have hrewrite :
        ∑' r : Ω, (A.seed r).toReal * (1 - seedColl A D r) =
          ∑' r : Ω, ((A.seed r).toReal - (A.seed r).toReal * seedColl A D r) :=
      tsum_congr fun r => by ring
    rw [hrewrite, (Probability.PMF.summable_toReal A.seed).tsum_sub hsum_agree,
      Probability.PMF.tsum_toReal A.seed]
  have hsub : {r : Ω | seedColl A D r < c} ⊆ {r : Ω | 1 - c ≤ 1 - seedColl A D r} :=
    fun r hr => by simp only [Set.mem_ofPred_eq] at hr ⊢; linarith
  refine (Probability.PMF.toOuterMeasure_toReal_mono _ hsub).trans ?_
  exact pmf_markov_ge_toReal_le A.seed (fun r => 1 - seedColl A D r) h1c
    (fun r => sub_nonneg.mpr (seedColl_le_one A D r))
    (fun r => sub_le_self 1 (seedColl_nonneg A D r)) hdisagree

private theorem pmfPiFin_forall_lt_le {Ω : Type*} (p : PMF Ω) (P : Ω → Prop) :
    ∀ T : ℕ,
      (pmfPiFin fun _ : Fin T => p).toOuterMeasure {rs : Fin T → Ω | ∀ t, P (rs t)} ≤
        p.toOuterMeasure {r : Ω | P r} ^ T
  | 0 => by simp
  | T + 1 => by
    rw [pmfPiFin, pow_succ']
    refine Probability.PMF.toOuterMeasure_bind_le_mul_ennreal p _ {r | P r} _ le_rfl ?_ ?_
    · intro r₀ _ hr₀
      rw [PMF.toOuterMeasure_map_apply]
      have hsub :
          (Fin.cons r₀ ⁻¹' {rs : Fin (T + 1) → Ω | ∀ t, P (rs t)}) ⊆
          {rs' : Fin T → Ω | ∀ t, P (rs' t)} := by
        intro rs' hrs' t
        exact hrs' t.succ
      exact ((pmfPiFin _).toOuterMeasure.mono hsub).trans (pmfPiFin_forall_lt_le p P T)
    · intro r₀ _ hr₀
      rw [PMF.toOuterMeasure_map_apply]
      have hempty : Fin.cons r₀ ⁻¹' {rs : Fin (T + 1) → Ω | ∀ t, P (rs t)} = ∅ := by
        ext rs'
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hr₀ (h 0)
      rw [hempty]
      simp

/-- Single candidate-seed trial inside `amplifyReplicability`: using `k₁` independent sample
pairs to estimate the seed's collision probability and `k₂` independent samples to find its
strict-majority output. -/
@[expose] noncomputable def trialRun [DecidableEq α] (A : Algorithm X Ω α m) (k₁ k₂ : ℕ)
    [NeZero k₂] (S : Fin (k₁ * (m + m) + k₂ * m) → X) (r : Ω) : PMF (ℝ × α) :=
  let sp := splitSample (k₁ * (m + m)) (k₂ * m) S
  let csLaw : PMF (Fin k₁ → Bool) := pmfPiFin fun l : Fin k₁ =>
    let pair := splitSample m m (BitString.block (m := k₁) (k := m + m) sp.1 l)
    (A.run pair.1 r).bind fun y₁ => (A.run pair.2 r).map fun y₂ => decide (y₁ = y₂)
  let zsLaw : PMF (Fin k₂ → α) := pmfPiFin fun j : Fin k₂ =>
    A.run (BitString.block (m := k₂) (k := m) sp.2 j) r
  csLaw.bind fun cs =>
    zsLaw.map fun zs =>
      (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
        strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩))

private noncomputable def trialRunMarginal [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X)
    (r : Ω) (k₁ k₂ : ℕ) [NeZero k₂] : PMF (ℝ × α) :=
  let μ := seedOutput A D r
  let collBool : PMF Bool := μ.bind fun y₁ => μ.map fun y₂ => decide (y₁ = y₂)
  (Probability.PMF.iid collBool k₁).bind fun cs =>
    (Probability.PMF.iid μ k₂).map fun zs =>
      (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
        strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩))

private theorem iid_bind_trialRun [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X) (r : Ω)
    (k₁ k₂ : ℕ) [NeZero k₂] :
    ((Probability.PMF.iid D (k₁ * (m + m) + k₂ * m)).bind fun S => trialRun A k₁ k₂ S r) =
      trialRunMarginal A D r k₁ k₂ := by
  have hsplit :
      (Probability.PMF.iid D (k₁ * (m + m) + k₂ * m)).bind (fun S => trialRun A k₁ k₂ S r) =
        (Probability.PMF.iid D (k₁ * (m + m))).bind fun S₁ =>
          (Probability.PMF.iid D (k₂ * m)).bind fun S₂ =>
            (pmfPiFin fun l : Fin k₁ =>
              let pair := splitSample m m (BitString.block (m := k₁) (k := m + m) S₁ l)
              (A.run pair.1 r).bind fun y₁ =>
                (A.run pair.2 r).map fun y₂ => decide (y₁ = y₂)).bind fun cs =>
              (pmfPiFin fun j : Fin k₂ =>
                  A.run (BitString.block (m := k₂) (k := m) S₂ j) r).map fun zs =>
                (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
                  strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩)) := by
    dsimp only [trialRun] at *
    have hm := (PMF.bind_map (Probability.PMF.iid D (k₁ * (m + m) + k₂ * m))
      (splitSample (k₁ * (m + m)) (k₂ * m))
      (fun p =>
        (pmfPiFin fun l : Fin k₁ =>
          let pair := splitSample m m (BitString.block (m := k₁) (k := m + m) p.1 l)
          (A.run pair.1 r).bind fun y₁ =>
            (A.run pair.2 r).map fun y₂ => decide (y₁ = y₂)).bind fun cs =>
          (pmfPiFin fun j : Fin k₂ =>
              A.run (BitString.block (m := k₂) (k := m) p.2 j) r).map fun zs =>
            (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
              strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩)))).symm
    dsimp only [Function.comp_def] at hm
    rw [hm, iid_map_splitSample, PMF.bind_bind]
    refine congrArg (PMF.bind (Probability.PMF.iid D (k₁ * (m + m)))) (funext fun S₁ => ?_)
    rw [PMF.bind_map]
    rfl
  rw [hsplit]
  have hpair_eq :
      ((Probability.PMF.iid D (m + m)).bind fun b =>
        (A.run (splitSample m m b).1 r).bind fun y₁ =>
          (A.run (splitSample m m b).2 r).map fun y₂ => decide (y₁ = y₂)) =
      (seedOutput A D r).bind fun y₁ => (seedOutput A D r).map fun y₂ => decide (y₁ = y₂) := by
    have hm := (PMF.bind_map (Probability.PMF.iid D (m + m)) (splitSample m m)
      (fun sp => (A.run sp.1 r).bind fun y₁ => (A.run sp.2 r).map fun y₂ =>
        decide (y₁ = y₂))).symm
    dsimp only [Function.comp_def] at hm
    rw [hm, iid_map_splitSample, PMF.bind_bind]
    simp only [seedOutput, PMF.bind_bind]
    refine congrArg (PMF.bind (Probability.PMF.iid D m)) (funext fun U₁ => ?_)
    rw [PMF.bind_map]
    dsimp only [Function.comp_def]
    rw [PMF.bind_comm]
    refine congrArg (PMF.bind (A.run U₁ r)) (funext fun y₁ => ?_)
    exact (PMF.map_bind _ _ _).symm
  have hS₁ :
      ((Probability.PMF.iid D (k₁ * (m + m))).bind fun S₁ =>
        pmfPiFin fun l : Fin k₁ =>
          let pair := splitSample m m (BitString.block (m := k₁) (k := m + m) S₁ l)
          (A.run pair.1 r).bind fun y₁ => (A.run pair.2 r).map fun y₂ => decide (y₁ = y₂)) =
      Probability.PMF.iid
        ((seedOutput A D r).bind fun y₁ => (seedOutput A D r).map fun y₂ => decide (y₁ = y₂))
        k₁ := by
    have hm := (PMF.bind_map (Probability.PMF.iid D (k₁ * (m + m)))
      (BitString.block (α := X) (m := k₁) (k := m + m))
      (fun B => pmfPiFin fun l : Fin k₁ =>
        let pair := splitSample m m (B l)
        (A.run pair.1 r).bind fun y₁ => (A.run pair.2 r).map fun y₂ => decide (y₁ = y₂))).symm
    dsimp only [Function.comp_def] at hm
    rw [hm, iid_map_block, ← pmfPiFin_const,
      pmfPiFin_bind (fun _ : Fin k₁ => Probability.PMF.iid D (m + m))
        (fun _ b => (A.run (splitSample m m b).1 r).bind fun y₁ =>
          (A.run (splitSample m m b).2 r).map fun y₂ => decide (y₁ = y₂))]
    simp_rw [hpair_eq]
    exact pmfPiFin_const _ k₁
  have hS₂ :
      ((Probability.PMF.iid D (k₂ * m)).bind fun S₂ =>
        pmfPiFin fun j : Fin k₂ => A.run (BitString.block (m := k₂) (k := m) S₂ j) r) =
      Probability.PMF.iid (seedOutput A D r) k₂ := by
    have hm := (PMF.bind_map (Probability.PMF.iid D (k₂ * m))
      (BitString.block (α := X) (m := k₂) (k := m))
      (fun B => pmfPiFin fun j : Fin k₂ => A.run (B j) r)).symm
    dsimp only [Function.comp_def] at hm
    rw [hm, iid_map_block, ← pmfPiFin_const,
      pmfPiFin_bind (fun _ : Fin k₂ => Probability.PMF.iid D m) (fun _ b => A.run b r)]
    exact pmfPiFin_const (seedOutput A D r) k₂
  have hcomm :
      ((Probability.PMF.iid D (k₁ * (m + m))).bind fun S₁ =>
        (Probability.PMF.iid D (k₂ * m)).bind fun S₂ =>
          (pmfPiFin fun l : Fin k₁ =>
            let pair := splitSample m m (BitString.block (m := k₁) (k := m + m) S₁ l)
            (A.run pair.1 r).bind fun y₁ =>
              (A.run pair.2 r).map fun y₂ => decide (y₁ = y₂)).bind fun cs =>
            (pmfPiFin fun j : Fin k₂ =>
                A.run (BitString.block (m := k₂) (k := m) S₂ j) r).map fun zs =>
              (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
                strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩))) =
      ((Probability.PMF.iid D (k₁ * (m + m))).bind fun S₁ =>
        pmfPiFin fun l : Fin k₁ =>
          let pair := splitSample m m (BitString.block (m := k₁) (k := m + m) S₁ l)
          (A.run pair.1 r).bind fun y₁ => (A.run pair.2 r).map fun y₂ => decide (y₁ = y₂)).bind
        fun cs =>
          ((Probability.PMF.iid D (k₂ * m)).bind fun S₂ =>
            pmfPiFin fun j : Fin k₂ =>
              A.run (BitString.block (m := k₂) (k := m) S₂ j) r).map fun zs =>
              (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
                strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩)) := by
    simp only [PMF.bind_bind]
    refine congrArg (PMF.bind (Probability.PMF.iid D (k₁ * (m + m)))) (funext fun S₁ => ?_)
    rw [PMF.bind_comm]
    refine congrArg (PMF.bind (pmfPiFin _)) (funext fun cs => ?_)
    exact (PMF.map_bind _ _ _).symm
  rw [hcomm, hS₁, hS₂]
  rfl

/-- Pick the first trial `t` whose empirical collision estimate passes `thresholdRound a b N i`,
falling back to trial `0` when none qualifies. -/
@[expose] noncomputable def pickFirstThresholded {T : ℕ} [NeZero T] (a b : ℝ) (N : ℕ)
    (i : Fin N) (trials : Fin T → ℝ × α) : α :=
  let cands := Finset.univ.filter fun t : Fin T =>
    thresholdRound a b N i (trials t).1 = true
  if h : cands.Nonempty then (trials (cands.min' h)).2 else (trials ⟨0, NeZero.pos T⟩).2

/-- General-domain replicability amplification [ImpagliazzoLeiPitassiSorrell2022]: draws `T`
independent shared seeds `r_t ~ A.seed` and one threshold `i ~ uniform (Fin N)`, runs
`trialRun` on each candidate seed over disjoint sample blocks, and outputs the strict-majority
candidate of the first seed passing `thresholdValue a b N i`. -/
@[expose] noncomputable def amplifyReplicability [DecidableEq α] (A : Algorithm X Ω α m)
    (a b : ℝ) (T k₁ k₂ N : ℕ) [NeZero T] [NeZero k₂] [NeZero N] :
    Algorithm X ((Fin T → Ω) × Fin N) α (T * (k₁ * (m + m) + k₂ * m)) where
  seed := (pmfPiFin fun _ : Fin T => A.seed).bind fun rs =>
    (Probability.PMF.uniformOfFintype (Fin N)).map fun i => (rs, i)
  run S seed :=
    (pmfPiFin fun t : Fin T =>
      trialRun A k₁ k₂ (BitString.block (m := T) (k := k₁ * (m + m) + k₂ * m) S t)
        (seed.1 t)).map
      fun trials => pickFirstThresholded a b N seed.2 trials

private theorem iid_bind_trialRun_block [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X)
    (T k₁ k₂ : ℕ) [NeZero k₂] (rs : Fin T → Ω) :
    ((Probability.PMF.iid D (T * (k₁ * (m + m) + k₂ * m))).bind fun S =>
      pmfPiFin fun t : Fin T =>
        trialRun A k₁ k₂ (BitString.block (m := T) (k := k₁ * (m + m) + k₂ * m) S t) (rs t)) =
      pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂ := by
  have hm := (PMF.bind_map (Probability.PMF.iid D (T * (k₁ * (m + m) + k₂ * m)))
    (BitString.block (α := X) (m := T) (k := k₁ * (m + m) + k₂ * m))
    fun B => pmfPiFin fun t : Fin T => trialRun A k₁ k₂ (B t) (rs t)).symm
  dsimp only [Function.comp_def] at hm
  rw [hm, iid_map_block, ← pmfPiFin_const,
    pmfPiFin_bind (fun _ : Fin T => Probability.PMF.iid D (k₁ * (m + m) + k₂ * m))
      (fun t b => trialRun A k₁ k₂ b (rs t))]
  exact congrArg pmfPiFin (funext fun t => iid_bind_trialRun A D (rs t) k₁ k₂)

private theorem marginal_amplifyReplicability [DecidableEq α] (A : Algorithm X Ω α m)
    (a b : ℝ) (T k₁ k₂ N : ℕ) [NeZero T] [NeZero k₂] [NeZero N] (D : PMF X) :
    (amplifyReplicability A a b T k₁ k₂ N).marginal D =
      (pmfPiFin fun _ : Fin T => A.seed).bind fun rs =>
        (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials =>
          (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
            pickFirstThresholded a b N i trials := by
  rw [Algorithm.marginal_eq_seed_bind]
  simp only [amplifyReplicability, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  refine congrArg (PMF.bind (pmfPiFin fun _ : Fin T => A.seed)) (funext fun rs => ?_)
  calc ((Probability.PMF.uniformOfFintype (Fin N)).bind fun i =>
          (Probability.PMF.iid D (T * (k₁ * (m + m) + k₂ * m))).bind fun S =>
            (pmfPiFin fun t : Fin T =>
              trialRun A k₁ k₂ (BitString.block (m := T) (k := k₁ * (m + m) + k₂ * m) S t)
                (rs t)).map fun trials => pickFirstThresholded a b N i trials)
      = (Probability.PMF.uniformOfFintype (Fin N)).bind fun i =>
          (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).map fun trials =>
            pickFirstThresholded a b N i trials := by
        refine congrArg (PMF.bind (Probability.PMF.uniformOfFintype (Fin N))) (funext fun i => ?_)
        rw [← PMF.map_bind, iid_bind_trialRun_block A D T k₁ k₂ rs]
    _ = (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials =>
          (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
            pickFirstThresholded a b N i trials := by
        change ((Probability.PMF.uniformOfFintype (Fin N)).bind fun i =>
            (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials =>
              PMF.pure (pickFirstThresholded a b N i trials)) = _
        rw [PMF.bind_comm]
        rfl

private theorem pairedOutput_amplifyReplicability [DecidableEq α] (A : Algorithm X Ω α m)
    (a b : ℝ) (T k₁ k₂ N : ℕ) [NeZero T] [NeZero k₂] [NeZero N] (D : PMF X) :
    (amplifyReplicability A a b T k₁ k₂ N).pairedOutput D =
      (pmfPiFin fun _ : Fin T => A.seed).bind fun rs =>
        (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₁ =>
          (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₂ =>
            (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
              (pickFirstThresholded a b N i trials₁, pickFirstThresholded a b N i trials₂) := by
  simp only [Algorithm.pairedOutput, amplifyReplicability, PMF.bind_bind, PMF.bind_map,
    Function.comp_def]
  refine congrArg (PMF.bind (pmfPiFin fun _ : Fin T => A.seed)) (funext fun rs => ?_)
  have hpull := iid_bind_trialRun_block A D T k₁ k₂ rs
  have hS (i : Fin N) :
      ((Probability.PMF.iid D (T * (k₁ * (m + m) + k₂ * m))).bind fun S₁ =>
        (Probability.PMF.iid D (T * (k₁ * (m + m) + k₂ * m))).bind fun S₂ =>
          (pmfPiFin fun t : Fin T =>
            trialRun A k₁ k₂ (BitString.block (m := T) (k := k₁ * (m + m) + k₂ * m) S₁ t)
              (rs t)).bind
              fun trials₁ =>
            (pmfPiFin fun t : Fin T =>
              trialRun A k₁ k₂ (BitString.block (m := T) (k := k₁ * (m + m) + k₂ * m) S₂ t)
                (rs t)).map
                fun trials₂ =>
                  (pickFirstThresholded a b N i trials₁,
                    pickFirstThresholded a b N i trials₂)) =
      (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₁ =>
        (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₂ =>
          PMF.pure
            (pickFirstThresholded a b N i trials₁, pickFirstThresholded a b N i trials₂) := by
    calc _ = (Probability.PMF.iid D (T * (k₁ * (m + m) + k₂ * m))).bind fun S₁ =>
              (pmfPiFin fun t : Fin T =>
                trialRun A k₁ k₂ (BitString.block (m := T) (k := k₁ * (m + m) + k₂ * m) S₁ t)
                  (rs t)).bind
                  fun trials₁ =>
                ((Probability.PMF.iid D (T * (k₁ * (m + m) + k₂ * m))).bind fun S₂ =>
                  pmfPiFin fun t : Fin T =>
                    trialRun A k₁ k₂ (BitString.block (m := T) (k := k₁ * (m + m) + k₂ * m) S₂ t)
                      (rs t)).map
                    fun trials₂ =>
                      (pickFirstThresholded a b N i trials₁,
                        pickFirstThresholded a b N i trials₂) := by
            refine congrArg (PMF.bind (Probability.PMF.iid D _)) (funext fun S₁ => ?_)
            rw [PMF.bind_comm]
            refine congrArg (PMF.bind (pmfPiFin _)) (funext fun trials₁ => ?_)
            exact (PMF.map_bind _ _ _).symm
      _ = ((Probability.PMF.iid D (T * (k₁ * (m + m) + k₂ * m))).bind fun S₁ =>
              pmfPiFin fun t : Fin T =>
                trialRun A k₁ k₂ (BitString.block (m := T) (k := k₁ * (m + m) + k₂ * m) S₁ t)
                  (rs t)).bind
              fun trials₁ =>
            (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).map
              fun trials₂ =>
                (pickFirstThresholded a b N i trials₁, pickFirstThresholded a b N i trials₂) := by
            rw [← PMF.bind_bind]
            simp_rw [hpull]
      _ = (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₁ =>
            (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₂ =>
              PMF.pure
                (pickFirstThresholded a b N i trials₁, pickFirstThresholded a b N i trials₂) := by
            rw [hpull]
            rfl
  calc ((Probability.PMF.uniformOfFintype (Fin N)).bind fun i =>
          (Probability.PMF.iid D (T * (k₁ * (m + m) + k₂ * m))).bind fun S₁ =>
            (Probability.PMF.iid D (T * (k₁ * (m + m) + k₂ * m))).bind fun S₂ =>
              (pmfPiFin fun t : Fin T =>
                trialRun A k₁ k₂ (BitString.block (m := T) (k := k₁ * (m + m) + k₂ * m) S₁ t)
                  (rs t)).bind
                  fun trials₁ =>
                PMF.map (fun y₂ => (pickFirstThresholded a b N i trials₁, y₂))
                  (PMF.map (fun trials => pickFirstThresholded a b N i trials)
                    (pmfPiFin fun t : Fin T =>
                      trialRun A k₁ k₂
                        (BitString.block (m := T) (k := k₁ * (m + m) + k₂ * m) S₂ t)
                        (rs t))))
      = (Probability.PMF.uniformOfFintype (Fin N)).bind fun i =>
          (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₁ =>
            (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₂ =>
              PMF.pure
                (pickFirstThresholded a b N i trials₁, pickFirstThresholded a b N i trials₂) := by
        refine congrArg (PMF.bind (Probability.PMF.uniformOfFintype (Fin N))) (funext fun i => ?_)
        simp_rw [PMF.map_comp, Function.comp_def]
        exact hS i
    _ = (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₁ =>
          (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₂ =>
            (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
              (pickFirstThresholded a b N i trials₁, pickFirstThresholded a b N i trials₂) := by
        rw [PMF.bind_comm]
        refine congrArg (PMF.bind (pmfPiFin _)) (funext fun trials₁ => ?_)
        rw [PMF.bind_comm]
        rfl

private theorem trialRunMarginal_single_fail [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X)
    (r : Ω) {a δ : ℝ} (hδ : 0 ≤ δ) (ha_half : 1 / 2 + δ < a) (k₁ k₂ : ℕ)
    [NeZero k₁] [NeZero k₂] :
    ((trialRunMarginal A D r k₁ k₂).toOuterMeasure
      {pr : ℝ × α |
        |pr.1 - seedColl A D r| ≤ δ ∧
        (a - δ ≤ seedColl A D r →
          ∀ y : α, a - δ ≤ (seedOutput A D r y).toReal → pr.2 = y)}ᶜ).toReal ≤
      2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) +
        2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2) := by
  let μ := seedOutput A D r
  let collBool : PMF Bool := μ.bind fun y₁ => μ.map fun y₂ => decide (y₁ = y₂)
  have h1 :
      ((Probability.PMF.iid collBool k₁).toOuterMeasure
        {cs : Fin k₁ → Bool |
          δ < |(((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁) -
            seedColl A D r|}).toReal ≤
        2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) := by
    have hconc := empFreq_concentrates collBool k₁ hδ true
    rwa [seedColl_eq_collBool_true] at hconc
  by_cases hcoll : a - δ ≤ seedColl A D r
  · obtain ⟨yStar, hyStar⟩ := exists_heavy_of_le_tsum_sq μ hcoll
    have huniq : ∀ y : α, a - δ ≤ (μ y).toReal → y = yStar := fun y hy => by
      by_contra hne
      have hsum : (μ y).toReal + (μ yStar).toReal ≤ 1 := by
        have hle := ((Probability.PMF.summable_toReal μ).sum_le_tsum ({y, yStar} : Finset α)
          fun _ _ => ENNReal.toReal_nonneg).trans_eq (Probability.PMF.tsum_toReal μ)
        rwa [Finset.sum_pair hne] at hle
      linarith
    let δ_maj : ℝ := (a - δ - 1 / 2) / 2
    have hδ_maj : 0 < δ_maj := by dsimp only [δ_maj]; linarith
    have h2 :
        ((Probability.PMF.iid μ k₂).toOuterMeasure
          {zs : Fin k₂ → α |
            strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩) ≠ yStar}).toReal ≤
          2 * Real.exp (-2 * (k₂ : ℝ) * δ_maj ^ 2) := by
      let q : PMF Bool := μ.map fun z => decide (z = yStar)
      have hq : (q true).toReal = (μ yStar).toReal := by
        rw [← PMF.toOuterMeasure_apply_singleton q true, PMF.toOuterMeasure_map_apply]
        have hset : (fun z : α => decide (z = yStar)) ⁻¹' {true} = {yStar} := by
          ext z
          simp
        rw [hset, PMF.toOuterMeasure_apply_singleton]
      have hsub :
          {zs : Fin k₂ → α | strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩) ≠ yStar} ⊆
          (fun zs : Fin k₂ → α => fun j => decide (zs j = yStar)) ⁻¹'
            {bs : Fin k₂ → Bool | δ_maj < |empFreq k₂ bs true - (q true).toReal|} := by
        intro zs hzs
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, ne_eq] at hzs ⊢
        have hnot : ¬ k₂ < 2 * (Finset.univ.filter fun j : Fin k₂ => zs j = yStar).card :=
          fun hlt => hzs (strictMajorityCandidate_eq_of_lt_two_mul zs _ yStar hlt)
        rw [not_lt] at hnot
        have hcard :
            (Finset.univ.filter fun j : Fin k₂ => decide (zs j = yStar) = true).card =
            (Finset.univ.filter fun j : Fin k₂ => zs j = yStar).card := by
          congr 1
        have hk₂ : (0 : ℝ) < k₂ := Nat.cast_pos.mpr (NeZero.pos k₂)
        have hemp : empFreq k₂ (fun j => decide (zs j = yStar)) true ≤ 1 / 2 := by
          dsimp only [empFreq]
          rw [hcard, div_le_div_iff₀ hk₂ (by norm_num : (0 : ℝ) < 2), one_mul]
          exact_mod_cast
            (by linarith : (Finset.univ.filter fun j => zs j = yStar).card * 2 ≤ k₂)
        have hgap :
            δ_maj < (q true).toReal - empFreq k₂ (fun j => decide (zs j = yStar)) true := by
          rw [hq]
          dsimp only [δ_maj]
          linarith
        exact hgap.trans_le (le_abs_self _ |>.trans (by rw [abs_sub_comm]))
      calc ((Probability.PMF.iid μ k₂).toOuterMeasure _).toReal
          ≤ ((Probability.PMF.iid μ k₂).toOuterMeasure _).toReal :=
            Probability.PMF.toOuterMeasure_toReal_mono _ hsub
        _ = ((Probability.PMF.iid q k₂).toOuterMeasure
              {bs : Fin k₂ → Bool | δ_maj < |empFreq k₂ bs true - (q true).toReal|}).toReal := by
            rw [← PMF.toOuterMeasure_map_apply,
              (Probability.PMF.iid_map μ (fun z => decide (z = yStar)) k₂).symm]
        _ ≤ 2 * Real.exp (-2 * (k₂ : ℝ) * δ_maj ^ 2) := empFreq_concentrates q k₂ hδ_maj.le true
    have hfail1 :
        (((Probability.PMF.iid collBool k₁).bind fun cs =>
          (Probability.PMF.iid μ k₂).map fun zs =>
            (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
              strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩))).toOuterMeasure
          {pr : ℝ × α |
            |pr.1 - seedColl A D r| ≤ δ ∧
            (a - δ ≤ seedColl A D r →
              ∀ y : α, a - δ ≤ (μ y).toReal → pr.2 = y)}ᶜ).toReal ≤
          2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) +
            2 * Real.exp (-2 * (k₂ : ℝ) * δ_maj ^ 2) := by
      let good₁ : Set (Fin k₁ → Bool) :=
        {cs | |(((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁) -
          seedColl A D r| ≤ δ}
      refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ good₁ _
        (error := 2 * Real.exp (-2 * (k₂ : ℝ) * δ_maj ^ 2)) (by positivity) ?_).trans ?_
      · intro cs _ hcs
        rw [PMF.toOuterMeasure_map_apply]
        have hsub :
            (fun zs : Fin k₂ → α =>
              (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
                strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩))) ⁻¹'
              {pr : ℝ × α |
                |pr.1 - seedColl A D r| ≤ δ ∧
                (a - δ ≤ seedColl A D r →
                  ∀ y : α, a - δ ≤ (μ y).toReal → pr.2 = y)}ᶜ ⊆
            {zs : Fin k₂ → α | strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩) ≠ yStar} := by
          intro zs hzs hEq
          simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and] at hzs
          exact hzs hcs (fun _ y hy => hEq.trans (huniq y hy).symm)
        exact (Probability.PMF.toOuterMeasure_toReal_mono _ hsub).trans h2
      · have heqc : good₁ᶜ = {cs : Fin k₁ → Bool |
            δ < |(((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁) -
              seedColl A D r|} := by
          ext cs
          simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, good₁]
        rw [heqc]
        exact add_le_add h1 le_rfl
    exact hfail1
  · have htriv :
        {pr : ℝ × α |
          |pr.1 - seedColl A D r| ≤ δ ∧
          (a - δ ≤ seedColl A D r →
            ∀ y : α, a - δ ≤ (μ y).toReal → pr.2 = y)}ᶜ =
        {pr : ℝ × α | δ < |pr.1 - seedColl A D r|} := by
      ext pr
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, hcoll, false_implies, and_true, not_le]
    dsimp only [trialRunMarginal]
    rw [htriv]
    have hfail2 :
        (((Probability.PMF.iid collBool k₁).bind fun cs =>
          (Probability.PMF.iid μ k₂).map fun zs =>
            (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
              strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩))).toOuterMeasure
          {pr : ℝ × α | δ < |pr.1 - seedColl A D r|}).toReal ≤
          2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) := by
      let good₁ : Set (Fin k₁ → Bool) :=
        {cs | |(((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁) -
          seedColl A D r| ≤ δ}
      refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ good₁ _
        (error := 0) le_rfl ?_).trans ?_
      · intro cs _ hcs
        rw [PMF.toOuterMeasure_map_apply]
        have hempty :
            (fun zs : Fin k₂ → α =>
              (((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁,
                strictMajorityCandidate zs (zs ⟨0, NeZero.pos k₂⟩))) ⁻¹'
              {pr : ℝ × α | δ < |pr.1 - seedColl A D r|} = ∅ := by
          ext zs
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
            not_lt]
          exact hcs
        rw [hempty]
        simp
      · have heqc : good₁ᶜ = {cs : Fin k₁ → Bool |
            δ < |(((Finset.univ.filter fun l : Fin k₁ => cs l = true).card : ℝ) / k₁) -
              seedColl A D r|} := by
          ext cs
          simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, good₁]
        rw [heqc, add_zero]
        exact h1
    exact hfail2.trans (le_add_of_nonneg_right (by positivity))

private theorem seed_markov_err_lt (A : Algorithm X Ω α m) (D : PMF X) (good : Set α)
    {c β₀ : ℝ} (hc : 0 < c) (hacc : ((A.marginal D).toOuterMeasure goodᶜ).toReal ≤ β₀) :
    (A.seed.toOuterMeasure
      {r : Ω | c ≤ ((seedOutput A D r).toOuterMeasure goodᶜ).toReal}).toReal ≤ β₀ / c := by
  have hm_sum :
      ∑' r : Ω, (A.seed r).toReal * ((seedOutput A D r).toOuterMeasure goodᶜ).toReal ≤ β₀ := by
    refine le_trans ?_ hacc
    rw [Algorithm.marginal_eq_seed_bind, PMF.toOuterMeasure_bind_apply, ENNReal.tsum_toReal_eq]
    · exact le_of_eq (tsum_congr fun r => ENNReal.toReal_mul.symm)
    · intro r
      exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (Probability.PMF.toOuterMeasure_ne_top _ _)
  exact pmf_markov_ge_toReal_le A.seed
    (fun r => ((seedOutput A D r).toOuterMeasure goodᶜ).toReal) hc
    (fun _ => ENNReal.toReal_nonneg) (fun r => Probability.PMF.toOuterMeasure_toReal_le_one _ _)
    hm_sum

private theorem pmfPiFin_biUnion_toReal_le {Ω : Type*} {T : ℕ} (p : Fin T → PMF Ω)
    (B : Fin T → Set Ω) (bound : Fin T → ℝ)
    (hB : ∀ t : Fin T, ((p t).toOuterMeasure (B t)).toReal ≤ bound t) :
    ((pmfPiFin p).toOuterMeasure
      (⋃ t ∈ (Finset.univ : Finset (Fin T)), (fun xs : Fin T → Ω => xs t) ⁻¹' B t)).toReal ≤
      ∑ t : Fin T, bound t := by
  refine (Probability.PMF.toOuterMeasure_toReal_biUnion_finset_le _ _ _).trans ?_
  calc ∑ t : Fin T,
          ((pmfPiFin p).toOuterMeasure ((fun xs : Fin T → Ω => xs t) ⁻¹' B t)).toReal
      = ∑ t : Fin T, ((p t).toOuterMeasure (B t)).toReal := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [← PMF.toOuterMeasure_map_apply, pmfPiFin_map_eval]
    _ ≤ ∑ t : Fin T, bound t := Finset.sum_le_sum fun t _ => hB t

private theorem pmfPiFin_exists_le {Ω : Type*} (p : PMF Ω) (P : Ω → Prop) (bound : ℝ)
    (hP : (p.toOuterMeasure {r | P r}).toReal ≤ bound) (T : ℕ) :
    ((pmfPiFin fun _ : Fin T => p).toOuterMeasure
      {rs : Fin T → Ω | ∃ t, P (rs t)}).toReal ≤ (T : ℝ) * bound := by
  have hunion :
      {rs : Fin T → Ω | ∃ t, P (rs t)} =
        ⋃ t ∈ (Finset.univ : Finset (Fin T)),
          (fun rs : Fin T → Ω => rs t) ⁻¹' {r : Ω | P r} := by
    ext rs
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_univ, Set.mem_preimage,
      exists_true_left]
  rw [hunion]
  refine (pmfPiFin_biUnion_toReal_le (fun _ : Fin T => p) (fun _ => {r : Ω | P r})
    (fun _ => bound) (fun _ => hP)).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem bad_goodSeeds_le (A : Algorithm X Ω α m) (D : PMF X) {θ_acc : ℝ}
    (hθ_lt : θ_acc < 1) (T : ℕ) :
    ((pmfPiFin fun _ : Fin T => A.seed).toOuterMeasure
      ({rs : Fin T → Ω | ∃ t : Fin T, θ_acc ≤ seedColl A D (rs t)})ᶜ).toReal ≤
      (A.disagreeProb D / (1 - θ_acc)) ^ T := by
  have heqc : ({rs : Fin T → Ω | ∃ t : Fin T, θ_acc ≤ seedColl A D (rs t)})ᶜ =
      {rs : Fin T → Ω | ∀ t : Fin T, seedColl A D (rs t) < θ_acc} := by
    ext rs
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_le]
  rw [heqc]
  have hpow := ENNReal.toReal_mono
    (ENNReal.pow_ne_top (Probability.PMF.toOuterMeasure_ne_top _ _))
    (pmfPiFin_forall_lt_le A.seed (fun r => seedColl A D r < θ_acc) T)
  rw [ENNReal.toReal_pow] at hpow
  exact hpow.trans (pow_le_pow_left₀ ENNReal.toReal_nonneg (seed_markov_coll_lt A D hθ_lt) T)

private noncomputable def goodTrialsSet (A : Algorithm X Ω α m) (D : PMF X)
    (a δ : ℝ) {T : ℕ} (rs : Fin T → Ω) : Set (Fin T → ℝ × α) :=
  {trials | ∀ t : Fin T,
    |(trials t).1 - seedColl A D (rs t)| ≤ δ ∧
    (a - δ ≤ seedColl A D (rs t) →
      ∀ y : α, a - δ ≤ (seedOutput A D (rs t) y).toReal → (trials t).2 = y)}

private theorem goodTrials_fail_le [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X)
    {a δ : ℝ} (hδ : 0 ≤ δ) (ha_half : 1 / 2 + δ < a) (T k₁ k₂ : ℕ)
    [NeZero k₁] [NeZero k₂] (rs : Fin T → Ω) :
    ((pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).toOuterMeasure
      (goodTrialsSet A D a δ rs)ᶜ).toReal ≤
      (T : ℝ) * (2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) +
        2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2)) := by
  have hunion :
      (goodTrialsSet A D a δ rs)ᶜ =
      ⋃ t ∈ (Finset.univ : Finset (Fin T)),
        (fun trials : Fin T → ℝ × α => trials t) ⁻¹'
          {pr : ℝ × α |
            |pr.1 - seedColl A D (rs t)| ≤ δ ∧
            (a - δ ≤ seedColl A D (rs t) →
              ∀ y : α, a - δ ≤ (seedOutput A D (rs t) y).toReal → pr.2 = y)}ᶜ := by
    ext trials
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, Set.mem_iUnion,
      Finset.mem_univ, Set.mem_preimage, exists_true_left, goodTrialsSet]
  rw [hunion]
  refine (pmfPiFin_biUnion_toReal_le
    (fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂)
    (fun t : Fin T =>
      {pr : ℝ × α |
        |pr.1 - seedColl A D (rs t)| ≤ δ ∧
        (a - δ ≤ seedColl A D (rs t) →
          ∀ y : α, a - δ ≤ (seedOutput A D (rs t) y).toReal → pr.2 = y)}ᶜ)
    (fun _ => 2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) +
      2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2))
    (fun t => trialRunMarginal_single_fail A D (rs t) hδ ha_half k₁ k₂)).trans_eq ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem goodTrial_heavy_of_thresholdPass (A : Algorithm X Ω α m) (D : PMF X)
    {a b δ : ℝ} (hab : a ≤ b) {T N : ℕ} {rs : Fin T → Ω} {trials : Fin T → ℝ × α}
    (htr : trials ∈ goodTrialsSet A D a δ rs) (i : Fin N) (t : Fin T)
    (ht_pass : thresholdRound a b N i (trials t).1 = true) :
    ∃ yStar : α,
      a - δ ≤ seedColl A D (rs t) ∧
      a - δ ≤ (seedOutput A D (rs t) yStar).toReal ∧
      (trials t).2 = yStar := by
  have ht_ge : a ≤ (trials t).1 := by
    by_contra hlt
    rw [not_le] at hlt
    exact absurd ht_pass (by rw [thresholdRound_false_of_lt_left hab i hlt]; decide)
  have hcoll_ge : a - δ ≤ seedColl A D (rs t) := by
    have h2 := (abs_sub_le_iff.mp (htr t).1).1
    linarith
  obtain ⟨yStar, hyStar⟩ := exists_heavy_of_le_tsum_sq (seedOutput A D (rs t)) hcoll_ge
  exact ⟨yStar, hcoll_ge, hyStar, (htr t).2 hcoll_ge yStar hyStar⟩

private theorem pickFirstThresholded_eq_heavy (A : Algorithm X Ω α m) (D : PMF X)
    {a b θ_acc δ : ℝ} (hab : a ≤ b) (hb_acc : b ≤ θ_acc - δ) {T N : ℕ} [NeZero T]
    {rs : Fin T → Ω} {t₀ : Fin T} (ht₀ : θ_acc ≤ seedColl A D (rs t₀))
    {trials : Fin T → ℝ × α} (htr : trials ∈ goodTrialsSet A D a δ rs) (i : Fin N) :
    ∃ tStar : Fin T, ∃ yStar : α,
      pickFirstThresholded a b N i trials = yStar ∧
      a - δ ≤ (seedOutput A D (rs tStar) yStar).toReal := by
  have ht₀_pass : thresholdRound a b N i (trials t₀).1 = true := by
    have h1 := (abs_sub_le_iff.mp (htr t₀).1).2
    exact thresholdRound_true_of_right_le hab i (by linarith)
  have hne : (Finset.univ.filter fun t : Fin T =>
      thresholdRound a b N i (trials t).1 = true).Nonempty :=
    ⟨t₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht₀_pass⟩⟩
  let tStar := (Finset.univ.filter fun t : Fin T =>
    thresholdRound a b N i (trials t).1 = true).min' hne
  have hpick : pickFirstThresholded a b N i trials = (trials tStar).2 := by
    dsimp only [pickFirstThresholded]
    split_ifs
    rfl
  have ht_pass : thresholdRound a b N i (trials tStar).1 = true :=
    (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  obtain ⟨yStar, _, hyStar, heq⟩ :=
    goodTrial_heavy_of_thresholdPass A D hab htr i tStar ht_pass
  exact ⟨tStar, yStar, hpick.trans heq, hyStar⟩

/-- Disagreement probability upper bound for `amplifyReplicability`: if
`1 / 2 + δ < a < b ≤ θ_acc - δ` and `θ_acc < 1`, then
`(amplifyReplicability A a b T k₁ k₂ N).disagreeProb D` is bounded by the bad-seed probability
`(A.disagreeProb D / (1 - θ_acc)) ^ T`, twice the concentration error over `T` trials, and the
threshold discretization error `T * (2 * δ / (b - a) + 1 / N)`. -/
theorem disagreeProb_amplifyReplicability_le [DecidableEq α] (A : Algorithm X Ω α m) (D : PMF X)
    {a b θ_acc δ : ℝ} (hab : a < b) (hδ : 0 ≤ δ) (ha_half : 1 / 2 + δ < a)
    (hb_acc : b ≤ θ_acc - δ) (hθ_lt : θ_acc < 1) (T k₁ k₂ N : ℕ)
    [NeZero T] [NeZero k₁] [NeZero k₂] [NeZero N] :
    (amplifyReplicability A a b T k₁ k₂ N).disagreeProb D ≤
      (A.disagreeProb D / (1 - θ_acc)) ^ T +
        2 * ((T : ℝ) * (2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) +
          2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2))) +
        (T : ℝ) * (2 * δ / (b - a) + 1 / N) := by
  rw [Algorithm.disagreeProb, pairedOutput_amplifyReplicability]
  let collFail : ℝ := 2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2)
  let majFail : ℝ := 2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2)
  let trialFail : ℝ := (T : ℝ) * (collFail + majFail)
  let seedFail : ℝ := (T : ℝ) * (2 * δ / (b - a) + 1 / N)
  have htf_nn : 0 ≤ trialFail := by positivity
  have hsf_nn : 0 ≤ seedFail := by
    have hba : 0 < b - a := sub_pos.mpr hab
    positivity
  let goodSeeds : Set (Fin T → Ω) := {rs | ∃ t : Fin T, θ_acc ≤ seedColl A D (rs t)}
  have hbad_seeds :
      ((pmfPiFin fun _ : Fin T => A.seed).toOuterMeasure goodSeedsᶜ).toReal ≤
        (A.disagreeProb D / (1 - θ_acc)) ^ T :=
    bad_goodSeeds_le A D hθ_lt T
  have hrs_step :
      ∀ rs ∈ goodSeeds,
        (((pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₁ =>
          (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₂ =>
            (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
              (pickFirstThresholded a b N i trials₁,
                pickFirstThresholded a b N i trials₂)).toOuterMeasure
          {p : α × α | p.1 ≠ p.2}).toReal ≤
          2 * trialFail + seedFail := by
    intro rs ⟨t₀, ht₀⟩
    let goodTrials := goodTrialsSet A D a δ rs
    have hbad_trials :
        ((pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).toOuterMeasure
          goodTrialsᶜ).toReal ≤ trialFail :=
      goodTrials_fail_le A D hδ ha_half T k₁ k₂ rs
    have htrials_inner :
        ∀ trials₁ ∈ goodTrials,
          (((pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₂ =>
            (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
              (pickFirstThresholded a b N i trials₁,
                pickFirstThresholded a b N i trials₂)).toOuterMeasure
            {p : α × α | p.1 ≠ p.2}).toReal ≤ trialFail + seedFail := by
      intro trials₁ htr₁
      refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ goodTrials _ hsf_nn
        ?_).trans (add_le_add hbad_trials le_rfl)
      intro trials₂ _ htr₂
      rw [PMF.toOuterMeasure_map_apply]
      have hpre :
          (fun i : Fin N =>
            (pickFirstThresholded a b N i trials₁, pickFirstThresholded a b N i trials₂)) ⁻¹'
            {p : α × α | p.1 ≠ p.2} ⊆
          ⋃ t ∈ (Finset.univ : Finset (Fin T)),
            {i : Fin N | thresholdRound a b N i (trials₁ t).1 ≠
              thresholdRound a b N i (trials₂ t).1} := by
        intro i hi
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, ne_eq, Set.mem_iUnion, Finset.mem_univ,
          exists_true_left] at hi ⊢
        by_contra hnone
        push Not at hnone
        have hcand :
            (Finset.univ.filter fun t : Fin T => thresholdRound a b N i (trials₁ t).1 = true) =
            (Finset.univ.filter fun t : Fin T => thresholdRound a b N i (trials₂ t).1 = true) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnone t]
        have ht₀_pass1 : thresholdRound a b N i (trials₁ t₀).1 = true := by
          have h1 := (abs_sub_le_iff.mp (htr₁ t₀).1).2
          exact thresholdRound_true_of_right_le hab.le i (by linarith)
        have hne1 : (Finset.univ.filter fun t : Fin T =>
            thresholdRound a b N i (trials₁ t).1 = true).Nonempty :=
          ⟨t₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht₀_pass1⟩⟩
        have hne2 : (Finset.univ.filter fun t : Fin T =>
            thresholdRound a b N i (trials₂ t).1 = true).Nonempty := hcand ▸ hne1
        let tStar := (Finset.univ.filter fun t : Fin T =>
          thresholdRound a b N i (trials₁ t).1 = true).min' hne1
        have hpick1 : pickFirstThresholded a b N i trials₁ = (trials₁ tStar).2 := by
          dsimp only [pickFirstThresholded]
          split_ifs
          rfl
        have hpick2 : pickFirstThresholded a b N i trials₂ = (trials₂ tStar).2 := by
          have h2 : pickFirstThresholded a b N i trials₂ =
              (trials₂ ((Finset.univ.filter fun t : Fin T =>
                thresholdRound a b N i (trials₂ t).1 = true).min' hne2)).2 := by
            dsimp only [pickFirstThresholded]
            split_ifs
            rfl
          rw [h2]
          have hmin : ∀ (s₁ s₂ : Finset (Fin T)) (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty),
              s₁ = s₂ → s₁.min' h₁ = s₂.min' h₂ := by
            rintro s _ h₁ h₂ rfl
            rfl
          exact congrArg (fun t => (trials₂ t).2) (hmin _ _ hne2 hne1 hcand.symm)
        have ht_pass : thresholdRound a b N i (trials₁ tStar).1 = true :=
          (Finset.mem_filter.mp (Finset.min'_mem _ hne1)).2
        obtain ⟨yStar, hcoll_ge, hyStar, h1eq⟩ :=
          goodTrial_heavy_of_thresholdPass A D hab.le htr₁ i tStar ht_pass
        have h2eq : (trials₂ tStar).2 = yStar := (htr₂ tStar).2 hcoll_ge yStar hyStar
        exact hi (by rw [hpick1, hpick2, h1eq, h2eq])
      have hmono := Probability.PMF.toOuterMeasure_toReal_mono
        (Probability.PMF.uniformOfFintype (Fin N)) hpre
      have hunionR := Probability.PMF.toOuterMeasure_toReal_biUnion_finset_le
        (Probability.PMF.uniformOfFintype (Fin N)) Finset.univ
        (fun t => {i : Fin N | thresholdRound a b N i (trials₁ t).1 ≠
          thresholdRound a b N i (trials₂ t).1})
      refine (hmono.trans hunionR).trans ?_
      calc ∑ t : Fin T, ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure
              {i : Fin N | thresholdRound a b N i (trials₁ t).1 ≠
                thresholdRound a b N i (trials₂ t).1}).toReal
          ≤ ∑ _t : Fin T, (2 * δ / (b - a) + 1 / N) := by
            refine Finset.sum_le_sum fun t _ => ?_
            have hdist : |(trials₁ t).1 - (trials₂ t).1| ≤ 2 * δ := by
              have h1 := (htr₁ t).1
              have h2 := (htr₂ t).1
              rw [abs_sub_comm] at h2
              calc |(trials₁ t).1 - (trials₂ t).1|
                  = |((trials₁ t).1 - seedColl A D (rs t)) +
                      (seedColl A D (rs t) - (trials₂ t).1)| := by ring_nf
                _ ≤ |(trials₁ t).1 - seedColl A D (rs t)| +
                      |seedColl A D (rs t) - (trials₂ t).1| := abs_add_le _ _
                _ ≤ δ + δ := add_le_add h1 h2
                _ = 2 * δ := by ring
            refine (thresholdRound_disagree_le hab (trials₁ t).1 (trials₂ t).1).trans ?_
            have hba : 0 < b - a := sub_pos.mpr hab
            gcongr
        _ = seedFail := by
            dsimp only [seedFail]
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have houter := Probability.PMF.toOuterMeasure_bind_failure_toReal_le
      (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂)
      (fun trials₁ => (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind
        fun trials₂ => (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
          (pickFirstThresholded a b N i trials₁, pickFirstThresholded a b N i trials₂))
      goodTrials {p : α × α | p.1 ≠ p.2} (add_nonneg htf_nn hsf_nn)
      (fun trials₁ _ htr₁ => htrials_inner trials₁ htr₁)
    linarith [houter, hbad_trials]
  have hfull := Probability.PMF.toOuterMeasure_bind_failure_toReal_le
    (pmfPiFin fun _ : Fin T => A.seed)
    (fun rs =>
      (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₁ =>
        (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials₂ =>
          (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
            (pickFirstThresholded a b N i trials₁, pickFirstThresholded a b N i trials₂))
    goodSeeds {p : α × α | p.1 ≠ p.2} (by positivity) (fun rs _ hrs => hrs_step rs hrs)
  dsimp only [trialFail, seedFail, collFail, majFail] at hfull
  linarith [hfull, hbad_seeds]

/-- **Accuracy preservation for `amplifyReplicability`**: under `IsReplicableFor A 𝒟 ρ₀` and
`IsAccurateFor A 𝒟 good β₀` with `1 / 2 + δ < a < b ≤ θ_acc - δ` and `θ_acc < 1`, the failure
probability of `amplifyReplicability` is bounded by the bad-seed probability
`(ρ₀ / (1 - θ_acc)) ^ T`, the Markov union bound `(T : ℝ) * (β₀ / (a - δ))` over the `T`
candidate seeds, and the per-trial concentration errors. -/
theorem isAccurateFor_amplifyReplicability [DecidableEq α] (A : Algorithm X Ω α m)
    {𝒟 : Set (PMF X)} {good : PMF X → Set α} {ρ₀ β₀ a b θ_acc δ : ℝ}
    (hrep : IsReplicableFor A 𝒟 ρ₀) (hacc : IsAccurateFor A 𝒟 good β₀)
    (hab : a < b) (hδ : 0 ≤ δ) (ha_half : 1 / 2 + δ < a) (hb_acc : b ≤ θ_acc - δ)
    (hθ_lt : θ_acc < 1) (T k₁ k₂ N : ℕ) [NeZero T] [NeZero k₁] [NeZero k₂] [NeZero N] :
    IsAccurateFor (amplifyReplicability A a b T k₁ k₂ N) 𝒟 good
      ((ρ₀ / (1 - θ_acc)) ^ T + (T : ℝ) * (β₀ / (a - δ)) +
        (T : ℝ) * (2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2) +
          2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2))) := by
  intro D hD
  rw [marginal_amplifyReplicability]
  have had_pos : 0 < a - δ := by linarith
  let collFail : ℝ := 2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2)
  let majFail : ℝ := 2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2)
  let trialFail : ℝ := (T : ℝ) * (collFail + majFail)
  have htf_nn : 0 ≤ trialFail := by positivity
  let goodSeeds : Set (Fin T → Ω) := {rs | ∃ t : Fin T, θ_acc ≤ seedColl A D (rs t)}
  let badErrSeeds : Set (Fin T → Ω) :=
    {rs | ∃ t : Fin T, a - δ ≤ ((seedOutput A D (rs t)).toOuterMeasure (good D)ᶜ).toReal}
  let goodRS : Set (Fin T → Ω) := goodSeeds ∩ badErrSeedsᶜ
  have hbad_coll :
      ((pmfPiFin fun _ : Fin T => A.seed).toOuterMeasure goodSeedsᶜ).toReal ≤
        (ρ₀ / (1 - θ_acc)) ^ T := by
    refine (bad_goodSeeds_le A D hθ_lt T).trans ?_
    exact pow_le_pow_left₀ (div_nonneg (A.disagreeProb_nonneg D) (sub_pos.mpr hθ_lt).le)
      (div_le_div_of_nonneg_right (hrep D hD) (sub_pos.mpr hθ_lt).le) T
  have hbad_err :
      ((pmfPiFin fun _ : Fin T => A.seed).toOuterMeasure badErrSeeds).toReal ≤
        (T : ℝ) * (β₀ / (a - δ)) :=
    pmfPiFin_exists_le A.seed
      (fun r => a - δ ≤ ((seedOutput A D r).toOuterMeasure (good D)ᶜ).toReal)
      (β₀ / (a - δ)) (seed_markov_err_lt A D (good D) had_pos (hacc D hD)) T
  have hgoodRS_c :
      ((pmfPiFin fun _ : Fin T => A.seed).toOuterMeasure goodRSᶜ).toReal ≤
        (ρ₀ / (1 - θ_acc)) ^ T + (T : ℝ) * (β₀ / (a - δ)) := by
    have hsub : goodRSᶜ ⊆ goodSeedsᶜ ∪ badErrSeeds := by
      intro rs hrs
      simp only [Set.mem_compl_iff, Set.mem_inter_iff, not_and, not_not, goodRS] at hrs
      by_cases hg : rs ∈ goodSeeds
      · exact Or.inr (hrs hg)
      · exact Or.inl hg
    have hle := (MeasureTheory.measure_mono (μ := (pmfPiFin fun _ : Fin T => A.seed).toOuterMeasure)
      hsub).trans (MeasureTheory.measure_union_le goodSeedsᶜ badErrSeeds)
    have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨Probability.PMF.toOuterMeasure_ne_top _ _, Probability.PMF.toOuterMeasure_ne_top _ _⟩) hle
    rw [ENNReal.toReal_add (Probability.PMF.toOuterMeasure_ne_top _ _)
      (Probability.PMF.toOuterMeasure_ne_top _ _)] at hreal
    exact hreal.trans (add_le_add hbad_coll hbad_err)
  have hrs_step :
      ∀ rs ∈ goodRS,
        (((pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials =>
          (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
            pickFirstThresholded a b N i trials).toOuterMeasure (good D)ᶜ).toReal ≤ trialFail := by
    rintro rs ⟨⟨t₀, ht₀⟩, herr⟩
    let goodTrials := goodTrialsSet A D a δ rs
    have hbad_trials :
        ((pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).toOuterMeasure
          goodTrialsᶜ).toReal ≤ trialFail :=
      goodTrials_fail_le A D hδ ha_half T k₁ k₂ rs
    refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ goodTrials (good D)ᶜ
      le_rfl fun trials _ htr => ?_).trans (by linarith)
    rw [PMF.toOuterMeasure_map_apply]
    have hempty : (fun i : Fin N => pickFirstThresholded a b N i trials) ⁻¹' (good D)ᶜ = ∅ := by
      ext i
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
      obtain ⟨tStar, yStar, hpick, hyStar⟩ :=
        pickFirstThresholded_eq_heavy A D hab.le hb_acc ht₀ htr i
      rw [hpick]
      by_contra hy_bad
      have herr_t : ((seedOutput A D (rs tStar)).toOuterMeasure (good D)ᶜ).toReal < a - δ := by
        by_contra hge
        rw [not_lt] at hge
        exact herr ⟨tStar, hge⟩
      have hle_y : (seedOutput A D (rs tStar) yStar).toReal ≤
          ((seedOutput A D (rs tStar)).toOuterMeasure (good D)ᶜ).toReal := by
        calc (seedOutput A D (rs tStar) yStar).toReal
            = ((seedOutput A D (rs tStar)).toOuterMeasure {yStar}).toReal := by
              rw [PMF.toOuterMeasure_apply_singleton]
          _ ≤ ((seedOutput A D (rs tStar)).toOuterMeasure (good D)ᶜ).toReal :=
              Probability.PMF.toOuterMeasure_toReal_mono _ (Set.singleton_subset_iff.mpr hy_bad)
      linarith
    rw [hempty]
    simp
  have hfull := Probability.PMF.toOuterMeasure_bind_failure_toReal_le
    (pmfPiFin fun _ : Fin T => A.seed)
    (fun rs => (pmfPiFin fun t : Fin T => trialRunMarginal A D (rs t) k₁ k₂).bind fun trials =>
      (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
        pickFirstThresholded a b N i trials)
    goodRS (good D)ᶜ htf_nn (fun rs _ hrs => hrs_step rs hrs)
  dsimp only [trialFail, collFail, majFail] at hfull
  linarith [hfull, hgoodRS_c]

/-- **General-domain replicability and accuracy-preserving amplification**: over any
`[DecidableEq α]`, for any initial `ρ₀ < 1 / 2` and target `ρ, β > 0`, there exist shared-seed
and trial parameters `(a, b, T, k₁, k₂, N)` together with an initial-error threshold `β₀_req > 0`
(of order `O(β / T)`) such that any `ρ₀`-replicable algorithm `A` whose error satisfies
`β₀ ≤ β₀_req` is amplified to `ρ`-replicability while preserving `(good, β)` accuracy. -/
theorem exists_amplifyReplicability_accurate {ρ₀ ρ β : ℝ} (hρ₀_nonneg : 0 ≤ ρ₀)
    (hρ₀ : ρ₀ < 1 / 2) (hρ : 0 < ρ) (hβ : 0 < β) :
    ∃ (a b : ℝ) (T k₁ k₂ N : ℕ) (_ : NeZero T) (_ : NeZero k₁) (_ : NeZero k₂) (_ : NeZero N)
      (β₀_req : ℝ), 0 < β₀_req ∧
      ∀ {X : Type u} {Ω : Type v} {α : Type w} {m : ℕ} [DecidableEq α]
        (A : Algorithm X Ω α m) {𝒟 : Set (PMF X)} {good : PMF X → Set α} {β₀ : ℝ},
        IsReplicableFor A 𝒟 ρ₀ → IsAccurateFor A 𝒟 good β₀ → β₀ ≤ β₀_req →
          IsReplicableFor (amplifyReplicability A a b T k₁ k₂ N) 𝒟 ρ ∧
          IsAccurateFor (amplifyReplicability A a b T k₁ k₂ N) 𝒟 good β := by
  let ε : ℝ := min ρ β
  have hε : 0 < ε := lt_min hρ hβ
  let γ : ℝ := (1 / 2 - ρ₀) / 4
  have hγ : 0 < γ := by positivity
  let a : ℝ := 1 / 2 + γ
  let b : ℝ := 1 / 2 + 2 * γ
  let θ_acc : ℝ := 1 / 2 + 3 * γ
  have hab : a < b := by dsimp only [a, b]; linarith
  have hba : 0 < b - a := sub_pos.mpr hab
  have hθ_lt : θ_acc < 1 := by dsimp only [θ_acc, γ]; linarith
  let q : ℝ := ρ₀ / (1 - θ_acc)
  have hq0 : 0 ≤ q := div_nonneg hρ₀_nonneg (sub_pos.mpr hθ_lt).le
  have hq1 : q < 1 := by
    rw [div_lt_one (sub_pos.mpr hθ_lt)]
    dsimp only [θ_acc, γ]
    linarith
  obtain ⟨T0, hT0⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ε / 4) hq1
  let T : ℕ := max T0 1
  have hTpos : 0 < T := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hT_inst : NeZero T := ⟨Nat.ne_of_gt hTpos⟩
  have hT_pow : q ^ T ≤ ε / 4 :=
    (pow_le_pow_of_le_one hq0 hq1.le (le_max_left T0 1)).trans hT0.le
  obtain ⟨N, hN_gt⟩ := exists_nat_gt (4 * (T : ℝ) / ρ)
  have hNpos : 0 < N := by
    have : 0 < 4 * (T : ℝ) / ρ := by positivity
    exact_mod_cast this.trans hN_gt
  have hN_inst : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  have hN_bound : (T : ℝ) / N ≤ ρ / 4 := by
    have hmul : 4 * (T : ℝ) < (N : ℝ) * ρ := (div_lt_iff₀ hρ).mp hN_gt
    have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
    rw [div_le_div_iff₀ hNR (by norm_num : (0 : ℝ) < 4)]
    linarith
  let δ : ℝ := min (γ / 2) ((ρ / (8 * (T : ℝ))) * (b - a))
  have hδ : 0 < δ := lt_min (by positivity) (mul_pos (div_pos hρ (by positivity)) hba)
  have ha_half : 1 / 2 + δ < a := by
    have : δ ≤ γ / 2 := min_le_left _ _
    dsimp only [a]
    linarith
  have hb_acc : b ≤ θ_acc - δ := by
    have : δ ≤ γ / 2 := min_le_left _ _
    dsimp only [b, θ_acc]
    linarith
  let δ_maj : ℝ := (a - δ - 1 / 2) / 2
  have hδ_maj : 0 < δ_maj := by dsimp only [δ_maj]; linarith
  obtain ⟨k₁, hk₁pos, hk₁_bound⟩ := exp_decay_exists (2 * (T : ℝ)) hδ
    (by positivity : 0 < ε / 8)
  have hk₁_inst : NeZero k₁ := ⟨Nat.ne_of_gt hk₁pos⟩
  obtain ⟨k₂, hk₂pos, hk₂_bound⟩ := exp_decay_exists (2 * (T : ℝ)) hδ_maj
    (by positivity : 0 < ε / 8)
  have hk₂_inst : NeZero k₂ := ⟨Nat.ne_of_gt hk₂pos⟩
  let β₀_req : ℝ := (β / 4) * (a - δ) / T
  have had_pos : 0 < a - δ := by linarith
  have hTR : (0 : ℝ) < T := Nat.cast_pos.mpr hTpos
  have hβ₀_req : 0 < β₀_req := by positivity
  refine ⟨a, b, T, k₁, k₂, N, hT_inst, hk₁_inst, hk₂_inst, hN_inst, β₀_req, hβ₀_req, ?_⟩
  intro X Ω α m _ A 𝒟 good β₀ hrep hacc hβ₀_le
  have hε_rho : ε ≤ ρ := min_le_left _ _
  have hε_beta : ε ≤ β := min_le_right _ _
  have hrep_out : IsReplicableFor (amplifyReplicability A a b T k₁ k₂ N) 𝒟 ρ := by
    intro D hD
    have hbase := disagreeProb_amplifyReplicability_le A D hab hδ.le ha_half hb_acc hθ_lt T k₁ k₂ N
    have hpow : (A.disagreeProb D / (1 - θ_acc)) ^ T ≤ ρ / 4 := by
      have hdiv : A.disagreeProb D / (1 - θ_acc) ≤ q :=
        div_le_div_of_nonneg_right (hrep D hD) (sub_pos.mpr hθ_lt).le
      exact (pow_le_pow_left₀ (div_nonneg (A.disagreeProb_nonneg D) (sub_pos.mpr hθ_lt).le)
        hdiv T).trans (hT_pow.trans (by linarith))
    have hseed1 : (T : ℝ) * (2 * δ / (b - a)) ≤ ρ / 4 := by
      have hle : δ ≤ (ρ / (8 * (T : ℝ))) * (b - a) := min_le_right _ _
      calc (T : ℝ) * (2 * δ / (b - a))
          ≤ (T : ℝ) * (2 * ((ρ / (8 * (T : ℝ))) * (b - a)) / (b - a)) := by gcongr
        _ = ρ / 4 := by field_simp [hTR.ne', hba.ne']; ring
    have hseed2 : (T : ℝ) * (2 * δ / (b - a) + 1 / N) =
        (T : ℝ) * (2 * δ / (b - a)) + (T : ℝ) / N := by ring
    dsimp only [δ_maj] at hk₂_bound
    linarith [hbase, hpow, hk₁_bound, hk₂_bound, hseed1, hseed2, hN_bound]
  have hacc_out : IsAccurateFor (amplifyReplicability A a b T k₁ k₂ N) 𝒟 good β := by
    refine (isAccurateFor_amplifyReplicability A hrep hacc hab hδ.le ha_half hb_acc hθ_lt
      T k₁ k₂ N).mono ?_
    have h1 : (ρ₀ / (1 - θ_acc)) ^ T ≤ β / 4 := hT_pow.trans (by linarith)
    have h2 : (T : ℝ) * (β₀ / (a - δ)) ≤ β / 4 := by
      calc (T : ℝ) * (β₀ / (a - δ))
          ≤ (T : ℝ) * (β₀_req / (a - δ)) := by gcongr
        _ = β / 4 := by
            dsimp only [β₀_req]
            field_simp [hTR.ne', had_pos.ne']
    have h_exp1 : (T : ℝ) * (2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2)) ≤ β / 8 := by
      have hnn : 0 ≤ (T : ℝ) * (2 * Real.exp (-2 * (k₁ : ℝ) * δ ^ 2)) := by positivity
      linarith
    have h_exp2 :
        (T : ℝ) * (2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2)) ≤ β / 8 := by
      have hnn :
          0 ≤ (T : ℝ) * (2 * Real.exp (-2 * (k₂ : ℝ) * ((a - δ - 1 / 2) / 2) ^ 2)) := by
        positivity
      dsimp only [δ_maj] at hk₂_bound
      linarith
    linarith
  exact ⟨hrep_out, hacc_out⟩

/-- **General-domain replicability amplification** [ImpagliazzoLeiPitassiSorrell2022]: over any
`[DecidableEq α]` output type, any algorithm `A` that is weakly (or strongly) `ρ₀`-replicable on
`𝒟` with `ρ₀ < 1 / 2` can be amplified to `ρ`-replicability for **any** target `ρ > 0`.
See `exists_amplifyReplicability_accurate` for preserved `(good, β)` accuracy under `O(β / T)`
initial error. -/
theorem exists_amplifyReplicability [DecidableEq α] (A : Algorithm X Ω α m) {𝒟 : Set (PMF X)}
    {ρ₀ ρ : ℝ} (hrep : IsReplicableFor A 𝒟 ρ₀) (hρ₀_nonneg : 0 ≤ ρ₀) (hρ₀ : ρ₀ < 1 / 2)
    (hρ : 0 < ρ) :
    ∃ (a b : ℝ) (T k₁ k₂ N : ℕ) (_ : NeZero T) (_ : NeZero k₁) (_ : NeZero k₂) (_ : NeZero N),
      IsReplicableFor (amplifyReplicability A a b T k₁ k₂ N) 𝒟 ρ := by
  obtain ⟨a, b, T, k₁, k₂, N, hT, hk₁, hk₂, hN, β₀_req, hβ₀_pos, hspec⟩ :=
    exists_amplifyReplicability_accurate.{u, v, w} hρ₀_nonneg hρ₀ hρ zero_lt_one
  have hacc_triv : IsAccurateFor A 𝒟 (fun _ => Set.univ) 0 := fun D _ => by simp
  exact ⟨a, b, T, k₁, k₂, N, hT, hk₁, hk₂, hN, (hspec A hrep hacc_triv hβ₀_pos.le).1⟩

end GeneralDomainAmplification

end Cslib.MachineLearning.Replicable
