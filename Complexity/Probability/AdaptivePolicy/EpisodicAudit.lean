/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.AdaptivePolicy.Covariance
public import Complexity.Probability.ImportanceSampling
public import Complexity.Probability.PMF
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

/-!
# Finite-horizon trajectory experiments

[Aldridge2027], Section 5.2, PDF pp. 5–6. A trajectory retains every sampled
action and next state, including the terminal state. The law below uses the
actual controlled transitions, with no independence assumption between successive
states. Independent episodes are products of this trajectory law.

## Main definitions

* `EpisodeTail`: actions and next states in a finite episode.
* `FiniteMDP.episodeLaw`: the actual whole-trajectory law.
* `FiniteMDP.episodeLoss`: total observed cost along the trajectory.

## Main results

* `FiniteMDP.episodic_auditor_moments`: actual expectation and variance bounds.
* `FiniteMDP.trajectoryChiSquared_product_bound`: supported-state divergence product bound.
* `FiniteMDP.episodic_observed_auditor`: confidence using only the observed episode records.
* `FiniteMDP.episodic_auditor_ceiling`: the exact integer episode count.
* `FiniteMDP.episodic_gap_eq_zero`: the zero-parameter branch, including horizon zero.
-/

public section
noncomputable section
open Finset MeasureTheory ProbabilityTheory
namespace Cslib.Probability.AdaptivePolicy

universe u v

/-- Actions and next states following a given initial state. -/
@[expose] def EpisodeTail (S : Type u) (A : Type v) : ℕ → Type (max u v)
  | 0 => PUnit
  | n + 1 => A × S × EpisodeTail S A n

instance episodeTailFintype (S A : Type*) [Fintype S] [Fintype A] :
    (n : ℕ) → Fintype (EpisodeTail S A n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => let := episodeTailFintype S A n
             inferInstanceAs (Fintype (A × S × EpisodeTail S A n))

instance episodeTailZeroUnique (S A : Type*) : Unique (EpisodeTail S A 0) :=
  inferInstanceAs (Unique PUnit)

instance episodeTailMeasurableSpace (S A : Type*) (n : ℕ) :
    MeasurableSpace (EpisodeTail S A n) := ⊤

instance episodeTailDiscrete (S A : Type*) (n : ℕ) :
    DiscreteMeasurableSpace (EpisodeTail S A n) := ⟨fun _ => trivial⟩

namespace FiniteMDP
variable {S A : Type*} [Fintype S] [Fintype A]
variable (M : FiniteMDP S A)

/-- Conditional trajectory mass from the current state and time. -/
@[expose] def episodeMassFrom (π : MarkovPolicy S A) :
    (n : ℕ) → ℕ → S → EpisodeTail S A n → ℝ
  | 0, _, _, _ => 1
  | n + 1, t, s, (a, s', tail) =>
      π.prob t s a * M.transition t s a s' * episodeMassFrom π n (t + 1) s' tail

/-- Trajectory mass is nonnegative. -/
theorem episodeMassFrom_nonneg (π : MarkovPolicy S A) (n t : ℕ) (s : S)
    (z : EpisodeTail S A n) : 0 ≤ M.episodeMassFrom π n t s z := by
  induction n generalizing t s with
  | zero => exact zero_le_one
  | succ n ih =>
    obtain ⟨a, s', tail⟩ := z
    exact mul_nonneg (mul_nonneg (π.nonneg t s a) (M.transition_nonneg t s a s'))
      (ih (t + 1) s' tail)

/-- The full conditional trajectory law is normalized. -/
theorem episodeMassFrom_sum (π : MarkovPolicy S A) (n t : ℕ) (s : S) :
    ∑ z, M.episodeMassFrom π n t s z = 1 := by
  induction n generalizing t s with
  | zero => simp [episodeMassFrom]
  | succ n ih =>
    change (∑ z : A × S × EpisodeTail S A n,
      π.prob t s z.1 * M.transition t s z.1 z.2.1 *
        M.episodeMassFrom π n (t + 1) z.2.1 z.2.2) = 1
    simp only [Fintype.sum_prod_type, ← mul_sum,
      ih, mul_one, M.transition_sum, π.sum_prob]

/-- Draw the initial state, then all conditionally independent action/transition
randomizations along one actual episode. -/
@[expose] def episodeLaw (π : MarkovPolicy S A) (H : ℕ) : PMF (S × EpisodeTail S A H) :=
  PMF.ofFintype (fun (s, tail) => ENNReal.ofReal
    (M.initial s * M.episodeMassFrom π H 0 s tail)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun ⟨s, tail⟩ _ =>
        mul_nonneg (M.initial_nonneg s) (M.episodeMassFrom_nonneg π H 0 s tail))]
      simp only [Fintype.sum_prod_type, ← mul_sum, M.episodeMassFrom_sum, mul_one,
        M.initial_sum, ENNReal.ofReal_one])

/-- The law has exactly the product of the initial, policy and transition factors. -/
theorem episodeLaw_real (π : MarkovPolicy S A) (H : ℕ) (s : S) (tail : EpisodeTail S A H) :
    (M.episodeLaw π H (s, tail)).toReal = M.initial s * M.episodeMassFrom π H 0 s tail :=
  ENNReal.toReal_ofReal (mul_nonneg (M.initial_nonneg s)
    (M.episodeMassFrom_nonneg π H 0 s tail))

/-- Total cost from the current state, retaining the actual successive actions. -/
@[expose] def episodeLossFrom : (n : ℕ) → ℕ → S → EpisodeTail S A n → ℝ
  | 0, _, _, _ => 0
  | n + 1, t, s, (a, s', tail) => M.cost t s a + episodeLossFrom n (t + 1) s' tail

/-- Total observed trajectory cost. -/
@[expose] def episodeLoss (H : ℕ) : S × EpisodeTail S A H → ℝ :=
  fun (s, tail) => M.episodeLossFrom H 0 s tail

/-- Expected trajectory cost agrees with the ordinary backward value function. -/
theorem episodeLossFrom_expect (π : MarkovPolicy S A) (n t : ℕ) (s : S) :
    (∑ z, M.episodeMassFrom π n t s z * M.episodeLossFrom n t s z) = M.value π n t s := by
  induction n generalizing t s with
  | zero => simp [episodeLossFrom, value]
  | succ n ih =>
    change (∑ z : A × S × EpisodeTail S A n,
      (π.prob t s z.1 * M.transition t s z.1 z.2.1 *
        M.episodeMassFrom π n (t + 1) z.2.1 z.2.2) *
          (M.cost t s z.1 + M.episodeLossFrom n (t + 1) z.2.1 z.2.2)) = _
    simp only [Fintype.sum_prod_type,
      mul_add, sum_add_distrib, ← mul_sum, mul_assoc]
    simp only [← mul_assoc, ← sum_mul, M.episodeMassFrom_sum, one_mul, ih]
    simp only [value, mul_add, sum_add_distrib, M.transition_sum, mul_one]

/-- Whole-trajectory expected cost equals the established finite-MDP cost,
so trajectory importance sampling estimates the original adaptivity target. -/
theorem episodeLoss_integral [MeasurableSpace S] [MeasurableSingletonClass S]
    (π : MarkovPolicy S A) (H : ℕ) :
    ∫ z, M.episodeLoss H z ∂(M.episodeLaw π H).toMeasure = M.totalCost π H := by
  rw [PMF.integral_eq_sum, M.totalCost_eq_value]
  simp only [Fintype.sum_prod_type, episodeLaw_real, episodeLoss, smul_eq_mul, mul_assoc,
    ← mul_sum, M.episodeLossFrom_expect]

/-- Unit step costs give a trajectory cost in `[0,H]`, including horizon zero. -/
theorem episodeLossFrom_mem_Icc {H : ℕ}
    (hcost : ∀ t < H, ∀ s a, M.cost t s a ∈ Set.Icc (0 : ℝ) 1)
    (n t : ℕ) (s : S) (z : EpisodeTail S A n) (ht : n + t ≤ H) :
    M.episodeLossFrom n t s z ∈ Set.Icc (0 : ℝ) n := by
  induction n generalizing t s with
  | zero => simp [episodeLossFrom]
  | succ n ih =>
    obtain ⟨a, s', tail⟩ := z
    have htail := ih (t + 1) s' tail (by omega)
    simp only [episodeLossFrom, Nat.cast_add, Nat.cast_one]
    exact ⟨by linarith [(hcost t (by omega) s a).1, htail.1],
      by linarith [(hcost t (by omega) s a).2, htail.2]⟩

/-- Product of the logged target/behavior action-propensity ratios. -/
@[expose] def episodeWeightFrom (π ν : MarkovPolicy S A) :
    (n : ℕ) → ℕ → S → EpisodeTail S A n → ℝ
  | 0, _, _, _ => 1
  | n + 1, t, s, (a, s', tail) =>
      ν.prob t s a / π.prob t s a * episodeWeightFrom π ν n (t + 1) s' tail

/-- Whole-trajectory importance weight; transition factors do not enter it. -/
@[expose] def episodeWeight (π ν : MarkovPolicy S A) (H : ℕ) :
    S × EpisodeTail S A H → ℝ := fun (s, tail) => episodeWeightFrom π ν H 0 s tail

/-- Products of nonnegative action ratios are nonnegative. -/
theorem episodeWeightFrom_nonneg (π ν : MarkovPolicy S A) (n t : ℕ) (s : S)
    (z : EpisodeTail S A n) : 0 ≤ episodeWeightFrom π ν n t s z := by
  induction n generalizing t s with
  | zero => exact zero_le_one
  | succ n ih =>
    obtain ⟨a, s', tail⟩ := z
    exact mul_nonneg (div_nonneg (ν.nonneg t s a) (π.nonneg t s a)) (ih _ _ tail)

/-- A positive-probability action and transition from a reached state give a
reached next state. This propagates overlap only where the paper assumes it. -/
theorem stateLaw_pos_next (π : MarkovPolicy S A) {t : ℕ} {s s' : S} {a : A}
    (hs : 0 < M.stateLaw π t s) (ha : 0 < π.prob t s a)
    (htrans : 0 < M.transition t s a s') : 0 < M.stateLaw π (t + 1) s' := by
  have hpos := mul_pos (mul_pos hs ha) htrans
  apply hpos.trans_le
  change _ ≤ ∑ x, ∑ b, M.stateLaw π t x * π.prob t x b * M.transition t x b s'
  exact (single_le_sum (fun b _ => mul_nonneg
    (mul_nonneg (M.stateLaw_nonneg π t s) (π.nonneg t s b)) (M.transition_nonneg t s b s'))
      (mem_univ a)).trans
    (single_le_sum (fun x _ => sum_nonneg fun b _ => mul_nonneg
      (mul_nonneg (M.stateLaw_nonneg π t x) (π.nonneg t x b)) (M.transition_nonneg t x b s'))
        (mem_univ s))

/-- The transition factors cancel along every possible trajectory. The overlap
premise is restricted to behavior-supported states, as in Assumption 1. -/
theorem episodeMassFrom_mul_weight (π ν : MarkovPolicy S A) {H : ℕ}
    (hoverlap : ∀ t < H, ∀ s, 0 < M.stateLaw π t s →
      ∀ a, π.prob t s a = 0 → ν.prob t s a = 0)
    (n t : ℕ) (s : S) (hs : 0 < M.stateLaw π t s) (ht : n + t ≤ H)
    (z : EpisodeTail S A n) :
    M.episodeMassFrom π n t s z * episodeWeightFrom π ν n t s z =
      M.episodeMassFrom ν n t s z := by
  induction n generalizing t s with
  | zero => simp [episodeMassFrom, episodeWeightFrom]
  | succ n ih =>
    obtain ⟨a, s', tail⟩ := z
    by_cases hb : π.prob t s a = 0
    · have hq := hoverlap t (by omega) s hs a hb
      simp [episodeMassFrom, episodeWeightFrom, hb, hq]
    by_cases htr : M.transition t s a s' = 0
    · simp [episodeMassFrom, episodeWeightFrom, htr]
    have hs' := M.stateLaw_pos_next π hs
      (lt_of_le_of_ne (π.nonneg t s a) (Ne.symm hb))
      (lt_of_le_of_ne (M.transition_nonneg t s a s') (Ne.symm htr))
    have htail := ih (t + 1) s' hs' (by omega) tail
    simp only [episodeMassFrom, episodeWeightFrom]
    calc π.prob t s a * M.transition t s a s' * M.episodeMassFrom π n (t + 1) s' tail *
        (ν.prob t s a / π.prob t s a * episodeWeightFrom π ν n (t + 1) s' tail) =
        ν.prob t s a * M.transition t s a s' *
          (M.episodeMassFrom π n (t + 1) s' tail *
            episodeWeightFrom π ν n (t + 1) s' tail) := by field_simp
      _ = _ := by rw [htail]

/-- The actual whole-trajectory target law has the logged ratio as its density
relative to the behavior trajectory law. -/
theorem episodeLaw_change [MeasurableSpace S] [MeasurableSingletonClass S]
    (π ν : MarkovPolicy S A) {H : ℕ}
    (hoverlap : ∀ t < H, ∀ s, 0 < M.stateLaw π t s →
      ∀ a, π.prob t s a = 0 → ν.prob t s a = 0) :
    (M.episodeLaw π H).toMeasure.withDensity
      (fun z => ENNReal.ofReal (episodeWeight π ν H z)) = (M.episodeLaw ν H).toMeasure := by
  apply Measure.ext_of_singleton
  intro ⟨s, tail⟩
  rw [withDensity_apply _ (measurableSet_singleton _), lintegral_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  change ENNReal.ofReal (episodeWeightFrom π ν H 0 s tail) *
    ENNReal.ofReal (M.initial s * M.episodeMassFrom π H 0 s tail) =
      ENNReal.ofReal (M.initial s * M.episodeMassFrom ν H 0 s tail)
  rw [← ENNReal.ofReal_mul (episodeWeightFrom_nonneg π ν H 0 s tail)]
  congr 1
  by_cases hs : M.initial s = 0
  · simp [hs]
  have hstate : 0 < M.stateLaw π 0 s := lt_of_le_of_ne (M.initial_nonneg s) (Ne.symm hs)
  have heq := M.episodeMassFrom_mul_weight π ν hoverlap H 0 s hstate (by omega) tail
  calc episodeWeightFrom π ν H 0 s tail * (M.initial s * M.episodeMassFrom π H 0 s tail) =
      M.initial s * (M.episodeMassFrom π H 0 s tail * episodeWeightFrom π ν H 0 s tail) := by ring
    _ = _ := by rw [heq]

/-- Conditional chi-squared divergence at a reached state, in real form.
Overlap is required when interpreting zero denominator terms. -/
@[expose] def stepChi (π ν : MarkovPolicy S A) (t : ℕ) (s : S) : ℝ :=
  ∑ a, (ν.prob t s a - π.prob t s a) ^ 2 / π.prob t s a

/-- Conditional Pearson discrepancies are nonnegative. -/
theorem stepChi_nonneg (π ν : MarkovPolicy S A) (t : ℕ) (s : S) :
    0 ≤ stepChi π ν t s := sum_nonneg fun a _ => div_nonneg (sq_nonneg _) (π.nonneg t s a)

private def reachedStates (π : MarkovPolicy S A) (t : ℕ) : Finset S :=
  univ.filter fun s => 0 < M.stateLaw π t s

private theorem reachedStates_nonempty (π : MarkovPolicy S A) (t : ℕ) :
    (M.reachedStates π t).Nonempty := by
  classical
  by_contra hn
  have hz (s : S) : M.stateLaw π t s = 0 := by
    have hh : ¬ 0 < M.stateLaw π t s := by
      intro h
      exact hn ⟨s, mem_filter.mpr ⟨mem_univ _, h⟩⟩
    exact le_antisymm (not_lt.mp hh) (M.stateLaw_nonneg π t s)
  have hsum := M.stateLaw_sum π t
  simp only [hz, sum_const_zero, zero_ne_one] at hsum

/-- Maximum conditional divergence over behavior-supported states only. -/
def maxStepChi (π ν : MarkovPolicy S A) (t : ℕ) : ℝ :=
  (M.reachedStates π t).sup' (M.reachedStates_nonempty π t) (stepChi π ν t)

/-- The supported maximum bounds every reached state's conditional divergence. -/
theorem stepChi_le_maxStepChi (π ν : MarkovPolicy S A) (t : ℕ) (s : S)
    (hs : 0 < M.stateLaw π t s) : stepChi π ν t s ≤ M.maxStepChi π ν t := by
  classical
  have hs' : s ∈ M.reachedStates π t := mem_filter.mpr ⟨mem_univ _, hs⟩
  exact le_sup' (stepChi π ν t) hs'

/-- The supported maximum is nonnegative. -/
theorem maxStepChi_nonneg (π ν : MarkovPolicy S A) (t : ℕ) : 0 ≤ M.maxStepChi π ν t := by
  obtain ⟨s, hs⟩ := M.reachedStates_nonempty π t
  exact (stepChi_nonneg π ν t s).trans (le_sup' _ hs)

/-- The conditional second moment of one importance weight is one plus the
conditional chi-squared divergence. -/
theorem step_weight_secondMoment (π ν : MarkovPolicy S A) (t : ℕ) (s : S)
    (hoverlap : ∀ a, π.prob t s a = 0 → ν.prob t s a = 0) :
    (∑ a, π.prob t s a * (ν.prob t s a / π.prob t s a) ^ 2) = 1 + stepChi π ν t s := by
  have heq (a : A) : π.prob t s a * (ν.prob t s a / π.prob t s a) ^ 2 =
      (ν.prob t s a - π.prob t s a) ^ 2 / π.prob t s a + 2 * ν.prob t s a - π.prob t s a := by
    by_cases hb : π.prob t s a = 0
    · simp [hb, hoverlap a hb]
    · field_simp
      ring
  simp_rw [heq]
  rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ν.sum_prob, π.sum_prob]
  unfold stepChi
  ring

private def momentEnvelope (C : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | n + 1, t => (1 + C t) * momentEnvelope C n (t + 1)

private theorem momentEnvelope_nonneg (C : ℕ → ℝ) (hC : ∀ t, 0 ≤ C t) (n t : ℕ) :
    0 ≤ momentEnvelope C n t := by
  induction n generalizing t with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (by linarith [hC t]) (ih _)

private theorem momentEnvelope_eq_prod (C : ℕ → ℝ) (n t : ℕ) :
    momentEnvelope C n t = ∏ j ∈ range n, (1 + C (t + j)) := by
  induction n generalizing t with
  | zero => simp [momentEnvelope]
  | succ n ih =>
    rw [momentEnvelope, prod_range_succ']
    simp only [ih, Nat.add_zero, Nat.add_comm, Nat.add_left_comm, mul_comm]


private theorem episode_secondMomentFrom_le (π ν : MarkovPolicy S A) {H : ℕ}
    (hoverlap : ∀ t < H, ∀ s, 0 < M.stateLaw π t s →
      ∀ a, π.prob t s a = 0 → ν.prob t s a = 0)
    (n t : ℕ) (s : S) (hs : 0 < M.stateLaw π t s) (ht : n + t ≤ H) :
    (∑ z, M.episodeMassFrom π n t s z * episodeWeightFrom π ν n t s z ^ 2) ≤
      momentEnvelope (M.maxStepChi π ν) n t := by
  induction n generalizing t s with
  | zero => simp [episodeMassFrom, episodeWeightFrom, momentEnvelope]
  | succ n ih =>
    let K := momentEnvelope (M.maxStepChi π ν) n (t + 1)
    have hK : 0 ≤ K := momentEnvelope_nonneg _ (M.maxStepChi_nonneg π ν) n (t + 1)
    have hcoeff (a : A) (s' : S) :
        0 ≤ π.prob t s a * (ν.prob t s a / π.prob t s a) ^ 2 * M.transition t s a s' :=
      mul_nonneg (mul_nonneg (π.nonneg t s a) (sq_nonneg _)) (M.transition_nonneg t s a s')
    have heq : (∑ z, M.episodeMassFrom π (n + 1) t s z *
        episodeWeightFrom π ν (n + 1) t s z ^ 2) =
        ∑ a, ∑ s', π.prob t s a * (ν.prob t s a / π.prob t s a) ^ 2 *
          M.transition t s a s' * (∑ tail, M.episodeMassFrom π n (t + 1) s' tail *
            episodeWeightFrom π ν n (t + 1) s' tail ^ 2) := by
      change (∑ z : A × S × EpisodeTail S A n,
        (π.prob t s z.1 * M.transition t s z.1 z.2.1 *
          M.episodeMassFrom π n (t + 1) z.2.1 z.2.2) *
        (ν.prob t s z.1 / π.prob t s z.1 *
          episodeWeightFrom π ν n (t + 1) z.2.1 z.2.2) ^ 2) = _
      simp only [Fintype.sum_prod_type, mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro s' _
      apply sum_congr rfl
      intro tail _
      ring
    rw [heq]
    calc (∑ a, ∑ s', π.prob t s a * (ν.prob t s a / π.prob t s a) ^ 2 *
        M.transition t s a s' * (∑ tail, M.episodeMassFrom π n (t + 1) s' tail *
          episodeWeightFrom π ν n (t + 1) s' tail ^ 2)) ≤
        ∑ a, ∑ s', π.prob t s a * (ν.prob t s a / π.prob t s a) ^ 2 *
          M.transition t s a s' * K := by
          apply sum_le_sum
          intro a _
          apply sum_le_sum
          intro s' _
          by_cases hb : π.prob t s a = 0
          · simp [hb]
          by_cases htr : M.transition t s a s' = 0
          · simp [htr]
          apply mul_le_mul_of_nonneg_left _ (hcoeff a s')
          exact ih (t + 1) s' (M.stateLaw_pos_next π hs
            (lt_of_le_of_ne (π.nonneg t s a) (Ne.symm hb))
            (lt_of_le_of_ne (M.transition_nonneg t s a s') (Ne.symm htr))) (by omega)
      _ = (1 + stepChi π ν t s) * K := by
          simp only [← sum_mul, ← mul_sum, M.transition_sum, mul_one]
          rw [step_weight_secondMoment π ν t s (hoverlap t (by omega) s hs)]
      _ ≤ momentEnvelope (M.maxStepChi π ν) (n + 1) t :=
          mul_le_mul_of_nonneg_right (by linarith [M.stepChi_le_maxStepChi π ν t s hs]) hK

/-- The second moment of the actual whole-trajectory weight is bounded by the
product of the worst supported conditional divergences. -/
theorem episode_secondMoment_le [MeasurableSpace S] [MeasurableSingletonClass S]
    (π ν : MarkovPolicy S A) {H : ℕ}
    (hoverlap : ∀ t < H, ∀ s, 0 < M.stateLaw π t s →
      ∀ a, π.prob t s a = 0 → ν.prob t s a = 0) :
    (∫ z, episodeWeight π ν H z ^ 2 ∂(M.episodeLaw π H).toMeasure) ≤
      ∏ t ∈ range H, (1 + M.maxStepChi π ν t) := by
  rw [PMF.integral_eq_sum]
  simp only [Fintype.sum_prod_type, episodeLaw_real, episodeWeight, smul_eq_mul, mul_assoc,
    ← mul_sum]
  have heq : ∏ t ∈ range H, (1 + M.maxStepChi π ν t) =
      momentEnvelope (M.maxStepChi π ν) H 0 := by simp [momentEnvelope_eq_prod]
  rw [heq]
  calc (∑ s, M.initial s * ∑ tail,
      M.episodeMassFrom π H 0 s tail * episodeWeightFrom π ν H 0 s tail ^ 2) ≤
      ∑ s, M.initial s * momentEnvelope (M.maxStepChi π ν) H 0 := by
        apply sum_le_sum
        intro s _
        by_cases hs : M.initial s = 0
        · simp [hs]
        apply mul_le_mul_of_nonneg_left _ (M.initial_nonneg s)
        exact M.episode_secondMomentFrom_le π ν hoverlap H 0 s
          (lt_of_le_of_ne (M.initial_nonneg s) (Ne.symm hs)) (by omega)
    _ = _ := by rw [← sum_mul, M.initial_sum, one_mul]

/-- Real squared-weight discrepancy. Under overlap, `episodeLaw_change` identifies
the weight with the true likelihood ratio, so this is trajectory chi-squared divergence.
Without overlap this total real expression does not represent infinite divergence. -/
@[expose] def trajectoryChiSquared [MeasurableSpace S]
    (π ν : MarkovPolicy S A) (H : ℕ) : ℝ :=
  densityChiSquared (M.episodeLaw π H).toMeasure (episodeWeight π ν H)

/-- Theorem 5.5's divergence product bound, including horizon zero and arbitrary
endogenous transition dynamics. Only behavior-supported states enter each maximum. -/
theorem trajectoryChiSquared_product_bound [MeasurableSpace S] [MeasurableSingletonClass S]
    (π ν : MarkovPolicy S A) {H : ℕ}
    (hoverlap : ∀ t < H, ∀ s, 0 < M.stateLaw π t s →
      ∀ a, π.prob t s a = 0 → ν.prob t s a = 0) :
    1 + M.trajectoryChiSquared π ν H ≤ ∏ t ∈ range H, (1 + M.maxStepChi π ν t) := by
  have hW : MemLp (episodeWeight π ν H) 2 (M.episodeLaw π H).toMeasure := MemLp.of_discrete
  have heq := densityChiSquared_eq_integral_sq_sub_one
    (M.episodeLaw π H).toMeasure (M.episodeLaw ν H).toMeasure
    (measurable_of_countable _) hW
    (fun ⟨s, tail⟩ => episodeWeightFrom_nonneg π ν H 0 s tail)
    (M.episodeLaw_change π ν hoverlap)
  change 1 + densityChiSquared (M.episodeLaw π H).toMeasure (episodeWeight π ν H) ≤ _
  rw [heq]
  linarith [M.episode_secondMoment_le π ν hoverlap]

/-- Theorem 5.5's auditor operates on complete independent trajectories and
uses their logged propensity ratios and total observed costs. Its target is the
original policy-minus-open-loop cost under endogenous dynamics. -/
theorem episodic_auditor [MeasurableSpace S] [MeasurableSingletonClass S]
    (π : MarkovPolicy S A) {H : ℕ}
    (hoverlap : ∀ t < H, ∀ s, 0 < M.stateLaw π t s →
      ∀ a, π.prob t s a = 0 → (M.openLoop π).prob t s a = 0)
    (hcost : ∀ t < H, ∀ s a, M.cost t s a ∈ Set.Icc (0 : ℝ) 1)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hsize : 4 * (H ^ 2 * M.trajectoryChiSquared π (M.openLoop π) H) ≤ m * δ ^ 2)
    (hblocks : 8 * Real.log (1 / η) ≤ k) :
    (blockSampleLaw (M.episodeLaw π H).toMeasure m k).real
      {z | δ ≤ |medianOfMeans (importanceScore (M.episodeLoss H)
        (episodeWeight π (M.openLoop π) H)) m k z -
          (M.totalCost π H - M.totalCost (M.openLoop π) H)|} ≤ η := by
  have hW : MemLp (episodeWeight π (M.openLoop π) H) 2
      (M.episodeLaw π H).toMeasure := MemLp.of_discrete
  have hb : ∀ᵐ z ∂(M.episodeLaw π H).toMeasure, |M.episodeLoss H z| ≤ H :=
    ae_of_all _ fun ⟨s, tail⟩ => by
      have h := M.episodeLossFrom_mem_Icc hcost H 0 s tail (by omega)
      change |M.episodeLossFrom H 0 s tail| ≤ (H : ℝ)
      exact abs_le.mpr ⟨by linarith [h.1, (Nat.cast_nonneg H : (0 : ℝ) ≤ H)], h.2⟩
  have h := importanceScore_confidence (M.episodeLaw π H).toMeasure
    (M.episodeLaw (M.openLoop π) H).toMeasure
    (measurable_of_countable (M.episodeLoss H)) (measurable_of_countable _) hW
    (fun ⟨s, tail⟩ => episodeWeightFrom_nonneg π (M.openLoop π) H 0 s tail)
    (M.episodeLaw_change π (M.openLoop π) hoverlap) (Nat.cast_nonneg H) hb
    hδ hη hm hk hsize hblocks
  rwa [M.episodeLoss_integral π H, M.episodeLoss_integral (M.openLoop π) H] at h


/-- Theorem 5.5's unbiasedness and variance statements for the actual trajectory
score, derived from the law and bounded total cost. -/
theorem episodic_auditor_moments [MeasurableSpace S] [MeasurableSingletonClass S]
    (π : MarkovPolicy S A) {H : ℕ}
    (hoverlap : ∀ t < H, ∀ s, 0 < M.stateLaw π t s →
      ∀ a, π.prob t s a = 0 → (M.openLoop π).prob t s a = 0)
    (hcost : ∀ t < H, ∀ s a, M.cost t s a ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z, importanceScore (M.episodeLoss H) (episodeWeight π (M.openLoop π) H) z
      ∂(M.episodeLaw π H).toMeasure) = M.totalCost π H - M.totalCost (M.openLoop π) H ∧
    variance (importanceScore (M.episodeLoss H) (episodeWeight π (M.openLoop π) H))
      (M.episodeLaw π H).toMeasure ≤ H ^ 2 * M.trajectoryChiSquared π (M.openLoop π) H := by
  have hW : MemLp (episodeWeight π (M.openLoop π) H) 2
      (M.episodeLaw π H).toMeasure := MemLp.of_discrete
  have hb : ∀ᵐ z ∂(M.episodeLaw π H).toMeasure, |M.episodeLoss H z| ≤ H :=
    ae_of_all _ fun ⟨s, tail⟩ => by
      have h := M.episodeLossFrom_mem_Icc hcost H 0 s tail (by omega)
      change |M.episodeLossFrom H 0 s tail| ≤ (H : ℝ)
      exact abs_le.mpr ⟨by linarith [h.1, (Nat.cast_nonneg H : (0 : ℝ) ≤ H)], h.2⟩
  constructor
  · have h := importanceScore_integral (M.episodeLaw π H).toMeasure
      (M.episodeLaw (M.openLoop π) H).toMeasure
      (measurable_of_countable (M.episodeLoss H)) (measurable_of_countable _) hW
      (fun ⟨s, tail⟩ => episodeWeightFrom_nonneg π (M.openLoop π) H 0 s tail)
      (M.episodeLaw_change π (M.openLoop π) hoverlap) hb
    rwa [M.episodeLoss_integral π H, M.episodeLoss_integral (M.openLoop π) H] at h
  · exact importanceScore_variance_le _ (measurable_of_countable _) hW (Nat.cast_nonneg H) hb

/-- The exact episode count printed in Theorem 5.5, in the positive-variance
regime. Each observation is a whole episode, not an independent time step. -/
theorem episodic_auditor_ceiling [MeasurableSpace S] [MeasurableSingletonClass S]
    (π : MarkovPolicy S A) {H : ℕ}
    (hoverlap : ∀ t < H, ∀ s, 0 < M.stateLaw π t s →
      ∀ a, π.prob t s a = 0 → (M.openLoop π).prob t s a = 0)
    (hcost : ∀ t < H, ∀ s a, M.cost t s a ∈ Set.Icc (0 : ℝ) 1)
    (hv : 0 < (H : ℝ) ^ 2 * M.trajectoryChiSquared π (M.openLoop π) H)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) (hηone : η < 1) :
    let v := (H : ℝ) ^ 2 * M.trajectoryChiSquared π (M.openLoop π) H
    let m := ⌈4 * v / δ ^ 2⌉₊
    let k := ⌈8 * Real.log (1 / η)⌉₊
    (blockSampleLaw (M.episodeLaw π H).toMeasure m k).real
      {z | δ ≤ |medianOfMeans (importanceScore (M.episodeLoss H)
        (episodeWeight π (M.openLoop π) H)) m k z -
          (M.totalCost π H - M.totalCost (M.openLoop π) H)|} ≤ η := by
  dsimp only
  apply M.episodic_auditor π hoverlap hcost hδ hη
  · exact Nat.one_le_ceil_iff.mpr (div_pos (mul_pos (by norm_num) hv) (sq_pos_of_pos hδ))
  · apply Nat.one_le_ceil_iff.mpr
    have : 1 < 1 / η := (lt_div_iff₀ hη).mpr (by linarith)
    exact mul_pos (by norm_num) (Real.log_pos this)
  · exact (div_le_iff₀ (sq_pos_of_pos hδ)).mp (Nat.le_ceil _)
  · exact Nat.le_ceil _

/-- If the episode variance parameter is zero, outputting zero is exact and
requires no episode. This includes horizon zero and zero trajectory divergence. -/
theorem episodic_gap_eq_zero [MeasurableSpace S] [MeasurableSingletonClass S]
    (π : MarkovPolicy S A) {H : ℕ}
    (hoverlap : ∀ t < H, ∀ s, 0 < M.stateLaw π t s →
      ∀ a, π.prob t s a = 0 → (M.openLoop π).prob t s a = 0)
    (hcost : ∀ t < H, ∀ s a, M.cost t s a ∈ Set.Icc (0 : ℝ) 1)
    (hv : (H : ℝ) ^ 2 * M.trajectoryChiSquared π (M.openLoop π) H = 0) :
    M.totalCost π H - M.totalCost (M.openLoop π) H = 0 := by
  by_cases hH : H = 0
  · simp [hH, totalCost]
  have hHsq : (H : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hH)
  have hχ : M.trajectoryChiSquared π (M.openLoop π) H = 0 := (mul_eq_zero.mp hv).resolve_left hHsq
  have hW : MemLp (episodeWeight π (M.openLoop π) H) 2
      (M.episodeLaw π H).toMeasure := MemLp.of_discrete
  have hb : ∀ᵐ z ∂(M.episodeLaw π H).toMeasure, |M.episodeLoss H z| ≤ H :=
    ae_of_all _ fun ⟨s, tail⟩ => by
      have h := M.episodeLossFrom_mem_Icc hcost H 0 s tail (by omega)
      change |M.episodeLossFrom H 0 s tail| ≤ (H : ℝ)
      exact abs_le.mpr ⟨by linarith [h.1, (Nat.cast_nonneg H : (0 : ℝ) ≤ H)], h.2⟩
  have h := cost_gap_eq_zero_of_densityChiSquared_eq_zero
    (M.episodeLaw π H).toMeasure (M.episodeLaw (M.openLoop π) H).toMeasure
    (measurable_of_countable (M.episodeLoss H)) (measurable_of_countable _) hW
    (fun ⟨s, tail⟩ => episodeWeightFrom_nonneg π (M.openLoop π) H 0 s tail)
    (M.episodeLaw_change π (M.openLoop π) hoverlap) hb hχ
  rwa [M.episodeLoss_integral π H, M.episodeLoss_integral (M.openLoop π) H] at h

/-- One observable round: state/action, observed cost, target propensity and
logged behavior propensity. There is no terminal next state or counterfactual cost. -/
abbrev EpisodeRecord (S A : Type*) := (S × A) × ℝ × ℝ × ℝ

/-- The observed cost coordinate. -/
@[expose] def recordCost : EpisodeRecord S A → ℝ := fun (_, cost, _, _) => cost

/-- Ratio of the known target and logged behavior propensities. -/
@[expose] def recordRatio : EpisodeRecord S A → ℝ :=
  fun (_, _, target, behavior) => target / behavior

/-- Extract exactly the paper's observable episode records, discarding the
redundant terminal state retained in the proof representation. -/
@[expose] def episodeObservationFrom (π ν : MarkovPolicy S A) :
    (n : ℕ) → ℕ → S → EpisodeTail S A n → Fin n → EpisodeRecord S A
  | 0, _, _, _ => Fin.elim0
  | n + 1, t, s, (a, s', tail) =>
      Fin.cases ((s, a), M.cost t s a, ν.prob t s a, π.prob t s a)
        (episodeObservationFrom π ν n (t + 1) s' tail)

/-- Observable complete episode, with no extra access to the terminal state. -/
@[expose] def episodeObservation (π ν : MarkovPolicy S A) (H : ℕ) :
    S × EpisodeTail S A H → Fin H → EpisodeRecord S A :=
  fun (s, tail) => M.episodeObservationFrom π ν H 0 s tail

/-- The importance score computed solely from recorded costs and propensities. -/
@[expose] def episodeObservedScore (H : ℕ) (z : Fin H → EpisodeRecord S A) : ℝ :=
  (∑ t, recordCost (z t)) * (1 - ∏ t, recordRatio (z t))

/-- Recording an episode preserves precisely its total observed cost. -/
theorem sum_recordCost (π ν : MarkovPolicy S A) (n t : ℕ) (s : S) (z : EpisodeTail S A n) :
    (∑ i, recordCost (M.episodeObservationFrom π ν n t s z i)) = M.episodeLossFrom n t s z := by
  induction n generalizing t s with
  | zero => simp [episodeLossFrom]
  | succ n ih =>
    obtain ⟨a, s', tail⟩ := z
    simp only [episodeObservationFrom, Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ,
      episodeLossFrom]
    change M.cost t s a + (∑ i, recordCost
      (M.episodeObservationFrom π ν n (t + 1) s' tail i)) = _
    rw [ih]

/-- Recording an episode preserves precisely its importance weight. -/
theorem prod_recordRatio (π ν : MarkovPolicy S A) (n t : ℕ) (s : S) (z : EpisodeTail S A n) :
    (∏ i, recordRatio (M.episodeObservationFrom π ν n t s z i)) =
      episodeWeightFrom π ν n t s z := by
  induction n generalizing t s with
  | zero => simp [episodeWeightFrom]
  | succ n ih =>
    obtain ⟨a, s', tail⟩ := z
    simp only [episodeObservationFrom, Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ,
      episodeWeightFrom]
    change ν.prob t s a / π.prob t s a * (∏ i, recordRatio
      (M.episodeObservationFrom π ν n (t + 1) s' tail i)) = _
    rw [ih]

/-- The full-path proof score factors through exactly the observable log. -/
theorem episodeObservedScore_comp (π ν : MarkovPolicy S A) (H : ℕ) :
    episodeObservedScore H ∘ M.episodeObservation π ν H =
      importanceScore (M.episodeLoss H) (episodeWeight π ν H) := by
  funext ⟨s, tail⟩
  simp only [Function.comp_apply, episodeObservedScore, episodeObservation,
    M.sum_recordCost, M.prod_recordRatio, importanceScore, episodeLoss, episodeWeight]

/-- Whole-episode likelihood ratio using only observed propensities. -/
@[expose] def episodeObservedWeight (H : ℕ) (z : Fin H → EpisodeRecord S A) : ℝ :=
  ∏ t, recordRatio (z t)

/-- The logged weight is exactly the trajectory likelihood ratio. -/
theorem episodeObservedWeight_comp (π ν : MarkovPolicy S A) (H : ℕ) :
    episodeObservedWeight H ∘ M.episodeObservation π ν H = episodeWeight π ν H := by
  funext ⟨s, tail⟩
  exact M.prod_recordRatio π ν H 0 s tail

/-- The observable target law has the logged weight as its actual density;
dropping the terminal state does not weaken the change-of-measure identity. -/
theorem episodeObservedLaw_change [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace A] (π ν : MarkovPolicy S A) {H : ℕ}
    (hoverlap : ∀ t < H, ∀ s, 0 < M.stateLaw π t s →
      ∀ a, π.prob t s a = 0 → ν.prob t s a = 0) :
    ((M.episodeLaw π H).toMeasure.map (M.episodeObservation π ν H)).withDensity
      (fun z => ENNReal.ofReal (episodeObservedWeight H z)) =
        (M.episodeLaw ν H).toMeasure.map (M.episodeObservation π ν H) := by
  have hg : Measurable (episodeObservedWeight H : (Fin H → EpisodeRecord S A) → ℝ) := by
    unfold episodeObservedWeight recordRatio
    fun_prop
  apply withDensity_map_of_factorization _ _ (measurable_of_countable _) hg
  have heq : (fun x => ENNReal.ofReal (episodeObservedWeight H
      (M.episodeObservation π ν H x))) = fun x => ENNReal.ofReal (episodeWeight π ν H x) :=
    congrArg (fun g => fun x => ENNReal.ofReal (g x)) (M.episodeObservedWeight_comp π ν H)
  rw [heq]
  exact M.episodeLaw_change π ν hoverlap

/-- The observable squared-weight discrepancy equals the proof representation's
value. Under overlap both are actual chi-squared divergences, so the extra
terminal transition contributes no divergence. -/
theorem episodeObservedChiSquared_eq [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace A] (π ν : MarkovPolicy S A) (H : ℕ) :
    densityChiSquared ((M.episodeLaw π H).toMeasure.map (M.episodeObservation π ν H))
      (episodeObservedWeight H) = M.trajectoryChiSquared π ν H := by
  have hg : Measurable (fun z : Fin H → EpisodeRecord S A =>
      (1 - episodeObservedWeight H z) ^ 2) := by
    unfold episodeObservedWeight recordRatio
    fun_prop
  unfold densityChiSquared trajectoryChiSquared
  rw [integral_map (measurable_of_countable _).aemeasurable hg.aestronglyMeasurable]
  have heq := congrFun (M.episodeObservedWeight_comp π ν H)
  congr 1
  ext z
  rw [show episodeObservedWeight H (M.episodeObservation π ν H z) =
    episodeWeight π ν H z from heq z]

/-- Theorem 5.5 on the exact observable-record experiment. Its episode score
uses no terminal state, transitions or unobserved counterfactual losses. -/
theorem episodic_observed_auditor [MeasurableSpace S] [MeasurableSingletonClass S]
    [MeasurableSpace A] (π : MarkovPolicy S A) {H : ℕ}
    (hoverlap : ∀ t < H, ∀ s, 0 < M.stateLaw π t s →
      ∀ a, π.prob t s a = 0 → (M.openLoop π).prob t s a = 0)
    (hcost : ∀ t < H, ∀ s a, M.cost t s a ∈ Set.Icc (0 : ℝ) 1)
    {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η) {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hsize : 4 * (H ^ 2 * M.trajectoryChiSquared π (M.openLoop π) H) ≤ m * δ ^ 2)
    (hblocks : 8 * Real.log (1 / η) ≤ k) :
    (blockSampleLaw ((M.episodeLaw π H).toMeasure.map
      (M.episodeObservation π (M.openLoop π) H)) m k).real
      {z | δ ≤ |medianOfMeans (episodeObservedScore H) m k z -
        (M.totalCost π H - M.totalCost (M.openLoop π) H)|} ≤ η := by
  have hg : Measurable (episodeObservedScore H : (Fin H → EpisodeRecord S A) → ℝ) := by
    unfold episodeObservedScore recordCost recordRatio
    fun_prop
  rw [medianOfMeans_observation_failure _ (measurable_of_countable _) hg m k,
    M.episodeObservedScore_comp]
  exact M.episodic_auditor π hoverlap hcost hδ hη hm hk hsize hblocks

end FiniteMDP
end Cslib.Probability.AdaptivePolicy
