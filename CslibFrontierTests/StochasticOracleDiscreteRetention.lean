/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.DiscreteCost
import CslibFrontierTests.StochasticOracleAdaptiveSelection
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Actual retention from unbounded geometric responses

Response zero proposes the positive-cost singleton cover; all positive responses
propose nothing. The geometric source has unbounded positive-probability support,
so the response alphabet cannot be given a `Fintype` instance. The local dual test,
retention, productive-event probability and completion bound are checked together.
-/

noncomputable section
namespace CslibFrontierTests.DiscreteRetention
open Cslib.Probability Cslib.Probability.StochasticOracle
open AdaptiveSelection PartialCover MeasureTheory
open StochasticOracleAdaptiveSelectionTests (toy)
open scoped ENNReal

private def half : Set.Icc (0 : ℝ) 1 := ⟨1 / 2, by norm_num⟩
private def law (_ : List ℕ) : PMF ℕ := (ProbabilityTheory.geometricMeasure half).toPMF
private def proposals (_ : List ℕ) (x : ℕ) : List (Finset Unit) :=
  if x = 0 then [{()}] else []

private theorem selected_eq (h : List ℕ) :
    selected toy 1 proposals h = if 0 ∈ h then {()} else ∅ := by
  induction h with
  | nil => simp [selected]
  | cons x h ih =>
    rw [selected, ih]
    by_cases hx : x = 0 <;> by_cases hh : 0 ∈ h <;>
      simp [proposals, hx, hh, eq_comm, Instance.retain, Instance.Certified,
        Instance.covered, Instance.cost, toy]

private theorem productive_eq (h : List ℕ) (x : ℕ) :
    productive toy 1 proposals 1 h x = decide (0 ∈ h ∨ x = 0) := by
  simp only [productive, AdaptiveSelection.residual, selected_eq]
  by_cases hx : x = 0 <;> by_cases hh : 0 ∈ h <;>
    simp [hx, hh, eq_comm, Instance.covered, toy]

private theorem law_pos (n : ℕ) : 0 < law [] n := by
  rw [law, Measure.toPMF_apply, ProbabilityTheory.geometricMeasure_singleton
    (by intro h; have he := congrArg (fun p : Set.Icc (0 : ℝ) 1 => (p : ℝ)) h
        norm_num [half] at he)]
  apply ENNReal.ofReal_pos.mpr
  simp only [half, Subtype.coe_mk]
  positivity

example (N : ℕ) : ∃ x ∈ (law []).support, N < x :=
  ⟨N + 1, ne_of_gt (law_pos _), Nat.lt_succ_self N⟩

private theorem envelope (h : List ℕ)
    (hc : toy.covered (selected toy 1 proposals h) ≠ toy.ground) :
    (half : ℝ) ≤ ((law h).toOuterMeasure
      {x | productive toy 1 proposals 1 h x = true}).toReal := by
  have hn : 0 ∉ h := by
    intro hh
    apply hc
    rw [selected_eq, ite_eq_left hh]
    simp [Instance.covered, toy]
  have he : {x | productive toy 1 proposals 1 h x = true} = {0} := by
    ext x
    simp [productive_eq, hn]
  rw [he, PMF.toOuterMeasure_apply_singleton, law, Measure.toPMF_apply,
    ProbabilityTheory.geometricMeasure_singleton
      (by intro h; have he := congrArg (fun p : Set.Icc (0 : ℝ) 1 => (p : ℝ)) h
          norm_num [half] at he)]
  norm_num [half]

-- The source endpoint applies at every horizon despite the unbounded response law.
example (n : ℕ) :
    1 - (ProbabilityTheory.binomial n half).real (Set.Iio 1) ≤
      ((PMF.seqProcess (responseStep law) n).toOuterMeasure
        {h | toy.covered (selected toy 1 proposals (PMF.seqHistory h)) = toy.ground}).toReal := by
  apply binomial_le_completion_discrete toy 1 proposals law 1 1 n (by norm_num [toy]) half
  intro t ht h hh hc
  exact envelope _ hc

-- The output certificate still uses the actual retained family, including repeats.
example (h : List ℕ) :
    toy.cost (selected toy 1 proposals h) ≤
      ∑ e ∈ toy.covered (selected toy 1 proposals h), toy.dual e := by
  simpa only [one_mul] using selected_bound toy 1 proposals h

private def charge (_ : List ℕ) (x : ℕ) : ℝ := x + 1

private theorem charge_mean (h : List ℕ) :
    (∑' x, law h x * ENNReal.ofReal (charge h x)) = 2 := by
  have hs1 : HasSum (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) 2 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num) using 1
    norm_num
  have hs0 : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := by
    convert hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) using 1
    norm_num
  have hs : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n * (1 / 2) * (n + 1)) 2 := by
    convert (hs1.add hs0).mul_right (1 / 2) using 1
    · funext n
      ring
    · norm_num
  have hm (n : ℕ) : law h n = ENNReal.ofReal ((1 / 2 : ℝ) ^ n * (1 / 2)) := by
    rw [law, Measure.toPMF_apply, ProbabilityTheory.geometricMeasure_singleton
      (by intro h; have he := congrArg (fun p : Set.Icc (0 : ℝ) 1 => (p : ℝ)) h
          norm_num [half] at he)]
    norm_num [half]
  simp_rw [hm, charge, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / 2 : ℝ) ^ _ * (1 / 2))]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hs.summable, hs.tsum_eq]
  norm_num

-- Realized invoices are unbounded and correlated with the productive response:
-- success costs one; every failure costs at least two. Their conditional mean is two.
example (N : ℕ) : ∃ x ∈ (law []).support, (N : ℝ) < charge [] x := by
  refine ⟨N + 1, ne_of_gt (law_pos _), ?_⟩
  simp only [charge, Nat.cast_add, Nat.cast_one]
  linarith

example (n : ℕ) :
    (∑' h, PMF.seqProcess (responseStep law) n h *
      ENNReal.ofReal (accruedBill (stoppedBill toy 1 proposals charge) (PMF.seqHistory h))) ≤
      ENNReal.ofReal (2 * ∑ t ∈ Finset.range n,
        (ProbabilityTheory.binomial t half).real (Set.Iio 1)) := by
  apply accruedBill_le_binomial_sum_discrete toy 1 proposals law 1 1 n
    (by norm_num [toy]) half
  · intro t ht h hh hc
    exact envelope _ hc
  · intro h x
    dsimp [charge]
    positivity
  · norm_num
  · intro t ht h hh hc
    simpa using (charge_mean (PMF.seqHistory h)).le

-- The same actual execution satisfies both finite-budget and waiting-time bounds.
example (n : ℕ) :
    (∑' h, PMF.seqProcess (responseStep law) n h *
      ENNReal.ofReal (accruedBill (stoppedBill toy 1 proposals charge) (PMF.seqHistory h))) ≤
      ENNReal.ofReal (2 * min (n : ℝ) 2) := by
  have hb := accruedBill_le_mean_discrete toy 1 proposals law 1 1 n
    (by norm_num [toy]) half (by norm_num [half])
    (fun _ _ _ _ hc => envelope _ hc) charge (fun _ _ => by dsimp [charge]; positivity)
    2 (by norm_num) (fun _ _ h _ _ => by simpa using (charge_mean (PMF.seqHistory h)).le)
  simpa [half] using hb

end CslibFrontierTests.DiscreteRetention
