/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Probability.HypothesisSelection.LeCamBirge
import CslibFrontier.Probability.HypothesisSelection.Likelihood
import CslibFrontier.Probability.HypothesisSelection.Tournament
import Mathlib.Data.Fin.VecNotation

/-!
Nonvacuous unit and contrast tests for finite-family hypothesis selection:
likelihood-ratio Chernoff bounds, finite-family MLE, zero-likelihood misspecified MLE failure vs.
pairwise Scheffé / Le Cam–Birgé tests, Scheffé TV and Le Cam–Birgé Hellinger tournament
robustness, sample complexity bounds, and finite cover bounds.
-/

namespace CslibFrontierTests.HypothesisSelection

open Cslib.Probability.PMF Cslib.Probability.HypothesisSelection
open scoped BigOperators ENNReal

private noncomputable def coin (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : _root_.PMF Bool :=
  ⟨fun b => if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p), by
    convert hasSum_fintype _ using 1
    rw [Fintype.sum_bool]
    simp [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]⟩

private noncomputable def coinOneFifth : _root_.PMF Bool :=
  coin (1 / 5) (by norm_num) (by norm_num)

private noncomputable def coinHalf : _root_.PMF Bool :=
  coin (1 / 2) (by norm_num) (by norm_num)

private noncomputable def coinFourFifths : _root_.PMF Bool :=
  coin (4 / 5) (by norm_num) (by norm_num)

private noncomputable def coinOutlier : _root_.PMF Bool :=
  coin (99 / 100) (by norm_num) (by norm_num)

private noncomputable def coinNearOneFifth : _root_.PMF Bool :=
  coin (201 / 1000) (by norm_num) (by norm_num)

private noncomputable def coinDet : _root_.PMF Bool :=
  _root_.PMF.pure true

private theorem coin_apply (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    coin p hp0 hp1 b = if b then ENNReal.ofReal p else ENNReal.ofReal (1 - p) :=
  rfl

private theorem coin_apply_true {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coin p hp0 hp1 true).toReal = p := by
  rw [coin_apply]
  simp [hp0]

private theorem coin_apply_false {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (coin p hp0 hp1 false).toReal = 1 - p := by
  rw [coin_apply]
  simp [sub_nonneg.mpr hp1]

private theorem coin_apply_ne_zero {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (b : Bool) :
    coin p hp0.le hp1.le b ≠ 0 := by
  rw [coin_apply]
  cases b <;> simp [hp0, hp1]

private theorem bhattacharyya_oneFifth_fourFifths :
    bhattacharyya coinOneFifth coinFourFifths = 4 / 5 := by
  rw [bhattacharyya_eq_sum, Fintype.sum_bool]
  simp only [coinOneFifth, coinFourFifths, coin_apply_true, coin_apply_false]
  rw [show (1 / 5 : ℝ) * (4 / 5) = (2 / 5) ^ 2 by norm_num,
    show (1 - 1 / 5 : ℝ) * (1 - 4 / 5) = (2 / 5) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

private theorem hellingerSq_oneFifth_fourFifths :
    hellingerSq coinOneFifth coinFourFifths = 1 / 5 := by
  rw [hellingerSq_eq_one_sub_bhattacharyya, bhattacharyya_oneFifth_fourFifths]
  norm_num

private theorem dist_oneFifth_fourFifths :
    dist coinOneFifth coinFourFifths = 3 / 5 := by
  rw [Cslib.Probability.PMF.dist_eq_sum_filter_lt, Finset.sum_filter, Fintype.sum_bool]
  simp only [coinOneFifth, coinFourFifths, coin_apply_true, coin_apply_false]
  norm_num

private theorem log_le_four_of_le_35 {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 35) :
    Real.log x ≤ 4 := by
  have h1 : (5 / 4 : ℝ) < Real.exp (1 / 4) := by
    linarith [Real.add_one_lt_exp (by norm_num : (1 / 4 : ℝ) ≠ 0)]
  have h16 : (5 / 4 : ℝ) ^ 16 < Real.exp (1 / 4) ^ 16 :=
    pow_lt_pow_left₀ h1 (by norm_num) (by positivity)
  rw [← Real.exp_nat_mul, show ((16 : ℕ) : ℝ) * (1 / 4 : ℝ) = 4 by norm_num] at h16
  have hexp4 : x < Real.exp 4 :=
    (hx.trans_lt (by norm_num : (35 : ℝ) < (5 / 4 : ℝ) ^ 16)).trans h16
  exact ((Real.log_lt_iff_lt_exp hx0).mpr hexp4).le

/-! ### Milestone 1: Likelihood-ratio Chernoff and MLE tests -/

private theorem chernoff_oneFifth_fourFifths_20 :
    ((iid coinOneFifth 20).toOuterMeasure
      {x | iid coinOneFifth 20 x ≤ iid coinFourFifths 20 x}).toReal ≤ (4 / 5 : ℝ) ^ 20 := by
  simpa only [bhattacharyya_oneFifth_fourFifths] using
    toOuterMeasure_iid_le_bhattacharyya_pow coinOneFifth coinFourFifths 20

private theorem chernoff_oneFifth_fourFifths_exp_20 :
    ((iid coinOneFifth 20).toOuterMeasure
      {x | iid coinOneFifth 20 x ≤ iid coinFourFifths 20 x}).toReal ≤ Real.exp (-4) := by
  have h := toOuterMeasure_iid_le_exp_hellingerDist coinOneFifth coinFourFifths 20
  rw [hellingerDist_sq, hellingerSq_oneFifth_fourFifths] at h
  calc _ ≤ _ := h
    _ = Real.exp (-4) := by congr 1; norm_num

private noncomputable def threeCoins : Fin 3 → _root_.PMF Bool :=
  ![coinOneFifth, coinHalf, coinFourFifths]

private theorem mle_threeCoins_hellinger :
    ((iid (threeCoins 0) 100).toOuterMeasure
      {x | (1 / 4 : ℝ) < hellingerDist (threeCoins 0) (threeCoins (mleFin threeCoins x))}).toReal
      ≤ 2 * Real.exp (-25 / 4) := by
  have h := mleFin_hellingerDist_gt_le threeCoins 0 100 (r := 1 / 4) (by norm_num)
  calc _ ≤ _ := h
    _ = 2 * Real.exp (-25 / 4) := by norm_num

private theorem mle_threeCoins_sample_complexity :
    ((iid (threeCoins 0) 64).toOuterMeasure
      {x | (1 / 4 : ℝ) ≤ hellingerDist (threeCoins 0) (threeCoins (mleFin threeCoins x))}).toReal
      ≤ 1 / 10 := by
  refine mleFin_hellingerDist_ge_le_of_log threeCoins 0 (r := 1 / 4) (δ := 1 / 10)
    (by norm_num) (by norm_num) ?_
  have hlog : Real.log ((3 : ℝ) / (1 / 10)) ≤ 4 := log_le_four_of_le_35 (by norm_num) (by norm_num)
  have hdiv : Real.log ((3 : ℝ) / (1 / 10)) / (1 / 4 : ℝ) ^ 2 ≤ 4 / (1 / 4 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hlog (by norm_num)
  linarith

/-! ### Milestone 2: Pairwise robust tests and misspecified MLE failure vs. tournaments -/

private theorem scheffeTest_oneFifth_fourFifths :
    ((iid coinOneFifth 50).toOuterMeasure
      {x | scheffeTest coinOneFifth coinFourFifths x = false}).toReal ≤ Real.exp (-9) ∧
    ((iid coinFourFifths 50).toOuterMeasure
      {x | scheffeTest coinOneFifth coinFourFifths x = true}).toReal ≤ Real.exp (-9) := by
  constructor
  · have h := scheffeTest_false_le (p := coinOneFifth) (q₀ := coinOneFifth) (q₁ := coinFourFifths)
      (γ := 3 / 10) (by norm_num)
      (by rw [dist_self, zero_add, dist_oneFifth_fourFifths]; norm_num) 50
    calc _ ≤ _ := h
      _ = Real.exp (-9) := by congr 1; norm_num
  · have h := scheffeTest_true_le (p := coinFourFifths) (q₀ := coinOneFifth) (q₁ := coinFourFifths)
      (γ := 3 / 10) (by norm_num)
      (by rw [dist_self, zero_add, dist_oneFifth_fourFifths]; norm_num) 50
    calc _ ≤ _ := h
      _ = Real.exp (-9) := by congr 1; norm_num

private theorem leCamBirgeTest_oneFifth_fourFifths :
    ((iid coinOneFifth 625).toOuterMeasure
      {x | leCamBirgeTest coinOneFifth coinFourFifths x = false}).toReal ≤ Real.exp (-4) ∧
    ((iid coinFourFifths 625).toOuterMeasure
      {x | leCamBirgeTest coinOneFifth coinFourFifths x = true}).toReal ≤ Real.exp (-4) := by
  have hsep : 10 * (1 / 25 : ℝ) ≤ hellingerDist coinOneFifth coinFourFifths := by
    refine le_of_sq_le_sq ?_ (hellingerDist_nonneg _ _)
    rw [hellingerDist_sq, hellingerSq_oneFifth_fourFifths]
    norm_num
  constructor
  · have h := leCamBirgeTest_false_le_of_radius (p := coinOneFifth) (q₀ := coinOneFifth)
      (q₁ := coinFourFifths) (r := 1 / 25) (by norm_num)
      (by rw [hellingerDist_self]; norm_num) hsep 625
    calc _ ≤ _ := h
      _ = Real.exp (-4) := by congr 1; norm_num
  · have h := leCamBirgeTest_true_le_of_radius (p := coinFourFifths) (q₀ := coinOneFifth)
      (q₁ := coinFourFifths) (r := 1 / 25) (by norm_num)
      (by rw [hellingerDist_self]; norm_num) hsep 625
    calc _ ≤ _ := h
      _ = Real.exp (-4) := by congr 1; norm_num

private noncomputable def twoCoinsDetHalf : Fin 2 → _root_.PMF Bool :=
  ![coinDet, coinHalf]

private def sampleNineTrueOneFalse : Fin 10 → Bool :=
  fun i => decide (i.val < 9)

private theorem dist_coinOutlier_coinDet : dist coinOutlier coinDet = 1 / 100 := by
  rw [Cslib.Probability.PMF.dist_eq_sum_filter_lt]
  have h0 : (coinDet true).toReal = 1 := by simp [coinDet]
  have h1 : (coinDet false).toReal = 0 := by simp [coinDet]
  have hp0 : (coinOutlier true).toReal = 99 / 100 := by
    simp [coinOutlier, coin_apply_true]
  have hp1 : (coinOutlier false).toReal = 1 / 100 := by
    simp only [coinOutlier, coin_apply_false]
    norm_num
  rw [Finset.sum_filter, Fintype.sum_bool]
  simp only [h0, h1, hp0, hp1]
  norm_num

private theorem mle_fails_on_single_outlier :
    mleFin twoCoinsDetHalf sampleNineTrueOneFalse = 1 := by
  have hle := le_iid_mle (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty
    twoCoinsDetHalf (n := 10) (x := sampleNineTrueOneFalse) (Finset.mem_univ 1)
  have h0 : iid coinDet 10 sampleNineTrueOneFalse = 0 := by
    rw [iid_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ ⟨9, by decide⟩) ?_
    simp [coinDet, sampleNineTrueOneFalse]
  have h1 : iid coinHalf 10 sampleNineTrueOneFalse ≠ 0 := by
    rw [iid_apply]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      coin_apply_ne_zero (p := 1 / 2) (by norm_num) (by norm_num) (sampleNineTrueOneFalse i)
  change iid (twoCoinsDetHalf 1) 10 sampleNineTrueOneFalse ≤
      iid (twoCoinsDetHalf (mleFin twoCoinsDetHalf sampleNineTrueOneFalse)) 10
        sampleNineTrueOneFalse at hle
  by_cases hmle : mleFin twoCoinsDetHalf sampleNineTrueOneFalse = 0
  · exfalso
    have heq0 : twoCoinsDetHalf 0 = coinDet := rfl
    have heq1 : twoCoinsDetHalf 1 = coinHalf := rfl
    rw [hmle, heq0, heq1, h0, le_zero_iff] at hle
    exact h1 hle
  · refine Fin.ext ?_
    have hlt := (mleFin twoCoinsDetHalf sampleNineTrueOneFalse).isLt
    have hne0 : (mleFin twoCoinsDetHalf sampleNineTrueOneFalse).val ≠ 0 :=
      fun hv => hmle (Fin.ext hv)
    omega

private theorem scheffeSet_det_half : scheffeSet coinDet coinHalf = {true} := by
  ext b
  cases b <;> simp [scheffeSet, coinDet, coinHalf, coin_apply_true, coin_apply_false] <;> norm_num

private theorem scheffeSet_half_det : scheffeSet coinHalf coinDet = {false} := by
  ext b
  cases b <;> simp [scheffeSet, coinDet, coinHalf, coin_apply_true, coin_apply_false] <;> norm_num

private theorem scheffe_succeeds_on_outlier :
    scheffeSelectFin twoCoinsDetHalf sampleNineTrueOneFalse = 0 := by
  let s : Finset (Fin 2) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  have hle : scheffeScore s hs twoCoinsDetHalf sampleNineTrueOneFalse
      (scheffeSelectFin twoCoinsDetHalf sampleNineTrueOneFalse) ≤
      scheffeScore s hs twoCoinsDetHalf sampleNineTrueOneFalse 0 :=
    (Classical.choose_spec (s.exists_min_image
      (scheffeScore s hs twoCoinsDetHalf sampleNineTrueOneFalse) hs)).2 0 (Finset.mem_univ 0)
  have hscore0 : scheffeScore s hs twoCoinsDetHalf sampleNineTrueOneFalse 0 ≤ 1 / 10 := by
    refine Finset.sup'_le hs _ fun j _ => ?_
    by_cases hj : j = 0
    · subst hj
      change |empiricalMass (scheffeSet coinDet coinDet) sampleNineTrueOneFalse -
        (coinDet.toOuterMeasure (scheffeSet coinDet coinDet : Set Bool)).toReal| ≤ 1 / 10
      simp [scheffeSet_self, empiricalMass]
    · have hj1 : j = 1 := by
        refine Fin.ext ?_
        have hlt := j.isLt
        have hne : j.val ≠ 0 := fun hv => hj (Fin.ext hv)
        omega
      subst hj1
      have hfalse : empiricalMass ({false} : Finset Bool) sampleNineTrueOneFalse = 1 / 10 := by
        let last : Fin 10 := ⟨9, by decide⟩
        rw [empiricalMass, ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ last)]
        have hrest : ∑ j ∈ Finset.univ.erase last,
            (if sampleNineTrueOneFalse j ∈ ({false} : Finset Bool) then (1 : ℝ) else 0) = 0 :=
          Finset.sum_eq_zero fun j hj => by
            have hne : j.val ≠ 9 := fun hv => (Finset.mem_erase.mp hj).1 (Fin.ext hv)
            have hlt : j.val < 9 := by omega
            simp [sampleNineTrueOneFalse, hlt]
        have hlast : (if sampleNineTrueOneFalse last ∈ ({false} : Finset Bool)
            then (1 : ℝ) else 0) = 1 := by
          simp [sampleNineTrueOneFalse, last]
        rw [hrest, hlast]
        norm_num
      change |empiricalMass (scheffeSet coinHalf coinDet) sampleNineTrueOneFalse -
        (coinDet.toOuterMeasure (scheffeSet coinHalf coinDet : Set Bool)).toReal| ≤ 1 / 10
      rw [scheffeSet_half_det, hfalse, toOuterMeasure_apply_toReal]
      simp [coinDet]
  have hscore1 : 4 / 10 ≤ scheffeScore s hs twoCoinsDetHalf sampleNineTrueOneFalse 1 := by
    have hterm := Finset.le_sup' (fun j =>
      |empiricalMass (scheffeSet (twoCoinsDetHalf j) (twoCoinsDetHalf 1)) sampleNineTrueOneFalse -
        ((twoCoinsDetHalf 1).toOuterMeasure
          (scheffeSet (twoCoinsDetHalf j) (twoCoinsDetHalf 1) : Set Bool)).toReal|)
      (Finset.mem_univ 0)
    change |empiricalMass (scheffeSet (twoCoinsDetHalf 0) (twoCoinsDetHalf 1))
        sampleNineTrueOneFalse - ((twoCoinsDetHalf 1).toOuterMeasure
          (scheffeSet (twoCoinsDetHalf 0) (twoCoinsDetHalf 1) : Set Bool)).toReal| ≤
      scheffeScore s hs twoCoinsDetHalf sampleNineTrueOneFalse 1 at hterm
    have htrue : empiricalMass ({true} : Finset Bool) sampleNineTrueOneFalse = 9 / 10 := by
      let last : Fin 10 := ⟨9, by decide⟩
      rw [empiricalMass, ← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ last)]
      have hrest : ∑ j ∈ Finset.univ.erase last,
          (if sampleNineTrueOneFalse j ∈ ({true} : Finset Bool) then (1 : ℝ) else 0) = 9 := by
        have hcongr : ∑ j ∈ Finset.univ.erase last,
            (if sampleNineTrueOneFalse j ∈ ({true} : Finset Bool) then (1 : ℝ) else 0) =
            ∑ _j ∈ Finset.univ.erase last, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hne : j.val ≠ 9 := fun hv => (Finset.mem_erase.mp hj).1 (Fin.ext hv)
          have hlt : j.val < 9 := by omega
          simp [sampleNineTrueOneFalse, hlt]
        rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ last),
          Finset.card_univ, Fintype.card_fin]
        norm_num
      have hlast : (if sampleNineTrueOneFalse last ∈ ({true} : Finset Bool)
          then (1 : ℝ) else 0) = 0 := by
        simp [sampleNineTrueOneFalse, last]
      rw [hrest, hlast]
      norm_num
    have hdet : scheffeSet (twoCoinsDetHalf 0) (twoCoinsDetHalf 1) = {true} := scheffeSet_det_half
    have hmeas : ((twoCoinsDetHalf 1).toOuterMeasure ({true} : Set Bool)).toReal = 1 / 2 := by
      rw [toOuterMeasure_apply_toReal]
      simp [twoCoinsDetHalf, coinHalf, coin_apply_true]
    rw [hdet, htrue, Finset.coe_singleton, hmeas] at hterm
    exact (by norm_num : (4 / 10 : ℝ) ≤ |9 / 10 - 1 / 2|).trans hterm
  by_contra hsfin
  have hs1 : scheffeSelectFin twoCoinsDetHalf sampleNineTrueOneFalse = 1 := by
    refine Fin.ext ?_
    have hlt := (scheffeSelectFin twoCoinsDetHalf sampleNineTrueOneFalse).isLt
    have hne : (scheffeSelectFin twoCoinsDetHalf sampleNineTrueOneFalse).val ≠ 0 :=
      fun hv => hsfin (Fin.ext hv)
    omega
  rw [hs1] at hle
  linarith

private theorem birge_succeeds_on_outlier :
    birgeTournamentSelectFin twoCoinsDetHalf sampleNineTrueOneFalse = 0 := by
  let s : Finset (Fin 2) := Finset.univ
  have hs : s.Nonempty := Finset.univ_nonempty
  have hle : maxDefeatRadius s hs twoCoinsDetHalf sampleNineTrueOneFalse
      (birgeTournamentSelectFin twoCoinsDetHalf sampleNineTrueOneFalse) ≤
      maxDefeatRadius s hs twoCoinsDetHalf sampleNineTrueOneFalse 0 :=
    (Classical.choose_spec (s.exists_min_image
      (maxDefeatRadius s hs twoCoinsDetHalf sampleNineTrueOneFalse) hs)).2 0 (Finset.mem_univ 0)
  have hwt_t : birgeWeight coinDet coinHalf true = Real.sqrt (4 / 5) := by
    rw [birgeWeight_eq]
    have h0 : (coinDet true).toReal = 1 := by simp [coinDet]
    have h1 : (coinHalf true).toReal = 1 / 2 := by simp [coinHalf, coin_apply_true]
    rw [h0, h1]
    norm_num
  have hwt_f : birgeWeight coinDet coinHalf false = Real.sqrt 2 := by
    rw [birgeWeight_eq]
    have h0 : (coinDet false).toReal = 0 := by simp [coinDet]
    have h1 : (coinHalf false).toReal = 1 / 2 := by
      simp [coinHalf, coin_apply_false]; norm_num
    rw [h0, h1]
    norm_num
  have hprod : ∏ j : Fin 10, birgeWeight coinDet coinHalf (sampleNineTrueOneFalse j) =
      Real.sqrt (4 / 5) ^ 9 * Real.sqrt 2 := by
    let last : Fin 10 := ⟨9, by decide⟩
    rw [← Finset.prod_erase_mul Finset.univ (fun j =>
      birgeWeight coinDet coinHalf (sampleNineTrueOneFalse j)) (Finset.mem_univ last)]
    have hrest : ∏ j ∈ Finset.univ.erase last,
        birgeWeight coinDet coinHalf (sampleNineTrueOneFalse j) = Real.sqrt (4 / 5) ^ 9 := by
      have hcongr : ∏ j ∈ Finset.univ.erase last,
          birgeWeight coinDet coinHalf (sampleNineTrueOneFalse j) =
          ∏ _j ∈ Finset.univ.erase last, Real.sqrt (4 / 5) := by
        refine Finset.prod_congr rfl fun j hj => ?_
        have hne : j.val ≠ 9 := fun hv => (Finset.mem_erase.mp hj).1 (Fin.ext hv)
        have hlt : j.val < 9 := by omega
        simp [sampleNineTrueOneFalse, hlt, hwt_t]
      rw [hcongr, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ last),
        Finset.card_univ, Fintype.card_fin]
    have hlast : birgeWeight coinDet coinHalf (sampleNineTrueOneFalse last) = Real.sqrt 2 := by
      simp [sampleNineTrueOneFalse, last, hwt_f]
    rw [hrest, hlast]
  have hprod_lt : ∏ j : Fin 10, birgeWeight coinDet coinHalf (sampleNineTrueOneFalse j) < 1 := by
    rw [hprod]
    have hsq : (Real.sqrt (4 / 5) ^ 9 * Real.sqrt 2) ^ 2 < 1 ^ 2 := by
      calc (Real.sqrt (4 / 5) ^ 9 * Real.sqrt 2) ^ 2
          = (Real.sqrt (4 / 5) ^ 2) ^ 9 * Real.sqrt 2 ^ 2 := by ring
        _ = (4 / 5 : ℝ) ^ 9 * 2 := by rw [Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
        _ < 1 ^ 2 := by norm_num
    exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq
  have htest01 : leCamBirgeTest (twoCoinsDetHalf 0) (twoCoinsDetHalf 1)
      sampleNineTrueOneFalse = true := by
    change leCamBirgeTest coinDet coinHalf sampleNineTrueOneFalse = true
    simpa only [leCamBirgeTest, decide_eq_true_eq] using hprod_lt
  have htest10 : leCamBirgeTest (twoCoinsDetHalf 1) (twoCoinsDetHalf 0)
      sampleNineTrueOneFalse = false := by
    simp only [leCamBirgeTest, decide_eq_false_iff_not, not_lt]
    have hpos : 0 < ∏ j : Fin 10, birgeWeight coinDet coinHalf (sampleNineTrueOneFalse j) :=
      Finset.prod_pos fun _ _ => birgeWeight_pos _ _ _
    have hinv : ∏ j : Fin 10, birgeWeight coinHalf coinDet (sampleNineTrueOneFalse j) =
        (∏ j : Fin 10, birgeWeight coinDet coinHalf (sampleNineTrueOneFalse j))⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun _ _ => birgeWeight_symm _ _ _
    change 1 ≤ ∏ j : Fin 10, birgeWeight coinHalf coinDet (sampleNineTrueOneFalse j)
    rw [hinv]
    exact (one_le_inv₀ hpos).mpr hprod_lt.le
  have hrad0 : maxDefeatRadius s hs twoCoinsDetHalf sampleNineTrueOneFalse 0 = 0 := by
    apply le_antisymm
    · refine Finset.sup'_le hs _ fun j _ => ?_
      by_cases hj : j = 0
      · subst hj; simp [hellingerDist_self]
      · have hj1 : j = 1 := by
          refine Fin.ext ?_
          have hlt := j.isLt
          have hne : j.val ≠ 0 := fun hv => hj (Fin.ext hv)
          omega
        subst hj1; simp [htest01]
    · exact (Finset.le_sup' (fun j =>
        if leCamBirgeTest (twoCoinsDetHalf 0) (twoCoinsDetHalf j) sampleNineTrueOneFalse
        then 0 else hellingerDist (twoCoinsDetHalf 0) (twoCoinsDetHalf j))
        (Finset.mem_univ 0)).trans' (by simp [hellingerDist_self])
  have hrad1_pos : 0 < maxDefeatRadius s hs twoCoinsDetHalf sampleNineTrueOneFalse 1 := by
    have hterm := Finset.le_sup' (fun j =>
      if leCamBirgeTest (twoCoinsDetHalf 1) (twoCoinsDetHalf j) sampleNineTrueOneFalse
      then 0 else hellingerDist (twoCoinsDetHalf 1) (twoCoinsDetHalf j)) (Finset.mem_univ 0)
    change (if leCamBirgeTest (twoCoinsDetHalf 1) (twoCoinsDetHalf 0) sampleNineTrueOneFalse
      then 0 else hellingerDist (twoCoinsDetHalf 1) (twoCoinsDetHalf 0)) ≤
        maxDefeatRadius s hs twoCoinsDetHalf sampleNineTrueOneFalse 1 at hterm
    rw [htest10] at hterm
    simp only [Bool.false_eq_true, ↓reduceIte] at hterm
    have hbc : bhattacharyya (twoCoinsDetHalf 1) (twoCoinsDetHalf 0) = Real.sqrt (1 / 2) := by
      rw [bhattacharyya_eq_sum, Fintype.sum_bool]
      have h1t : (twoCoinsDetHalf 1 true).toReal = 1 / 2 := by
        simp [twoCoinsDetHalf, coinHalf, coin_apply_true]
      have h1f : (twoCoinsDetHalf 1 false).toReal = 1 / 2 := by
        simp [twoCoinsDetHalf, coinHalf, coin_apply_false]; norm_num
      have h0t : (twoCoinsDetHalf 0 true).toReal = 1 := by simp [twoCoinsDetHalf, coinDet]
      have h0f : (twoCoinsDetHalf 0 false).toReal = 0 := by simp [twoCoinsDetHalf, coinDet]
      simp [h1t, h1f, h0t, h0f]
    have hpos : 0 < hellingerDist (twoCoinsDetHalf 1) (twoCoinsDetHalf 0) := by
      have hsq : 0 < hellingerDist (twoCoinsDetHalf 1) (twoCoinsDetHalf 0) ^ 2 := by
        rw [hellingerDist_sq, hellingerSq_eq_one_sub_bhattacharyya, hbc]
        have hlt1 : Real.sqrt (1 / 2) < 1 := Real.sqrt_lt' (by norm_num) |>.mpr (by norm_num)
        linarith
      nlinarith [hellingerDist_nonneg (twoCoinsDetHalf 1) (twoCoinsDetHalf 0)]
    exact hpos.trans_le hterm
  by_contra hb
  have hb1 : birgeTournamentSelectFin twoCoinsDetHalf sampleNineTrueOneFalse = 1 := by
    refine Fin.ext ?_
    have hlt := (birgeTournamentSelectFin twoCoinsDetHalf sampleNineTrueOneFalse).isLt
    have hne : (birgeTournamentSelectFin twoCoinsDetHalf sampleNineTrueOneFalse).val ≠ 0 :=
      fun hv => hb (Fin.ext hv)
    omega
  rw [hb1, hrad0] at hle
  linarith

/-! ### Milestone 2: Probabilistic tournament localization and sample complexity checks -/

private theorem dist_nearOneFifth_eq :
    dist coinNearOneFifth (threeCoins 0) = 1 / 1000 := by
  rw [Cslib.Probability.PMF.dist_eq_sum_filter_lt]
  have hp0 : (coinNearOneFifth true).toReal = 201 / 1000 := by
    simp [coinNearOneFifth, coin_apply_true]
  have hp1 : (coinNearOneFifth false).toReal = 799 / 1000 := by
    simp only [coinNearOneFifth, coin_apply_false]; norm_num
  have hq0 : (threeCoins 0 true).toReal = 1 / 5 := by
    simp [threeCoins, coinOneFifth, coin_apply_true]
  have hq1 : (threeCoins 0 false).toReal = 4 / 5 := by
    change (coinOneFifth false).toReal = 4 / 5
    rw [coinOneFifth, coin_apply_false]; norm_num
  rw [Finset.sum_filter, Fintype.sum_bool]
  simp only [hp0, hp1, hq0, hq1]
  norm_num

private theorem hellingerDist_nearOneFifth_le :
    hellingerDist coinNearOneFifth (threeCoins 0) ≤ 1 / 50 := by
  have hbc : 9998 / 10000 ≤ bhattacharyya coinNearOneFifth coinOneFifth := by
    rw [bhattacharyya_eq_sum, Fintype.sum_bool]
    simp only [coinNearOneFifth, coinOneFifth, coin_apply_true, coin_apply_false]
    have ht : 2004 / 10000 ≤ Real.sqrt ((201 / 1000 : ℝ) * (1 / 5)) :=
      Real.le_sqrt_of_sq_le (by norm_num)
    have hf : 7994 / 10000 ≤ Real.sqrt ((1 - (201 / 1000 : ℝ)) * (1 - 1 / 5)) :=
      Real.le_sqrt_of_sq_le (by norm_num)
    linarith
  have hsq : hellingerSq coinNearOneFifth (threeCoins 0) ≤ (1 / 50) ^ 2 := by
    change hellingerSq coinNearOneFifth coinOneFifth ≤ (1 / 50) ^ 2
    rw [hellingerSq_eq_one_sub_bhattacharyya]
    linarith
  refine le_of_sq_le_sq ?_ (by norm_num)
  rw [hellingerDist_sq]
  exact hsq

private theorem scheffe_threeCoins_prob_bound :
    ((iid coinNearOneFifth 10000).toOuterMeasure
      {x | 3 * (1 / 1000 : ℝ) + 2 * (1 / 20 : ℝ) <
        dist coinNearOneFifth (threeCoins (scheffeSelectFin threeCoins x))}).toReal ≤
      12 * Real.exp (-50) := by
  have h := scheffeSelectFin_prob_gt_le coinNearOneFifth threeCoins 0 10000
    (γ := 1 / 20) (by norm_num)
  rw [dist_nearOneFifth_eq] at h
  calc _ ≤ _ := h
    _ = 12 * Real.exp (-50) := by norm_num

private theorem scheffe_threeCoins_sample_complexity :
    ((iid coinNearOneFifth 800).toOuterMeasure
      {x | 3 * (1 / 1000 : ℝ) + 2 * (1 / 20 : ℝ) ≤
        dist coinNearOneFifth (threeCoins (scheffeSelectFin threeCoins x))}).toReal ≤
      3 / 5 := by
  have h := scheffeSelectFin_ge_le_of_log coinNearOneFifth threeCoins 0 (n := 800)
    (γ := 1 / 20) (δ := 3 / 5) (by norm_num) (by norm_num) ?_
  · rwa [dist_nearOneFifth_eq] at h
  · have hlog : Real.log (2 * (3 : ℝ) ^ 2 / (3 / 5)) ≤ 4 :=
      log_le_four_of_le_35 (by norm_num) (by norm_num)
    have hdiv : Real.log (2 * (3 : ℝ) ^ 2 / (3 / 5)) / (2 * (1 / 20 : ℝ) ^ 2) ≤
        4 / (2 * (1 / 20 : ℝ) ^ 2) := div_le_div_of_nonneg_right hlog (by norm_num)
    linarith

private theorem scheffe_cover_example :
    ((iid coinNearOneFifth 10000).toOuterMeasure
      {x | 3 * (1 / 1000 : ℝ) + 2 * (1 / 20 : ℝ) <
        dist coinNearOneFifth (threeCoins
          (scheffeSelect Finset.univ Finset.univ_nonempty threeCoins x))}).toReal ≤
      12 * Real.exp (-50) := by
  have h := scheffeSelect_of_cover Finset.univ Finset.univ_nonempty threeCoins
    {coinNearOneFifth} (r := 1 / 1000) (γ := 1 / 20) (by norm_num)
    (fun p hp => by
      rw [Set.mem_singleton_iff.mp hp]
      exact ⟨0, Finset.mem_univ 0, dist_nearOneFifth_eq.le⟩)
    (Set.mem_singleton coinNearOneFifth) 10000
  rw [Finset.card_univ, Fintype.card_fin] at h
  calc _ ≤ _ := h
    _ = 12 * Real.exp (-50) := by norm_num

private theorem birge_cover_threeCoins :
    ((iid coinNearOneFifth 2500).toOuterMeasure
      {x | 11 * (1 / 50 : ℝ) <
        hellingerDist coinNearOneFifth (threeCoins (birgeTournamentSelectFin threeCoins x))}).toReal
      ≤ 4 * Real.exp (-4) := by
  have h := birgeTournamentSelectFin_prob_gt_le threeCoins (p := coinNearOneFifth) 0 2500
    (r := 1 / 50) (by norm_num) hellingerDist_nearOneFifth_le
  calc _ ≤ _ := h
    _ = 4 * Real.exp (-4) := by norm_num

private theorem birge_threeCoins_sample_complexity :
    ((iid coinNearOneFifth 2500).toOuterMeasure
      {x | 11 * (1 / 50 : ℝ) ≤
        hellingerDist coinNearOneFifth (threeCoins (birgeTournamentSelectFin threeCoins x))}).toReal
      ≤ 1 / 5 := by
  refine birgeTournamentSelectFin_ge_le_of_log threeCoins (p := coinNearOneFifth) 0
    (r := 1 / 50) (δ := 1 / 5) (by norm_num) (by norm_num) hellingerDist_nearOneFifth_le ?_
  have hlog : Real.log (2 * (3 : ℝ) / (1 / 5)) ≤ 4 :=
    log_le_four_of_le_35 (by norm_num) (by norm_num)
  have hdiv : Real.log (2 * (3 : ℝ) / (1 / 5)) / (4 * (1 / 50 : ℝ) ^ 2) ≤
      4 / (4 * (1 / 50 : ℝ) ^ 2) := div_le_div_of_nonneg_right hlog (by norm_num)
  linarith

private theorem birge_cover_example :
    ((iid coinNearOneFifth 2500).toOuterMeasure
      {x | 11 * (1 / 50 : ℝ) <
        hellingerDist coinNearOneFifth (threeCoins
          (birgeTournamentSelect Finset.univ Finset.univ_nonempty threeCoins x))}).toReal
      ≤ 4 * Real.exp (-4) := by
  have h := birgeTournamentSelect_of_cover Finset.univ Finset.univ_nonempty threeCoins
    {coinNearOneFifth} (r := 1 / 50) (by norm_num)
    (fun p hp => by
      rw [Set.mem_singleton_iff.mp hp]
      exact ⟨0, Finset.mem_univ 0, hellingerDist_nearOneFifth_le⟩)
    (Set.mem_singleton coinNearOneFifth) 2500
  rw [Finset.card_univ, Fintype.card_fin] at h
  calc _ ≤ _ := h
    _ = 4 * Real.exp (-4) := by norm_num

end CslibFrontierTests.HypothesisSelection
