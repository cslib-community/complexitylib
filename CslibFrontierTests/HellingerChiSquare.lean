/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests for Hellinger distance and chi-square divergence)

import CslibFrontier.Probability.ChiSquare
import CslibFrontier.Probability.Hellinger
import CslibFrontier.Probability.PMF.Coin
import CslibFrontier.Probability.PMF.ToReal

/-!
# Hellinger distance and chi-square divergence tests

Nonvacuous test clients exercising concrete Bhattacharyya/Hellinger/`χ²` calculations, support and
off-support behavior (`echiSquare = ⊤`), metric and triangle inequality properties, total variation
bounds, product/`iid` tensorization, data processing under `map` and `bind`, comparison
inequalities `2 h² ≤ KL ≤ log (1 + χ²) ≤ χ²`, the `n`-fold i.i.d. Hellinger acceptance bound, and
the Ingster/Le Cam mixture second-moment pipeline.
-/

set_option linter.privateModule false

section

open Cslib.Probability.PMF
open scoped Cslib.Probability.PMF unitInterval

private noncomputable def coinRat (a b : ℕ) (h : a ≤ b) (hb : 0 < b) : PMF Bool :=
  coin ⟨(a : ℝ) / b, by positivity, (div_le_one (by exact_mod_cast hb)).mpr
    (by exact_mod_cast h)⟩

private lemma coinRat_apply_true (a b : ℕ) (h : a ≤ b) (hb : 0 < b) :
    (coinRat a b h hb true).toReal = (a : ℝ) / b := by
  simp [coinRat, coin_apply_toReal]

private lemma coinRat_apply_false (a b : ℕ) (h : a ≤ b) (hb : 0 < b) :
    (coinRat a b h hb false).toReal = 1 - (a : ℝ) / b := by
  simp [coinRat, coin_apply_toReal]

private lemma coinRat_support_univ {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    (coinRat a b hab.le (ha.trans hab)).support = Set.univ := by
  ext x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  rw [PMF.mem_support_iff]
  intro hx0
  have h0 : (coinRat a b hab.le (ha.trans hab) x).toReal = 0 := by simp [hx0]
  cases x
  · rw [coinRat_apply_false] at h0
    have hlt : (a : ℝ) / b < 1 := (div_lt_one (by exact_mod_cast (ha.trans hab))).mpr
      (by exact_mod_cast hab)
    linarith
  · rw [coinRat_apply_true] at h0
    have hpos : (0 : ℝ) < (a : ℝ) / b := div_pos (by exact_mod_cast ha)
      (by exact_mod_cast (ha.trans hab))
    linarith

/-- Disjoint point masses have zero Bhattacharyya coefficient, unit Hellinger distance, and
`echiSquare = ⊤` due to broken support containment. -/
example :
    bhattacharyya (PMF.pure true) (PMF.pure false) = 0 ∧
      hellingerSq (PMF.pure true) (PMF.pure false) = 1 ∧
      hellingerDist (PMF.pure true) (PMF.pure false) = 1 ∧
      echiSquare (PMF.pure true) (PMF.pure false) = ⊤ := by
  have hdisj : Disjoint (PMF.pure true).support (PMF.pure false).support := by
    simp
  have hbc : bhattacharyya (PMF.pure true) (PMF.pure false) = 0 :=
    (bhattacharyya_eq_zero_iff _ _).mpr hdisj
  have hsq : hellingerSq (PMF.pure true) (PMF.pure false) = 1 := by
    rw [hellingerSq_eq_one_sub_bhattacharyya, hbc, sub_zero]
  have hd : hellingerDist (PMF.pure true) (PMF.pure false) = 1 := by
    rw [hellingerDist_eq_sqrt_hellingerSq, hsq, Real.sqrt_one]
  have hnsup : ¬ (PMF.pure true).support ⊆ (PMF.pure false).support := by
    intro h
    have : (true : Bool) ∈ (PMF.pure false).support := h (by simp)
    simp at this
  exact ⟨hbc, hsq, hd, echiSquare_eq_top_iff.mpr hnsup⟩

/-- Concrete values for `p = Bernoulli(1/5)` vs `q = Bernoulli(4/5)`: exact `bhattacharyya`,
`hellingerSq`, `dist`, `chiSquare`, total variation inequalities (`dist` and `tvDist`), and the
`2 h² ≤ KL ≤ log(1 + χ²) ≤ χ²` hierarchy. -/
example :
    let p := coinRat 1 5 (by decide) (by decide)
    let q := coinRat 4 5 (by decide) (by decide)
    letI : MeasurableSpace Bool := ⊤
    bhattacharyya p q = 4 / 5 ∧
      hellingerSq p q = 1 / 5 ∧
      dist p q = 3 / 5 ∧
      chiSquare p q = 9 / 4 ∧
      4 * dist p q ^ 2 ≤ chiSquare p q ∧
      MeasureTheory.tvDist p.toMeasure q.toMeasure ≤ Real.sqrt (chiSquare p q) ∧
      2 * hellingerSq p q ≤ (InformationTheory.klDiv p.toMeasure q.toMeasure).toReal ∧
      (InformationTheory.klDiv p.toMeasure q.toMeasure).toReal ≤
        Real.log (1 + chiSquare p q) ∧
      2 * hellingerSq p q ≤ chiSquare p q := by
  intro p q
  let : MeasurableSpace Bool := ⊤
  have : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  have hsup : p.support ⊆ q.support := by
    rw [coinRat_support_univ (by decide) (by decide),
      coinRat_support_univ (by decide) (by decide)]
  have hbc : bhattacharyya p q = 4 / 5 := by
    rw [bhattacharyya_eq_sum, Fintype.sum_bool, coinRat_apply_true, coinRat_apply_true,
      coinRat_apply_false, coinRat_apply_false]
    norm_num
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, show (25 : ℝ) = 5 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]
    ring
  have hsq : hellingerSq p q = 1 / 5 := by
    rw [hellingerSq_eq_one_sub_bhattacharyya, hbc]
    norm_num
  have hdist : dist p q = 3 / 5 := by
    rw [dist_eq, Fintype.sum_bool, coinRat_apply_true, coinRat_apply_true,
      coinRat_apply_false, coinRat_apply_false]
    norm_num
  have hchi : chiSquare p q = 9 / 4 := by
    rw [chiSquare_eq_sum hsup, Fintype.sum_bool, coinRat_apply_true, coinRat_apply_true,
      coinRat_apply_false, coinRat_apply_false]
    norm_num
  exact ⟨hbc, hsq, hdist, hchi, four_mul_dist_sq_le_chiSquare hsup,
    tvDist_le_sqrt_chiSquare hsup, two_mul_hellingerSq_le_toReal_klDiv hsup,
    toReal_klDiv_le_log_one_add_chiSquare hsup, two_mul_hellingerSq_le_chiSquare hsup⟩

/-- Triangle inequality and sharp/standard `h² ↔ dist ↔ tvDist` bounds on distinct coins. -/
example :
    let p := coinRat 1 5 (by decide) (by decide)
    let q := coinRat 1 2 (by decide) (by decide)
    let r := coinRat 4 5 (by decide) (by decide)
    letI : MeasurableSpace Bool := ⊤
    hellingerDist p r ≤ hellingerDist p q + hellingerDist q r ∧
      hellingerSq p r ≤ dist p r ∧
      dist p r ≤ hellingerDist p r * Real.sqrt (2 - hellingerSq p r) ∧
      dist p r ≤ Real.sqrt 2 * hellingerDist p r ∧
      2 * hellingerSq p r ≤ MeasureTheory.tvDist p.toMeasure r.toMeasure ∧
      MeasureTheory.tvDist p.toMeasure r.toMeasure ≤ 2 * Real.sqrt 2 * hellingerDist p r := by
  intro p q r
  let : MeasurableSpace Bool := ⊤
  have : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  exact ⟨hellingerDist_triangle p q r, hellingerSq_le_dist p r,
    dist_le_hellingerDist_mul_sqrt_two_sub_hellingerSq p r,
    dist_le_sqrt_two_mul_hellingerDist p r,
    two_mul_hellingerSq_le_tvDist p r,
    tvDist_le_two_mul_sqrt_two_mul_hellingerDist p r⟩

/-- Tensorization for `iid` coins (`n = 5`) and non-identical `pi` products. -/
example :
    let p := coinRat 1 5 (by decide) (by decide)
    let q := coinRat 4 5 (by decide) (by decide)
    bhattacharyya (iid p 5) (iid q 5) = (4 / 5 : ℝ) ^ 5 ∧
      hellingerSq (iid p 5) (iid q 5) = 1 - (4 / 5 : ℝ) ^ 5 ∧
      hellingerDist (iid p 5) (iid q 5) ≤ Real.sqrt (5 : ℕ) * hellingerDist p q ∧
      1 + chiSquare (iid p 5) (iid q 5) = (13 / 4 : ℝ) ^ 5 ∧
      1 + chiSquare (pi fun i : Fin 2 => if i = 0 then p else q)
          (pi fun i : Fin 2 => if i = 0 then q else q) = (13 / 4 : ℝ) ∧
      dist (pi fun i : Fin 2 => if i = 0 then p else q)
          (pi fun i : Fin 2 => if i = 0 then q else q) ≤
        Real.sqrt (2 * ∑ i : Fin 2, hellingerSq (if i = 0 then p else q) q) := by
  intro p q
  have hsup : p.support ⊆ q.support := by
    rw [coinRat_support_univ (by decide) (by decide),
      coinRat_support_univ (by decide) (by decide)]
  have hbc : bhattacharyya p q = 4 / 5 := by
    rw [bhattacharyya_eq_sum, Fintype.sum_bool, coinRat_apply_true, coinRat_apply_true,
      coinRat_apply_false, coinRat_apply_false]
    norm_num
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, show (25 : ℝ) = 5 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]
    ring
  have hchi : chiSquare p q = 9 / 4 := by
    rw [chiSquare_eq_sum hsup, Fintype.sum_bool, coinRat_apply_true, coinRat_apply_true,
      coinRat_apply_false, coinRat_apply_false]
    norm_num
  refine ⟨?_, ?_, hellingerDist_iid_le p q 5, ?_, ?_, ?_⟩
  · rw [bhattacharyya_iid, hbc]
  · rw [hellingerSq_eq_one_sub_bhattacharyya, bhattacharyya_iid, hbc]
  · rw [one_add_chiSquare_iid hsup, hchi]
    norm_num
  · rw [one_add_chiSquare_pi _ _ (fun i => by fin_cases i <;> simp [hsup]), Fin.prod_univ_two]
    simp [chiSquare_self, hchi]
    norm_num
  · simpa using dist_pi_le_sqrt_two_mul_sum_hellingerSq
      (fun i : Fin 2 => if i = 0 then p else q) (fun _ : Fin 2 => q)

/-- Acceptance client for `n` i.i.d. draws from close Pythagorean-triple coins `Bernoulli(49/625)`
and `Bernoulli(25/169)`: `10` i.i.d. samples still have statistical distance strictly below `1 / 2`.
-/
example :
    let p := coinRat 49 625 (by decide) (by decide)
    let q := coinRat 25 169 (by decide) (by decide)
    dist (iid p 10) (iid q 10) < 1 / 2 ∧
      dist (iid p 10) (iid q 10) ≤ Real.sqrt (2 * (10 : ℕ)) * hellingerDist p q := by
  intro p q
  have hbc : bhattacharyya p q = 323 / 325 := by
    rw [bhattacharyya_eq_sum, Fintype.sum_bool, coinRat_apply_true, coinRat_apply_true,
      coinRat_apply_false, coinRat_apply_false]
    norm_num
    rw [show (49 : ℝ) = 7 ^ 2 by norm_num, show (4225 : ℝ) = 65 ^ 2 by norm_num,
      show (82944 : ℝ) = 288 ^ 2 by norm_num, show (105625 : ℝ) = 325 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num),
      Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]
    norm_num
  have hbound : dist (iid p 10) (iid q 10) ≤ Real.sqrt (2 * (10 : ℕ)) * hellingerDist p q :=
    dist_iid_le_sqrt_two_mul_nat_mul_hellingerDist p q 10
  have hlt : Real.sqrt (2 * (10 : ℕ)) * hellingerDist p q < 1 / 2 := by
    have hh : hellingerDist p q = Real.sqrt (2 / 325) := by
      rw [hellingerDist_eq_sqrt_one_sub_bhattacharyya, hbc]
      norm_num
    rw [hh, Nat.cast_ofNat, ← Real.sqrt_mul (by norm_num)]
    have hlt_sq : (2 * (10 : ℝ)) * (2 / 325) < (1 / 2) ^ 2 := by norm_num
    calc Real.sqrt (2 * 10 * (2 / 325))
      _ < Real.sqrt ((1 / 2 : ℝ) ^ 2) :=
          Real.sqrt_lt_sqrt (by norm_num) hlt_sq
      _ = 1 / 2 := Real.sqrt_sq (by norm_num)
  exact ⟨lt_of_le_of_lt hbound hlt, hbound⟩

/-- Data processing inequalities for `map`, `bind`, and injectivity invariance. -/
example (p q : PMF Bool) (h : p.support ⊆ q.support) (kernel : Bool → PMF (Fin 3))
    (f : Bool → Fin 3) (hf : Function.Injective f) :
    hellingerDist (p.bind kernel) (q.bind kernel) ≤ hellingerDist p q ∧
      chiSquare (p.bind kernel) (q.bind kernel) ≤ chiSquare p q ∧
      hellingerDist (p.map f) (q.map f) = hellingerDist p q ∧
      echiSquare (p.map f) (q.map f) ≤ echiSquare p q ∧
      ENNReal.ofReal (4 * dist p q ^ 2) ≤ echiSquare p q :=
  ⟨hellingerDist_bind_le p q kernel, chiSquare_bind_le h kernel,
    hellingerDist_map_of_injective p q hf, echiSquare_map_le p q f,
    ofReal_four_mul_dist_sq_le_echiSquare p q⟩

/-- Ingster / Le Cam mixture second-moment pipeline: mixing `n = 2` i.i.d. copies of
`Bernoulli(4/5)` vs `Bernoulli(1/5)` equally against uniform `Bernoulli(1/2)` gives exact
`χ² = 81 / 625`, yielding `dist ≤ 9 / 50`. -/
example :
    let μ := coinRat 1 2 (by decide) (by decide)
    let K : Bool → PMF Bool := fun t =>
      if t then coinRat 4 5 (by decide) (by decide) else coinRat 1 5 (by decide) (by decide)
    let q := coinRat 1 2 (by decide) (by decide)
    1 + chiSquare (μ.bind fun t => iid (K t) 2) (iid q 2) = 706 / 625 ∧
      dist (μ.bind fun t => iid (K t) 2) (iid q 2) ≤ 9 / 50 := by
  intro μ K q
  have hsup : ∀ t ∈ μ.support, (K t).support ⊆ q.support := by
    intro t _
    cases t <;> simp only [K, ↓reduceIte, Bool.false_eq_true]
    · rw [coinRat_support_univ (by decide) (by decide),
        coinRat_support_univ (by decide) (by decide)]
    · rw [coinRat_support_univ (by decide) (by decide),
        coinRat_support_univ (by decide) (by decide)]
  have hmix : 1 + chiSquare (μ.bind fun t => iid (K t) 2) (iid q 2) = 706 / 625 := by
    rw [one_add_chiSquare_bind_iid_eq μ K q 2 hsup, Fintype.sum_bool, Fintype.sum_bool,
      Fintype.sum_bool]
    simp only [Fintype.sum_bool, μ, K, q, ↓reduceIte, Bool.false_eq_true,
      coinRat_apply_true, coinRat_apply_false]
    norm_num
  have hsupp_iid : (μ.bind fun t => iid (K t) 2).support ⊆ (iid q 2).support := by
    refine support_bind_subset_of_forall fun t ht => ?_
    intro u hu
    rw [iid_eq_pi, mem_support_pi_iff] at hu ⊢
    intro i
    exact hsup t ht (hu i)
  have hd : dist (μ.bind fun t => iid (K t) 2) (iid q 2) ≤ 9 / 50 := by
    refine (dist_le_sqrt_chiSquare_div_two hsupp_iid).trans_eq ?_
    have hchi : chiSquare (μ.bind fun t => iid (K t) 2) (iid q 2) = (9 / 25 : ℝ) ^ 2 := by
      linarith
    rw [hchi, Real.sqrt_sq (by norm_num)]
    norm_num
  exact ⟨hmix, hd⟩

end
