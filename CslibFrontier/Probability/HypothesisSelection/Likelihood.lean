/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Hellinger
public import CslibFrontier.Probability.IID
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Union
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Likelihood-ratio Chernoff bounds and finite-family MLE

This module proves the Bhattacharyya / likelihood-ratio Chernoff bound for discrete distributions
and uses it to bound the Hellinger estimation error of maximum likelihood estimation (MLE) over a
finite family of models, building on `CslibFrontier.Probability.Hellinger` (see [Canonne2022] and
[Tsybakov2009] for background; the discrete finite-family likelihood-ratio Chernoff and MLE
formulations below are proved in this library).

## Main definitions

* `Cslib.Probability.HypothesisSelection.mle`: maximum likelihood estimator over a nonempty finite
  family of distributions indexed by `s : Finset ι`.
* `Cslib.Probability.HypothesisSelection.mleFin`: finite specialization indexed by `Fin M`.

## Main results

* `Cslib.Probability.PMF.toOuterMeasure_le_bhattacharyya`: single-sample likelihood-ratio tail
  bound `(p.toOuterMeasure {a | p a ≤ q a}).toReal ≤ bhattacharyya p q`.
* `Cslib.Probability.PMF.toOuterMeasure_iid_le_bhattacharyya_pow`: `n`-fold i.i.d.
  likelihood-ratio Chernoff bound
  `((iid p n).toOuterMeasure {x | iid p n x ≤ iid q n x}).toReal ≤ bhattacharyya p q ^ n`.
* `Cslib.Probability.PMF.toOuterMeasure_iid_le_exp_hellingerDist`: exponential Hellinger form
  `≤ Real.exp (-n * hellingerDist p q ^ 2)`.
* `Cslib.Probability.HypothesisSelection.mle_hellingerDist_gt_le`,
  `Cslib.Probability.HypothesisSelection.mleFin_hellingerDist_gt_le`: MLE over `M` candidate
  models returns a model within Hellinger radius `r` except with probability at most
  `(M - 1) * Real.exp (-n * r ^ 2)` when the true model lies in the family.

## References

* [Clément L. Canonne, *Topics and Techniques in Distribution Testing*][Canonne2022], Appendix B
  (March 10, 2024 draft; cited for background Hellinger inequalities in `Hellinger.lean`).
* [Alexandre B. Tsybakov, *Introduction to Nonparametric Estimation*][Tsybakov2009] (full text
  not inspected; cited at book level for divergence/Hellinger background).
-/

public section

namespace Cslib.Probability.PMF

open Finset
open scoped BigOperators ENNReal

variable {α : Type*}

/-- Weighted single-sample likelihood-ratio bound: the `p`-probability of `{a | c * p a ≤ q a}`
is at most `bhattacharyya p q / √c` for every `c > 0`. -/
theorem toOuterMeasure_mul_le_bhattacharyya_div_sqrt (p q : PMF α) {c : ℝ} (hc : 0 < c) :
    (p.toOuterMeasure {a | c * (p a).toReal ≤ (q a).toReal}).toReal ≤
      bhattacharyya p q / Real.sqrt c := by
  classical
  let s : Set α := {a | c * (p a).toReal ≤ (q a).toReal}
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq fun a => by
    by_cases ha : a ∈ s
    · rw [Set.indicator_of_mem ha]
      exact p.apply_ne_top a
    · rw [Set.indicator_of_notMem ha]
      exact ENNReal.zero_ne_top]
  have hpt (a : α) :
      (s.indicator p a).toReal ≤ Real.sqrt ((p a).toReal * (q a).toReal) / Real.sqrt c := by
    by_cases ha : a ∈ s
    · rw [Set.indicator_of_mem ha]
      have hcu : c * (p a).toReal ≤ (q a).toReal := ha
      have hp0 : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
      have hsq : Real.sqrt c * (p a).toReal ≤ Real.sqrt ((p a).toReal * (q a).toReal) := by
        refine Real.le_sqrt_of_sq_le ?_
        calc (Real.sqrt c * (p a).toReal) ^ 2
            = (Real.sqrt c ^ 2) * (p a).toReal * (p a).toReal := by ring
          _ = (c * (p a).toReal) * (p a).toReal := by rw [Real.sq_sqrt hc.le]
          _ ≤ (q a).toReal * (p a).toReal := mul_le_mul_of_nonneg_right hcu hp0
          _ = (p a).toReal * (q a).toReal := mul_comm _ _
      exact (le_div_iff₀ (Real.sqrt_pos.mpr hc)).mpr (by linarith)
    · rw [Set.indicator_of_notMem ha, ENNReal.toReal_zero]
      exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum_ind : Summable (fun a => (s.indicator p a).toReal) :=
    ENNReal.summable_toReal (p.tsum_coe_indicator_ne_top s)
  have hsum_rhs : Summable (fun a => Real.sqrt ((p a).toReal * (q a).toReal) / Real.sqrt c) :=
    (summable_sqrt_toReal_mul p q).div_const _
  calc ∑' a, (s.indicator p a).toReal
      ≤ ∑' a, Real.sqrt ((p a).toReal * (q a).toReal) / Real.sqrt c :=
        Summable.tsum_le_tsum hpt hsum_ind hsum_rhs
    _ = bhattacharyya p q / Real.sqrt c := by
        rw [tsum_div_const, bhattacharyya_eq_tsum]

/-- Single-sample likelihood-ratio Chernoff bound: `(p.toOuterMeasure {a | p a ≤ q a}).toReal ≤
bhattacharyya p q`. -/
theorem toOuterMeasure_le_bhattacharyya (p q : PMF α) :
    (p.toOuterMeasure {a | p a ≤ q a}).toReal ≤ bhattacharyya p q := by
  have heq : {a : α | p a ≤ q a} = {a : α | 1 * (p a).toReal ≤ (q a).toReal} := by
    ext a
    simp only [Set.mem_ofPred_eq, one_mul,
      ENNReal.toReal_le_toReal (p.apply_ne_top a) (q.apply_ne_top a)]
  rw [heq]
  simpa using toOuterMeasure_mul_le_bhattacharyya_div_sqrt p q zero_lt_one

/-- Real-valued form of the single-sample likelihood-ratio Chernoff bound. -/
theorem toOuterMeasure_toReal_le_bhattacharyya (p q : PMF α) :
    (p.toOuterMeasure {a | (p a).toReal ≤ (q a).toReal}).toReal ≤ bhattacharyya p q := by
  simpa using toOuterMeasure_mul_le_bhattacharyya_div_sqrt p q zero_lt_one

/-- Weighted `n`-fold i.i.d. likelihood-ratio Chernoff bound: for `c > 0`,
`((iid p n).toOuterMeasure {x | c * (iid p n x).toReal ≤ (iid q n x).toReal}).toReal ≤
bhattacharyya p q ^ n / √c`. -/
theorem toOuterMeasure_iid_mul_le_bhattacharyya_pow_div_sqrt [Finite α]
    (p q : PMF α) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ((iid p n).toOuterMeasure {x | c * (iid p n x).toReal ≤ (iid q n x).toReal}).toReal ≤
      bhattacharyya p q ^ n / Real.sqrt c :=
  (toOuterMeasure_mul_le_bhattacharyya_div_sqrt (iid p n) (iid q n) hc).trans_eq
    (by rw [bhattacharyya_iid])

/-- The `n`-fold i.i.d. likelihood-ratio Chernoff bound:
`((iid p n).toOuterMeasure {x | iid p n x ≤ iid q n x}).toReal ≤ bhattacharyya p q ^ n`. -/
theorem toOuterMeasure_iid_le_bhattacharyya_pow [Finite α] (p q : PMF α) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | iid p n x ≤ iid q n x}).toReal ≤ bhattacharyya p q ^ n :=
  (toOuterMeasure_le_bhattacharyya (iid p n) (iid q n)).trans_eq (bhattacharyya_iid p q n)

/-- Product form of the `n`-fold i.i.d. likelihood-ratio Chernoff bound. -/
theorem toOuterMeasure_iid_prod_le_bhattacharyya_pow [Finite α] (p q : PMF α) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | ∏ i, p (x i) ≤ ∏ i, q (x i)}).toReal ≤
      bhattacharyya p q ^ n := by
  simpa only [← iid_apply] using toOuterMeasure_iid_le_bhattacharyya_pow p q n

/-- Real-valued product form of the `n`-fold i.i.d. likelihood-ratio Chernoff bound. -/
theorem toOuterMeasure_iid_prod_toReal_le_bhattacharyya_pow [Finite α]
    (p q : PMF α) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | ∏ i, (p (x i)).toReal ≤ ∏ i, (q (x i)).toReal}).toReal ≤
      bhattacharyya p q ^ n := by
  have heq :
      {x : Fin n → α | ∏ i, (p (x i)).toReal ≤ ∏ i, (q (x i)).toReal} =
        {x : Fin n → α | iid p n x ≤ iid q n x} := by
    ext x
    simp only [Set.mem_ofPred_eq, ← ENNReal.toReal_prod, ← iid_apply,
      ENNReal.toReal_le_toReal ((iid p n).apply_ne_top x) ((iid q n).apply_ne_top x)]
  rw [heq]
  exact toOuterMeasure_iid_le_bhattacharyya_pow p q n

/-- Exponential upper bound on the `n`-th power of the Bhattacharyya coefficient:
`bhattacharyya p q ^ n ≤ Real.exp (-n * hellingerSq p q)`. -/
theorem bhattacharyya_pow_le_exp_hellingerSq (p q : PMF α) (n : ℕ) :
    bhattacharyya p q ^ n ≤ Real.exp (-(n : ℝ) * hellingerSq p q) := by
  rw [hellingerSq_eq_one_sub_bhattacharyya]
  have hpow := Real.one_sub_pow_le_exp (p := 1 - bhattacharyya p q)
    (c := (n : ℝ) * (1 - bhattacharyya p q)) (R := n) (by linarith [bhattacharyya_nonneg p q])
    le_rfl
  simpa only [sub_sub_cancel, neg_mul] using hpow

/-- Exponential Hellinger form of the `n`-fold i.i.d. likelihood-ratio Chernoff bound in terms of
`hellingerSq`. -/
theorem toOuterMeasure_iid_le_exp_hellingerSq [Finite α] (p q : PMF α) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | iid p n x ≤ iid q n x}).toReal ≤
      Real.exp (-(n : ℝ) * hellingerSq p q) :=
  (toOuterMeasure_iid_le_bhattacharyya_pow p q n).trans
    (bhattacharyya_pow_le_exp_hellingerSq p q n)

/-- Exponential Hellinger form of the `n`-fold i.i.d. likelihood-ratio Chernoff bound in terms of
`hellingerDist`: `((iid p n).toOuterMeasure {x | iid p n x ≤ iid q n x}).toReal ≤
Real.exp (-n * hellingerDist p q ^ 2)`. -/
theorem toOuterMeasure_iid_le_exp_hellingerDist [Finite α] (p q : PMF α) (n : ℕ) :
    ((iid p n).toOuterMeasure {x | iid p n x ≤ iid q n x}).toReal ≤
      Real.exp (-(n : ℝ) * hellingerDist p q ^ 2) := by
  simpa only [hellingerDist_sq] using toOuterMeasure_iid_le_exp_hellingerSq p q n

end Cslib.Probability.PMF

namespace Cslib.Probability.HypothesisSelection

open Cslib.Probability.PMF Finset
open scoped BigOperators ENNReal

variable {ι α : Type*}

/-- Maximum likelihood estimator over a nonempty finite family of distributions `models` indexed by
`s : Finset ι`. Returns an index `i ∈ s` maximizing `iid (models i) n x`. -/
@[expose] noncomputable def mle (s : Finset ι) (hs : s.Nonempty) (models : ι → _root_.PMF α)
    {n : ℕ} (x : Fin n → α) : ι :=
  (Finset.exists_max_image s (fun i => (iid (models i) n x).toReal) hs).choose

/-- Membership of `mle s hs models x` in `s`. -/
theorem mle_mem (s : Finset ι) (hs : s.Nonempty) (models : ι → _root_.PMF α)
    {n : ℕ} (x : Fin n → α) : mle s hs models x ∈ s :=
  (Finset.exists_max_image s (fun i => (iid (models i) n x).toReal) hs).choose_spec.1

/-- Optimality of `mle`: the selected model maximizes `iid (models i) n x` over `s`. -/
theorem le_iid_mle (s : Finset ι) (hs : s.Nonempty) (models : ι → _root_.PMF α)
    {n : ℕ} (x : Fin n → α) {j : ι} (hj : j ∈ s) :
    iid (models j) n x ≤ iid (models (mle s hs models x)) n x := by
  have hreal : (iid (models j) n x).toReal ≤ (iid (models (mle s hs models x)) n x).toReal :=
    (Finset.exists_max_image s (fun i => (iid (models i) n x).toReal) hs).choose_spec.2 j hj
  exact (ENNReal.toReal_le_toReal ((iid _ n).apply_ne_top x) ((iid _ n).apply_ne_top x)).mp hreal

private theorem mle_hellingerDist_sum_bc [DecidableEq ι] [Finite α]
    (s : Finset ι) (hs : s.Nonempty) (models : ι → _root_.PMF α)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (n : ℕ) (P : ι → Prop) [DecidablePred P] (hP : ¬ P i₀) :
    ((iid (models i₀) n).toOuterMeasure {x | P (mle s hs models x)}).toReal ≤
      ∑ j ∈ (s.erase i₀).filter P, bhattacharyya (models i₀) (models j) ^ n := by
  let bad : Finset ι := (s.erase i₀).filter P
  have hsub : {x : Fin n → α | P (mle s hs models x)} ⊆
      ⋃ j ∈ bad, {x | iid (models i₀) n x ≤ iid (models j) n x} := by
    intro x hx
    have hmem : mle s hs models x ∈ s := mle_mem s hs models x
    have hne : mle s hs models x ≠ i₀ := fun heq => hP (heq ▸ hx)
    refine Set.mem_iUnion₂.mpr ⟨mle s hs models x, ?_, le_iid_mle s hs models x hi₀⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hmem⟩, hx⟩
  calc ((iid (models i₀) n).toOuterMeasure {x | P (mle s hs models x)}).toReal
      ≤ ((iid (models i₀) n).toOuterMeasure
          (⋃ j ∈ bad, {x | iid (models i₀) n x ≤ iid (models j) n x})).toReal :=
        toOuterMeasure_toReal_mono _ hsub
    _ ≤ ∑ j ∈ bad, ((iid (models i₀) n).toOuterMeasure
          {x | iid (models i₀) n x ≤ iid (models j) n x}).toReal :=
        toOuterMeasure_toReal_biUnion_finset_le _ _ _
    _ ≤ ∑ j ∈ bad, bhattacharyya (models i₀) (models j) ^ n :=
        Finset.sum_le_sum fun j _ => toOuterMeasure_iid_le_bhattacharyya_pow _ _ n

open Classical in
/-- Sharp Bhattacharyya sum bound for MLE over a finite family when the true model `models i₀`
lies in `s`: the probability of selecting a model outside Hellinger radius `r ≥ 0` is at most
the sum of `bhattacharyya (models i₀) (models j) ^ n` over `j ∈ s.erase i₀` beyond radius `r`. -/
theorem mle_hellingerDist_gt_le_sum_bhattacharyya [DecidableEq ι] [Finite α]
    (s : Finset ι) (hs : s.Nonempty) (models : ι → _root_.PMF α)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ((iid (models i₀) n).toOuterMeasure
      {x | r < hellingerDist (models i₀) (models (mle s hs models x))}).toReal ≤
        ∑ j ∈ (s.erase i₀).filter (fun j => r < hellingerDist (models i₀) (models j)),
          bhattacharyya (models i₀) (models j) ^ n :=
  mle_hellingerDist_sum_bc s hs models hi₀ n
    (fun j => r < hellingerDist (models i₀) (models j))
    (by simp only [hellingerDist_self]; linarith)

private theorem mle_hellingerDist_pred_le [Finite α]
    (s : Finset ι) (hs : s.Nonempty) (models : ι → _root_.PMF α)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (P : ι → Prop) (hP0 : ¬ P i₀) (hPr : ∀ j, P j → r ≤ hellingerDist (models i₀) (models j)) :
    ((iid (models i₀) n).toOuterMeasure {x | P (mle s hs models x)}).toReal ≤
      (s.card - 1 : ℝ) * Real.exp (-(n : ℝ) * r ^ 2) := by
  classical
  have hsum := mle_hellingerDist_sum_bc s hs models hi₀ n P hP0
  let bad := (s.erase i₀).filter P
  have hterm : ∀ j ∈ bad, bhattacharyya (models i₀) (models j) ^ n ≤
      Real.exp (-(n : ℝ) * r ^ 2) := by
    intro j hj
    have hrle : r ≤ hellingerDist (models i₀) (models j) :=
      hPr j (Finset.mem_filter.mp hj).2
    have hsq : r ^ 2 ≤ hellingerSq (models i₀) (models j) := by
      rw [← hellingerDist_sq]
      exact sq_le_sq' (by linarith) hrle
    refine (bhattacharyya_pow_le_exp_hellingerSq _ _ n).trans (Real.exp_le_exp.mpr ?_)
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hcard_bad : bad.card ≤ s.card - 1 :=
    (Finset.card_filter_le _ _).trans (Finset.card_erase_of_mem hi₀).le
  have hcard_sub : ((s.card - 1 : ℕ) : ℝ) = (s.card : ℝ) - 1 := by
    simpa using Nat.cast_sub hs.card_pos
  calc ((iid (models i₀) n).toOuterMeasure {x | P (mle s hs models x)}).toReal
      ≤ ∑ j ∈ bad, bhattacharyya (models i₀) (models j) ^ n := hsum
    _ ≤ ∑ _j ∈ bad, Real.exp (-(n : ℝ) * r ^ 2) := Finset.sum_le_sum hterm
    _ = (bad.card : ℝ) * Real.exp (-(n : ℝ) * r ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (s.card - 1 : ℝ) * Real.exp (-(n : ℝ) * r ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        rw [← hcard_sub]
        exact Nat.cast_le.mpr hcard_bad

/-- Maximum likelihood estimation over `s` (`|s| = M`) returns a model within Hellinger radius
`r ≥ 0` (strict failure `r < h`) except with probability at most `(M - 1) * exp (-n * r ^ 2)`. -/
theorem mle_hellingerDist_gt_le [Finite α]
    (s : Finset ι) (hs : s.Nonempty) (models : ι → _root_.PMF α)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ((iid (models i₀) n).toOuterMeasure
      {x | r < hellingerDist (models i₀) (models (mle s hs models x))}).toReal ≤
        (s.card - 1 : ℝ) * Real.exp (-(n : ℝ) * r ^ 2) :=
  mle_hellingerDist_pred_le s hs models hi₀ n hr
    (fun j => r < hellingerDist (models i₀) (models j))
    (by simp only [hellingerDist_self]; linarith)
    (fun _ hj => le_of_lt hj)

/-- Non-strict Hellinger radius bound `r ≤ h` for MLE when `0 < r`. -/
theorem mle_hellingerDist_ge_le [Finite α]
    (s : Finset ι) (hs : s.Nonempty) (models : ι → _root_.PMF α)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ((iid (models i₀) n).toOuterMeasure
      {x | r ≤ hellingerDist (models i₀) (models (mle s hs models x))}).toReal ≤
        (s.card - 1 : ℝ) * Real.exp (-(n : ℝ) * r ^ 2) :=
  mle_hellingerDist_pred_le s hs models hi₀ n hr.le
    (fun j => r ≤ hellingerDist (models i₀) (models j))
    (by simp only [hellingerDist_self]; linarith)
    (fun _ hj => hj)

/-- Maximum likelihood estimator over an indexed family of `M` candidate distributions (`M > 0`).
-/
@[expose] noncomputable def mleFin {M : ℕ} [NeZero M] (models : Fin M → _root_.PMF α)
    {n : ℕ} (x : Fin n → α) : Fin M :=
  mle Finset.univ Finset.univ_nonempty models x

/-- MLE over `M` models (`M > 0`) returns a model within Hellinger radius `r ≥ 0` except with
probability at most `(M - 1) * Real.exp (-n * r ^ 2)` when `models i₀` generates the samples. -/
theorem mleFin_hellingerDist_gt_le [Finite α] {M : ℕ} [NeZero M]
    (models : Fin M → _root_.PMF α) (i₀ : Fin M) (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ((iid (models i₀) n).toOuterMeasure
      {x | r < hellingerDist (models i₀) (models (mleFin models x))}).toReal ≤
        (M - 1 : ℝ) * Real.exp (-(n : ℝ) * r ^ 2) := by
  simpa only [mleFin, Finset.card_univ, Fintype.card_fin] using
    mle_hellingerDist_gt_le Finset.univ Finset.univ_nonempty models (Finset.mem_univ i₀) n hr

/-- Non-strict Hellinger radius bound for `mleFin` when `0 < r`. -/
theorem mleFin_hellingerDist_ge_le [Finite α] {M : ℕ} [NeZero M]
    (models : Fin M → _root_.PMF α) (i₀ : Fin M) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ((iid (models i₀) n).toOuterMeasure
      {x | r ≤ hellingerDist (models i₀) (models (mleFin models x))}).toReal ≤
        (M - 1 : ℝ) * Real.exp (-(n : ℝ) * r ^ 2) := by
  simpa only [mleFin, Finset.card_univ, Fintype.card_fin] using
    mle_hellingerDist_ge_le Finset.univ Finset.univ_nonempty models (Finset.mem_univ i₀) n hr

/-- Sample-complexity helper: if `c ≤ K`, `0 < K`, `0 < a`, `0 < δ`, and
`Real.log (K / δ) / a ≤ n`, then `c * Real.exp (-(a * n)) ≤ δ`. -/
theorem mul_exp_neg_le_of_log {c K n a δ : ℝ}
    (hcK : c ≤ K) (hK : 0 < K) (ha : 0 < a) (hδ : 0 < δ)
    (hn : Real.log (K / δ) / a ≤ n) :
    c * Real.exp (-(a * n)) ≤ δ := by
  have hlog : Real.log (K / δ) ≤ a * n := ((div_le_iff₀ ha).mp hn).trans_eq (mul_comm n a)
  have hexp : Real.exp (-(a * n)) ≤ δ / K := by
    calc Real.exp (-(a * n))
        ≤ Real.exp (-Real.log (K / δ)) := Real.exp_le_exp.mpr (by linarith)
      _ = (K / δ)⁻¹ := by rw [Real.exp_neg, Real.exp_log (div_pos hK hδ)]
      _ = δ / K := inv_div K δ
  calc c * Real.exp (-(a * n))
      ≤ K * Real.exp (-(a * n)) := mul_le_mul_of_nonneg_right hcK (Real.exp_pos _).le
    _ ≤ K * (δ / K) := mul_le_mul_of_nonneg_left hexp hK.le
    _ = δ := mul_div_cancel₀ δ hK.ne'

/-- Sample complexity of `mleFin`: `n ≥ log (M / δ) / r ^ 2` suffices for `mleFin` to succeed
within Hellinger radius `r > 0` with failure probability at most `δ > 0`. -/
theorem mleFin_hellingerDist_ge_le_of_log [Finite α] {M : ℕ} [NeZero M]
    (models : Fin M → _root_.PMF α) (i₀ : Fin M) {n : ℕ} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ)
    (hn : Real.log ((M : ℝ) / δ) / r ^ 2 ≤ n) :
    ((iid (models i₀) n).toOuterMeasure
      {x | r ≤ hellingerDist (models i₀) (models (mleFin models x))}).toReal ≤ δ := by
  refine (mleFin_hellingerDist_ge_le models i₀ n hr).trans ?_
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  rw [show -(n : ℝ) * r ^ 2 = -(r ^ 2 * (n : ℝ)) by ring]
  exact mul_exp_neg_le_of_log (by linarith) (by linarith) (sq_pos_of_pos hr) hδ hn

end Cslib.Probability.HypothesisSelection
