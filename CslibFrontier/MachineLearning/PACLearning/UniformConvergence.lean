/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.ERM
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.Product.MapMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Uniform convergence of empirical errors

A labeled sample is *ε-representative* for a class `C` under a distribution `D` on `α × β` if the
empirical error of every hypothesis of `C` on the sample is within `ε` of its true error
[ShalevShwartzBenDavid2014, Definition 4.1]. For a single hypothesis, Hoeffding's inequality bounds
the probability that `m` i.i.d. examples misestimate its error by `ε` by `2 exp (-2 m ε²)`
[Hoeffding1963]. A union bound gives uniform convergence for a finite class
[ShalevShwartzBenDavid2014, Section 4.2]. On an `ε / 2`-representative sample every empirical risk
minimizer is within `ε` of the best error in the class [ShalevShwartzBenDavid2014, Lemma 4.2]. This
is the agnostic route to PAC learning: no concept of the class needs to fit the distribution.

The domain and label spaces are arbitrary measurable spaces. Each hypothesis needs a measurable
misclassification set; `measurableSet_misclassified` supplies this for measurable hypotheses with
`Bool` labels. Hoeffding's inequality is the library's finite-PMF form for `[0, 1]` scores
(`Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge_card_mul`), applied to the Bernoulli indicator of a
measurable event; the empirical error of a hypothesis is the relative frequency of its
misclassification set. Uniform convergence for infinite classes of finite VC dimension is in
`VCUniformConvergence.lean`.

## Main definitions

- `IsRepresentative D C ε S`: the sample `S` is `ε`-representative for `C` under `D`.

## Main results

- `measure_pi_le_abs_card_filter_div_sub_measure`: Hoeffding's inequality for the relative
  frequency of one measurable event.
- `measure_pi_le_abs_empiricalMiscount_div_sub_error`: Hoeffding's inequality for the empirical
  error of one hypothesis.
- `measure_pi_not_isRepresentative_le`: uniform convergence for a finite class.
- `IsRepresentative.error_le_optimalError_add`: ERM on an `ε / 2`-representative sample is
  `ε`-optimal.

## References

* [W. Hoeffding, *Probability inequalities for sums of bounded random variables*][Hoeffding1963]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [DecidableEq β]

/-- A labeled sample `S` is *ε-representative* for the class `C` under `D` if the empirical error
`empiricalMiscount h S / m` of every `h ∈ C` is within `ε` of its true error
[ShalevShwartzBenDavid2014, Definition 4.1]. -/
@[expose] def IsRepresentative (D : Measure (α × β)) (C : ConceptClass α β) (ε : ℝ) {m : ℕ}
    (S : LabeledSample α β m) : Prop :=
  ∀ h ∈ C, |(empiricalMiscount h S : ℝ) / m - (error D h).toReal| ≤ ε

section Hoeffding

variable {Z : Type*} [MeasurableSpace Z]

/-- **Hoeffding's inequality for a relative frequency** [Hoeffding1963]: under `m` i.i.d. samples
from `μ`, the fraction of sample points where a measurable `g : Z → Bool` is `true` differs from
`μ {g = true}` by at least `ε` with probability at most `2 exp (-2 m ε²)`. -/
theorem measure_pi_le_abs_card_filter_div_sub_measure (μ : Measure Z) [IsProbabilityMeasure μ]
    {g : Z → Bool} (hg : Measurable g) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => μ)
        {S | ε ≤ |((Finset.univ.filter fun i => g (S i) = true).card : ℝ) / m -
          (μ {z | g z = true}).toReal|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * m * ε ^ 2)) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine prob_le_one.trans ?_
    rw [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero, mul_one, ENNReal.ofReal_ofNat]
    norm_num
  set q : PMF Bool := (μ.map g).toPMF
  have hmap : (Measure.pi fun _ : Fin m => μ).map (fun S i => g (S i)) =
      (Cslib.Probability.PMF.pi fun _ : Fin m => q).toMeasure :=
    Cslib.Probability.PMF.map_measurePi_eq_toMeasure_pi _ fun _ => hg.aemeasurable
  have hgm : Measurable fun (S : Fin m → Z) i => g (S i) :=
    measurable_pi_iff.2 fun i => hg.comp (measurable_pi_apply i)
  have hqt : (q true).toReal = (μ {z | g z = true}).toReal := by
    rw [Measure.toPMF_apply, Measure.map_apply hg (measurableSet_singleton _)]
    rfl
  set score : Fin m → Bool → ℝ := fun _ b => if b = true then 1 else 0
  have hscore : ∀ i b, b ∈ q.support → score i b ∈ Set.Icc (0 : ℝ) 1 := by
    intro i b _
    cases b <;> simp [score]
  have hcount (S : Fin m → Z) :
      ((Finset.univ.filter fun i => g (S i) = true).card : ℝ) = ∑ i, score i (g (S i)) := by
    simp only [score, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hmean : ∑ i : Fin m, ∑ a, (q a).toReal * score i a = m * (μ {z | g z = true}).toReal := by
    simp only [score, Fintype.sum_bool, ite_true, mul_one, Bool.false_eq_true, ite_false,
      mul_zero, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hqt]
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hpre : {S : Fin m → Z | ε ≤ |((Finset.univ.filter fun i => g (S i) = true).card : ℝ) / m -
          (μ {z | g z = true}).toReal|} =
      (fun S i => g (S i)) ⁻¹' {b : Fin m → Bool |
        m * ε ≤ |∑ i, score i (b i) - ∑ i : Fin m, ∑ a, (q a).toReal * score i a|} := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hmean, ← hcount]
    rw [show ((Finset.univ.filter fun i => g (S i) = true).card : ℝ) -
          m * (μ {z | g z = true}).toReal =
        m * (((Finset.univ.filter fun i => g (S i) = true).card : ℝ) / m -
          (μ {z | g z = true}).toReal) by field_simp,
      abs_mul, abs_of_pos hmR, mul_le_mul_iff_right₀ hmR]
  rw [hpre, ← Measure.map_apply hgm (Set.toFinite _).measurableSet, hmap,
    PMF.toMeasure_apply_eq_toOuterMeasure]
  have hne : (Cslib.Probability.PMF.pi fun _ : Fin m => q).toOuterMeasure
      {b : Fin m → Bool |
        m * ε ≤ |∑ i, score i (b i) - ∑ i : Fin m, ∑ a, (q a).toReal * score i a|} ≠ ⊤ :=
    Cslib.Probability.PMF.toOuterMeasure_ne_top _ _
  rw [ENNReal.le_ofReal_iff_toReal_le hne (by positivity)]
  simpa only [Fintype.card_fin] using
    Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge_card_mul (fun _ : Fin m => q) score hscore hε

end Hoeffding

/-- **Hoeffding's inequality for the empirical error of one hypothesis** [Hoeffding1963]: under `m`
i.i.d. examples from `D`, the empirical error of `h` differs from `error D h` by at least `ε` with
probability at most `2 exp (-2 m ε²)`. The domain is an arbitrary measurable space; only the
misclassification set of `h` must be measurable. -/
theorem measure_pi_le_abs_empiricalMiscount_div_sub_error (D : Measure (α × β))
    [IsProbabilityMeasure D] {h : α → β} (hh : MeasurableSet {p : α × β | h p.1 ≠ p.2})
    (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => D)
        {S | ε ≤ |(empiricalMiscount h S : ℝ) / m - (error D h).toReal|} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * m * ε ^ 2)) := by
  set f : α × β → Bool := fun p => decide (h p.1 ≠ p.2)
  have hf : Measurable f := by
    refine measurable_to_countable' fun b => ?_
    cases b
    · have : f ⁻¹' {false} = {p : α × β | h p.1 ≠ p.2}ᶜ := by
        ext p; simp [f]
      rw [this]; exact hh.compl
    · have : f ⁻¹' {true} = {p : α × β | h p.1 ≠ p.2} := by
        ext p; simp [f]
      rw [this]; exact hh
  have hset : {p : α × β | f p = true} = {p : α × β | h p.1 ≠ p.2} := by
    ext p
    simp only [f, Set.mem_ofPred_eq, decide_eq_true_eq]
  have hcount (S : LabeledSample α β m) :
      empiricalMiscount h S = (Finset.univ.filter fun i => f (S i) = true).card := by
    simp only [empiricalMiscount, f, decide_eq_true_eq]
  have h := measure_pi_le_abs_card_filter_div_sub_measure D hf m hε
  simp only [hset] at h
  simpa only [hcount, error] using h

/-- **Uniform convergence for a finite class** [ShalevShwartzBenDavid2014, Section 4.2]: `m` i.i.d.
examples fail to be `ε`-representative for a finite class `H` with probability at most
`|H| · 2 exp (-2 m ε²)`. -/
theorem measure_pi_not_isRepresentative_le (D : Measure (α × β)) [IsProbabilityMeasure D]
    {H : Finset (α → β)} (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2})
    (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => D) {S | ¬ IsRepresentative D (H : Set (α → β)) ε S} ≤
      H.card * ENNReal.ofReal (2 * Real.exp (-2 * m * ε ^ 2)) := by
  have hsub : {S : LabeledSample α β m | ¬ IsRepresentative D (H : Set (α → β)) ε S} ⊆
      ⋃ h ∈ H, {S | ε ≤ |(empiricalMiscount h S : ℝ) / m - (error D h).toReal|} := by
    intro S hS
    simp only [IsRepresentative, Finset.mem_coe, not_forall, not_le, Set.mem_ofPred_eq] at hS
    obtain ⟨h, hh, hlt⟩ := hS
    exact Set.mem_biUnion hh hlt.le
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc ∑ h ∈ H, Measure.pi (fun _ : Fin m => D)
        {S | ε ≤ |(empiricalMiscount h S : ℝ) / m - (error D h).toReal|}
      ≤ ∑ _h ∈ H, ENNReal.ofReal (2 * Real.exp (-2 * m * ε ^ 2)) :=
        Finset.sum_le_sum fun h hh =>
          measure_pi_le_abs_empiricalMiscount_div_sub_error D (hH h hh) m hε
    _ = H.card * ENNReal.ofReal (2 * Real.exp (-2 * m * ε ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Uniform convergence for a finite class**, sample-size form: `m` i.i.d. examples fail to be
`ε`-representative for a finite class `H` with probability at most `δ` once
`log (2 |H| / δ) ≤ 2 m ε²`. -/
theorem measure_pi_not_isRepresentative_le_of_log_le (D : Measure (α × β))
    [IsProbabilityMeasure D] {H : Finset (α → β)}
    (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2}) {m : ℕ} {ε δ : ℝ} (hε : 0 ≤ ε)
    (hδ : 0 < δ) (hm : Real.log (2 * H.card / δ) ≤ 2 * m * ε ^ 2) :
    Measure.pi (fun _ : Fin m => D) {S | ¬ IsRepresentative D (H : Set (α → β)) ε S} ≤
      ENNReal.ofReal δ := by
  refine (measure_pi_not_isRepresentative_le D hH m hε).trans ?_
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases Nat.eq_zero_or_pos H.card with h0 | hn
  · rw [h0, Nat.cast_zero, zero_mul]
    exact hδ.le
  have hn' : (0 : ℝ) < 2 * H.card := by positivity
  rw [Real.log_div hn'.ne' hδ.ne'] at hm
  calc (H.card : ℝ) * (2 * Real.exp (-2 * m * ε ^ 2)) =
        Real.exp (Real.log (2 * H.card) + -(2 * m * ε ^ 2)) := by
        rw [Real.exp_add, Real.exp_log hn', show -(2 * (m : ℝ) * ε ^ 2) = -2 * m * ε ^ 2 by ring]
        ring
    _ ≤ Real.exp (Real.log δ) := Real.exp_le_exp.2 (by linarith)
    _ = δ := Real.exp_log hδ

/-- **ERM on a representative sample** [ShalevShwartzBenDavid2014, Lemma 4.2]: on an
`ε / 2`-representative sample for `C`, every empirical risk minimizer for `C` outputs a hypothesis
whose error is at most `optimalError D C + ε`. The class need not be finite. -/
theorem IsRepresentative.error_le_optimalError_add {D : Measure (α × β)} [IsProbabilityMeasure D]
    {C : ConceptClass α β} {m : ℕ} {A : Learner α β m} (hA : IsERM A C) {S : LabeledSample α β m}
    {ε : ℝ} (hS : IsRepresentative D C (ε / 2) S) :
    error D (A S) ≤ optimalError D C + ENNReal.ofReal ε := by
  obtain ⟨hAC, hmin⟩ := hA S
  rw [optimalError, ENNReal.iInf_add]
  refine le_iInf fun h => ?_
  rw [ENNReal.iInf_add]
  refine le_iInf fun hh => ?_
  have hg := (abs_le.1 (hS _ hAC)).1
  have hh' := (abs_le.1 (hS h hh)).2
  have hmis : (empiricalMiscount (A S) S : ℝ) / m ≤ (empiricalMiscount h S : ℝ) / m :=
    div_le_div_of_nonneg_right (by exact_mod_cast hmin h hh) (Nat.cast_nonneg _)
  have hreal : (error D (A S)).toReal ≤ (error D h).toReal + ε := by linarith
  have hfin : ∀ g : α → β, error D g ≠ ⊤ := fun g => measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal (hfin (A S)), ← ENNReal.ofReal_toReal (hfin h),
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg (by
      have : 0 ≤ ε / 2 := (abs_nonneg _).trans (hS h hh)
      linarith)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- An `ε`-representative sample is `ε'`-representative for every `ε' ≥ ε`. -/
theorem IsRepresentative.mono {D : Measure (α × β)} {C : ConceptClass α β} {ε ε' : ℝ} {m : ℕ}
    {S : LabeledSample α β m} (hS : IsRepresentative D C ε S) (hε : ε ≤ ε') :
    IsRepresentative D C ε' S := fun h hh => (hS h hh).trans hε

end Cslib.MachineLearning.PACLearning
