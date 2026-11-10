/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.PACLearning.ERM
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Constructions.Pi
import Complexity.Probability.Concentration
import Complexity.Probability.PMF.Event
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
`Bool` labels. Hoeffding's inequality is the library's finite-PMF form
(`Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge`), applied to the Bernoulli indicators of
misclassification.

## Main definitions

- `IsRepresentative D C ε S`: the sample `S` is `ε`-representative for `C` under `D`.

## Main results

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
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine prob_le_one.trans ?_
    rw [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero, mul_one, ENNReal.ofReal_ofNat]
    norm_num
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
  set q : PMF Bool := (D.map f).toPMF
  have hq : q.toMeasure = D.map f := Measure.toPMF_toMeasure _
  have hmap : (Measure.pi fun _ : Fin m => D).map (fun S i => f (S i)) =
      (Cslib.Probability.PMF.pi fun _ : Fin m => q).toMeasure := by
    rw [Cslib.Probability.PMF.toMeasure_pi, hq]
    exact Measure.pi_map_pi (fun _ => hf.aemeasurable)
  have hfm : Measurable fun (S : Fin m → α × β) i => f (S i) :=
    measurable_pi_iff.2 fun i => hf.comp (measurable_pi_apply i)
  have hqt : (q true).toReal = (error D h).toReal := by
    rw [Measure.toPMF_apply, Measure.map_apply hf (measurableSet_singleton _)]
    congr 2
    ext p; simp [f]
  set score : Fin m → Bool → ℝ := fun _ b => if b = true then 1 else 0
  have hscore : ∀ i b, b ∈ q.support → score i b ∈ Set.Icc (0 : ℝ) 1 := by
    intro i b _
    cases b <;> simp [score]
  have hcount (S : Fin m → α × β) :
      (empiricalMiscount h S : ℝ) = ∑ i, score i (f (S i)) := by
    simp only [empiricalMiscount, score, f, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero, decide_eq_true_eq]
  have hmean : ∑ i : Fin m, ∑ a, (q a).toReal * score i a = m * (error D h).toReal := by
    simp only [score, Fintype.sum_bool, ite_true, mul_one, Bool.false_eq_true, ite_false,
      mul_zero, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hqt]
  have hmR : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hpre : {S : LabeledSample α β m |
      ε ≤ |(empiricalMiscount h S : ℝ) / m - (error D h).toReal|} =
      (fun S i => f (S i)) ⁻¹' {b : Fin m → Bool |
        m * ε ≤ |∑ i, score i (b i) - ∑ i : Fin m, ∑ a, (q a).toReal * score i a|} := by
    ext S
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hmean, ← hcount]
    rw [show (empiricalMiscount h S : ℝ) - m * (error D h).toReal =
        m * ((empiricalMiscount h S : ℝ) / m - (error D h).toReal) by field_simp,
      abs_mul, abs_of_pos hmR, mul_le_mul_iff_right₀ hmR]
  rw [hpre, ← Measure.map_apply hfm (Set.toFinite _).measurableSet, hmap,
    PMF.toMeasure_apply_eq_toOuterMeasure]
  have hne : (Cslib.Probability.PMF.pi fun _ : Fin m => q).toOuterMeasure
      {b : Fin m → Bool |
        m * ε ≤ |∑ i, score i (b i) - ∑ i : Fin m, ∑ a, (q a).toReal * score i a|} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (Cslib.Probability.PMF.toOuterMeasure_le_one _ _)
  rw [ENNReal.le_ofReal_iff_toReal_le hne (by positivity)]
  refine (Cslib.Probability.PMF.pi_sum_abs_sub_mean_ge (fun _ : Fin m => q) score
    (bound := 1) zero_le_one hscore (by positivity)).trans_eq ?_
  congr 2
  simp only [Fintype.card_fin, one_pow, mul_one]
  field_simp

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

end Cslib.MachineLearning.PACLearning
