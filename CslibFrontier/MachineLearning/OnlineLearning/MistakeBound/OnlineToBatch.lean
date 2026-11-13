/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Basic
public import CslibFrontier.MachineLearning.PACLearning.RealizableSample
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# From mistake bounds to PAC learning

A deterministic online learner `A` with mistake bound `M` on a class `C` is turned into a batch
learner for distributions realizable by `C`. Run `A` on `m + 1` i.i.d. examples `z₀, …, z_m` from
`D`. The hypothesis `prefixHypothesis A S t` that `A` holds after the first `t` examples depends
only on them, so its error is the probability that `A` errs on the fresh example `z_t`
(`lintegral_error_prefixHypothesis_eq`). Summing over `t ≤ m`, the expected total error of the
`m + 1` prefix hypotheses is the expected number of mistakes of `A` on `z₀, …, z_m`, at most `M`
(`sum_lintegral_error_prefixHypothesis_le`). So a prefix hypothesis chosen uniformly at random has
expected error at most `M / (m + 1)`: this is the online-to-batch conversion of
[Littlestone1989] and [CesaBianchiConconiGentile2004] (locators unverified).

The library's `IsPACLearnerFor` asks for a deterministic learner. On a sample of size `m`, the
majority vote `prefixMajority A S` of the `m + 1` prefix hypotheses after `0, …, m` examples errs
only where at least half of them err, so its error is at most twice their average and its expected
error is at most `2 M / (m + 1)` (`lintegral_error_prefixMajority_le`). Markov's inequality then
gives `IsPACLearnerFor m ε δ C (realizableDistributions C)` whenever `2 M ≤ ε δ (m + 1)`
(`isPACLearnerFor_prefixMajority`). The sample size is `O(M / (ε δ))`; the confidence dependence is
`1 / δ`, not the `log (1 / δ)` of Littlestone's hypothesis-testing conversion, which is not
formalized here.

**Measurability.** The argument applies Fubini's theorem to the event that `A` errs on the fresh
example, so `A` must be measurable as a function of the history and the instance, for each history
length (`IsMeasurableLearner`). Every learner on a countable domain with measurable singletons is
measurable (`isMeasurableLearner_of_countable`), so on such domains a finite optimal mistake bound
implies PAC learnability (`isPACLearnable_of_optimalMistakeBound_ne_top`).

Mistake bound ⇒ PAC learnability also follows from the sample compression scheme of a mistake-bound
learner and from the finite VC dimension of classes of finite Littlestone dimension; this file gives
the direct online-to-batch route with its explicit sample size.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.IsMeasurableLearner`: the prediction is
  measurable in the history and the instance, for each history length.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.prefixHypothesis`: the hypothesis of the
  learner after the first `t` examples of a sample.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.prefixMajority`: the majority vote of the
  prefix hypotheses after `0, …, m` examples of a sample of size `m`.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.lintegral_error_prefixHypothesis_eq`: the
  expected error of the hypothesis after `t` examples is the probability of a mistake on example
  `t`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.sum_lintegral_error_prefixHypothesis_le`: the
  expected errors of the hypotheses after `0, …, m` examples sum to at most the mistake bound.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.lintegral_error_prefixMajority_le`: the
  majority vote has expected error at most `2 M / (m + 1)`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.isPACLearnerFor_prefixMajority`: a mistake
  bound `M` gives an `(ε, δ)`-PAC learner over the realizable distributions from `m` examples when
  `2 M ≤ ε δ (m + 1)`.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.isPACLearnable_of_optimalMistakeBound_ne_top`:
  on a countable domain with measurable singletons, a class with a finite optimal mistake bound is
  PAC learnable over its realizable distributions.

## References

* [N. Littlestone, *From on-line to batch learning*][Littlestone1989]
* [N. Cesa-Bianchi, A. Conconi, C. Gentile, *On the generalization ability of on-line learning
  algorithms*][CesaBianchiConconiGentile2004]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

open PACLearning (ConceptClass LabeledSample error IsPACLearnerFor IsPACLearnable
  realizableDistributions IsRealizableBy)

variable {α : Type*} [MeasurableSpace α]

/-- An online learner is *measurable* if, for every history length `n`, its prediction is a
measurable function of the history (a sample of length `n`) and the current instance. -/
@[expose] def IsMeasurableLearner (A : OnlineLearner α) : Prop :=
  ∀ n : ℕ, Measurable fun p : (Fin n → α × Bool) × α => A (List.ofFn p.1) p.2

/-- On a countable domain with measurable singletons every online learner is measurable. -/
theorem isMeasurableLearner_of_countable [Countable α] [MeasurableSingletonClass α]
    (A : OnlineLearner α) : IsMeasurableLearner A :=
  fun _ => measurable_of_countable _

/-- The hypothesis of the online learner `A` after the first `t` examples of the sample `S`. If
`t ≥ m`, it has seen the whole sample. -/
@[expose] def prefixHypothesis {m : ℕ} (A : OnlineLearner α) (S : LabeledSample α Bool m)
    (t : ℕ) : α → Bool :=
  A ((List.ofFn S).take t)

/-- The majority vote of the hypotheses of `A` after `0, 1, …, m` examples of a sample `S` of
size `m`: it predicts `true` iff more than half of these `m + 1` hypotheses do. -/
@[expose] def prefixMajority {m : ℕ} (A : OnlineLearner α) (S : LabeledSample α Bool m) :
    α → Bool := fun x =>
  decide (m + 1 < 2 *
    (Finset.univ.filter fun t : Fin (m + 1) => prefixHypothesis A S t x = true).card)

/-! ### Measurability -/

/-- The prediction of a measurable learner after `t` examples is measurable in the sample and the
instance. -/
private theorem IsMeasurableLearner.measurable_prefix {A : OnlineLearner α}
    (hA : IsMeasurableLearner A) (m t : ℕ) :
    Measurable fun p : LabeledSample α Bool m × α => prefixHypothesis A p.1 t p.2 := by
  have hg : Measurable fun p : LabeledSample α Bool m × α =>
      (Fin.take (min t m) (min_le_right t m) p.1, p.2) :=
    (Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_fst).prodMk
      measurable_snd
  have h := (hA (min t m)).comp hg
  simp only [Function.comp_def, Fin.ofFn_take_eq_take_ofFn] at h
  simpa only [prefixHypothesis, List.take_eq_take_min (i := t), List.length_ofFn] using h

/-- The set of samples on which the hypothesis after `t` examples misclassifies example `i`. -/
private theorem IsMeasurableLearner.measurableSet_prefix_ne {A : OnlineLearner α}
    (hA : IsMeasurableLearner A) {m : ℕ} (t : ℕ) (i : Fin m) :
    MeasurableSet {S : LabeledSample α Bool m | prefixHypothesis A S t (S i).1 ≠ (S i).2} := by
  have h : Measurable fun S : LabeledSample α Bool m => prefixHypothesis A S t (S i).1 :=
    (hA.measurable_prefix m t).comp (measurable_id.prodMk (by fun_prop))
  exact (measurableSet_eq_fun h (by fun_prop)).compl

/-- The misclassification set of `(S, z) ↦ prefixHypothesis A S t` is measurable. -/
private theorem IsMeasurableLearner.measurableSet_misclassified {A : OnlineLearner α}
    (hA : IsMeasurableLearner A) (m t : ℕ) :
    MeasurableSet {p : LabeledSample α Bool m × (α × Bool) |
      prefixHypothesis A p.1 t p.2.1 ≠ p.2.2} := by
  have h : Measurable fun p : LabeledSample α Bool m × (α × Bool) =>
      prefixHypothesis A p.1 t p.2.1 :=
    (hA.measurable_prefix m t).comp (measurable_fst.prodMk (by fun_prop))
  exact (measurableSet_eq_fun h (by fun_prop)).compl

/-- The error of the hypothesis after `t` examples is measurable in the sample. -/
private theorem IsMeasurableLearner.measurable_error_prefix {A : OnlineLearner α}
    (hA : IsMeasurableLearner A) (D : Measure (α × Bool)) [SFinite D] (m t : ℕ) :
    Measurable fun S : LabeledSample α Bool m => error D (prefixHypothesis A S t) :=
  measurable_measure_prodMk_left (hA.measurableSet_misclassified m t)

/-- The total error of the hypotheses after `0, …, m` examples is measurable in the sample. -/
private theorem IsMeasurableLearner.measurable_sum_error_prefix {A : OnlineLearner α}
    (hA : IsMeasurableLearner A) (D : Measure (α × Bool)) [SFinite D] (m : ℕ) :
    Measurable fun S : LabeledSample α Bool m =>
      ∑ t : Fin (m + 1), error D (prefixHypothesis A S t) :=
  Finset.measurable_sum Finset.univ fun (t : Fin (m + 1)) _ => hA.measurable_error_prefix D m t

/-- The expected total error of the hypotheses after `0, …, m` examples is the sum of their
expected errors. -/
private theorem IsMeasurableLearner.lintegral_two_mul_sum_error_prefix {A : OnlineLearner α}
    (hA : IsMeasurableLearner A) (D : Measure (α × Bool)) [SFinite D] (m : ℕ) :
    ∫⁻ S, 2 * ∑ t : Fin (m + 1), error D (prefixHypothesis A S t)
        ∂Measure.pi (fun _ : Fin m => D) =
      2 * ∑ t : Fin (m + 1), ∫⁻ S, error D (prefixHypothesis A S t)
        ∂Measure.pi (fun _ : Fin m => D) := by
  rw [lintegral_const_mul _ (hA.measurable_sum_error_prefix D m),
    lintegral_finsetSum _ fun (t : Fin (m + 1)) _ => hA.measurable_error_prefix D m t]

/-! ### The expected error of a prefix hypothesis -/

omit [MeasurableSpace α] in
private theorem prefixHypothesis_removeNth {m : ℕ} (A : OnlineLearner α)
    (S : LabeledSample α Bool (m + 1)) (t : Fin (m + 1)) :
    prefixHypothesis A (t.removeNth S) t = prefixHypothesis A S t := by
  unfold prefixHypothesis
  congr 1
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn]
    omega
  · intro i h₁ h₂
    simp only [List.length_take, List.length_ofFn] at h₁ h₂
    simp only [List.getElem_take, List.getElem_ofFn, Fin.removeNth]
    congr 1
    ext
    simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc]
    split_ifs with h <;> simp_all

/-- **The expected error of a prefix hypothesis.** For i.i.d. examples, the expected error of the
hypothesis that a measurable learner `A` holds after the first `t` of `m` examples is the
probability that `A` errs on example `t` of `m + 1` examples: that example is fresh. -/
theorem lintegral_error_prefixHypothesis_eq {A : OnlineLearner α} (hA : IsMeasurableLearner A)
    (D : Measure (α × Bool)) [IsProbabilityMeasure D] {m : ℕ} (t : Fin (m + 1)) :
    ∫⁻ S, error D (prefixHypothesis A S t) ∂Measure.pi (fun _ : Fin m => D) =
      Measure.pi (fun _ : Fin (m + 1) => D)
        {S | prefixHypothesis A S t (S t).1 ≠ (S t).2} := by
  set F : Set ((α × Bool) × LabeledSample α Bool m) :=
    {q | prefixHypothesis A q.2 t q.1.1 ≠ q.1.2}
  have hF : MeasurableSet F := by
    have h := (hA.measurableSet_misclassified m t).preimage
      (measurable_snd.prodMk measurable_fst :
        Measurable fun q : (α × Bool) × LabeledSample α Bool m => (q.2, q.1))
    exact h
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => D) t
  have hset : {S : LabeledSample α Bool (m + 1) | prefixHypothesis A S t (S t).1 ≠ (S t).2} =
      MeasurableEquiv.piFinSuccAbove (fun _ => α × Bool) t ⁻¹' F := by
    ext S
    simp only [mem_ofPred_eq, mem_preimage, F, MeasurableEquiv.piFinSuccAbove_apply,
      Fin.insertNthEquiv_symm_apply]
    rw [prefixHypothesis_removeNth]
  rw [hset, he.measure_preimage hF.nullMeasurableSet, Measure.prod_apply_symm hF]
  rfl

/-! ### Summing over prefixes -/

omit [MeasurableSpace α] in
/-- The mistakes of `A` on the sequence of examples of `S` are the rounds `t` whose prefix
hypothesis misclassifies example `t`. -/
private theorem mistakes_ofFn_eq_card {m : ℕ} (A : OnlineLearner α) (S : LabeledSample α Bool m) :
    mistakes A (List.ofFn S) =
      (Finset.univ.filter fun t : Fin m => prefixHypothesis A S t (S t).1 ≠ (S t).2).card := by
  rw [mistakes_eq_card]
  refine Finset.card_bij (fun t _ => Fin.cast (List.length_ofFn) t) ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    simpa [prefixHypothesis, Fin.cast] using ht
  · intro a _ b _ h
    exact Fin.cast_injective _ h
  · intro t ht
    refine ⟨Fin.cast List.length_ofFn.symm t, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    simpa [prefixHypothesis] using ht

omit [MeasurableSpace α] in
/-- A sample labelled by a concept of `C` is realizable by `C` as a list. -/
private theorem realizable_ofFn {C : ConceptClass α Bool} {m : ℕ} {S : LabeledSample α Bool m}
    (hS : PACLearning.Realizable C S) : Realizable C (List.ofFn S) := by
  obtain ⟨c, hc, hcS⟩ := hS
  refine realizable_iff.mpr ⟨c, hc, fun p hp => ?_⟩
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact (hcS i).symm

/-- **Online-to-batch for mistake bounds** [Littlestone1989] [CesaBianchiConconiGentile2004]
(locators unverified). If the measurable learner `A` has mistake bound `M` on `C` and `D` is
realizable by `C`, the expected errors of the hypotheses of `A` after `0, 1, …, m` i.i.d.
examples sum to at most `M`. So the hypothesis after a uniformly random number of examples in
`{0, …, m}` has expected error at most `M / (m + 1)`. -/
theorem sum_lintegral_error_prefixHypothesis_le {A : OnlineLearner α} (hA : IsMeasurableLearner A)
    {C : ConceptClass α Bool} {M : ℕ} (hM : mistakeBound A C ≤ M) {D : Measure (α × Bool)}
    [IsProbabilityMeasure D] (hD : IsRealizableBy D C) (m : ℕ) :
    ∑ t : Fin (m + 1), ∫⁻ S, error D (prefixHypothesis A S t) ∂Measure.pi (fun _ : Fin m => D) ≤
      M := by
  set μ := Measure.pi (fun _ : Fin (m + 1) => D)
  simp_rw [lintegral_error_prefixHypothesis_eq hA D]
  have hmeas := fun t : Fin (m + 1) => hA.measurableSet_prefix_ne (t : ℕ) t
  calc ∑ t : Fin (m + 1), μ {S | prefixHypothesis A S t (S t).1 ≠ (S t).2}
      = ∫⁻ S, ∑ t : Fin (m + 1),
          {S : LabeledSample α Bool (m + 1) | prefixHypothesis A S t (S t).1 ≠ (S t).2}.indicator
            1 S ∂μ := by
        rw [lintegral_finsetSum _ fun t _ => measurable_one.indicator (hmeas t)]
        simp only [lintegral_indicator_one (hmeas _)]
    _ ≤ ∫⁻ _, (M : ℝ≥0∞) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hD.ae_realizable (m + 1)] with S hS
        have hcount : ∑ t : Fin (m + 1),
            {S : LabeledSample α Bool (m + 1) | prefixHypothesis A S t (S t).1 ≠ (S t).2}.indicator
              1 S = (mistakes A (List.ofFn S) : ℝ≥0∞) := by
          rw [mistakes_ofFn_eq_card, Finset.card_filter, Nat.cast_sum]
          refine Finset.sum_congr rfl fun t _ => ?_
          by_cases h : prefixHypothesis A S t (S t).1 ≠ (S t).2 <;> simp [h]
        rw [hcount]
        exact_mod_cast (mistakes_le_mistakeBound (realizable_ofFn hS)).trans hM
    _ = M := by simp

/-! ### The majority vote -/

omit [MeasurableSpace α] in
/-- Where the majority vote errs, at least half of the prefix hypotheses err. -/
private theorem le_two_mul_card_of_prefixMajority_ne {m : ℕ} (A : OnlineLearner α)
    (S : LabeledSample α Bool m) {x : α} {y : Bool} (h : prefixMajority A S x ≠ y) :
    m + 1 ≤ 2 * (Finset.univ.filter fun t : Fin (m + 1) => prefixHypothesis A S t x ≠ y).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun t : Fin (m + 1) => prefixHypothesis A S t x = true)
  simp only [Finset.card_univ, Fintype.card_fin] at hsplit
  simp only [prefixMajority] at h
  cases y <;> simp_all <;> omega

/-- Pointwise in the sample, `m + 1` times the error of the majority vote is at most twice the
total error of the prefix hypotheses. -/
private theorem mul_error_prefixMajority_le {A : OnlineLearner α} (hA : IsMeasurableLearner A)
    (D : Measure (α × Bool)) {m : ℕ} (S : LabeledSample α Bool m) :
    (m + 1 : ℝ≥0∞) * error D (prefixMajority A S) ≤
      2 * ∑ t : Fin (m + 1), error D (prefixHypothesis A S t) := by
  have hmeas : ∀ t : ℕ, MeasurableSet {z : α × Bool | prefixHypothesis A S t z.1 ≠ z.2} :=
    fun t => measurable_prodMk_left (hA.measurableSet_misclassified m t)
  set f : α × Bool → ℝ≥0∞ := fun z => 2 * ∑ t : Fin (m + 1),
    {z : α × Bool | prefixHypothesis A S t z.1 ≠ z.2}.indicator 1 z
  have hsum : Measurable fun z : α × Bool => ∑ t : Fin (m + 1),
      {z : α × Bool | prefixHypothesis A S t z.1 ≠ z.2}.indicator (1 : α × Bool → ℝ≥0∞) z :=
    Finset.measurable_sum Finset.univ fun (t : Fin (m + 1)) _ => measurable_one.indicator (hmeas t)
  have hf : Measurable f := hsum.const_mul _
  have hsub : {z : α × Bool | prefixMajority A S z.1 ≠ z.2} ⊆ {z | (m + 1 : ℝ≥0∞) ≤ f z} := by
    intro z hz
    have h := le_two_mul_card_of_prefixMajority_ne A S hz
    have hsum : ∑ t : Fin (m + 1), {z : α × Bool | prefixHypothesis A S t z.1 ≠ z.2}.indicator 1 z
        = ((Finset.univ.filter fun t : Fin (m + 1) => prefixHypothesis A S t z.1 ≠ z.2).card :
          ℝ≥0∞) := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases ht : prefixHypothesis A S t z.1 ≠ z.2 <;> simp [ht]
    simp only [mem_ofPred_eq, f, hsum]
    exact_mod_cast h
  calc (m + 1 : ℝ≥0∞) * error D (prefixMajority A S)
      ≤ (m + 1 : ℝ≥0∞) * D {z | (m + 1 : ℝ≥0∞) ≤ f z} := by
        gcongr
        exact measure_mono hsub
    _ ≤ ∫⁻ z, f z ∂D := mul_meas_ge_le_lintegral hf _
    _ = 2 * ∑ t : Fin (m + 1), error D (prefixHypothesis A S t) := by
        rw [lintegral_const_mul _ hsum,
          lintegral_finsetSum _ fun (t : Fin (m + 1)) _ => measurable_one.indicator (hmeas t)]
        simp only [lintegral_indicator_one (hmeas _), error]

/-- **Expected error of the majority vote.** If the measurable learner `A` has mistake bound `M`
on `C` and `D` is realizable by `C`, the majority vote of the prefix hypotheses on `m` i.i.d.
examples has expected error at most `2 M / (m + 1)`, in the form `(m + 1) 𝔼 error ≤ 2 M`. -/
theorem lintegral_error_prefixMajority_le {A : OnlineLearner α} (hA : IsMeasurableLearner A)
    {C : ConceptClass α Bool} {M : ℕ} (hM : mistakeBound A C ≤ M) {D : Measure (α × Bool)}
    [IsProbabilityMeasure D] (hD : IsRealizableBy D C) (m : ℕ) :
    (m + 1 : ℝ≥0∞) * ∫⁻ S, error D (prefixMajority A S) ∂Measure.pi (fun _ : Fin m => D) ≤
      2 * M := by
  rw [← lintegral_const_mul' _ _ (by simp)]
  calc ∫⁻ S, (m + 1 : ℝ≥0∞) * error D (prefixMajority A S) ∂Measure.pi (fun _ : Fin m => D)
      ≤ ∫⁻ S, 2 * ∑ t : Fin (m + 1), error D (prefixHypothesis A S t)
          ∂Measure.pi (fun _ : Fin m => D) :=
        lintegral_mono fun S => mul_error_prefixMajority_le hA D S
    _ = 2 * ∑ t : Fin (m + 1), ∫⁻ S, error D (prefixHypothesis A S t)
          ∂Measure.pi (fun _ : Fin m => D) := hA.lintegral_two_mul_sum_error_prefix D m
    _ ≤ 2 * M := by
        gcongr
        exact sum_lintegral_error_prefixHypothesis_le hA hM hD m

/-- **Mistake bounds give PAC learners.** If the measurable learner `A` has mistake bound `M` on
`C`, then the majority vote of its prefix hypotheses is an `(ε, δ)`-PAC learner over the
distributions realizable by `C` from `m` examples whenever `2 M ≤ ε δ (m + 1)`. -/
theorem isPACLearnerFor_prefixMajority {A : OnlineLearner α} (hA : IsMeasurableLearner A)
    {C : ConceptClass α Bool} {M : ℕ} (hM : mistakeBound A C ≤ M) {m : ℕ}
    {ε δ : Set.Ioo (0 : ℝ≥0) 1} (hm : 2 * (M : ℝ≥0) ≤ ε.val * δ.val * (m + 1)) :
    IsPACLearnerFor m ε δ C (realizableDistributions C) := by
  refine ⟨prefixMajority A, fun D _ hD => ?_⟩
  rw [IsRealizableBy.optimalError_eq_zero hD, zero_add]
  set μ := Measure.pi (fun _ : Fin m => D)
  have hε : (ε.val : ℝ≥0∞) ≠ 0 := by simpa using ε.2.1.ne'
  have hpos : ((m + 1 : ℝ≥0∞)) ≠ 0 := by positivity
  have hmeas := (hA.measurable_sum_error_prefix D m).const_mul 2
  have hint : ∫⁻ S, 2 * ∑ t : Fin (m + 1), error D (prefixHypothesis A S t) ∂μ ≤ 2 * M := by
    rw [hA.lintegral_two_mul_sum_error_prefix D m]
    gcongr
    exact sum_lintegral_error_prefixHypothesis_le hA hM hD m
  have hsub : {S : LabeledSample α Bool m | (ε.val : ℝ≥0∞) < error D (prefixMajority A S)} ⊆
      {S | (ε.val : ℝ≥0∞) * (m + 1) ≤ 2 * ∑ t : Fin (m + 1), error D (prefixHypothesis A S t)} := by
    intro S hS
    calc (ε.val : ℝ≥0∞) * (m + 1) ≤ error D (prefixMajority A S) * (m + 1) := by
          gcongr
          exact hS.le
      _ = (m + 1) * error D (prefixMajority A S) := mul_comm _ _
      _ ≤ _ := mul_error_prefixMajority_le hA D S
  calc μ {S | (ε.val : ℝ≥0∞) < error D (prefixMajority A S)}
      ≤ μ {S | (ε.val : ℝ≥0∞) * (m + 1) ≤
          2 * ∑ t : Fin (m + 1), error D (prefixHypothesis A S t)} := measure_mono hsub
    _ ≤ (∫⁻ S, 2 * ∑ t : Fin (m + 1), error D (prefixHypothesis A S t) ∂μ) /
          ((ε.val : ℝ≥0∞) * (m + 1)) :=
        meas_ge_le_lintegral_div hmeas.aemeasurable (mul_ne_zero hε hpos)
          (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp))
    _ ≤ 2 * M / ((ε.val : ℝ≥0∞) * (m + 1)) := by gcongr
    _ ≤ δ.val := by
        rw [ENNReal.div_le_iff (mul_ne_zero hε hpos)
          (ENNReal.mul_ne_top ENNReal.coe_ne_top (by simp))]
        have : ((2 * (M : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ≤ ((ε.val * δ.val * (m + 1) : ℝ≥0) : ℝ≥0∞) :=
          ENNReal.coe_le_coe.mpr hm
        push_cast at this
        calc (2 * M : ℝ≥0∞) ≤ ε.val * δ.val * (m + 1) := this
          _ = δ.val * (ε.val * (m + 1)) := by ring

/-- A class with a learner of finite mistake bound is PAC learnable over its realizable
distributions, provided the learner is measurable; the sample size is `⌈2 M / (ε δ)⌉`. -/
theorem isPACLearnable_of_mistakeBound_le {A : OnlineLearner α} (hA : IsMeasurableLearner A)
    {C : ConceptClass α Bool} {M : ℕ} (hM : mistakeBound A C ≤ M) :
    IsPACLearnable C (realizableDistributions C) := by
  intro ε δ
  refine ⟨⌈2 * (M : ℝ≥0) / (ε.val * δ.val)⌉₊, isPACLearnerFor_prefixMajority hA hM ?_⟩
  have hεδ : 0 < ε.val * δ.val := mul_pos ε.2.1 δ.2.1
  have h := Nat.le_ceil (2 * (M : ℝ≥0) / (ε.val * δ.val))
  rw [div_le_iff₀' hεδ] at h
  exact h.trans (by gcongr; exact le_self_add)

/-- **Mistake bounds give PAC learnability** on countable domains with measurable singletons: a
class with a finite optimal mistake bound (equivalently, finite Littlestone dimension) is PAC
learnable over its realizable distributions. -/
theorem isPACLearnable_of_optimalMistakeBound_ne_top [Countable α] [MeasurableSingletonClass α]
    {C : ConceptClass α Bool} (hC : optimalMistakeBound C ≠ ⊤) :
    IsPACLearnable C (realizableDistributions C) := by
  obtain ⟨A, hA⟩ : ∃ A : OnlineLearner α, mistakeBound A C ≠ ⊤ := by
    by_contra h
    exact hC (top_le_iff.mp (le_optimalMistakeBound_iff.mpr fun A =>
      top_le_iff.mpr (not_not.mp fun hA => h ⟨A, hA⟩)))
  exact isPACLearnable_of_mistakeBound_le (isMeasurableLearner_of_countable A)
    (M := (mistakeBound A C).toNat) (ENat.natCast_toNat hA).ge

end Cslib.MachineLearning.OnlineLearning.MistakeBound
