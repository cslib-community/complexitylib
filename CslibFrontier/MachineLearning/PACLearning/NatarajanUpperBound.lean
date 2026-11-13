/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.NatarajanDimension
public import CslibFrontier.MachineLearning.PACLearning.VCUpperBound
import CslibFrontier.Foundations.Data.Nat.Choose.Real
import CslibFrontier.MachineLearning.PACLearning.ERM

/-! # The realizable upper bound for multiclass PAC learning on countable domains

Let `C` be a concept class on a countable domain `α` with labels in a finite type `β` of size `k`,
all of whose N-shattered finite sets have at most `d` points. Then every consistent learner (in
particular every empirical risk minimizer) learns `C` to accuracy `ε` with confidence `1 - δ` over
every distribution realizable by `C` from

`m ≥ (8 / ε) (d log (48 / ε) + 2 d log k + log (4 / δ))`

examples. Hence every class of finite Natarajan dimension with finitely many labels is PAC
learnable in the realizable setting, with realizable sample complexity
`O((d log (k / ε) + log (1 / δ)) / ε)`. This gives the realizable upper bound of the multiclass
fundamental theorem [ShalevShwartzBenDavid2014, Theorem 29.3(3)], which is
`C (d log (k d / ε) + log (1 / δ)) / ε` for an absolute constant `C`, with explicit constants.

The proof is that of the binary VC upper bound (`VCUpperBound.lean`): the ε-net theorem applied to
the Boolean loss class `{(x, y) ↦ [h x ≠ y] | h ∈ C}`. Only the growth function bound changes. The
misclassification pattern on labeled points is determined by the labeling of their domain points,
so Natarajan's lemma bounds the growth function of the loss class by
`natarajanSum m k d ≤ k ^ (2 d) exp (m / T) T ^ d`. The factor `k ^ (2 d)` is absorbed by running
the binary calculation at confidence `δ / k ^ (2 d)`.

The domain is assumed countable with measurable singletons and the labels finite, so that every set
of samples is measurable. The learners are arbitrary semantic maps from samples to hypotheses, and
no running time is claimed. The agnostic bound and the lower bounds of Theorem 29.3 are not proved
here.

## Main definitions

- `natarajanSampleSize d k ε δ`: the sample size
  `(8 / ε) (d log (48 / ε) + 2 d log k + log (4 / δ))`.

## Main results

- `growthFunction_lossClass_le_natarajanSum`: the loss class of a class whose N-shattered sets have
  at most `d` points has growth function at most `natarajanSum m k d`.
- `natarajanSum_le_pow_mul_exp_mul_pow`: `natarajanSum n k d ≤ k ^ (2 d) exp (n / T) T ^ d`.
- `natarajanSampleSize_eq_vcSampleSize`: the multiclass sample size is the VC sample size at
  confidence `δ / k ^ (2 d)`.
- `IsConsistent.measure_pi_lt_error_le_of_natarajanSampleSize_le`: **the multiclass upper bound**
  for consistent learners.
- `isPACLearnerFor_realizableDistributions_of_natarajanSampleSize_le`: the corresponding
  `IsPACLearnerFor` statement.
- `sampleComplexity_realizableDistributions_le_of_hasFiniteNatarajanDim`: the realizable sample
  complexity of a class of finite Natarajan dimension is at most
  `⌈natarajanSampleSize (natarajanDim C) k ε δ⌉`.
- `isPACLearnable_realizableDistributions_of_hasFiniteNatarajanDim`: every class of finite
  Natarajan dimension with finitely many labels on a countable domain is PAC learnable in the
  realizable setting.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*}

/-- **Natarajan's lemma for the loss class**: if `C` N-shatters no finite set of more than `d`
points, its loss class has growth function at most `∑_{i ≤ d} (m choose i) (k choose 2) ^ i`. The
misclassification pattern on labeled points is determined by the labeling of their domain points. -/
theorem growthFunction_lossClass_le_natarajanSum [Fintype β] [DecidableEq β] {C : ConceptClass α β}
    {d : ℕ} (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) (m : ℕ) :
    growthFunction (lossClass C) m ≤ natarajanSum m (Fintype.card β) d := by
  refine growthFunction_le fun x => ?_
  have hsub : restriction (lossClass C) x ⊆
      (fun v i => decide (v i ≠ (x i).2)) '' ((· ∘ fun i => (x i).1) '' C) := by
    intro w hw
    obtain ⟨_, hl, hw⟩ := mem_restriction.1 hw
    obtain ⟨h, hh, rfl⟩ := mem_lossClass.1 hl
    exact ⟨h ∘ fun i => (x i).1, ⟨h, hh, rfl⟩, funext hw⟩
  calc (restriction (lossClass C) x).ncard
      ≤ ((fun v i => decide (v i ≠ (x i).2)) '' ((· ∘ fun i => (x i).1) '' C)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ((· ∘ fun i => (x i).1) '' C).ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ natarajanSum m (Fintype.card β) d := ncard_restriction_le_natarajanSum hC _

/-- Natarajan's lemma in the form used for sample sizes: with at least one label,
`∑_{i ≤ d} (n choose i) (k choose 2) ^ i ≤ k ^ (2 d) exp (n / T) T ^ d` for every real `T ≥ 1`. -/
theorem natarajanSum_le_pow_mul_exp_mul_pow (n d : ℕ) {k : ℕ} (hk : 0 < k) {T : ℝ} (hT : 1 ≤ T) :
    (natarajanSum n k d : ℝ) ≤ (k : ℝ) ^ (2 * d) * (Real.exp (n / T) * T ^ d) := by
  calc (natarajanSum n k d : ℝ)
      ≤ (∑ i ∈ Finset.range (d + 1), (n.choose i : ℝ)) * (k : ℝ) ^ (2 * d) := by
        exact_mod_cast natarajanSum_le_sum_choose_mul n d hk
    _ ≤ Real.exp (n / T) * T ^ d * (k : ℝ) ^ (2 * d) := by
        gcongr
        exact Cslib.sum_choose_le_exp_mul_pow n d T hT
    _ = (k : ℝ) ^ (2 * d) * (Real.exp (n / T) * T ^ d) := mul_comm _ _

/-- The multiclass sample size `(8 / ε) (d log (48 / ε) + 2 d log k + log (4 / δ))` for `k` labels.
It is the VC sample size at confidence `δ / k ^ (2 d)` (`natarajanSampleSize_eq_vcSampleSize`). -/
@[expose] noncomputable def natarajanSampleSize (d k : ℕ) (ε δ : ℝ) : ℝ :=
  8 / ε * (d * Real.log (48 / ε) + 2 * d * Real.log k + Real.log (4 / δ))

/-- The multiclass sample size is the VC sample size at confidence `δ / k ^ (2 d)`. -/
theorem natarajanSampleSize_eq_vcSampleSize (d : ℕ) {k : ℕ} (hk : 0 < k) (ε : ℝ) {δ : ℝ}
    (hδ : 0 < δ) : natarajanSampleSize d k ε δ = vcSampleSize d ε (δ / k ^ (2 * d)) := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hK : (4 : ℝ) * k ^ (2 * d) ≠ 0 := by positivity
  rw [natarajanSampleSize, vcSampleSize, div_div_eq_mul_div, Real.log_div hK hδ.ne',
    Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_div (by norm_num) hδ.ne']
  push_cast
  ring

variable [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
  [MeasurableSpace β] [MeasurableSingletonClass β]

section Fintype

variable [Fintype β]

/-- **The multiclass upper bound for consistent learners** on a countable domain with finitely many
labels [ShalevShwartzBenDavid2014, Theorem 29.3(3)]: if every finite set N-shattered by `C` has at
most `d` points, `D` is realizable by `C`, `A` is consistent with `C`, and
`m ≥ (8 / ε) (d log (48 / ε) + 2 d log k + log (4 / δ))` with `k` labels, then the output of `A` on
`m` i.i.d. examples has error greater than `ε` with probability at most `δ`. -/
theorem IsConsistent.measure_pi_lt_error_le_of_natarajanSampleSize_le {C : ConceptClass α β}
    {d : ℕ} (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d) {m : ℕ}
    {A : Learner α β m} (hA : IsConsistent A C) {D : Measure (α × β)} [IsProbabilityMeasure D]
    (hD : IsRealizableBy D C) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : natarajanSampleSize d (Fintype.card β) ε δ ≤ m) :
    Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal ε < error D (A S)} ≤
      ENNReal.ofReal δ := by
  classical
  have : Nonempty β := (nonempty_of_isProbabilityMeasure D).map Prod.snd
  have hk : 0 < Fintype.card β := Fintype.card_pos
  set K : ℝ := (Fintype.card β : ℝ) ^ (2 * d) with hKdef
  have hK1 : 1 ≤ K := one_le_pow₀ (by exact_mod_cast hk)
  have hK : 0 < K := by positivity
  have hT : 1 ≤ 48 / ε := by rw [le_div_iff₀ hε]; linarith
  rw [natarajanSampleSize_eq_vcSampleSize d hk ε hδ] at hm
  -- The binary calculation at confidence `δ / K` absorbs the factor `K` of Natarajan's lemma.
  obtain ⟨h8, hN⟩ := le_of_vcSampleSize_le hε hε1 (div_pos hδ hK)
    ((div_le_one hK).2 (hδ1.trans hK1)) hm le_rfl
  have hgrowth : 2 * (growthFunction (lossClass C) (m + m) : ℝ) ≤ δ * 2 ^ ⌈ε * m / 2⌉₊ := by
    calc 2 * (growthFunction (lossClass C) (m + m) : ℝ)
        ≤ 2 * (natarajanSum (m + m) (Fintype.card β) d : ℝ) := by
          gcongr
          exact_mod_cast growthFunction_lossClass_le_natarajanSum hC _
      _ ≤ 2 * (K * (Real.exp (((m + m : ℕ) : ℝ) / (48 / ε)) * (48 / ε) ^ d)) := by
          gcongr
          exact natarajanSum_le_pow_mul_exp_mul_pow _ _ hk hT
      _ = K * (2 * (Real.exp (((m + m : ℕ) : ℝ) / (48 / ε)) * (48 / ε) ^ d)) := by ring
      _ ≤ K * (δ / K * 2 ^ ⌈ε * m / 2⌉₊) := by gcongr
      _ = δ * 2 ^ ⌈ε * m / 2⌉₊ := by field_simp
  calc Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal ε < error D (A S)}
      ≤ Measure.pi (fun _ : Fin m => D) {S | ¬ IsEpsNet D (lossClass C) ε S} :=
        measure_mono_ae (hA.ae_not_isEpsNet_of_lt_error hD ε)
    _ ≤ ENNReal.ofReal δ :=
        measure_pi_not_isEpsNet_le_of_growthFunction_le D (lossClass C) h8 hgrowth

/-- **The multiclass upper bound for realizable PAC learning** on a countable domain with finitely
many labels [ShalevShwartzBenDavid2014, Theorem 29.3(3)]: a class whose N-shattered finite sets
have at most `d` points is `(ε, δ)`-PAC learnable over the distributions it realizes from
`m ≥ (8 / ε) (d log (48 / ε) + 2 d log k + log (4 / δ))` examples, by any consistent learner (by
any learner at all if the class is empty, since then no distribution is realizable). -/
theorem isPACLearnerFor_realizableDistributions_of_natarajanSampleSize_le [Nonempty β]
    {C : ConceptClass α β} {d : ℕ} (hC : ∀ W : Finset α, NatarajanShatters C ↑W → W.card ≤ d)
    {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hm : natarajanSampleSize d (Fintype.card β) ε.val δ.val ≤ m) :
    IsPACLearnerFor m ε δ C (realizableDistributions C) := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact isPACLearnerFor_realizableDistributions_empty (fun _ _ => Classical.arbitrary β) ε δ
  obtain ⟨A, hA⟩ := exists_isConsistent (m := m) hne
  refine ⟨A, fun D _ hD => ?_⟩
  have h := hA.measure_pi_lt_error_le_of_natarajanSampleSize_le hC hD
    (by exact_mod_cast ε.2.1) (by exact_mod_cast ε.2.2.le) (by exact_mod_cast δ.2.1)
    (by exact_mod_cast δ.2.2.le) hm
  rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal] at h
  rw [IsRealizableBy.optimalError_eq_zero hD, zero_add]
  exact h

/-- The realizable sample complexity of a class of finite Natarajan dimension with `k` labels on a
countable domain is at most `⌈(8 / ε) (Ndim(C) log (48 / ε) + 2 Ndim(C) log k + log (4 / δ))⌉`. -/
theorem sampleComplexity_realizableDistributions_le_of_hasFiniteNatarajanDim [Nonempty β]
    {C : ConceptClass α β} (hC : HasFiniteNatarajanDim C) (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    sampleComplexity IsPACLearnerFor C ε δ (realizableDistributions C) ≤
      ⌈natarajanSampleSize (natarajanDim C) (Fintype.card β) ε.val δ.val⌉₊ :=
  Nat.sInf_le (isPACLearnerFor_realizableDistributions_of_natarajanSampleSize_le
    (fun _ hW => hW.card_le_natarajanDim hC) (Nat.le_ceil _))

end Fintype

/-- **Finite Natarajan dimension implies realizable PAC learnability** on a countable domain with
finitely many labels [ShalevShwartzBenDavid2014, Theorem 29.3(3)]. -/
theorem isPACLearnable_realizableDistributions_of_hasFiniteNatarajanDim [Finite β] [Nonempty β]
    {C : ConceptClass α β} (hC : HasFiniteNatarajanDim C) :
    IsPACLearnable C (realizableDistributions C) := by
  have := Fintype.ofFinite β
  intro ε δ
  obtain ⟨d, hd⟩ := hasFiniteNatarajanDim_iff.1 hC
  exact ⟨_, isPACLearnerFor_realizableDistributions_of_natarajanSampleSize_le hd (Nat.le_ceil _)⟩

end Cslib.MachineLearning.PACLearning
