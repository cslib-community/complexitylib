/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.PACLearning.EpsilonNet
public import Complexity.MachineLearning.PACLearning.RealizableSample
import Complexity.MachineLearning.PACLearning.ERM
import Complexity.MachineLearning.PACLearning.VCDimension

/-! # The VC upper bound for realizable PAC learning on countable domains

Let `C` be a binary concept class on a countable domain `α` all of whose shattered finite sets
have at most `d` points. Then every consistent learner (in particular every empirical risk
minimizer) learns `C` to accuracy `ε` with confidence `1 - δ` over every distribution realizable
by `C` from

`m ≥ (8 / ε) (d log (48 / ε) + log (4 / δ))`

examples [BlumerEhrenfeuchtHausslerWarmuth1989, Theorem 2.1;
ShalevShwartzBenDavid2014, Section 28.3]. Hence every class of finite VC dimension on a countable
domain is PAC learnable in the realizable setting, with realizable sample complexity
`O((d log (1 / ε) + log (1 / δ)) / ε)`. The constants differ from those of the cited sources but
have the same form.

The proof applies the ε-net theorem (`EpsilonNet.lean`) to the *loss class*
`{(x, y) ↦ [h x ≠ y] | h ∈ C}` and the example distribution `D`. Its growth function is at most that
of `C`. On a realizable sample a consistent learner almost surely outputs some `h ∈ C` agreeing
with every example, so if `error D h > ε` the sample is not an ε-net for the loss class.

The domain is assumed countable with measurable singletons and the labels are `Bool`; the
learners are arbitrary semantic maps from samples to hypotheses, and no running time is claimed.
General domains need a measurability hypothesis on the class and are not formalized here. The
matching `Ω(d / ε)` lower bound of Ehrenfeucht, Haussler, Kearns and Valiant is being developed
upstream in CSLib.

## Main definitions

- `lossClass C`: the class of misclassification indicators of the concepts of `C`.

## Main results

- `mem_lossClass`: membership in the loss class.
- `growthFunction_lossClass_le`: the loss class has at most the growth function of `C`.
- `IsConsistent.ae_not_isEpsNet_of_lt_error`: a consistent learner with error above `ε` on a
  realizable sample witnesses that the sample is not an ε-net for the loss class.
- `IsConsistent.measure_pi_lt_error_mul_two_pow_le`: the tail bound
  `D^m {error D (A S) > ε} * 2 ^ ⌈εm/2⌉ ≤ 2 Π_C(2m)` when `8 ≤ εm`.
- `IsConsistent.measure_pi_lt_error_le_of_vcSampleSize_le`: **the VC upper bound** for consistent
  learners, with the explicit sample size `vcSampleSize d ε δ`.
- `isPACLearnerFor_realizableDistributions_of_vcSampleSize_le`: the corresponding
  `IsPACLearnerFor` statement.
- `sampleComplexity_realizableDistributions_le_of_hasFiniteVCDim`: the realizable sample
  complexity of a class of finite VC dimension is at most `⌈vcSampleSize (vcDim C) ε δ⌉`.
- `isPACLearnable_realizableDistributions_of_hasFiniteVCDim`: every class of finite VC dimension on
  a countable domain is PAC learnable in the realizable setting.

## References

* [A. Blumer, A. Ehrenfeucht, D. Haussler, M. K. Warmuth, *Learnability and the
  Vapnik–Chervonenkis dimension*][BlumerEhrenfeuchtHausslerWarmuth1989]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*}

/-- The *loss class* of a binary concept class `C`: for each `h ∈ C`, the indicator of the labeled
examples `(x, y)` that `h` misclassifies. -/
def lossClass (C : ConceptClass α Bool) : ConceptClass (α × Bool) Bool :=
  (fun h p => decide (h p.1 ≠ p.2)) '' C

theorem mem_lossClass {C : ConceptClass α Bool} {f : α × Bool → Bool} :
    f ∈ lossClass C ↔ ∃ h ∈ C, (fun p : α × Bool => decide (h p.1 ≠ p.2)) = f := by
  rw [lossClass, Set.mem_image]

/-- Passing to the loss class does not increase the growth function: the misclassification
pattern on labeled points is determined by the labeling of their domain points. -/
theorem growthFunction_lossClass_le (C : ConceptClass α Bool) (m : ℕ) :
    growthFunction (lossClass C) m ≤ growthFunction C m := by
  refine growthFunction_le fun x => ?_
  have hsub : restriction (lossClass C) x ⊆
      (fun v i => decide (v i ≠ (x i).2)) '' restriction C (fun i => (x i).1) := by
    intro w hw
    obtain ⟨_, ⟨h, hh, rfl⟩, hw⟩ := mem_restriction.1 hw
    exact ⟨fun i => h (x i).1, mem_restriction.2 ⟨h, hh, fun _ => rfl⟩, funext hw⟩
  calc (restriction (lossClass C) x).ncard
      ≤ ((fun v i => decide (v i ≠ (x i).2)) '' restriction C (fun i => (x i).1)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (restriction C (fun i => (x i).1)).ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ growthFunction C m := ncard_restriction_le_growthFunction C _

variable [MeasurableSpace α]

/-- Under a distribution realizable by `C`, a consistent learner whose output has error greater
than `ε` almost surely witnesses that the sample is not an ε-net for the loss class of `C`. -/
theorem IsConsistent.ae_not_isEpsNet_of_lt_error {C : ConceptClass α Bool} {m : ℕ}
    {A : Learner α Bool m} (hA : IsConsistent A C) {D : Measure (α × Bool)} [SigmaFinite D]
    (hD : IsRealizableBy D C) (ε : ℝ) :
    ∀ᵐ S ∂Measure.pi (fun _ : Fin m => D),
      ENNReal.ofReal ε < error D (A S) → ¬ IsEpsNet D (lossClass C) ε S := by
  filter_upwards [hA.ae_mem_versionSpace hD] with S hS hlt hnet
  obtain ⟨hAC, hAS⟩ := hS
  have hset : {z : α × Bool | decide (A S z.1 ≠ z.2) = true} = {p | A S p.1 ≠ p.2} := by
    ext z
    simp only [Set.mem_ofPred_eq, decide_eq_true_eq]
  obtain ⟨i, hi⟩ := hnet _ ⟨A S, hAC, rfl⟩ (by rw [hset]; exact le_of_lt hlt)
  simp only [hAS i, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true] at hi

variable [MeasurableSingletonClass α] [Countable α]

/-- **VC tail bound for consistent learners** on a countable domain: under a distribution
realizable by `C`, if `8 ≤ εm` then a consistent learner's output has error greater than `ε` with
probability at most `2 Π_C(2m) / 2 ^ ⌈εm/2⌉`. -/
theorem IsConsistent.measure_pi_lt_error_mul_two_pow_le {C : ConceptClass α Bool} {m : ℕ}
    {A : Learner α Bool m} (hA : IsConsistent A C) {D : Measure (α × Bool)}
    [IsProbabilityMeasure D] (hD : IsRealizableBy D C) {ε : ℝ} (hm : 8 ≤ ε * m) :
    Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal ε < error D (A S)} *
        2 ^ ⌈ε * m / 2⌉₊ ≤ 2 * growthFunction C (m + m) := by
  have hle : (growthFunction (lossClass C) (m + m) : ℝ≥0∞) ≤ growthFunction C (m + m) := by
    exact_mod_cast growthFunction_lossClass_le C _
  calc Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal ε < error D (A S)} * 2 ^ ⌈ε * m / 2⌉₊
      ≤ Measure.pi (fun _ : Fin m => D) {S | ¬ IsEpsNet D (lossClass C) ε S} *
          2 ^ ⌈ε * m / 2⌉₊ := by
        gcongr ?_ * _
        exact measure_mono_ae (hA.ae_not_isEpsNet_of_lt_error hD ε)
    _ ≤ 2 * growthFunction (lossClass C) (m + m) :=
        measure_pi_not_isEpsNet_mul_two_pow_le D (lossClass C) hm
    _ ≤ 2 * growthFunction C (m + m) := by gcongr

/-- **The VC upper bound for consistent learners** on a countable domain
[BlumerEhrenfeuchtHausslerWarmuth1989, Theorem 2.1; ShalevShwartzBenDavid2014, Section 28.3]: if
every finite set shattered by `C` has at most `d` points, `D` is realizable by `C`, `A` is
consistent with `C`, and `m ≥ (8 / ε) (d log (48 / ε) + log (4 / δ))`, then the output of `A` on
`m` i.i.d. examples has error greater than `ε` with probability at most `δ`. -/
theorem IsConsistent.measure_pi_lt_error_le_of_vcSampleSize_le {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} {A : Learner α Bool m}
    (hA : IsConsistent A C) {D : Measure (α × Bool)} [IsProbabilityMeasure D]
    (hD : IsRealizableBy D C) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : vcSampleSize d ε δ ≤ m) :
    Measure.pi (fun _ : Fin m => D) {S | ENNReal.ofReal ε < error D (A S)} ≤
      ENNReal.ofReal δ := by
  obtain ⟨h8, hgrowth⟩ := growthFunction_le_of_vcSampleSize_le hC hε hε1 hδ hδ1 hm
  have h2 : (2 : ℝ≥0∞) * growthFunction C (m + m) ≤ ENNReal.ofReal δ * 2 ^ ⌈ε * m / 2⌉₊ := by
    have := ENNReal.ofReal_le_ofReal hgrowth
    rwa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast, ENNReal.ofReal_mul' (by positivity),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at this
  exact (ENNReal.mul_le_mul_iff_left (pow_ne_zero _ two_ne_zero)
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)).1
    ((hA.measure_pi_lt_error_mul_two_pow_le hD h8).trans h2)

/-- **The VC upper bound for realizable PAC learning** on a countable domain
[BlumerEhrenfeuchtHausslerWarmuth1989, Theorem 2.1]: a class whose shattered finite sets have at
most `d` points is `(ε, δ)`-PAC learnable over the distributions it realizes from
`m ≥ (8 / ε) (d log (48 / ε) + log (4 / δ))` examples, by any consistent learner (by any learner
at all if the class is empty, since then no distribution is realizable). -/
theorem isPACLearnerFor_realizableDistributions_of_vcSampleSize_le {C : ConceptClass α Bool}
    {d : ℕ} (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ}
    {ε δ : Set.Ioo (0 : ℝ≥0) 1} (hm : vcSampleSize d ε.val δ.val ≤ m) :
    IsPACLearnerFor m ε δ C (realizableDistributions C) := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact isPACLearnerFor_realizableDistributions_empty (fun _ _ => false) ε δ
  obtain ⟨A, hA⟩ := exists_isConsistent (m := m) hne
  refine ⟨A, fun D _ hD => ?_⟩
  have h := hA.measure_pi_lt_error_le_of_vcSampleSize_le hC hD (by exact_mod_cast ε.2.1)
    (by exact_mod_cast ε.2.2.le) (by exact_mod_cast δ.2.1) (by exact_mod_cast δ.2.2.le) hm
  rw [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal] at h
  rw [IsRealizableBy.optimalError_eq_zero hD, zero_add]
  exact h

/-- The realizable sample complexity of a class of finite VC dimension on a countable domain is at
most `⌈(8 / ε) (vcDim C log (48 / ε) + log (4 / δ))⌉`. -/
theorem sampleComplexity_realizableDistributions_le_of_hasFiniteVCDim {C : ConceptClass α Bool}
    (hC : HasFiniteVCDim C) (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    sampleComplexity IsPACLearnerFor C ε δ (realizableDistributions C) ≤
      ⌈vcSampleSize (vcDim C) ε.val δ.val⌉₊ :=
  Nat.sInf_le (isPACLearnerFor_realizableDistributions_of_vcSampleSize_le
    (fun _ hW => hW.card_le_vcDim hC) (Nat.le_ceil _))

/-- **Finite VC dimension implies realizable PAC learnability** on a countable domain
[BlumerEhrenfeuchtHausslerWarmuth1989, Theorem 2.1]. -/
theorem isPACLearnable_realizableDistributions_of_hasFiniteVCDim {C : ConceptClass α Bool}
    (hC : HasFiniteVCDim C) : IsPACLearnable C (realizableDistributions C) := by
  intro ε δ
  obtain ⟨d, hd⟩ := hasFiniteVCDim_iff.1 hC
  exact ⟨_, isPACLearnerFor_realizableDistributions_of_vcSampleSize_le hd (Nat.le_ceil _)⟩

end Cslib.MachineLearning.PACLearning
