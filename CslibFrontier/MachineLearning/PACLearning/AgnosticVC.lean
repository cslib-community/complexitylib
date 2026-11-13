/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.VCUniformConvergence
import CslibFrontier.MachineLearning.PACLearning.VCDimension

/-! # Agnostic PAC learning of classes of finite VC dimension

A binary concept class `C` of finite VC dimension on a countable domain is agnostically PAC
learnable for the 0-1 loss by empirical risk minimization [VapnikChervonenkis1971;
ShalevShwartzBenDavid2014, Theorem 6.7]. If every finite set shattered by `C` has at most `d`
points, then under *every* distribution `D` on labeled examples an ERM learner on

`m ≥ (64 / ε²) (2 d log (20 / ε) + log (4 / δ))`

i.i.d. examples outputs a hypothesis with error at most `optimalError D C + ε` with probability at
least `1 - δ`. This is the upstream `IsPACLearnerFor` over the family `Set.univ` of all
distributions. The proof combines uniform convergence from the growth function
(`VCUniformConvergence.lean`) with ERM on an `ε / 2`-representative sample
[ShalevShwartzBenDavid2014, Lemma 4.2].

The sample size is `O ((d log (1 / ε) + log (1 / δ)) / ε²)`. The sharp agnostic rate
`O ((d + log (1 / δ)) / ε²)` [ShalevShwartzBenDavid2014, Theorem 6.8] needs chaining and is not
proved here. The domain is countable with measurable singletons, so that every set of samples is
measurable; uncountable domains need a measurability hypothesis on the class. The learners are
semantic maps: no running time is claimed, and finding an empirical risk minimizer can be
computationally hard.

## Main results

- `IsERM.measure_pi_lt_error_le_growthFunction`: the agnostic tail bound
  `4 Π_C(2m) exp (-m ε² / 32)` for ERM.
- `IsERM.measure_pi_lt_error_le_of_uniformConvergenceSampleSize_le`: failure probability at most
  `δ` from the explicit sample size.
- `isPACLearnerFor_univ_of_uniformConvergenceSampleSize_le`: the corresponding `IsPACLearnerFor`
  over all distributions.
- `sampleComplexity_univ_le_of_hasFiniteVCDim`: the agnostic sample complexity of a class of
  finite VC dimension is at most `⌈(64 / ε²) (2 vcDim C log (20 / ε) + log (4 / δ))⌉`.
- `isPACLearnable_univ_of_hasFiniteVCDim`: **finite VC dimension implies agnostic PAC
  learnability** on a countable domain.

## References

* [V. N. Vapnik, A. Ya. Chervonenkis, *On the uniform convergence of relative frequencies of events
  to their probabilities*][VapnikChervonenkis1971]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]

/-- **Agnostic tail bound for ERM** on a countable domain: under every distribution `D`, an
empirical risk minimizer for `C` misses `optimalError D C + ε` with probability at most
`4 Π_C(2m) exp (-m ε² / 32)`. -/
theorem IsERM.measure_pi_lt_error_le_growthFunction (D : Measure (α × Bool))
    [IsProbabilityMeasure D] {C : ConceptClass α Bool} {m : ℕ} {A : Learner α Bool m}
    (hA : IsERM A C) {ε : ℝ} (hε : 0 ≤ ε) :
    Measure.pi (fun _ : Fin m => D) {S | optimalError D C + ENNReal.ofReal ε < error D (A S)} ≤
      ENNReal.ofReal (4 * growthFunction C (m + m) * Real.exp (-(m * ε ^ 2 / 32))) := by
  refine (measure_mono fun S hS => ?_).trans
    ((measure_pi_not_isRepresentative_le_growthFunction D C m (ε := ε / 2) (by positivity)).trans_eq
      ?_)
  · exact fun hrep => (not_le.2 hS) (hrep.error_le_optimalError_add hA)
  · rw [show (m : ℝ) * (ε / 2) ^ 2 / 8 = m * ε ^ 2 / 32 by ring]

/-- **Agnostic learning of a class of finite VC dimension by ERM** on a countable domain: if every
finite set shattered by `C` has at most `d` points and
`m ≥ (64 / ε²) (2 d log (20 / ε) + log (4 / δ))`, then under every distribution an empirical risk
minimizer for `C` misses `optimalError D C + ε` with probability at most `δ`. -/
theorem IsERM.measure_pi_lt_error_le_of_uniformConvergenceSampleSize_le (D : Measure (α × Bool))
    [IsProbabilityMeasure D] {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} {A : Learner α Bool m}
    (hA : IsERM A C) {ε δ : ℝ} (hε : 0 < ε) (hε20 : ε ≤ 20) (hδ : 0 < δ)
    (hm : uniformConvergenceSampleSize d (ε / 2) δ ≤ m) :
    Measure.pi (fun _ : Fin m => D) {S | optimalError D C + ENNReal.ofReal ε < error D (A S)} ≤
      ENNReal.ofReal δ := by
  refine (measure_mono fun S hS => ?_).trans
    (measure_pi_not_isRepresentative_le_of_uniformConvergenceSampleSize_le D hC (by positivity)
      (by linarith) hδ hm)
  exact fun hrep => (not_le.2 hS) (hrep.error_le_optimalError_add hA)

/-- **Agnostic PAC learning of classes of finite VC dimension** for the 0-1 loss on a countable
domain: a class whose shattered finite sets have at most `d` points is `(ε, δ)`-PAC learnable over
all distributions from `m ≥ (64 / ε²) (2 d log (20 / ε) + log (4 / δ))` examples. If `C` is
nonempty the learner is any empirical risk minimizer. If `C` is empty the optimal error is `⊤` and
any learner works. -/
theorem isPACLearnerFor_univ_of_uniformConvergenceSampleSize_le {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hm : uniformConvergenceSampleSize d ((ε.val : ℝ) / 2) δ.val ≤ m) :
    IsPACLearnerFor m ε δ C Set.univ := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => false, fun D _ _ => by simp [optimalError]⟩
  obtain ⟨A, hA⟩ := exists_isERM (m := m) hne
  refine ⟨A, fun D _ _ => ?_⟩
  have hε1 : (ε.val : ℝ) ≤ 1 := by exact_mod_cast ε.2.2.le
  have h := hA.measure_pi_lt_error_le_of_uniformConvergenceSampleSize_le D hC
    (by exact_mod_cast ε.2.1) (by linarith) (by exact_mod_cast δ.2.1) hm
  rwa [ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal] at h

/-- The agnostic sample complexity of a class of finite VC dimension on a countable domain is at
most `⌈(64 / ε²) (2 vcDim C log (20 / ε) + log (4 / δ))⌉`. -/
theorem sampleComplexity_univ_le_of_hasFiniteVCDim {C : ConceptClass α Bool}
    (hC : HasFiniteVCDim C) (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    sampleComplexity IsPACLearnerFor C ε δ Set.univ ≤
      ⌈uniformConvergenceSampleSize (vcDim C) ((ε.val : ℝ) / 2) δ.val⌉₊ :=
  Nat.sInf_le (isPACLearnerFor_univ_of_uniformConvergenceSampleSize_le
    (fun _ hW => hW.card_le_vcDim hC) (Nat.le_ceil _))

/-- **Finite VC dimension implies agnostic PAC learnability** on a countable domain
[VapnikChervonenkis1971; ShalevShwartzBenDavid2014, Theorem 6.7]. -/
theorem isPACLearnable_univ_of_hasFiniteVCDim {C : ConceptClass α Bool}
    (hC : HasFiniteVCDim C) : IsPACLearnable C Set.univ := by
  intro ε δ
  obtain ⟨d, hd⟩ := hasFiniteVCDim_iff.1 hC
  exact ⟨_, isPACLearnerFor_univ_of_uniformConvergenceSampleSize_le hd (Nat.le_ceil _)⟩

end Cslib.MachineLearning.PACLearning
