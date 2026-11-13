/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.UniformConvergence

/-! # The uniform convergence property and learnability by every ERM

A concept class `C` has the *uniform convergence property* over a family `𝒟` of distributions if,
for every accuracy `ε` and confidence `δ` in `(0, 1)`, all sufficiently large i.i.d. samples from
any `D ∈ 𝒟` are `ε`-representative for `C` with probability at least `1 - δ`
[ShalevShwartzBenDavid2014, Definition 4.3]. The class is *learnable by every ERM* over `𝒟` if,
for every `ε` and `δ`, every empirical risk minimizer for `C` is an `(ε, δ)`-PAC learner over `𝒟`
from all sufficiently large samples; over all distributions and over the distributions `C` realizes,
these are statements 2 and 5 of the fundamental theorem [ShalevShwartzBenDavid2014, Theorem 6.7].

The uniform convergence property gives learnability by every ERM with the same confidence and half
the accuracy [ShalevShwartzBenDavid2014, Corollary 4.4], through ERM on an `ε / 2`-representative
sample (`IsRepresentative.error_le_optimalError_add`). Learnability by every ERM gives PAC
learnability, because every nonempty class has an ERM (`exists_isERM`).

The definitions quantify the sample size before the learner: a single threshold works for every
ERM. The source's statement 2 lets the threshold depend on the ERM rule; uniform convergence gives
the uniform version, so the characterizations agree. `HasUniformConvergenceRate` in `SRM.lean`
records an explicit rate instead of a threshold.

## Main definitions

- `HasUniformConvergence C 𝒟`: the uniform convergence property over `𝒟`.
- `IsERMLearnable C 𝒟`: every empirical risk minimizer for `C` learns `C` over `𝒟` from all
  sufficiently large samples.

## Main results

- `HasUniformConvergence.isERMLearnable`: uniform convergence implies learnability by every ERM.
- `IsERMLearnable.isPACLearnable`: learnability by every ERM implies PAC learnability.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [DecidableEq β]

/-- The class `C` has the *uniform convergence property* over the family `𝒟`: for every accuracy
`ε` and confidence `δ` in `(0, 1)` there is a sample size `m₀` such that, for every `m ≥ m₀` and
every `D ∈ 𝒟`, `m` i.i.d. examples from `D` fail to be `ε`-representative for `C` with probability
at most `δ` [ShalevShwartzBenDavid2014, Definition 4.3]. -/
@[expose] def HasUniformConvergence (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∃ m₀ : ℕ, ∀ m ≥ m₀,
    ∀ (D : Measure (α × β)) [IsProbabilityMeasure D], D ∈ 𝒟 →
      Measure.pi (fun _ : Fin m => D) {S | ¬ IsRepresentative D C ε S} ≤ ENNReal.ofReal δ

/-- The class `C` is *learnable by every ERM* over the family `𝒟`: for every accuracy `ε` and
confidence `δ` there is a sample size `m₀` such that, for every `m ≥ m₀`, every empirical risk
minimizer for `C` on `m` examples misses `optimalError D C + ε` with probability at most `δ` under
every `D ∈ 𝒟`. Over `Set.univ` and over `realizableDistributions C` these are statements 2 and 5
of [ShalevShwartzBenDavid2014, Theorem 6.7]. -/
@[expose] def IsERMLearnable (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∀ ε δ : Set.Ioo (0 : ℝ≥0) 1, ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ A : Learner α β m, IsERM A C →
    ∀ (D : Measure (α × β)) [IsProbabilityMeasure D], D ∈ 𝒟 →
      Measure.pi (fun _ : Fin m => D) {S | optimalError D C + ↑ε.val < error D (A S)} ≤ ↑δ.val

/-- **Uniform convergence implies learnability by every ERM** [ShalevShwartzBenDavid2014,
Corollary 4.4]: an `ε / 2`-representative sample makes every ERM `ε`-optimal, so the uniform
convergence threshold at accuracy `ε / 2` and confidence `δ` serves every ERM. -/
theorem HasUniformConvergence.isERMLearnable {C : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    (h : HasUniformConvergence C 𝒟) : IsERMLearnable C 𝒟 := by
  intro ε δ
  have hε0 : (0 : ℝ) < ε.val := by exact_mod_cast ε.2.1
  have hε1 : (ε.val : ℝ) < 1 := by exact_mod_cast ε.2.2
  obtain ⟨m₀, hm₀⟩ := h (ε.val / 2) δ.val (by positivity) (by linarith)
    (by exact_mod_cast δ.2.1) (by exact_mod_cast δ.2.2)
  refine ⟨m₀, fun m hm A hA D _ hD => ?_⟩
  calc Measure.pi (fun _ : Fin m => D) {S | optimalError D C + ↑ε.val < error D (A S)}
      ≤ Measure.pi (fun _ : Fin m => D) {S | ¬ IsRepresentative D C (ε.val / 2) S} := by
        refine measure_mono fun S hS hrep => ?_
        have := hrep.error_le_optimalError_add hA
        rw [ENNReal.ofReal_coe_nnreal] at this
        exact (not_le.2 hS) this
    _ ≤ ↑δ.val := by simpa only [ENNReal.ofReal_coe_nnreal] using hm₀ m hm D hD

/-- **Learnability by every ERM implies PAC learnability**: at the threshold sample size, an ERM
exists when `C` is nonempty, and any learner works when `C` is empty, because the optimal error of
the empty class is `⊤`. -/
theorem IsERMLearnable.isPACLearnable [Nonempty β] {C : ConceptClass α β}
    {𝒟 : Set (Measure (α × β))} (h : IsERMLearnable C 𝒟) : IsPACLearnable C 𝒟 := by
  intro ε δ
  obtain ⟨m₀, hm₀⟩ := h ε δ
  refine ⟨m₀, ?_⟩
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ _ => Classical.arbitrary β, fun D _ _ => by simp [optimalError]⟩
  obtain ⟨A, hA⟩ := exists_isERM (m := m₀) hne
  exact ⟨A, fun D _ hD => hm₀ m₀ le_rfl A hA D hD⟩

/-- Learnability by every ERM is antitone in the distribution family. -/
theorem IsERMLearnable.antitone_family {C : ConceptClass α β} {𝒟 𝒟' : Set (Measure (α × β))}
    (h𝒟 : 𝒟 ⊆ 𝒟') (h : IsERMLearnable C 𝒟') : IsERMLearnable C 𝒟 :=
  fun ε δ => (h ε δ).imp fun _ hm m hm₀ A hA D _ hD => hm m hm₀ A hA D (h𝒟 hD)

end Cslib.MachineLearning.PACLearning
