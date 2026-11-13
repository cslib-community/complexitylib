/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.SRM

/-! # Nonuniform learnability

A class `C` is *nonuniformly learnable* if the sample size needed to compete with a hypothesis
`h ∈ C` may depend on `h` [ShalevShwartzBenDavid2014, Definition 7.1]: for every accuracy `ε` and
confidence `δ` there is a learner, one for each sample size, such that for every `h ∈ C` and every
distribution `D` of the family, from some sample size `m₀(ε, δ, h)` on the learner's error exceeds
`L_D(h) + ε` with probability at most `δ`. PAC learnability asks for one sample size that works for
every `h` simultaneously, measured against `optimalError D C`.

A countable union `⋃ i, H i` of classes with uniform convergence rates `ε i m δ → 0` is
nonuniformly learnable by structural risk minimization [ShalevShwartzBenDavid2014, Theorems 7.3
and 7.5]. In particular every countable class whose hypotheses have measurable misclassification
sets is nonuniformly learnable, as the union of its singletons with Hoeffding rates
[ShalevShwartzBenDavid2014, Section 7.3], even when it has infinite VC dimension and is not PAC
learnable.

The definition follows the upstream `IsPACLearnable` conventions: accuracy and confidence range
over `Set.Ioo (0 : ℝ≥0) 1`, the distribution family is a parameter, and the learner may depend on
`ε` and `δ` (the SRM learner depends only on `δ`). The source fixes one algorithm for all `(ε, δ)`
in Definition 7.1 but runs SRM with confidence `δ` as an input.

## Main definitions

- `IsNonuniformLearnable C 𝒟`: `C` is nonuniformly learnable over the family `𝒟`.

## Main results

- `IsNonuniformLearnable.antitone_family`, `IsNonuniformLearnable.antitone_C`: monotonicity.
- `isNonuniformLearnable_iUnion`: a countable union of classes with vanishing uniform convergence
  rates is nonuniformly learnable by SRM.
- `isNonuniformLearnable_of_countable`: every countable class with measurable misclassification
  sets is nonuniformly learnable over all distributions.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The class `C` is *nonuniformly learnable* over the family `𝒟` [ShalevShwartzBenDavid2014,
Definition 7.1]: for every accuracy `ε` and confidence `δ` there are learners `A m`, one for each
sample size, such that for every `h ∈ C` there is a sample size `m₀` from which on, for every
probability measure `D ∈ 𝒟`, the error of `A m` exceeds `error D h + ε` with probability at most
`δ`. -/
@[expose] def IsNonuniformLearnable (C : ConceptClass α β) (𝒟 : Set (Measure (α × β))) : Prop :=
  ∀ ε δ : Set.Ioo (0 : ℝ≥0) 1, ∃ A : (m : ℕ) → Learner α β m, ∀ h ∈ C, ∃ m₀, ∀ m ≥ m₀,
    ∀ (D : Measure (α × β)) [IsProbabilityMeasure D], D ∈ 𝒟 →
      Measure.pi (fun _ : Fin m => D) {S | error D h + ↑ε.val < error D (A m S)} ≤ ↑δ.val

/-- Nonuniform learnability is antitone in the distribution family. -/
theorem IsNonuniformLearnable.antitone_family {C : ConceptClass α β}
    {𝒟 𝒟' : Set (Measure (α × β))} (h𝒟 : 𝒟 ⊆ 𝒟') (hC : IsNonuniformLearnable C 𝒟') :
    IsNonuniformLearnable C 𝒟 := fun ε δ => by
  obtain ⟨A, hA⟩ := hC ε δ
  exact ⟨A, fun h hh => by
    obtain ⟨m₀, hm₀⟩ := hA h hh
    exact ⟨m₀, fun m hm D _ hD => hm₀ m hm D (h𝒟 hD)⟩⟩

/-- Nonuniform learnability is antitone in the class. -/
theorem IsNonuniformLearnable.antitone_C {C C' : ConceptClass α β}
    {𝒟 : Set (Measure (α × β))} (hCC' : C ⊆ C') (hC : IsNonuniformLearnable C' 𝒟) :
    IsNonuniformLearnable C 𝒟 := fun ε δ => by
  obtain ⟨A, hA⟩ := hC ε δ
  exact ⟨A, fun h hh => hA h (hCC' hh)⟩

/-- **Countable unions of uniformly convergent classes are nonuniformly learnable**
[ShalevShwartzBenDavid2014, Theorems 7.3 and 7.5]: if each class `H i` of a countable family has
uniform convergence rate `ε i` over `𝒟` with `ε i m δ → 0` as `m → ∞` for every `δ > 0`, then
`⋃ i, H i` is nonuniformly learnable over `𝒟`, by structural risk minimization. The rate plays the
role of the source's `ε_n(m, δ)` (Equation (7.1)), defined there from the uniform convergence
sample complexity. The learner charges class `i` the penalty `max (ε i m (w i · δ)) 0 + e i / m`
for an injection `e : ι → ℕ`; the second term makes the penalties tend to infinity along the
indices, so that an SRM minimizer exists on every sample, and vanishes as `m → ∞`. The instance
`Nonempty (α → β)` supplies a learner when every class is empty. Theorem 7.5's explicit sample
complexity `m^UC_{H n(h)}(ε / 2, w(n(h)) δ)` is not stated: the proof only produces some sample
size, through the excess-risk guarantee `IsSRM.measure_pi_exists_lt_error_le`. -/
theorem isNonuniformLearnable_iUnion [DecidableEq β] [Nonempty (α → β)] {ι : Type*}
    [Countable ι] {H : ι → ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    {ε : ι → ℕ → ℝ → ℝ}
    (hH : ∀ i, HasUniformConvergenceRate (H i) 𝒟 (ε i))
    (hε : ∀ i, ∀ δ : ℝ, 0 < δ → Tendsto (fun m => ε i m δ) atTop (𝓝 0)) :
    IsNonuniformLearnable (⋃ i, H i) 𝒟 := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat ι
  obtain ⟨w⟩ := Weighting.nonempty (ι := ι)
  intro ε₀ δ₀
  set δ : ℝ := (δ₀.val : ℝ)
  have hδ : 0 < δ := by exact_mod_cast δ₀.2.1
  -- The penalty of class `i` at sample size `m`.
  set pen : ℕ → ι → ℝ := fun m i => max (ε i m (w i * δ)) 0 + (e i : ℝ) / m
  have hpen_top : ∀ m, 0 < m → Tendsto (pen m) cofinite atTop := fun m hm => by
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    refine Tendsto.nonneg_add_atTop (fun i => le_max_right _ _) (Tendsto.atTop_div_const hm' ?_)
    exact tendsto_natCast_atTop_atTop.comp (Nat.cofinite_eq_atTop ▸ he.tendsto_cofinite)
  have hSRM : ∀ m, 0 < m → (∃ i, (H i).Nonempty) → ∃ A : Learner α β m, IsSRM A H (pen m) :=
    fun m hm hne => exists_isSRM hne (hpen_top m hm)
  let A : (m : ℕ) → Learner α β m := fun m =>
    if h : 0 < m ∧ ∃ i, (H i).Nonempty then Classical.choose (hSRM m h.1 h.2)
    else fun _ => Classical.arbitrary _
  refine ⟨A, fun h hh => ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 hh
  have hne : ∃ i, (H i).Nonempty := ⟨i, h, hi⟩
  -- Eventually `2 · pen m i < ε₀`.
  have hlim : Tendsto (fun m => 2 * pen m i) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => max (ε i m (w i * δ)) 0) atTop (𝓝 0) := by
      simpa using (hε i _ (mul_pos (w.pos i) hδ)).max (tendsto_const_nhds (x := (0 : ℝ)))
    simpa using ((h1.add (tendsto_const_div_atTop_nhds_zero_nat (e i : ℝ))).const_mul 2)
  have hε₀ : (0 : ℝ) < ε₀.val := by exact_mod_cast ε₀.2.1
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1 (hlim.eventually_lt_const hε₀)
  refine ⟨max m₀ 1, fun m hmm D _ hD => ?_⟩
  have hm : 0 < m := lt_of_lt_of_le one_pos (le_of_max_le_right hmm)
  have hAm : IsSRM (A m) H (pen m) := by
    simp only [A, dite_eq_left (And.intro hm hne)]
    exact Classical.choose_spec (hSRM m hm hne)
  have hbound := hAm.measure_pi_exists_lt_error_le hH w hm hδ (fun j => le_max_left _ _ |>.trans
    (le_add_of_nonneg_right (by positivity))) D hD
  refine (measure_mono fun S hS => ?_).trans (hbound.trans_eq ENNReal.ofReal_coe_nnreal)
  replace hS : error D h + ↑ε₀.val < error D (A m S) := hS
  refine ⟨i, h, hi, ?_⟩
  have hfin : ∀ g : α → β, error D g ≠ ⊤ := fun g => measure_ne_top _ _
  have hS' := (ENNReal.toReal_lt_toReal (ENNReal.add_ne_top.2 ⟨hfin h, ENNReal.coe_ne_top⟩)
    (hfin _)).2 hS
  rw [ENNReal.toReal_add (hfin h) ENNReal.coe_ne_top, ENNReal.coe_toReal] at hS'
  linarith [hm₀ m (le_of_max_le_left hmm)]

/-- **Countable classes are nonuniformly learnable** [ShalevShwartzBenDavid2014, Section 7.3]:
every countable class whose hypotheses have measurable misclassification sets is nonuniformly
learnable over all distributions, by SRM over its singletons with Hoeffding rates. -/
theorem isNonuniformLearnable_of_countable [Nonempty (α → β)] {C : ConceptClass α β}
    (hC : C.Countable) (hmeas : ∀ h ∈ C, MeasurableSet {p : α × β | h p.1 ≠ p.2}) :
    IsNonuniformLearnable C Set.univ := by
  classical
  have : Countable C := hC.to_subtype
  have hU : C = ⋃ h : C, ({(h : α → β)} : ConceptClass α β) := by
    ext g
    simp
  rw [hU]
  exact isNonuniformLearnable_iUnion (fun h => hasUniformConvergenceRate_singleton (hmeas h h.2))
    fun _ δ _ => tendsto_sqrt_log_div_two_mul_atTop (2 / δ)

end Cslib.MachineLearning.PACLearning
