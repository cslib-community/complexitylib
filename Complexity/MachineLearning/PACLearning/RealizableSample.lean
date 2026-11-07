/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.MachineLearning.PACLearning.Realizable
public import Cslib.MachineLearning.PACLearning.VersionSpace

/-! # Realizable distributions give realizable samples

This file connects the distribution-level realizability assumption `IsRealizableBy D C` (some
concept of `C` has zero true error under `D`) with the sample-level notions `Realizable C S`,
`VersionSpace C S` and `IsConsistent A C`. Under i.i.d. sampling from a realizable distribution,
almost every sample is labeled by the zero-error concept, so it is realizable and every consistent
learner outputs a concept of the version space. The pushforward of a domain distribution along the
graph of a concept of `C` is realizable; this is the "domain distribution plus labeling function"
form of realizability in [ShalevShwartzBenDavid2014, Definition 2.1].

## Main results

- `measurableSet_misclassified`: the misclassification set of a measurable hypothesis is
  measurable when equality on the label type is measurable.
- `ae_apply_eq_of_error_eq_zero`: a zero-error hypothesis labels `D`-almost every example
  correctly.
- `IsRealizableBy.ae_realizable`: i.i.d. samples from a realizable distribution are almost surely
  realizable.
- `IsConsistent.ae_mem_versionSpace`: under such samples, a consistent learner almost surely
  outputs a concept of the version space.
- `isRealizableBy_map_graph`: the pushforward along the graph of a concept of `C` is realizable
  by `C`.
- `realizableDistributions_empty`, `isPACLearnerFor_realizableDistributions_empty`: the empty
  class realizes no distribution, so every learner PAC-learns it; this discharges the empty case
  of the sample-complexity corollaries.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The set of examples misclassified by a measurable hypothesis is measurable, provided equality
on the label type is a measurable relation (for example, `β` countable with measurable
singletons). -/
theorem measurableSet_misclassified [MeasurableEq β] {h : α → β} (hh : Measurable h) :
    MeasurableSet {p : α × β | h p.1 ≠ p.2} :=
  (measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd).compl

/-- A hypothesis of zero true error labels almost every example correctly. -/
theorem ae_apply_eq_of_error_eq_zero {D : Measure (α × β)} {h : α → β} (hh : error D h = 0) :
    ∀ᵐ p ∂D, h p.1 = p.2 :=
  ae_iff.2 hh

/-- **Realizable distributions give realizable samples.** If `D` is realizable by `C`, then
`m` i.i.d. examples from `D` are almost surely labeled by a single concept of `C`. -/
theorem IsRealizableBy.ae_realizable {D : Measure (α × β)} [SigmaFinite D]
    {C : ConceptClass α β} (hD : IsRealizableBy D C) (m : ℕ) :
    ∀ᵐ S ∂Measure.pi (fun _ : Fin m => D), Realizable C S := by
  obtain ⟨c, hc, hc0⟩ := hD
  have hall : ∀ᵐ S ∂Measure.pi (fun _ : Fin m => D), ∀ i, c (S i).1 = (S i).2 :=
    ae_all_iff.2 fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin m => D) (i := i)).eventually
      (p := fun p : α × β => c p.1 = p.2) (ae_apply_eq_of_error_eq_zero hc0)
  filter_upwards [hall] with S hS
  exact ⟨c, hc, fun i => (hS i).symm⟩

/-- Under i.i.d. sampling from a distribution realizable by `C`, a consistent learner almost
surely outputs a concept of the version space. -/
theorem IsConsistent.ae_mem_versionSpace {m : ℕ} {A : Learner α β m} {C : ConceptClass α β}
    (hA : IsConsistent A C) {D : Measure (α × β)} [SigmaFinite D] (hD : IsRealizableBy D C) :
    ∀ᵐ S ∂Measure.pi (fun _ : Fin m => D), A S ∈ VersionSpace C S := by
  filter_upwards [hD.ae_realizable m] with S hS
  exact hA S hS

/-- The pushforward of a distribution on the domain along the graph `x ↦ (x, c x)` of a measurable
concept `c ∈ C` is realizable by `C`. -/
theorem isRealizableBy_map_graph [MeasurableEq β] (P : Measure α) {C : ConceptClass α β}
    {c : α → β} (hc : c ∈ C) (hcm : Measurable c) :
    IsRealizableBy (P.map fun x => (x, c x)) C := by
  refine ⟨c, hc, ?_⟩
  rw [error, Measure.map_apply (by fun_prop : Measurable fun x => (x, c x))
    (measurableSet_misclassified hcm)]
  have : (fun x => (x, c x)) ⁻¹' {p : α × β | c p.1 ≠ p.2} = ∅ := by
    ext x
    simp
  rw [this, measure_empty]

/-- No distribution is realizable by the empty class. -/
theorem realizableDistributions_empty : realizableDistributions (∅ : ConceptClass α β) = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨_, hc, _⟩ => Set.notMem_empty _ hc

/-- Over the distributions realizable by the empty class, which are none, every learner is an
`(ε, δ)`-PAC learner. -/
theorem isPACLearnerFor_realizableDistributions_empty {m : ℕ} (A : Learner α β m)
    (ε δ : Set.Ioo (0 : ℝ≥0) 1) :
    IsPACLearnerFor m ε δ (∅ : ConceptClass α β) (realizableDistributions ∅) :=
  ⟨A, fun D _ hD => by simp only [realizableDistributions_empty, Set.mem_empty_iff_false] at hD⟩

end Cslib.MachineLearning.PACLearning
