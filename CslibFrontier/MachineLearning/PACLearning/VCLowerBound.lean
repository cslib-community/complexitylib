/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.Realizable
public import Cslib.MachineLearning.PACLearning.VCDimension
import CslibFrontier.Foundations.MeasureTheory.MeasurableSpace.Embedding
import CslibFrontier.MachineLearning.PACLearning.SampleComplexityLower
import CslibFrontier.MachineLearning.PACLearning.RealizableSample

/-!
# The VC lower bound for PAC learning on general domains

Ehrenfeucht, Haussler, Kearns and Valiant [EHKV1989, §3, Theorem 1] showed that learning a binary
class which shatters `d + 1` points to accuracy `ε ≤ 1/8` with confidence `1 - δ`, `δ ≤ 1/100`,
needs at least `d / (32 ε)` examples, even for randomized learners and even over the distributions
the class realizes. The vendored `SampleComplexityLower` proves the same bound for the wider
confidence range `δ < 1/14`, an adaptation of the source's constants made by the vendored proof,
for classes of measurable concepts.
This module removes the measurability hypothesis, so that the bound holds for every binary class on
every domain with measurable singletons:

`W.card ≤ 32 ε m + 1` for every finite set `W` shattered by `C` and every randomized
`(ε, δ)`-PAC learner for `C` from `m` examples over a family containing the realizable
distributions.

The proof restricts the learning problem to the shattered set. Restricting a concept class to a
countable subdomain `s` (`restrictDomain C s`) preserves PAC learners
(`IsPACLearnerFor.restrictDomain`, `IsRPACLearnerFor.restrictDomain`): composing a learner for `C`
with the inclusion of `s` learns the restricted class, because a distribution on `s × Bool` and its
pushforward to `α × Bool` assign the same errors and the same optimal error. On the finite domain
`W` every concept is measurable, and the vendored bound applies.

Consequently PAC learnability over the realizable distributions, and *a fortiori* agnostic PAC
learnability, forces finite VC dimension on every domain with measurable singletons
(`IsRPACLearnable.hasFiniteVCDim`, `IsPACLearnable.hasFiniteVCDim`), with
`vcDim C ≤ 32 ε m + 1` for each learner (`vcDim_le_of_isRPACLearnerFor`). The measurable-singleton
hypothesis cannot be dropped entirely: on a domain with the trivial σ-algebra the error of any
nonconstant hypothesis is one under every distribution, so the class of all Boolean functions is
learned agnostically by a majority vote although it shatters every finite set.

## Main definitions

- `restrictDomain C s`: the restriction of a concept class on `α` to the subdomain `s`.

## Main results

- `SetShatters.restrictDomain`: a class shattering `s` restricts to a class shattering all of `s`.
- `IsPACLearnerFor.restrictDomain`, `IsRPACLearnerFor.restrictDomain`: PAC learners restrict to
  countable subdomains.
- `isRealizableBy_map_inclusion`: pushing a distribution realizable by the restricted class forward
  along the inclusion gives a distribution realizable by `C`.
- `card_le_of_isRPACLearnerFor`, `card_le_of_isPACLearnerFor`: **the EHKV lower bound** for
  arbitrary binary classes on domains with measurable singletons.
- `vcDim_le_of_isRPACLearnerFor`: the corresponding bound on the VC dimension.
- `IsRPACLearnable.hasFiniteVCDim`, `IsPACLearnable.hasFiniteVCDim`: PAC learnability over a family
  containing the realizable distributions implies finite VC dimension.

## References

* [A. Ehrenfeucht, D. Haussler, M. Kearns, L. Valiant,
  *A General Lower Bound on the Number of Examples Needed for Learning*][EHKV1989]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*}

/-- The restriction of a concept class `C` on `α` to the subdomain `s`: the concepts of `C`, each
evaluated only at the points of `s`. -/
def restrictDomain (C : ConceptClass α β) (s : Set α) : ConceptClass s β :=
  (fun c x => c x) '' C

theorem mem_restrictDomain {C : ConceptClass α β} {s : Set α} {c : s → β} :
    c ∈ restrictDomain C s ↔ ∃ c' ∈ C, (fun x : s => c' x) = c :=
  Iff.rfl

/-- A class that shatters `s` restricts to a class that shatters all of `s`. -/
theorem SetShatters.restrictDomain {C : ConceptClass α Bool} {s : Set α}
    (hs : SetShatters C s) : SetShatters (PACLearning.restrictDomain C s) univ := by
  intro T _
  obtain ⟨c, hc, hcs⟩ := hs (Subtype.val '' T) (image_subset_iff.2 fun x _ => x.2)
  refine ⟨fun x => c x, ⟨c, hc, rfl⟩, ?_⟩
  ext x
  have hx := congrArg (x.1 ∈ ·) hcs
  simp only [mem_inter_iff, mem_preimage, Subtype.coe_prop, and_true, eq_iff_iff,
    Subtype.val_injective.mem_set_image] at hx
  simpa only [mem_inter_iff, mem_preimage, mem_univ, and_true] using hx

/-! ### Restricting learners to a countable subdomain -/

section Transfer

variable [MeasurableSpace α] [MeasurableSingletonClass α] {s : Set α} [Countable s]

private theorem measurableEmbedding_inclusion :
    MeasurableEmbedding (Prod.map Subtype.val id : s × Bool → α × Bool) :=
  MeasurableEmbedding.of_countable (Subtype.val_injective.prodMap Function.injective_id)

private theorem error_map_inclusion (D : Measure (s × Bool)) (h : α → Bool) :
    error (D.map (Prod.map Subtype.val id)) h = error D fun x => h x := by
  rw [error, measurableEmbedding_inclusion.map_apply]
  rfl

private theorem optimalError_map_inclusion (D : Measure (s × Bool)) (C : ConceptClass α Bool) :
    optimalError (D.map (Prod.map Subtype.val id)) C = optimalError D (restrictDomain C s) := by
  simp only [optimalError, restrictDomain, iInf_image, error_map_inclusion]

/-- The failure probability of a learner for `C` under the pushforward of `D` along the inclusion
equals that of the restricted learner for the restricted class under `D`. -/
private theorem failure_map_inclusion {m : ℕ} (D : Measure (s × Bool)) [IsProbabilityMeasure D]
    (C : ConceptClass α Bool) (A : Learner α Bool m) (ε : ℝ≥0∞) :
    (Measure.pi fun _ : Fin m => D.map (Prod.map Subtype.val id))
        {S : LabeledSample α Bool m |
          optimalError (D.map (Prod.map Subtype.val id)) C + ε <
            error (D.map (Prod.map Subtype.val id)) (A S)} =
      (Measure.pi fun _ : Fin m => D)
        {S : LabeledSample s Bool m |
          optimalError D (restrictDomain C s) + ε <
            error D fun x => A (Prod.map Subtype.val id ∘ S) x} := by
  have hpi : (Measure.pi fun _ : Fin m => D.map (Prod.map Subtype.val id)) =
      (Measure.pi fun _ : Fin m => D).map fun S i => Prod.map Subtype.val id (S i) :=
    (Measure.pi_map_pi fun _ => measurableEmbedding_inclusion.measurable.aemeasurable).symm
  have hemb : MeasurableEmbedding fun (S : LabeledSample s Bool m) i =>
      Prod.map Subtype.val id (S i) :=
    MeasurableEmbedding.of_countable fun S T hST =>
      funext fun i => measurableEmbedding_inclusion.injective (congrFun hST i)
  rw [hpi, hemb.map_apply]
  simp only [preimage_ofPred_eq, optimalError_map_inclusion, error_map_inclusion]
  rfl

/-- **PAC learners restrict to countable subdomains.** If `C` has an `(ε, δ)`-PAC learner from `m`
examples over a family containing the pushforwards of the distributions in `𝒟'` along the
inclusion of `s`, then so has its restriction to `s` over `𝒟'`: run the learner for `C` and restrict
its hypothesis to `s`. -/
theorem IsPACLearnerFor.restrictDomain {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α Bool} {𝒟 : Set (Measure (α × Bool))} {𝒟' : Set (Measure (s × Bool))}
    (h𝒟 : ∀ D ∈ 𝒟', D.map (Prod.map Subtype.val id) ∈ 𝒟) (h : IsPACLearnerFor m ε δ C 𝒟) :
    IsPACLearnerFor m ε δ (PACLearning.restrictDomain C s) 𝒟' := by
  obtain ⟨A, hA⟩ := h
  refine ⟨fun S x => A (Prod.map Subtype.val id ∘ S) x, fun D _ hD => ?_⟩
  rw [← failure_map_inclusion]
  exact hA _ (h𝒟 D hD)

/-- **Randomized PAC learners restrict to countable subdomains**; see
`IsPACLearnerFor.restrictDomain`. -/
theorem IsRPACLearnerFor.restrictDomain.{u} {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    {C : ConceptClass α Bool} {𝒟 : Set (Measure (α × Bool))} {𝒟' : Set (Measure (s × Bool))}
    (h𝒟 : ∀ D ∈ 𝒟', D.map (Prod.map Subtype.val id) ∈ 𝒟)
    (h : IsRPACLearnerFor.{_, _, u} m ε δ C 𝒟) :
    IsRPACLearnerFor.{_, _, u} m ε δ (PACLearning.restrictDomain C s) 𝒟' := by
  obtain ⟨Ω, _, Q, _, A, hA⟩ := h
  refine ⟨Ω, _, Q, inferInstance, fun ω S x => A ω (Prod.map Subtype.val id ∘ S) x,
    fun D _ hD => ?_⟩
  simp only [← failure_map_inclusion]
  exact hA _ (h𝒟 D hD)

/-- Pushing a distribution realizable by the restriction of `C` to `s` forward along the inclusion
gives a distribution realizable by `C`. -/
theorem isRealizableBy_map_inclusion {C : ConceptClass α Bool} {D : Measure (s × Bool)}
    (hD : IsRealizableBy D (restrictDomain C s)) :
    IsRealizableBy (D.map (Prod.map Subtype.val id)) C := by
  obtain ⟨_, ⟨c, hc, rfl⟩, herr⟩ := hD
  exact ⟨c, hc, (error_map_inclusion D c).trans herr⟩

end Transfer

/-! ### The EHKV lower bound on general domains -/

section LowerBound

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **The EHKV lower bound** [EHKV1989, §3, Theorem 1] for an arbitrary binary class on a domain
with measurable singletons: if `C` shatters the finite set `W`, then every randomized
`(ε, δ)`-PAC learner for `C` with `ε ≤ 1/8` and `δ < 1/14` over a family containing the
distributions `C` realizes uses `m ≥ (W.card - 1) / (32 ε)` examples. No measurability of the
concepts is assumed. The source states the bound for `δ ≤ 1/100`; the range `δ < 1/14` is the
vendored proof's adaptation (see `sample_complexity_lower_bound_randomized`). -/
theorem card_le_of_isRPACLearnerFor.{u} {C : ConceptClass α Bool} {W : Finset α}
    (hW : SetShatters C ↑W) {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1} (hε : (ε : ℝ) ≤ 1 / 8)
    (hδ : (δ : ℝ) < 1 / 14) {𝒟 : Set (Measure (α × Bool))}
    (h𝒟 : realizableDistributions C ⊆ 𝒟) (hlearn : IsRPACLearnerFor.{_, _, u} m ε δ C 𝒟) :
    (W.card : ℝ) ≤ 32 * ε * m + 1 := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 ε.2.1
  by_cases hW2 : W.card < 2
  · have : (W.card : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 hW2
    nlinarith [show (0 : ℝ) ≤ m from m.cast_nonneg]
  have hlearn' : IsRPACLearnerFor.{_, _, u} m ε δ (restrictDomain C ↑W)
      (realizableDistributions (restrictDomain C ↑W)) :=
    hlearn.restrictDomain fun _ hD => h𝒟 (isRealizableBy_map_inclusion hD)
  have hbound := sample_complexity_lower_bound_randomized (W := Finset.univ)
    (by simpa only [Finset.coe_univ] using hW.restrictDomain)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      Set.ncard_coe_finset]; exact not_lt.1 hW2) hε hδ
    (fun _ _ => .of_discrete) (fun P _ c hc => isRealizableBy_map_graph P hc .of_discrete) hlearn'
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    div_le_iff₀ (by positivity)] at hbound
  linarith

/-- **The EHKV lower bound** for deterministic learners; see `card_le_of_isRPACLearnerFor`. -/
theorem card_le_of_isPACLearnerFor {C : ConceptClass α Bool} {W : Finset α}
    (hW : SetShatters C ↑W) {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1} (hε : (ε : ℝ) ≤ 1 / 8)
    (hδ : (δ : ℝ) < 1 / 14) {𝒟 : Set (Measure (α × Bool))}
    (h𝒟 : realizableDistributions C ⊆ 𝒟) (hlearn : IsPACLearnerFor m ε δ C 𝒟) :
    (W.card : ℝ) ≤ 32 * ε * m + 1 :=
  card_le_of_isRPACLearnerFor.{_, 0} hW hε hδ h𝒟 hlearn.toIsRPACLearnerFor

/-- The VC dimension of a class with a randomized `(ε, δ)`-PAC learner from `m` examples, `ε ≤ 1/8`
and `δ < 1/14`, over a family containing the realizable distributions is at most `32 ε m + 1`. -/
theorem vcDim_le_of_isRPACLearnerFor.{u} {C : ConceptClass α Bool} {m : ℕ}
    {ε δ : Set.Ioo (0 : ℝ≥0) 1} (hε : (ε : ℝ) ≤ 1 / 8) (hδ : (δ : ℝ) < 1 / 14)
    {𝒟 : Set (Measure (α × Bool))} (h𝒟 : realizableDistributions C ⊆ 𝒟)
    (hlearn : IsRPACLearnerFor.{_, _, u} m ε δ C 𝒟) :
    (vcDim C : ℝ) ≤ 32 * ε * m + 1 := by
  have hpos : (0 : ℝ) ≤ 32 * ε * m + 1 := by positivity
  have hle : vcDim C ≤ ⌊32 * (ε : ℝ) * m + 1⌋₊ := by
    refine csSup_le' ?_
    rintro _ ⟨W, rfl, hW⟩
    exact Nat.le_floor (card_le_of_isRPACLearnerFor hW hε hδ h𝒟 hlearn)
  exact (Nat.cast_le.2 hle).trans (Nat.floor_le hpos)

private noncomputable def eighth : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 8, by norm_num, by norm_num⟩

private noncomputable def fifteenth : Set.Ioo (0 : ℝ≥0) 1 := ⟨1 / 15, by norm_num, by norm_num⟩

/-- **Learnability implies finite VC dimension** on every domain with measurable singletons: a class
that is randomized PAC learnable over a family containing the distributions it realizes has finite
VC dimension. -/
theorem IsRPACLearnable.hasFiniteVCDim {C : ConceptClass α Bool} {𝒟 : Set (Measure (α × Bool))}
    (h : IsRPACLearnable C 𝒟) (h𝒟 : realizableDistributions C ⊆ 𝒟) : HasFiniteVCDim C := by
  obtain ⟨m, hm⟩ := h eighth fifteenth
  refine hasFiniteVCDim_iff.2 ⟨4 * m + 1, fun W hW => ?_⟩
  have := card_le_of_isRPACLearnerFor hW (by norm_num [eighth]) (by norm_num [fifteenth]) h𝒟 hm
  norm_num [eighth] at this
  exact_mod_cast (by linarith : (W.card : ℝ) ≤ 4 * m + 1)

/-- **Learnability implies finite VC dimension** on every domain with measurable singletons, for
deterministic learners; in particular agnostic PAC learnability (`𝒟 = Set.univ`) implies finite VC
dimension. -/
theorem IsPACLearnable.hasFiniteVCDim {C : ConceptClass α Bool} {𝒟 : Set (Measure (α × Bool))}
    (h : IsPACLearnable C 𝒟) (h𝒟 : realizableDistributions C ⊆ 𝒟) : HasFiniteVCDim C :=
  h.toIsRPACLearnable.hasFiniteVCDim h𝒟

end LowerBound

end Cslib.MachineLearning.PACLearning
