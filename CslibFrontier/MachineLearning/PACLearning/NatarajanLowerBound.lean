/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.NatarajanDimension
public import CslibFrontier.MachineLearning.PACLearning.Realizable
import CslibFrontier.Foundations.MeasureTheory.MeasurableSpace.Embedding
import CslibFrontier.MachineLearning.PACLearning.NatarajanUpperBound
import CslibFrontier.MachineLearning.PACLearning.VCLowerBound

/-! # The multiclass lower bound by reduction to the binary case

A multiclass class `C : ConceptClass α β` that N-shatters a finite set `W` is at least as hard to
learn as the class of all Boolean functions on `W`. Let `f₀, f₁` be the witnesses of the
N-shattering. A binary learner on `W` can encode the label `b` of a point `x` as `f₀ x` (for
`true`) or `f₁ x` (for `false`), run a multiclass learner for `C`, and answer `true` at `x` exactly
when the multiclass hypothesis predicts `f₀ x`. Distributions realizable by the class of all
Boolean functions on `W` encode to distributions realizable by `C`, and every binary mistake is a
multiclass mistake. The EHKV lower bound (`card_le_of_isPACLearnerFor`) therefore transfers. This
is the reduction to the binary fundamental theorem by which [ShalevShwartzBenDavid2014,
Section 29.2.1] derives the lower bounds of Theorem 29.3; Chapter 29, Exercise 5 asks for it in the
agnostic case:

`W.card ≤ 32 ε m + 1` for every finite set `W` N-shattered by `C` and every `(ε, δ)`-PAC learner
for `C` from `m` examples with `ε ≤ 1/8` and `δ < 1/14`, over any family containing the
distributions `C` realizes.

Consequently PAC learnability, over the realizable distributions or agnostically, forces finite
Natarajan dimension on every domain with measurable singletons and labels with measurable
singletons. With the realizable upper bound of `NatarajanUpperBound`, on a countable domain with
finitely many labels a class is PAC learnable over the distributions it realizes iff it has finite
Natarajan dimension.

This is the `d / ε` part of the lower bounds of [ShalevShwartzBenDavid2014, Theorem 29.3]. The
`log (1 / δ) / ε` part and the agnostic `(d + log (1 / δ)) / ε²` lower bound would follow by the
same reduction from binary bounds that the library does not have. The reduction is stated for
deterministic learners: a randomized multiclass learner yields a randomized binary learner whose
failure probability is only bounded above by a measurable function of the randomness, which the
randomized EHKV statement does not accept.

## Main results

- `card_le_of_natarajanShatters_of_isPACLearnerFor`: **the multiclass EHKV lower bound**
  `W.card ≤ 32 ε m + 1` for an N-shattered finite set `W`.
- `natarajanDim_le_of_isPACLearnerFor`: `natarajanDim C ≤ 32 ε m + 1` for every such learner.
- `IsPACLearnable.hasFiniteNatarajanDim`: PAC learnability over a family containing the realizable
  distributions implies finite Natarajan dimension; with the family `Set.univ` this covers agnostic
  learnability.
- `sampleComplexity_lower_bound_natarajanDim`: the sample complexity of a learnable class is at
  least `(natarajanDim C - 1) / (32 ε)`.
- `isPACLearnable_realizableDistributions_iff_hasFiniteNatarajanDim`: **the multiclass fundamental
  theorem, realizable case, qualitative form**, on countable domains with finitely many labels.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
* [A. Ehrenfeucht, D. Haussler, M. Kearns, L. Valiant,
  *A General Lower Bound on the Number of Examples Needed for Learning*][EHKV1989]
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β]

/-- **The multiclass EHKV lower bound** [EHKV1989; ShalevShwartzBenDavid2014, Section 29.2.1]: if
`C` N-shatters the finite set `W`, then every `(ε, δ)`-PAC learner for `C` with `ε ≤ 1/8` and
`δ < 1/14` over a family containing the distributions `C` realizes uses
`m ≥ (W.card - 1) / (32 ε)` examples. -/
theorem card_le_of_natarajanShatters_of_isPACLearnerFor {C : ConceptClass α β} {W : Finset α}
    (hW : NatarajanShatters C ↑W) {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1} (hε : (ε : ℝ) ≤ 1 / 8)
    (hδ : (δ : ℝ) < 1 / 14) {𝒟 : Set (Measure (α × β))}
    (h𝒟 : realizableDistributions C ⊆ 𝒟) (hlearn : IsPACLearnerFor m ε δ C 𝒟) :
    (W.card : ℝ) ≤ 32 * ε * m + 1 := by
  classical
  obtain ⟨f₀, f₁, hne, hsh⟩ := hW
  obtain ⟨A, hA⟩ := hlearn
  -- Encode a binary example on `W` as a multiclass example: `true ↦ f₀`, `false ↦ f₁`.
  let e : W × Bool → α × β := fun p => (p.1, cond p.2 (f₀ p.1) (f₁ p.1))
  have he : MeasurableEmbedding e := by
    refine MeasurableEmbedding.of_countable fun p q hpq => ?_
    obtain ⟨⟨x, hx⟩, b⟩ := p
    obtain ⟨⟨y, hy⟩, b'⟩ := q
    simp only [e, Prod.mk.injEq] at hpq
    obtain ⟨rfl, hb⟩ := hpq
    have := hne x hx
    cases b <;> cases b' <;> simp_all [eq_comm]
  have hS : MeasurableEmbedding fun (S : LabeledSample W Bool m) i => e (S i) :=
    MeasurableEmbedding.of_countable fun S T hST =>
      funext fun i => he.injective (congrFun hST i)
  -- The binary learner runs `A` on the encoded sample and decodes by comparison with `f₀`.
  let A' : Learner W Bool m := fun S x => decide (A (fun i => e (S i)) x = f₀ x)
  have hlearn' : IsPACLearnerFor m ε δ (Set.univ : ConceptClass W Bool)
      (realizableDistributions Set.univ) := by
    refine ⟨A', fun D _ hD => ?_⟩
    -- Encoded realizable distributions are realizable by `C`.
    have hD' : D.map e ∈ realizableDistributions C := by
      obtain ⟨c, -, hc⟩ := hD
      obtain ⟨h, hh, h₀, h₁⟩ := hsh (Subtype.val '' {x | c x = true}) (by
        rintro _ ⟨x, -, rfl⟩
        exact x.2)
      refine ⟨h, hh, ?_⟩
      rw [error, he.map_apply]
      refine measure_mono_null (fun p hp => ?_) hc
      obtain ⟨⟨x, hx⟩, b⟩ := p
      simp only [mem_preimage, mem_ofPred_eq, e] at hp ⊢
      intro hcb
      apply hp
      cases b
      · have hxB : x ∉ Subtype.val '' {x : W | c x = true} := by
          rintro ⟨y, hy, rfl⟩
          simp_all
        exact h₁ x ⟨hx, hxB⟩
      · exact h₀ x ⟨⟨x, hx⟩, hcb, rfl⟩
    have hopt : optimalError D (Set.univ : ConceptClass W Bool) = 0 := hD.optimalError_eq_zero
    have hopt' : optimalError (D.map e) C = 0 := IsRealizableBy.optimalError_eq_zero hD'
    -- Every binary mistake is a multiclass mistake.
    have herr : ∀ S : LabeledSample W Bool m,
        error D (A' S) ≤ error (D.map e) (A fun i => e (S i)) := by
      intro S
      rw [error, error, he.map_apply]
      refine measure_mono fun p hp => ?_
      obtain ⟨⟨x, hx⟩, b⟩ := p
      simp only [mem_ofPred_eq, mem_preimage, A', e] at hp ⊢
      cases b
      · simp only [Bool.cond_false, ne_eq, decide_eq_false_iff_not, Decidable.not_not] at hp ⊢
        rw [hp]
        exact hne x hx
      · simpa using hp
    have hpi : (Measure.pi fun _ : Fin m => D.map e) =
        (Measure.pi fun _ : Fin m => D).map fun S i => e (S i) :=
      (Measure.pi_map_pi fun _ => he.measurable.aemeasurable).symm
    calc Measure.pi (fun _ : Fin m => D)
          {S | optimalError D Set.univ + ε.val < error D (A' S)}
        ≤ Measure.pi (fun _ : Fin m => D) ((fun S i => e (S i)) ⁻¹'
            {S | optimalError (D.map e) C + ε.val < error (D.map e) (A S)}) := by
          refine measure_mono fun S hS => ?_
          simp only [mem_ofPred_eq, mem_preimage, hopt, hopt', zero_add] at hS ⊢
          exact hS.trans_le (herr S)
      _ = Measure.pi (fun _ : Fin m => D.map e)
            {S | optimalError (D.map e) C + ε.val < error (D.map e) (A S)} := by
          rw [hpi, hS.map_apply]
      _ ≤ δ.val := hA _ (h𝒟 hD')
  have hshatter : SetShatters (Set.univ : ConceptClass W Bool) ↑(Finset.univ : Finset W) :=
    fun T _ => ⟨fun x => decide (x ∈ T), mem_univ _, by ext; simp⟩
  have := card_le_of_isPACLearnerFor hshatter hε hδ subset_rfl hlearn'
  rwa [Finset.card_univ, Fintype.card_coe] at this

/-- The Natarajan dimension of a class with an `(ε, δ)`-PAC learner from `m` examples, `ε ≤ 1/8` and
`δ < 1/14`, over a family containing the realizable distributions is at most `32 ε m + 1`. -/
theorem natarajanDim_le_of_isPACLearnerFor {C : ConceptClass α β} {m : ℕ}
    {ε δ : Set.Ioo (0 : ℝ≥0) 1} (hε : (ε : ℝ) ≤ 1 / 8) (hδ : (δ : ℝ) < 1 / 14)
    {𝒟 : Set (Measure (α × β))} (h𝒟 : realizableDistributions C ⊆ 𝒟)
    (hlearn : IsPACLearnerFor m ε δ C 𝒟) :
    (natarajanDim C : ℝ) ≤ 32 * ε * m + 1 := by
  have hpos : (0 : ℝ) ≤ 32 * ε * m + 1 := by positivity
  have hle : natarajanDim C ≤ ⌊32 * (ε : ℝ) * m + 1⌋₊ := natarajanDim_le fun W hW =>
    Nat.le_floor (card_le_of_natarajanShatters_of_isPACLearnerFor hW hε hδ h𝒟 hlearn)
  exact (Nat.cast_le.2 hle).trans (Nat.floor_le hpos)

/-- **Learnability implies finite Natarajan dimension** on every domain with measurable singletons
and labels with measurable singletons: a class that is PAC learnable over a family containing the
distributions it realizes has finite Natarajan dimension. With `𝒟 = Set.univ` this covers agnostic
PAC learnability. -/
theorem IsPACLearnable.hasFiniteNatarajanDim {C : ConceptClass α β}
    {𝒟 : Set (Measure (α × β))} (h : IsPACLearnable C 𝒟) (h𝒟 : realizableDistributions C ⊆ 𝒟) :
    HasFiniteNatarajanDim C := by
  obtain ⟨m, hm⟩ := h ⟨1 / 8, by norm_num, by norm_num⟩ ⟨1 / 15, by norm_num, by norm_num⟩
  refine hasFiniteNatarajanDim_iff.2 ⟨4 * m + 1, fun W hW => ?_⟩
  have := card_le_of_natarajanShatters_of_isPACLearnerFor hW (by norm_num) (by norm_num) h𝒟 hm
  norm_num at this
  exact_mod_cast (by linarith : (W.card : ℝ) ≤ 4 * m + 1)

/-- **The multiclass sample-complexity lower bound**: if `C` is `(ε, δ)`-PAC learnable from some
number of examples, `ε ≤ 1/8` and `δ < 1/14`, over a family containing the realizable
distributions, then its sample complexity is at least `(natarajanDim C - 1) / (32 ε)`. -/
theorem sampleComplexity_lower_bound_natarajanDim {C : ConceptClass α β}
    {ε δ : Set.Ioo (0 : ℝ≥0) 1} (hε : (ε : ℝ) ≤ 1 / 8) (hδ : (δ : ℝ) < 1 / 14)
    {𝒟 : Set (Measure (α × β))} (h𝒟 : realizableDistributions C ⊆ 𝒟)
    (hlearnable : {n : ℕ | IsPACLearnerFor n ε δ C 𝒟}.Nonempty) :
    ((natarajanDim C : ℝ) - 1) / (32 * ε) ≤ sampleComplexity IsPACLearnerFor C ε δ 𝒟 := by
  have hε0 : (0 : ℝ) < ε := NNReal.coe_pos.2 ε.2.1
  have := natarajanDim_le_of_isPACLearnerFor hε hδ h𝒟 (Nat.sInf_mem hlearnable)
  rw [div_le_iff₀ (by positivity)]
  rw [sampleComplexity]
  linarith

/-- **The multiclass fundamental theorem, realizable case, qualitative form**
[ShalevShwartzBenDavid2014, Theorem 29.3(3)]: on a countable domain with measurable singletons and
finitely many labels, a class is PAC learnable over the distributions it realizes iff it has finite
Natarajan dimension. -/
theorem isPACLearnable_realizableDistributions_iff_hasFiniteNatarajanDim [Countable α] [Finite β]
    [Nonempty β] {C : ConceptClass α β} :
    IsPACLearnable C (realizableDistributions C) ↔ HasFiniteNatarajanDim C :=
  ⟨fun h => h.hasFiniteNatarajanDim subset_rfl,
    isPACLearnable_realizableDistributions_of_hasFiniteNatarajanDim⟩

end Cslib.MachineLearning.PACLearning
