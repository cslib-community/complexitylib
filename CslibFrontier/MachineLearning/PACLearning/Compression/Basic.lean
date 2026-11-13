/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.RealizableSample
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Logic.Function.DependsOn
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Data.Nat.Choose.Sum
import CslibFrontier.MachineLearning.PACLearning.FiniteClass
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Sample compression schemes

A *sample compression scheme of size `k`* for a concept class `C`
[LittlestoneWarmuth1986] [FloydWarmuth1995] keeps at most `k` examples of every sample that `C`
realizes, and reconstructs from the kept examples alone a hypothesis that labels the *whole*
sample correctly. Here a scheme keeps a list of indices into the sample, so kept examples may
repeat and their order is part of the message, and the reconstructed hypothesis need not belong
to `C`.

The **compression bound** says that a small scheme generalizes. On `m` i.i.d. examples from a
distribution realizable by `C`, the reconstructed hypothesis has error greater than `ε` with
probability at most `(m + 1) ^ k (1 - ε) ^ (m - k)`. For each of the at most `(m + 1) ^ k` ways
to choose the kept indices, the reconstructed hypothesis depends only on the kept examples, so
conditionally on them it must also label at least `m - k` independent fresh examples correctly;
a hypothesis of error greater than `ε` does so with probability at most `(1 - ε) ^ (m - k)`
(`measure_pi_lt_error_and_forall_notMem_apply_eq_le`). A union bound over the index choices
finishes the proof.

The bound needs the misclassification sets of the reconstruction map to be measurable jointly in
the kept examples and the test example (`MeasurableReconstruction`). This holds on countable
domains with measurable singletons (`measurableReconstruction_of_countable`) and whenever the
reconstruction is jointly measurable (`measurableReconstruction_of_measurable`). No measurability
of the compression map is needed: the union bound runs over the index choices, not over samples.

## Main definitions

- `SampleCompressionScheme C k`: compression and reconstruction maps of size `k` for `C`.
- `SampleCompressionScheme.learner`: the learner that reconstructs from the compressed sample.
- `MeasurableReconstruction`: joint measurability of the misclassification sets of a
  reconstruction map.

## Main results

- `measure_pi_lt_error_and_forall_notMem_apply_eq_le`: a learner that reads only the examples
  indexed by `J` and labels the other examples correctly has error greater than `ε` with
  probability at most `(1 - ε) ^ (m - |J|)`.
- `SampleCompressionScheme.measure_pi_lt_error_learner_le`: the compression bound
  `(m + 1) ^ k (1 - ε) ^ (m - k)` for every distribution realizable by `C`.
- `SampleCompressionScheme.isPACLearnerFor`: the scheme's learner is an `(ε, δ)`-PAC learner over
  `realizableDistributions C` whenever `(m + 1) ^ k (1 - ε) ^ (m - k) ≤ δ`;
  `SampleCompressionScheme.isPACLearnerFor_of_log_le` replaces the condition by
  `k log (m + 1) + log (1 / δ) ≤ ε (m - k)`.
- `SampleCompressionScheme.isPACLearnable`: a class with a sample compression scheme of finite
  size is PAC learnable in the realizable setting.

## Source mapping

Littlestone and Warmuth introduced compression schemes and showed that they give PAC learners
[LittlestoneWarmuth1986]; Floyd and Warmuth study their variants [FloydWarmuth1995] (locators in
both unverified). [ShalevShwartzBenDavid2014, Definition 30.4] defines a scheme of size `k` by maps
`A : Z ^ m → [m] ^ k` and `B : Z ^ k → H` with zero sample error on every realizable sample. Here
a scheme keeps a list of *at most* `k` indices and the reconstructed hypothesis need not lie in
`C`; this generality costs the factor `(m + 1) ^ k ≥ ∑ j ≤ k, m ^ j` in place of the `m ^ k`
index sequences of the union bound in the proof of [ShalevShwartzBenDavid2014, Theorem 30.2].
That theorem is the agnostic bound via Bernstein's inequality for `m ≥ 2 k`, and its realizable
[ShalevShwartzBenDavid2014, Corollary 30.3] gives error at most `8 k log (m / δ) / m`. The bound
here is the direct realizable one: each fixed index choice survives with probability at most
`(1 - ε) ^ (m - k)`, with no restriction on `m`. The learner is a semantic map; no running time is
claimed.

## References

* [N. Littlestone, M. K. Warmuth, *Relating data compression and learnability*]
  [LittlestoneWarmuth1986]
* [S. Floyd, M. K. Warmuth, *Sample compression, learnability, and the Vapnik–Chervonenkis
  dimension*][FloydWarmuth1995]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace Cslib.MachineLearning.PACLearning

variable {α β : Type*}

/-- A *sample compression scheme of size `k`* for the concept class `C`. On every sample realized
by `C`, `compress` keeps at most `k` indices into the sample, and `reconstruct`, applied to the
kept examples in the kept order, returns a hypothesis that labels every example of the sample
correctly. The reconstructed hypothesis need not belong to `C`. -/
structure SampleCompressionScheme (C : ConceptClass α β) (k : ℕ) where
  /-- The indices of the kept examples. -/
  compress : ∀ {m : ℕ}, LabeledSample α β m → List (Fin m)
  /-- The hypothesis reconstructed from a list of kept examples. -/
  reconstruct : List (α × β) → α → β
  /-- On a realizable sample at most `k` examples are kept. -/
  length_compress_le : ∀ {m : ℕ} (S : LabeledSample α β m), Realizable C S →
    (compress S).length ≤ k
  /-- On a realizable sample the reconstructed hypothesis labels every example correctly. -/
  reconstruct_correct : ∀ {m : ℕ} (S : LabeledSample α β m), Realizable C S →
    ∀ i, reconstruct ((compress S).map S) (S i).1 = (S i).2

namespace SampleCompressionScheme

variable {C : ConceptClass α β} {k : ℕ}

/-- The learner of a sample compression scheme: compress the sample, then reconstruct. -/
@[expose] def learner (κ : SampleCompressionScheme C k) {m : ℕ} : Learner α β m :=
  fun S => κ.reconstruct ((κ.compress S).map S)

/-- The learner's hypothesis is the reconstruction from the compressed sample. -/
theorem learner_apply (κ : SampleCompressionScheme C k) {m : ℕ} (S : LabeledSample α β m) :
    κ.learner S = κ.reconstruct ((κ.compress S).map S) := rfl

/-- On a realizable sample, the learner of a scheme labels every example correctly. -/
theorem learner_apply_eq (κ : SampleCompressionScheme C k) {m : ℕ} {S : LabeledSample α β m}
    (hS : Realizable C S) (i : Fin m) : κ.learner S (S i).1 = (S i).2 :=
  κ.reconstruct_correct S hS i

/-- A scheme for `C` restricts to every subclass of `C`, with the same compression and
reconstruction maps. -/
@[expose] def ofSubset (κ : SampleCompressionScheme C k) {C' : ConceptClass α β} (h : C' ⊆ C) :
    SampleCompressionScheme C' k where
  compress := κ.compress
  reconstruct := κ.reconstruct
  length_compress_le S hS :=
    κ.length_compress_le S (let ⟨c, hc, hcS⟩ := hS; ⟨c, h hc, hcS⟩)
  reconstruct_correct S hS :=
    κ.reconstruct_correct S (let ⟨c, hc, hcS⟩ := hS; ⟨c, h hc, hcS⟩)

end SampleCompressionScheme

variable [MeasurableSpace α] [MeasurableSpace β]

/-- A reconstruction map has *measurable misclassification sets* when, for every number `j` of
kept examples, the set of pairs (kept examples, test example) on which the reconstructed
hypothesis errs is measurable. -/
@[expose] def MeasurableReconstruction (ρ : List (α × β) → α → β) : Prop :=
  ∀ j : ℕ, MeasurableSet
    {q : (LabeledSample α β j × α) × β | Function.uncurry (fun T x => ρ (List.ofFn T) x) q.1 ≠ q.2}

/-- On countable domains with measurable singletons every reconstruction map has measurable
misclassification sets. -/
theorem measurableReconstruction_of_countable [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] (ρ : List (α × β) → α → β) :
    MeasurableReconstruction ρ :=
  fun _ => (Set.to_countable _).measurableSet

/-- A reconstruction map that is jointly measurable in the kept examples and the test example,
for every number of kept examples, has measurable misclassification sets when equality on `β` is
measurable. -/
theorem measurableReconstruction_of_measurable [MeasurableEq β] {ρ : List (α × β) → α → β}
    (hρ : ∀ j : ℕ, Measurable (Function.uncurry fun (T : LabeledSample α β j) x =>
      ρ (List.ofFn T) x)) :
    MeasurableReconstruction ρ :=
  fun j => measurableSet_misclassified (hρ j)

/-- **Hold-out bound.** Let `g` be a learner whose hypothesis depends only on the examples indexed
by `J`, with measurable misclassification sets. Then, on `m` i.i.d. examples from `D`, the
probability that `g` has error greater than `ε` and still labels every example outside `J`
correctly is at most `(1 - ε) ^ (m - |J|)`. -/
theorem measure_pi_lt_error_and_forall_notMem_apply_eq_le (D : Measure (α × β))
    [IsProbabilityMeasure D] {m : ℕ} (J : Finset (Fin m)) {g : LabeledSample α β m → α → β}
    (hg : DependsOn g (J : Set (Fin m)))
    (hgm : MeasurableSet {q : (LabeledSample α β m × α) × β | Function.uncurry g q.1 ≠ q.2})
    (ε : ℝ≥0∞) :
    Measure.pi (fun _ : Fin m => D)
        {S | ε < error D (g S) ∧ ∀ i ∉ J, g S (S i).1 = (S i).2} ≤ (1 - ε) ^ (m - J.card) := by
  classical
  set T := {S : LabeledSample α β m | ε < error D (g S) ∧ ∀ i ∉ J, g S (S i).1 = (S i).2}
  -- Each hypothesis `g S` has a measurable misclassification set, its error is measurable in `S`,
  -- and so is the event `T`.
  have hslice (S : LabeledSample α β m) : MeasurableSet {p : α × β | g S p.1 ≠ p.2} :=
    hgm.preimage (f := fun p : α × β => ((S, p.1), p.2)) (by fun_prop)
  have herr : Measurable fun S => error D (g S) := by
    have hs : MeasurableSet {q : LabeledSample α β m × (α × β) | g q.1 q.2.1 ≠ q.2.2} :=
      hgm.preimage (f := fun q : LabeledSample α β m × (α × β) => ((q.1, q.2.1), q.2.2))
        (by fun_prop)
    exact measurable_measure_prodMk_left hs
  have hT : MeasurableSet T := by
    change MeasurableSet ({S | ε < error D (g S)} ∩
      {S : LabeledSample α β m | ∀ i ∉ J, g S (S i).1 = (S i).2})
    refine (measurableSet_lt measurable_const herr).inter ?_
    have : {S : LabeledSample α β m | ∀ i ∉ J, g S (S i).1 = (S i).2} =
        ⋂ i ∈ (Jᶜ : Finset (Fin m)), {S | g S (S i).1 = (S i).2} := by
      ext S
      simp only [mem_ofPred_eq, mem_iInter, Finset.mem_compl]
    rw [this]
    refine Finset.measurableSet_biInter _ fun i _ => ?_
    have := (hgm.preimage (f := fun S : LabeledSample α β m => ((S, (S i).1), (S i).2))
      (by fun_prop)).compl
    simpa only [preimage_compl, preimage_ofPred_eq, Function.uncurry_apply_pair, ne_eq, not_not,
      compl_ofPred] using this
  -- Split the coordinates into those in `J` and the others.
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin m => α × β) (· ∈ J)
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ : Fin m => D) (· ∈ J)
  rw [← he.symm.measure_preimage_equiv T, Measure.prod_apply (e.symm.measurable hT)]
  -- For fixed coordinates in `J`, the hypothesis is fixed, so each slice is the event that a
  -- fixed hypothesis of error greater than `ε` labels the other coordinates correctly.
  have hbound (u : (i : {i // i ∈ J}) → α × β) :
      Measure.pi (fun _ : {i // i ∉ J} => D) (Prod.mk u ⁻¹' (e.symm ⁻¹' T)) ≤
        (1 - ε) ^ (m - J.card) := by
    rcases (Prod.mk u ⁻¹' (e.symm ⁻¹' T)).eq_empty_or_nonempty with h0 | ⟨v₀, hv₀⟩
    · rw [h0, measure_empty]
      exact zero_le
    set h := g (e.symm (u, v₀))
    have hconst (v : (i : {i // i ∉ J}) → α × β) : g (e.symm (u, v)) = h :=
      hg fun i hi => by
        simp only [e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, Finset.mem_coe.1 hi,
          dite_true]
    have hsub : Prod.mk u ⁻¹' (e.symm ⁻¹' T) ⊆ {v | ∀ i, h (v i).1 = (v i).2} := by
      intro v hv i
      have := hv.2 i i.2
      rw [hconst v] at this
      simpa only [e, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, i.2, dite_false,
        Subtype.coe_eta] using this
    have hh : ε ≤ error D h := by
      have := hv₀.1
      rw [hconst v₀] at this
      exact this.le
    calc Measure.pi (fun _ : {i // i ∉ J} => D) (Prod.mk u ⁻¹' (e.symm ⁻¹' T))
        ≤ Measure.pi (fun _ : {i // i ∉ J} => D) {v | ∀ i, h (v i).1 = (v i).2} :=
          measure_mono hsub
      _ = (1 - error D h) ^ Fintype.card {i // i ∉ J} :=
          measure_pi_forall_apply_eq_eq_pow_card D (hslice _)
      _ ≤ (1 - ε) ^ (m - J.card) := by
          rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
          gcongr
  refine (lintegral_mono hbound).trans_eq ?_
  rw [lintegral_const, measure_univ, mul_one]

namespace SampleCompressionScheme

variable {C : ConceptClass α β} {k : ℕ}

/-- **Compression bound** [LittlestoneWarmuth1986] [FloydWarmuth1995]. If `C` has a sample
compression scheme of size `k` with measurable reconstruction and `D` is realizable by `C`, then
on `m` i.i.d. examples the scheme's learner has error greater than `ε` with probability at most
`(m + 1) ^ k (1 - ε) ^ (m - k)`. -/
theorem measure_pi_lt_error_learner_le (κ : SampleCompressionScheme C k)
    (hκ : MeasurableReconstruction κ.reconstruct) {D : Measure (α × β)} [IsProbabilityMeasure D]
    (hD : IsRealizableBy D C) (m : ℕ) (ε : ℝ≥0∞) :
    Measure.pi (fun _ : Fin m => D) {S | ε < error D (κ.learner S)} ≤
      ((m + 1) ^ k : ℕ) * (1 - ε) ^ (m - k) := by
  classical
  set μ := Measure.pi (fun _ : Fin m => D)
  -- An index list of length at most `k`, the hypothesis reconstructed from it, and the indices
  -- it reads.
  let g (ι : Σ j : Fin (k + 1), Fin j → Fin m) (S : LabeledSample α β m) : α → β :=
    κ.reconstruct (List.ofFn (S ∘ ι.2))
  let J (ι : Σ j : Fin (k + 1), Fin j → Fin m) : Finset (Fin m) := Finset.univ.image ι.2
  let B (ι : Σ j : Fin (k + 1), Fin j → Fin m) : Set (LabeledSample α β m) :=
    {S | ε < error D (g ι S) ∧ ∀ i ∉ J ι, g ι S (S i).1 = (S i).2}
  -- On a realizable sample, the compressed sample is one of the index lists.
  have hsub : {S | ε < error D (κ.learner S)} ≤ᵐ[μ] ⋃ ι, B ι := by
    filter_upwards [hD.ae_realizable m] with S hS hlt
    set L := κ.compress S
    have hL : L.length < k + 1 := Nat.lt_succ_of_le (κ.length_compress_le S hS)
    let ι : Σ j : Fin (k + 1), Fin j → Fin m := ⟨⟨L.length, hL⟩, L.get⟩
    have hgS : g ι S = κ.learner S := by
      simp only [g, ι, learner_apply, L]
      rw [← List.map_ofFn, List.ofFn_get]
    refine mem_iUnion.2 ⟨ι, ?_, fun i _ => ?_⟩
    · rw [hgS]
      exact hlt
    · rw [hgS]
      exact κ.learner_apply_eq hS i
  have hJ (ι : Σ j : Fin (k + 1), Fin j → Fin m) : (J ι).card ≤ k :=
    Finset.card_image_le.trans (by simpa using Nat.lt_succ_iff.1 ι.1.2)
  have hB (ι : Σ j : Fin (k + 1), Fin j → Fin m) : μ (B ι) ≤ (1 - ε) ^ (m - k) := by
    refine (measure_pi_lt_error_and_forall_notMem_apply_eq_le D (J ι) (g := g ι) ?_ ?_ ε).trans
      (pow_le_pow_right_of_le_one' tsub_le_self (Nat.sub_le_sub_left (hJ ι) m))
    · intro S S' hSS'
      simp only [g]
      congr 2
      funext t
      exact hSS' _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))
    · exact (hκ ι.1).preimage (f := fun q : (LabeledSample α β m × α) × β =>
        ((q.1.1 ∘ ι.2, q.1.2), q.2)) (by fun_prop)
  have hcard : Fintype.card (Σ j : Fin (k + 1), Fin j → Fin m) ≤ (m + 1) ^ k := by
    simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun j => m ^ j)]
    exact Cslib.sum_range_pow_le_add_one_pow m k
  calc μ {S | ε < error D (κ.learner S)}
      ≤ μ (⋃ ι, B ι) := measure_mono_ae hsub
    _ ≤ ∑ ι, μ (B ι) := measure_iUnion_fintype_le μ B
    _ ≤ ∑ _ι : Σ j : Fin (k + 1), Fin j → Fin m, (1 - ε) ^ (m - k) :=
        Finset.sum_le_sum fun ι _ => hB ι
    _ = Fintype.card (Σ j : Fin (k + 1), Fin j → Fin m) * (1 - ε) ^ (m - k) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((m + 1) ^ k : ℕ) * (1 - ε) ^ (m - k) := by
        gcongr

/-- **Sample compression schemes give PAC learners**: the learner of a scheme of size `k` with
measurable reconstruction is an `(ε, δ)`-PAC learner over the distributions realizable by `C`
from `m` examples whenever `(m + 1) ^ k (1 - ε) ^ (m - k) ≤ δ`. -/
theorem isPACLearnerFor (κ : SampleCompressionScheme C k)
    (hκ : MeasurableReconstruction κ.reconstruct) {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hm : ((m : ℝ) + 1) ^ k * (1 - (ε.val : ℝ)) ^ (m - k) ≤ δ.val) :
    IsPACLearnerFor m ε δ C (realizableDistributions C) := by
  refine ⟨κ.learner, fun D _ hD => ?_⟩
  rw [IsRealizableBy.optimalError_eq_zero hD, zero_add]
  refine (κ.measure_pi_lt_error_learner_le hκ hD m _).trans ?_
  have hε : ε.val ≤ 1 := ε.2.2.le
  have hm' : ((m + 1) ^ k : ℝ≥0) * (1 - ε.val) ^ (m - k) ≤ δ.val := by
    rw [← NNReal.coe_le_coe]
    push_cast [NNReal.coe_sub hε]
    exact hm
  calc (((m + 1) ^ k : ℕ) : ℝ≥0∞) * (1 - (ε.val : ℝ≥0∞)) ^ (m - k)
      = (((m + 1) ^ k * (1 - ε.val) ^ (m - k) : ℝ≥0) : ℝ≥0∞) := by
        push_cast [ENNReal.coe_sub]
        rfl
    _ ≤ δ.val := ENNReal.coe_le_coe.2 hm'

/-- The compression bound in logarithmic form: the learner of a scheme of size `k` with
measurable reconstruction is an `(ε, δ)`-PAC learner over the distributions realizable by `C`
from `m` examples whenever `k log (m + 1) + log (1 / δ) ≤ ε (m - k)`. -/
theorem isPACLearnerFor_of_log_le (κ : SampleCompressionScheme C k)
    (hκ : MeasurableReconstruction κ.reconstruct) {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}
    (hm : k * Real.log (m + 1) + Real.log (δ.val : ℝ)⁻¹ ≤ ε.val * (m - k : ℕ)) :
    IsPACLearnerFor m ε δ C (realizableDistributions C) := by
  refine κ.isPACLearnerFor hκ ?_
  have hδ : (0 : ℝ) < δ.val := by exact_mod_cast δ.2.1
  rw [Real.log_inv] at hm
  calc ((m : ℝ) + 1) ^ k * (1 - (ε.val : ℝ)) ^ (m - k)
      ≤ Real.exp (k * Real.log (m + 1)) * Real.exp (-(ε.val * (m - k : ℕ))) := by
        rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
        gcongr
        exact Real.one_sub_pow_le_exp (by exact_mod_cast ε.2.2.le) (by rw [mul_comm])
    _ ≤ δ.val := by
        rw [← Real.exp_add, ← Real.exp_log hδ]
        exact Real.exp_le_exp.2 (by linarith)

/-- For `0 < r < 1`, `(m + 1) ^ k r ^ (m - k) ≤ δ` for some `m`. -/
private theorem exists_pow_mul_pow_le (k : ℕ) {r δ : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hδ : 0 < δ) : ∃ m : ℕ, ((m : ℝ) + 1) ^ k * r ^ (m - k) ≤ δ := by
  have hlim : Tendsto (fun n : ℕ => ((n + (k + 1) : ℕ) : ℝ) ^ k * r ^ (n + (k + 1)))
      atTop (𝓝 0) :=
    (tendsto_pow_const_mul_const_pow_of_abs_lt_one k (by rwa [abs_of_pos hr0])).comp
      (tendsto_add_atTop_nat (k + 1))
  have hlim' := hlim.const_mul (r ^ (k + 1))⁻¹
  rw [mul_zero] at hlim'
  obtain ⟨n, hn⟩ := (hlim'.eventually (ge_mem_nhds hδ)).exists
  refine ⟨n + k, le_of_eq_of_le ?_ hn⟩
  have hrk : r ^ (k + 1) ≠ 0 := pow_ne_zero _ hr0.ne'
  simp only [Nat.add_sub_cancel]
  rw [pow_add r n (k + 1)]
  field_simp
  push_cast
  ring

/-- A class with a sample compression scheme of finite size and measurable reconstruction is PAC
learnable in the realizable setting [LittlestoneWarmuth1986]. -/
theorem isPACLearnable (κ : SampleCompressionScheme C k)
    (hκ : MeasurableReconstruction κ.reconstruct) :
    IsPACLearnable C (realizableDistributions C) := fun ε δ => by
  have hε0 : (0 : ℝ) < 1 - ε.val := sub_pos.2 (by exact_mod_cast ε.2.2)
  have hε1 : 1 - (ε.val : ℝ) < 1 := sub_lt_self _ (by exact_mod_cast ε.2.1)
  obtain ⟨m, hm⟩ := exists_pow_mul_pow_le k hε0 hε1 (by exact_mod_cast δ.2.1)
  exact ⟨m, κ.isPACLearnerFor hκ hm⟩

end SampleCompressionScheme

end Cslib.MachineLearning.PACLearning
