/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: vendored SamuelSchlesinger:feat/pac-learning-ehkv-headline @a9fb889df4 (unsubmitted)

public import Cslib.MachineLearning.PACLearning.VCDimension
public import CslibFrontier.MachineLearning.PACLearning.SampleComplexityLower.EHKVProof

-- vendored: the Theorem 1 entry below records the source's `δ ≤ 1/100` against this proof's
-- `δ < 1/14`.
/-! # Sample Complexity Lower Bound

We use the prefix `ehkv` for Ehrenfeucht–Haussler–Kearns–Valiant throughout.

This module formalizes the main result of [EHKV1989]: a lower bound on the
number of examples required for PAC learning of a binary concept class, in
terms of its Vapnik-Chervonenkis dimension.

The headline theorem is parameterized by an arbitrary distribution family
`𝒟 : Set (Measure (α × Bool))`. We require that `𝒟` contains all *realizable
distributions* for `C`, i.e. pushforwards `P.map (x ↦ (x, c x))` for any
probability measure `P : Measure α` and concept `c ∈ C`. The agnostic case
(`𝒟 = Set.univ`) and the (minimal) realizable case fall out as one-line
corollaries.

The argument uses a marginal-sample-space EHKV witness lemma (in
`SampleComplexityLower.EHKVProof`) and bridges to the joint-sample-space
failure event of `IsPACLearnerFor` / `IsRPACLearnerFor` via the
change-of-variables `pi_map_sampleOf` below.

## Main statements

- `pi_map_sampleOf`, `error_realizable_self_eq_zero`,
  `optimalError_realizable_eq_zero`: joint↔marginal bridge lemmas.
- `sample_complexity_lower_bound_randomized`: **Theorem 1** of [EHKV1989] for
  randomized learners, family-parametric, with the confidence range `δ < 1/14`
  in place of the source's `δ ≤ 1/100`.
- `sample_complexity_lower_bound`: deterministic corollary via
  `IsPACLearnerFor.toIsRPACLearnerFor`.
- `sample_complexity_lower_bound_agnostic_randomized`,
  `sample_complexity_lower_bound_agnostic`: agnostic specialization
  (`𝒟 = Set.univ`).
- `sample_complexity_lower_bound_vcDim`: randomized bound stated in terms of
  `vcDim`.
- `sampleComplexity_lower_bound_vcDim`,
  `rsampleComplexity_lower_bound_vcDim`: lower bounds on deterministic and
  randomized sample complexities phrased via `vcDim`.

## References

* [A. Ehrenfeucht, D. Haussler, M. Kearns, L. Valiant,
  *A General Lower Bound on the Number of Examples Needed
  for Learning*][EHKV1989]
-/

-- vendored: plain `public section`; the section exposes no definition (local changed-file lint).
public section

open MeasureTheory Set Finset
open scoped ENNReal NNReal

noncomputable section

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*} [MeasurableSpace α]

/-! ### Bridge lemmas: joint sample space ↔ marginal sample space -/

open Classical in
private lemma measurable_decide_mem {c : Set α} (hc : MeasurableSet c) :
    Measurable (fun x : α => decide (x ∈ c)) := by
  refine measurable_to_bool ?_
  have hset : (fun x : α => decide (x ∈ c)) ⁻¹' {true} = c := by
    ext x; exact decide_eq_true_iff
  rw [hset]; exact hc

private lemma measurable_graph_of_bool {c : α → Bool} (hc : Measurable c) :
    Measurable (fun x : α => (x, c x)) :=
  Measurable.prodMk measurable_id hc

private lemma measurableSet_ne_bool (h : α → Bool) (hh : Measurable h) :
    MeasurableSet {p : α × Bool | h p.1 ≠ p.2} := by
  have hrewrite : {p : α × Bool | h p.1 ≠ p.2} =
      ({x | h x = true} ×ˢ ({false} : Set Bool)) ∪
        ({x | h x = false} ×ˢ ({true} : Set Bool)) := by
    ext ⟨x, b⟩
    cases b <;> cases hx : h x <;> simp [hx]
  rw [hrewrite]
  refine MeasurableSet.union ?_ ?_
  · exact (hh (measurableSet_singleton true)).prod (measurableSet_singleton false)
  · exact (hh (measurableSet_singleton false)).prod (measurableSet_singleton true)

open Classical in
/-- The pi-product of pushforwards along `(x ↦ (x, decide (x ∈ c)))` equals the
pushforward of the pi-product along `sampleOf c`. -/
theorem pi_map_sampleOf
    {m : ℕ} (P : Measure α) [IsProbabilityMeasure P]
    {c : Set α} (hc : MeasurableSet c) :
    Measure.pi (fun _ : Fin m => P.map (fun x : α => (x, decide (x ∈ c)))) =
      (Measure.pi (fun _ : Fin m => P)).map (sampleOf c) := by
  have hmeasf : Measurable (fun x : α => (x, decide (x ∈ c))) :=
    Measurable.prodMk measurable_id (measurable_decide_mem hc)
  -- vendored: the pinned Mathlib makes `IsProbabilityMeasure (P.map f)` a global instance and
  -- removes `Measure.isProbabilityMeasure_map`, so the local instances are dropped.
  have hsampleOf_eq : (sampleOf c : (Fin m → α) → LabeledSample α Bool m) =
      (fun xs i => (fun x : α => (x, decide (x ∈ c))) (xs i)) := by
    funext xs i; rfl
  rw [hsampleOf_eq]
  exact (Measure.pi_map_pi (fun _ => hmeasf.aemeasurable)).symm

open Classical in
/-- The realizable joint distribution `P.map (x ↦ (x, c x))` has zero error
against `c` itself. -/
theorem error_realizable_self_eq_zero
    (P : Measure α) {c : α → Bool} (hc_meas : Measurable c) :
    error (P.map (fun x : α => (x, c x))) c = 0 := by
  simp only [error]
  rw [Measure.map_apply (measurable_graph_of_bool hc_meas) (measurableSet_ne_bool c hc_meas),
    show (fun x : α => (x, c x)) ⁻¹' {p : α × Bool | c p.1 ≠ p.2} = ∅ from by ext x; simp]
  exact measure_empty

open Classical in
/-- For a concept `c ∈ C`, the realizable distribution `P.map (x ↦ (x, c x))`
has `optimalError = 0`. -/
theorem optimalError_realizable_eq_zero
    (P : Measure α) {C : ConceptClass α Bool}
    {c : α → Bool} (hc : c ∈ C) (hc_meas : Measurable c) :
    optimalError (P.map (fun x : α => (x, c x))) C = 0 :=
  nonpos_iff_eq_zero.mp <|
    (iInf₂_le c hc).trans (error_realizable_self_eq_zero P hc_meas).le

/-! ### Bridge: finite-support equality of joint and marginal failure events -/

variable [MeasurableSingletonClass α]

open Classical in
/-- For a probability measure `P` supported on the finite set `↑W` and a
measurable concept `c`, the realizable pushforward `D = P.map (x ↦ (x, c x))`
is supported on the finite image `↑(W.image (graph c))`. -/
private lemma map_graph_supportedOn_image
    {P : Measure α} {W : Finset α} (hP_supp : P (↑W : Set α)ᶜ = 0)
    {c : α → Bool} (hc_meas : Measurable c) :
    (P.map (fun x : α => (x, c x)))
        (↑(W.image (fun x : α => (x, c x))) : Set (α × Bool))ᶜ = 0 := by
  have hmeasf := measurable_graph_of_bool hc_meas
  set V : Finset (α × Bool) := W.image (fun x : α => (x, c x))
  have hVc_meas : MeasurableSet (↑V : Set (α × Bool))ᶜ :=
    V.finite_toSet.measurableSet.compl
  rw [Measure.map_apply hmeasf hVc_meas]
  have hpre :
      (fun x : α => (x, c x)) ⁻¹' (↑V : Set (α × Bool))ᶜ = (↑W : Set α)ᶜ := by
    rw [Set.preimage_compl]
    congr 1
    ext x
    rw [Set.mem_preimage, Finset.mem_coe, Finset.mem_image]
    refine ⟨?_, ?_⟩
    · rintro ⟨y, hy, hxy⟩
      exact (Prod.mk.inj hxy).1 ▸ hy
    · intro hxW
      exact ⟨x, hxW, rfl⟩
  rw [hpre]; exact hP_supp

open Classical in
/-- **Key bridge lemma**: when `P` is supported on the finite set `↑W` and `c`
is measurable, the 0-1 `error` of *any* (possibly non-measurable) hypothesis
`h : α → Bool` under the realizable distribution `D = P.map (x ↦ (x, c x))`
collapses to the marginal-space `hypothesisError P (h ⁻¹' {true}) (c ⁻¹' {true})`.

The hypothesis `h` need not be measurable: since `D` is supported on a finite
set, every set in `α × Bool` is null-measurable w.r.t. `D`, and
`Measure.map_apply₀` applies. -/
-- vendored: the unused `[IsProbabilityMeasure P]` argument is dropped (`unusedArguments` linter).
private lemma error_map_eq_hypothesisError_set_finite_supp
    {P : Measure α}
    {W : Finset α} (hP_supp : P (↑W : Set α)ᶜ = 0)
    {c : α → Bool} (hc_meas : Measurable c) (h : α → Bool) :
    error (P.map (fun x : α => (x, c x))) h =
      hypothesisError P (h ⁻¹' {true}) (c ⁻¹' {true}) := by
  have hmeasf := measurable_graph_of_bool hc_meas
  let V : Finset (α × Bool) := W.image (fun x : α => (x, c x))
  have hVc_null : (P.map (fun x : α => (x, c x))) (↑V : Set (α × Bool))ᶜ = 0 :=
    map_graph_supportedOn_image hP_supp hc_meas
  have hSV_meas : MeasurableSet ({p : α × Bool | h p.1 ≠ p.2} ∩ ↑V) :=
    -- vendored: `fun _ hx => hx.2` no longer elaborates against the pinned Mathlib.
    (V.finite_toSet.subset Set.inter_subset_right).measurableSet
  have hSnull : NullMeasurableSet {p : α × Bool | h p.1 ≠ p.2}
      (P.map (fun x : α => (x, c x))) := by
    have heq : {p : α × Bool | h p.1 ≠ p.2} =
        ({p : α × Bool | h p.1 ≠ p.2} ∩ ↑V) ∪
          ({p : α × Bool | h p.1 ≠ p.2} \ ↑V) := by
      ext x; constructor
      · intro hx; by_cases hxV : x ∈ (↑V : Set (α × Bool))
        · exact Or.inl ⟨hx, hxV⟩
        · exact Or.inr ⟨hx, hxV⟩
      · rintro (⟨hxS, _⟩ | ⟨hxS, _⟩) <;> exact hxS
    rw [heq]
    refine NullMeasurableSet.union hSV_meas.nullMeasurableSet
      (NullMeasurableSet.of_null ?_)
    exact measure_mono_null (fun _ hx => hx.2) hVc_null
  simp only [error, hypothesisError]
  rw [Measure.map_apply₀ hmeasf.aemeasurable hSnull]
  congr 1
  ext x
  -- vendored: `sup_eq_union` is ambiguous with `Finset.sup_eq_union` under the pinned Mathlib,
  -- which also deprecates `Set.mem_setOf_eq` and `Set.mem_diff`.
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, symmDiff_def, Set.sup_eq_union,
    Set.mem_union, Set.mem_sdiff, Set.mem_singleton_iff]
  cases hhx : h x <;> cases hcx : c x <;> simp

open Classical in
/-- Pointwise equality of joint and marginal failure measures under a
realizable distribution `D = P.map (x ↦ (x, c x))` for `P` finitely supported.

This is the bridge used at the heart of the EHKV lower bound to translate the
new framework's `IsRPACLearnerFor` joint-sample-space failure event into the
marginal-sample-space failure event consumed by `exists_bad_concept_marginal`. -/
private lemma joint_failure_eq_marginal
    {m : ℕ} {P : Measure α} [IsProbabilityMeasure P]
    {W : Finset α} (hP_supp : P (↑W : Set α)ᶜ = 0)
    {c : α → Bool} (hc_meas : Measurable c)
    (A : LabeledSample α Bool m → α → Bool) (ε : ℝ≥0∞) :
    (Measure.pi (fun _ : Fin m => P.map (fun x : α => (x, c x))))
        {S : LabeledSample α Bool m |
          error (P.map (fun x : α => (x, c x))) (A S) > ε} =
      (Measure.pi (fun _ : Fin m => P))
        {xs : Fin m → α |
          hypothesisError P
            ((A (sampleOf (c ⁻¹' {true}) xs)) ⁻¹' {true})
            (c ⁻¹' {true}) > ε} := by
  have hc_set : MeasurableSet (c ⁻¹' {true}) := hc_meas (measurableSet_singleton true)
  have hgraph_eq : (fun x : α => (x, c x)) =
      (fun x : α => (x, decide (x ∈ c ⁻¹' {true}))) := by
    funext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    cases h : c x <;> simp
  have hπ_eq : Measure.pi (fun _ : Fin m => P.map (fun x : α => (x, c x))) =
      (Measure.pi (fun _ : Fin m => P)).map (sampleOf (c ⁻¹' {true})) := by
    rw [hgraph_eq]; exact pi_map_sampleOf P hc_set
  -- Pointwise: error D h = hypErr P (h⁻¹'{true}) (c⁻¹'{true}) for ANY h.
  have hev_rewrite :
      {S : LabeledSample α Bool m |
          error (P.map (fun x : α => (x, c x))) (A S) > ε} =
      {S : LabeledSample α Bool m |
          hypothesisError P ((A S) ⁻¹' {true}) (c ⁻¹' {true}) > ε} := by
    ext S
    -- vendored: `Set.mem_setOf_eq` is deprecated in the pinned Mathlib; `Set.mem_ofPred_eq`.
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq,
      error_map_eq_hypothesisError_set_finite_supp hP_supp hc_meas (A S)]
  rw [hev_rewrite, hπ_eq]
  -- Now apply Measure.map_apply₀ to the rewritten event.
  have hmeasSampleOf :
      Measurable (sampleOf (c ⁻¹' {true}) : (Fin m → α) → LabeledSample α Bool m) := by
    refine measurable_pi_iff.mpr fun i => ?_
    refine (measurable_pi_apply i).prodMk ?_
    exact (measurable_decide_mem hc_set).comp (measurable_pi_apply i)
  -- The rewritten event is null-measurable w.r.t. the pushforward measure
  -- (which equals `D^m`, a finitely-supported pi-product).
  have hnull : NullMeasurableSet
      {S : LabeledSample α Bool m |
        hypothesisError P ((A S) ⁻¹' {true}) (c ⁻¹' {true}) > ε}
      ((Measure.pi (fun _ : Fin m => P)).map (sampleOf (c ⁻¹' {true}))) := by
    rw [← hπ_eq]
    -- vendored: local `IsProbabilityMeasure (P.map _)` instance dropped, as above.
    exact nullMeasurableSet_pi_of_finite_support
      (map_graph_supportedOn_image hP_supp hc_meas) _
  rw [Measure.map_apply₀ hmeasSampleOf.aemeasurable hnull]
  rfl

/-! ### Headline EHKV lower bound -/

section EHKVLowerBound

variable {C : ConceptClass α Bool} {W : Finset α}
  {m : ℕ} {ε δ : Set.Ioo (0 : ℝ≥0) 1}

open Classical in
-- vendored: the Theorem 1 label is qualified with the source's confidence range (§3, Theorem 1
-- assumes `δ ≤ 1/100`); this proof's `δ < 1/14` is its own adaptation of the constants.
/-- **Theorem 1 (randomized, family-parametric)** [EHKV1989]:
The sample-complexity lower bound `(|W| - 1) / (32 ε) ≤ m` holds for
*randomized* `(ε, δ)`-PAC learners over any distribution family `𝒟` containing
all realizable distributions for `C`. [EHKV1989, §3, Theorem 1] states this
for `0 < δ ≤ 1/100`; the proof here allows the wider range `δ < 1/14`. -/
theorem sample_complexity_lower_bound_randomized
    (hW : SetShatters C ↑W) (hW_card : 2 ≤ W.card)
    (hε_le : ε.val.toReal ≤ 1 / 8)
    (hδ_lt : δ.val.toReal < 1 / 14)
    (hC_meas : ∀ c ∈ C, Measurable c)
    {𝒟 : Set (Measure (α × Bool))}
    (h_real : ∀ (P : Measure α), IsProbabilityMeasure P → ∀ c ∈ C,
      P.map (fun x : α => (x, c x)) ∈ 𝒟)
    (hlearn : IsRPACLearnerFor m ε δ C 𝒟) :
    (W.card - 1 : ℝ) / (32 * ε.val.toReal) ≤ m := by
  by_contra h
  push Not at h
  -- ε, δ in `ℝ≥0∞` form. The `nnreal_eq_ofReal_toReal` rewrite below converts
  -- `(x.val : ℝ≥0∞)` to `ENNReal.ofReal x.val.toReal`, enabling `ofReal`-style bounds.
  set εE : ℝ≥0∞ := (ε.val : ℝ≥0∞) with hεE_def
  set δE : ℝ≥0∞ := (δ.val : ℝ≥0∞) with hδE_def
  have hε'_pos : 0 < ε.val.toReal := NNReal.coe_pos.mpr ε.property.1
  have hεE_pos : 0 < εE := by rw [hεE_def]; exact_mod_cast ε.property.1
  have nnreal_eq_ofReal_toReal : ∀ (x : NNReal),
      (x : ℝ≥0∞) = ENNReal.ofReal x.toReal := fun _ => ENNReal.ofReal_coe_nnreal.symm
  have hεE_le : εE ≤ ENNReal.ofReal (1 / 8) := by
    rw [hεE_def, nnreal_eq_ofReal_toReal]
    exact ENNReal.ofReal_le_ofReal hε_le
  have hδE_lt : δE < ENNReal.ofReal (1 / 14) := by
    rw [hδE_def, nnreal_eq_ofReal_toReal]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hδ_lt
  have h32ε_pos : (0 : ℝ) < 32 * ε.val.toReal := by positivity
  have hW_sub : (0 : ℝ) < (W.card : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hW_card
    linarith
  have hε_toReal : ENNReal.toReal εE = ε.val.toReal := by rw [hεE_def]; simp
  have hm_ennreal : (↑m : ℝ≥0∞) < ENNReal.ofReal
      ((W.card - 1 : ℝ) / (32 * ENNReal.toReal εE)) := by
    rw [← ENNReal.ofReal_natCast (n := m), hε_toReal]
    exact (ENNReal.ofReal_lt_ofReal_iff (div_pos hW_sub h32ε_pos)).mpr h
  -- Project `C` to `Set α` via the characteristic-set map and verify shattering.
  set C_set : Set (Set α) := {s | ∃ c ∈ C, c ⁻¹' {true} = s}
  have hW_set : ∀ W' ⊆ (↑W : Set α), ∃ s ∈ C_set, s ∩ ↑W = W' := by
    intro W' hW'
    obtain ⟨c, hc, hc_eq⟩ := hW W' hW'
    exact ⟨c ⁻¹' {true}, ⟨c, hc, rfl⟩, hc_eq⟩
  -- Extract the randomized learner.
  obtain ⟨Ω, mΩ, Q, hQ, A, hA⟩ := hlearn
  -- Set-valued projection of the learner.
  let A_set : Ω → LabeledSample α Bool m → Set α :=
    fun ω S => (A ω S) ⁻¹' {true}
  -- For any realizable `c ∈ C`, the PAC bound at the realizable pushforward
  -- `D = P.map (x ↦ (x, c x))` collapses `optimalError = 0`.
  have collapsed : ∀ (P : Measure α) [IsProbabilityMeasure P] {c : α → Bool}, c ∈ C →
      AEMeasurable (fun ω => (Measure.pi (fun _ : Fin m => P.map (fun x => (x, c x))))
        {S : LabeledSample α Bool m |
          error (P.map (fun x => (x, c x))) (A ω S) > εE}) Q ∧
      ∫⁻ ω, (Measure.pi (fun _ : Fin m => P.map (fun x => (x, c x))))
        {S : LabeledSample α Bool m |
          error (P.map (fun x => (x, c x))) (A ω S) > εE} ∂Q ≤ ↑δ.val := by
    intro P hP_prob c hc
    have hc_meas := hC_meas c hc
    -- vendored: local `IsProbabilityMeasure (P.map _)` instance dropped, as above.
    have ⟨haem, hint⟩ := hA _ (h_real P hP_prob c hc)
    rw [optimalError_realizable_eq_zero P hc hc_meas, zero_add] at haem hint
    exact ⟨haem, hint⟩
  -- AE-measurability of marginal failure (for `P` supported on `↑W`) from
  -- joint AE-measurability via `joint_failure_eq_marginal`.
  have hA_aem : ∀ (P : Measure α) [IsProbabilityMeasure P],
      P (↑W : Set α)ᶜ = 0 → ∀ s ∈ C_set,
        AEMeasurable (fun ω => (Measure.pi (fun _ : Fin m => P))
          {xs : Fin m → α |
            hypothesisError P ((A_set ω) (sampleOf s xs)) s > εE}) Q := by
    intro P hP_prob hP_supp s hs
    obtain ⟨c_bool, hc_bool_mem, hc_bool_eq⟩ := hs
    have hcb_meas := hC_meas c_bool hc_bool_mem
    obtain ⟨hjoint_aem, _⟩ := collapsed P hc_bool_mem
    subst hc_bool_eq
    exact hjoint_aem.congr (Filter.Eventually.of_forall fun ω =>
      joint_failure_eq_marginal (m := m) hP_supp hcb_meas (A ω) εE)
  -- Apply the EHKV witness lemma.
  obtain ⟨P, hP_prob, hP_supp, c_set, hc_set_mem, hbad⟩ :=
    exists_bad_concept_marginal hW_set hW_card hεE_pos hεE_le hδE_lt
      hm_ennreal Q A_set hA_aem
  -- vendored: `haveI` becomes `have` (the pinned Mathlib's `haveI` style linter).
  have := hP_prob
  obtain ⟨c_bool, hc_bool_mem, hc_bool_eq⟩ := hc_set_mem
  have hcb_meas := hC_meas c_bool hc_bool_mem
  obtain ⟨_, hPAC⟩ := collapsed P hc_bool_mem
  -- Bridge: pointwise equality joint = marginal, hence the integrals agree.
  have hint_eq : ∫⁻ ω, (Measure.pi (fun _ : Fin m =>
        P.map (fun x : α => (x, c_bool x))))
          {S : LabeledSample α Bool m |
            error (P.map (fun x : α => (x, c_bool x))) (A ω S) > εE} ∂Q =
      ∫⁻ ω, (Measure.pi (fun _ : Fin m => P))
        {xs : Fin m → α |
          hypothesisError P ((A_set ω) (sampleOf c_set xs)) c_set > εE} ∂Q := by
    subst hc_bool_eq
    exact lintegral_congr fun ω => joint_failure_eq_marginal hP_supp hcb_meas (A ω) εE
  -- Combine: ∫ marginal ≤ δE  (from PAC + bridge) contradicts δE < ∫ marginal.
  rw [hint_eq] at hPAC
  exact absurd hPAC (not_le.mpr hbad)

/-- Deterministic specialization via `IsPACLearnerFor.toIsRPACLearnerFor`. -/
theorem sample_complexity_lower_bound
    (hW : SetShatters C ↑W) (hW_card : 2 ≤ W.card)
    (hε_le : ε.val.toReal ≤ 1 / 8)
    (hδ_lt : δ.val.toReal < 1 / 14)
    (hC_meas : ∀ c ∈ C, Measurable c)
    {𝒟 : Set (Measure (α × Bool))}
    (h_real : ∀ (P : Measure α), IsProbabilityMeasure P → ∀ c ∈ C,
      P.map (fun x : α => (x, c x)) ∈ 𝒟)
    (hlearn : IsPACLearnerFor m ε δ C 𝒟) :
    (W.card - 1 : ℝ) / (32 * ε.val.toReal) ≤ m :=
  sample_complexity_lower_bound_randomized hW hW_card hε_le hδ_lt hC_meas h_real
    (IsPACLearnerFor.toIsRPACLearnerFor.{_, _, 0} hlearn)

/-- Agnostic specialization (`𝒟 = Set.univ`): the realizable distributions are
trivially included.

Loose: this is the realizable bound applied to the agnostic case; the tight
agnostic rate is `Ω(d/ε²)` (see TODO at the bottom of this file). -/
theorem sample_complexity_lower_bound_agnostic_randomized
    (hW : SetShatters C ↑W) (hW_card : 2 ≤ W.card)
    (hε_le : ε.val.toReal ≤ 1 / 8)
    (hδ_lt : δ.val.toReal < 1 / 14)
    (hC_meas : ∀ c ∈ C, Measurable c)
    (hlearn : IsRPACLearnerFor m ε δ C Set.univ) :
    (W.card - 1 : ℝ) / (32 * ε.val.toReal) ≤ m :=
  sample_complexity_lower_bound_randomized hW hW_card hε_le hδ_lt hC_meas
    (fun _ _ _ _ => Set.mem_univ _) hlearn

/-- Deterministic agnostic specialization. -/
theorem sample_complexity_lower_bound_agnostic
    (hW : SetShatters C ↑W) (hW_card : 2 ≤ W.card)
    (hε_le : ε.val.toReal ≤ 1 / 8)
    (hδ_lt : δ.val.toReal < 1 / 14)
    (hC_meas : ∀ c ∈ C, Measurable c)
    (hlearn : IsPACLearnerFor m ε δ C Set.univ) :
    (W.card - 1 : ℝ) / (32 * ε.val.toReal) ≤ m :=
  sample_complexity_lower_bound_agnostic_randomized hW hW_card hε_le hδ_lt hC_meas
    (IsPACLearnerFor.toIsRPACLearnerFor.{_, _, 0} hlearn)

/-- **Corollary**: the EHKV lower bound stated in terms of `vcDim`.

The `HasFiniteVCDim C` hypothesis is what makes `vcDim C` mathematically
meaningful: it guarantees the indexing set of shattered cardinalities is
bounded, so `sSup` returns the actual maximum rather than `0` (its default
on unbounded `ℕ`-sets). See `hasFiniteVCDim_iff` for the more intuitive
"exists a uniform bound on shattered cardinalities" reformulation. -/
theorem sample_complexity_lower_bound_vcDim
    (hε_le : ε.val.toReal ≤ 1 / 8)
    (hδ_lt : δ.val.toReal < 1 / 14)
    (hvc : 2 ≤ vcDim C)
    (hbdd : HasFiniteVCDim C)
    (hC_meas : ∀ c ∈ C, Measurable c)
    {𝒟 : Set (Measure (α × Bool))}
    (h_real : ∀ (P : Measure α), IsProbabilityMeasure P → ∀ c ∈ C,
      P.map (fun x : α => (x, c x)) ∈ 𝒟)
    (hlearn : IsRPACLearnerFor m ε δ C 𝒟) :
    (vcDim C - 1 : ℝ) / (32 * ε.val.toReal) ≤ m := by
  set S := {n : ℕ | ∃ W : Finset α, W.card = n ∧ SetShatters C (↑W)}
  have hne : S.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have : (2 : ℕ) ≤ sSup (∅ : Set ℕ) := hempty ▸ hvc
    simp at this
  obtain ⟨W, hWcard, hW⟩ := Nat.sSup_mem hne hbdd
  have hW_card : 2 ≤ W.card := hWcard ▸ hvc
  have hvc_eq : vcDim C = W.card := hWcard.symm
  simp only [hvc_eq]
  exact sample_complexity_lower_bound_randomized hW hW_card hε_le hδ_lt hC_meas
    h_real hlearn

/-- Lower bound on deterministic sample complexity in terms of `vcDim`. -/
theorem sampleComplexity_lower_bound_vcDim
    (hε_le : ε.val.toReal ≤ 1 / 8)
    (hδ_lt : δ.val.toReal < 1 / 14)
    (hvc : 2 ≤ vcDim C)
    (hbdd : HasFiniteVCDim C)
    (hC_meas : ∀ c ∈ C, Measurable c)
    {𝒟 : Set (Measure (α × Bool))}
    (h_real : ∀ (P : Measure α), IsProbabilityMeasure P → ∀ c ∈ C,
      P.map (fun x : α => (x, c x)) ∈ 𝒟)
    (hlearnable : {n : ℕ | IsPACLearnerFor n ε δ C 𝒟}.Nonempty) :
    (vcDim C - 1 : ℝ) / (32 * ε.val.toReal) ≤ sampleComplexity IsPACLearnerFor C ε δ 𝒟 := by
  have hmem : IsPACLearnerFor _ ε δ C 𝒟 := Nat.sInf_mem hlearnable
  exact sample_complexity_lower_bound_vcDim hε_le hδ_lt hvc hbdd hC_meas h_real
    (IsPACLearnerFor.toIsRPACLearnerFor.{_, _, 0} hmem)

/-- Lower bound on randomized sample complexity in terms of `vcDim`. -/
theorem rsampleComplexity_lower_bound_vcDim
    (hε_le : ε.val.toReal ≤ 1 / 8)
    (hδ_lt : δ.val.toReal < 1 / 14)
    (hvc : 2 ≤ vcDim C)
    (hbdd : HasFiniteVCDim C)
    (hC_meas : ∀ c ∈ C, Measurable c)
    {𝒟 : Set (Measure (α × Bool))}
    (h_real : ∀ (P : Measure α), IsProbabilityMeasure P → ∀ c ∈ C,
      P.map (fun x : α => (x, c x)) ∈ 𝒟)
    (hlearnable : {n : ℕ | IsRPACLearnerFor.{_, _, 0} n ε δ C 𝒟}.Nonempty) :
    (vcDim C - 1 : ℝ) / (32 * ε.val.toReal) ≤ rsampleComplexity C ε δ 𝒟 := by
  have hmem : IsRPACLearnerFor _ ε δ C 𝒟 := Nat.sInf_mem hlearnable
  exact sample_complexity_lower_bound_vcDim hε_le hδ_lt hvc hbdd hC_meas h_real hmem

end EHKVLowerBound

-- TODO: tight agnostic lower bound `Ω(d/ε²)` via Assouad's lemma. The
-- `*_agnostic{,_randomized}` corollaries above instantiate the realizable
-- EHKV bound at `𝒟 = univ` and so inherit its `Ω(d/ε)` rate. The tight rate
-- needs Pinsker + a packaged TV-distance on probability measures, neither in
-- Mathlib yet. Anthony-Bartlett 1999 Thm 5.2.

end Cslib.MachineLearning.PACLearning
