/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: vendored SamuelSchlesinger:feat/pac-learning-ehkv-headline @a9fb889df4 (unsubmitted)

public import CslibFrontier.MachineLearning.PACLearning.SampleComplexityLower.AdversarialMeasure
public import CslibFrontier.MachineLearning.PACLearning.SampleComplexityLower.InvolutionPairing

-- vendored: the Lemma 3 entry below records the source's `δ ≤ 1/100` against this proof's
-- `δ < 1/14`.
/-! # EHKV Proof Assembly

This module assembles the Markov bound, involution pairing, and adversarial
measure construction into the marginal-sample-space form of the EHKV proof.

The lower-bound argument here works on the marginal sample space `Fin m → α`
under a probability measure `P : Measure α`, with concepts viewed as
`Set α`. The translation to the joint sample space `LabeledSample α Bool m`
under a realizable distribution `D = P.map (x ↦ (x, c x))` is performed in
`SampleComplexityLower.lean` via `pi_map_sampleOf`.

## Main statements

- `markov_bad_samples`: **Lemma 3** [EHKV1989] — bad samples occur with
  probability `> 1/2` when the sample size is too small. The source proves its
  lemmas within Theorem 1's confidence range `δ ≤ 1/100`; this development
  adapts the argument to `δ < 1/14`.
- `ehkv_sum_lower_bound`: the half-fraction sum lower bound via involution.
- `ehkv_final_contradiction`: the final arithmetic contradiction.
- `exists_bad_concept_marginal`: for any set-valued learner with too few
  samples, there exists a concept among `2^d` shattered concepts whose
  marginal-sample-space failure measure exceeds `δ`. Used as a black box by
  the top-level `SampleComplexityLower` theorems via `pi_map_sampleOf`.

## References

* [A. Ehrenfeucht, D. Haussler, M. Kearns, L. Valiant,
  *A General Lower Bound on the Number of Examples Needed
  for Learning*][EHKV1989]
-/

-- vendored: plain `public section`; the section exposes no definition (local changed-file lint).
public section

open MeasureTheory Set Finset
open scoped ENNReal

noncomputable section

namespace Cslib.MachineLearning.PACLearning

section EHKVProof

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

open Classical in
-- vendored: the Lemma 3 label is qualified: the source works with Theorem 1's `δ ≤ 1/100`, and
-- this development adapts the argument to `δ < 1/14`.
/-- **Lemma 3** [EHKV1989]: Markov bound on bad samples (in the form used for this
development's confidence range `δ < 1/14`; the source states its lemmas for `δ ≤ 1/100`).

When the sample size `m` satisfies `m < d / (32ε)`, the probability
(under the product measure `P^m`) that the sample reveals at most
half of the shattered set `W'` exceeds `1/2`. -/
theorem markov_bad_samples
    {W : Finset α} {w₀ : α} (hw₀ : w₀ ∈ W)
    (hW_card : 2 ≤ W.card)
    {ε' : ℝ} (hε'_pos : 0 < ε') (hε'_le : ε' ≤ 1 / 8)
    {m : ℕ} (hm : (m : ℝ) < ((W.erase w₀).card : ℝ) / (32 * ε'))
    (P : Measure α) [IsProbabilityMeasure P]
    (hP_w : ∀ w ∈ W.erase w₀,
      P {w} = ENNReal.ofReal (8 * ε' / (W.erase w₀).card)) :
    ENNReal.ofReal (1 / 2) <
      (Measure.pi (fun _ : Fin m => P))
        {xs : Fin m → α |
          (seenElements (W.erase w₀) xs).card ≤ (W.erase w₀).card / 2} := by
  set W' := W.erase w₀ with hW'_def
  set d := W'.card with hd_def
  set μ := Measure.pi (fun _ : Fin m => P)
  -- vendored: `haveI` becomes `have` and `Set.mem_setOf_eq` becomes `Set.mem_ofPred_eq` in this
  -- proof, for the pinned Mathlib's `haveI` style linter and deprecation.
  have hμ_prob : IsProbabilityMeasure μ := Measure.pi.instIsProbabilityMeasure _
  have hd_pos : 0 < d := by rw [hd_def, hW'_def, card_erase_of_mem hw₀]; omega
  have hd_cast : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd_pos
  have hp_nonneg : (0 : ℝ) ≤ 8 * ε' / d := by positivity
  have hp_le_one : 8 * ε' / d ≤ 1 := by
    rw [div_le_one hd_cast]
    linarith [show (1 : ℝ) ≤ d from by exact_mod_cast hd_pos]
  have hf_meas : Measurable (fun xs : Fin m → α => ((seenElements W' xs).card : ℝ≥0∞)) :=
    measurable_seenElements_card W'
  set good : Set (Fin m → α) := {xs | (seenElements W' xs).card ≤ d / 2}
  set bad : Set (Fin m → α) := {xs | d / 2 < (seenElements W' xs).card}
  have hgood_compl_bad : good = badᶜ := by
    ext xs; simp only [good, bad, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt]
  have hbad_meas : MeasurableSet bad := by
    have : bad = {xs | ((d / 2 : ℕ) : ℝ≥0∞) < ((seenElements W' xs).card : ℝ≥0∞)} := by
      ext xs; simp only [bad, Set.mem_ofPred_eq, Nat.cast_lt]
    rw [this]; exact measurableSet_lt measurable_const hf_meas
  have hE_bound : ∫⁻ xs, ((seenElements W' xs).card : ℝ≥0∞) ∂μ
      ≤ ENNReal.ofReal (8 * ↑m * ε') :=
    calc ∫⁻ xs, ((seenElements W' xs).card : ℝ≥0∞) ∂μ
        ≤ ENNReal.ofReal (↑d * (↑m * (8 * ε' / ↑d))) :=
          expected_seenElements_le hp_nonneg hp_le_one P hP_w
      _ = ENNReal.ofReal (8 * ↑m * ε') := by congr 1; field_simp
  set k := d / 2 + 1
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  have hbad_eq : bad = {xs | (k : ℝ≥0∞) ≤ ((seenElements W' xs).card : ℝ≥0∞)} := by
    ext xs; simp only [bad, Set.mem_ofPred_eq, Nat.cast_le]; omega
  have hbad_bound : μ bad ≤ ENNReal.ofReal (8 * ↑m * ε' / ↑k) := by
    rw [hbad_eq]
    calc μ {xs | (k : ℝ≥0∞) ≤ ↑(seenElements W' xs).card}
        ≤ (∫⁻ xs, ↑(seenElements W' xs).card ∂μ) / ↑k :=
          meas_ge_le_lintegral_div hf_meas.aemeasurable
            (by exact_mod_cast (show k ≠ 0 by omega)) (ENNReal.natCast_ne_top k)
      _ ≤ ENNReal.ofReal (8 * ↑m * ε') / ↑k :=
          ENNReal.div_le_div_right hE_bound _
      _ = ENNReal.ofReal (8 * ↑m * ε') / ENNReal.ofReal (↑k) := by
          rw [ENNReal.ofReal_natCast]
      _ = ENNReal.ofReal (8 * ↑m * ε' / ↑k) :=
          (ENNReal.ofReal_div_of_pos hk_pos).symm
  have harith : 8 * ↑m * ε' / ↑k < 1 / 2 := by
    have h8mε : 8 * (m : ℝ) * ε' < (↑d : ℝ) / 4 := by
      calc 8 * (m : ℝ) * ε' < 8 * ((↑d : ℝ) / (32 * ε')) * ε' :=
            mul_lt_mul_of_pos_right (by linarith) hε'_pos
        _ = ↑d / 4 := by field_simp; ring
    have h2k : (d : ℝ) < 2 * ↑k := by
      exact_mod_cast (show d < 2 * k from by omega)
    calc 8 * ↑m * ε' / ↑k
        < (↑d / 4) / ↑k := div_lt_div_of_pos_right h8mε hk_pos
      _ = ↑d / (4 * ↑k) := by ring
      _ < 1 / 2 := by
          rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * ↑k)]; linarith
  have hbad_lt : μ bad < ENNReal.ofReal (1 / 2) := calc
    μ bad ≤ ENNReal.ofReal (8 * ↑m * ε' / ↑k) := hbad_bound
    _ < ENNReal.ofReal (1 / 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1 / 2)).mpr harith
  rw [hgood_compl_bad]
  have hfin : μ bad ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hbad_lt ENNReal.ofReal_lt_top.le)
  have h_sum := prob_add_prob_compl hbad_meas (μ := μ)
  rw [← ENNReal.add_lt_add_iff_left hfin, h_sum]
  calc μ bad + ENNReal.ofReal (1 / 2)
      < ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hbad_lt
    _ = ENNReal.ofReal 1 := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
    _ = 1 := ENNReal.ofReal_one

open Classical in
/-- Per-learner half-fraction sum lower bound: for any set-valued learner `A'`
and any assignment of concepts to subsets of `W' = W \ {w₀}` satisfying the
shattering intersection property, the weighted measure of "bad" samples is
bounded by the sum of failure measures over the powerset. -/
theorem ehkv_sum_lower_bound
    {W : Finset α}
    (hW_card : 2 ≤ W.card)
    {w₀ : α} (hw₀ : w₀ ∈ W)
    {ε' : ℝ} (hε'_pos : 0 < ε')
    {m : ℕ}
    (A' : LabeledSample α Bool m → Set α)
    (P : Measure α) [IsProbabilityMeasure P]
    (hP_w : ∀ w ∈ W.erase w₀,
      P {w} = ENNReal.ofReal (8 * ε' / (W.erase w₀).card))
    (hP_supp : P (↑W : Set α)ᶜ = 0)
    (concepts : Finset α → Set α)
    (hconcepts_eq : ∀ S ∈ (W.erase w₀).powerset,
      concepts S ∩ ↑W = {w₀} ∪ ↑S) :
    (2 ^ (W.erase w₀).card / 2 : ℕ) •
      (Measure.pi (fun _ : Fin m => P))
        {xs : Fin m → α |
          (seenElements (W.erase w₀) xs).card ≤ (W.erase w₀).card / 2} ≤
      ∑ S ∈ (W.erase w₀).powerset,
        (Measure.pi (fun _ : Fin m => P))
          {xs : Fin m → α |
            hypothesisError P (A' (sampleOf (concepts S) xs)) (concepts S) >
              ENNReal.ofReal ε'} := by
  set W' := W.erase w₀ with hW'_def
  set d := W'.card with hd_def
  set μ := Measure.pi (fun _ : Fin m => P)
  have hd_pos : 0 < d := by rw [hd_def, hW'_def, card_erase_of_mem hw₀]; omega
  let cMap : (S : Finset α) → S ∈ W'.powerset → Set α := fun S _ => concepts S
  set fail : Set α → Set (Fin m → α) :=
    fun c => {xs | hypothesisError P (A' (sampleOf c xs)) c > ENNReal.ofReal ε'} with hfail_def
  set B := {xs : Fin m → α | (seenElements W' xs).card ≤ d / 2}
  set Wm := {xs : Fin m → α | ∀ i, xs i ∈ (↑W : Set α)}
  have hμ_supp : μ Wmᶜ = 0 := pi_measure_compl_zero hP_supp
  have hWm_ae : Wm ∈ (ae μ) := mem_ae_iff.mpr hμ_supp
  have hnull_meas : ∀ (S : Set (Fin m → α)), NullMeasurableSet S μ :=
    nullMeasurableSet_pi_of_finite_support hP_supp
  have hhalf_fraction : ∀ xs, xs ∈ B → xs ∈ Wm →
      (2 ^ d / 2 : ℕ) ≤ (W'.powerset.filter (fun S => xs ∈ fail (concepts S))).card := by
    intro xs hxs_bad hxs_Wm
    let T := seenElements W' xs
    let U := W' \ T
    let σ : Finset α → Finset α := fun S => (S ∩ T) ∪ (U \ S)
    have hσ_self : ∀ S, S ∈ W'.powerset → σ (σ S) = S := by
      intro S hS; rw [Finset.mem_powerset] at hS
      ext x; simp only [σ, U, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto
    have hσ_mem : ∀ S ∈ W'.powerset, σ S ∈ W'.powerset := by
      intro S hS; rw [Finset.mem_powerset] at hS ⊢
      exact union_subset (inter_subset_left.trans hS) (sdiff_subset.trans sdiff_subset)
    have hσ_agree_T : ∀ S, σ S ∩ T = S ∩ T := by
      intro S; ext x
      simp only [σ, U, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]; tauto
    have hpairing : ∀ S ∈ W'.powerset,
        xs ∈ fail (concepts S) ∨ xs ∈ fail (concepts (σ S)) := by
      intro S hS
      have hσS_mem := hσ_mem S hS
      have h_sample_agree : ∀ i, xs i ∈ concepts S ↔ xs i ∈ concepts (σ S) :=
        concepts_agree_of_seen_inter cMap hconcepts_eq hS hσS_mem
          (by rw [Finset.inter_comm, hσ_agree_T, Finset.inter_comm]) hxs_Wm
      have h_same_sample : sampleOf (concepts S) xs = sampleOf (concepts (σ S)) xs :=
        sampleOf_eq_of_agree h_sample_agree
      set h₀_local := A' (sampleOf (concepts S) xs)
      have hU_in_S : ∀ w ∈ U, w ∈ S → w ∉ σ S := by
        intro w hwU hwS
        simp only [σ, U, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at *; tauto
      have hU_not_S : ∀ w ∈ U, w ∉ S → w ∈ σ S := by
        intro w hwU hwnS
        simp only [σ, Finset.mem_union, Finset.mem_sdiff]; exact Or.inr ⟨hwU, hwnS⟩
      have hU_sub_symmDiff : (↑U : Set α) ⊆
          symmDiff h₀_local (concepts S) ∪ symmDiff h₀_local (concepts (σ S)) := by
        intro w hwU
        have hwU' := mem_coe.mp hwU
        have hwW : w ∈ (↑W : Set α) :=
          mem_coe.mpr (erase_subset _ _ (Finset.sdiff_subset hwU'))
        have hw_ne_w₀ : w ≠ w₀ := Finset.ne_of_mem_erase (Finset.sdiff_subset hwU')
        -- For any S' ∈ W'.powerset and w ≠ w₀ with w ∈ W: w ∈ concepts S' ↔ w ∈ S'.
        have hmem_iff : ∀ {S' : Finset α} (hS' : S' ∈ W'.powerset),
            w ∈ concepts S' ↔ w ∈ S' := by
          intro S' hS'
          refine ⟨fun hw => ?_, fun hw => ?_⟩
          · have : w ∈ concepts S' ∩ ↑W := ⟨hw, hwW⟩
            rw [hconcepts_eq S' hS'] at this
            exact this.resolve_left (hw_ne_w₀ ∘ Set.mem_singleton_iff.mp) |> mem_coe.mp
          · have : w ∈ ({w₀} ∪ ↑S' : Set α) := Or.inr (mem_coe.mpr hw)
            rw [← hconcepts_eq S' hS'] at this; exact this.1
        -- Place w in the appropriate symmDiff based on its h₀_local membership.
        have hplace : ∀ {A B : Set α}, w ∈ A → w ∉ B →
            w ∈ symmDiff h₀_local A ∨ w ∈ symmDiff h₀_local B := by
          intro A B hwA hwB
          by_cases hwh : w ∈ h₀_local
          · exact Or.inr (Set.mem_symmDiff.mpr (Or.inl ⟨hwh, hwB⟩))
          · exact Or.inl (Set.mem_symmDiff.mpr (Or.inr ⟨hwA, hwh⟩))
        by_cases hwS : w ∈ S
        · exact hplace ((hmem_iff hS).mpr hwS)
            (mt (hmem_iff hσS_mem).mp (hU_in_S w hwU' hwS))
        · exact (hplace ((hmem_iff hσS_mem).mpr (hU_not_S w hwU' hwS))
            (mt (hmem_iff hS).mp hwS)).symm
      have hT_sub_W' : T ⊆ W' := filter_subset _ _
      have h2U : d ≤ 2 * U.card := by
        have hTeq : U.card = d - T.card := card_sdiff_of_subset hT_sub_W'
        have hTle : T.card ≤ d / 2 := hxs_bad
        omega
      have hP_U : ENNReal.ofReal (4 * ε') ≤ P (↑U) :=
        unseen_measure_ge hε'_pos (by omega) h2U
          (fun w hw => hP_w w (Finset.sdiff_subset hw))
      by_contra h_neither
      push Not at h_neither
      obtain ⟨hS_ok, hσS_ok⟩ := h_neither
      -- vendored: `Set.mem_setOf_eq` is deprecated in the pinned Mathlib; `Set.mem_ofPred_eq`.
      simp only [hfail_def, Set.mem_ofPred_eq, not_lt] at hS_ok hσS_ok
      rw [show A' (sampleOf (concepts (σ S)) xs) = h₀_local from
        congr_arg A' h_same_sample.symm] at hσS_ok
      exact complementary_error_contradiction hε'_pos hU_sub_symmDiff hP_U hS_ok hσS_ok
    rw [show 2 ^ d / 2 = W'.powerset.card / 2 from by rw [card_powerset]]
    have := involution_half_count (P := fun S => xs ∈ fail (concepts S))
      hσ_self hσ_mem hpairing
    convert this
  have haem : ∀ S ∈ W'.powerset,
      AEMeasurable (fun xs =>
        (fail (concepts S)).indicator (1 : (Fin m → α) → ℝ≥0∞) xs) μ :=
    fun S _ => (aemeasurable_indicator_const_iff (1 : ℝ≥0∞)).mpr (hnull_meas _)
  have hsum_eq_integral :
      ∑ S ∈ W'.powerset, μ (fail (concepts S)) =
      ∫⁻ xs, ∑ S ∈ W'.powerset, (fail (concepts S)).indicator 1 xs ∂μ := by
    rw [lintegral_finsetSum' _ haem]
    congr 1; ext S
    exact (lintegral_indicator_one₀ (hnull_meas _)).symm
  rw [hsum_eq_integral, nsmul_eq_mul]
  rw [show (↑(2 ^ d / 2 : ℕ) : ℝ≥0∞) * μ B =
      ∫⁻ xs, B.indicator (fun _ => (↑(2 ^ d / 2 : ℕ) : ℝ≥0∞)) xs ∂μ from
    (lintegral_indicator_const₀ (hnull_meas _) _).symm]
  apply lintegral_mono_ae
  filter_upwards [hWm_ae] with xs hxs_Wm
  by_cases hxs_B : xs ∈ B
  · simp only [Set.indicator_apply, hxs_B, ite_true, Pi.one_apply]
    rw [Finset.sum_boole]
    exact_mod_cast hhalf_fraction xs hxs_B hxs_Wm
  · simp only [Set.indicator_apply, hxs_B, ite_false]; exact bot_le

/-- The final arithmetic contradiction in the EHKV argument: if `(2^d/2) • μ(B) <
`2^d • (1/14)` but `1/2 < μ(B)`, then `μ(B) ≤ 1/7 < 1/2`, a contradiction. -/
theorem ehkv_final_contradiction
    {d : ℕ} (hd_pos : 0 < d) {μB : ℝ≥0∞}
    (hB_prob : ENNReal.ofReal (1 / 2) < μB)
    (h_combined : (2 ^ d / 2 : ℕ) • μB < (2 ^ d : ℕ) • ENNReal.ofReal (1 / 14)) : False := by
  have hB_upper : μB ≤ ENNReal.ofReal (1 / 7) := by
    have h2d_nat : (2 ^ d : ℕ) = 2 * (2 ^ d / 2) :=
      Nat.eq_mul_of_div_eq_right (dvd_pow_self 2 (by omega : d ≠ 0)) rfl
    rw [nsmul_eq_mul, nsmul_eq_mul] at h_combined
    have h_rhs : (↑(2 ^ d : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 14) =
        ↑(2 ^ d / 2 : ℕ) * ENNReal.ofReal (1 / 7) := by
      calc (↑(2 ^ d : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 14)
          = ↑(2 * (2 ^ d / 2) : ℕ) * ENNReal.ofReal (1 / 14) := by rw [← h2d_nat]
        _ = (2 * ↑(2 ^ d / 2 : ℕ)) * ENNReal.ofReal (1 / 14) := by push_cast; ring_nf
        _ = ↑(2 ^ d / 2 : ℕ) * (2 * ENNReal.ofReal (1 / 14)) := by ring
        _ = ↑(2 ^ d / 2 : ℕ) * ENNReal.ofReal (1 / 7) := by
            congr 1
            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by norm_num,
              ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            congr 1; norm_num
    rw [h_rhs] at h_combined
    exact (lt_of_mul_lt_mul_left' h_combined).le
  exact absurd hB_prob
    (not_lt.mpr (hB_upper.trans (ENNReal.ofReal_le_ofReal (by norm_num : (1:ℝ)/7 ≤ 1/2))))

open Classical in
/-- **Marginal-space EHKV witness lemma**: If the sample size `m` is strictly
less than `(|W|-1)/(32ε)`, then for any *randomized* set-valued learner
`(Ω, Q, A)` such that each per-concept failure event has a measurable failure
function, there exist a concept `c` among the `2^d` shattered concepts and an
adversarial measure `P` such that the marginal-sample-space integrated failure
exceeds `δ`.

This is the marginal-space form of EHKV; the headline `IsRPACLearnerFor`
lower bound in `SampleComplexityLower.lean` follows by translating the
joint-sample-space failure event to this marginal form via `pi_map_sampleOf`. -/
theorem exists_bad_concept_marginal
    {C_set : Set (Set α)}
    {W : Finset α} (hW : ∀ W' ⊆ (↑W : Set α), ∃ c ∈ C_set, c ∩ ↑W = W')
    (hW_card : 2 ≤ W.card)
    {m : ℕ} {ε δ : ℝ≥0∞}
    (hε_pos : 0 < ε) (hε_le : ε ≤ ENNReal.ofReal (1 / 8))
    (hδ_lt : δ < ENNReal.ofReal (1 / 14))
    (hm : (↑m : ℝ≥0∞) < ENNReal.ofReal
      ((W.card - 1 : ℝ) / (32 * ENNReal.toReal ε)))
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (A : Ω → LabeledSample α Bool m → Set α)
    (hA_aem : ∀ (P : Measure α) [IsProbabilityMeasure P],
      P (↑W : Set α)ᶜ = 0 → ∀ c ∈ C_set,
        AEMeasurable (fun ω => (Measure.pi (fun _ : Fin m => P))
          {xs : Fin m → α | hypothesisError P ((A ω) (sampleOf c xs)) c > ε}) Q) :
    ∃ (P : Measure α) (_ : IsProbabilityMeasure P) (_ : P (↑W : Set α)ᶜ = 0),
    ∃ c ∈ C_set,
      δ < ∫⁻ ω, (Measure.pi (fun _ : Fin m => P))
        {xs : Fin m → α |
          hypothesisError P ((A ω) (sampleOf c xs)) c > ε} ∂Q := by
  have hε_ne_top : ε ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hε_le
  set ε' := ε.toReal with hε'_def
  have hε'_pos : 0 < ε' := ENNReal.toReal_pos (ne_of_gt hε_pos) hε_ne_top
  have hε'_le : ε' ≤ 1 / 8 := by
    rw [hε'_def]
    have := (ENNReal.toReal_le_toReal hε_ne_top ENNReal.ofReal_ne_top).mpr hε_le
    rwa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 8)] at this
  have hε_eq : ENNReal.ofReal ε' = ε := ENNReal.ofReal_toReal hε_ne_top
  have hW_nonempty : W.Nonempty := card_pos.mp (by omega)
  obtain ⟨w₀, hw₀⟩ := hW_nonempty
  set W' := W.erase w₀ with hW'_def
  set d := W'.card with hd_def
  have hd : 1 ≤ W'.card := by rw [hW'_def, card_erase_of_mem hw₀]; omega
  have hd_pos : 0 < d := by omega
  set P := adversarialMeasure W w₀ ε'
  have hP_prob : IsProbabilityMeasure P :=
    adversarialMeasure_isProbabilityMeasure hε'_pos hε'_le hd
  have hP_w : ∀ w ∈ W', P {w} = ENNReal.ofReal (8 * ε' / W'.card) :=
    fun w hw => adversarialMeasure_singleton hw
  have hP_supp : P (↑W : Set α)ᶜ = 0 := adversarialMeasure_support hw₀
  have hm_real : (m : ℝ) < (W'.card : ℝ) / (32 * ε') := by
    have hW'_eq : (W'.card : ℝ) = (W.card : ℝ) - 1 := by
      rw [hW'_def, card_erase_of_mem hw₀]
      simp [Nat.cast_sub (by omega : 1 ≤ W.card)]
    rw [hW'_eq]
    have h32ε_pos : (0 : ℝ) < 32 * ε' := by positivity
    rw [← ENNReal.ofReal_natCast (n := m)] at hm
    have hW_pos : (0 : ℝ) < (W.card : ℝ) - 1 := by
      linarith [show (2 : ℝ) ≤ W.card from by exact_mod_cast hW_card]
    rwa [ENNReal.ofReal_lt_ofReal_iff (div_pos hW_pos h32ε_pos)] at hm
  -- vendored: `haveI` becomes `have` (the pinned Mathlib's `haveI` style linter).
  have := hP_prob
  set μ := Measure.pi (fun _ : Fin m => P)
  refine ⟨P, hP_prob, hP_supp, ?_⟩
  suffices ∃ c ∈ C_set, ENNReal.ofReal (1 / 14) ≤
      ∫⁻ ω, μ {xs : Fin m → α |
        hypothesisError P ((A ω) (sampleOf c xs)) c > ε} ∂Q by
    obtain ⟨c, hc, hprob⟩ := this
    exact ⟨c, hc, lt_of_lt_of_le hδ_lt hprob⟩
  by_contra h_neg
  push Not at h_neg
  have hcMap : ∀ S ∈ W'.powerset, ∃ c ∈ C_set, c ∩ ↑W = {w₀} ∪ ↑S := by
    intro S hS
    refine hW _ (Set.union_subset (Set.singleton_subset_iff.mpr (mem_coe.mpr hw₀))
      ((coe_subset.mpr (Finset.mem_powerset.mp hS)).trans (coe_subset.mpr (erase_subset _ _))))
  choose cMap hcMap_mem hcMap_eq using hcMap
  set concepts : Finset α → Set α :=
    fun S => if h : S ∈ W'.powerset then cMap S h else ∅
  -- vendored: `dif_pos` is deprecated in the pinned core; `dite_eq_left`.
  have hconcepts_eq : ∀ S ∈ W'.powerset, concepts S ∩ ↑W = {w₀} ∪ ↑S := by
    intro S hS; simp only [concepts, dite_eq_left hS]; exact hcMap_eq S hS
  have hconcepts_mem : ∀ S ∈ W'.powerset, concepts S ∈ C_set := by
    intro S hS; simp only [concepts, dite_eq_left hS]; exact hcMap_mem S hS
  set B := {xs : Fin m → α | (seenElements W' xs).card ≤ d / 2}
  have hB_prob : ENNReal.ofReal (1 / 2) < μ B :=
    markov_bad_samples hw₀ hW_card hε'_pos hε'_le hm_real P hP_w
  have hlower_ω : ∀ ω : Ω, (2 ^ d / 2 : ℕ) • μ B ≤
      ∑ S ∈ W'.powerset, μ {xs : Fin m → α |
        hypothesisError P ((A ω) (sampleOf (concepts S) xs)) (concepts S) > ε} := by
    intro ω; simpa only [hε_eq] using
      ehkv_sum_lower_bound hW_card hw₀ hε'_pos (A ω) P hP_w hP_supp concepts hconcepts_eq
  have hintegrate : (2 ^ d / 2 : ℕ) • μ B ≤
      ∑ S ∈ W'.powerset, ∫⁻ ω, μ {xs : Fin m → α |
        hypothesisError P ((A ω) (sampleOf (concepts S) xs)) (concepts S) > ε} ∂Q := by
    calc (2 ^ d / 2 : ℕ) • μ B
        = ∫⁻ _ : Ω, ((2 ^ d / 2 : ℕ) • μ B : ℝ≥0∞) ∂Q := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ ω, ∑ S ∈ W'.powerset, μ {xs : Fin m → α |
            hypothesisError P ((A ω) (sampleOf (concepts S) xs)) (concepts S) > ε} ∂Q :=
          lintegral_mono (fun ω => hlower_ω ω)
      _ = ∑ S ∈ W'.powerset, ∫⁻ ω, μ {xs : Fin m → α |
            hypothesisError P ((A ω) (sampleOf (concepts S) xs)) (concepts S) > ε} ∂Q :=
          lintegral_finsetSum' _ (fun S hS => hA_aem P hP_supp (concepts S) (hconcepts_mem S hS))
  have hfail_bound : ∀ S ∈ W'.powerset,
      ∫⁻ ω, μ {xs : Fin m → α |
        hypothesisError P ((A ω) (sampleOf (concepts S) xs)) (concepts S) > ε} ∂Q <
      ENNReal.ofReal (1 / 14) :=
    fun S hS => h_neg (concepts S) (hconcepts_mem S hS)
  have hpow_nonempty : W'.powerset.Nonempty := ⟨∅, Finset.empty_mem_powerset _⟩
  have h_combined : (2 ^ d / 2 : ℕ) • μ B < (2 ^ d : ℕ) • ENNReal.ofReal (1 / 14) :=
    lt_of_le_of_lt hintegrate (by
      calc ∑ S ∈ W'.powerset, ∫⁻ ω, μ {xs : Fin m → α |
              hypothesisError P ((A ω) (sampleOf (concepts S) xs)) (concepts S) > ε} ∂Q
          < ∑ _S ∈ W'.powerset, ENNReal.ofReal (1 / 14) :=
            ENNReal.sum_lt_sum_of_nonempty hpow_nonempty hfail_bound
        _ = (2 ^ d : ℕ) • ENNReal.ofReal (1 / 14) := by rw [Finset.sum_const, card_powerset])
  exact ehkv_final_contradiction hd_pos hB_prob h_combined

end EHKVProof

end Cslib.MachineLearning.PACLearning
