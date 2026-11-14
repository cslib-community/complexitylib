/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticDomination.SequentialUpper
import CslibFrontier.Probability.PMF.Event
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Tactic

/-!
# Reached-prefix comparison with unbounded response metadata

Every actual response has an authenticated tag and an independent fair success
bit. On impossible unauthenticated prefixes the comparison event is empty, so
the old all-prefix lower hypothesis is false; its complement similarly violates
the all-prefix upper hypothesis. Geometric metadata has unbounded support;
no finite response alphabet is installed for this process.
-/

noncomputable section
namespace CslibFrontierTests.SequentialSupport
open Cslib.Probability MeasureTheory
open scoped ENNReal unitInterval

private structure Response where
  /-- Unbounded raw response metadata. -/
  metadata : ℕ
  /-- The actual source always authenticates this tag. -/
  authenticated : Bool
  /-- The progress bit is a fresh fair coin. -/
  success : Bool

private def half : I := ⟨1 / 2, by norm_num⟩
private def metadata : PMF ℕ := (ProbabilityTheory.geometricMeasure half).toPMF
private def step (t : ℕ) (_ : Fin t → Response) : PMF Response :=
  metadata.bind fun m => (PMF.uniformOfFintype Bool).map fun b => ⟨m, true, b⟩
private def event (t : ℕ) (h : Fin t → Response) : Set Response :=
  if ∀ i, (h i).authenticated = true then {x | x.success = true} else ∅

private theorem metadata_pos (n : ℕ) : 0 < metadata n := by
  rw [metadata, Measure.toPMF_apply, ProbabilityTheory.geometricMeasure_singleton
    (by intro h; have he := congrArg (fun p : I => (p : ℝ)) h; norm_num [half] at he)]
  apply ENNReal.ofReal_pos.mpr
  simp only [half, Subtype.coe_mk]
  positivity

-- Unboundedness concerns actual positive-probability responses, not just their type.
example (N : ℕ) : ∃ x ∈ (step 0 Fin.elim0).support, N < x.metadata := by
  refine ⟨⟨N + 1, true, true⟩, ?_, Nat.lt_succ_self N⟩
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨N + 1, ?_, ?_⟩
  · exact ne_of_gt (metadata_pos _)
  · exact (PMF.mem_support_map_iff _ _ _).mpr ⟨true, by simp, rfl⟩

private theorem authenticated (t : ℕ) (h : Fin t → Response)
    (hh : h ∈ (PMF.seqProcess step t).support) : ∀ i, (h i).authenticated = true := by
  induction t with
  | zero => intro i; exact Fin.elim0 i
  | succ t ih =>
    simp only [PMF.seqProcess, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hh
    obtain ⟨g, hg, x, hx, rfl⟩ := hh
    simp only [step, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hx
    obtain ⟨m, _, b, _, rfl⟩ := hx
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa only [Fin.snoc_castSucc] using ih g hg j

private theorem probability (t : ℕ) (h : Fin t → Response)
    (hh : h ∈ (PMF.seqProcess step t).support) :
    (step t h).toOuterMeasure (event t h) = 1 / 2 := by
  have he : event t h = {x | x.success = true} := by
    simp [event, authenticated t h hh]
  rw [he, step, PMF.toOuterMeasure_bind_apply]
  have hm (m : ℕ) :
      ((PMF.uniformOfFintype Bool).map fun b => (⟨m, true, b⟩ : Response)).toOuterMeasure
        {x | x.success = true} = 1 / 2 := by
    rw [PMF.toOuterMeasure_map_apply]
    change (PMF.uniformOfFintype Bool).toOuterMeasure {true} = 1 / 2
    rw [PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
    norm_num
  simp_rw [hm]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

-- This positive-probability process satisfies the new reached-prefix hypothesis.
example : PMF.StochasticallyDominates
    ((PMF.seqProcess step 3).map (PMF.seqCount event 3))
    (PMF.poissonBinomial [half, half, half]) := by
  apply PMF.seqCount_stochasticallyDominates_poissonBinomial_of_support
  intro t ht h hh
  rw [probability t h hh]
  have ht' : t < 3 := ht
  interval_cases t <;> norm_num [half]

example :
    (((PMF.seqProcess step 3).map (PMF.seqCount event 3)).toOuterMeasure (Set.Iio 1)).toReal ≤
      (ProbabilityTheory.binomial 3 half).real (Set.Iio 1) := by
  apply PMF.seqCount_active_toReal_Iio_le_of_support
  intro t ht h hh _
  rw [probability t h hh]
  norm_num [half]

private def bad : Fin 1 → Response := fun _ => ⟨0, false, false⟩
private theorem bad_event : event 1 bad = ∅ := by
  have hb : ¬ ∀ i : Fin 1, (bad i).authenticated = true := by
    intro h
    have he := h 0
    cases he
  simp [event, hb]

-- An unsupported prefix makes the all-prefix probability premise false; it cannot
-- be discharged by the original theorem even though the actual process is sound.
example : ¬ ((half : ℝ) ≤ ((step 1 bad).toOuterMeasure (event 1 bad)).toReal) := by
  rw [bad_event]
  norm_num [half]

example : bad ∉ (PMF.seqProcess step 1).support := by
  intro h
  have he := authenticated 1 bad h 0
  cases he

-- Complementing the event gives an upper-envelope client: the impossible
-- unauthenticated prefix now has probability one, contradicting the old premise.
private theorem complement_probability (t : ℕ) (h : Fin t → Response)
    (hh : h ∈ (PMF.seqProcess step t).support) :
    ((step t h).toOuterMeasure (event t h)ᶜ).toReal = 1 / 2 := by
  have ha := PMF.toOuterMeasure_toReal_add_compl (step t h) (event t h)
  rw [probability t h hh] at ha
  norm_num at ha ⊢
  linarith

example : PMF.StochasticallyDominates (PMF.poissonBinomial (List.replicate 3 half))
    ((PMF.seqProcess step 3).map (PMF.seqCount (fun t h => (event t h)ᶜ) 3)) := by
  apply PMF.poissonBinomial_replicate_stochasticallyDominates_seqCount_of_support
  intro t _ h hh
  rw [complement_probability t h hh]
  norm_num [half]

example :
    (((PMF.seqProcess step 3).map (PMF.seqCount (fun t h => (event t h)ᶜ) 3)).toOuterMeasure
      (Set.Ici 2)).toReal ≤ (ProbabilityTheory.binomial 3 half).real (Set.Ici 2) := by
  apply PMF.seqCount_toReal_Ici_le_of_support
  intro t _ h hh
  rw [complement_probability t h hh]
  norm_num [half]

example : ¬ (((step 1 bad).toOuterMeasure (event 1 bad)ᶜ).toReal ≤ (half : ℝ)) := by
  rw [bad_event, Set.compl_empty,
    (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)]
  norm_num [half]

-- An unattainable threshold has probability zero even with unbounded responses.
example : ((PMF.seqProcess step 3).map
    (PMF.seqCount (fun t h => (event t h)ᶜ) 3)).toOuterMeasure (Set.Ici 4) = 0 := by
  rw [PMF.toOuterMeasure_map_apply]
  have he : (PMF.seqCount (fun t h => (event t h)ᶜ) 3) ⁻¹' Set.Ici 4 = ∅ := by
    ext h
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
    have := PMF.seqCount_le (fun t h => (event t h)ᶜ) 3 h
    omega
  rw [he, measure_empty]

end CslibFrontierTests.SequentialSupport
