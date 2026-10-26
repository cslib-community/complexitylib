/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource.Combined
import Complexity.Crypto.Computational.Pseudoentropy.Seed
import Complexity.Crypto.Computational.Pseudoentropy.WordSeedExtraction
import Complexity.Tactic.PPT

/-! Saved-seed contracts, unused randomness and supported-score concentration. -/

namespace ComplexityTests.PseudoentropySeed

open Cslib Cslib.Probability Cslib.Probability.PMF Cslib.Crypto.Pseudoentropy
open Turing.MultiTapeTM Filter

-- Arbitrary, possibly biased, independent bits: no uniformity assumption on the marginals.
example (count : ℕ) (p : Fin count → PMF Bool) {ε : ℝ} (hε : 0 ≤ ε) :
    ((pi p).toOuterMeasure {outcome |
      ε ≤ |(∑ i, if outcome i then (1 : ℝ) else 0) - ∑ i, (p i true).toReal|}).toReal ≤
      2 * Real.exp (-2 * ε ^ 2 / count) := by
  simpa [Fintype.sum_bool] using pi_sum_abs_sub_mean_ge p
    (fun _ bit => if bit then (1 : ℝ) else 0) (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ bit _ => by cases bit <;> simp) hε

-- Zero coordinates and a zero score bound remain legitimate inputs to the theorem.
example :
    ((pi (fun _ : Fin 0 => PMF.pure false)).toOuterMeasure {outcome |
      (∑ i, if outcome i then (100 : ℝ) else 0) ≤ 0}).toReal = 1 := by
  rw [(PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (by intro outcome _; simp)]
  rfl

-- The bound is required only on supported values; the impossible score can be 100.
example (count : ℕ) :
    ((pi (fun _ : Fin count => PMF.pure false)).toOuterMeasure {outcome |
      (∑ i, if outcome i then (100 : ℝ) else 0) ≤ 0}).toReal ≤ 1 := by
  simpa using pi_sum_le_mean_sub (fun _ : Fin count => PMF.pure false)
    (fun _ bit => if bit then (100 : ℝ) else 0) (bound := 0) (ε := 0) le_rfl
    (fun _ bit h => by simpa using h) le_rfl

private noncomputable def fairPair : SamplablePair where
  Observation _ := Unit
  finite _ := inferInstance
  encode _ := ⟨fun _ => [], fun _ _ _ => Subsingleton.elim _ _⟩
  joint _ := (uniformOfFintype Bool).map ((), ·)
  sample _ := (fun bit => ([], bit)) <$> ProbComp.uniform Bool
  efficient := by ppt
  eval_sample _ := by
    simp only [ProbComp.eval_map, ProbComp.eval_uniform, PMF.map_comp, Function.comp_def]
    rfl

-- The evaluator reads one bit and deliberately ignores all remaining seed bits.
private noncomputable def paddedSeed : fairPair.SeedRealization where
  length n := n + 1
  length_isPolyTime := by fun_prop
  evaluate _ bits := ([], bits.headD false)
  efficient := by fun_prop
  distribution n := by
    simp only [BitString.uniformList_succ, Function.comp_def, List.headD_cons, PMF.map,
      PMF.bind_const, fairPair, PMF.bind_bind, PMF.pure_bind]
    rfl

example : Nonempty fairPair.SeedRealization := fairPair.exists_seedRealization

-- The shared padding contract has a concrete saved sampler and a realizable common schedule.
example : ∃ common, EntropyGrid.PaddingBounds paddedSeed (fun _ => 0) (fun _ => 2) common := by
  obtain ⟨common, hcommon, _, _, hsize⟩ := EntropyGrid.exists_common_seedLength
    paddedSeed.length_isPolyTime
    (show ComputableInPolyTime (fun _ => 0) encUnary encUnary from by fun_prop)
    (show ComputableInPolyTime (fun _ => 2) encUnary encUnary from by fun_prop)
  exact ⟨common, ⟨by fun_prop, by fun_prop, hcommon, fun _ _ _ => Nat.le_refl 0, hsize⟩⟩

-- The evaluator is total on malformed seeds too; here an empty seed returns the default bit.
example : paddedSeed.evaluate 7 [] = ([], false) := rfl

-- The complete seed/output experiment is efficient under its ordinary pair encoding.
example : IsPPTOn encUnary (encPair (encPair encBits encBool) encBits)
    paddedSeed.sampleWithSeed := by ppt

-- Captured input and an alternative input encoding compose through the same certificate.
example : IsPPTOn (encPair encBool encUnary) (encPair (encPair encBits encBool) encBits)
    (fun input : Bool × ℕ => paddedSeed.sampleWithSeed input.2) := by ppt

-- An explicit bind spells the same sampler without a specialized tactic syntax rule.
example : IsPPTOn encUnary (encPair (encPair encBits encBool) encBits)
    (fun n => BitString.sampleList (n + 1) >>= fun bits =>
      pure (([], bits.headD false), bits)) := by
  ppt

example (n : ℕ) : ProbComp.eval (paddedSeed.sampleWithSeed n) =
    (paddedSeed.jointWithSeed n).map (fun result => (([], result.1.2), List.ofFn result.2)) :=
  paddedSeed.eval_sampleWithSeed n

-- Exactly n unused random bits remain after disclosing the hidden bit and the constant observation.
private theorem residual_entropy (n : ℕ) : conditionalEntropy (paddedSeed.jointWithSeed n) = n := by
  have h := paddedSeed.entropy_chain_rule n
  change entropy (((uniformOfFintype Bool).map ((), ·)).map Prod.fst) +
    conditionalEntropy ((uniformOfFintype Bool).map ((), ·)) +
    conditionalEntropy (paddedSeed.jointWithSeed n) = ((n + 1 : ℕ) : ℝ) at h
  rw [conditionalEntropy_map_const, entropy_uniform] at h
  norm_num [PMF.map_comp, Function.comp_def, PMF.map, PMF.bind_const] at h
  linarith

-- The joint law retains every unused coin, not just the marginal observation and label.
example (n : ℕ) : ProbComp.eval (paddedSeed.sampleWithSeed n) =
    (BitString.uniformList (n + 1)).map (fun bits => (([], bits.headD false), bits)) := by
  simp only [SamplablePair.SeedRealization.sampleWithSeed, paddedSeed, bind_pure_comp,
    ProbComp.eval_map, BitString.eval_sampleList]

private theorem slack_budget (n width : ℕ) :
    (ExtractionSchedule.slack n width 0 : ℝ) + 2 * ExtractionSchedule.slack n width 0 ≤
      ExtractionSchedule.count n width 0 := by
  have h := ExtractionSchedule.two_slack_eq n width 0
  norm_num at h
  linarith [Nat.cast_nonneg (α := ℝ) (ExtractionSchedule.slack n width 0)]

-- Extract positively many bits from the unused coins, against every randomized full-output test.
example :
    let count := fun n => ExtractionSchedule.count n (n + 1) 0
    let bits := fun n => ExtractionSchedule.slack n (n + 1) 0
    Cslib.Crypto.Game.Indistinguishable
      (fun (test : ℕ → List (List Bool × Bool) × List Bool × List Bool → Cslib.Crypto.Game) n =>
        (ProbComp.eval (OracleComp.replicate (count n) (paddedSeed.sampleWithSeed n) >>=
          extractWordSeeds (count n) (n + 1) (bits n))).bind (test n))
      (fun test n => (ProbComp.eval (extractMatrixLabelsIdeal (fairPair.sample n) (count n)
        (count n * (n + 1)) (bits n))).bind (test n)) (fun _ => True) := by
  apply paddedSeed.extract_word_seeds (fun _ => 0)
    (fun n => ExtractionSchedule.slack n (n + 1) 0)
  filter_upwards [eventually_ge_atTop 1] with n hn
  right
  have hresidual : (paddedSeed.length n : ℝ) - entropy ((fairPair.joint n).map Prod.fst) -
      conditionalEntropy (fairPair.joint n) = n := by
    linarith [paddedSeed.entropy_chain_rule n, residual_entropy n]
  rw [hresidual]
  exact (slack_budget n (n + 1)).trans
    (le_mul_of_one_le_right (by positivity) (by exact_mod_cast hn))

-- The observation has one fair bit, and the hidden label is constant.
private noncomputable def observedPair : SamplablePair where
  Observation _ := Bool
  finite _ := inferInstance
  encode _ := encBool
  joint _ := (uniformOfFintype Bool).map (fun bit => (bit, false))
  sample _ := (fun bit => ([bit], false)) <$> ProbComp.uniform Bool
  efficient := by ppt
  eval_sample _ := by
    simp only [ProbComp.eval_map, ProbComp.eval_uniform, PMF.map_comp, Function.comp_def]
    rfl

private noncomputable def observedSeed : observedPair.SeedRealization where
  length _ := 1
  length_isPolyTime := by fun_prop
  evaluate _ bits := ([bits.headD false], false)
  efficient := by fun_prop
  distribution _ := by
    simp only [BitString.uniformList_succ, Function.comp_def, List.headD_cons, PMF.map,
      PMF.bind_const, observedPair, PMF.bind_bind, PMF.pure_bind]
    rfl

-- Padding carries a genuine supported length bound; extraction includes the entire hash seed.
example :
    let count := fun n => ExtractionSchedule.count n 1 0
    let bits := fun n => ExtractionSchedule.slack n 1 0
    Cslib.Crypto.Game.Indistinguishable
      (fun (test : ℕ → List Bool → Cslib.Crypto.Game) n =>
        (ProbComp.eval (OracleComp.replicate (count n) (Prod.fst <$> observedPair.sample n) >>=
          extractWordObservations 1 (bits n))).bind (test n))
      (fun test n => (BitString.uniformList (bits n * (count n * 3) + bits n)).bind (test n))
      (fun _ => True) := by
  apply observedSeed.extract_word_observations (fun _ => 1) (fun _ => 0)
    (fun n => ExtractionSchedule.slack n 1 0) (by
      intro n observation _
      change [observation].length ≤ 1
      simp)
  apply Eventually.of_forall
  intro n
  right
  have hentropy : entropy ((observedPair.joint n).map Prod.fst) = 1 := by
    simp only [observedPair, PMF.map_comp, Function.comp_def]
    change entropy ((uniformOfFintype Bool).map id) = 1
    rw [PMF.map_id]
    norm_num [entropy_uniform]
  rw [hentropy, mul_one]
  exact slack_budget n 1

-- The full amplified grid has a concrete seed realization, including unused seed bits.
example : ComputableInPolyTime
    (fun p : (ℕ × ℕ) × List Bool => EntropyGrid.amplifiedGenerate p.1.1 (p.1.1 + 1)
      0 2 (p.1.1 + 4) p.1.2 (fun bits => ([], bits.headD false)) p.2)
    (encPair (encPair encUnary encUnary) encBits) encBits :=
  (EntropyGrid.isPolyTime_amplifiedGenerate paddedSeed
    (observationBound := fun _ => 0) (densityBound := fun _ => 2) (common := fun n => n + 4)
    (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)))

example : ComputableInPolyTime
    (fun p : ℕ × List Bool => EntropyGrid.combinedGenerate p.1 (p.1 + 1)
      0 2 (p.1 + 4) (fun bits => ([], bits.headD false)) p.2)
    (encPair encUnary encBits) encBits :=
  (EntropyGrid.isPolyTime_combinedGenerate paddedSeed
    (observationBound := fun _ => 0) (densityBound := fun _ => 2) (common := fun n => n + 4)
    (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)))

-- Output width is fixed even for malformed seeds; security uses the declared uniform seed law.
example (n : ℕ) (seed : List Bool) :
    (EntropyGrid.combinedGenerate n (n + 1) 0 2 (n + 4)
      (fun bits => ([], bits.headD false)) seed).length =
      EntropyGrid.size (n + 1) 2 * (n + 4) + 1 :=
  EntropyGrid.length_combinedGenerate ..

end ComplexityTests.PseudoentropySeed
