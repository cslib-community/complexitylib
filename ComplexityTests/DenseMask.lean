/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Pseudoentropy.DenseMask
import Complexity.Crypto.Computational.Pseudoentropy.MaskedExtraction
import Complexity.Crypto.Computational.Pseudoentropy.Selection
import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource
import Complexity.Crypto.Computational.Pseudoentropy.WordExtraction
import Complexity.Tactic.PPT

/-! Uniform candidate selection, latent laws, label-dependent masks and complete public output. -/

namespace ComplexityTests.DenseMask

open Cslib Cslib.Probability Cslib.Probability.PMF Cslib.Crypto Cslib.Crypto.Pseudoentropy
  Cslib.BitString Turing.MultiTapeTM Filter

-- Both spellings retain the source input while validating and predicting.
example : IsPPTOn encBits encBool (fun word =>
    selectPredictor (word.length + 1) (word.length + 2) (pure (word, true))
      (fun i observation => pure (i < observation.length)) word) := by ppt

example : IsPPTOn (encList encBool) encBool (fun word => do
    let count := word.length + 1
    let trials := word.length + 2
    selectPredictor count trials (pure (word, true))
      (fun i observation => pure (i < observation.length)) word) := by ppt

-- An uncertified callback is still an obligation.
example (predict : ℕ → List Bool → ProbComp Bool)
    (hpredict : IsPPTOn (encPair encUnary encBits) encBool (fun pair => predict pair.1 pair.2)) :
    IsPPTOn encBits encBool (fun word =>
      selectPredictor 2 3 (pure (word, false)) predict word) := by
  fail_if_success (clear hpredict; ppt)
  ppt

private noncomputable def fairPair : SamplablePair where
  Observation _ := Unit
  finite _ := inferInstance
  encode _ := ⟨fun _ => [true, false], fun _ _ _ => Subsingleton.elim _ _⟩
  joint _ := (uniformOfFintype Bool).map ((), ·)
  sample _ := (fun bit => ([true, false], bit)) <$> ProbComp.uniform Bool
  efficient := by ppt
  eval_sample _ := by
    simp only [ProbComp.eval_map, ProbComp.eval_uniform, PMF.map_comp, Function.comp_def]
    rfl

private theorem fairPair_entropy (n : ℕ) : conditionalEntropy (fairPair.joint n) = 1 := by
  change conditionalEntropy ((uniformOfFintype Bool).map ((), ·)) = 1
  rw [conditionalEntropy, entropy_map_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
  rw [PMF.map_comp]
  change entropy (uniformOfFintype Bool) -
    entropy ((uniformOfFintype Bool).map (Function.const Bool ())) = 1
  rw [PMF.map_const]
  simp [entropy_uniform]

-- The latent decoder preserves the hidden bit and has conditional entropy one.
example (n : ℕ) :
    ProbComp.eval (fairPair.latentSample n) = (uniformOfFintype Bool).map ((), ·) ∧
      conditionalEntropy (ProbComp.eval (fairPair.latentSample n)) = 1 := by
  rw [fairPair.eval_latentSample n]
  exact ⟨rfl, fairPair_entropy n⟩

private theorem fairPair_gap : fairPair.HasGap (fun _ => 0) := by
  intro adversary _
  apply Eventually.of_forall
  intro n
  have hbit (guess : Bool) : (uniformOfFintype Bool).map (fun bit => guess == bit) =
      uniformOfFintype Bool := by
    ext bit
    cases guess <;> cases bit <;>
      norm_num [PMF.map_apply, tsum_fintype, Fintype.sum_bool, PMF.uniformOfFintype_apply]
  have hgame : ProbComp.eval (predictionGame fairPair.sample adversary n) =
      uniformOfFintype Bool := by
    simp only [predictionGame, fairPair, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_map, Function.comp_def]
    rw [PMF.bind_comm]
    change (ProbComp.eval (adversary n [true, false])).bind
      (fun guess => (uniformOfFintype Bool).map (fun bit => guess == bit)) = _
    simp only [hbit, PMF.bind_const]
  rw [hgame, fairPair_entropy]
  norm_num [PMF.uniformOfFintype_apply]

private noncomputable def saved : fairPair.SeedRealization :=
  Classical.choice fairPair.exists_seedRealization

-- The complete three-source theorem has a real client with positive label output. A zero-gap
-- pair supplies no expansion claim; the two other digest budgets are deliberately zero.
example :
    let count := fun n => ExtractionSchedule.count n (saved.length n) 0
    let bits := fun n => ExtractionSchedule.slack n (saved.length n) 0
    ComputationallyIndistinguishable
      (fun n => ProbComp.eval
        (ThreeSource.extract (count n) (saved.length n) 2 0 (bits n) 0 (saved.sampleWithSeed n)))
      (fun n => uniformList
        (ThreeSource.outputLength (count n) (saved.length n) 2 0 (bits n) 0)) := by
  have hlength := saved.length_isPolyTime
  apply fairPair_gap.extract_three saved
    (bound := fun _ => 2) (inverseSlack := fun _ => 0)
    (observationBits := fun _ => 0) (remainingBits := fun _ => 0)
    (labelBits := fun n => ExtractionSchedule.slack n (saved.length n) 0)
    (numerator := fun _ => 2) (densityBound := fun _ => 0)
    (by constructor <;> fun_prop)
    (by intro n observation _; exact Nat.le_refl 2)
    (Eventually.of_forall (by intro n; rw [fairPair_entropy]; norm_num [dyadicSize]))
    (Eventually.of_forall (by intro n; exact Or.inl rfl)) ?_
    (Eventually.of_forall (by intro n; exact Or.inl rfl))
  apply Eventually.of_forall
  intro n
  have h := ExtractionSchedule.two_slack_eq n (saved.length n) 0
  norm_num [dyadicSize] at h ⊢
  linarith [Nat.cast_nonneg (α := ℝ) (ExtractionSchedule.slack n (saved.length n) 0)]

-- A positive extraction budget on a real pair. Arbitrary bounded choices need no algorithm;
-- the test itself must be one uniform efficient family, with the full output available.
example (choose : ℕ → ℕ) (hchoose : ∀ n, choose n < n + 1)
    (test : ℕ → ℕ → List (List Bool) × List Bool × List Bool → ProbComp Bool)
    (htest : IsPPTOn (encPair (encPair encUnary encUnary)
      (encPair (encList encBits) (encPair encBits encBits))) encBool
        (fun input => test input.1.1 input.1.2 input.2)) :
    let count := fun n => ExtractionSchedule.count n (saved.length n) 0
    let bits := fun n => ExtractionSchedule.slack n (saved.length n) 0
    Negligible (fun n => Game.advantage
      (ProbComp.eval (OracleComp.replicate (count n) (fairPair.sample n) >>= fun values =>
        extractWordLabels (count n) (bits n) values >>= test n (choose n)))
      (ProbComp.eval (extractWordLabelsIdeal (Prod.fst <$> fairPair.sample n) (count n) (bits n)
        >>= test n (choose n)))) := by
  have hlength := saved.length_isPolyTime
  apply fairPair_gap.extract_indexed_word_labels saved choose
    (candidates := fun n => n + 1) (inverseSlack := fun _ => 0)
    (outputBits := fun n _ => ExtractionSchedule.slack n (saved.length n) 0)
    (numerator := fun _ _ => 2) (densityBound := fun _ => 0)
    (by fun_prop)
    (ExtractionSchedule.isPolyTime_slack (by fun_prop) (by fun_prop)
      (by fun_prop))
    (by fun_prop) (by fun_prop) (by fun_prop)
      (Eventually.of_forall hchoose)
    (Eventually.of_forall (by intro n; rw [fairPair_entropy]; norm_num [dyadicSize]))
    ?_ test htest
  apply Eventually.of_forall
  intro n
  have h := ExtractionSchedule.two_slack_eq n (saved.length n) 0
  norm_num [dyadicSize] at h ⊢
  linarith [Nat.cast_nonneg (α := ℝ) (ExtractionSchedule.slack n (saved.length n) 0)]

-- A real zero-gap pair has positive conditional entropy: valid positive-density requests are
-- nonvacuous. The eventual threshold is shared by all n+1 tests, not chosen once per index.
example : ∀ᶠ n in atTop, ∀ i < n + 1,
    ∃ mask : Unit × Bool → ProbComp Bool,
      (1 / 2 : ℝ) ≤ (ProbComp.eval (fairPair.latentSample n >>= mask) true).toReal ∧
      (Game.advantage
        (ProbComp.eval (OracleComp.replicate (n + 1) (fairPair.sample n) >>=
          fun values => pure ((values.headD ([], false)).2 ^^ decide (i < n))))
        (ProbComp.eval (OracleComp.replicate (n + 1)
          (maskedSample (fairPair.latentSample n)
            (fun value => fairPair.encode n value.1) Prod.snd mask) >>=
            fun values => pure ((values.headD ([], false)).2 ^^ decide (i < n)))) : ℝ) <
          (dyadicSize (n + 1) : ℝ) / (4 * (n + 1)) := by
  have h := fairPair_gap.eventually_exists_indexed_mask
    (fun n i values => pure ((values.headD ([], false)).2 ^^ decide (i < n))) (by fun_prop)
    (candidates := fun n => n + 1) (count := fun n => n + 1)
    (numerator := fun _ _ => 1) (densityBound := fun _ => 1)
    (inverseGap := fun n => 4 * (n + 1))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by lia)
  filter_upwards [h] with n hn
  intro i hi
  obtain ⟨mask, hdense, _, hclose⟩ := hn i hi (by decide) (by decide)
    (by rw [fairPair_entropy]; norm_num [dyadicSize])
  exact ⟨mask, by simpa [dyadicSize] using hdense,
    by simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hclose⟩

-- Masks may depend on the hidden label, and observations may identify distinct source draws.
example (pair : ℕ × Bool) (hpair : pair ∈ (ProbComp.eval
    (maskedSample (ProbComp.uniform Bool) (fun _ => 7) id (fun bit => pure bit))).support) :
    (1 / 8 : ℝ) ≤ (ProbComp.eval
      (maskedSample (ProbComp.uniform Bool) (fun _ => 7) id
        (fun bit => pure bit)) pair).toReal := by
  have h := maskedSample_dyadic_mass_ge (ProbComp.uniform Bool) (fun _ => 7) id
    (fun bit => pure bit) 1 1
    (by intro bit _; norm_num [ProbComp.eval_uniform, PMF.uniformOfFintype_apply])
    (by intro bit _; cases bit <;> norm_num [dyadicSize]) pair hpair
  norm_num [Real.rpow_neg, dyadicSize] at h ⊢
  exact h

-- The hash family is concrete and nonempty, and the test can use the entire infinite-typed
-- public observation list as well as the seed and the one-bit output.
private theorem oneBitHash : IsTwoUniversal (uniformOfFintype Bool)
    (fun key (bits : Fin 1 → Bool) => key ^^ (List.ofFn bits).headD false) := by
  intro x y hne
  have hxy : x 0 ≠ y 0 := by
    intro h
    apply hne
    funext i
    fin_cases i
    exact h
  simp [List.ofFn_succ, hxy]

example (test : List ℕ × Bool × Bool → PMF (Fin 3)) :
    dist ((ProbComp.eval (OracleComp.replicate 1
        (maskedSample (ProbComp.uniform Bool) (fun bit => if bit then 7 else 11) id
          (fun _ => pure true)) >>=
          extractLabels (ProbComp.uniform Bool)
            (fun key bits => key ^^ bits.headD false))).bind test)
      ((extractLabelsIdeal (Output := Bool)
        ((fun bit => if bit then 7 else 11) <$> ProbComp.uniform Bool) 1
        (ProbComp.uniform Bool)).bind test) ≤
      2 * Real.exp 0 + Real.sqrt 2 / 2 := by
  have hmass := maskedSample_dyadic_mass_ge (ProbComp.uniform Bool) id id
    (fun _ => pure true) 1 1
    (by intro bit _; norm_num [ProbComp.eval_uniform, PMF.uniformOfFintype_apply])
    (by intro _ _ _; norm_num [dyadicSize])
  have h := maskedSample_extract_dist_bind_le (ProbComp.uniform Bool)
    (fun bit => if bit then 7 else 11) id (fun _ => pure true) 1 3
    (by simpa using hmass) (ProbComp.uniform Bool) (fun key bits => key ^^ bits.headD false)
    (by simpa using oneBitHash) (δ := 1) (slack := 0) (by simp) (by norm_num) test
  norm_num at h ⊢
  exact h

-- Zero samples and zero source-information bits are valid, including a test that reads the
-- public seed together with the output. The totalized concentration bound is then three.
example :
    let source := maskedSample (pure ()) (fun _ => 7) (fun _ => false) (fun _ => pure false)
    let test := fun result : List ℕ × Bool × Bool => PMF.pure (result.2.1 == result.2.2)
    dist ((ProbComp.eval (OracleComp.replicate 0 source >>=
        extractLabels (ProbComp.uniform Bool) (fun key _ => key))).bind test)
      ((extractLabelsIdeal (Output := Bool) (pure 7) 0 (ProbComp.uniform Bool)).bind test) ≤ 3 := by
  dsimp only
  have h := maskedSample_extract_dist_bind_le (pure ()) (fun _ => 7) (fun _ => false)
    (fun _ => pure false) 0 0
    (by
      intro pair hpair
      have hp : pair = ((), false) := by simpa [maskedSample, maskBit] using hpair
      subst pair
      simp [maskedSample, maskBit])
    (ProbComp.uniform Bool) (fun key _ => key)
    (by intro x y hne; exact (hne (Subsingleton.elim _ _)).elim)
    (δ := 0) (slack := 0) (by simp) (by norm_num)
    (fun result : List ℕ × Bool × Bool => PMF.pure (result.2.1 == result.2.2))
  norm_num at h ⊢
  have hsqrt : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [hsqrt] at h
  exact h

end ComplexityTests.DenseMask
