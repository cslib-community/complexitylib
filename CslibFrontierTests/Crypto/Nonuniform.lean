/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Nonuniform.ZeroKnowledge
import CslibFrontier.Crypto.Computational.ZeroKnowledge.AuxClock
import CslibFrontier.Crypto.Computational.GeneratorXor
import CslibFrontier.Crypto.Computational.Stretch
import CslibFrontier.Crypto.Computational.Pseudoentropy.OneWay
import CslibFrontier.Crypto.Computational.Pseudoentropy.LabelExtraction
import CslibFrontier.Crypto.Computational.Pseudoentropy.ThreeSource.Padding
import CslibFrontier.Languages.Probabilistic.Notation
import CslibFrontier.Tactic.PPT

/-! Checked clients of the nonuniform security notions. Existence of a nonuniform one-way
function or generator is open, so these checks show that the notions are not trivially true
(constant functions, fixed words and length-wise constant generators fail them) and that the
indistinguishability notion is not trivially false. They do not separate the nonuniform notions
from the uniform ones. -/

namespace CslibFrontierTests.Crypto.Nonuniform

open Cslib Cslib.Crypto Probability

/-- A constant function is not nonuniformly one-way, because it is not even uniformly one-way. -/
example (word : List Bool) : ¬ NonuniformOneWay (fun _ => word) :=
  fun h => not_oneWay_const word h.toOneWay

/-- Inverting a constant function is not hard even with empty advice: by
`oneWay_iff_inversionHardWithAdvice_nil` that would make it uniformly one-way. -/
example (word : List Bool) : ¬ InversionHardWithAdvice (fun _ => word) (fun _ => []) :=
  fun h => not_oneWay_const word (oneWay_iff_inversionHardWithAdvice_nil.mpr
    ⟨Turing.MultiTapeTM.ComputableInPolyTime.const word, h⟩)

/-- The nonuniform indistinguishability relation holds between equal ensembles. -/
example : NonuniformlyIndistinguishable (fun n => BitString.uniformList n)
    (fun n => BitString.uniformList n) :=
  NonuniformlyIndistinguishable.refl _

/-- The all-`true` words are distinguishable from uniform words of each positive length. -/
example : ¬ NonuniformlyIndistinguishable (fun n => PMF.pure (List.replicate n true))
    (fun n => BitString.uniformList n) :=
  not_nonuniformlyIndistinguishable_pure_uniformList _ (Filter.eventually_ge_atTop 1)

/-- A generator that, at each seed length, outputs one fixed word of the right length is not a
nonuniform PRG (nor a uniform one): its output's first bit is constant. -/
example : ¬ NonuniformPRG (fun seed => List.replicate (seed.length + 1) false) (· + 1) := by
  intro h
  refine not_nonuniformlyIndistinguishable_pure_uniformList (fun n => List.replicate (n + 1) false)
    (.of_forall fun n => Nat.le_add_left 1 n) ?_
  have hensemble :
      generatorEnsemble (fun seed => List.replicate (seed.length + 1) false) =
        fun n => PMF.pure (List.replicate (n + 1) false) := by
    funext n
    rw [generatorEnsemble_postprocess (fun _ => []) (fun n _ => List.replicate (n + 1) false)]
    simp only [generatorEnsemble, PMF.map_comp]
    exact PMF.map_const _ _
  have hsecure := h.secure
  rw [hensemble] at hsecure
  exact hsecure

/-- The nonuniform generator premise gives the GMW advice premise for CNF instances. -/
example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : NonuniformPRG generator length) :
    GMW.AdvicePRG Complexity.encCNF generator length :=
  h.advicePRG _

/-- With empty advice, indistinguishability with advice is uniform indistinguishability, so the
uniform first-bit separation transfers. -/
example : ¬ IndistinguishableWithAdvice (fun _ => []) (fun n => PMF.pure (List.replicate n true))
    (fun n => BitString.uniformList n) := fun h =>
  not_computationallyIndistinguishable_pure_uniformList _ (Filter.eventually_ge_atTop 1)
    (computationallyIndistinguishable_iff_indistinguishableWithAdvice_nil.mpr h)

/-- A nonuniform one-bit PRG feeds the auxiliary-input GMW theorem directly; the theorem stretches
it to the GMW length `3 * n + 1` itself. -/
example {generator : List Bool → List Bool} (h : NonuniformPRG generator (fun n => n + 1))
    {α : Type} {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ Complexity.NP enc) :
    ∃ zk : ZeroKnowledgeProof enc A, zk.AuxiliaryInputZeroKnowledge :=
  h.exists_auxiliaryInputZeroKnowledge_of_mem_NP hA

private noncomputable def fairPair : Pseudoentropy.SamplablePair where
  Observation _ := Unit
  finite _ := inferInstance
  encode _ := ⟨fun _ => [true, false], fun _ _ _ => Subsingleton.elim _ _⟩
  joint _ := (PMF.uniformOfFintype Bool).map ((), ·)
  sample _ := (fun bit => ([true, false], bit)) <$> ProbComp.uniform Bool
  efficient := by ppt
  eval_sample _ := by
    simp only [ProbComp.eval_map, ProbComp.eval_uniform, PMF.map_comp, Function.comp_def]
    rfl

private theorem fairPair_entropy (n : ℕ) :
    PMF.conditionalEntropy (fairPair.joint n) = 1 := by
  change PMF.conditionalEntropy ((PMF.uniformOfFintype Bool).map ((), ·)) = 1
  rw [PMF.conditionalEntropy, PMF.entropy_map_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
  rw [PMF.map_comp]
  change PMF.entropy (PMF.uniformOfFintype Bool) -
    PMF.entropy ((PMF.uniformOfFintype Bool).map (Function.const Bool ())) = 1
  rw [PMF.map_const]
  simp [PMF.entropy_uniform]

/-- An independent fair hidden bit has zero prediction gap against predictors receiving any
fixed advice family. -/
private theorem fairPair_gapWithAdvice (advice : ℕ → List Bool) :
    fairPair.HasGapWithAdvice (fun _ => 0) advice := by
  intro adversary _
  apply Filter.Eventually.of_forall
  intro n
  have hbit (guess : Bool) : (PMF.uniformOfFintype Bool).map (fun bit => guess == bit) =
      PMF.uniformOfFintype Bool := by
    ext bit
    cases guess <;> cases bit <;>
      norm_num [PMF.map_apply, tsum_fintype, Fintype.sum_bool, PMF.uniformOfFintype_apply]
  have hgame : ProbComp.eval
      (Pseudoentropy.predictionGame fairPair.sample
        (fun n word => adversary ((n, advice n), word)) n) =
      PMF.uniformOfFintype Bool := by
    simp only [Pseudoentropy.predictionGame, fairPair, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_map, Function.comp_def]
    rw [PMF.bind_comm]
    change (ProbComp.eval (adversary ((n, advice n), [true, false]))).bind
      (fun guess => (PMF.uniformOfFintype Bool).map (fun bit => guess == bit)) = _
    simp only [hbit, PMF.bind_const]
  rw [hgame, fairPair_entropy]
  norm_num [PMF.uniformOfFintype_apply]

private def nonemptyAdvice (n : ℕ) : List Bool :=
  true :: List.replicate n false

private def advisedMaskTest (a : ℕ × List Bool)
    (values : List (List Bool × Bool)) : ProbComp Bool :=
  pure (a.2.headD false && (values.headD ([], false)).2)

/-- The concrete advised test genuinely depends on the nonempty advice word: running it with
`nonemptyAdvice n` succeeds with probability `1`, whereas running it with empty advice succeeds with
probability `0`. -/
example (n : ℕ) :
    Pr[advisedMaskTest (n, nonemptyAdvice n) [([true, false], true)]] = 1 ∧
      Pr[advisedMaskTest (n, []) [([true, false], true)]] = 0 := by
  simp [advisedMaskTest, nonemptyAdvice]

/-- An advice-dependent predictor on `fairPair` with nonempty advice has prediction error at least
`1 / 2` via `HasGapWithAdvice.eventually_error_ge`. -/
example :
    ∀ᶠ n in Filter.atTop, (1 / 2 : ℝ) ≤
      (ProbComp.eval
        (Pseudoentropy.predictionGame fairPair.sample
          (fun n _ => pure ((nonemptyAdvice n).headD false)) n) false).toReal := by
  have h := (fairPair_gapWithAdvice nonemptyAdvice).eventually_error_ge
    (fun input => pure (input.1.2.headD false)) (by fun_prop)
  filter_upwards [h] with n hn
  simpa [fairPair_entropy] using hn

/-- Concrete exercised client of `HasGapWithAdvice.eventually_exists_mask` on `fairPair` with
nonempty advice `nonemptyAdvice`, an advice-dependent test `advisedMaskTest`, discharged density
premises (`1 / 2 ≤ 1`), and a nontrivial advantage bound `1 / 2 < 1` (`count = 1`,
`inverseGap = 4`). -/
example :
    ∀ᶠ n in Filter.atTop,
      ∃ mask : Unit × Bool → ProbComp Bool,
        (1 / 2 : ℝ) ≤ Pr[fairPair.latentSample n >>= mask] ∧
        (Game.advantage
          (ProbComp.eval
            (OracleComp.replicate 1 (fairPair.sample n) >>=
              advisedMaskTest (n, nonemptyAdvice n)))
          (ProbComp.eval
            (OracleComp.replicate 1
              (Pseudoentropy.maskedSample (fairPair.latentSample n)
                (fun value => fairPair.encode n value.1) Prod.snd mask) >>=
              advisedMaskTest (n, nonemptyAdvice n))) : ℝ) < 1 / 2 := by
  have h := (fairPair_gapWithAdvice nonemptyAdvice).eventually_exists_mask
    advisedMaskTest (by unfold advisedMaskTest; fun_prop)
    (count := fun _ => 1) (numerator := fun _ => 1) (densityBound := fun _ => 1)
    (inverseGap := fun _ => 4)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (fun _ => by decide)
  have hbound : (dyadicSize 1 : ℝ) / (4 : ℕ) = 1 / 2 := by norm_num [dyadicSize]
  filter_upwards [h] with n hn
  obtain ⟨mask, hdense, _, hclose⟩ := hn (by decide) (by decide)
    (by rw [fairPair_entropy]; norm_num [dyadicSize])
  refine ⟨mask, by simpa [dyadicSize] using hdense, ?_⟩
  rwa [hbound] at hclose

private noncomputable def saved : fairPair.SeedRealization :=
  Classical.choice fairPair.exists_seedRealization

private def advisedWordDistinguisher
    (input : (ℕ × List Bool) × List Bool) : ProbComp Bool :=
  pure (input.1.2.headD false && input.2.headD false)

/-- The concrete word distinguisher depends on the nonempty advice word: it accepts `[true]` under
`nonemptyAdvice n` with probability `1` and under empty advice with probability `0`. -/
example (n : ℕ) :
    Pr[advisedWordDistinguisher ((n, nonemptyAdvice n), [true])] = 1 ∧
      Pr[advisedWordDistinguisher ((n, []), [true])] = 0 := by
  simp [advisedWordDistinguisher, nonemptyAdvice]

/-- Concrete exercised client of `HasGapWithAdvice.extract_three` on `fairPair` with nonempty
advice `nonemptyAdvice`, positive extracted label output
`ExtractionSchedule.slack n (saved.length n) 0`, and the advice-dependent distinguisher
`advisedWordDistinguisher`. -/
example :
    let count := fun n => Pseudoentropy.ExtractionSchedule.count n (saved.length n) 0
    let bits := fun n => Pseudoentropy.ExtractionSchedule.slack n (saved.length n) 0
    Negligible (fun n => Game.advantage
      (distinguishingGame
        (ProbComp.eval
          (Pseudoentropy.ThreeSource.extract (count n) (saved.length n) 2 0 (bits n) 0
            (saved.sampleWithSeed n)))
        (fun word => advisedWordDistinguisher ((n, nonemptyAdvice n), word)))
      (distinguishingGame
        (BitString.uniformList
          (Pseudoentropy.ThreeSource.outputLength (count n) (saved.length n) 2 0 (bits n) 0))
        (fun word => advisedWordDistinguisher ((n, nonemptyAdvice n), word)))) := by
  have hlength := saved.length_isPolyTime
  have hind : IndistinguishableWithAdvice nonemptyAdvice
      (fun n => ProbComp.eval
        (Pseudoentropy.ThreeSource.extract
          (Pseudoentropy.ExtractionSchedule.count n (saved.length n) 0)
          (saved.length n) 2 0
          (Pseudoentropy.ExtractionSchedule.slack n (saved.length n) 0) 0
          (saved.sampleWithSeed n)))
      (fun n => BitString.uniformList
        (Pseudoentropy.ThreeSource.outputLength
          (Pseudoentropy.ExtractionSchedule.count n (saved.length n) 0)
          (saved.length n) 2 0
          (Pseudoentropy.ExtractionSchedule.slack n (saved.length n) 0) 0)) := by
    apply (fairPair_gapWithAdvice nonemptyAdvice).extract_three saved
      (bound := fun _ => 2) (inverseSlack := fun _ => 0)
      (observationBits := fun _ => 0) (remainingBits := fun _ => 0)
      (labelBits := fun n => Pseudoentropy.ExtractionSchedule.slack n (saved.length n) 0)
      (numerator := fun _ => 2) (densityBound := fun _ => 0)
      (by constructor <;> fun_prop)
      (by intro n observation _; exact Nat.le_refl 2)
      (Filter.Eventually.of_forall (by intro n; rw [fairPair_entropy]; norm_num [dyadicSize]))
      (Filter.Eventually.of_forall (by intro n; exact Or.inl rfl)) ?_
      (Filter.Eventually.of_forall (by intro n; exact Or.inl rfl))
    apply Filter.Eventually.of_forall
    intro n
    have h := Pseudoentropy.ExtractionSchedule.two_slack_eq n (saved.length n) 0
    norm_num [dyadicSize] at h ⊢
    linarith [Nat.cast_nonneg (α := ℝ)
      (Pseudoentropy.ExtractionSchedule.slack n (saved.length n) 0)]
  exact hind advisedWordDistinguisher (by unfold advisedWordDistinguisher; fun_prop)

/-- Concrete exercised client of `HasGapWithAdvice.extract_indexed_word_labels` on `fairPair` with
nonempty advice `nonemptyAdvice` and an advice-dependent indexed test. -/
example (choose : ℕ → ℕ) (hchoose : ∀ n, choose n < n + 1) :
    let count := fun n => Pseudoentropy.ExtractionSchedule.count n (saved.length n) 0
    let bits := fun n => Pseudoentropy.ExtractionSchedule.slack n (saved.length n) 0
    let test : ℕ × List Bool → ℕ → List (List Bool) × List Bool × List Bool → ProbComp Bool :=
      fun a i result => pure (a.2.headD false && (result.2.2.headD false ^^ decide (i < a.1)))
    Negligible (fun n => Game.advantage
      (ProbComp.eval do
        let values ← OracleComp.replicate (count n) (fairPair.sample n)
        let labels ← Pseudoentropy.extractWordLabels (count n) (bits n) values
        test (n, nonemptyAdvice n) (choose n) labels)
      (ProbComp.eval
        (Pseudoentropy.extractWordLabelsIdeal
          (Prod.fst <$> fairPair.sample n) (count n) (bits n) >>=
          test (n, nonemptyAdvice n) (choose n)))) := by
  have hlength := saved.length_isPolyTime
  apply (fairPair_gapWithAdvice nonemptyAdvice).extract_indexed_word_labels saved choose
    (candidates := fun n => n + 1) (inverseSlack := fun _ => 0)
    (outputBits := fun n _ => Pseudoentropy.ExtractionSchedule.slack n (saved.length n) 0)
    (numerator := fun _ _ => 2) (densityBound := fun _ => 0)
    (by fun_prop)
    (Pseudoentropy.ExtractionSchedule.isPolyTime_slack (by fun_prop) (by fun_prop) (by fun_prop))
    (by fun_prop) (by fun_prop) (by fun_prop)
    (Filter.Eventually.of_forall hchoose)
    (Filter.Eventually.of_forall (by intro n; rw [fairPair_entropy]; norm_num [dyadicSize]))
    ?_
    (fun a i result => pure (a.2.headD false && (result.2.2.headD false ^^ decide (i < a.1))))
    (by fun_prop)
  apply Filter.Eventually.of_forall
  intro n
  have h := Pseudoentropy.ExtractionSchedule.two_slack_eq n (saved.length n) 0
  norm_num [dyadicSize] at h ⊢
  linarith [Nat.cast_nonneg (α := ℝ) (Pseudoentropy.ExtractionSchedule.slack n (saved.length n) 0)]

/-- Conditional client of `EntropyGrid.exists_secure_padded_choice_withAdvice` assuming a
nonuniform one-way function `hf : NonuniformOneWay f` (which supplies a pseudoentropy pair with
positive gap `1 / (2 * (n + 7))` discharging `4 / dyadicSize (16 * (n + 7)) ≤ gap n`, whereas the
unconditional `fairPair` fixture has gap `0`), tested with nonempty advice `nonemptyAdvice` and
`advisedWordDistinguisher`. -/
example {f : List Bool → List Bool} (hf : NonuniformOneWay f) :
    ∃ (pair : Pseudoentropy.SamplablePair) (savedPair : pair.SeedRealization)
      (bound common choose : ℕ → ℕ),
      (∀ᶠ n in Filter.atTop,
        choose n < Pseudoentropy.EntropyGrid.size (savedPair.length n) (16 * (n + 7))) ∧
      Negligible (fun n => Game.advantage
        (((BitString.uniformList (common n)).map
          (Pseudoentropy.EntropyGrid.paddedGenerate n (savedPair.length n) (bound n)
            (16 * (n + 7)) (common n) (choose n) (savedPair.evaluate n))).bind
          (fun word => ProbComp.eval
            (advisedWordDistinguisher ((n, nonemptyAdvice n), word))))
        ((BitString.uniformList (common n + 1)).bind
          (fun word => ProbComp.eval
            (advisedWordDistinguisher ((n, nonemptyAdvice n), word))))) := by
  obtain ⟨pair, hpair⟩ := hf.exists_pseudoentropyPair
  obtain ⟨savedPair⟩ := pair.exists_seedRealization
  obtain ⟨bound, hbound, hfits⟩ := pair.exists_observationBound
  have hdensity : Turing.MultiTapeTM.ComputableInPolyTime
      (fun n => 16 * (n + 7)) Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary := by
    fun_prop
  obtain ⟨common, hcommon, _, _, hsize⟩ :=
    Pseudoentropy.EntropyGrid.exists_common_seedLength
      savedPair.length_isPolyTime hbound hdensity
  have hadvice : PolynomiallyBounded (fun n => (nonemptyAdvice n).length) := by
    simpa [nonemptyAdvice, Nat.add_comm] using PolynomiallyBounded.id.add (.const 1)
  obtain ⟨choose, hchoose, hsecure⟩ :=
    Pseudoentropy.EntropyGrid.exists_secure_padded_choice_withAdvice
      (hpair nonemptyAdvice hadvice) savedPair
      ⟨hbound, hdensity, hcommon, hfits, hsize⟩
      (Filter.Eventually.of_forall Pseudoentropy.EntropyGrid.four_steps_le_owf_gap)
  refine ⟨pair, savedPair, bound, common, choose, hchoose, ?_⟩
  exact hsecure (fun a _ word => advisedWordDistinguisher (a, word))
    (by unfold advisedWordDistinguisher; fun_prop)

/-- Unconditional concrete client of `GeneratorXor.indistinguishableWithAdvice`: combining a
constant-zero candidate (`index = 0`) with an identity candidate (`index = 1`) yields an ensemble
indistinguishable from `uniformList (n + 1)` under `nonemptyAdvice`, evaluated on the
advice-dependent distinguisher `advisedWordDistinguisher`. -/
example :
    let candidate (n index : ℕ) (seed : List Bool) : List Bool :=
      if index = 0 then List.replicate (n + 1) false else seed.take (n + 1)
    Negligible (fun n => Game.advantage
      (distinguishingGame
        ((BitString.uniformList (2 * (n + 1))).map
          (GeneratorXor.generate 2 (n + 1) (n + 1) (candidate n)))
        (fun word => advisedWordDistinguisher ((n, nonemptyAdvice n), word)))
      (distinguishingGame
        (BitString.uniformList (n + 1))
        (fun word => advisedWordDistinguisher ((n, nonemptyAdvice n), word)))) := by
  let candidate (n index : ℕ) (seed : List Bool) : List Bool :=
    if index = 0 then List.replicate (n + 1) false else seed.take (n + 1)
  have hcand : Turing.MultiTapeTM.ComputableInPolyTime
      (fun input : (ℕ × ℕ) × List Bool => candidate input.1.1 input.1.2 input.2)
      (Turing.MultiTapeTM.encPair
        (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary Turing.MultiTapeTM.encUnary)
        Turing.MultiTapeTM.encBits)
      Turing.MultiTapeTM.encBits := by
    dsimp only [candidate]
    fun_prop
  have hind : IndistinguishableWithAdvice nonemptyAdvice
      (fun n => (BitString.uniformList (2 * (n + 1))).map
        (GeneratorXor.generate 2 (n + 1) (n + 1) (candidate n)))
      (fun n => BitString.uniformList (n + 1)) := by
    apply GeneratorXor.indistinguishableWithAdvice (choose := fun _ => 1)
      (by fun_prop) (by fun_prop) (by fun_prop) hcand
      (Filter.Eventually.of_forall fun _ => by decide)
    intro adversary _
    have hid (n : ℕ) :
        (BitString.uniformList (n + 1)).map (candidate n 1) = BitString.uniformList (n + 1) := by
      simpa only [candidate, one_ne_zero, ↓reduceIte] using
        BitString.uniformList_take (le_refl (n + 1))
    simpa only [hid, Game.advantage_self] using negligible_zero
  exact hind advisedWordDistinguisher (by unfold advisedWordDistinguisher; fun_prop)

/-- Concrete exercised client of `NonuniformOneWay.exists_nonuniformPRG`,
`NonuniformOneWay.exists_nonuniformPRG_three_mul`,
`NonuniformOneWay.exists_auxiliaryInputZeroKnowledge_of_mem_NP` (chained to
`UnboundedAuxiliaryInputZeroKnowledge` and `InstanceAuxiliaryInputZeroKnowledge`),
`NonuniformOneWay.exists_auxiliaryInputZeroKnowledge_of_npRelation`, and the soundness-amplified
(`(1 / 3) ^ (n + 1)`, `ZKProof.NegligibleSoundness`) landmark theorems
`NonuniformOneWay.exists_zkProof_of_mem_NP` and
`NonuniformOneWay.exists_zkProof_of_npRelation` on `ThreeSAT`. -/
example {f : List Bool → List Bool} (hf : NonuniformOneWay f) :
    (∃ g₁ : List Bool → List Bool, NonuniformPRG g₁ (fun n => n + 1)) ∧
    (∃ g₃ : List Bool → List Bool, NonuniformPRG g₃ (fun n => 3 * n + 1)) ∧
    (∃ zk : ZeroKnowledgeProof Complexity.encCNF Complexity.ThreeSAT,
      zk.AuxiliaryInputZeroKnowledge ∧
      zk.UnboundedAuxiliaryInputZeroKnowledge ∧
      zk.InstanceAuxiliaryInputZeroKnowledge) ∧
    (∃ zk : ZeroKnowledgeProof Complexity.encCNF Complexity.ThreeSAT.npRelation.language,
      (∀ a w, zk.isWitness a w = true ↔ Complexity.ThreeSAT.npRelation.IsWitness a w) ∧
      zk.AuxiliaryInputZeroKnowledge) ∧
    (∃ zk : ZKProof Complexity.encCNF Complexity.ThreeSAT
        (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      zk.NegligibleSoundness ∧
      zk.AuxiliaryInputZeroKnowledge ∧
      zk.UnboundedAuxiliaryInputZeroKnowledge ∧
      zk.InstanceAuxiliaryInputZeroKnowledge) ∧
    (∃ zk : ZKProof Complexity.encCNF Complexity.ThreeSAT.npRelation.language
        (fun n => (1 / 3 : ENNReal) ^ (n + 1)),
      (∀ a w, zk.isWitness a w = true ↔ Complexity.ThreeSAT.npRelation.IsWitness a w) ∧
      zk.NegligibleSoundness ∧
      zk.AuxiliaryInputZeroKnowledge ∧
      zk.UnboundedAuxiliaryInputZeroKnowledge ∧
      zk.InstanceAuxiliaryInputZeroKnowledge) := by
  obtain ⟨zk, hzk⟩ :=
    hf.exists_auxiliaryInputZeroKnowledge_of_mem_NP Complexity.ThreeSAT.mem_NP
  obtain ⟨zkSeq, hnegSeq, hzkSeq⟩ :=
    hf.exists_zkProof_of_mem_NP Complexity.ThreeSAT.mem_NP
  obtain ⟨zkRel, hwRel, hnegRel, hzkRel⟩ :=
    hf.exists_zkProof_of_npRelation Complexity.ThreeSAT.npRelation
  exact ⟨hf.exists_nonuniformPRG, hf.exists_nonuniformPRG_three_mul,
    ⟨zk, hzk, hzk.unboundedAuxiliaryInputZeroKnowledge, hzk.instanceAuxiliaryInputZeroKnowledge⟩,
    hf.exists_auxiliaryInputZeroKnowledge_of_npRelation Complexity.ThreeSAT.npRelation,
    ⟨zkSeq, hnegSeq, hzkSeq,
      hzkSeq.unboundedAuxiliaryInputZeroKnowledge,
      hzkSeq.instanceAuxiliaryInputZeroKnowledge⟩,
    ⟨zkRel, hwRel, hnegRel, hzkRel,
      hzkRel.unboundedAuxiliaryInputZeroKnowledge,
      hzkRel.instanceAuxiliaryInputZeroKnowledge⟩⟩

end CslibFrontierTests.Crypto.Nonuniform
