/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Nonuniform.ZeroKnowledge
import Complexity.Crypto.Computational.Stretch
import Complexity.Crypto.Computational.Pseudoentropy.OneWay
import Complexity.Crypto.Computational.Pseudoentropy.LabelExtraction
import Complexity.Languages.Probabilistic.Notation
import Complexity.Tactic.PPT

/-! Checked clients of the nonuniform security notions. Existence of a nonuniform one-way
function or generator is open, so these checks show that the notions are not trivially true
(constant functions, fixed words and length-wise constant generators fail them) and that the
indistinguishability notion is not trivially false. They do not separate the nonuniform notions
from the uniform ones. -/

namespace ComplexityTests.Crypto.Nonuniform

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

/-- Stretching a nonuniform one-bit PRG to `3 * n + 1` bits, the GMW length, and feeding it to the
auxiliary-input GMW theorem. -/
example {generator : List Bool → List Bool} (h : NonuniformPRG generator (fun n => n + 1))
    {α : Type} {enc : α ↪ List Bool} {A : Set α} (hA : A ∈ Complexity.NP enc) :
    ∃ zk : ZeroKnowledgeProof enc A, zk.AuxiliaryInputZeroKnowledge :=
  (h.amplify (fun n => 3 * n + 1) (by fun_prop) (fun n => by omega))
    |>.exists_auxiliaryInputZeroKnowledge_of_mem_NP (fun _ => le_rfl) hA

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

end ComplexityTests.Crypto.Nonuniform
