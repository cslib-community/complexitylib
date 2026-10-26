/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Crypto.Computational.OneWay
public import Complexity.Crypto.Computational.Prediction
public import Complexity.Crypto.Computational.PseudorandomGenerator
import Complexity.Languages.Probabilistic.Notation
import Complexity.Tactic.PPT


import Diag1155.Measure
/-!
# Hard-core predicates and one-bit expansion

A hard-core predicate is efficiently computable from a seed but unpredictable from its image.
Security quantifies over uniform PPT predictors and measures absolute bias from one half, so it
also rules out reliable anticorrelation. This property alone does not require the image function
to be one-way or injective.

The reduction appends a fixed trial bit to the image, runs a distinguisher, and predicts the trial
on acceptance or its complement on rejection. The distinguishing gap is the average of the signed
biases of the two fixed predictors. Both are single uniform programs, with no choice depending on
the security parameter. `Pr[p]` is the probability, in the reals, that the program `p` returns
`true` (the scoped notation of `Cslib.Probability`).

Appending a hard-core predicate to an efficient length-preserving permutation gives a one-bit PRG
in the existing finite-family security API. This is conditional on the hard-core predicate;
the Goldreich–Levin construction is a separate step in the OWP-to-PRG reduction.

## Main definitions

* `Cslib.Crypto.HardCore`: efficient evaluation and uniform computational unpredictability.
* `Cslib.Crypto.hardCorePredictor`: the functional distinguishing-to-prediction reduction.

## Main results

* `Cslib.Crypto.isPPT_hardCorePredictor`: the distinguishing-to-prediction reduction is strict PPT.
* `Cslib.Crypto.hardCore_advantage_le`: a concrete average-prediction-bias bound.
* `Cslib.Crypto.HardCore.indistinguishable`: replace a hidden predicate by an independent bit.
* `Cslib.Crypto.OneWayPermutation.pseudorandomGenerator_of_hardCore`: conditional one-bit PRG.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 9.
* [L. Trevisan, *CS276 Lecture 13: Pseudorandom Generators*][Trevisan2009PRG],
  scribed by Siu-On Chan, Theorem 2 and its prediction reduction.

Adapted from Crypto/Computational/HardCore.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared nonnegative game API and tidy machines.
-/


diag1155_install
@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- Predict a predicate of a uniform seed, given only its image and the security parameter. -/
noncomputable def predictionGame (f : List Bool → List Bool) (predicate : List Bool → Bool)
    (adversary : Distinguisher) (n : ℕ) : ProbComp Bool := do
  let seed ← BitString.sampleList n
  let guess ← adversary n (f seed)
  return guess == predicate seed

/-- Absolute bias above or below the correctness probability of a fair guess. -/
noncomputable abbrev predictionAdvantage (f : List Bool → List Bool)
    (predicate : List Bool → Bool) (adversary : Distinguisher) (n : ℕ) : ℝ≥0 :=
  Game.guessingAdvantage (ProbComp.eval (predictionGame f predicate adversary n))

/-- A plain polynomial-time predicate whose value is computationally hidden by the image
function. -/
structure HardCore (f : List Bool → List Bool) (predicate : List Bool → Bool) : Prop where
  /-- Computing the predicate from the seed uses a fixed polynomial-time machine. -/
  polyTime : ComputableInPolyTime predicate encBits encBool
  /-- A predictor's correctness is indistinguishable from a fair coin. -/
  secure : Game.Indistinguishable
    (fun adversary n => ProbComp.eval (predictionGame f predicate adversary n))
    (fun _ _ => PMF.uniformOfFintype Bool) (IsPPT encBool)

/-- The shared security property gives negligible absolute prediction bias. -/
theorem HardCore.unpredictable {f : List Bool → List Bool} {predicate : List Bool → Bool}
    (h : HardCore f predicate) (adversary : Distinguisher) (ha : IsPPT encBool adversary) :
    Negligible (predictionAdvantage f predicate adversary) := h.secure adversary ha

/-- Establish a hard-core predicate from efficient evaluation and negligible prediction bias. -/
theorem HardCore.of_unpredictable {f : List Bool → List Bool} {predicate : List Bool → Bool}
    (hp : ComputableInPolyTime predicate encBits encBool)
    (h : ∀ adversary : Distinguisher, IsPPT encBool adversary →
      Negligible (predictionAdvantage f predicate adversary)) : HardCore f predicate := by
  simp only [Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime] at hp
  exact ⟨.of_tidy hp, h⟩

/-- The prediction experiment is a uniform PPT program when its ingredients are efficient. -/
@[program_certificate]
theorem isPPTOn_predictionGame {f : List Bool → List Bool} {predicate : List Bool → Bool}
    {adversary : Distinguisher} (hf : ComputableInPolyTime f encBits encBits)
    (hp : ComputableInPolyTime predicate encBits encBool) (ha : IsPPT encBool adversary) :
    IsPPTOn encUnary encBool (predictionGame f predicate adversary) := by
  unfold predictionGame
  ppt

/-- Use acceptance of an appended trial bit to predict the hidden predicate. -/
def hardCorePredictor (adversary : Distinguisher) (trial : Bool) : Distinguisher :=
  fun n image => trialPredictor (fun bit => adversary n (image ++ [bit])) trial

/-- The reduction charges for constructing the extended input and executing the distinguisher. -/
@[program_certificate]
theorem isPPT_hardCorePredictor {adversary : Distinguisher}
    (ha : IsPPT encBool adversary) (trial : Bool) :
    IsPPT encBool (hardCorePredictor adversary trial) := by
  unfold hardCorePredictor
  ppt

/-- The ideal hybrid replaces the hidden predicate by an independent fair bit. -/
noncomputable def hardCoreIdeal (f : List Bool → List Bool) (n : ℕ) : PMF (List Bool) := do
  let seed ← BitString.uniformList n
  (PMF.uniformOfFintype Bool).map (fun bit => f seed ++ [bit])

private theorem real_probability (f : List Bool → List Bool) (predicate : List Bool → Bool)
    (adversary : Distinguisher) (n : ℕ) :
    Pr[prgRealGame (fun seed => f seed ++ [predicate seed]) adversary n] =
      ∑ bits : BitString n, ((PMF.uniformOfFintype (BitString n)) bits).toReal *
        Pr[adversary n (f (List.ofFn bits) ++ [predicate (List.ofFn bits)])] := by
  simp only [eval_prgRealGame, distinguishingGame, PMF.monad_bind_eq_bind,
    generatorEnsemble,
    BitString.uniformList, PMF.bind_map, Function.comp_def, PMF.map_comp, PMF.bind_apply_toReal]

private theorem ideal_probability (f : List Bool → List Bool) (adversary : Distinguisher)
    (n : ℕ) :
    (Game.succProbability (distinguishingGame (hardCoreIdeal f n) (adversary n)) : ℝ) =
      ∑ bits : BitString n, ((PMF.uniformOfFintype (BitString n)) bits).toReal *
        ((Pr[adversary n (f (List.ofFn bits) ++ [false])] +
          Pr[adversary n (f (List.ofFn bits) ++ [true])]) / 2) := by
  simp only [Game.coe_succProbability, distinguishingGame, hardCoreIdeal, PMF.monad_bind_eq_bind,
    BitString.uniformList,
    PMF.bind_map, PMF.bind_bind, Function.comp_def, PMF.bind_apply_toReal]
  apply Finset.sum_congr rfl
  intro bits _
  norm_num [PMF.uniformOfFintype_apply, Fintype.sum_bool]
  ring

private theorem prediction_probability (f : List Bool → List Bool) (predicate : List Bool → Bool)
    (adversary : Distinguisher) (n : ℕ) :
    Pr[predictionGame f predicate adversary n] =
      ∑ bits : BitString n, ((PMF.uniformOfFintype (BitString n)) bits).toReal *
        Pr[(fun guess => guess == predicate (List.ofFn bits)) <$> adversary n (f (List.ofFn bits))]
      := by
  simp only [predictionGame, ProbComp.eval_bind, BitString.eval_sampleList,
    BitString.uniformList, PMF.bind_map, Function.comp_def, ProbComp.eval_map, ProbComp.eval_pure]
  rw [PMF.bind_apply_toReal]
  rfl

/-- The distinguishing gap is the average signed bias of two fixed uniform predictors. -/
theorem hardCore_gap (f : List Bool → List Bool) (predicate : List Bool → Bool)
    (adversary : Distinguisher) (n : ℕ) :
    Pr[prgRealGame (fun seed => f seed ++ [predicate seed]) adversary n] -
        (Game.succProbability (distinguishingGame (hardCoreIdeal f n) (adversary n)) : ℝ) =
      (Pr[predictionGame f predicate (hardCorePredictor adversary false) n] +
        Pr[predictionGame f predicate (hardCorePredictor adversary true) n] - 1) / 2 := by
  have hstep (seed : List Bool) :=
    trialPredictor_gap (fun trial => adversary n (f seed ++ [trial])) (predicate seed)
  rw [real_probability, ideal_probability, prediction_probability, prediction_probability,
    ← Finset.sum_sub_distrib]
  simp only [hardCorePredictor]
  simp_rw [← mul_sub, hstep]
  simp only [← mul_div_assoc, ← Finset.sum_div, mul_sub, mul_add, mul_one,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, PMF.sum_toReal]

/-- Distinguishing the predicate from a fair bit costs at most the average prediction bias. -/
theorem hardCore_advantage_le (f : List Bool → List Bool) (predicate : List Bool → Bool)
    (adversary : Distinguisher) (n : ℕ) :
    Game.advantage
        (ProbComp.eval (prgRealGame (fun seed => f seed ++ [predicate seed]) adversary n))
        (distinguishingGame (hardCoreIdeal f n) (adversary n)) ≤
      (predictionAdvantage f predicate (hardCorePredictor adversary false) n +
        predictionAdvantage f predicate (hardCorePredictor adversary true) n) / 2 := by
  apply NNReal.coe_le_coe.mp
  rw [Game.coe_advantage, NNReal.coe_div, NNReal.coe_add, NNReal.coe_ofNat,
    predictionAdvantage, predictionAdvantage, Game.coe_guessingAdvantage,
    Game.coe_guessingAdvantage,
    Game.coe_succProbability (ProbComp.eval (prgRealGame _ adversary n)), hardCore_gap]
  let left := Pr[predictionGame f predicate (hardCorePredictor adversary false) n]
  let right := Pr[predictionGame f predicate (hardCorePredictor adversary true) n]
  change |(left + right - 1) / 2| ≤ (|left - 1 / 2| + |right - 1 / 2|) / 2
  rw [show left + right - 1 = (left - 1 / 2) + (right - 1 / 2) by ring, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)

/-- A hard-core predicate can be replaced by an independent fair bit in every uniform PPT test. -/
theorem HardCore.indistinguishable {f : List Bool → List Bool} {predicate : List Bool → Bool}
    (h : HardCore f predicate) :
    ComputationallyIndistinguishable (generatorEnsemble (fun seed => f seed ++ [predicate seed]))
      (hardCoreIdeal f) := by
  intro adversary ha
  have hleft := h.unpredictable _ (isPPT_hardCorePredictor ha false)
  have hright := h.unpredictable _ (isPPT_hardCorePredictor ha true)
  apply negligible_of_le (hleft.add_fun hright)
  intro n
  simpa only [eval_prgRealGame] using (hardCore_advantage_le f predicate adversary n).trans
    (div_le_self (by positivity) (by norm_num))

/-- If the image function preserves uniform seeds, the ideal hybrid is uniform at length n+1. -/
theorem HardCore.indistinguishable_of_uniform {f : List Bool → List Bool}
    {predicate : List Bool → Bool} (h : HardCore f predicate)
    (huniform : ∀ n, (BitString.uniformList n).map f = BitString.uniformList n) :
    ComputationallyIndistinguishable (generatorEnsemble (fun seed => f seed ++ [predicate seed]))
      (fun n => BitString.uniformList (n + 1)) := by
  have hideal : hardCoreIdeal f = fun n => BitString.uniformList (n + 1) := by
    funext n
    change (BitString.uniformList n).bind
      ((fun word => (PMF.uniformOfFintype Bool).map (fun bit => word ++ [bit])) ∘ f) = _
    rw [← PMF.bind_map, huniform]
    exact (BitString.uniformList_snoc n).symm
  rw [← hideal]
  exact h.indistinguishable

/-- An efficient length-preserving function that preserves uniform seeds gives a one-bit PRG
when extended by a hard-core predicate. The later predicate construction uses one-wayness. -/
theorem HardCore.pseudorandomGenerator {f : List Bool → List Bool} {predicate : List Bool → Bool}
    (h : HardCore f predicate) (hf : ComputableInPolyTime f encBits encBits)
    (hlen : ∀ word, (f word).length = word.length)
    (huniform : ∀ n, (BitString.uniformList n).map f = BitString.uniformList n) :
    PseudorandomGenerator (fun seed => f seed ++ [predicate seed]) (fun n => n + 1) := by
  have hf := hf.tidy
  have hp := h.polyTime.tidy
  refine PseudorandomGenerator.of_indistinguishable (.of_tidy (by fun_prop)) ?_ Nat.lt_succ_self
    (h.indistinguishable_of_uniform huniform)
  intro seed
  simp [hlen]

/-- A one-way permutation with a hard-core predicate gives a uniform polynomial-time one-bit PRG. -/
theorem OneWayPermutation.pseudorandomGenerator_of_hardCore {f : List Bool → List Bool}
    {predicate : List Bool → Bool} (hf : OneWayPermutation f) (h : HardCore f predicate) :
    PseudorandomGenerator (fun seed => f seed ++ [predicate seed]) (fun n => n + 1) :=
  h.pseudorandomGenerator hf.oneWay.polyTime hf.length_eq hf.uniformList_map

end Cslib.Crypto
