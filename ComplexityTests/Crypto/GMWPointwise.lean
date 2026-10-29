/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.GMW.Simulator
import Complexity.Tactic.PPT

/-! Concrete model clients for the pointwise GMW reduction. These checks assert no security
property of a toy generator. The formula and witness reuse the zero-knowledge test instance. -/

namespace ComplexityTests.Crypto.GMWPointwise

open Cslib Cslib.Crypto Cslib.Complexity Cslib.Probability Cslib.Logic.PL Turing.MultiTapeTM
open scoped NNReal

def satFormula : CNF ℕ := [[(0, true), (1, false)]]

theorem satFormula_verified : ThreeSAT.verifier (satFormula, [true, false]) = true := by
  decide

example : GMW.totalLen satFormula = 36 := by decide

/-- Keep one private coin and one commitment bit, derive the challenge from both, and retain
the coin, commitment prefix, challenge, opening prefix and auxiliary input in the output. -/
noncomputable def adaptiveVerifier (_n : ℕ) (_φ : CNF ℕ) (z : List Bool) :
    WordOracleComp Unit (List Bool) := do
  let coins ← ProbOracleComp.sample (BitString.sampleList 1)
  let first ← List.take 1 <$> ProbOracleComp.query ((), z)
  let ch := List.take 3 (first ++ coins ++ [false, false, false])
  let opened ← List.take 2 <$> ProbOracleComp.query ((), ch)
  return coins ++ first ++ ch ++ opened ++ z

theorem adaptiveVerifier_isOraclePPTOn :
    IsOraclePPTOn (encPair encUnary (encPair encCNF encBits)) encBits
      (fun p => adaptiveVerifier p.1 p.2.1 p.2.2) := by
  unfold adaptiveVerifier
  apply IsOraclePPTOn.bind_with (middle := encBits)
  · exact (isPPTOn_sampleList.preprocess (.const 1)).isOraclePPTOn
  · apply IsOraclePPTOn.bind_with (middle := encBits)
    · exact IsOraclePPTOn.query_take () (by fun_prop) (by fun_prop)
    · dsimp only
      apply IsOraclePPTOn.bind_with (middle := encBits)
      · exact IsOraclePPTOn.query_take () (by fun_prop) (by fun_prop)
      · fun_prop

/-- A deterministic two-round handler exposes the verifier's complete output jointly with the
recorded challenge. Private randomness is still sampled and appears unchanged in the output. -/
theorem runTwoRound_adaptiveVerifier (n : ℕ) (φ : CNF ℕ) (z : List Bool) (b : Bool) :
    GMW.runTwoRound (fun _ => [b]) id (adaptiveVerifier n φ z) (0, [false, false, false]) =
      (fun coins =>
        let ch := List.take 3 ([b] ++ coins ++ [false, false, false])
        let row := BitString.listRow 3 0 ch
        (coins ++ [b] ++ ch ++ List.take 2 row ++ z, (2, row))) <$>
          BitString.sampleList 1 := by
  simp [adaptiveVerifier, GMW.runTwoRound_bind, GMW.runTwoRound_map, GMW.twoRoundStep]

-- The challenge changes with the first commitment bit even when the private coin is fixed.
example (coin : Bool) :
    List.take 3 ([false] ++ [coin] ++ [false, false, false]) ≠
      List.take 3 ([true] ++ [coin] ++ [false, false, false]) := by
  cases coin <;> decide

-- The empty formula is a valid input, with no pad coordinates to replace.
example : ThreeSAT.verifier (([] : CNF ℕ), []) = true := by decide

example : GMW.totalLen ([] : CNF ℕ) = 0 := by decide

-- Padding indices reject when the hybrid has no coordinates, regardless of its postprocessor.
example {α : Type} (left right : ProbComp α) (test : List α → ProbComp Bool) (challenge : α) :
    ProbComp.eval (sequenceTest left right 0 test challenge) = PMF.pure false := by
  simp only [sequenceTest, Nat.not_lt_zero, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure]
  exact PMF.bind_const _ _

example : dyadicSize 0 = 2 := by decide

example {α : Type} (left right : ProbComp α) :
    sequenceHybrid left right 0 0 = pure [] := by
  simp [sequenceHybrid]

-- This concrete expansion is used only to instantiate the finite theorem and its clock.
def tripleGen (seed : List Bool) : List Bool := seed ++ seed ++ seed ++ [false]

theorem tripleGen_polyTime : ComputableInPolyTime tripleGen encBits encBits := by
  unfold tripleGen
  fun_prop

theorem length_tripleGen (seed : List Bool) : (tripleGen seed).length = 3 * seed.length + 1 := by
  simp only [tripleGen, List.length_append, List.length_cons, List.length_nil]
  omega

/-- Inspect the security parameter, common input, auxiliary word and full verifier output. -/
def retainedTest (n : ℕ) (φ : CNF ℕ) (z view : List Bool) : ProbComp Bool :=
  pure (view.length == φ.length + z.length + n)

theorem retainedTest_isPPTOn :
    IsPPTOn (encPair (encPair encUnary (encPair encCNF encBits)) encBits) encBool
      (fun p => retainedTest p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  unfold retainedTest
  ppt

theorem reduction_isPPTOn :
    IsPPTOn
      (encPair (encPair encUnary (encPair encCNF (encPair encBits encBits))) encBits) encBool
      (fun p : (ℕ × (CNF ℕ × (List Bool × List Bool))) × List Bool =>
        GMW.gmwViewReduction tripleGen (fun k => 3 * k + 1) id adaptiveVerifier retainedTest
          p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) :=
  GMW.isPPTOn_gmwViewReduction tripleGen_polyTime length_tripleGen
    ComputableInPolyTime.id' adaptiveVerifier_isOraclePPTOn retainedTest_isPPTOn

noncomputable def viewAdvantage (n : ℕ) (φ : CNF ℕ) (w z : List Bool) : ℝ≥0 :=
  Game.advantage
    (distinguishingGame
      (((GMW.gmwProver tripleGen (n + 7) (3 * (n + 7) + 1) φ w).run
        (adaptiveVerifier n φ z)
        (GMW.gmwProver tripleGen (n + 7) (3 * (n + 7) + 1) φ w).init).map Prod.fst)
      (retainedTest n φ z))
    (distinguishingGame
      (ProbComp.eval (GMW.gmwSimulator tripleGen (fun k => 3 * k + 1) id adaptiveVerifier n φ z))
      (retainedTest n φ z))

noncomputable def reductionAdvantage (n : ℕ) (φ : CNF ℕ) (w z : List Bool) : ℝ≥0 :=
  Game.advantage
    (ProbComp.eval ((tripleGen <$> BitString.sampleList (n + 7)) >>=
      GMW.gmwViewReduction tripleGen (fun k => 3 * k + 1) id adaptiveVerifier retainedTest n φ w z))
    (ProbComp.eval (BitString.sampleList (3 * (n + 7) + 1) >>=
      GMW.gmwViewReduction tripleGen (fun k => 3 * k + 1) id adaptiveVerifier retainedTest n φ w z))

theorem sat_viewAdvantage_le (n : ℕ) (z : List Bool) :
    viewAdvantage n satFormula [true, false] z ≤ (7 / 8 : ℝ≥0) ^ (n + 1) +
      (dyadicSize (n + 1) : ℝ≥0) * (dyadicSize 36 : ℝ≥0) *
        reductionAdvantage n satFormula [true, false] z := by
  exact GMW.gmwView_advantage_le tripleGen (fun k => 3 * k + 1) id
    adaptiveVerifier retainedTest n satFormula [true, false] z satFormula_verified

/-- With no commitments the inner hybrid rejects every challenge, including malformed words. -/
theorem eval_emptyReduction (n : ℕ) (w z challenge : List Bool) :
    ProbComp.eval (GMW.gmwViewReduction tripleGen (fun k => 3 * k + 1) id
      adaptiveVerifier retainedTest n [] w z challenge) = PMF.pure false := by
  simp only [GMW.gmwViewReduction, id_eq, show GMW.totalLen ([] : CNF ℕ) = 0 by decide,
    sequenceTest, Nat.not_lt_zero, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure]
  exact PMF.bind_const _ _

theorem empty_viewAdvantage_le (n : ℕ) (z : List Bool) :
    viewAdvantage n [] [] z ≤ (7 / 8 : ℝ≥0) ^ (n + 1) := by
  have hbound := GMW.gmwView_advantage_le tripleGen (fun k => 3 * k + 1) id
    adaptiveVerifier retainedTest n [] [] z (by decide)
  have hreduce (source : ProbComp (List Bool)) :
      ProbComp.eval (source >>= GMW.gmwViewReduction tripleGen (fun k => 3 * k + 1) id
        adaptiveVerifier retainedTest n [] [] z) = PMF.pure false := by
    simp only [ProbComp.eval_bind, eval_emptyReduction]
    exact PMF.bind_const _ _
  simpa only [viewAdvantage, id_eq, hreduce, Game.advantage_self, mul_zero, add_zero] using hbound

end ComplexityTests.Crypto.GMWPointwise
