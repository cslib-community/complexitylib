/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GGM.Expansion
public import Complexity.Crypto.Computational.Hybrid.Sequence
public import Complexity.Computability.Probabilistic.Presample
import Complexity.Tactic.PPT

/-!
# The GGM reduction to one generator challenge

The expansion game consumes at most one fresh draw per adversary call. Pre-sampling a sufficient
list exposes it as a test of independent samples, so the shared sequence hybrid supplies a single
challenge reduction. Cached replies ignore the extra draw, preserving repeated-query consistency.

## Main definitions

* `Cslib.Crypto.GGM.sampleGame`: a saved-list version of the expansion game.
* `Cslib.Crypto.GGM.levelTest`: insert one challenge at a sampled query coordinate.
* `Cslib.Crypto.GGM.reduction`: sample a level to obtain one uniform generator distinguisher.

## Main results

* `Cslib.Crypto.GGM.sampleGame_replicate`: presampling independent expansions yields the online
  game.
* `Cslib.Crypto.GGM.isPPT_reduction`: strict PPT for the complete single-challenge reduction.
* `Cslib.Crypto.GGM.reduction_advantage`: exact loss, including at zero width and query budget.

## References

* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986],
  Section 3.3, the simulation used in the proof of Theorem 3.

Adapted from Crypto/Computational/GGM/Reduction.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the shared stateful interpreter and game API.

-/

@[expose] public section

namespace Cslib.Crypto.GGM

open Probability Turing.MultiTapeTM

/-- Run the expansion game using a saved list, consuming one entry at each adversary call.
Truncation and the empty fallback make the test total on every challenge list. -/
def sampleGame (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (n depth : ℕ) (values : List (List Bool)) : ProbComp Bool :=
  Prod.fst <$> (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
      (OracleComp.withSampleList [] (fun expansion request =>
        expansionOracle generator (pure expansion) n depth request.2))) (adversary n [])).run
          ([], values)

private theorem expansionOracle_sample (generator : List Bool → List Bool)
    (sample : ProbComp (List Bool))
    (n depth : ℕ) (query : List Bool) (cache : Cache) :
    (ProbComp.eval sample).bind (fun expansion =>
      ProbComp.eval (expansionOracle generator (pure expansion) n depth query cache)) =
        ProbComp.eval (expansionOracle generator sample n depth query cache) := by
  by_cases hquery : query.length = n
  · cases hlookup : cache.lookup (query.take depth) <;>
      simp [expansionOracle, hquery, memoize, hlookup, PMF.map, Function.comp_def]
  · simp [expansionOracle, hquery]

/-- A list with one independent expansion per possible query gives exactly the online game. -/
theorem sampleGame_replicate (generator : List Bool → List Bool) (sample : ProbComp (List Bool))
    (adversary : OracleDistinguisher) (n depth count : ℕ)
    (hqueries : (adversary n []).IsQueryBounded count) :
    ProbComp.eval (OracleComp.replicate count sample >>= sampleGame generator adversary n depth) =
      ProbComp.eval (expansionGame generator sample adversary n depth) := by
  have h := hqueries.eval_presample sample []
    (fun expansion request => expansionOracle generator (pure expansion) n depth request.2) []
  have hout := congrArg (PMF.map Prod.fst) h
  have hstep := fun query cache => expansionOracle_sample generator sample n depth query cache
  simpa only [sampleGame, expansionGame, ProbComp.eval_bind, ProbComp.eval_map,
    ProbOracleComp.eval_run_interpret, PMF.map_bind, PMF.map_comp, Function.comp_def, hstep]
    using hout

/-- The saved-sample game is uniformly PPT, including arbitrary and short challenge lists.
The shared interpreter accounts for list consumption, cache lookup and tree evaluation. -/
theorem isPPTOn_sampleGame {Caller : Type} {input : Caller ↪ List Bool}
    {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    {width depth : Caller → ℕ} {values : Caller → List (List Bool)}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hdepth : ComputableInPolyTime depth input encUnary)
    (hvalues : ComputableInPolyTime values input (encList encBits))
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsPPTOn input encBool
      (fun a => sampleGame generator adversary (width a) (depth a) (values a)) := by
  have hgenerator := hgenerator.tidy
  have hwidth := hwidth.tidy
  have hdepth := hdepth.tidy
  have hvalues := hvalues.tidy
  have hrun : IsPPTOn input
      (encPair encBool (encPair cacheEncoding (encList encBits))) (fun a =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
            (OracleComp.withSampleList [] (fun expansion request =>
              expansionOracle generator (pure expansion) (width a) (depth a) request.2)))
                (adversary (width a) [])).run ([], values a)) := by
    refine hadversary.run_interpret_withSampleList (operationEncoding := encFinEnum Unit) []
      (prepare := fun a => (width a, [])) (by fun_prop) (by fun_prop) (by fun_prop) hvalues
      (fun a cache => ∀ entry ∈ cache, entry.2.length ≤ 2 * width a) (by simp)
      (resources := fun a query => 4 * query.length + 4 * width a + 3) (by fun_prop) ?_
    intro a expansion request cache hcache result hresult
    obtain ⟨hcache', hreply, hgrowth⟩ := expansionOracle_bounds generator
      (pure expansion) (width a) (depth a) request.2 cache hcache result hresult
    exact ⟨hcache', by lia, by lia⟩
  exact hrun.map (ComputableInPolyTime.fst _ _)

/-- Insert one challenge among simulated uniform and generated expansions at a chosen level. -/
noncomputable def levelTest (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (n depth count : ℕ) (challenge : List Bool) : ProbComp Bool :=
  sequenceTest (BitString.sampleList (2 * n)) (generator <$> BitString.sampleList n) count
    (sampleGame generator adversary n depth) challenge

/-- The single-challenge reduction is PPT whenever its level and query budget are efficiently
computed. No semantic query-bound hypothesis is needed for this efficiency certificate. -/
theorem isPPTOn_levelTest {Caller : Type} {input : Caller ↪ List Bool}
    {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    {width depth count : Caller → ℕ} {challenge : Caller → List Bool}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hdepth : ComputableInPolyTime depth input encUnary)
    (hcount : ComputableInPolyTime count input encUnary)
    (hchallenge : ComputableInPolyTime challenge input encBits)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsPPTOn input encBool (fun a =>
      levelTest generator adversary (width a) (depth a) (count a) (challenge a)) := by
  have htest : IsPPTOn (encPair input (encList encBits)) encBool
      (fun pair => sampleGame generator adversary (width pair.1) (depth pair.1) pair.2) :=
    isPPTOn_sampleGame hgenerator (by polytime) (by polytime) (by polytime) hadversary
  unfold levelTest
  ppt

/-- The single-challenge test captures the signed gap of adjacent GGM levels. Its loss is the
dyadic sampling range for the query budget, including padding coordinates. -/
theorem levelTest_gap (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (n depth count : ℕ) (hdepth : depth < n) (hqueries : (adversary n []).IsQueryBounded count) :
    (Game.succProbability (ProbComp.eval (hybridGame generator adversary n depth)) : ℝ) -
        Game.succProbability (ProbComp.eval (hybridGame generator adversary n (depth + 1))) =
      (dyadicSize count : ℝ) *
        ((Game.succProbability (ProbComp.eval ((generator <$> BitString.sampleList n) >>=
          levelTest generator adversary n depth count)) : ℝ) -
        (Game.succProbability (ProbComp.eval (BitString.sampleList (2 * n) >>=
          levelTest generator adversary n depth count)) : ℝ)) := by
  unfold levelTest
  have h := sequenceTest_gap (BitString.sampleList (2 * n))
    (generator <$> BitString.sampleList n) count (sampleGame generator adversary n depth)
  simpa only [sampleGame_replicate generator _ adversary n depth count
    hqueries, expansionGame_generated generator adversary n depth hdepth,
    expansionGame_uniform generator adversary n depth hdepth] using h

/-- Choose a level uniformly and run its single-challenge reduction. Both random choices use
dyadic ranges, and unused indices reject. The query budget is a fixed function of the parameter. -/
noncomputable def reduction (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (count : ℕ → ℕ) : Distinguisher := fun n challenge => do
  let depth ← ProbComp.sampleDyadicIndex n
  if depth < n then levelTest generator adversary n depth (count n) challenge else pure false

/-- Efficient generation and an efficient query budget give one uniform PPT reduction. -/
theorem isPPT_reduction {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits)
    {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) {count : ℕ → ℕ}
    (hcount : ComputableInPolyTime count encUnary encUnary) :
    IsPPT encBool (reduction generator adversary count) := by
  have hlevel : IsPPTOn (encPair (encPair encUnary encBits) encUnary) encBool
      (fun pair => levelTest generator adversary pair.1.1 pair.2 (count pair.1.1) pair.1.2) :=
    isPPTOn_levelTest hgenerator (by polytime) (by polytime) (by polytime) (by polytime) hadversary
  unfold reduction
  ppt

/-- The GGM reduction preserves the full real/ideal signed gap up to the product of the two
dyadic sampling ranges. This statement is exact, including the zero-width game. -/
theorem reduction_gap (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (count : ℕ → ℕ) (n : ℕ) (hqueries : (adversary n []).IsQueryBounded (count n)) :
    (Game.succProbability (ProbComp.eval (prfRealGame (eval generator) adversary n)) : ℝ) -
        (Game.succProbability (ProbComp.eval (prfIdealGame adversary n)) : ℝ) =
      (dyadicSize n : ℝ) * dyadicSize (count n) *
        ((Game.succProbability (ProbComp.eval ((generator <$> BitString.sampleList n) >>=
          reduction generator adversary count n)) : ℝ) -
        (Game.succProbability (ProbComp.eval (BitString.sampleList (2 * n) >>=
          reduction generator adversary count n)) : ℝ)) := by
  unfold reduction
  have h := Game.succProbability_hybrid_reduction
    (fun depth => ProbComp.eval (hybridGame generator adversary n depth))
    (fun depth => ProbComp.eval ((generator <$> BitString.sampleList n) >>=
      levelTest generator adversary n depth (count n)))
    (fun depth => ProbComp.eval (BitString.sampleList (2 * n) >>=
      levelTest generator adversary n depth (count n))) n (dyadicSize n)
    (lt_dyadicSize n).le (dyadicSize (count n))
    (fun depth hdepth =>
      levelTest_gap generator adversary n depth (count n) hdepth hqueries)
  simpa only [ProbComp.eval_bind_sampleDyadicIndex_guard, PMF.monad_bind_eq_bind,
    hybridGame_zero, hybridGame_self] using h

/-- The real/ideal PRF advantage is the reduction's generator advantage times the two sampling
ranges. The loss is polynomial whenever the query budget is polynomial. -/
theorem reduction_advantage (generator : List Bool → List Bool) (adversary : OracleDistinguisher)
    (count : ℕ → ℕ) (n : ℕ) (hqueries : (adversary n []).IsQueryBounded (count n)) :
    Game.advantage (ProbComp.eval (prfRealGame (eval generator) adversary n))
        (ProbComp.eval (prfIdealGame adversary n)) =
      dyadicSize n * dyadicSize (count n) *
        Game.advantage
          (ProbComp.eval ((generator <$> BitString.sampleList n) >>=
            reduction generator adversary count n))
          (ProbComp.eval (BitString.sampleList (2 * n) >>=
            reduction generator adversary count n)) := by
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_natCast,
    Game.coe_advantage, Game.coe_advantage, reduction_gap generator adversary count n
      hqueries, abs_mul, abs_mul, Nat.abs_cast, Nat.abs_cast]

end Cslib.Crypto.GGM
