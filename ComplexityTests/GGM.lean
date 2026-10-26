/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.GGM.Security
import Complexity.Tactic.PPT

/-! GGM's evaluator, adaptive games, uniform reduction and conditional security theorem. Concrete
generators below exercise the certificates without being assumed pseudorandom. -/

namespace ComplexityTests.GGM

open Turing.MultiTapeTM Cslib Cslib.Crypto Cslib.Probability

example : GGM.eval (fun seed => seed ++ seed.reverse ++ [true]) [false, true] [true, false] =
    [true, false] := by decide

example (query : List Bool) : GGM.eval (fun _ => [true]) [] query = [] := by
  exact List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (GGM.length_eval_le _ [] query))

-- Duplicating the seed is a concrete efficient generator, though it is not pseudorandom.
example : ComputableInPolyTime
    (fun p : List Bool × List Bool => GGM.eval (fun seed => seed ++ seed) p.1 p.2)
    (encPair encBits encBits) encBits := by fun_prop

-- A shrinking expansion is allowed: efficiency does not require a PRG or a length hypothesis.
example : ComputableInPolyTime
    (fun p : List Bool × List Bool => GGM.eval List.tail p.1 p.2)
    (encPair encBits encBits) encBits := by fun_prop

example (generator : List Bool → List Bool)
    (hgenerator : ComputableInPolyTime generator encBits encBits) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => GGM.eval generator p.1 (p.2 ++ p.2))
      (encPair encBits encBits) encBits := by fun_prop

-- Computed inputs and a nonempty cache use the same registered handler rule.
example : IsPPTOn (encPair encUnary encBits) (encPair encBits GGM.cacheEncoding)
    (fun pair => GGM.frontierOracle (fun seed => seed ++ seed) pair.1 (pair.1 + 1)
      pair.2.reverse [(pair.2, pair.2)]) := by fun_prop

-- The ordinary monadic spelling exposes no machine or tape-layout details.
example : IsPPTOn (encPair encUnary encBits) (encPair encBits GGM.cacheEncoding)
    (fun pair => if pair.2.length = pair.1 then do
      let (seed, cache) ← memoize (fun _ => BitString.sampleList pair.1)
        (pair.2.take (pair.1 + 1)) []
      return (GGM.eval List.tail seed (pair.2.drop (pair.1 + 1)), cache)
    else pure ([], [])) := by
  unfold GGM.cacheEncoding
  ppt

-- The full-game certificate has concrete inhabitants without a cryptographic assumption.
example : IsPPTOn (encPair encUnary encUnary) encBool
    (fun pair => GGM.hybridGame (fun seed => seed ++ seed)
      (fun n input => pure (decide (input.length ≤ n))) pair.1 pair.2) :=
  GGM.isPPTOn_hybridGame (.of_tidy (by fun_prop)) (by fun_prop)

-- An empty seed and query still create exactly one empty root entry.
example (generator : List Bool → List Bool) :
    GGM.frontierOracle generator 0 0 [] [] = pure ([], [([], [])]) := by
  simp [GGM.frontierOracle, memoize, BitString.sampleList]

-- Rejection does not touch arbitrary preassigned private state.
example (generator : List Bool → List Bool) (depth : ℕ) (cache : GGM.Cache) :
    GGM.frontierOracle generator 1 depth [] cache = pure ([], cache) := by
  simp [GGM.frontierOracle]

-- Repeated keys use the first entry; depths past the query length are also well defined.
example (generator : List Bool → List Bool) :
    GGM.frontierOracle generator 1 3 [false] [([false], [true]), ([false], [false])] =
      pure ([true], [([false], [true]), ([false], [false])]) := by
  simp [GGM.frontierOracle, memoize]

-- When the client makes no queries, lazily deferring the root draw preserves its private coin.
example (generator : List Bool → List Bool) (n : ℕ) :
    ProbComp.eval (GGM.hybridGame generator
      (fun _ _ => ProbOracleComp.sample (ProbComp.uniform Bool)) n 0) =
        PMF.uniformOfFintype Bool := by
  rw [GGM.hybridGame_zero]
  simp only [prfRealGame, ProbComp.eval_bind, ProbOracleComp.eval_interpret]
  simpa [ProbOracleComp.interpret_sample] using
    (show OracleComp.interpret ProbComp.unifOracle (ProbComp.uniform Bool) =
      PMF.uniformOfFintype Bool from ProbComp.eval_uniform Bool)

-- Captured samplers and computed indices use ordinary list and option operations.
example : IsPPTOn (encPair encUnary encBits) (encPair encBits GGM.cacheEncoding)
    (fun pair => GGM.expansionOracle List.tail
      ((fun bits => bits ++ pair.2) <$> BitString.sampleList (pair.1 + 1))
        pair.1 (pair.1 + 1) pair.2.reverse [(pair.2, pair.2)]) := by fun_prop

-- A preassigned cache is retained on malformed queries, without invoking the sampler.
example (generator : List Bool → List Bool) (sample : ProbComp (List Bool))
    (depth : ℕ) (cache : GGM.Cache) :
    GGM.expansionOracle generator sample 1 depth [] cache = pure ([], cache) := by
  simp [GGM.expansionOracle]

-- Truncation charges and stores only two labels even for a longer sampled challenge.
example : GGM.expansionOracle List.tail (pure [true, false, true]) 1 0 [false] [] =
    pure ([true], [([], [true, false])]) := by
  simp [GGM.expansionOracle, GGM.selectChild, memoize]

-- Short challenges are allowed: the selected child may be empty.
example : GGM.expansionOracle List.tail (pure [true]) 1 0 [true] [] =
    pure ([], [([], [true])]) := by
  simp [GGM.expansionOracle, GGM.selectChild, memoize]

-- Cache hits do not resample; duplicate parent keys keep their first expansion.
example : GGM.expansionOracle List.tail (pure []) 1 0 [true]
      [([], [false, true]), ([], [true, false])] =
    pure ([true], [([], [false, true]), ([], [true, false])]) := by
  simp [GGM.expansionOracle, GGM.selectChild, memoize]

-- A private coin chooses query order; comparing the answers detects correlated child labels.
private noncomputable def siblings (_ : ℕ) (_ : List Bool) : WordOracleComp Unit Bool := do
  let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
  let first ← ProbOracleComp.query ((), [coin])
  let second ← ProbOracleComp.query ((), [!coin])
  return first.headD false == second.headD false

example : ProbComp.eval (GGM.expansionGame List.tail (BitString.sampleList 2) siblings 1 0) =
    ProbComp.eval (prfIdealGame siblings 1) := by
  rw [GGM.expansionGame_uniform List.tail siblings 1 0 (by decide), GGM.hybridGame_self]

-- Every certified sampler and adaptive adversary compose through the complete-game contract.
example {generator : List Bool → List Bool} {sample : ℕ → ProbComp (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hs : IsPPTOn encUnary encBits sample) {adversary : OracleDistinguisher}
    (ha : IsOraclePPT encBool adversary) : IsPPTOn encUnary encBool
      (fun n => GGM.expansionGame generator (sample n) adversary n (n + 1)) :=
  GGM.isPPTOn_expansionGame hg hs (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)) ha

-- Saved challenges may be short, oversized or absent, and the requested depth may exceed width.
example {adversary : OracleDistinguisher} (ha : IsOraclePPT encBool adversary) :
    IsPPTOn (encPair encUnary (encList encBits)) encBool (fun pair =>
      GGM.sampleGame List.tail adversary pair.1 (pair.1 + 1) pair.2) :=
  GGM.isPPTOn_sampleGame (.of_tidy (by fun_prop)) (.of_tidy (by fun_prop)) (.of_tidy (by
    fun_prop)) (.of_tidy (by fun_prop)) ha

-- The complete reduction has a concrete certificate without any cryptographic premise.
example : IsPPT encBool (GGM.reduction (fun seed => seed ++ seed)
    (fun n word => pure (decide (word.length ≤ n))) (fun n => n ^ 2 + 3)) :=
  GGM.isPPT_reduction (.of_tidy (by fun_prop)) (by fun_prop) (.of_tidy (by fun_prop))

-- The semantic sibling client has a bound on its external calls, including its private coin.
private theorem siblings_queryBounds (n : ℕ) : (siblings n []).IsQueryBounded 2 :=
  ((ProbOracleComp.IsQueryBounded.sample _).bind fun coin =>
    (ProbOracleComp.IsQueryBounded.query ((), [coin])).bind fun first =>
      (ProbOracleComp.IsQueryBounded.query ((), [!coin])).bind fun second =>
        OracleComp.IsCostBounded.pure _ 0).mono (by norm_num)

-- The exact reduction loss applies to this randomized two-query client without a PPT premise.
example (generator : List Bool → List Bool) :
    Game.advantage (ProbComp.eval (prfRealGame (GGM.eval generator) siblings 1))
        (ProbComp.eval (prfIdealGame siblings 1)) =
      dyadicSize 1 * dyadicSize 2 *
        Game.advantage
          (ProbComp.eval ((generator <$> BitString.sampleList 1) >>=
            GGM.reduction generator siblings (fun _ => 2) 1))
          (ProbComp.eval (BitString.sampleList 2 >>=
            GGM.reduction generator siblings (fun _ => 2) 1)) :=
  GGM.reduction_advantage generator siblings (fun _ => 2) 1 (siblings_queryBounds 1)

-- Any PRG, including the strict zero-width convention, supplies the full adaptive PRF contract.
example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (h : PseudorandomGenerator generator length) :
    ∃ family : List Bool → List Bool → List Bool, PseudorandomFunction family :=
  h.exists_pseudorandomFunction

end ComplexityTests.GGM
