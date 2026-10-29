/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.MAC

/-!
# Tests for uniform symmetric MAC schemes and the PRF-to-MAC construction

Provides concrete instantiations of `MACScheme` (both a trivial scheme and `prfMAC` applied to the
identity-keyed evaluator `fun _ m => m`), verifies that `OneTimeEUFCMA` and `EUFCMA` reject the
trivial scheme via an explicit zero-query PPT forger, and checks `prfMAC` tagging/verification
and `macToPrfDistinguisher` on concrete inputs.
-/

namespace ComplexityTests.Crypto.MAC

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Concrete trivial MAC scheme where every tag is accepted. Used to witness that the `MACScheme`
fields are jointly satisfiable and to verify that `OneTimeEUFCMA` and `EUFCMA` reject insecure
schemes. -/
noncomputable def trivialMACScheme : MACScheme where
  keyGen _ := pure []
  sign _ msg := pure msg
  verify _ _ _ := true
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ _ _ _ _
    rfl

/-- Concrete instantiation of `prfMAC` on the message-echo family `fun _ msg => msg`. -/
noncomputable def echoPrfMAC : MACScheme :=
  prfMAC (fun _ msg => msg) (ComputableInPolyTime.snd _ _)

-- Matching key and message lengths produce a valid tag accepted by `verify`.
example : echoPrfMAC.sign [true, false] [false, true] = pure [false, true] := by
  rfl

example : echoPrfMAC.verify [true, false] [false, true] [false, true] = true := by
  rfl

-- A wrong tag or wrong message length is rejected by `verify`.
example : echoPrfMAC.verify [true, false] [false, true] [true, true] = false := by
  rfl

example : echoPrfMAC.verify [true, false] [false] [false] = false := by
  rfl

-- A wrong-length query to `echoPrfMAC.oneTimeSigningOracle` returns `[]` and consumes the single
-- query slot.
example : echoPrfMAC.oneTimeSigningOracle [true, false] ((), [true]) [] =
    pure ([], [[true]]) := by
  rfl

example : echoPrfMAC.oneTimeSigningOracle [true, false] ((), [false, true]) [[true]] =
    pure ([], [[true]]) := by
  rfl

-- Even an always-accepting verifier cannot bypass the game's n-bit message check.
example (n : ℕ) : trivialMACScheme.eufOneTimeGame
      (fun _ _ => ProbOracleComp.sample (pure ([], []))) (n + 1) = pure false := by
  simp [MACScheme.eufOneTimeGame, trivialMACScheme]

-- A wrong-length candidate forgery causes `macToPrfDistinguisher` to reject without making a
-- verification query.
example (n : ℕ) : macToPrfDistinguisher
      (fun _ _ => ProbOracleComp.sample (pure ([], []))) (n + 1) [] = pure false := by
  simp [macToPrfDistinguisher]

/-- The trivial MAC scheme is not one-time EUF-CMA secure: a zero-query PPT forger that outputs
`(0^n, [])` succeeds with probability `1`. -/
theorem not_oneTimeEUFCMA_trivialMACScheme :
    ¬ trivialMACScheme.OneTimeEUFCMA := by
  intro hsec
  let forger : Forger := fun n _ =>
    ProbOracleComp.sample (pure (List.replicate n false, []))
  have hforgerBody : IsPPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p : ℕ × List Bool => (pure (List.replicate p.1 false, []) :
        ProbComp (List Bool × List Bool))) := by
    have hpair : ComputableInPolyTime
        (fun p : ℕ × List Bool => (List.replicate p.1 false, ([] : List Bool)))
        (encPair encUnary encBits) (encPair encBits encBits) := by polytime
    exact hpair.isPPTOn
  have hforger : IsOraclePPT (encPair encBits encBits) forger :=
    hforgerBody.isOraclePPTOn.isOraclePPT
  have hneg := hsec.negligible forger hforger
  have heval (n : ℕ) :
      Game.succProbability
        (ProbComp.eval (trivialMACScheme.eufOneTimeGame forger n)) = 1 := by
    simp [MACScheme.eufOneTimeGame, trivialMACScheme, forger, Game.succProbability]
  simp only [heval] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- The trivial MAC scheme is not EUF-CMA secure. -/
theorem not_eufCMA_trivialMACScheme :
    ¬ trivialMACScheme.EUFCMA :=
  fun h => not_oneTimeEUFCMA_trivialMACScheme h.oneTimeEUFCMA

/-- The trivial MAC scheme is not SUF-CMA secure. -/
theorem not_sufCMA_trivialMACScheme :
    ¬ trivialMACScheme.SUFCMA :=
  fun h => not_eufCMA_trivialMACScheme h.eufCma

/-! ### Separating fresh-message (`EUFCMA`) and fresh-pair (`SUFCMA`) freshness -/

/-- Randomized MAC scheme whose `sign` algorithm samples a uniform 1-bit tag and whose `verify`
algorithm accepts any 1-bit tag. Because each message has two distinct valid tags `[false]` and
`[true]`, querying a message and flipping the returned tag bit produces a fresh valid `(msg, tag)`
pair on a previously queried message. -/
noncomputable def randomizedTagMACScheme : MACScheme where
  keyGen _ := pure []
  sign _ _ := BitString.sampleList 1
  verify _ _ tag := tag.length == 1
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ _ _ tag htag
    rw [BitString.eval_sampleList] at htag
    simp [BitString.length_of_mem_support_uniformList htag]

/-- Adaptive forger that queries the `n`-bit message `0^n`, receives a 1-bit tag `tag`, and outputs
`(0^n, [!tag.headD false])`—a new valid tag on the previously signed message `0^n`. -/
def sameMessageNewTagForger : Forger :=
  fun n _ =>
    (fun tag => (List.replicate n false, [!tag.headD false])) <$>
      (List.take 1 <$> ProbOracleComp.query ((), List.replicate n false))

/-- `sameMessageNewTagForger` is uniformly strict oracle-PPT. -/
theorem isOraclePPT_sameMessageNewTagForger :
    IsOraclePPT (encPair encBits encBits) sameMessageNewTagForger := by
  have hq : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool =>
        List.take 1 <$> ProbOracleComp.query ((), List.replicate p.1 false)) :=
    IsOraclePPTOn.query_take () (by polytime) (by polytime)
  unfold sameMessageNewTagForger
  exact (hq.map_with (by polytime)).isOraclePPT

/-- In the fresh-message `eufCmaGame`, `sameMessageNewTagForger` always loses (`PMF.pure false`)
because its forgery message `0^n` was previously queried to the signing oracle. -/
theorem eval_eufCmaGame_randomizedTagMACScheme_sameMessageNewTagForger (n : ℕ) :
    ProbComp.eval (randomizedTagMACScheme.eufCmaGame sameMessageNewTagForger n) =
      PMF.pure false := by
  simp only [MACScheme.eufCmaGame, randomizedTagMACScheme, sameMessageNewTagForger,
    Functor.map_map, OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_bind, PMF.bind_map,
    Function.comp_def]
  dsimp only [StateT.run, MACScheme.signingOracle]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  have hcongr : PMF.bind (ProbComp.eval (BitString.sampleList 1))
      (fun tag : List Bool =>
        PMF.pure (((List.replicate n false).length == n) &&
          !([List.replicate n false].contains (List.replicate n false)) &&
          ([!(tag.take 1).headD false].length == 1))) =
      PMF.bind (ProbComp.eval (BitString.sampleList 1)) (fun _ => PMF.pure false) := by
    refine PMF.bind_congr_on_support _ _ _ fun tag _ => ?_
    simp
  rw [hcongr, PMF.bind_const]

/-- In the strong fresh-pair `sufCmaGame`, `sameMessageNewTagForger` always wins (`PMF.pure true`)
because for every 1-bit tag `[b]` returned by the randomized signer, the output pair
`(0^n, [!b])` is valid and distinct from the recorded pair `(0^n, [b])`. -/
theorem eval_sufCmaGame_randomizedTagMACScheme_sameMessageNewTagForger (n : ℕ) :
    ProbComp.eval (randomizedTagMACScheme.sufCmaGame sameMessageNewTagForger n) =
      PMF.pure true := by
  simp only [MACScheme.sufCmaGame, randomizedTagMACScheme, sameMessageNewTagForger,
    Functor.map_map, OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
    ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_bind, PMF.bind_map,
    Function.comp_def]
  dsimp only [StateT.run, MACScheme.signingPairOracle]
  simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind]
  have hcongr : PMF.bind (ProbComp.eval (BitString.sampleList 1))
      (fun tag : List Bool =>
        PMF.pure (((List.replicate n false).length == n) &&
          !([(List.replicate n false, tag)].contains
            (List.replicate n false, [!(tag.take 1).headD false])) &&
          ([!(tag.take 1).headD false].length == 1))) =
      PMF.bind (ProbComp.eval (BitString.sampleList 1)) (fun _ => PMF.pure true) := by
    refine PMF.bind_congr_on_support _ _ _ fun tag htag => ?_
    rw [BitString.eval_sampleList] at htag
    have hlen : tag.length = 1 := BitString.length_of_mem_support_uniformList htag
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hlen
    cases b <;> simp
  rw [hcongr, PMF.bind_const]

/-- On `sameMessageNewTagForger`, the EUF-CMA success probability is `0` while the SUF-CMA success
probability is `1`, strictly separating the two freshness predicates. -/
theorem succProbability_eufCma_lt_sufCma_sameMessageNewTagForger (n : ℕ) :
    Game.succProbability
        (ProbComp.eval (randomizedTagMACScheme.eufCmaGame sameMessageNewTagForger n)) <
      Game.succProbability
        (ProbComp.eval (randomizedTagMACScheme.sufCmaGame sameMessageNewTagForger n)) := by
  rw [eval_eufCmaGame_randomizedTagMACScheme_sameMessageNewTagForger,
    eval_sufCmaGame_randomizedTagMACScheme_sameMessageNewTagForger]
  simp [Game.succProbability]

/-! ### Schedule reindexing (`MACScheme.reindex`) -/

/-- Doubling schedule `2 * n` is computable in plain polynomial time in unary. -/
theorem computableInPolyTime_double :
    ComputableInPolyTime (fun n : ℕ => 2 * n) encUnary encUnary := by
  polytime

/-- Doubling schedule `2 * n` is strictly monotone on `ℕ`. -/
theorem strictMono_double : StrictMono (fun n : ℕ => 2 * n) :=
  fun _ _ h => Nat.mul_lt_mul_of_pos_left h (by decide)

/-- Reindexed `echoPrfMAC` authenticating `2 * n`-bit messages at parameter `n`. -/
noncomputable def doubleEchoPrfMAC : MACScheme :=
  echoPrfMAC.reindex (fun n => 2 * n) computableInPolyTime_double

example : doubleEchoPrfMAC.msgLen 3 = 6 := rfl

example : doubleEchoPrfMAC.verify [false, true] [true, false] [true, false] = true := by
  decide

example : GeneratorReindex.parameter (fun k => 2 * k) 10 = 5 := by
  simpa using GeneratorReindex.parameter_apply_of_strictMono strictMono_double 5

example {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family) :
    ((prfMAC family hprf.polyTime).reindex (fun n => 2 * n) computableInPolyTime_double).SUFCMA :=
  hprf.sufCma_prfMAC.reindex computableInPolyTime_double strictMono_double

end ComplexityTests.Crypto.MAC
