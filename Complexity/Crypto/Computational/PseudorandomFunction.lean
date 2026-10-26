/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Probabilistic.Oracle.Parameter
public import Complexity.Crypto.Game
public import Complexity.Foundations.Data.BitString.List
public import Complexity.Languages.Probabilistic.BitString
public import Complexity.Languages.Probabilistic.RandomOracle
import Complexity.Languages.Probabilistic.RandomOracle.Probabilistic

/-!
# Uniform computational pseudorandom functions

Keys, valid queries and answers have length `n`. An adversary receives the unary security
parameter, independent private randomness and adaptive access to one word channel. The real game
samples one key; the ideal game samples one whole function and reuses it across calls. Both games
invoke the adversary with empty auxiliary input and reject malformed queries with the empty word.
The table is a semantic specification; `RandomOracle` certifies a lazy realization of the same
law for oracle-PPT adversaries.

The keyed evaluator has a uniform deterministic TM certificate on the encoded key/query pair.
Admissible adversaries satisfy `IsOraclePPT`, charging ordinary computation and request writing,
with one machine and polynomial for all parameters and auxiliary inputs.

## Main definitions

* `Cslib.Crypto.OracleDistinguisher`: a parameterized randomized adaptive oracle test.
* `Cslib.Crypto.prfRealGame`, `.prfIdealGame`: the keyed and random-function experiments.
* `Cslib.Crypto.PseudorandomFunction`: efficient evaluation, length and adaptive security.

## Main results

* `Cslib.Crypto.interpret_randomFunctionQuery`: correctness of the finite-domain adapter.
* `Cslib.Crypto.prfIdealGame_eq_lazy`: an exact lazy implementation of the ideal experiment.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 4.
* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986].

Adapted from Crypto/Computational/PseudorandomFunction.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared typed interpreter and word channel.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- An adaptive test with a unary parameter, an auxiliary word and one external word channel. -/
abbrev OracleDistinguisher := ℕ → List Bool → WordOracleComp Unit Bool

/-- A keyed oracle rejects queries outside the declared domain. -/
def prfOracle (family : List Bool → List Bool → List Bool) (n : ℕ) (key query : List Bool) :
    List Bool := if query.length = n then family key query else []

/-- Read a fixed random table, rejecting malformed words before interpreting their bits. -/
def randomFunctionOracle (n : ℕ) (table : BitString n → BitString n) (query : List Bool) :
    List Bool := if query.length = n then List.ofFn (table (BitString.ofList n query)) else []

/-- Adapt a valid word to the finite domain. Malformed words make no external call. -/
def randomFunctionQuery (n : ℕ) (query : List Bool) :
    ProbOracleComp (fun _ : BitString n => BitString n) (List Bool) :=
  if query.length = n then List.ofFn <$> ProbOracleComp.query (BitString.ofList n query)
  else pure []

/-- The finite query adapter preserves the word-valued table interface in every lawful monad. -/
theorem interpret_randomFunctionQuery {m : Type → Type*} [Monad m] [LawfulMonad m]
    (random : (n : ℕ) → m (Fin (n + 1))) (n : ℕ) (table : BitString n → BitString n)
    (query : List Bool) :
    OracleComp.interpret (ProbOracleComp.handler random (fun bits => pure (table bits)))
      (randomFunctionQuery n query) = pure (randomFunctionOracle n table query) := by
  by_cases h : query.length = n <;> simp [randomFunctionQuery, randomFunctionOracle, h]

open Classical in
/-- A semantic random-function cache, retaining only the finite-domain answers already used. -/
noncomputable def lazyRandomFunctionOracle (n : ℕ) (query : List Bool) :
    StateT (RandomOracle.Cache (fun _ : BitString n => BitString n)) PMF (List Bool) :=
  OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
      (RandomOracle.answer (fun _ => PMF.uniformOfFintype (BitString n))))
        (randomFunctionQuery n query)

/-- Sample one key and reuse it across every adaptive call. -/
noncomputable def prfRealGame (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let key ← BitString.sampleList n
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifFin (fun request =>
      pure (prfOracle family n key request.2))) (adversary n [])

/-- Sample one whole random function, independently of the adversary's private samples. -/
noncomputable def prfIdealGame (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let table ← ProbComp.uniform (BitString n → BitString n)
  OracleComp.interpret
    (ProbOracleComp.handler ProbComp.unifFin (fun request =>
      pure (randomFunctionOracle n table request.2))) (adversary n [])

/-- The ideal game admits consistent lazy answers to adaptive queries, with private randomness
independent of the table and the same rejection convention for malformed inputs. -/
theorem prfIdealGame_eq_lazy (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfIdealGame adversary n) =
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun request => lazyRandomFunctionOracle n request.2)) (adversary n [])).run
            (fun _ => none)).map Prod.fst := by
  classical
  let adapted := OracleComp.interpret
    (ProbOracleComp.handler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (fun request : Unit × List Bool => randomFunctionQuery n request.2)) (adversary n [])
  have h := RandomOracle.uniform_interpret_prob_eq_lazy adapted
  have heager (table : BitString n → BitString n) (query : List Bool) :
      OracleComp.interpret
        (ProbOracleComp.handler ProbComp.unifOracle (fun bits => PMF.pure (table bits)))
          (randomFunctionQuery n query) = PMF.pure (randomFunctionOracle n table query) :=
    interpret_randomFunctionQuery ProbComp.unifOracle n table query
  simpa only [adapted, prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform,
    ProbOracleComp.eval_interpret, ProbComp.eval_pure, OracleComp.interpret_interpret,
    ProbOracleComp.interpret_handler, ProbOracleComp.interpret_sample, ProbComp.unifFin,
    OracleComp.interpret_query, heager, lazyRandomFunctionOracle, PMF.monad_bind_eq_bind] using h

/-- A keyed family evaluated in plain polynomial time, secure against every uniform adaptive
oracle test. -/
structure PseudorandomFunction (family : List Bool → List Bool → List Bool) : Prop where
  /-- One deterministic machine evaluates the family from the encoded key and query. -/
  polyTime : ComputableInPolyTime (fun pair => family pair.1 pair.2)
    (encPair encBits encBits) encBits
  /-- Valid queries receive answers of the declared width. -/
  length_eq : ∀ key query, query.length = key.length → (family key query).length = key.length
  /-- The real and ideal experiments use the common game-security calculus. -/
  secure : Game.Indistinguishable
    (fun adversary n => ProbComp.eval (prfRealGame family adversary n))
    (fun adversary n => ProbComp.eval (prfIdealGame adversary n)) (IsOraclePPT encBool)

end Cslib.Crypto
