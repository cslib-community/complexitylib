/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Languages.Probabilistic.Oracle.Codec
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.RandomOracle
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic

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

* `Cslib.Crypto.wordOracle_bitString_pure`: a fixed table read through `OracleCodec.bitString` is
  `randomFunctionOracle`, so the ideal game is a finite-domain experiment of the adapted adversary.
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

/-- A fixed table on `n`-bit strings presents `randomFunctionOracle` on the word channel. -/
theorem wordOracle_bitString_pure {m : Type → Type*} [Monad m] [LawfulMonad m] (n : ℕ)
    (table : BitString n → BitString n) :
    (OracleCodec.bitString n).wordOracle (fun x => (pure (table x) : m (BitString n))) =
      fun request => pure (randomFunctionOracle n table request.2) := by
  funext ⟨⟨⟩, query⟩
  by_cases h : query.length = n
  · simp [OracleCodec.wordOracle_bitString_of_length_eq _ h, randomFunctionOracle, h]
  · simp [OracleCodec.wordOracle_bitString_of_length_ne _ h, randomFunctionOracle, h]

open Classical in
/-- A semantic random-function cache, retaining only the finite-domain answers already used. -/
noncomputable def lazyRandomFunctionOracle (n : ℕ) (query : List Bool) :
    StateT (RandomOracle.Cache (fun _ : BitString n => BitString n)) PMF (List Bool) :=
  (OracleCodec.bitString n).wordOracle
    (RandomOracle.answer (fun _ => PMF.uniformOfFintype (BitString n))) ((), query)

/-- Sample one key and reuse it across every adaptive call. -/
noncomputable def prfRealGame (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let key ← BitString.sampleList n
  (adversary n []).run fun request => pure (prfOracle family n key request.2)

/-- Sample one whole random function, independently of the adversary's private samples. -/
noncomputable def prfIdealGame (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let table ← ProbComp.uniform (BitString n → BitString n)
  (adversary n []).run fun request => pure (randomFunctionOracle n table request.2)

/-- The ideal game admits consistent lazy answers to adaptive queries, with private randomness
independent of the table and the same rejection convention for malformed inputs. -/
theorem prfIdealGame_eq_lazy (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfIdealGame adversary n) =
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun request => lazyRandomFunctionOracle n request.2)) (adversary n [])).run
            (fun _ => none)).map Prod.fst := by
  classical
  have h := RandomOracle.uniform_interpret_prob_eq_lazy
    ((OracleCodec.bitString n).adapt (adversary n []))
  have heager (table : BitString n → BitString n) :
      (OracleCodec.bitString n).wordOracle (fun x => PMF.pure (table x)) =
        fun request => PMF.pure (randomFunctionOracle n table request.2) :=
    wordOracle_bitString_pure n table
  simp only [OracleCodec.interpret_adapt, heager, ProbOracleComp.runWith,
    OracleComp.runWith] at h
  simpa only [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform, ProbOracleComp.eval_run,
    ProbComp.eval_pure, lazyRandomFunctionOracle, PMF.monad_bind_eq_bind] using h

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
