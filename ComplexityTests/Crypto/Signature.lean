/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.OneWayToSignature
import Complexity.Crypto.Computational.Signature

/-!
# Tests for digital signature schemes, Lamport's one-time signature scheme, and OWF reductions

Provides concrete instantiations of `SignatureScheme` (both a trivial scheme and `lamportScheme`
applied to the identity function), and verifies that `OneTimeEUFCMA` and `EUFCMA` reject the
trivial scheme via an explicit zero-query PPT forger.
-/

namespace ComplexityTests.Crypto.Signature

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

/-- Concrete trivial signature scheme where every signature is accepted. Used to witness that the
`SignatureScheme` fields are jointly satisfiable and to verify that `OneTimeEUFCMA` and `EUFCMA`
reject insecure schemes. -/
noncomputable def trivialSignatureScheme : SignatureScheme where
  keyGen _ := pure ([], [])
  sign _ msg := pure msg
  verify _ _ _ := true
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ _ _ _ _
    rfl

/-- Concrete instantiation of `lamportScheme` on the identity function. -/
noncomputable def idLamportScheme : SignatureScheme :=
  lamportScheme (fun x => x) .id'

-- Ordinary certificates construct the actual scheme and reduction, with no public raw premise.
example : idLamportScheme.verify = lamportVerify id := rfl

example :
    IsPPT encBits
      (lamportInverter id .id'
        (fun n _ => ProbOracleComp.sample (pure (List.replicate n false, [])))) := by
  refine isPPT_lamportInverter .id' ?_
  have hpair : ComputableInPolyTime
      (fun p : ℕ × List Bool => (List.replicate p.1 false, ([] : List Bool)))
      (encPair encUnary encBits) (encPair encBits encBits) := by polytime
  exact hpair.isPPTOn.isOraclePPTOn.isOraclePPT

-- Each message bit selects the corresponding secret from its pair.
example : lamportSign (encList encBits
      [[false, false], [false, true], [true, false], [true, true]]) [false, true] =
    pure (encList encBits [[false, false], [true, true]]) := by
  simp only [lamportSign, frames_encList]
  rfl

-- A valid signature is accepted, but reusing it for a different message is rejected.
example : lamportVerify id (encList encBits
      [[false, false], [false, true], [true, false], [true, true]]) [false, true]
      (encList encBits [[false, false], [true, true]]) = true := by
  simp only [lamportVerify, frames_encList]
  decide

example : lamportVerify id (encList encBits
      [[false, false], [false, true], [true, false], [true, true]]) [true, false]
      (encList encBits [[false, false], [true, true]]) = false := by
  simp only [lamportVerify, frames_encList]
  decide

-- A wrong-length first query returns no Lamport secret but still consumes the one query.
example : idLamportScheme.oneTimeSigningOracle
      (encList encBits [[false], [true]]) ((), []) [] = pure ([], [[]]) := by
  simp only [SignatureScheme.oneTimeSigningOracle, idLamportScheme, lamportScheme, lamportSign,
    frames_encList]
  rfl

example : idLamportScheme.oneTimeSigningOracle
      (encList encBits [[false], [true]]) ((), [true]) [[]] = pure ([], [[]]) := by
  rfl

-- Even an always-accepting verifier cannot bypass the game's n-bit message check.
example (n : ℕ) : trivialSignatureScheme.eufOneTimeGame
      (fun _ _ => ProbOracleComp.sample (pure ([], []))) (n + 1) = pure false := by
  simp [SignatureScheme.eufOneTimeGame, trivialSignatureScheme]

/-- The trivial signature scheme is not one-time EUF-CMA secure: a zero-query PPT forger that
outputs `(0^n, [])` succeeds with probability `1`. -/
theorem not_oneTimeEUFCMA_trivialSignatureScheme :
    ¬ trivialSignatureScheme.OneTimeEUFCMA := by
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
        (ProbComp.eval (trivialSignatureScheme.eufOneTimeGame forger n)) = 1 := by
    simp [SignatureScheme.eufOneTimeGame, trivialSignatureScheme, forger, Game.succProbability]
  simp only [heval] at hneg
  exact not_negligible_const one_ne_zero hneg

/-- The trivial signature scheme is not EUF-CMA secure. -/
theorem not_eufCMA_trivialSignatureScheme :
    ¬ trivialSignatureScheme.EUFCMA :=
  fun h => not_oneTimeEUFCMA_trivialSignatureScheme h.oneTimeEUFCMA

end ComplexityTests.Crypto.Signature
