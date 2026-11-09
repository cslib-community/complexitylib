/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Signature.RandomOracle
import CslibFrontier.Crypto.Protocols.SigmaProtocol.FiatShamir
import CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrIdentification
import CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrSignature
import CslibFrontierTests.Crypto.FiatShamir
import CslibFrontierTests.Crypto.Signature

/-!
# Tests for the typed ROMSignature ↔ computational SignatureScheme bridge

Verifies the `Interactive.World` execution core and final-message admissibility companions in
`CslibFrontier.Crypto.Protocols.Signature.RandomOracle`, and instantiates the computational bridge
`CslibFrontier.Crypto.Computational.Signature.RandomOracle` on:
- `trivialSignatureScheme` (`SignatureScheme`),
- `idLamportScheme` (`SignatureScheme`),
- `trivialWordSignatureScheme` (`WordSignatureScheme`),
- `schnorrROMScheme` (`ROMSignature.Scheme` over `ZMod 11`).
-/

namespace CslibFrontierTests.ROMSignature

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols
open Cslib.Crypto.Protocols.ROMSignature Cslib.Crypto.Protocols.SigmaProtocol
open Turing.MultiTapeTM CslibFrontierTests.Crypto.Signature
open scoped NNReal

/-! ## Final-message freshness vs pairwise `Nodup` -/

-- Repeated signing queries on the same message falsify `FreshOutputs` even for a fresh forgery,
-- while `FreshOutputsOnFinalMessage` depends only on `msg ∉ queried`.
example : ¬ FreshOutputs [false, false] true := by
  decide

example : FreshOutputsOnFinalMessage [false, false] true := by
  decide

-- Replaying a queried message is rejected by both freshness predicates.
example : ¬ FreshOutputsOnFinalMessage [false, true] false := by
  decide

/-! ## Bridge instantiation 1: `trivialSignatureScheme` -/

-- `trivialSignatureScheme.toROMSignatureScheme n` satisfies `CorrectOn` on `n`-bit messages.
example (n : ℕ) :
    (trivialSignatureScheme.toROMSignatureScheme n).CorrectOn (fun msg => msg.length = n) :=
  trivialSignatureScheme.correctOn_toROMSignatureScheme n

-- A zero-query `n`-bit forgery wins with probability `1` in both `eufCmaGame` and `romEufCmaGame`.
noncomputable def zeroQueryForger : Forger :=
  fun n _ => ProbOracleComp.sample (pure (List.replicate n false, []))

example (n : ℕ) :
    trivialSignatureScheme.romEufCmaGame zeroQueryForger n = pure true := by
  rw [← trivialSignatureScheme.eval_eufCmaGame_eq_romEufCmaGame]
  simp [SignatureScheme.eufCmaGame, trivialSignatureScheme, zeroQueryForger]

-- A wrong-length forgery (`[]` at security parameter `n + 1`) is rejected by the
-- `msg.length == n` guard in `romEufCmaGame`.
noncomputable def emptyMsgForger : Forger :=
  fun _ _ => ProbOracleComp.sample (pure ([], []))

example (n : ℕ) :
    trivialSignatureScheme.romEufCmaGame emptyMsgForger (n + 1) = pure false := by
  rw [← trivialSignatureScheme.eval_eufCmaGame_eq_romEufCmaGame]
  simp [SignatureScheme.eufCmaGame, trivialSignatureScheme, emptyMsgForger]

-- Querying the signing oracle on `[]` and forging on `[false]` at `n = 1` succeeds in both
-- `eufCmaGame` and `romEufCmaGame`.
noncomputable def queryEmptyThenForge : Forger :=
  fun _ _ => do
    let _ ← ProbOracleComp.query ((), ([] : List Bool))
    return ([false], [])

example :
    trivialSignatureScheme.romEufCmaGame queryEmptyThenForge 1 = pure true := by
  have h : trivialSignatureScheme.eufCmaGame queryEmptyThenForge 1 = pure true := rfl
  rw [← trivialSignatureScheme.eval_eufCmaGame_eq_romEufCmaGame, h]
  rfl

-- Querying `[true]` and replaying `[true]` as the final forgery at `n = 1` is rejected by
-- final-message freshness `!(pairs.map Prod.fst).contains msg`.
noncomputable def replayQueriedForger : Forger :=
  fun _ _ => do
    let sig ← ProbOracleComp.query ((), [true])
    return ([true], sig)

example :
    trivialSignatureScheme.romEufCmaGame replayQueriedForger 1 = pure false := by
  have h : trivialSignatureScheme.eufCmaGame replayQueriedForger 1 = pure false := rfl
  rw [← trivialSignatureScheme.eval_eufCmaGame_eq_romEufCmaGame, h]
  rfl

/-! ## Bridge instantiation 2: `idLamportScheme` -/

-- `idLamportScheme.toROMSignatureScheme n` satisfies `CorrectOn` on `n`-bit messages and has
-- the exact same game distribution as `idLamportScheme.eufCmaGame`.
example (n : ℕ) :
    (idLamportScheme.toROMSignatureScheme n).CorrectOn (fun msg => msg.length = n) :=
  idLamportScheme.correctOn_toROMSignatureScheme n

example (adversary : Forger) (n : ℕ) :
    ProbComp.eval (idLamportScheme.eufCmaGame adversary n) =
      idLamportScheme.romEufCmaGame adversary n :=
  idLamportScheme.eval_eufCmaGame_eq_romEufCmaGame adversary n

-- On `idLamportScheme` at `n = 0`, the empty-message forgery `([], encList encBits [])` is
-- accepted (`pure true`), while a wrong-length 1-bit forgery `([false], [])` is rejected
-- (`pure false`).
example :
    idLamportScheme.romEufCmaGame
      (fun _ _ => ProbOracleComp.sample (pure ([], encList encBits []))) 0 = pure true := by
  rw [← idLamportScheme.eval_eufCmaGame_eq_romEufCmaGame]
  simp [SignatureScheme.eufCmaGame, idLamportScheme, lamportScheme, lamportKeyGen, lamportVerify]

example :
    idLamportScheme.romEufCmaGame
      (fun _ _ => ProbOracleComp.sample (pure ([false], []))) 0 = pure false := by
  have h :
      idLamportScheme.eufCmaGame
        (fun _ _ => ProbOracleComp.sample (pure ([false], []))) 0 = pure false := rfl
  rw [← idLamportScheme.eval_eufCmaGame_eq_romEufCmaGame, h]
  rfl

/-! ## Bridge instantiation 3: `WordSignatureScheme` -/

/-- Trivial unrestricted-length word signature scheme. -/
noncomputable def trivialWordSignatureScheme : WordSignatureScheme where
  keyGen _ := pure ([], [])
  sign _ msg := pure msg
  verify _ _ _ := true
  keyGen_ppt := by ppt
  sign_ppt := by ppt
  verify_polyTime := by polytime
  verify_sign := by
    intro _ _ _ _ _ _ _
    rfl

-- `WordSignatureScheme.toROMSignatureScheme` satisfies unrestricted `ROMSignature.Scheme.Correct`.
example (n : ℕ) : (trivialWordSignatureScheme.toROMSignatureScheme n).Correct :=
  trivialWordSignatureScheme.correct_toROMSignatureScheme n

-- Without the `n`-bit length restriction, `emptyMsgForger` wins `WordSignatureScheme.romEufCmaGame`
-- with probability `1` at every `n + 1`.
example (n : ℕ) :
    trivialWordSignatureScheme.romEufCmaGame emptyMsgForger (n + 1) = pure true := by
  rw [← trivialWordSignatureScheme.eval_eufCmaGame_eq_romEufCmaGame]
  simp [WordSignatureScheme.eufCmaGame, trivialWordSignatureScheme, emptyMsgForger]

/-! ## Bridge instantiation 4: `schnorrROMScheme` (`ZMod 11`) -/

open CslibFrontierTests.Crypto.FiatShamir

/-- `schnorrROMScheme` on `Bool` messages in `ZMod 11` with base `2` equals the Fiat–Shamir
transform of `schnorr`. -/
example :
    schnorrROMScheme (M := Bool) ι (2 : ZMod 11) =
      CslibFrontierTests.Crypto.FiatShamir.scheme := rfl

-- `schnorrROMScheme_correct` establishes unrestricted `ROMSignature.Scheme.Correct`.
example : (schnorrROMScheme (M := Bool) ι (2 : ZMod 11)).Correct :=
  schnorrROMScheme_correct (M := Bool) ι (2 : ZMod 11)

-- `schnorrROMScheme` also satisfies `CorrectOn` on every message predicate via `Correct.correctOn`.
example : (schnorrROMScheme (M := Bool) ι (2 : ZMod 11)).CorrectOn (fun b => b = true) :=
  (schnorrROMScheme_correct (M := Bool) ι (2 : ZMod 11)).correctOn _

-- `eufCmaGame` and `eufCmaFinalMsgGame` on `schnorrROMScheme` factor through `worldGame`, and the
-- knowing forger succeeds with probability `1` in both.
example :
    Game.succProbability
      (eufCmaGame (schnorrROMScheme (M := Bool) ι (2 : ZMod 11)) knower) = 1 :=
  succProbability_knower

example :
    Game.succProbability
      (eufCmaFinalMsgGame (fun _ => true) (schnorrROMScheme (M := Bool) ι (2 : ZMod 11)) knower) =
      1 := by
  rw [eufCmaFinalMsgGame_true]
  exact succProbability_knower

example :
    (eufCmaFinalMsgGame (fun b => b) (schnorrROMScheme (M := Bool) ι (2 : ZMod 11)) knower) true ≤
      (eufCmaGame (schnorrROMScheme (M := Bool) ι (2 : ZMod 11)) knower) true :=
  eufCmaFinalMsgGame_apply_true_le (fun b => b)
    (schnorrROMScheme (M := Bool) ι (2 : ZMod 11)) knower

end CslibFrontierTests.ROMSignature
