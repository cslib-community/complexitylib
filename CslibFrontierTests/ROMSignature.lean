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

Verifies the freshness predicates of `CslibFrontier.Crypto.Protocols.Signature.RandomOracle`, and
instantiates the typed bridge `Signature.Scheme.toROM`
(`CslibFrontier.Crypto.Computational.Signature.RandomOracle`) on the typed schemes of:
- `trivialSignatureScheme` (`SignatureScheme`),
- `idLamportScheme` (`SignatureScheme`),
- `trivialWordSignatureScheme` (`WordSignatureScheme`).

It also checks the random-oracle scheme `schnorrROMScheme` over `ZMod 11`.
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

/-- The random-oracle EUF-CMA experiment of the typed scheme of the word scheme `S` at `n`. -/
noncomputable abbrev romGame (S : SignatureScheme) (adversary : Forger) (n : ℕ) : PMF Bool :=
  worldGame (S.toScheme n).toROM (adversary.toTyped n).toROM
    (fun verified (⟨m, _⟩ : List Bool × List Bool) pairs =>
      verified && !(pairs.map Prod.fst).contains m)

-- `(trivialSignatureScheme.toScheme n).toROM` satisfies `CorrectOn` on `n`-bit messages.
example (n : ℕ) :
    (trivialSignatureScheme.toScheme n).toROM.CorrectOn (fun msg => msg.length = n) :=
  trivialSignatureScheme.correctOn_toROM n

-- A zero-query `n`-bit forgery wins with probability `1` in both `eufCmaGame` and `romGame`.
noncomputable def zeroQueryForger : Forger :=
  fun n _ => ProbOracleComp.sample (pure (List.replicate n false, []))

example (n : ℕ) : romGame trivialSignatureScheme zeroQueryForger n = pure true := by
  rw [romGame, ← trivialSignatureScheme.eufCmaGame_eq_worldGame_toROM]
  simp [SignatureScheme.eufCmaGame, trivialSignatureScheme, zeroQueryForger]

-- A wrong-length forgery (`[]` at security parameter `n + 1`) is rejected: the typed scheme
-- verifies only `n`-bit messages.
noncomputable def emptyMsgForger : Forger :=
  fun _ _ => ProbOracleComp.sample (pure ([], []))

example (n : ℕ) : romGame trivialSignatureScheme emptyMsgForger (n + 1) = pure false := by
  rw [romGame, ← trivialSignatureScheme.eufCmaGame_eq_worldGame_toROM]
  simp [SignatureScheme.eufCmaGame, trivialSignatureScheme, emptyMsgForger]

-- Querying the signing oracle on `[]` and forging on `[false]` at `n = 1` succeeds in both
-- `eufCmaGame` and `romGame`.
noncomputable def queryEmptyThenForge : Forger :=
  fun _ _ => do
    let _ ← ProbOracleComp.query ((), ([] : List Bool))
    return ([false], [])

example : romGame trivialSignatureScheme queryEmptyThenForge 1 = pure true := by
  have h : trivialSignatureScheme.eufCmaGame queryEmptyThenForge 1 = pure true := rfl
  rw [romGame, ← trivialSignatureScheme.eufCmaGame_eq_worldGame_toROM, h]
  rfl

-- Querying `[true]` and replaying `[true]` as the final forgery at `n = 1` is rejected by
-- final-message freshness `!(pairs.map Prod.fst).contains msg`.
noncomputable def replayQueriedForger : Forger :=
  fun _ _ => do
    let sig ← ProbOracleComp.query ((), [true])
    return ([true], sig)

example : romGame trivialSignatureScheme replayQueriedForger 1 = pure false := by
  have h : trivialSignatureScheme.eufCmaGame replayQueriedForger 1 = pure false := rfl
  rw [romGame, ← trivialSignatureScheme.eufCmaGame_eq_worldGame_toROM, h]
  rfl

/-! ## Bridge instantiation 2: `idLamportScheme` -/

-- `(idLamportScheme.toScheme n).toROM` satisfies `CorrectOn` on `n`-bit messages, and its
-- random-oracle experiment has the distribution of `idLamportScheme.eufCmaGame`.
example (n : ℕ) :
    (idLamportScheme.toScheme n).toROM.CorrectOn (fun msg => msg.length = n) :=
  idLamportScheme.correctOn_toROM n

example (adversary : Forger) (n : ℕ) :
    ProbComp.eval (idLamportScheme.eufCmaGame adversary n) = romGame idLamportScheme adversary n :=
  idLamportScheme.eufCmaGame_eq_worldGame_toROM adversary n

-- On `idLamportScheme` at `n = 0`, the empty-message forgery `([], encList encBits [])` is
-- accepted (`pure true`), while a wrong-length 1-bit forgery `([false], [])` is rejected
-- (`pure false`).
example :
    romGame idLamportScheme
      (fun _ _ => ProbOracleComp.sample (pure ([], encList encBits []))) 0 = pure true := by
  rw [romGame, ← idLamportScheme.eufCmaGame_eq_worldGame_toROM]
  simp [SignatureScheme.eufCmaGame, idLamportScheme, lamportScheme, lamportKeyGen, lamportVerify]

example :
    romGame idLamportScheme (fun _ _ => ProbOracleComp.sample (pure ([false], []))) 0 =
      pure false := by
  have h :
      idLamportScheme.eufCmaGame
        (fun _ _ => ProbOracleComp.sample (pure ([false], []))) 0 = pure false := rfl
  rw [romGame, ← idLamportScheme.eufCmaGame_eq_worldGame_toROM, h]
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

-- The typed scheme of a `WordSignatureScheme` is a correct random-oracle scheme on every message.
example (n : ℕ) : (trivialWordSignatureScheme.toScheme n).toROM.Correct :=
  trivialWordSignatureScheme.correct_toROM n

-- Without the `n`-bit length restriction, `emptyMsgForger` wins the random-oracle experiment of
-- `trivialWordSignatureScheme` with probability `1` at every `n + 1`.
example (n : ℕ) :
    worldGame (trivialWordSignatureScheme.toScheme (n + 1)).toROM
        (emptyMsgForger.toTyped (n + 1)).toROM
        (fun verified (⟨m, _⟩ : List Bool × List Bool) pairs =>
          verified && !(pairs.map Prod.fst).contains m) = pure true := by
  rw [← trivialWordSignatureScheme.eufCmaGame_eq_worldGame_toROM]
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

-- `eufCmaGame` on `schnorrROMScheme` factors through `worldGame`, and the knowing forger succeeds
-- with probability `1`.
example :
    Game.succProbability
      (eufCmaGame (schnorrROMScheme (M := Bool) ι (2 : ZMod 11)) knower) = 1 :=
  succProbability_knower

end CslibFrontierTests.ROMSignature
