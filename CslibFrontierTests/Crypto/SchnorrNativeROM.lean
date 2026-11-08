/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SchnorrSignature.NativeROM
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import Mathlib.Tactic.NormNum.Prime

/-!
# Native sampled Schnorr ROM regressions

Check bounded reply prefixes, scalar and commitment aliases, total signature decoding, actual
stateful execution, and the separate nonce/key-generation sampling laws.
-/

noncomputable section

namespace ComplexityTests.Crypto.SchnorrNativeROM

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols SigmaProtocol ROMSignature
open Turing.MultiTapeTM
open scoped NNReal

private def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

private def fixedReply (answer : List Bool) :
    Unit × List Bool → StateT (List (List Bool)) PMF (List Bool) :=
  fun query log => PMF.pure (answer, query.2 :: log)

private theorem runVerify_fixed (F : PrimeOrderGroupFamily) (d : F.Desc) (m : ℕ)
    (pk msg sig answer : List Bool) (log : List (List Bool)) :
    ProbOracleComp.runWith (fixedReply answer) (F.schnorrROMVerify d m pk msg sig) log =
      PMF.pure (F.schnorrSigVerifyBits
        (d, pk, msg, (Decoder.bits.pair Decoder.bits).decode sig, answer.take m),
        encPair encBits encBits (msg, ((Decoder.bits.pair Decoder.bits).decode sig).1) :: log) := by
  simp [PrimeOrderGroupFamily.schnorrROMVerify, ProbOracleComp.runWith_map,
    ProbOracleComp.runWith_query, fixedReply, PMF.pure_map]

-- The native verifier reads only three bits; an overlong reply cannot change the challenge.
example : ProbOracleComp.runWith (fixedReply [true, false, true, true, true])
    (schnorrGroups.schnorrROMVerify d23 3 (Nat.bits 8) [true]
      (encPair encBits encBits (Nat.bits 9, Nat.bits 20))) [[]] =
      PMF.pure (true, [encPair encBits encBits ([true], Nat.bits 9), []]) := by
  rw [runVerify_fixed]
  congr 1

-- An empty reply is handled totally, as scalar zero; it is not an m-bit ideal-oracle claim.
example : ProbOracleComp.runWith (fixedReply [])
    (schnorrGroups.schnorrROMVerify d23 3 (Nat.bits 8) [true]
      (encPair encBits encBits (Nat.bits 9, Nat.bits 5))) [] =
      PMF.pure (true, [encPair encBits encBits ([true], Nat.bits 9)]) := by
  rw [runVerify_fixed]
  congr 1

-- Commitment aliases still fail through the actual oracle program.
example : ProbOracleComp.runWith (fixedReply [true, false, true])
    (schnorrGroups.schnorrROMVerify d23 3 (Nat.bits 8) [true]
      (encPair encBits encBits (Nat.bits 32, Nat.bits 20))) [] =
      PMF.pure (false, [encPair encBits encBits ([true], Nat.bits 32)]) := by
  rw [runVerify_fixed]
  congr 1

-- The existing total decoder determines the behavior of a malformed outer signature word.
example : (Decoder.bits.pair Decoder.bits).decode [true] = ([], []) := by decide

example : ProbOracleComp.runWith (fixedReply [true, false, true])
    (schnorrGroups.schnorrROMVerify d23 3 (Nat.bits 8) [true] [true]) [] =
      PMF.pure (false, [encPair encBits encBits ([true], [])]) := by
  rw [runVerify_fixed]
  congr 1

-- Private nonce randomness leaves external state alone; exactly one hash request is made.
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc) (m : ℕ) (sk msg answer : List Bool)
    (count : ℕ) :
    (ProbOracleComp.runWith (fun _ state => PMF.pure (answer, state + 1))
      (F.schnorrROMSign n d m sk msg) count).map Prod.snd = PMF.pure (count + 1) := by
  simp [PrimeOrderGroupFamily.schnorrROMSign, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_sample, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
    PMF.bind_map, PMF.map_bind, PMF.pure_map, PMF.bind_const]

private def c5 : BitString 3 := ![true, false, true]
private def c6 : BitString 3 := ![false, true, true]

private def cache : List (List Bool × BitString 3) :=
  [([], c6), (encPair encBits encBits ([true], Nat.bits 9), c5), ([true], c6)]

-- A cache hit uses its original answer and preserves both distinct junk entries and their order.
example : ProbOracleComp.runWith
    (fun (q : Unit × List Bool) st =>
      (oracle (BitString 3) q.2 st).map (Prod.map List.ofFn id))
    (schnorrGroups.schnorrROMVerify d23 3 (Nat.bits 8) [true]
      (encPair encBits encBits (Nat.bits 9, Nat.bits 20))) cache =
      PMF.pure (true, cache) := by
  simp only [PrimeOrderGroupFamily.schnorrROMVerify, ProbOracleComp.runWith_bind,
    ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
    Decoder.decode_enc]
  have hcache : oracle (BitString 3) (encPair encBits encBits ([true], Nat.bits 9)) cache =
      PMF.pure (c5, cache) := by
    unfold oracle
    exact @memoize_of_some _ _ PMF _ instBEqOfDecidableEq _ _ _ c5 (by decide)
  rw [hcache]
  simp only [PMF.pure_map, PMF.pure_bind]
  rfl

-- Actual m-bit cached answers are sufficient; the whole cache remains in the comparison.
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc) {m : ℕ} (hm : 2 ^ m ≤ F.order d)
    (x : ZMod (F.order d)) (u : F.Carrier d) (msg : List Bool)
    (cache : List (List Bool × BitString m)) :
    CloseTo
      (((F.schnorrWordROMScheme d hm).signCoins (x, u) msg).bind fun coins =>
        (OracleComp.runWith (oracle (BitString m))
          ((F.schnorrWordROMScheme d hm).sign (x, u) msg coins) cache).map
            (Prod.map (encPair encBits encBits) id))
      (ProbOracleComp.runWith (fun (q : Unit × List Bool) st =>
        (oracle (BitString m) q.2 st).map (Prod.map List.ofFn id))
        (F.schnorrROMSign n d m (F.encScalar d x) msg) cache) (1 / 2 ^ n : ℝ≥0) :=
  F.closeTo_runWith_schnorrROMSign d hm (oracle (BitString m)) n x u msg cache

-- Key generation pays its own error; the signing theorem does not assert exact native keys.
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc) :
    CloseTo (F.schnorrIdealKeyGen d) (ProbComp.eval (F.schnorrSigKeyGen n d))
      (1 / 2 ^ n : ℝ≥0) := F.closeTo_schnorrSigKeyGen n d

end ComplexityTests.Crypto.SchnorrNativeROM
