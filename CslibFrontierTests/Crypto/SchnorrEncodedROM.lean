/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SchnorrSignature.EncodedROM
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import Mathlib.Tactic.NormNum.Prime

/-!
# Encoded signatures, total decoding and shared freshness

The identity key accepts a missing outer frame terminator. A word forger makes repeated signing
requests and distinct/repeated junk hash queries; the representation bridge retains its budgets,
signature-dependent output, cache and message log.
-/

noncomputable section

namespace ComplexityTests.Crypto.SchnorrEncodedROM

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols SigmaProtocol ROMSignature
open Turing.MultiTapeTM OracleComp

private def d23 : schnorrGroups.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

local instance : AddCommGroup (schnorrGroups.Carrier d23) := schnorrGroups.addCommGroup d23
local instance : Module (ZMod (schnorrGroups.order d23)) (schnorrGroups.Carrier d23) :=
  schnorrGroups.module d23
local instance : NeZero (schnorrGroups.order d23) := ⟨by decide⟩

private theorem challenge_bound : 2 ^ 3 ≤ schnorrGroups.order d23 := by decide

-- A malformed outer word can decode to a valid commitment and zero response.
example : (Decoder.bits.pair Decoder.bits).decode [true, true] = ([true], []) := by decide

example : ¬ ∃ p, encPair encBits encBits p = [true, true] := by
  rintro ⟨p, hp⟩
  have hfalse : false ∈ encPair encBits encBits p := by simp [encPair_apply, frame]
  rw [hp] at hfalse
  simp at hfalse

example : schnorrGroups.schnorrSigVerifyBits
    (d23, [true], [], (Decoder.bits.pair Decoder.bits).decode [true, true],
      [true, false, true]) = true := by decide

-- Total outer decoding does not weaken the existing canonical commitment check.
example : schnorrGroups.schnorrSigVerifyBits
    (d23, Nat.bits 8, [], (Nat.bits 32, Nat.bits 20), [true, false, true]) = false := by decide

private def forger (finalMsg : List Bool) :
    Forger (List Bool) (List Bool) (List Bool) (List Bool) (BitString 3) where
  Coins := Unit
  coins := PMF.pure ()
  forge _ _ := do
    let sig ← query (.inl [])
    let _ ← query (.inl [])
    let _ ← query (.inr [])
    let _ ← query (.inr [true])
    let _ ← query (.inr [])
    return (finalMsg, if sig == encPair encBits encBits ([true], []) then [true, true] else [true])

private theorem forger_bound (msg : List Bool) : (forger msg).CallBounded 2 3 := by
  intro _ _
  constructor
  · exact .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ =>
      .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0
  · exact .liftBind _ _ 3 fun _ => .liftBind _ _ 3 fun _ =>
      .liftBind _ _ 2 fun _ => .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0

example (msg : List Bool) :
    (schnorrGroups.schnorrDecodedForger d23 (forger msg)).CallBounded 2 3 :=
  schnorrGroups.callBounded_schnorrDecodedForger d23 (forger_bound msg)

-- The ideal game equality applies to this actual forger, including both output branches.
example (msg : List Bool) :
    eufCmaGame (schnorrGroups.schnorrEncodedROMScheme d23 3
      (schnorrGroups.schnorrIdealKeyGen d23)
      (PMF.uniformOfFintype (ZMod (schnorrGroups.order d23)))) (forger msg) =
      eufCmaGame (schnorrGroups.schnorrWordROMScheme d23 challenge_bound)
        (schnorrGroups.schnorrDecodedForger d23 (forger msg)) :=
  schnorrGroups.eufCmaGame_schnorrEncodedROMScheme_eq d23 challenge_bound (forger msg)

private def c5 : BitString 3 := ![true, false, true]
private def c6 : BitString 3 := ![false, true, true]

private def cache : List (List Bool × BitString 3) :=
  [(encPair encBits encBits ([], [true]), c5), ([], c5), ([true], c6)]

-- The ideal law also retains an already populated junk cache and nonempty signing log.
example (msg : List Bool) :
    runWith (handler (schnorrGroups.schnorrWordROMScheme d23 challenge_bound) (0, 0))
      ((schnorrGroups.schnorrDecodedForger d23 (forger msg)).forge 0 ()) (cache, [[]]) =
      (runWith (handler (schnorrGroups.schnorrEncodedROMScheme d23 3
        (schnorrGroups.schnorrIdealKeyGen d23)
        (PMF.uniformOfFintype (ZMod (schnorrGroups.order d23))))
        (schnorrGroups.encScalar d23 0))
        ((forger msg).forge (schnorrGroups.encode d23 0) ()) (cache, [[]])).map
          (Prod.map (Prod.map id (Decoder.bits.pair Decoder.bits).decode) id) :=
  schnorrGroups.runWith_schnorrDecodedForger d23 challenge_bound
    (schnorrGroups.schnorrIdealKeyGen d23) (forger msg) 0 0 0 () (cache, [[]])

private def fixture := schnorrGroups.schnorrEncodedROMScheme d23 3
  (PMF.pure ([true], [])) (PMF.pure 0)

private theorem cache_hit (word : List Bool) (value : BitString 3)
    (h : @List.lookup _ _ instBEqOfDecidableEq word cache = some value) :
    oracle (BitString 3) word cache = PMF.pure (value, cache) :=
  @memoize_of_some _ _ PMF _ instBEqOfDecidableEq _ _ _ value h

private theorem fixture_sign (log : List (List Bool)) :
    handler fixture [] (Sum.inl []) (cache, log) =
      PMF.pure (encPair encBits encBits ([true], []), (cache, [] :: log)) := by
  have hcommit : schnorrGroups.schnorrCommitBits (d23, []) = [true] := by decide
  have hscalar : schnorrGroups.encScalar d23 (0 : ZMod (schnorrGroups.order d23)) = [] := by
    decide
  simp only [handler, fixture, PrimeOrderGroupFamily.schnorrEncodedROMScheme,
    PMF.monad_bind_eq_bind, PMF.pure_bind]
  rw [interpret_map, interpret_query, StateT.run_map]
  simp only [hscalar, hcommit, StateT.run]
  rw [cache_hit (encPair encBits encBits ([], [true])) c5 (by decide)]
  simp [PrimeOrderGroupFamily.schnorrSignCoins, PrimeOrderGroupFamily.schnorrRespondBits,
    hcommit, ofBits]

private theorem fixture_hash_empty (log : List (List Bool)) :
    handler fixture [] (Sum.inr []) (cache, log) = PMF.pure (c5, (cache, log)) := by
  simp only [handler]
  rw [cache_hit [] c5 (by decide)]
  simp

private theorem fixture_hash_one (log : List (List Bool)) :
    handler fixture [] (Sum.inr [true]) (cache, log) = PMF.pure (c6, (cache, log)) := by
  simp only [handler]
  rw [cache_hit [true] c6 (by decide)]
  simp

-- This fixture uses the actual encoded arithmetic with explicit deterministic laws.
private theorem run_forger (msg : List Bool) :
    runWith (handler fixture []) ((forger msg).forge [true] ()) (cache, []) =
      PMF.pure ((msg, [true, true]), (cache, [[], []])) := by
  simp [forger, fixture_sign, fixture_hash_empty, fixture_hash_one]

-- The repeated signing log permits a fresh final message and rejects a signed final message.
example : (runWith (handler fixture []) ((forger [true]).forge [true] ()) (cache, [])).map
    (fun out => !(out.2.2.contains out.1.1)) = PMF.pure true := by
  rw [run_forger]
  simp

example : (runWith (handler fixture []) ((forger []).forge [true] ()) (cache, [])).map
    (fun out => !(out.2.2.contains out.1.1)) = PMF.pure false := by
  rw [run_forger]
  simp

-- Real sampling stays explicit and differs from the ideal game specialization above.
example (n : ℕ) :
    (schnorrGroups.schnorrEncodedROMScheme d23 3
      (ProbComp.eval (schnorrGroups.schnorrSigKeyGen n d23))
      ((ProbComp.eval (schnorrGroups.sampleExp n d23)).map Nat.cast)).keyGen =
      ProbComp.eval (schnorrGroups.schnorrSigKeyGen n d23) := rfl

end ComplexityTests.Crypto.SchnorrEncodedROM
