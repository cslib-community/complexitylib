/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.SchnorrSignature.WordROM
import Complexity.Crypto.Computational.DiscreteLog.SchnorrGroup
import Mathlib.Tactic.NormNum.Prime

/-!
# Canonical word Schnorr ROM regressions

The order-11 group modulo 23 checks actual word verification, including scalar aliases and
malformed commitment rejection. A forger queries two distinct junk words, a canonical point and a
repeated junk word, with the full finite-query theorem applied to its checked budget.
-/

noncomputable section

namespace ComplexityTests.Crypto.SchnorrWordROM

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols SigmaProtocol ROMSignature
open Turing.MultiTapeTM
open scoped NNReal

private def d23 : SchnorrGroup.Desc :=
  ⟨(23, 11, 2), ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩⟩

local instance : AddCommGroup (schnorrGroups.Carrier d23) := schnorrGroups.addCommGroup d23
local instance : Module (ZMod (schnorrGroups.order d23)) (schnorrGroups.Carrier d23) :=
  schnorrGroups.module d23
local instance : DecidableEq (schnorrGroups.Carrier d23) :=
  schnorrGroups.instDecidableEqCarrier d23
local instance : NeZero (schnorrGroups.order d23) := ⟨by decide⟩

private theorem challenge_bound : 2 ^ 3 ≤ schnorrGroups.order d23 := by decide

private def c5 : BitString 3 := ![true, false, true]
private def c6 : BitString 3 := ![false, true, true]

-- Scalars are interpreted modulo 11: response 20 is accepted wherever canonical response 9 is.
private theorem accepts5 : (schnorrGroups.schnorrWordSigma d23 challenge_bound).Accepts
    ((3 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23)
    (Nat.bits 9) c5 (Nat.bits 20) := by decide

-- The same literal commitment with a different challenge supports extraction, even with aliases.
private theorem accepts6 : (schnorrGroups.schnorrWordSigma d23 challenge_bound).Accepts
    ((3 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23)
    (Nat.bits 9) c6 (Nat.bits 12) := by decide

example : schnorrGroups.schnorrWordExtract d23 challenge_bound
    ((3 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23)
    (Nat.bits 9) c5 (Nat.bits 20)
      c6 (Nat.bits 12) = (3 : ZMod (schnorrGroups.order d23)) := by
  apply schnorrGroups.smul_generator_injective d23
  exact schnorrGroups.schnorrWordSigma_specialSoundness d23 challenge_bound
    _ _ _ _ _ _ (by decide : c5 ≠ c6) accepts5 accepts6

-- A commitment alias is rejected by the very same native verifier used by this instance.
example : ¬ (schnorrGroups.schnorrWordSigma d23 challenge_bound).Accepts
    ((3 : ZMod (schnorrGroups.order d23)) • schnorrGroups.generator d23)
    (Nat.bits 32) c5 (Nat.bits 20) := by decide

example : (schnorrGroups.schnorrWordROMScheme d23 challenge_bound).Correct :=
  schnorrGroups.schnorrWordROMScheme_correct d23 challenge_bound

example : (schnorrGroups.schnorrWordSigma d23 challenge_bound).SpecialHVZK
    (fun x u => x • schnorrGroups.generator d23 = u)
    (schnorrGroups.schnorrWordSimulate d23 challenge_bound) :=
  schnorrGroups.schnorrWordSigma_specialHVZK d23 challenge_bound

-- With no challenge bits, distinct challenges cannot occur; completeness still holds.
example : (schnorrGroups.schnorrWordROMScheme d23 (m := 0) (by decide)).Correct :=
  schnorrGroups.schnorrWordROMScheme_correct d23 (by decide)

-- These two raw words are both outside the hash-point encoding image.
example (msg t : List Bool) : encPair encBits encBits (msg, t) ≠ [] := by
  have h := length_encPair (enc₁ := encBits) (enc₂ := encBits) (msg, t)
  intro he
  rw [he] at h
  simp only [List.length_nil] at h
  omega

example (msg t : List Bool) : encPair encBits encBits (msg, t) ≠ [true] := by
  cases msg with
  | nil => simp [encPair_apply, encBits, frame]
  | cons b msg =>
    have h := length_encPair (enc₁ := encBits) (enc₂ := encBits) (b :: msg, t)
    intro he
    rw [he] at h
    simp only [encBits_apply, List.length_cons, List.length_nil] at h
    omega

private def queries :
    OracleComp (ForgerSpec (List Bool) (List Bool) (List Bool × List Bool) (BitString 3))
      (BitString 3 × BitString 3 × BitString 3 × BitString 3) := do
  let first ← OracleComp.query (.inr [])
  let canonical ← OracleComp.query (.inr (encPair encBits encBits ([], Nat.bits 9)))
  let other ← OracleComp.query (.inr [true])
  let repeated ← OracleComp.query (.inr [])
  return (first, canonical, other, repeated)

-- Four calls retain three separate cache keys, with no default-key collapse for junk words.
example :
    OracleComp.runWithAnswers c5
      ((OracleComp.interpret (FiatShamir.reductionHandler (encPair encBits encBits))
        queries).run ⟨[], [], 0, []⟩) [c5, c6, c6] =
      (((c5, c6, c6, c5),
        ⟨[([true], c6, some 2), (encPair encBits encBits ([], Nat.bits 9), c6, some 1),
          ([], c5, some 0)], [], 3, []⟩),
        [[], encPair encBits encBits ([], Nat.bits 9), [true]]) := by rfl

private noncomputable def forger :
    Forger (schnorrGroups.Carrier d23) (List Bool) (List Bool × List Bool)
      (List Bool) (BitString 3) where
  Coins := Unit
  coins := PMF.pure ()
  forge _ _ := do
    let _ ← queries
    return ([], (Nat.bits 9, Nat.bits 20))

private theorem forger_bound : forger.CallBounded 0 4 := by
  intro _ _
  constructor
  · exact .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ =>
      .liftBind _ _ 0 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0
  · exact .liftBind _ _ 3 fun _ => .liftBind _ _ 2 fun _ =>
      .liftBind _ _ 1 fun _ => .liftBind _ _ 0 fun _ => .pure _ 0

-- The theorem is instantiated with actual word outputs and unrestricted raw hash queries.
example :
    (Game.succProbability (eufCmaGame
      (schnorrGroups.schnorrWordROMScheme d23 challenge_bound) forger) : ℝ) ≤
      0 * (0 + 4) / 11 + (4 + 1) / 2 ^ 3 +
        √((4 + 1) * Game.succProbability
          (oneWayGame (schnorrKeyGen (schnorrGroups.generator d23))
            (fun α u => α • schnorrGroups.generator d23 = u)
            (schnorrGroups.schnorrWordROMSchemeReduction d23 challenge_bound forger 0 4))) := by
  simpa only [show schnorrGroups.order d23 = 11 from rfl, Nat.cast_zero, Nat.cast_ofNat] using
    schnorrGroups.succProbability_eufCmaGame_schnorrWordROMScheme_le
      d23 challenge_bound forger forger_bound

end ComplexityTests.Crypto.SchnorrWordROM
