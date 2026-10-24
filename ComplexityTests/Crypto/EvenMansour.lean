/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.Cipher.EvenMansour
import Mathlib.Data.ZMod.Basic

/-!
# Tests for the Even–Mansour cipher in the ideal-permutation model

Exercises `Complexity/Crypto/Protocols/Cipher/EvenMansour.lean` on concrete finite groups
(`ZMod 7` and `BitString 4`) and audits the axiom footprint of its headline theorems.
-/

namespace Cslib.Crypto.EvenMansour.Tests

open Cslib.Crypto Cslib.Crypto.EvenMansour Cslib.OracleComp Cslib.Probability

/-! ### Concrete algebraic and attack checks over `ZMod 7` and `BitString 4` -/

/-- Sample permutation on `ZMod 7` used for concrete Even–Mansour checks. -/
def samplePermZMod7 : Equiv.Perm (ZMod 7) :=
  Equiv.swap (1 : ZMod 7) 4 * Equiv.addRight 2

example (x : ZMod 7) :
    (evenMansourEquiv samplePermZMod7 3 5).symm (evenMansourEquiv samplePermZMod7 3 5 x) = x := by
  decide +revert

example (x : ZMod 7) :
    (evenMansourEquiv samplePermZMod7 3 5).symm x =
      evenMansourEquiv samplePermZMod7.symm (-5) (-3) x := by
  decide +revert

example :
    evalTwoPerms (preWhitenEquiv samplePermZMod7 4) samplePermZMod7
      (preWhitenKeyRecoveryAttack (2 : ZMod 7)) = 4 := by
  decide

example :
    evalTwoPerms (postWhitenEquiv samplePermZMod7 6) samplePermZMod7
      (postWhitenKeyRecoveryAttack (2 : ZMod 7)) = 6 := by
  decide

example :
    isBadEvenMansourKey (G := ZMod 7) [(2, 5)] [(6, 1)] (4, 0) = true := by
  decide

example :
    isBadEvenMansourKey (G := ZMod 7) [(2, 5)] [(6, 1)] (1, 1) = false := by
  decide

private def samplePermBits4 : Equiv.Perm (BitString 4) :=
  Equiv.swap (Fin.repeat 2 ![true, false]) (Fin.repeat 2 ![false, true])

example :
    let k₀ : BitString 4 := Fin.repeat 2 ![true, false]
    let k₁ : BitString 4 := Fin.repeat 2 ![true, true]
    (evenMansourEquiv samplePermBits4 k₀ k₁).symm =
      evenMansourEquiv samplePermBits4.symm k₁ k₀ :=
  evenMansourEquiv_symm_bitString samplePermBits4 _ _

/-! ### Concrete theorem instantiations -/

example (x : ZMod 7) :
    (Game.advantage (preWhitenKeyRecoveryRealGame x) (preWhitenKeyRecoveryIdealGame x) : ℝ) =
      1 - (Fintype.card (ZMod 7) : ℝ)⁻¹ :=
  advantage_preWhitenKeyRecoveryGame_eq x

example (x : BitString 4) :
    (Game.advantage (postWhitenKeyRecoveryRealGame x) (postWhitenKeyRecoveryIdealGame x) : ℝ) =
      1 - (Fintype.card (BitString 4) : ℝ)⁻¹ :=
  advantage_postWhitenKeyRecoveryGame_eq x

example (T_e T_π : List (BitString 4 × BitString 4)) :
    ((PMF.uniformOfFintype (BitString 4 × BitString 4)).toOuterMeasure
      {k | isBadEvenMansourKey T_e T_π k = true}).toReal ≤
      2 * (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card (BitString 4) : ℝ) :=
  toOuterMeasure_isBadEvenMansourKey_toReal_le T_e T_π

example (T_e T_π : List (BitString 4 × BitString 4)) :
    ((PMF.uniformOfFintype (BitString 4)).toOuterMeasure
      {k | isBadSingleKeyEvenMansour T_e T_π k = true}).toReal ≤
      2 * (T_e.length : ℝ) * (T_π.length : ℝ) / (Fintype.card (BitString 4) : ℝ) :=
  toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le T_e T_π

example (program : OracleComp (EvenMansourSpec (BitString 4)) Bool) :
    evenMansourIdealGame program =
      (((OracleComp.interpret idealLazyHandler program).run ([], [])).map Prod.fst : PMF Bool) :=
  evenMansourIdealGame_eq_lazy program

example (k : BitString 4 × BitString 4)
    (program : OracleComp (EvenMansourSpec (BitString 4)) Bool) :
    (PMF.uniformOfFintype (Equiv.Perm (BitString 4))).bind
        (fun π => PMF.pure (evalEvenMansour π k.1 k.2 program)) =
      (((OracleComp.interpret (realLazyHandler k) program).run []).map Prod.fst : PMF Bool) :=
  realGameForKey_eq_lazy k program

/-- A concrete two-sided distinguisher making `1` cipher query and `1` primitive query on
`ZMod 7`. -/
def sampleTwoSidedDistinguisher : OracleComp (EvenMansourSpec (ZMod 7)) Bool := do
  let y ← queryCipherForward (0 : ZMod 7)
  let u ← queryPermInverse y
  return decide (u = 0)

theorem isCallBounded_sampleTwoSidedDistinguisher :
    IsCallBounded sampleTwoSidedDistinguisher 1 1 := by
  constructor
  · simpa [sampleTwoSidedDistinguisher] using
      (isCallBounded_queryCipherForward (0 : ZMod 7)).1.bind fun y =>
        (isCallBounded_queryPermInverse y).1.bind fun u => IsCostBounded.pure _ 0
  · simpa [sampleTwoSidedDistinguisher] using
      (isCallBounded_queryCipherForward (0 : ZMod 7)).2.bind fun y =>
        (isCallBounded_queryPermInverse y).2.bind fun u => IsCostBounded.pure _ 0

example :
    (Game.advantage (evenMansourRealGame sampleTwoSidedDistinguisher)
      (evenMansourIdealGame sampleTwoSidedDistinguisher) : ℝ) ≤
      2 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (Fintype.card (ZMod 7) : ℝ) :=
  advantage_evenMansourRealGame_evenMansourIdealGame_le isCallBounded_sampleTwoSidedDistinguisher

example :
    (Game.advantage (singleKeyEvenMansourRealGame sampleTwoSidedDistinguisher)
      (evenMansourIdealGame sampleTwoSidedDistinguisher) : ℝ) ≤
      2 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (Fintype.card (ZMod 7) : ℝ) :=
  advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le
    isCallBounded_sampleTwoSidedDistinguisher

/-! ### Axiom guards for headline results -/

/--
info: 'Cslib.Crypto.EvenMansour.evenMansourEquiv_symm' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms evenMansourEquiv_symm

/--
info: 'Cslib.Crypto.EvenMansour.evenMansourEquiv_symm_bitString' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms evenMansourEquiv_symm_bitString

/--
info: 'Cslib.Crypto.EvenMansour.map_prod_evenMansourEncrypt_uniformOfFintype' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms map_prod_evenMansourEncrypt_uniformOfFintype

/--
info: 'Cslib.Crypto.EvenMansour.advantage_preWhitenKeyRecoveryGame_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms advantage_preWhitenKeyRecoveryGame_eq

/--
info: 'Cslib.Crypto.EvenMansour.advantage_postWhitenKeyRecoveryGame_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms advantage_postWhitenKeyRecoveryGame_eq

/--
info: 'Cslib.Crypto.EvenMansour.advantage_evenMansourRealGame_liftLeft_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms advantage_evenMansourRealGame_liftLeft_eq_zero

/--
info: 'Cslib.Crypto.EvenMansour.advantage_evenMansourRealGame_liftRight_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms advantage_evenMansourRealGame_liftRight_eq_zero

/--
info: 'Cslib.Crypto.EvenMansour.disjoint_of_isBadEvenMansourKey_eq_false' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms disjoint_of_isBadEvenMansourKey_eq_false

/--
info: 'Cslib.Crypto.EvenMansour.isBadEvenMansourKey_eq_isBadInputKey_of_evenMansourEquiv' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms isBadEvenMansourKey_eq_isBadInputKey_of_evenMansourEquiv

/--
info: 'Cslib.Crypto.EvenMansour.toOuterMeasure_isBadEvenMansourKey_toReal_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toOuterMeasure_isBadEvenMansourKey_toReal_le

/--
info: 'Cslib.Crypto.EvenMansour.toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le

/--
info: 'Cslib.Crypto.EvenMansour.IsCallBounded.badEvenMansourKey_toReal_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms IsCallBounded.badEvenMansourKey_toReal_le

/--
info: 'Cslib.Crypto.EvenMansour.IsCallBounded.badSingleKeyEvenMansour_toReal_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms IsCallBounded.badSingleKeyEvenMansour_toReal_le

/--
info: 'Cslib.Crypto.EvenMansour.evenMansourIdealGame_eq_lazy' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evenMansourIdealGame_eq_lazy

/--
info: 'Cslib.Crypto.EvenMansour.realGameForKey_eq_lazy' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms realGameForKey_eq_lazy

/--
info: 'Cslib.Crypto.EvenMansour.run_idealLazyHandler_good_le_realLazyHandler' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms run_idealLazyHandler_good_le_realLazyHandler

/--
info: 'Cslib.Crypto.EvenMansour.advantage_evenMansourRealGame_evenMansourIdealGame_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms advantage_evenMansourRealGame_evenMansourIdealGame_le

/--
info: 'Cslib.Crypto.EvenMansour.advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le

end Cslib.Crypto.EvenMansour.Tests
