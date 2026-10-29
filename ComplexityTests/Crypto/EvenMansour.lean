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

example :
    (Game.advantage (preWhitenKeyRecoveryRealGame (0 : ZMod 7))
        (preWhitenKeyRecoveryIdealGame (0 : ZMod 7)) : ℝ) =
      1 - (Fintype.card (ZMod 7) : ℝ)⁻¹ ∧
    (Game.advantage (postWhitenKeyRecoveryRealGame (0 : BitString 4))
        (postWhitenKeyRecoveryIdealGame (0 : BitString 4)) : ℝ) =
      1 - (Fintype.card (BitString 4) : ℝ)⁻¹ :=
  ⟨advantage_preWhitenKeyRecoveryGame_eq 0, advantage_postWhitenKeyRecoveryGame_eq 0⟩

example :
    ((PMF.uniformOfFintype (BitString 4 × BitString 4)).toOuterMeasure
      {k | isBadEvenMansourKey [(0, 0)] [(0, 0)] k = true}).toReal ≤
      2 * ([(0 : BitString 4 × BitString 4)].length : ℝ) *
        ([(0 : BitString 4 × BitString 4)].length : ℝ) / (Fintype.card (BitString 4) : ℝ) ∧
    ((PMF.uniformOfFintype (BitString 4)).toOuterMeasure
      {k | isBadSingleKeyEvenMansour [(0, 0)] [(0, 0)] k = true}).toReal ≤
      2 * ([(0 : BitString 4 × BitString 4)].length : ℝ) *
        ([(0 : BitString 4 × BitString 4)].length : ℝ) / (Fintype.card (BitString 4) : ℝ) :=
  ⟨toOuterMeasure_isBadEvenMansourKey_toReal_le [(0, 0)] [(0, 0)],
   toOuterMeasure_isBadSingleKeyEvenMansour_toReal_le [(0, 0)] [(0, 0)]⟩

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
    evenMansourIdealGame sampleTwoSidedDistinguisher =
      (((OracleComp.interpret idealLazyHandler sampleTwoSidedDistinguisher).run ([], [])).map
        Prod.fst : PMF Bool) ∧
    (PMF.uniformOfFintype (Equiv.Perm (ZMod 7))).bind
        (fun π => PMF.pure (evalEvenMansour π 3 5 sampleTwoSidedDistinguisher)) =
      (((OracleComp.interpret (realLazyHandler (3, 5)) sampleTwoSidedDistinguisher).run []).map
        Prod.fst : PMF Bool) ∧
    (Game.advantage (evenMansourRealGame sampleTwoSidedDistinguisher)
      (evenMansourIdealGame sampleTwoSidedDistinguisher) : ℝ) ≤
      2 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (Fintype.card (ZMod 7) : ℝ) ∧
    (Game.advantage (singleKeyEvenMansourRealGame sampleTwoSidedDistinguisher)
      (evenMansourIdealGame sampleTwoSidedDistinguisher) : ℝ) ≤
      2 * ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (Fintype.card (ZMod 7) : ℝ) :=
  ⟨evenMansourIdealGame_eq_lazy sampleTwoSidedDistinguisher,
   realGameForKey_eq_lazy (3, 5) sampleTwoSidedDistinguisher,
   advantage_evenMansourRealGame_evenMansourIdealGame_le isCallBounded_sampleTwoSidedDistinguisher,
   advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le
    isCallBounded_sampleTwoSidedDistinguisher⟩

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

end Cslib.Crypto.EvenMansour.Tests
