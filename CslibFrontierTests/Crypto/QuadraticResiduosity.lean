/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.QuadraticResiduosity
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for quadratic residuosity modulo `N = p * q`
-/

namespace ComplexityTests.Crypto.QuadraticResiduosity

open Cslib Cslib.Crypto

/-- Smallest odd-prime product `N = 3 * 5 = 15`. -/
def d15 : ModulusDesc where
  p := 3
  q := 5
  prime_p := by norm_num
  prime_q := by norm_num
  ne_pq := by decide
  two_lt_p := by decide
  two_lt_q := by decide

example : d15.p * d15.q = 15 := rfl

example :
    (ZMod.unitOfCoprime 4 (by decide) : (ZMod 15)ˣ) ∈ Subgroup.square (ZMod 15)ˣ := by
  rw [Subgroup.mem_square]
  exact ⟨ZMod.unitOfCoprime 2 (by decide), by decide⟩

example :
    letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    jacobiSymbol 3 5 (ZMod.unitOfCoprime 4 (by decide)) = 1 := by
  decide

example :
    letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    jacobiSymbol 3 5 (ZMod.unitOfCoprime 2 (by decide)) = 1 := by
  decide

example : jacobiSym 2 15 = 1 :=
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  (jacobiSymbol_eq_jacobiSym 3 5 (ZMod.unitOfCoprime 2 (by decide))).symm.trans (by decide)

/-- info: 'Cslib.Crypto.jacobiPosSet_eq_disjoint_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.jacobiPosSet_eq_disjoint_union

/--
info: 'Cslib.Crypto.card_quadResidueSet_eq_card_positiveNonresidues' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.Crypto.card_quadResidueSet_eq_card_positiveNonresidues

end ComplexityTests.Crypto.QuadraticResiduosity
