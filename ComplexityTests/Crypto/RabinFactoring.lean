/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.RabinFactoring
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Rabin squaring and factoring equivalence
-/

namespace ComplexityTests.Crypto.RabinFactoring

open Cslib Cslib.Crypto

/-- Smallest Blum integer `N = 3 * 7 = 21` (`3 ≡ 3 [MOD 4]`, `7 ≡ 3 [MOD 4]`). -/
def blum21 : BlumDesc :=
  ⟨(3, 7), ⟨⟨by norm_num, by decide⟩, ⟨by norm_num, by decide⟩, by decide⟩⟩

example : blum21.modulus = 21 := rfl

example : rabinEval 21 2 = 4 := by decide

example : rabinEval 21 5 = 4 := by decide

example : rabinFactorPair (2 + 5) 21 = (7, 3) := by decide

/-- info: 'Cslib.Crypto.factoringHard_of_rabinOneWay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.factoringHard_of_rabinOneWay

/-- info: 'Cslib.Crypto.rabinOneWay_of_factoringHard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.rabinOneWay_of_factoringHard

end ComplexityTests.Crypto.RabinFactoring
