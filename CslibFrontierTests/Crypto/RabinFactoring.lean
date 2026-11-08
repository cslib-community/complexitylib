/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.RabinFactoring
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Rabin squaring and factoring equivalence
-/

namespace CslibFrontierTests.Crypto.RabinFactoring

open Cslib Cslib.Crypto

/-- Smallest Blum integer `N = 3 * 7 = 21` (`3 ≡ 3 [MOD 4]`, `7 ≡ 3 [MOD 4]`). -/
def blum21 : BlumDesc :=
  ⟨(3, 7), ⟨⟨by norm_num, by decide⟩, ⟨by norm_num, by decide⟩, by decide⟩⟩

example : blum21.modulus = 21 := rfl

example : rabinEval 21 2 = 4 := by decide

example : rabinEval 21 5 = 4 := by decide

example : rabinFactorPair (2 + 5) 21 = (7, 3) := by decide

example : crtSqrt (rabinEval 21 5) 3 7 ^ 2 % 21 = rabinEval 21 5 := by decide

noncomputable example (gen : BlumGen) (F : ℕ → ℕ → _) (n : ℕ) :
    Game.succProbability (factoringGame gen F n) ≤
      Game.succProbability (rabinInversionGame gen (factorToRabin F) n) :=
  succProbability_factoringGame_le gen F n

example (gen : BlumGen) (h : FactoringHard gen) : RabinOneWay gen :=
  (rabinOneWay_iff_factoringHard gen).mpr h

/-- info: 'Cslib.Crypto.factoringHard_of_rabinOneWay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.factoringHard_of_rabinOneWay

/-- info: 'Cslib.Crypto.rabinOneWay_of_factoringHard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.rabinOneWay_of_factoringHard

end CslibFrontierTests.Crypto.RabinFactoring
