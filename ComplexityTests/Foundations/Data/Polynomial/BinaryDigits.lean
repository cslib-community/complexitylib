/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Polynomial.BinaryDigits
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Polynomial

/-!
# Checks for binary-digit polynomial encoding and exact recovery
-/

public section

namespace Polynomial.BinaryDigitsTests

example : (binaryDigits 13).coeff 0 = 1 ∧ (binaryDigits 13).coeff 1 = 0 ∧
    (binaryDigits 13).coeff 2 = 1 ∧ (binaryDigits 13).coeff 3 = 1 := by
  simp only [binaryDigits, coeff_ofCoeffList]
  decide

example : (binaryDigits 0).eval 2 = 0 ∧ (binaryDigits 13).eval 2 = 13 := by simp

example : (binaryDigits 13).eval 1 ≤ 4 ∧ (binaryDigits 13).natDegree ≤ 3 :=
  ⟨eval_one_binaryDigits_le 13, natDegree_binaryDigits_le 13⟩

-- The recovered coefficients need not themselves be bits.
example : evalCoeffList 2 [9, 5, 7, 3] = 71 := by decide

example (p : ℕ[X]) (hdeg : p.natDegree < 4) (hsize : p.eval 1 < 32) :
    ofCoeffList ((List.range 4).map fun i => p.coeff i % 32) = p :=
  ofCoeffList_coeffsBelow_mod hdeg hsize

open Turing.MultiTapeTM in
example : ComputableInPolyTime (evalCoeffList 2) (encList encNat) encNat :=
  ComputableInPolyTime.evalCoeffList_two

end Polynomial.BinaryDigitsTests
