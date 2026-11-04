/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.BinaryDigits
import Mathlib.Data.Fintype.BigOperators

/-!
# Weighted CSP recovery through binary digits
-/

public section

namespace Cslib.Logic.PL.CSP.BinaryDigitsTests

open Polynomial

/-- One unary constraint, so the two local weights are simply added. -/
@[expose] def oneVariable : CSP Unit ℕ := [((), [0])]

/-- Unequal four-bit and three-bit weights on the two assignments. -/
@[expose] def localWeight (_ : Unit) (w : List Bool) : ℕ := if w.headD false then 13 else 5

private theorem weight_bits :
    ∀ c ∈ oneVariable, ∀ w : List Bool, w.length = c.2.length →
      (localWeight c.1 w).size ≤ 4 := by
  intro c hc w hw
  unfold localWeight
  split <;> decide

example : oneVariable.partitionFunction localWeight = 18 := by decide

example : oneVariable.binaryDegreeBound (fun _ => 4) = 3 ∧
    oneVariable.binaryPrecision (fun _ => 4) = 5 := by decide

example : (oneVariable.binaryPartitionPolynomial localWeight).eval 2 = 18 := by
  rw [eval_two_binaryPartitionPolynomial]
  decide

-- Only four coefficients modulo 32 are needed although one weight already has four bits.
example : evalCoeffList 2 ((List.range 4).map fun i =>
    (oneVariable.binaryPartitionPolynomial localWeight).coeff i % 32) = 18 := by
  calc _ = oneVariable.partitionFunction localWeight :=
      evalCoeffList_binaryPartitionPolynomial_residues (b := fun _ => 4) weight_bits
    _ = 18 := by decide

-- Empty CSPs retain their multiplicative empty-product value over arbitrary semirings.
example : partitionFunction (fun (_ : Unit) (_ : List Bool) => (1 : ℕ[X]))
    ([] : CSP Unit ℕ) = 1 := by
  rw [partitionFunction]
  change (∑ _ : ((vars ([] : CSP Unit ℕ)).toFinset → Bool), (1 : ℕ[X])) = 1
  rw [Finset.sum_const, Finset.card_univ]
  have h : Fintype.card ((vars ([] : CSP Unit ℕ)).toFinset → Bool) = 1 := by decide
  rw [h, one_nsmul]

end Cslib.Logic.PL.CSP.BinaryDigitsTests
