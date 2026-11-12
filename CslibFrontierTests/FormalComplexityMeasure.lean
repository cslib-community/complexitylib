/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: candidate

import CslibFrontier.Computability.Circuit.Boolean.FormalComplexityMeasure

/-! # Clients of formal complexity measures

A truth-table evaluation gives an asymmetric measure. These examples exercise arbitrary internal
negations, the exact finite density conclusion, zero inputs, and the constants convention.
-/


open Cslib Cslib.Circuits Cslib.Circuits.Boolean

private def atZero (n : ℕ) : FormalComplexityMeasure n where
  measure f := if f (fun _ => false) then 1 else 0
  input_le _ := by simp
  not_input_le _ := by simp
  and_le f g := by
    dsimp
    by_cases hf : f (fun _ => false) = true <;>
      by_cases hg : g (fun _ => false) = true <;> simp_all
  or_le f g := by
    dsimp
    by_cases hf : f (fun _ => false) = true <;>
      by_cases hg : g (fun _ => false) = true <;> simp_all

-- The axioms permit different measures for a function and its complement.
example : (atZero 1).measure (fun _ => false) = 0 ∧
    (atZero 1).measure (fun _ => true) = 1 := by decide

private def sample : Formula signature 2 :=
  ((Formula.input 0).and (Formula.input 1)).not

example : sample.IsConstantFree := by trivial

example : (atZero 2).measure (sample.eval interpretation) = 1 ∧ sample.leafSize = 2 := by
  decide

example : (atZero 2).measure (sample.eval interpretation) ≤ sample.leafSize :=
  (atZero 2).le_leafSize (by trivial) (fun _ => rfl)

-- The uniform space includes both truth tables even when there are no input bits.
example : Fintype.card (BooleanFunction 0) = 2 := by decide

example : Fintype.card (BooleanFunction 0) ≤
    4 * (Finset.univ.filter fun g : BooleanFunction 0 =>
      1 ≤ 4 * (atZero 0).measure g).card :=
  (atZero 0).card_le_four_mul_card (fun _ => true) (by decide)

-- Dropping the constant-free hypothesis would make the leaf bound false.
example : ¬ (Formula.const true : Formula signature 0).IsConstantFree := by
  simp [Formula.const, Formula.IsConstantFree]

example : (atZero 0).measure (fun _ => true) >
    (Formula.const true : Formula signature 0).leafSize := by decide
