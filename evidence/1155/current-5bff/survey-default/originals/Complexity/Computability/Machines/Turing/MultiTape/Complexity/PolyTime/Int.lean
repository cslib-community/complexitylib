/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Mathlib.Logic.Equiv.Nat

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# Polynomial-time operations on signed unary integers

Operations on Christian Reitwiessner's `encInt`: the sign bit is followed by `n` unary bits for
`Int.ofNat n` or `Int.negSucc n`. In the negative case the magnitude is `n + 1`. Natural inputs
and outputs use `encUnary`, so these rules support polynomially bounded tape positions and their
indices in a computation tableau.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natCast`, `.int_negSucc`:
  constructing signed integers from unary naturals.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_natCast_sub`:
  the signed difference of unary naturals.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_succ`, `.int_pred`, `.int_pos`, `.int_neg`:
  unit shifts and sign tests.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_toNat`, `.int_natAbs`, `.int_equivNat`:
  nonnegative truncation, absolute value and the standard numbering of integers, in unary.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_sub_sign`, `.int_abs_le_nat`:
  fixed tape moves and membership in a unary-bounded window.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.int_abs_le_nat'`:
  window membership for computed positions and bounds.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Interpret a unary natural as a nonnegative signed integer. -/
@[fun_prop]
theorem int_natCast : ComputableTidilyInPolyTime (fun n : ℕ => (n : ℤ)) encUnary encInt :=
  (const (encMid := encBool) false).append (id' (encIn := encUnary)) fun _ => rfl

/-- Construct `-(n + 1)` from a unary natural `n`. -/
@[fun_prop]
theorem int_negSucc : ComputableTidilyInPolyTime Int.negSucc encUnary encInt :=
  .of_linear (.of_cons_true fun _ => rfl)

/-- Subtract unary naturals without truncating at zero. -/
@[fun_prop]
theorem int_natCast_sub :
    ComputableTidilyInPolyTime (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)
      (encPair encUnary encUnary) encInt := by
  have hle := unary_le.comp ((snd encUnary encUnary).prod (fst encUnary encUnary))
  have hpos : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => ((p.1 - p.2 : ℕ) : ℤ))
      (encPair encUnary encUnary) encInt := by fun_prop
  have hneg : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => Int.negSucc (p.2 - p.1 - 1))
      (encPair encUnary encUnary) encInt := by fun_prop
  have heq (p : ℕ × ℕ) :
      (p.1 : ℤ) - p.2 = if decide (p.2 ≤ p.1) then ((p.1 - p.2 : ℕ) : ℤ)
        else Int.negSucc (p.2 - p.1 - 1) := by
    split_ifs with hp <;> simp_all only [decide_eq_true_eq] <;> lia
  simpa only [Function.comp_def, ← heq] using hle.ite' hpos hneg

/-- Shift a signed unary integer one cell to the right. -/
@[fun_prop]
theorem int_succ : ComputableTidilyInPolyTime (fun z : ℤ => z + 1) encInt encInt :=
  ComputableTidilyInDegree.int_succ.computableTidilyInPolyTime

/-- Shift a signed unary integer one cell to the left. -/
@[fun_prop]
theorem int_pred : ComputableTidilyInPolyTime (fun z : ℤ => z - 1) encInt encInt :=
  ComputableTidilyInDegree.int_pred.computableTidilyInPolyTime

/-- Test whether a signed unary integer is positive. -/
@[fun_prop]
theorem int_pos : ComputableTidilyInPolyTime (fun z : ℤ => decide (0 < z)) encInt encBool :=
  ComputableTidilyInDegree.int_pos.computableTidilyInPolyTime

/-- Test whether a signed unary integer is negative. -/
@[fun_prop]
theorem int_neg : ComputableTidilyInPolyTime (fun z : ℤ => decide (z < 0)) encInt encBool :=
  ComputableTidilyInDegree.int_neg.computableTidilyInPolyTime

private def intTail : ℤ → ℕ
  | .ofNat n => n
  | .negSucc n => n

private theorem int_tail : ComputableTidilyInPolyTime intTail encInt encUnary :=
  .of_linear (.of_tail fun z => by cases z <;> rfl)

/-- Truncate a signed integer at zero and return the result in unary. -/
@[fun_prop]
theorem int_toNat : ComputableTidilyInPolyTime Int.toNat encInt encUnary := by
  have h := int_neg.ite' (const 0) int_tail
  convert h using 1
  funext z
  cases z <;> simp [intTail]

/-- Return the magnitude in unary, accounting for the offset in negative encodings. -/
@[fun_prop]
theorem int_natAbs : ComputableTidilyInPolyTime Int.natAbs encInt encUnary := by
  have h := int_neg.ite' (unary_add.comp (int_tail.prod (const 1))) int_tail
  convert h using 1
  funext z
  cases z <;> simp [intTail]

/-- Subtract a fixed tape direction from a signed unary position. -/
@[fun_prop]
theorem int_sub_sign (direction : SignType) :
    ComputableTidilyInPolyTime (fun z : ℤ => z - (direction : ℤ)) encInt encInt := by
  cases direction <;> simp only [SignType.cast, sub_neg_eq_add, sub_zero] <;> fun_prop

/-- Compare a signed unary position's magnitude with a unary window bound. -/
@[fun_prop]
theorem int_abs_le_nat :
    ComputableTidilyInPolyTime (fun p : ℤ × ℕ => decide (|p.1| ≤ (p.2 : ℤ)))
      (encPair encInt encUnary) encBool := by
  simpa only [← Int.natCast_natAbs, Int.ofNat_le, Function.comp_def] using
    unary_le.comp ((int_natAbs.comp (fst encInt encUnary)).prod (snd encInt encUnary))

/-- Test window membership after computing the signed position and unary bound. -/
@[fun_prop]
theorem int_abs_le_nat' {α : Type} {input : α ↪ List Bool} {position : α → ℤ} {bound : α → ℕ}
    (hposition : ComputableTidilyInPolyTime position input encInt)
    (hbound : ComputableTidilyInPolyTime bound input encUnary) :
    ComputableTidilyInPolyTime (fun a => decide (|position a| ≤ (bound a : ℤ)))
      input encBool :=
  int_abs_le_nat.comp (hposition.prod hbound)

/-- Number signed integers by `0, -1, 1, -2, …`, returning the index in unary. -/
@[fun_prop]
theorem int_equivNat : ComputableTidilyInPolyTime Equiv.intEquivNat encInt encUnary := by
  have hpos := unary_mul.comp ((const 2).prod int_tail)
  have h := int_neg.ite' (unary_add.comp (hpos.prod (const 1))) hpos
  convert h using 1
  funext z
  cases z with
  | ofNat n => rfl
  | negSucc n => simp [intTail, Equiv.intEquivNat, Equiv.intEquivNatSumNat]

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
