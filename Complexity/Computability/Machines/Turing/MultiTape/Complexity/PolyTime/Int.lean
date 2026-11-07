/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Mathlib.Logic.Equiv.Nat

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearCodecPrimitives

/-!
# Polynomial-time operations on signed unary integers

Operations on Christian Reitwiessner's `encIntUnary`: the sign bit is followed by `n` unary bits for
`Int.ofNat n` or `Int.negSucc n`. In the negative case the magnitude is `n + 1`. Natural inputs
and outputs use `encUnary`, so these rules support polynomially bounded tape positions and their
indices in a computation tableau.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.int_natCast`, `.int_negSucc`:
  constructing signed integers from unary naturals.
* `Turing.MultiTapeTM.ComputableInPolyTime.int_natCast_sub`:
  the signed difference of unary naturals.
* `Turing.MultiTapeTM.ComputableInPolyTime.int_succ`, `.int_pred`, `.int_pos`, `.int_neg`:
  unit shifts and sign tests.
* `Turing.MultiTapeTM.ComputableInPolyTime.int_toNat`, `.int_natAbs`, `.int_equivNat`:
  nonnegative truncation, absolute value and the standard numbering of integers, in unary.
* `Turing.MultiTapeTM.ComputableInPolyTime.int_sub`: subtraction of signed unary integers.
* `Turing.MultiTapeTM.ComputableInPolyTime.int_sub_sign`, `.int_abs_le_nat`:
  fixed tape moves and membership in a unary-bounded window.
* `Turing.MultiTapeTM.ComputableInPolyTime.int_abs_le_nat'`:
  window membership for computed positions and bounds.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Interpret a unary natural as a nonnegative signed integer. -/
@[fun_prop]
theorem int_natCast : ComputableInPolyTime (fun n : ℕ => (n : ℤ)) encUnary encIntUnary :=
  (bitsCons (const false) (encoding_comp (id' (encIn := encUnary)))).of_enc_eq fun _ => rfl

/-- Construct `-(n + 1)` from a unary natural `n`. -/
@[fun_prop]
theorem int_negSucc : ComputableInPolyTime Int.negSucc encUnary encIntUnary :=
  (ComputableInDegree.of_cons_true fun _ => rfl).computableInPolyTime

/-- Subtract unary naturals without truncating at zero. -/
@[fun_prop]
theorem int_natCast_sub :
    ComputableInPolyTime (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)
      (encPair encUnary encUnary) encIntUnary := by
  have hle := unary_le.comp ((snd encUnary encUnary).prod (fst encUnary encUnary))
  have hpos : ComputableInPolyTime (fun p : ℕ × ℕ => ((p.1 - p.2 : ℕ) : ℤ))
      (encPair encUnary encUnary) encIntUnary := by fun_prop
  have hneg : ComputableInPolyTime (fun p : ℕ × ℕ => Int.negSucc (p.2 - p.1 - 1))
      (encPair encUnary encUnary) encIntUnary := by fun_prop
  have heq (p : ℕ × ℕ) :
      (p.1 : ℤ) - p.2 = if decide (p.2 ≤ p.1) then ((p.1 - p.2 : ℕ) : ℤ)
        else Int.negSucc (p.2 - p.1 - 1) := by
    split_ifs with hp <;> simp_all only [decide_eq_true_eq] <;> lia
  simpa only [Function.comp_def, ← heq] using hle.ite' hpos hneg

/-- Shift a signed unary integer one cell to the right. -/
@[fun_prop]
theorem int_succ : ComputableInPolyTime (fun z : ℤ => z + 1) encIntUnary encIntUnary :=
  ComputableInDegree.int_succ.computableInPolyTime

/-- Shift a signed unary integer one cell to the left. -/
@[fun_prop]
theorem int_pred : ComputableInPolyTime (fun z : ℤ => z - 1) encIntUnary encIntUnary :=
  ComputableInDegree.int_pred.computableInPolyTime

private theorem int_head :
    ComputableInPolyTime (fun z : ℤ => ((encIntUnary z).take 1).headD false) encIntUnary encBool :=
  (ComputableInDegree.of_take_one (encIn := encIntUnary) (encMid := encBool)
    (fun z => by cases z <;> rfl)).computableInPolyTime

private theorem int_tailEmpty :
    ComputableInPolyTime (fun z : ℤ => (encIntUnary z).tail.isEmpty) encIntUnary encBool :=
  (ListEncoding.isEmpty (enc₁ := encBool) (enc := encBits)).computableInPolyTime.comp
    (ComputableInDegree.of_tail (f := fun z : ℤ => (encIntUnary z).tail)
      (encMid := encBits) fun _ => rfl).computableInPolyTime

/-- Test whether a signed unary integer is positive. -/
@[fun_prop]
theorem int_pos : ComputableInPolyTime (fun z : ℤ => decide (0 < z)) encIntUnary encBool := by
  convert (of_finite (encIn := encPair encBool encBool) (encOut := encBool)
    (fun t : Bool × Bool => !t.1 && !t.2)).comp (int_head.prod int_tailEmpty) using 1
  funext z
  rcases z with (_ | n) | n <;> simp

/-- Test whether a signed unary integer is negative. -/
@[fun_prop]
theorem int_neg : ComputableInPolyTime (fun z : ℤ => decide (z < 0)) encIntUnary encBool := by
  convert int_head using 1
  funext z
  rcases z with n | n <;> simp

private def intTail : ℤ → ℕ
  | .ofNat n => n
  | .negSucc n => n

private theorem int_tail : ComputableInPolyTime intTail encIntUnary encUnary :=
  (ComputableInDegree.of_tail fun z => by cases z <;> rfl).computableInPolyTime

/-- Truncate a signed integer at zero and return the result in unary. -/
@[fun_prop]
theorem int_toNat : ComputableInPolyTime Int.toNat encIntUnary encUnary := by
  have h := int_neg.ite' (const 0) int_tail
  convert h using 1
  funext z
  cases z <;> simp [intTail]

/-- Return the magnitude in unary, accounting for the offset in negative encodings. -/
@[fun_prop]
theorem int_natAbs : ComputableInPolyTime Int.natAbs encIntUnary encUnary := by
  have h := int_neg.ite' (unary_add.comp (int_tail.prod (const 1))) int_tail
  convert h using 1
  funext z
  cases z <;> simp [intTail]

/-- The negative part of a signed unary integer, in unary. -/
private theorem int_neg_toNat :
    ComputableInPolyTime (fun z : ℤ => (-z).toNat) encIntUnary encUnary := by
  have h := int_neg.ite' int_natAbs (const 0)
  convert h using 1
  funext z
  split_ifs with hz <;> simp_all only [decide_eq_true_eq] <;> lia

/-- Subtract two signed unary integers. -/
@[fun_prop]
theorem int_sub : ComputableInPolyTime (fun p : ℤ × ℤ => p.1 - p.2)
    (encPair encIntUnary encIntUnary) encIntUnary := by
  have h := int_natCast_sub.comp
    ((unary_add.comp ((int_toNat.comp (fst encIntUnary encIntUnary)).prod
        (int_neg_toNat.comp (snd encIntUnary encIntUnary)))).prod
      (unary_add.comp ((int_toNat.comp (snd encIntUnary encIntUnary)).prod
        (int_neg_toNat.comp (fst encIntUnary encIntUnary)))))
  convert h using 1
  funext p
  simp only [Function.comp_apply]
  push_cast
  lia

/-- Subtract a fixed tape direction from a signed unary position. -/
@[fun_prop]
theorem int_sub_sign (direction : SignType) :
    ComputableInPolyTime (fun z : ℤ => z - (direction : ℤ)) encIntUnary encIntUnary := by
  cases direction <;> simp only [SignType.cast, sub_neg_eq_add, sub_zero] <;> fun_prop

/-- Compare a signed unary position's magnitude with a unary window bound. -/
@[fun_prop]
theorem int_abs_le_nat :
    ComputableInPolyTime (fun p : ℤ × ℕ => decide (|p.1| ≤ (p.2 : ℤ)))
      (encPair encIntUnary encUnary) encBool := by
  simpa only [← Int.natCast_natAbs, Int.ofNat_le, Function.comp_def] using
    unary_le.comp ((int_natAbs.comp (fst encIntUnary encUnary)).prod (snd encIntUnary encUnary))

/-- Test window membership after computing the signed position and unary bound. -/
@[fun_prop]
theorem int_abs_le_nat' {α : Type} {input : α ↪ List Bool} {position : α → ℤ} {bound : α → ℕ}
    (hposition : ComputableInPolyTime position input encIntUnary)
    (hbound : ComputableInPolyTime bound input encUnary) :
    ComputableInPolyTime (fun a => decide (|position a| ≤ (bound a : ℤ)))
      input encBool :=
  int_abs_le_nat.comp (hposition.prod hbound)

/-- Number signed integers by `0, -1, 1, -2, …`, returning the index in unary. -/
@[fun_prop]
theorem int_equivNat : ComputableInPolyTime Equiv.intEquivNat encIntUnary encUnary := by
  have hpos := unary_mul.comp ((const 2).prod int_tail)
  have h := int_neg.ite' (unary_add.comp (hpos.prod (const 1))) hpos
  convert h using 1
  funext z
  cases z with
  | ofNat n => rfl
  | negSucc n => simp [intTail, Equiv.intEquivNat, Equiv.intEquivNatSumNat]

end Turing.MultiTapeTM.ComputableInPolyTime
