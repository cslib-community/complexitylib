/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatPower

/-!
# Concrete tests for plain `ComputableInDegree` rules

Exercises `fun_prop` synthesis and explicit degree composition on `ComputableInDegree`,
checking that independent output-size degrees (`0` for Boolean outputs, `1` for linear
bit/unary/binary outputs) are preserved under quadratic/cubic computation degrees, together
with concrete input-output checks.
-/

public section

namespace ComplexityTests.InDegreePlain

open Turing.MultiTapeTM

/-- Reversing, dropping the last bit, and re-appending the extracted last bit reconstructs any
bit list, synthesized at `(d, e) = (1, 1)` by `fun_prop`. -/
def dropAppendLast (w : List Bool) : List Bool :=
  w.dropLast ++ w.getLast?.toList

theorem dropAppendLast_deg :
    ComputableInDegree dropAppendLast encBits encBits 1 1 := by
  unfold dropAppendLast
  fun_prop (disch := first | apply le_refl | lia)

example : dropAppendLast [] = [] := rfl
example : dropAppendLast [true, false, true] = [true, false, true] := rfl

/-- A quadratic-cost unary expression `(a - b) + min a b` retains linear output degree `e = 1`
under `fun_prop`. -/
def unaryRecon (p : ℕ × ℕ) : ℕ :=
  (p.1 - p.2) + min p.1 p.2

theorem unaryRecon_deg :
    ComputableInDegree unaryRecon (encPair encUnary encUnary) encUnary 2 1 := by
  unfold unaryRecon
  fun_prop (disch := first | apply le_refl | lia)

theorem unaryRecon_eq_fst (a b : ℕ) : unaryRecon (a, b) = a := by
  simp only [unaryRecon]
  omega

example : unaryRecon (7, 3) = 7 := rfl
example : unaryRecon (2, 9) = 2 := rfl

/-- Composing cubic binary multiplication with quadratic binary equality retains constant output
degree `e = 0` at cost degree `3`, without inflating output degree to the runtime degree. -/
def checkPythagorean (p : (ℕ × ℕ) × ℕ) : Bool :=
  decide (p.1.1 * p.1.1 + p.1.2 * p.1.2 = p.2 * p.2)

theorem checkPythagorean_deg :
    ComputableInDegree checkPythagorean
      (encPair (encPair encNat encNat) encNat) encBool 3 0 := by
  have hp := ComputableInDegree.fst (encPair encNat encNat) encNat
  have ha := hp.fst'
  have hb := hp.snd'
  have hc := ComputableInDegree.snd (encPair encNat encNat) encNat
  have ha2 := computableInDegree_mul.comp (ha.prod ha)
  have hb2 := computableInDegree_mul.comp (hb.prod hb)
  have hc2 := computableInDegree_mul.comp (hc.prod hc)
  have hsum := computableInDegree_add.comp (ha2.prod hb2)
  exact ((ComputableInDegree.eq encNat).comp (hsum.prod hc2)).mono

example : checkPythagorean ((3, 4), 5) = true := rfl
example : checkPythagorean ((3, 4), 6) = false := rfl

/-- Composing `two_pow_length` twice computes `2 ^ (|w| + 1)` in linear time and linear output
size, checked against concrete bit lengths. -/
def doubleTwoPow (w : List Bool) : ℕ :=
  2 ^ (encNat (2 ^ w.length)).length

theorem doubleTwoPow_deg :
    ComputableInDegree doubleTwoPow encBits encNat 1 1 :=
  ((ComputableInDegree.two_pow_length encNat).comp
    (ComputableInDegree.two_pow_length encBits)).mono

example : doubleTwoPow [false, true] = 8 := by
  dsimp only [doubleTwoPow, List.length_cons, List.length_nil]
  rw [encNat_two_pow]
  decide

example : (encNat (doubleTwoPow [false, true])).length = 4 := by
  dsimp only [doubleTwoPow, List.length_cons, List.length_nil]
  rw [encNat_two_pow, encNat_two_pow]
  decide

end ComplexityTests.InDegreePlain
