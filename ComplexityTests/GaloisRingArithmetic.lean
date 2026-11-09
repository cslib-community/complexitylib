/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PolyTime.GaloisRingArithmetic

/-! # Arithmetic in `(ℤ / 2 ^ p)[U] / (f)` on coefficient lists

Concrete products in the Galois ring `(ℤ / 8)[U] / (U ^ 2 + U + 1)` (`p = 3`, `fl = [1, 1]`), the
correctness statements, and the polynomial-time certificates in closed form, with the precision
in unary and the coordinates in binary. -/

namespace ComplexityTests.GaloisRingArithmetic

open Cslib.GaloisRingArith Turing.MultiTapeTM

-- `U * U = U ^ 2 = -1 - U`, that is `7 + 7 U` modulo `8`.
example : mulX 3 [1, 1] [0, 1] = [7, 7] := by decide

-- `(1 + 2 U) (3 + U) = 3 + 7 U + 2 U ^ 2 = 1 + 5 U` modulo `8` and `U ^ 2 + U + 1`.
example : mul 3 [1, 1] [1, 2] [3, 1] = [1, 5] := by decide

-- Addition reduces each coordinate: `(7 + 5 U) + (3 + 6 U) = 2 + 3 U` modulo `8`.
example : add 3 [1, 1] [7, 5] [3, 6] = [2, 3] := by decide

-- `U` has order `3` here: `U ^ 3 = 1`.
example : mul 3 [1, 1] [0, 1] (mul 3 [1, 1] [0, 1] [0, 1]) = [1, 0] := by decide

-- Unreduced inputs are reduced: missing coordinates are zero, extra ones ignored.
example : mul 3 [1, 1] [9] [3, 1, 4] = [3, 1] := by decide

-- Degree three, `f = U ^ 3 + U + 1`, modulo `16`: `U ^ 2 * U = U ^ 3 = -1 - U`.
example : mulX 4 [1, 1, 0] [0, 0, 1] = [15, 15, 0] := by decide

-- The unit, and `U ^ 3 = 1` as a power.
example : one [1, 1] = [1, 0] ∧ pow 3 [1, 1] [0, 1] 3 = [1, 0] := by decide

-- `(1 + U) ^ 2 = 1 + 2 U + U ^ 2 = U`.
example : pow 3 [1, 1] [1, 1] 2 = [0, 1] := by decide

/-- Powers are correct. -/
example (c : List ℕ) (k : ℕ) : val 3 [1, 1] (pow 3 [1, 1] c k) = val 3 [1, 1] c ^ k :=
  val_pow c k

-- Inversion of units: `U⁻¹ = U ^ 2 = 7 + 7 U`, and `(1 + 2 U)⁻¹`, `(3 + 5 U)⁻¹` are inverses.
example : inv 3 [1, 1] [0, 1] = [7, 7] := by decide
example : mul 3 [1, 1] [1, 2] (inv 3 [1, 1] [1, 2]) = [1, 0] := by decide
example : mul 3 [1, 1] [3, 5] (inv 3 [1, 1] [3, 5]) = [1, 0] := by decide

-- `2` is not a unit, and inversion does not invert it.
example : mul 3 [1, 1] [2, 0] (inv 3 [1, 1] [2, 0]) ≠ [1, 0] := by decide

/-- Inversion is correct when the seed inverts modulo `2`. -/
example (x : List ℕ) {w : Ring 3 [1, 1]}
    (h : val 3 [1, 1] x * val 3 [1, 1] x ^ (2 ^ 2 - 2) = 1 + 2 * w) :
    val 3 [1, 1] x * val 3 [1, 1] (inv 3 [1, 1] x) = 1 :=
  val_mul_inv x h

/-- The defining polynomial is monic. -/
example : (monicOf [1, 1]).Monic := monic_monicOf _

/-- Multiplication is correct in the ring itself. -/
example (c d : List ℕ) : val 3 [1, 1] (mul 3 [1, 1] c d) = val 3 [1, 1] c * val 3 [1, 1] d :=
  val_mul c d

/-- **Multiplication in polynomial time**, on the ring description `(p, fl)` with `p` in unary
and the two coefficient lists in binary. -/
example : ComputableInPolyTime
    (fun q : (ℕ × List ℕ) × (List ℕ × List ℕ) => mul q.1.1 q.1.2 q.2.1 q.2.2)
    (encPair (encPair encUnary (encList encNat)) (encPair (encList encNat) (encList encNat)))
    (encList encNat) := by
  fun_prop

/-- **Addition in polynomial time**, in the same encoding. -/
example : ComputableInPolyTime
    (fun q : (ℕ × List ℕ) × (List ℕ × List ℕ) => add q.1.1 q.1.2 q.2.1 q.2.2)
    (encPair (encPair encUnary (encList encNat)) (encPair (encList encNat) (encList encNat)))
    (encList encNat) := by
  fun_prop

/-- **Powers in polynomial time**, with the exponent in unary. -/
example : ComputableInPolyTime
    (fun q : (ℕ × List ℕ) × (List ℕ × ℕ) => pow q.1.1 q.1.2 q.2.1 q.2.2)
    (encPair (encPair encUnary (encList encNat)) (encPair (encList encNat) encUnary))
    (encList encNat) := by
  fun_prop

/-- **Inversion in polynomial time.** -/
example : ComputableInPolyTime
    (fun q : (ℕ × List ℕ) × List ℕ => inv q.1.1 q.1.2 q.2)
    (encPair (encPair encUnary (encList encNat)) (encList encNat)) (encList encNat) := by
  fun_prop

end ComplexityTests.GaloisRingArithmetic
