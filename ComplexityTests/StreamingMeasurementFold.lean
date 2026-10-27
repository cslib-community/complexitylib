/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.GenericRAM.Native.MeasurementFold
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives

/-! Actual signed-value, order, arithmetic, encoding and native controls. Only small test
specifications materialize word lists; the native iterator does not construct the whole box. -/

open Cslib.GenericRAM Cslib.Radix Turing.MultiTapeTM
open Cslib.GenericRAM.MeasurementFold

example : measurementValues 0 100 123 = [] := by decide
example : measurementValues 3 0 999 = [0, 0, 0] := by decide
example : measurementValues 2 1 0 = [-1, -1] := by decide
example : measurementValues 2 1 4 = [0, 0] := by decide
example : measurementValues 2 1 8 = [1, 1] := by decide
example : measurementValues 2 1 9 = [-1, -1] := by decide

-- Both boundary cases have one tuple, retaining the original dimension/radius context.
example : run (fun p : ((ℕ × ℕ) × List ℤ) × ℕ => p.2 + 1) (0, 123) 0 =
    (1, ((0, 123), 1)) := by decide
example : run (fun p : ((ℕ × ℕ) × List ℤ) × ℕ => p.2 + 1) (4, 0) 0 =
    (1, ((4, 0), 1)) := by decide

-- Little-endian measurement VALUE order, not formal exponent tuples.
example : run (fun p : ((ℕ × ℕ) × List ℤ) × List (List ℤ) => p.2 ++ [p.1.2]) (2, 1) [] =
    (9, ((2, 1), [[-1, -1], [0, -1], [1, -1], [-1, 0], [0, 0], [1, 0],
      [-1, 1], [0, 1], [1, 1]])) := by decide

-- The callback sees the full radius and captured seed; it cannot overwrite the parameters.
example : run (fun p : ((ℕ × ℕ) × List ℤ) × (ℕ × List ℤ) =>
    (p.2.1, p.2.2 ++ [p.1.2.headD 0 + (p.2.1 : ℤ) + p.1.1.2])) (1, 1) (7, []) =
    (3, ((1, 1), (7, [7, 8, 9]))) := by decide

-- Actual binary output size: 3^8 has 13 bits, rather than a unary word of length 6561.
example : count (8, 1) = 6561 ∧ (encNat (count (8, 1))).length = 13 := by decide
-- Keep these large boundary inputs: use the algebraic one/zero-exponent laws rather than
-- asking the evaluator to expand a thousand-step power under its default safety threshold.
example : count (0, 1000) = 1 ∧ count (1000, 0) = 1 := by simp [count]

-- The unchanged word programs exercise borrow, exact division and the zero-divisor branch.
example : ((BinarySub.digitPairs (3, 5)).foldl BinarySub.subStep (false, [])).1 = true := by
  decide
example : ((13 : ℕ).bits.reverse.foldl (BinaryDiv.divModStep 3) (0, 0)) = (4, 1) := by decide
example : ((13 : ℕ).bits.reverse.foldl (BinaryDiv.divModStep 0) (0, 0)) = (0, 13) := by decide
example : Int.subNatNat 2 5 = -3 ∧ encIntBin (Int.subNatNat 2 5) = [true, true, true] := by decide
example : Int.subNatNat 5 2 = 3 ∧ Int.subNatNat 0 0 = 0 := by decide
example : Cslib.Radix.digit 0 13 0 = 13 ∧ Cslib.Radix.digit 0 13 1 = 0 := by decide
example : Cslib.Radix.digit 1 999 5 = 0 := by decide

-- A real fitting word reaches its own index, including the degenerate radius-zero box.
example : measurementValues 3 0 0 = [0, 0, 0] ∧
    measurementValues 2 2 17 = [0, 1] := by decide

-- Generic captured inputs retain their producer encodings, not just a closed signature.
example {α : Type} (enc : α ↪ List Bool) (B x i : α → ℕ)
    (hB : ComputableInPolyTime B enc encNat) (hx : ComputableInPolyTime x enc encNat)
    (hi : ComputableInPolyTime i enc encUnary) :
    ComputableInPolyTime (fun a => Cslib.Radix.digit (B a) (x a) (i a)) enc encNat :=
  ComputableInPolyTime.radix_digit.comp ((hB.prod hx).prod hi)

-- A binary position certificate does not discharge this API's unary-position obligation.
example {α : Type} (enc : α ↪ List Bool) (_B _x _i : α → ℕ)
    (_hB : ComputableInPolyTime _B enc encNat) (_hx : ComputableInPolyTime _x enc encNat)
    (_hi : ComputableInPolyTime _i enc encNat) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun a => Cslib.Radix.digit (_B a) (_x a) (_i a)) enc encNat := by
      exact ComputableInPolyTime.radix_digit.comp ((_hB.prod _hx).prod (by assumption))
  trivial

-- Signed tuple encoding charges the sign and the framed length of every coordinate.
example : (encList encIntBin (measurementValues 3 0 0)).length = 9 := by decide
example : (encList encIntBin (measurementValues 2 2 20)).length = 14 ∧
    (encList encIntBin (measurementValues 2 2 20)).length ≤ 2 * (2 * ((2 : ℕ).size + 1) + 1) := by
  constructor
  · decide
  · exact length_values_le 2 2 20

-- A Boolean accumulator gives a concrete all-prefix polynomial bound with no growth premise.
example (body : ((ℕ × ℕ) × List ℤ) × Bool → Bool) (c D j : ℕ) (hj : j ≤ count (c, D)) :
    (encPair encNat (encPair (encPair encUnary encNat) encBool)
      (runPrefix body (c, D) j false)).length ≤
      2 * (c * (D.size + 1) + 1) + 4 * c + 2 * D.size + 5 := by
  simpa [Nat.add_assoc] using length_prefix_le (encB := encBool) body c D j 1 false hj
    (by simp [encBool_apply])

private noncomputable def toggle :
    NativeCertificate (fun p : ((ℕ × ℕ) × List ℤ) × Bool => !p.2)
      (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encBool) encBool :=
  NativeCertificate.ofPolyTime (ComputableInPolyTime.bool_not.comp
    (ComputableInPolyTime.snd (encPair (encPair encUnary encNat) (encList encIntBin)) encBool))

-- Actual decoder/callback composition is polynomial per visit; whole-loop time is not claimed PT.
example : (visitCertificate toggle).IsPolynomial := by
  apply visitCertificate_isPolynomial
  exact NativeCertificate.ofPolyTime_isPolynomial _

-- One native machine covers all runtime dimensions/radii, including base one and dimension zero.
example : IsComputable (fun p : ℕ × ℕ =>
    run (fun q : ((ℕ × ℕ) × List ℤ) × Bool => !q.2) p false)
    (encPair encUnary encNat) (encPair encNat (encPair (encPair encUnary encNat) encBool)) := by
  exact (certificate (NativeCertificate.linear (ComputableInO.of_linear
    (.of_eq (encIn := encPair encUnary encNat) (f := id) fun _ => rfl)))
    (NativeCertificate.const false) toggle).isComputable
