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

-- Measurement values, boundary/little-endian/callback `run` checks, `count` bounds, and binary
-- arithmetic/radix word helpers.
example :
    (measurementValues 0 100 123 = [] ∧
      measurementValues 3 0 999 = [0, 0, 0] ∧
      measurementValues 2 1 0 = [-1, -1] ∧
      measurementValues 2 1 4 = [0, 0] ∧
      measurementValues 2 1 8 = [1, 1] ∧
      measurementValues 2 1 9 = [-1, -1]) ∧
    (run (fun p : ((ℕ × ℕ) × List ℤ) × ℕ => p.2 + 1) (0, 123) 0 = (1, ((0, 123), 1)) ∧
      run (fun p : ((ℕ × ℕ) × List ℤ) × ℕ => p.2 + 1) (4, 0) 0 = (1, ((4, 0), 1)) ∧
      run (fun p : ((ℕ × ℕ) × List ℤ) × List (List ℤ) => p.2 ++ [p.1.2]) (2, 1) [] =
        (9, ((2, 1), [[-1, -1], [0, -1], [1, -1], [-1, 0], [0, 0], [1, 0],
          [-1, 1], [0, 1], [1, 1]])) ∧
      run (fun p : ((ℕ × ℕ) × List ℤ) × (ℕ × List ℤ) =>
        (p.2.1, p.2.2 ++ [p.1.2.headD 0 + (p.2.1 : ℤ) + p.1.1.2])) (1, 1) (7, []) =
        (3, ((1, 1), (7, [7, 8, 9])))) ∧
    (count (8, 1) = 6561 ∧ (encNat (count (8, 1))).length = 13) ∧
    -- Keep these large boundary inputs: use the algebraic one/zero-exponent laws rather than
    -- asking the evaluator to expand a thousand-step power under its default safety threshold.
    (count (0, 1000) = 1 ∧ count (1000, 0) = 1) ∧
    (((BinarySub.digitPairs (3, 5)).foldl BinarySub.subStep (false, [])).1 = true ∧
      ((13 : ℕ).bits.reverse.foldl (BinaryDiv.divModStep 3) (0, 0)) = (4, 1) ∧
      ((13 : ℕ).bits.reverse.foldl (BinaryDiv.divModStep 0) (0, 0)) = (0, 13) ∧
      (Int.subNatNat 2 5 = -3 ∧ encIntBin (Int.subNatNat 2 5) = [true, true, true]) ∧
      (Int.subNatNat 5 2 = 3 ∧ Int.subNatNat 0 0 = 0) ∧
      (Cslib.Radix.digit 0 13 0 = 13 ∧ Cslib.Radix.digit 0 13 1 = 0) ∧
      Cslib.Radix.digit 1 999 5 = 0) ∧
    (measurementValues 3 0 0 = [0, 0, 0] ∧ measurementValues 2 2 17 = [0, 1]) :=
  ⟨by decide, by decide, by decide, by simp [count], by decide, by decide⟩

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

private noncomputable def toggle :
    NativeCertificate (fun p : ((ℕ × ℕ) × List ℤ) × Bool => !p.2)
      (encPair (encPair (encPair encUnary encNat) (encList encIntBin)) encBool) encBool :=
  NativeCertificate.ofPolyTime (ComputableInPolyTime.bool_not.comp
    (ComputableInPolyTime.snd (encPair (encPair encUnary encNat) (encList encIntBin)) encBool))

-- Signed tuple encoding lengths, all-prefix polynomial bound, `visitCertificate` polynomiality,
-- and native machine computability.
example (body : ((ℕ × ℕ) × List ℤ) × Bool → Bool) (c D j : ℕ) (hj : j ≤ count (c, D)) :
    (encList encIntBin (measurementValues 3 0 0)).length = 9 ∧
    ((encList encIntBin (measurementValues 2 2 20)).length = 14 ∧
      (encList encIntBin (measurementValues 2 2 20)).length ≤ 2 * (2 * ((2 : ℕ).size + 1) + 1)) ∧
    (encPair encNat (encPair (encPair encUnary encNat) encBool)
      (runPrefix body (c, D) j false)).length ≤
      2 * (c * (D.size + 1) + 1) + 4 * c + 2 * D.size + 5 ∧
    -- Decoder/callback composition is polynomial per visit; whole-loop time is not claimed PT.
    (visitCertificate toggle).IsPolynomial ∧
    IsComputable (fun p : ℕ × ℕ =>
      run (fun q : ((ℕ × ℕ) × List ℤ) × Bool => !q.2) p false)
      (encPair encUnary encNat) (encPair encNat (encPair (encPair encUnary encNat) encBool)) := by
  refine ⟨by decide,
    ⟨by decide, length_values_le 2 2 20⟩,
    ?_,
    visitCertificate_isPolynomial toggle (NativeCertificate.ofPolyTime_isPolynomial _),
    (certificate (NativeCertificate.linear (ComputableInO.of_linear
      (.of_eq (encIn := encPair encUnary encNat) (f := id) fun _ => rfl)))
      (NativeCertificate.const false) toggle).isComputable⟩
  simpa [Nat.add_assoc] using length_prefix_le (encB := encBool) body c D j 1 false hj
    (by simp [encBool_apply])
