/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.GenericRAM.Native.BooleanFold
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives

/-! Concrete runtime-width and native controls. Only these tiny specifications materialize
assignment lists; the implementation streams a binary index and one captured accumulator. -/

open Cslib.GenericRAM Cslib.BitString Turing.MultiTapeTM
open Cslib.GenericRAM.BooleanFold

example : lowBits 0 12345 = [] := by decide
example : lowBits 4 0 = [false, false, false, false] := by decide
example : lowBits 3 8 = [false, false, false] := by decide
example : lowBits 3 9 = [true, false, false] := by decide

-- Dimension zero has ONE empty assignment, not zero assignments.
example : run (fun p : (ℕ × List Bool) × ℕ => p.2 + 1) 0 0 = (1, (0, 1)) := by decide

-- Existing least-significant-bit-first order, including carry from 01 to 10.
example : run (fun p : (ℕ × List Bool) × List (List Bool) => p.2 ++ [p.1.2]) 2 [] =
    (4, (2, [[false, false], [true, false], [false, true], [true, true]])) := by decide

-- The callback receives the original runtime width and full captured accumulator.
example : run (fun p : (ℕ × List Bool) × (ℕ × ℕ) =>
    (p.2.1, p.2.2 + p.1.1 + if p.1.2.headD false then p.2.1 else 0))
    2 (7, 0) = (4, (2, (7, 22))) := by decide

-- The binary visit count is exponentially large but its construction/output are linear size.
example (n : ℕ) : (encNat (2 ^ n)).length = n + 1 := length_clock n
example (n : ℕ) : clock.time n = n ∧ clock.space n = n := by simp [clock]
example : (encNat (2 ^ 8)).length = 9 := by decide

-- Coverage includes arbitrary list words with their original declared length.
example (word : List Bool) : ∃! j : Fin (2 ^ word.length), lowBits word.length j = word :=
  decoder_coverage word.length word rfl

-- No callback growth premise is needed for a Boolean accumulator's concrete live-state bound.
example (body : (ℕ × List Bool) × Bool → Bool) (n j : ℕ) (hj : j ≤ 2 ^ n) :
    (encPair encNat (encPair encUnary encBool) (runPrefix body n j false)).length ≤
      4 * n + 5 := by
  simpa [Nat.add_assoc] using length_prefix_le (encB := encBool) body n j 1 false hj
    (by simp [encBool_apply])

-- Temporary callback input charges both width and all n decoded bits, including trailing zeros.
example (n j : ℕ) (b : Bool) :
    (encPair (encPair encUnary encBits) encBool ((n, lowBits n j), b)).length =
      6 * n + 4 := by
  simpa [encBool_apply, Nat.add_assoc] using
    length_callback_input (encB := encBool) n j b

private noncomputable def toggle :
    NativeCertificate (fun p : (ℕ × List Bool) × Bool => !p.2)
      (encPair (encPair encUnary encBits) encBool) encBool :=
  NativeCertificate.ofPolyTime (ComputableInPolyTime.bool_not.comp
    (ComputableInPolyTime.snd (encPair encUnary encBits) encBool))

-- Actual callback and decoder implementations compose to a polynomial PER-VISIT certificate.
example : (visitCertificate toggle).IsPolynomial := by
  apply visitCertificate_isPolynomial
  exact NativeCertificate.ofPolyTime_isPolynomial _

-- One native machine handles every runtime n, including n=0. No whole-loop PT assertion.
example : IsComputable (fun n : ℕ => run (fun p : (ℕ × List Bool) × Bool => !p.2) n false)
    encUnary (encPair encNat (encPair encUnary encBool)) := by
  exact (certificate (NativeCertificate.linear (ComputableInO.of_linear
    (.of_eq (encIn := encUnary) (f := id) fun _ => rfl)))
    (NativeCertificate.const false) toggle).isComputable

-- Missing arbitrary captured-body evidence cannot be filled by the decoder's certificate.
example {β : Type} (enc : β ↪ List Bool) (_body : (ℕ × List Bool) × β → β)
    (initial : ℕ → β) (_ci : NativeCertificate (fun n : ℕ => n) encUnary encUnary)
    (_initial : NativeCertificate initial encUnary enc) : True := by
  fail_if_success
    have : IsComputable (fun n : ℕ => run _body n (initial n))
        encUnary (encPair encNat (encPair encUnary enc)) := by
      exact (certificate _ci _initial (by assumption)).isComputable
  trivial
