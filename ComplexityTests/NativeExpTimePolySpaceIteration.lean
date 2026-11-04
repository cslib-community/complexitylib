/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.GenericRAM.Native.ExpTimePolySpace.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-!
# Iterating a callback supplied with an exponential time bound

The callback reverses its word and is deliberately certified with an exponential time allowance
and polynomial workspace. Repeating it for the input length demonstrates that the iteration rule
retains one common exponent, without requiring a polynomial-time callback certificate. The concrete
odd- and even-length examples also check that the callback is actually iterated.
-/

open Turing.MultiTapeTM Cslib.GenericRAM

namespace ComplexityTests.NativeExpTimePolySpaceIteration

private def countCertificate : NativeCertificate List.length encBits encNat where
  time w := (w.length + 1) ^ 2
  space w := w.length + 1
  computes := ComputableInO.lengthNat

private def copyCertificate : NativeCertificate (fun w : List Bool => w) encBits encBits :=
  .ofTimeAndSpace computableInTimeAndSpace_id

private noncomputable def reverseCertificate : NativeCertificate List.reverse encBits encBits :=
  .ofPolyTime ComputableInPolyTime.bitsReverse

private noncomputable def roundCertificate : NativeCertificate List.reverse encBits encBits where
  time w := reverseCertificate.time w * 2 ^ w.length
  space := reverseCertificate.space
  computes := reverseCertificate.computes.mono_le
    (fun _ => Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) (fun _ => le_rfl)

private theorem length_iterate_reverse (j : ℕ) (w : List Bool) :
    (List.reverse^[j] w).length = w.length := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', List.length_reverse, ih]

private theorem count_polynomial : countCertificate.IsPolynomial := by
  constructor
  · exact PolyBounded.of_forall_le 1 2 fun _ => by simp [countCertificate, encBits]
  · exact PolyBounded.of_forall_le 1 1 fun _ => by simp [countCertificate, encBits]

private theorem copy_polynomial : copyCertificate.IsPolynomial := by
  constructor
  · exact PolyBounded.of_forall_le 1 1 fun _ => by
      simp [copyCertificate, NativeCertificate.ofTimeAndSpace, encBits]
  · exact PolyBounded.of_forall_le 1 1 fun _ => by
      simp [copyCertificate, NativeCertificate.ofTimeAndSpace, encBits]

private theorem iteration_bound :
    (NativeCertificate.iterate countCertificate copyCertificate roundCertificate).ExpTimePolySpace
      List.length := by
  have hp : reverseCertificate.IsPolynomial := NativeCertificate.ofPolyTime_isPolynomial _
  obtain ⟨ct, dt, ht⟩ := hp.1.exists_le
  obtain ⟨cq, dq, hq⟩ := hp.2.exists_le
  apply NativeCertificate.ExpTimePolySpace.iterate_of_bounds
    countCertificate copyCertificate roundCertificate count_polynomial copy_polynomial
    (R := fun w => ct * (w.length + 1) ^ dt)
    (Q := fun w => cq * (w.length + 1) ^ dq) (B := List.length)
    PolyBounded.self
    ((PolyBounded.const ct).mul ((PolyBounded.self.add (.const 1)).pow dt))
    ((PolyBounded.const cq).mul ((PolyBounded.self.add (.const 1)).pow dq))
    PolyBounded.self
  · intro w j _
    change reverseCertificate.time (List.reverse^[j] w) * 2 ^ (List.reverse^[j] w).length ≤ _
    rw [length_iterate_reverse]
    apply Nat.mul_le_mul_right
    simpa only [encBits_apply, length_iterate_reverse] using
      ht (List.reverse^[j] w)
  · intro w j _
    change reverseCertificate.space (List.reverse^[j] w) ≤ _
    simpa only [encBits_apply, length_iterate_reverse] using
      hq (List.reverse^[j] w)
  · intro w j _
    exact (length_iterate_reverse j w).le

-- The output is not a constant or an unconditionally unchanged word.
example : List.reverse^[3] [true, false, false] = [false, false, true] := by decide
example : List.reverse^[2] [true, false] = [true, false] := by decide

-- The same deterministic machine has exponential time and polynomial workspace on runtime words.
example : ∃ e : ℕ, ComputableInO (fun w : List Bool => List.reverse^[w.length] w) encBits encBits
    (fun w => 2 ^ w.length * (w.length + 1) ^ e) (fun w => (w.length + 1) ^ e) :=
  iteration_bound.computableInO

end ComplexityTests.NativeExpTimePolySpaceIteration
