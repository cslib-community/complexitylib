/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Karn Seth
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Arithmetic
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison

/-!
# Direct polynomial-time binary arithmetic

The existing carry folds are certified using plain machine closure.
Reachable word states are bounded by the encoded input length, not the numeric operands.
Strict comparison is the linear zip-transducer certificate of `BinaryComparison`.
Multiplication weakens the cubic-time schoolbook certificate `ComputableInO.natMul`.
-/

@[expose] public section
namespace Turing.MultiTapeTM
open Cslib

namespace ComputableInPolyTime

/-- Addition of binary naturals, using the carry and remaining-word folds.
Compose this certificate with the producers' `.prod` certificate. Global automatic addition
remains separate from this named rule, since an unconstrained intermediate encoding can select
a binary branch where a surrounding computation needs a unary size. -/
theorem binary_add : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    (encPair encNat encNat) encNat :=
  ComputableInO.natAdd.computableInPolyTime
    (PolyBounded.of_forall_le 1 2 (fun _ => by simp))
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))

/-- Strict comparison of binary naturals, from the linear zip-transducer certificate
`Turing.MultiTapeTM.computableInTimeAndSpace_natLt`. -/
@[fun_prop]
theorem binary_lt : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
    (encPair encNat encNat) encBool :=
  (ComputableInO.of_linear ComputableInLinearTimeAndSpace.natLt).computableInPolyTime
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))

/-- Multiply computed binary values, fixing their intermediate encodings for proof search. -/
theorem binary_mul' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a * right a) input encNat :=
  (ComputableInO.natMul.computableInPolyTime (PolyBounded.of_forall_le 1 3 fun _ => by simp)
    (PolyBounded.of_forall_le 1 1 fun _ => by simp)).comp (hleft.prod hright)

/-- Non-strict binary comparison, composed from the existing strict comparison certificate.
Automatic composition uses the computed-operand rule `binary_le'`. -/
theorem binary_le : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encNat encNat) encBool := by
  simpa only [Function.comp_def, ← decide_not, Nat.not_lt] using
    bool_not.comp (binary_lt.comp ((snd encNat encNat).prod (fst encNat encNat)))

/-- Compare two binary naturals computed uniformly from the same encoded input. -/
@[fun_prop]
theorem binary_le' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => decide (left a ≤ right a)) input encBool :=
  binary_le.comp (hleft.prod hright)

end ComputableInPolyTime
end Turing.MultiTapeTM
