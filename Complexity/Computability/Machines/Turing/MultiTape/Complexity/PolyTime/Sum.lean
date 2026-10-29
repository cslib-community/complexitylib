/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time sum constructors

The two injections retain the supplied payload encoding and add its tag bit. Their certificates
reuse the existing bit-string constructor and charge the entire payload, with no finite-domain
assumption on either summand.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.sumInl`, `.sumInr`: tagged sum construction.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type}

/-- Tag an encoded value as belonging to the left summand. -/
@[fun_prop]
theorem sumInl (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInPolyTime (Sum.inl (α := α) (β := β)) left (encSum left right) :=
  ((const false).bitsCons
    (of_eq (f := left) (encIn := left) (encOut := encBits) fun _ => rfl)).of_enc_eq fun _ => rfl

/-- Tag an encoded value as belonging to the right summand. -/
@[fun_prop]
theorem sumInr (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInPolyTime (Sum.inr (α := α) (β := β)) right (encSum left right) :=
  ((const true).bitsCons
    (of_eq (f := right) (encIn := right) (encOut := encBits) fun _ => rfl)).of_enc_eq fun _ => rfl

end Turing.MultiTapeTM.ComputableInPolyTime
