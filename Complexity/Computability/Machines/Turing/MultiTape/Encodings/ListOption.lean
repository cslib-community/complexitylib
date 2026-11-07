/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Option

/-!
# Encoded sizes when selecting from lists and options

The optional head of a framed list and a value selected from an option have size bounds that
include the option tag and a possible default. These facts do not require a computation certificate.

## Main results

* `Turing.MultiTapeTM.length_head?_le`: bound the encoded optional head by the encoded list.
* `Turing.MultiTapeTM.length_getD_le`: bound a selected value by the option and its default.
-/

public section

namespace Turing.MultiTapeTM

variable {β γ : Type} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}

/-- The encoded optional head is bounded by the encoded list plus its option tag. -/
theorem length_head?_le (l : List β) :
    (encOption encB l.head?).length ≤ (encList encB l).length + 1 := by
  cases l with
  | nil => simp
  | cons b l =>
    have := SizedListEncoding.length_elem_le (encA := encB) (encL := encList encB)
      (b :: l) b List.mem_cons_self
    simp only [List.head?_cons, encOption_some, List.length_cons]
    omega

/-- Selecting an option value or its default charges the option and the encoded default. -/
theorem length_getD_le [Inhabited γ] (o : Option γ) :
    (encC (o.getD default)).length ≤ (encOption encC o).length + (encC default).length := by
  cases o with
  | none => simp
  | some c => simp only [Option.getD_some, encOption_some, List.length_cons]; omega

end Turing.MultiTapeTM
