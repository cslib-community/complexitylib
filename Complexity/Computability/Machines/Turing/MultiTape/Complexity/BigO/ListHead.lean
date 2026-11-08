/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.ListOption
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import Mathlib.Tactic.Linarith

/-!
# Linear bounds for the optional head of a list

The certificate uses the framed list and option encodings and charges encoded output to space.
The inhabitance hypothesis supplies a fixed default for the head primitive; the result remains
`none` on the empty list. Apply the certificate explicitly to compose it with other computations.

## Main results

* `Turing.MultiTapeTM.ComputableInO.head?`: linear time and charged space for `List.head?`.
-/

public section

namespace Turing.MultiTapeTM.ComputableInO

variable {β : Type} {encB : β ↪ List Bool}

/-- Read the optional head in linear time and charged space. The displayed constant depends
only on the fixed default encoding, not on the input list. -/
theorem head? [Inhabited β] : ComputableInO (fun l : List β => l.head?) (encList encB)
    (encOption encB) (fun l => (2 * (encB default).length + 8) * ((encList encB l).length + 1))
    fun l => (2 * (encB default).length + 8) * ((encList encB l).length + 1) := by
  have hsome := (ComputableInDegree.optionSome (enc₁ := encB) (enc := encOption encB)).inO_one
  have h : ComputableInO (fun l : List β => if l.isEmpty then none else some (l.headD default))
      (encList encB) (encOption encB) _ _ :=
    (ComputableInDegree.listIsEmpty encB).inO_one.ite (const none)
      (hsome.comp' (ComputableInDegree.listHeadD encB default).inO_one)
  refine (h.of_enc_eq fun l => by cases l <;> rfl).mono 4 (fun l => ?_) fun l => ?_
  all_goals
    have hd : (encB (l.headD default)).length ≤
        (encList encB l).length + (encB default).length := by
      cases l with
      | nil => simp
      | cons b l =>
        have := length_le_encList_of_mem encB (List.mem_cons_self (a := b) (l := l))
        simp only [List.headD_cons]
        omega
    have hmul : (encList encB l).length + (encB default).length + 1 ≤
        (2 * (encB default).length + 8) * ((encList encB l).length + 1) := by nlinarith
    split_ifs <;> omega

end Turing.MultiTapeTM.ComputableInO
