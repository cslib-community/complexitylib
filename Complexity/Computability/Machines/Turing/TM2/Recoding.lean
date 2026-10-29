/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import Complexity.Computability.Machines.Turing.TM2.PolyTime
public import Complexity.Computability.Machines.Turing.TM2.PolySpace

/-!
# Removing the stack-machine bridge's word recoding

The forward bridges `TM2.PolyTime` and `TM2.PolySpace` produce computations over framed lists of
encoded Boolean symbols (`encIn.trans (encList (encFinEnum Bool))`). Applying
`Turing.MultiTapeTM.trans_encList_polyTime` transfers them to the caller's original binary
encodings without requiring a computable inverse for either encoding.

## Main results

* `Turing.TM2ComputableInPolyTime.computableInPolyTime`: forward polynomial-time transfer.
* `Turing.TM2Computable.computableInPolySpace`: forward polynomial-space transfer.

## References

The word conventions are those of the forward bridges `TM2.PolyTime` and `TM2.PolySpace`.
-/

public section

namespace Turing.TM2ComputableInPolyTime

open MultiTapeTM

/-- The binary specialization of the forward bridge preserves the supplied encodings, without
requiring either encoding to have a computable inverse. -/
theorem computableInPolyTime {α β : Type}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (h : TM2ComputableInPolyTime encIn encOut f) [∀ stack, Finite (h.tm.Γ stack)] :
    ComputableInPolyTime f encIn encOut := by
  have hf := h.computableInPolyTime_encList (encA := encFinEnum Bool) (encB := encFinEnum Bool)
    encIn.injective encOut.injective
  obtain ⟨hinput, _⟩ := trans_encList_polyTime encIn (encFinEnum Bool)
  obtain ⟨_, houtput⟩ := trans_encList_polyTime encOut (encFinEnum Bool)
  simpa only [Function.comp_def] using houtput.comp (hf.comp hinput)

end Turing.TM2ComputableInPolyTime

namespace Turing.TM2Computable

open MultiTapeTM

/-- Termination and polynomially bounded stacks transfer to the original binary encodings.
All target stacks, including the input and output stacks, count towards the bound. -/
theorem computableInPolySpace {α β : Type}
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (h : TM2Computable encIn encOut f) [∀ stack, Finite (h.tm.Γ stack)]
    {space : α → ℕ} (hspace : PolyBounded (fun a => (encIn a).length) space)
    (hstacks : h.StacksBounded space) :
    ComputableInPolySpace f encIn encOut := by
  have hf := h.computableInPolySpace_encList (encA := encFinEnum Bool) (encB := encFinEnum Bool)
    encIn.injective encOut.injective hspace hstacks
  obtain ⟨hinput, _⟩ := trans_encList_polyTime encIn (encFinEnum Bool)
  obtain ⟨_, houtput⟩ := trans_encList_polyTime encOut (encFinEnum Bool)
  simpa only [Function.comp_def] using
    (ComputableInPolySpace.of_polyTime houtput).comp
      (hf.comp (ComputableInPolySpace.of_polyTime hinput))

end Turing.TM2Computable
