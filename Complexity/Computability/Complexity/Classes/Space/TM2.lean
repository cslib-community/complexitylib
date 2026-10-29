/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.TM2.PolySpace
public import Complexity.Computability.Complexity.Classes.Space.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain

/-!
# Polynomial-space Mathlib stack machines decide problems in PSPACE

The source certificate supplies termination and a Boolean answer. A polynomial bound on every
reachable source stack gives a tidy polynomial-space computation, then membership in `PSPACE`.
The source runtime need not be polynomially bounded. Input and output words use the bridge's
standard finite-symbol encodings; the final Boolean answer is recoded to `encBool`.

## Main results

* `Cslib.Complexity.mem_PSPACE_of_tm2`: a terminating Mathlib TM2 decider with polynomially
  bounded stacks decides a problem in `PSPACE`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.1][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM

/-- A terminating finite-alphabet Mathlib stack-machine decider with polynomially bounded
stacks decides a problem in `PSPACE`, under the standard binary input-word encoding.

The hypothesis `hstacks` uses `Turing.TM2.stepTotal`, which agrees with Mathlib's partial
`Turing.TM2.step` whenever it returns a successor and fixes halted configurations
(`Turing.TM2.stepTotal_of_step`). Thus it bounds the ordinary source run, including its initial
and final configurations; padding beyond halting imposes no additional stack bound. -/
theorem mem_PSPACE_of_tm2 {α αΓ βΓ : Type} [Finite αΓ] [Finite βΓ]
    {encA : αΓ ↪ List Bool}
    {ea : α → List αΓ} {eb : Bool → List βΓ} {f : α → Bool} {A : Set α}
    (h : TM2Computable ea eb f) [∀ k, Finite (h.tm.Γ k)]
    (ha : Function.Injective ea) (hb : Function.Injective eb)
    {space : α → ℕ} (hspace : PolyBounded (fun a => (ea a).length) space)
    (hstacks : h.StacksBounded space)
    (hA : ∀ a, a ∈ A ↔ f a = true) :
    A ∈ PSPACE ((⟨ea, ha⟩ : α ↪ List αΓ).trans (encList encA)) := by
  have hf := h.computableInPolySpace_encList (encA := encA) (encB := encFinite βΓ)
    ha hb hspace hstacks
  have hbool := ComputableInPolyTime.of_finite (id : Bool → Bool)
    (encIn := (⟨eb, hb⟩ : Bool ↪ List βΓ).trans (encList (encFinite βΓ))) (encOut := encBool)
  exact mem_PSPACE_of_computableInPolySpace ((ComputableInPolySpace.of_polyTime hbool).comp hf)
    hA

end Cslib.Complexity
