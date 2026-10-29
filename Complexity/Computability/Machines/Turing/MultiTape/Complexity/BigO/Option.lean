/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative

/-!
# Parameterized option elimination with retained input

Option elimination retains the original input for the selected handler. The construction tests
the tag and, on the `some` branch, computes the option again to extract its payload. Its bounds
explicitly charge both computations, input retention, and the selected handler. Linear native
tag extraction, payload extraction, and pairing costs are absorbed by the native calculus.
The bounds are asymptotic expressions with existential machine constants, not exact step counts.
No inhabitance assumption is imposed on the payload type.

## Main results

* `Turing.MultiTapeTM.ComputableInO.optionElimWithInput`: selected-branch time and space
  bounds for option elimination retaining the original input.

## References

Uses Christian Reitwiessner's native degree/resource calculus. The proof adapts
`Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Option.lean` while
preserving arbitrary resource bounds.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInO

/-- Eliminate an option while retaining the input. The conservative bound charges two option
computations even on the `none` branch; it charges only the selected handler. -/
theorem optionElimWithInput {α β γ : Type}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {value : α → Option β} {fallback : α → γ} {body : α → β → γ}
    {Tv Sv Tnone Snone : α → ℕ} {Tbody Sbody : α × β → ℕ}
    (hvalue : ComputableInO value encA (encOption encB) Tv Sv)
    (hfallback : ComputableInO fallback encA encC Tnone Snone)
    (hbody : ComputableInO (fun p : α × β => body p.1 p.2)
      (encPair encA encB) encC Tbody Sbody) :
    ComputableInO (fun a => (value a).elim (fallback a) (body a)) encA encC
      (fun a => 2 * Tv a + (encA a).length +
        (value a).elim (Tnone a) (fun b => Tbody (a, b)))
      (fun a => 2 * Sv a + (encA a).length +
        (value a).elim (Snone a) (fun b => Sbody (a, b))) := by
  rcases isEmpty_or_nonempty β with h | h
  · have hv : ∀ a, value a = none := by
      intro a
      cases value a with
      | none => rfl
      | some b => exact isEmptyElim b
    simpa only [hv, Option.elim_none] using hfallback.mono_le
      (T' := fun a => 2 * Tv a + (encA a).length + Tnone a)
      (S' := fun a => 2 * Sv a + (encA a).length + Snone a)
      (fun _ => by omega) (fun _ => by omega)
  · obtain ⟨b⟩ := h
    have hget := (ComputableInDegree.optionGetD encB b).inO_one.comp_linear hvalue
    have htag := (ComputableInDegree.isSome (enc := encB)).inO_one.comp_linear hvalue
    have hid : ComputableInO (fun a : α => a) encA encA
        (fun a => (encA a).length) (fun a => (encA a).length) :=
      (ComputableInDegree.id').inO_one
    have h := htag.ite (hbody.comp (hid.prod hget)) hfallback
    have h' := h.mono_le
      (T' := fun a => 2 * Tv a + (encA a).length +
        (value a).elim (Tnone a) (fun b => Tbody (a, b)))
      (S' := fun a => 2 * Sv a + (encA a).length +
        (value a).elim (Snone a) (fun b => Sbody (a, b)))
      (fun a => by
        cases hv : value a <;>
          simp only [Function.comp_def, hv, Option.isSome_none, Option.isSome_some,
            Option.getD_some, Option.elim_none, Option.elim_some, Bool.false_eq_true,
            ite_false, ite_true] <;> omega)
      (fun a => by
        cases hv : value a <;>
          simp only [Function.comp_def, hv, Option.isSome_none, Option.isSome_some,
            Option.getD_some, Option.elim_none, Option.elim_some, Bool.false_eq_true,
            ite_false, ite_true] <;> omega)
    convert h' using 1
    funext a
    change (value a).elim (fallback a) (body a) =
      if (value a).isSome then body a ((value a).getD b) else fallback a
    cases value a <;> rfl

end Turing.MultiTapeTM.ComputableInO
