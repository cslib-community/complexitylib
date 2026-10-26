/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelIte
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Branch

/-!
# Case distinction

If `c`, `f` and `g` are tidily computable from a common input, so is
`fun x => if c x then f x else g x`, within the bounds of `c` plus those of the branch taken.

`iteTM tmc tm₁ tm₂` runs `tmc` with its output written to a new work tape, runs `tm₁` if that word
is non-empty and `tm₂` otherwise (`Turing.MultiTapeTM.branch`), and clears the tape. The condition
`c` may be computed with any encoding of `Bool`: a finite-state transducer turns its output into a
word that is empty exactly for `false`.

## Main definitions

* `Turing.MultiTapeTM.iteTM`: the machine for a case distinction.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.ite`: the machine-level case distinction.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.ite`: case distinctions are tidily computable;
  each branch need only be computable on the inputs where it is taken.
-/

namespace Turing.MultiTapeTM

/-- A function tidily computable on all inputs is tidily computable on the inputs satisfying `p`, by
the same machine. -/
public theorem ComputableTidilyInTimeAndSpace.restrict {α β : Type*} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} {t s : α → ℕ}
    (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) (p : α → Prop) :
    ComputableTidilyInTimeAndSpace (f ∘ Subtype.val) ((Function.Embedding.subtype p).trans encIn)
      encOut (t ∘ Subtype.val) (s ∘ Subtype.val) :=
  let ⟨k, S, hS, tm, htm⟩ := h
  ⟨k, S, hS, tm, fun x => htm x⟩

/-- Case distinctions are tidily computable: if `c` is tidily computable, `f` on the inputs where
`c` holds and `g` on the others, then `fun x => if c x then f x else g x` is tidily computable,
within the bounds of `c` plus those of the branch taken, up to a constant. The condition may be
computed with any encoding of `Bool`. -/
public theorem ComputableTidilyInTimeAndSpace.ite {γ β : Type*} {encIn : γ ↪ List Bool}
    {encC : Bool ↪ List Bool} {encOut : β ↪ List Bool} {c : γ → Bool} {f g : γ → β}
    {tc sc tf sf tg sg : γ → ℕ}
    (hc : ComputableTidilyInTimeAndSpace c encIn encC tc sc)
    (hf : ComputableTidilyInTimeAndSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans encIn) encOut (tf ∘ Subtype.val)
      (sf ∘ Subtype.val))
    (hg : ComputableTidilyInTimeAndSpace (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans encIn) encOut (tg ∘ Subtype.val)
      (sg ∘ Subtype.val)) :
    ∃ k, ComputableTidilyInTimeAndSpace (fun x => if c x then f x else g x) encIn encOut
      (fun x => tc x + (if c x then tf x else tg x) + k)
      (fun x => sc x + (if c x then sf x else sg x) + k) := by
  -- the test word of the condition, in time bounded by the longer encoding of a truth value
  obtain ⟨l, hl⟩ : ∃ l, ∀ b, (encC b).length ≤ l :=
    ⟨(encC true).length + (encC false).length, fun b => by cases b <;> omega⟩
  have htest := (eqWordT (encC true)).computableTidilyInTimeAndSpace (f := id) (encIn := encC)
    (encOut := encTest) fun b => by
      rw [eqWordT_run_q₀]; cases b <;> simp [encTest_true, encTest_false]
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨ct, hct⟩ := ComputableTidilyInTimeAndSpace.comp_linear htest hc
  have hb (x : γ) : 4 * (encC (c x)).length + 8 + ct * ((encC (c x)).length + 1) ≤
      (ct + 4) * (l + 2) := by
    have := hl (c x)
    have := Nat.mul_le_mul_left ct this
    simp only [Nat.mul_add_one, Nat.add_mul]; omega
  obtain ⟨k₀, S₀, _, tmc, htmc⟩ := hct.mono (t' := fun x => tc x + (ct + 4) * (l + 2))
    (s' := fun x => sc x + (ct + 4) * (l + 2)) (fun x => by have := hb x; omega)
    (fun x => by have := hb x; omega)
  obtain ⟨k₁, S₁, _, tm₁, htm₁⟩ := hf
  obtain ⟨k₂, S₂, _, tm₂, htm₂⟩ := hg
  refine ⟨(ct + 4) * (l + 2) + 15 + 5 * max k₀ (max k₁ k₂), _, _, inferInstance,
    iteTM tmc tm₁ tm₂, fun x => ?_⟩
  have h := (htmc x).ite (tm₁ := tm₁) (tm₂ := tm₂) (y := encOut (if c x then f x else g x))
    (t₁ := tf x) (s₁ := sf x) (t₂ := tg x) (s₂ := sg x)
    (fun hw => by
      have hcx : c x = true := by cases hcx : c x <;> simp_all [encTest_true, encTest_false]
      simpa [hcx] using htm₁ ⟨x, hcx⟩)
    (fun hw => by
      have hcx : c x = false := by cases hcx : c x <;> simp_all [encTest_true, encTest_false]
      simpa [hcx] using htm₂ ⟨x, hcx⟩)
  refine TransformsTapes.mono h ?_ ?_ <;> cases hcx : c x <;>
    simp [hcx, encTest_true, encTest_false] <;> omega

end Turing.MultiTapeTM
