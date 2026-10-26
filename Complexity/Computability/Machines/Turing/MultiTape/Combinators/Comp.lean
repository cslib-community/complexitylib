/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- upstream: submitted #1111 @3441fa81
-- `transformsTapes_clearWork_only` and `ComputableTidilyInTimeAndSpace.comp_linear` are from
-- crei:crei/tidy-universal @7f7c0696 (unsubmitted).

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelComp
public import Mathlib.Basic.Finite.Sum
public import Cslib.Foundations.Data.Fin.Tuple
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Basic

/-!
# Composing tidy computations

`tm₂.comp tm₁ mark` runs `tm₁` with its output written to a work tape, then runs `tm₂` reading its
input from that tape, and finally clears the tape. If both machines compute tidily, so does the
composition. Its time is the sum of the two times plus a term linear in the length of the
intermediate word; so is its space, since the intermediate word is kept on a work tape.

## Main definitions

* `Turing.MultiTapeTM.comp`: the composed machine.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.comp`: tidy computations compose.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp`: tidily computable functions compose.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp_linear`: the same, with the overhead a
  constant multiple of the length of the intermediate word plus one.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.comp'`: the same, with the length of the
  intermediate word bounded by the time of the inner function.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength.comp`: the same for bounds of the
  input length, given a bound `l` on the length of the intermediate word.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.computableInTimeAndSpace_comp`: hence `f ∘ g`
  is computable in the sense of `Turing.MultiTapeTM.ComputableInTimeAndSpace`.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpaceOfLength.computableInTimeAndSpaceOfLength_comp`:
  the same for bounds of the input length.
-/

namespace Turing.MultiTapeTM

/-- If `g` and `f` are tidily computable, so is `f ∘ g`, in the sum of their times and spaces plus
a term linear in the length of the intermediate word `encMid (g a)`. -/
public theorem ComputableTidilyInTimeAndSpace.comp {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableTidilyInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => t₁ a + t₂ (g a) + 4 * (encMid (g a)).length + 9)
      (fun a => s₁ a + s₂ (g a) + 5 * (encMid (g a)).length + c) := by
  obtain ⟨k₁, S₁, _, tm₁, h₁⟩ := hg
  obtain ⟨k₂, S₂, _, tm₂, h₂⟩ := hf
  exact ⟨6 * max k₁ k₂ + 20, _, _, inferInstance, tm₂.comp tm₁ true,
    fun a => (h₁ a).comp (h₂ (g a)) true⟩

-- vendored: crei:crei/tidy-universal states `ComputableTidilyInTimeAndSpace.comp` with these
-- bounds; cslib #1111 states it with explicit constants, which this follows from
/-- If `g` and `f` are tidily computable, so is `f ∘ g`, in the sum of their times and spaces plus
a constant multiple of the length of the intermediate word `encMid (g a)` plus one. -/
public theorem ComputableTidilyInTimeAndSpace.comp_linear {α β γ : Type*} {g : α → β}
    {f : β → γ} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableTidilyInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => t₁ a + t₂ (g a) + c * ((encMid (g a)).length + 1))
      (fun a => s₁ a + s₂ (g a) + c * ((encMid (g a)).length + 1)) := by
  obtain ⟨c, h⟩ := hf.comp hg
  refine ⟨c + 9, h.mono (fun a => ?_) (fun a => ?_)⟩ <;>
  · have := Nat.le_mul_of_pos_right c (by omega : 0 < (encMid (g a)).length + 1)
    rw [Nat.add_mul]
    omega

/-- If `g` and `f` are tidily computable, so is `f ∘ g`: the intermediate word is no longer than
the time of `g`. -/
public theorem ComputableTidilyInTimeAndSpace.comp' {α β γ : Type*} {g : α → β} {f : β → γ}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableTidilyInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => 5 * t₁ a + t₂ (g a) + 9) (fun a => s₁ a + s₂ (g a) + 5 * t₁ a + c) := by
  obtain ⟨c, h⟩ := hf.comp hg
  obtain ⟨_, _, _, _, h₁⟩ := hg
  refine ⟨c, h.mono (fun a => ?_) (fun a => ?_)⟩ <;>
  · have := (h₁ a).length_output_le
    omega

/-- If `g` and `f` are tidily computable in time `t₁`, `t₂` and space `s₁`, `s₂` of the length of
their input, for monotone `t₂` and `s₂`, and the output of `g` on inputs of length `n` has length at
most `l n`, then `f ∘ g` is tidily computable with bounds depending on `t₂ (l n)`, `s₂ (l n)` and
`l n`. -/
public theorem ComputableTidilyInTimeAndSpaceOfLength.comp {α β γ : Type*} {g : α → β}
    {f : β → γ} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {l t₁ s₁ t₂ s₂ : ℕ → ℕ} (ht : Monotone t₂) (hs : Monotone s₂)
    (hl : ∀ a, (encMid (g a)).length ≤ l (encIn a).length)
    (hf : ComputableTidilyInTimeAndSpaceOfLength f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpaceOfLength g encIn encMid t₁ s₁) :
    ∃ c, ComputableTidilyInTimeAndSpaceOfLength (f ∘ g) encIn encOut
      (fun n => t₁ n + t₂ (l n) + 4 * l n + 9) (fun n => s₁ n + s₂ (l n) + 5 * l n + c) := by
  obtain ⟨c, h⟩ := ComputableTidilyInTimeAndSpace.comp hf hg
  refine ⟨c, h.mono (fun a => ?_) (fun a => ?_)⟩ <;>
  · have := hl a
    have := ht (hl a)
    have := hs (hl a)
    beta_reduce
    omega

/-- If `g` and `f` are tidily computable, then `f ∘ g` is computable. -/
public theorem ComputableTidilyInTimeAndSpace.computableInTimeAndSpace_comp {α β γ : Type*}
    {g : α → β} {f : β → γ} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {t₁ s₁ : α → ℕ} {t₂ s₂ : β → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpace g encIn encMid t₁ s₁) :
    ∃ c, ComputableInTimeAndSpace (f ∘ g) encIn encOut
      (fun a => 5 * t₁ a + t₂ (g a) + 9) (fun a => s₁ a + s₂ (g a) + 5 * t₁ a + c) :=
  let ⟨c, h⟩ := hf.comp' hg
  ⟨c, h.computableInTimeAndSpace⟩

/-- If `g` and `f` are tidily computable in time `t₁`, `t₂` and space `s₁`, `s₂` of the length of
their input, for monotone `t₂` and `s₂`, and the output of `g` on inputs of length `n` has length at
most `l n`, then `f ∘ g` is computable. -/
public theorem ComputableTidilyInTimeAndSpaceOfLength.computableInTimeAndSpaceOfLength_comp
    {α β γ : Type*} {g : α → β} {f : β → γ} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {l t₁ s₁ t₂ s₂ : ℕ → ℕ} (ht : Monotone t₂) (hs : Monotone s₂)
    (hl : ∀ a, (encMid (g a)).length ≤ l (encIn a).length)
    (hf : ComputableTidilyInTimeAndSpaceOfLength f encMid encOut t₂ s₂)
    (hg : ComputableTidilyInTimeAndSpaceOfLength g encIn encMid t₁ s₁) :
    ∃ c, ComputableInTimeAndSpaceOfLength (f ∘ g) encIn encOut
      (fun n => t₁ n + t₂ (l n) + 4 * l n + 9) (fun n => s₁ n + s₂ (l n) + 5 * l n + c) :=
  let ⟨c, h⟩ := comp ht hs hl hf hg
  ⟨c, ComputableTidilyInTimeAndSpace.computableInTimeAndSpace h⟩

end Turing.MultiTapeTM
