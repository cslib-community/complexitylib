/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Comp

/-!
# Direct composition at independent resource and output degrees

The proof combines machine normal forms, retaining the separate output degree of each input
certificate. Adapted from the direct-construction experiment in #869 by
worker-claude-tidyspike-c4b0c164.

## Main results

* `ComputableInDegree.comp`: resource degree `max d₁ (e₁ * d₂)` and output degree `e₁ * e₂`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInDegree

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- **Composition**, through the machine-level composition of tidy machines. The intermediate word
is no longer than the time of the inner machine. -/
theorem comp {f : β → γ} {g : α → β} {d₁ e₁ d₂ e₂ : ℕ}
    (hf : ComputableInDegree f encMid encOut d₂ e₂)
    (hg : ComputableInDegree g encIn encMid d₁ e₁) :
    ComputableInDegree (f ∘ g) encIn encOut (max d₁ (e₁ * d₂)) (e₁ * e₂) := by
  have hl₁ := hg.2
  have hl₂ := hf.2
  obtain ⟨t₁, s₁, ht₁, hs₁, k₁, Q₁, _, tm₁, h₁⟩ := Internal.NormalForm.degree hg
  obtain ⟨t₂, s₂, ht₂, hs₂, k₂, Q₂, _, tm₂, h₂⟩ := Internal.NormalForm.degree hf
  have hm : DegreeBounded (fun a => (encIn a).length) (fun a => (encMid (g a)).length) d₁ :=
    ht₁.mono fun a => (h₁ a).length_output_le
  have hd₁ : d₁ ≤ max d₁ (e₁ * d₂) := le_max_left _ _
  exact ⟨⟨_, _, ((ht₁.add_max (ht₂.comp hl₁)).add ((hm.smul 4).mono_deg hd₁)).add_const 9,
    ((hs₁.add_max (hs₂.comp hl₁)).add ((hm.smul 5).mono_deg hd₁)).add_const _,
    _, _, inferInstance, tm₂.comp tm₁ true,
    fun a => ((h₁ a).comp (h₂ (g a)) true).computesInTimeAndSpace⟩, hl₂.comp hl₁⟩

end Turing.MultiTapeTM.ComputableInDegree
