/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Relating optional values

`Option.Rel r o₁ o₂` lifts a relation to optional values: both are `none`, or both are `some` with
related contents. Core states only its four constructor cases. This module adds that it inherits
reflexivity, symmetry and transitivity from `r`, is monotone in `r`, reduces to equality for
`r = (· = ·)`, and is preserved by `Option.bind` with related continuations. Observing a
computation that may fail as an `Option` and relating results up to `r` uses exactly these facts.

## Main results

* `Option.rel_refl`, `Option.Rel.symm`, `Option.Rel.trans`, `Option.Rel.mono`: `Option.Rel`
  inherits the properties of `r`.
* `Option.rel_eq_iff`: lifting equality gives equality.
* `Option.Rel.bind`: binding related values to related continuations gives related values.
-/

public section

namespace Option

variable {α β γ δ : Type*} {r : α → β → Prop}

theorem rel_refl {r : α → α → Prop} (hr : ∀ a, r a a) : ∀ o : Option α, Rel r o o
  | none => .none
  | some a => .some (hr a)

theorem Rel.symm {r : α → α → Prop} (hr : ∀ a b, r a b → r b a) {o₁ o₂ : Option α}
    (h : Rel r o₁ o₂) : Rel r o₂ o₁ := by
  cases h with
  | none => exact .none
  | some h => exact .some (hr _ _ h)

theorem Rel.trans {r : α → α → Prop} (hr : ∀ a b c, r a b → r b c → r a c)
    {o₁ o₂ o₃ : Option α} (h₁₂ : Rel r o₁ o₂) (h₂₃ : Rel r o₂ o₃) : Rel r o₁ o₃ := by
  cases h₁₂ with
  | none => exact h₂₃
  | some h =>
    cases h₂₃ with
    | some h' => exact .some (hr _ _ _ h h')

theorem Rel.mono {s : α → β → Prop} (hrs : ∀ a b, r a b → s a b) {o₁ : Option α}
    {o₂ : Option β} (h : Rel r o₁ o₂) : Rel s o₁ o₂ := by
  cases h with
  | none => exact .none
  | some h => exact .some (hrs _ _ h)

@[simp] theorem rel_eq_iff {o₁ o₂ : Option α} : Rel (· = ·) o₁ o₂ ↔ o₁ = o₂ := by
  constructor
  · rintro (⟨rfl⟩ | _) <;> rfl
  · rintro rfl
    exact rel_refl (fun _ => rfl) o₁

/-- Binding related values to continuations that take related arguments to related results gives
related results. -/
theorem Rel.bind {s : γ → δ → Prop} {o₁ : Option α} {o₂ : Option β} (h : Rel r o₁ o₂)
    {f : α → Option γ} {g : β → Option δ} (hfg : ∀ a b, r a b → Rel s (f a) (g b)) :
    Rel s (o₁.bind f) (o₂.bind g) := by
  cases h with
  | none => exact .none
  | some h => exact hfg _ _ h

end Option
