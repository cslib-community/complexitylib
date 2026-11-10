/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Sequential

/-!
# Tape transformations given by equations

`TransformsWords tm ws ws' e t s`: started on the words `ws`, the machine `tm` leaves the words
`ws'` and emits `e`, within `t` steps and `s` work-tape cells. Most specifications of the parts of a
composed machine are of this form; for them, sequential composition is a plain chain of words, and
adapting a specification to other spellings of the words is rewriting.

## Main definitions

* `Turing.MultiTapeTM.TransformsWords`: tape transformations given by equations.

## Main results

* `Turing.MultiTapeTM.TransformsTapes.words`: a specification read on given words.
* `Turing.MultiTapeTM.TransformsWords.seq`: sequential composition.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State State₀ State₁ : Type*}

/-- `TransformsWords tm ws ws' e t s`: started on the words `ws`, the machine `tm` leaves the
words `ws'` and emits `e`, within `t` steps and `s` work-tape cells. -/
abbrev TransformsWords (tm : MultiTapeTM k Symbol State) (ws ws' : Fin k → List Symbol)
    (e : List Symbol) (t s : ℕ) : Prop :=
  TransformsTapes tm (fun _ v => v = ws) (fun _ _ v' e' => v' = ws' ∧ e' = e) t s

/-- **A specification read on given words**: the words satisfy the precondition, and the
postcondition determines the result. -/
theorem TransformsTapes.words {tm : MultiTapeTM k Symbol State}
    {P : List Symbol → (Fin k → List Symbol) → Prop}
    {Q : List Symbol → (Fin k → List Symbol) → (Fin k → List Symbol) → List Symbol → Prop}
    {t s : ℕ} (h : TransformsTapes tm P Q t s) {ws ws' : Fin k → List Symbol} {e : List Symbol}
    (hP : ∀ input, P input ws) (hQ : ∀ input v e', Q input ws v e' → v = ws' ∧ e' = e) :
    TransformsWords tm ws ws' e t s :=
  h.imp (by rintro input _ rfl; exact hP input)
    (by rintro input _ v e' rfl hq; exact hQ input v e' hq) le_rfl le_rfl

namespace TransformsWords

variable {tm : MultiTapeTM k Symbol State} {ws ws' ws₂ ws₂' : Fin k → List Symbol}
  {e e₂ : List Symbol} {t s t' s' : ℕ}

theorem mono (h : TransformsWords tm ws ws' e t s) (ht : t ≤ t') (hs : s ≤ s') :
    TransformsWords tm ws ws' e t' s' :=
  TransformsTapes.mono h ht hs

/-- Other spellings of the words and of the emitted word. -/
theorem congr (h : TransformsWords tm ws ws' e t s) (hws : ws₂ = ws) (hws' : ws' = ws₂')
    (he : e = e₂) : TransformsWords tm ws₂ ws₂' e₂ t s := by
  subst hws hws' he
  exact h

/-- **Sequential composition**: the words left by the first machine are those the second one
starts on, and the emitted words are concatenated. -/
theorem seq {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}
    {ws₀ ws₁ ws₂ : Fin k → List Symbol} {e₀ e₁ : List Symbol} {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : TransformsWords tm₀ ws₀ ws₁ e₀ t₀ s₀) (h₁ : TransformsWords tm₁ ws₁ ws₂ e₁ t₁ s₁) :
    TransformsWords (tm₀.seq tm₁) ws₀ ws₂ (e₀ ++ e₁) (t₀ + t₁) (s₀ + s₁) :=
  (transformsTapes_seq h₀ h₁ fun _ _ _ _ _ h => h.1).imp (fun _ _ h => h)
    (by rintro _ _ _ _ _ ⟨_, _, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩) le_rfl le_rfl

end TransformsWords

end Turing.MultiTapeTM
