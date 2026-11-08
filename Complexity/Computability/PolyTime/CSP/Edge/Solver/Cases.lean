/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Native case analysis for solver work codes

Reuse the existing native sum projections and option elimination to retain captured work data
while branching on a tag. The fallback only makes the intermediate double-option operation
total; sum exhaustiveness proves that execution never uses it. This bookkeeping is original.
No new machine primitive or global automation rule is introduced.
-/

public section

namespace Cslib.Complexity.CSP.EdgeSolver.NativeCases

open Turing.MultiTapeTM

/-- Native tagged-sum case analysis retaining the original captured input. -/
theorem sumElimSnd {α β γ δ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {eg : γ ↪ List Bool} {ed : δ ↪ List Bool} (fallback : δ)
    {left : γ → α → δ} {right : γ → β → δ}
    (hl : ComputableInPolyTime (fun p : γ × α => left p.1 p.2) (encPair eg ea) ed)
    (hr : ComputableInPolyTime (fun p : γ × β => right p.1 p.2) (encPair eg eb) ed) :
    ComputableInPolyTime
      (fun p : γ × (α ⊕ β) => p.2.elim (left p.1) (right p.1))
      (encPair eg (encSum ea eb)) ed := by
  have hleft : ComputableInPolyTime (fun p : γ × (α ⊕ β) => p.2.getLeft?)
      (encPair eg (encSum ea eb)) (encOption ea) :=
    (ComputableInO.getLeft?_deg ea eb).computableInPolyTime.comp (by fun_prop)
  have hright : ComputableInPolyTime (fun p : γ × (α ⊕ β) => p.2.getRight?)
      (encPair eg (encSum ea eb)) (encOption eb) :=
    (ComputableInO.getRight?_deg ea eb).computableInPolyTime.comp (by fun_prop)
  have hl' : ComputableInPolyTime
      (fun p : (γ × (α ⊕ β)) × α => left p.1.1 p.2)
      (encPair (encPair eg (encSum ea eb)) ea) ed := by
    simpa only [Function.comp_def] using hl.comp
      (show ComputableInPolyTime (fun p : (γ × (α ⊕ β)) × α => (p.1.1, p.2))
        (encPair (encPair eg (encSum ea eb)) ea) (encPair eg ea) from by fun_prop)
  have hr' : ComputableInPolyTime
      (fun p : (γ × (α ⊕ β)) × β => right p.1.1 p.2)
      (encPair (encPair eg (encSum ea eb)) eb) ed := by
    simpa only [Function.comp_def] using hr.comp
      (show ComputableInPolyTime (fun p : (γ × (α ⊕ β)) × β => (p.1.1, p.2))
        (encPair (encPair eg (encSum ea eb)) eb) (encPair eg eb) from by fun_prop)
  have h := ComputableInPolyTime.optionElimWithInput
    (body := fun p a => left p.1 a) hleft
    (ComputableInPolyTime.optionElimWithInput (body := fun p b => right p.1 b)
      hright (ComputableInPolyTime.const fallback) hr') hl'
  apply h.of_enc_eq
  rintro ⟨p, a | b⟩ <;> rfl

/-- Native case analysis on a computed sum, retaining captured original inputs. The fallback
only totalizes the existing projection/option implementation and is unreachable for sums. -/
theorem sumElimWithInput {α β γ δ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {eg : γ ↪ List Bool} {ed : δ ↪ List Bool} (fallback : δ)
    {value : γ → α ⊕ β} {left : γ → α → δ} {right : γ → β → δ}
    (hv : ComputableInPolyTime value eg (encSum ea eb))
    (hl : ComputableInPolyTime (fun p : γ × α => left p.1 p.2) (encPair eg ea) ed)
    (hr : ComputableInPolyTime (fun p : γ × β => right p.1 p.2) (encPair eg eb) ed) :
    ComputableInPolyTime (fun p => (value p).elim (left p) (right p)) eg ed := by
  simpa only [Function.comp_def] using (sumElimSnd fallback hl hr).comp
    ((ComputableInPolyTime.id' (encIn := eg)).prod hv)

end Cslib.Complexity.CSP.EdgeSolver.NativeCases
