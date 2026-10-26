/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial space on plain machines

`Turing.MultiTapeTM.ComputableInPolySpace`, computability within polynomial space by any machine,
agrees with its tidy counterpart `Turing.MultiTapeTM.ComputableTidilyInPolySpace`: the tidy normal
form changes the bounds by constant factors
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInO`). Proofs switch between the
notions with `Turing.MultiTapeTM.ComputableInPolySpace.tidy` and
`Turing.MultiTapeTM.ComputableInPolySpace.of_tidy`.

The plain predicate and its closure rules are registered with `fun_prop`. A plain goal can use
plain polynomial-space and polynomial-time hypotheses, together with tidy certificates through
`Turing.MultiTapeTM.ComputableTidilyInPolySpace.computableInPolySpace`. Only the tidy-to-plain
direction is a transition rule; the reverse bridge is used explicitly inside the proofs.

## Main results

* `Turing.MultiTapeTM.computableInPolySpace_iff_computableTidilyInPolySpace`: the plain and tidy
  notions agree, with the shortcuts `Turing.MultiTapeTM.ComputableInPolySpace.tidy`,
  `Turing.MultiTapeTM.ComputableInPolySpace.of_tidy` and
  `Turing.MultiTapeTM.ComputableTidilyInPolySpace.computableInPolySpace`.
* `Turing.MultiTapeTM.ComputableInPolySpace.of_polyTime`: plain polynomial time is within
  polynomial space.
* `Turing.MultiTapeTM.ComputableInPolySpace.comp`, `.prod`, `.ite`: closure properties.
-/

@[expose] public section

namespace Turing.MultiTapeTM

attribute [fun_prop] ComputableInPolySpace

variable {α β : Type} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- A function computable within polynomial space is tidily computable within polynomial space. -/
theorem ComputableInPolySpace.tidy (h : ComputableInPolySpace f encIn encOut) :
    ComputableTidilyInPolySpace f encIn encOut :=
  let ⟨_, _, hs, hc, hl⟩ := h
  ⟨_, _, .of_polynomiallyBounded _ hs, hc.computableTidilyInO hl⟩

/-- A function tidily computable within polynomial space is computable within polynomial space, by
the same machine. -/
theorem ComputableInPolySpace.of_tidy (h : ComputableTidilyInPolySpace f encIn encOut) :
    ComputableInPolySpace f encIn encOut := by
  obtain ⟨T, S, ⟨b, hb, hS⟩, c, hc, hl⟩ := h
  have hcS (a : α) : c * (S a + 1) ≤ c * (b (encIn a).length + 1) :=
    Nat.mul_le_mul_left c (Nat.add_le_add_right (hS a) 1)
  exact ⟨_, fun n => c * (b n + 1), by fun_prop,
    hc.computableInTimeAndSpace.mono (fun _ => le_rfl) hcS, fun a => (hl a).trans (hcS a)⟩

/-- `Turing.MultiTapeTM.ComputableInPolySpace.of_tidy` for dot notation on a tidy hypothesis and
the transition used by `fun_prop` to prove plain goals from tidy certificates. -/
@[fun_prop]
theorem ComputableTidilyInPolySpace.computableInPolySpace
    (h : ComputableTidilyInPolySpace f encIn encOut) : ComputableInPolySpace f encIn encOut :=
  .of_tidy h

/-- **Plain and tidy computability within polynomial space agree.** -/
theorem computableInPolySpace_iff_computableTidilyInPolySpace :
    ComputableInPolySpace f encIn encOut ↔ ComputableTidilyInPolySpace f encIn encOut :=
  ⟨ComputableInPolySpace.tidy, ComputableInPolySpace.of_tidy⟩

namespace ComputableInPolySpace

variable {γ δ : Type} {encMid : β ↪ List Bool} {encD : δ ↪ List Bool}

/-! ### Closure and automation -/

/-- Polynomial time is within polynomial space. -/
@[fun_prop]
theorem of_polyTime (h : ComputableInPolyTime f encIn encOut) :
    ComputableInPolySpace f encIn encOut :=
  .of_tidy (.of_polyTime h.tidy)

/-- The identity. -/
@[fun_prop]
theorem id' : ComputableInPolySpace (fun a : α => a) encIn encIn :=
  .of_tidy .id'

/-- Composition. -/
theorem comp {f : β → γ} {g : α → β} {encOut : γ ↪ List Bool}
    (hf : ComputableInPolySpace f encMid encOut) (hg : ComputableInPolySpace g encIn encMid) :
    ComputableInPolySpace (fun a => f (g a)) encIn encOut :=
  .of_tidy (hf.tidy.comp hg.tidy)

/-- Pairing. -/
@[fun_prop]
theorem prod {g : α → δ} (hf : ComputableInPolySpace f encIn encOut)
    (hg : ComputableInPolySpace g encIn encD) :
    ComputableInPolySpace (fun a => (f a, g a)) encIn (encPair encOut encD) :=
  .of_tidy (hf.tidy.prod hg.tidy)

/-- Case distinction. -/
@[fun_prop]
theorem ite {c : α → Bool} {g : α → β} (hc : ComputableInPolySpace c encIn encBool)
    (hf : ComputableInPolySpace f encIn encOut) (hg : ComputableInPolySpace g encIn encOut) :
    ComputableInPolySpace (fun a => if c a then f a else g a) encIn encOut :=
  .of_tidy (hc.tidy.ite hf.tidy hg.tidy)

/-- Composition, in the form used by `fun_prop`. -/
@[fun_prop]
theorem comp' {f : β → γ} {g : α → β} {encOut : γ ↪ List Bool}
    (hf : ComputableInPolySpace f encMid encOut) (hg : ComputableInPolySpace g encIn encMid) :
    ComputableInPolySpace (fun a => f (g a)) encIn encOut :=
  hf.comp hg

end ComputableInPolySpace

end Turing.MultiTapeTM
