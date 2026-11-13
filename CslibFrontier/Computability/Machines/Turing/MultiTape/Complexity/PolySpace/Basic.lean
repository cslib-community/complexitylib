/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-!
# Polynomial-space certificates

`Turing.MultiTapeTM.ComputableInPolySpace` packages one machine together with a polynomially
bounded space bound. This module converts between that predicate and its explicit certificates:
a polynomially bounded `Turing.MultiTapeTM.ComputableInSpace` bound, in both directions, and plain
polynomial time. It registers `ComputableInPolySpace` with `fun_prop`, with polynomial time as
its first rule. The closure rules (composition, pairing, conditionals and iteration) are in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain`; clients that
need only these constructors import this module instead and avoid that module's build closure.

## Main results

* `Turing.MultiTapeTM.ComputableInPolySpace.of_inSpace`,
  `Turing.MultiTapeTM.ComputableInPolySpace.exists_inSpace`: polynomial space is a polynomially
  bounded `ComputableInSpace` bound.
* `Turing.MultiTapeTM.ComputableInPolySpace.of_polyTime`: plain polynomial time is within
  polynomial space.
-/

public section

namespace Turing.MultiTapeTM

attribute [fun_prop] ComputableInPolySpace

variable {α β : Type} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

namespace ComputableInPolySpace

/-- Build `ComputableInPolySpace` from a polynomially bounded `ComputableInSpace` certificate,
retaining the same realizing machine. -/
theorem of_inSpace {S : α → ℕ} (hS : PolyBounded (fun a => (encIn a).length) S)
    (h : ComputableInSpace f encIn encOut S) :
    ComputableInPolySpace f encIn encOut := by
  obtain ⟨b, hb, hSb⟩ := hS
  obtain ⟨t, c, hc, hl⟩ := h
  have hcS (a : α) : c * (S a + 1) ≤ c * (b (encIn a).length + 1) :=
    Nat.mul_le_mul_left c (Nat.add_le_add_right (hSb a) 1)
  exact ⟨t, fun n => c * (b n + 1), by fun_prop,
    hc.mono (fun _ => le_rfl) hcS, fun a => (hl a).trans (hcS a)⟩

/-- Unpack `ComputableInPolySpace` into a polynomially bounded `ComputableInSpace` certificate,
retaining the same realizing machine. -/
theorem exists_inSpace (h : ComputableInPolySpace f encIn encOut) :
    ∃ S, PolyBounded (fun a => (encIn a).length) S ∧ ComputableInSpace f encIn encOut S := by
  obtain ⟨t, s, hs, hc, hl⟩ := h
  refine ⟨fun a => s (encIn a).length, .of_polynomiallyBounded _ hs, t, 1,
    hc.mono (fun _ => le_rfl) (fun a => by dsimp only; omega),
    fun a => (hl a).trans (by dsimp only; omega)⟩

/-- Polynomial time is within polynomial space. -/
@[fun_prop]
theorem of_polyTime (h : ComputableInPolyTime f encIn encOut) :
    ComputableInPolySpace f encIn encOut := by
  obtain ⟨t, s, ht, hs, hc⟩ := h
  exact ⟨fun a => t (encIn a).length, fun n => t n + s n, by fun_prop,
    hc.mono (fun _ => le_rfl) (fun _ => Nat.le_add_left _ _),
    fun a => (hc.length_le a).trans (Nat.le_add_right _ _)⟩

end ComputableInPolySpace

end Turing.MultiTapeTM
