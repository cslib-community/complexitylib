/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-!
# Direct polynomial resource consequences

These rules retain a single realizing machine. Existence of cost and output degrees is obtained
from its actual polynomial clocks; it does not use a higher normal-form calculus.

## Main results

* `ComputableInTimeAndSpace.computableInPolyTime`: polynomial time suffices at arbitrary space.
* `ComputableInPolyTime.exists_degree`: fixed resource and independent output degrees exist.
-/

@[expose] public section
namespace Turing.MultiTapeTM

open Cslib

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- **A polynomial time bound alone suffices.** A function computable by some machine within a time
bound polynomial in the length of the encoded input, with any space bound, is computable in
polynomial time: within `t` steps the machine visits at most `c t + c` work-tape cells. -/
theorem ComputableInTimeAndSpace.computableInPolyTime {t : ℕ → ℕ} {s : α → ℕ}
    (ht : PolynomiallyBounded t)
    (h : ComputableInTimeAndSpace f encIn encOut (fun a => t (encIn a).length) s) :
    ComputableInPolyTime f encIn encOut :=
  let ⟨c, h⟩ := h.exists_space_linear
  ⟨t, fun n => c * t n + c, ht, by fun_prop, h⟩

/-- Every polynomial-time realization has fixed resource and output degrees. The output degree
comes from its clock; it is not identified with its workspace degree. -/
theorem ComputableInPolyTime.exists_degree (h : ComputableInPolyTime f encIn encOut) :
    ∃ d e, ComputableInDegree f encIn encOut d e := by
  obtain ⟨t, s, ht, hs, h⟩ := h
  obtain ⟨ct, dt, ht⟩ := polynomiallyBounded_iff_le.mp ht
  obtain ⟨cs, ds, hs⟩ := polynomiallyBounded_iff_le.mp hs
  have htime : DegreeBounded (fun a => (encIn a).length)
      (fun a => t (encIn a).length) dt := ⟨ct, fun a => ht _⟩
  have hspace : DegreeBounded (fun a => (encIn a).length)
      (fun a => s (encIn a).length) ds := ⟨cs, fun a => hs _⟩
  exact ⟨max dt ds, dt, ⟨⟨_, _, htime.mono_deg (le_max_left _ _),
    hspace.mono_deg (le_max_right _ _), h⟩, htime.mono h.length_le⟩⟩

end Turing.MultiTapeTM
