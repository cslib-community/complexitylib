/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Basic
public import Cslib.Computability.Circuit.Synthesis

/-!
# Monotone synthesis

The generic synthesis rules specialize to the monotone basis: constants, conjunction and
disjunction each cost one gate, as for the De Morgan basis (`Cslib.Circuits.Synthesis.const`,
`Cslib.Circuits.Synthesis.and`, `Cslib.Circuits.Synthesis.or`).

## Main results

* `Cslib.Circuits.Synthesis.monotone_const`, `Cslib.Circuits.Synthesis.monotone_and`,
  `Cslib.Circuits.Synthesis.monotone_or`: the gates of the monotone basis.
-/

@[expose] public section

namespace Cslib.Circuits.Synthesis

variable {n : ℕ} {s : Set ((Fin n → Bool) → Bool)} {f g : (Fin n → Bool) → Bool} {a b : ℕ}

/-- Monotone constants cost one gate. -/
theorem monotone_const (value : Bool) :
    Synthesis Monotone.interpretation s {fun _ => value} 1 :=
  nullary (I := Monotone.interpretation) (.const value) rfl

/-- A monotone conjunction costs one gate beyond its arguments. -/
theorem monotone_and (hf : Synthesis Monotone.interpretation s {f} a)
    (hg : Synthesis Monotone.interpretation s {g} b) :
    Synthesis Monotone.interpretation s {fun x => f x && g x} (a + b + 1) := by
  simpa [Monotone.interpretation] using hf.binary hg .and

/-- A monotone disjunction costs one gate beyond its arguments. -/
theorem monotone_or (hf : Synthesis Monotone.interpretation s {f} a)
    (hg : Synthesis Monotone.interpretation s {g} b) :
    Synthesis Monotone.interpretation s {fun x => f x || g x} (a + b + 1) := by
  simpa [Monotone.interpretation] using hf.binary hg .or

end Cslib.Circuits.Synthesis
