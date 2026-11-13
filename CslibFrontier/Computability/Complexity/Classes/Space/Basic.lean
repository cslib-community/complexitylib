/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.SpaceInTime
import CslibFrontier.Foundations.Data.Nat.AffineBound

/-!
# Deterministic space classes

`Cslib.Complexity.DSPACE enc s` consists of the problems that some machine with a binary alphabet
and finitely many states decides within space `c₁ * s n + c₂`, for constants `c₁` and `c₂`, on
instances whose encoding under `enc` has length `n`. Space counts visited work-tape cells; the
input tape is read-only and the output tape write-only. The time bound may depend on the input
length, with no prescribed growth rate. By configuration counting this is equivalent to
allowing any halting time bound (`Cslib.Complexity.mem_DSPACE_iff`).

The definition follows the shape proposed in cslib pull request #767, for encoded instances.
The concrete classes expose their `DSPACE` characterizations in `Classes.LogSpace` and
`Classes.Space`.

## Main definitions

* `Cslib.Complexity.DSPACE`: deterministic space classes.

## Main results

* `Cslib.Complexity.mem_DSPACE_iff`: membership with an arbitrary time bound.
* `Cslib.Complexity.DSPACE_mono_of_le_mul_add`: `DSPACE` absorbs constant factors.
* `Cslib.Complexity.DSPACE_mono`, `Cslib.Complexity.DSPACE_mono_of_eventually_le`: monotonicity.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Definition 8.2][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Filter

variable {α : Type*} {enc : α ↪ List Bool} {A : Set α}

/-- The problems decidable within space `O(s n)`, that is `c₁ * s n + c₂` for constants `c₁` and
`c₂`, on instances whose encoding under `enc` has length `n`, by a machine with a binary alphabet
and finitely many states, within some time bound of `n` [Sipser, Definition 8.2][Sipser2013]. -/
def DSPACE (enc : α ↪ List Bool) (s : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ c₁ c₂ : ℕ, ∃ t : ℕ → ℕ,
    DecidableInTimeAndSpace A enc (fun a => t (enc a).length) fun a => c₁ * s (enc a).length + c₂}

/-- **Membership in `DSPACE`** asks for no particular time bound: a machine that halts within the
space bound halts within the number of its configurations, a function of the length of the
encoded instance (`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_time_of_length`). -/
theorem mem_DSPACE_iff {s : ℕ → ℕ} : A ∈ DSPACE enc s ↔
    ∃ c₁ c₂ : ℕ, ∃ t : α → ℕ,
      DecidableInTimeAndSpace A enc t fun a => c₁ * s (enc a).length + c₂ := by
  refine ⟨fun ⟨c₁, c₂, t, h⟩ => ⟨c₁, c₂, _, h⟩, fun ⟨c₁, c₂, t, h⟩ => ?_⟩
  obtain ⟨t', h'⟩ := ComputableInTimeAndSpace.exists_time_of_length (s := fun n => c₁ * s n + c₂) h
  exact ⟨c₁, c₂, t', h'⟩

/-- `DSPACE` absorbs constant factors: a bound `s₁ n ≤ C * s₂ n + C` puts `DSPACE enc s₁` inside
`DSPACE enc s₂`. -/
theorem DSPACE_mono_of_le_mul_add {s₁ s₂ : ℕ → ℕ} {C : ℕ} (h : ∀ n, s₁ n ≤ C * s₂ n + C) :
    DSPACE enc s₁ ⊆ DSPACE enc s₂ := by
  rintro A ⟨c₁, c₂, t, hA⟩
  exact ⟨c₁ * C, c₁ * C + c₂, t, ComputableInTimeAndSpace.mono hA (fun _ => le_rfl)
    fun _ => Nat.mul_add_le_mul_add_of_le_mul_add (h _) c₁ c₂⟩

/-- `DSPACE` is monotone in the space bound. -/
theorem DSPACE_mono {s₁ s₂ : ℕ → ℕ} (h : ∀ n, s₁ n ≤ s₂ n) : DSPACE enc s₁ ⊆ DSPACE enc s₂ :=
  DSPACE_mono_of_le_mul_add (C := 1) fun n => by have := h n; omega

/-- `DSPACE` only depends on the space bound eventually: the finitely many other values are
absorbed by the additive constant. -/
theorem DSPACE_mono_of_eventually_le {s₁ s₂ : ℕ → ℕ} (h : ∀ᶠ n in atTop, s₁ n ≤ s₂ n) :
    DSPACE enc s₁ ⊆ DSPACE enc s₂ :=
  let ⟨_, hC⟩ := Nat.exists_le_mul_add_of_eventually_le h
  DSPACE_mono_of_le_mul_add hC

end Cslib.Complexity
