/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Space.Basic
public import Complexity.Computability.Complexity.Classes.Time
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Comparing deterministic time and space classes

Time bounds space linearly, while a halting space-bounded computation can run for at most its
number of readable configurations. These are the encoded-instance inclusions corresponding
to cslib pull request #767; no hierarchy theorem is needed.

## Main results

* `Cslib.Complexity.DTIME_subset_DSPACE`: `DTIME t ⊆ DSPACE t`.
* `Cslib.Complexity.exists_mem_DTIME_of_mem_DSPACE`: a problem in `DSPACE s` lies in
  `DTIME ((n + 2) * 2 ^ (c * s n))` for some machine-dependent constant `c`.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 4.1][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

variable {α : Type*} {enc : α ↪ List Bool} {A : Set α}

/-- **Time bounds space**: a machine visits at most one new cell per work tape and step, so
`DTIME t ⊆ DSPACE t`. -/
theorem DTIME_subset_DSPACE {t : ℕ → ℕ} : DTIME enc t ⊆ DSPACE enc t := by
  rintro A ⟨c₁, c₂, s, hA⟩
  obtain ⟨c, h⟩ := ComputableInTimeAndSpace.exists_space_linear hA
  refine mem_DSPACE_iff.mpr ⟨c * c₁, c * c₂ + c, _, ComputableInTimeAndSpace.mono h
    (fun _ => le_rfl) fun a => ?_⟩
  rw [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- **Space bounds time exponentially** (the inclusion `DSPACE s ⊆ DTIME (2 ^ O(s))` of cslib pull
request #767, for encoded instances): a decider within space `O(s n)` halts within its number of
configurations, `O((n + 2) * 2 ^ (c * s n))` for a constant `c` of the decider. -/
theorem exists_mem_DTIME_of_mem_DSPACE {s : ℕ → ℕ} (h : A ∈ DSPACE enc s) :
    ∃ c, A ∈ DTIME enc fun n => (n + 2) * 2 ^ (c * s n) := by
  obtain ⟨c₁, c₂, t, hA⟩ := h
  obtain ⟨c, h⟩ := ComputableInTimeAndSpace.exists_time_two_pow (s := fun n => c₁ * s n + c₂) hA
  refine ⟨c * c₁, c * 2 ^ (c * c₂), 0, fun n => c₁ * s n + c₂, ComputableInTimeAndSpace.mono h
    (fun a => ?_) fun _ => le_rfl⟩
  dsimp only
  rw [Nat.mul_add, pow_add, ← Nat.mul_assoc c c₁]
  apply le_of_eq
  ring

end Cslib.Complexity
