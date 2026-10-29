/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Reduction.TuringAutoreducible

/-!
# Polynomial-time Turing autoreducibility unit tests

Tests for `PolyTimeTuringAutoreducible`:
* Unconditional Turing autoreducibility of sets in `P`.
* Non-vacuous instances: empty language and full language are Turing autoreducible.
* Fixed-point-free many-one reduction implies Turing autoreducible.
* Autoreduction induces a Turing reduction of `A` to `A`.
-/

open Cslib.Complexity
open Turing.MultiTapeTM

namespace ComplexityTests.TuringAutoreducible

/-- The empty and universal languages in `P` are polynomial-time Turing autoreducible. -/
example :
    PolyTimeTuringAutoreducible encBits (∅ : Set (List Bool)) ∧
    PolyTimeTuringAutoreducible encBits (Set.univ : Set (List Bool)) :=
  ⟨polyTimeTuringAutoreducible_of_mem_P (show (∅ : Set (List Bool)) ∈ P encBits from
      ⟨fun _ => false, by fun_prop, fun _ => by simp⟩),
    polyTimeTuringAutoreducible_of_mem_P (show (Set.univ : Set (List Bool)) ∈ P encBits from
      ⟨fun _ => true, by fun_prop, fun _ => by simp⟩)⟩

/-- The language of even-length bitstrings. -/
def paritySet : Set (List Bool) := {w : List Bool | w.length % 2 = 0}

/-- Prepending two bits is a fixed-point-free length-parity-preserving map, yielding a
Turing autoreduction on the parity language. -/
theorem paritySet_autoreducible : PolyTimeTuringAutoreducible encBits paritySet := by
  have hf : ComputableInPolyTime (fun w : List Bool => false :: false :: w) encBits encBits := by
    fun_prop
  have hne : ∀ w : List Bool, false :: false :: w ≠ w := by
    intro w h
    have : (false :: false :: w).length = w.length := congrArg List.length h
    simp only [List.length_cons] at this
    omega
  have hA : ∀ w : List Bool, (w.length % 2 = 0 ↔ (false :: false :: w).length % 2 = 0) := by
    intro w
    simp only [List.length_cons]
    omega
  exact polyTimeTuringAutoreducible_of_polyTimeReducible_fixedPointFree hf hne hA

/-- A concrete disjunctive truth-table autoreduction on non-empty bitstrings `{[]}ᶜ`,
making 0 queries when `w = []` and querying `true :: w` otherwise, induces a polynomial-time
Turing autoreduction on both `{[]}ᶜ` and `{[]}`. -/
theorem coEmpty_dtt_autoreducible :
    PolyTimeDTTAutoreducible encBits ({[]}ᶜ : Set (List Bool)) := by
  refine ⟨fun w => if w.isEmpty then 0 else 1,
    fun p => true :: p.1,
    by fun_prop, by fun_prop, fun w i hi => ?_, fun w => ?_⟩
  · cases w <;> simp at hi ⊢
  · cases w <;> simp

example :
    PolyTimeTuringReducible encBits encBits paritySet paritySet ∧
    PolyTimeTuringAutoreducible encBits ({[]}ᶜ : Set (List Bool)) ∧
    PolyTimeTuringAutoreducible encBits ({[]} : Set (List Bool)) := by
  have hctt : PolyTimeCTTAutoreducible encBits ({[]} : Set (List Bool)) := by
    simpa using polyTimeDTTAutoreducible_iff_polyTimeCTTAutoreducible_compl.mp
      coEmpty_dtt_autoreducible
  exact ⟨paritySet_autoreducible.polyTimeTuringReducible,
    coEmpty_dtt_autoreducible.polyTimeTuringAutoreducible,
    hctt.polyTimeTuringAutoreducible⟩

end ComplexityTests.TuringAutoreducible
