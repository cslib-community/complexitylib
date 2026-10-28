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

/-- The empty language in `P` is polynomial-time Turing autoreducible. -/
example : PolyTimeTuringAutoreducible encBits (∅ : Set (List Bool)) :=
  polyTimeTuringAutoreducible_of_mem_P (show (∅ : Set (List Bool)) ∈ P encBits from
    ⟨fun _ => false, by fun_prop, fun _ => by simp⟩)

/-- The universal language `Set.univ` in `P` is polynomial-time Turing autoreducible. -/
example : PolyTimeTuringAutoreducible encBits (Set.univ : Set (List Bool)) :=
  polyTimeTuringAutoreducible_of_mem_P (show (Set.univ : Set (List Bool)) ∈ P encBits from
    ⟨fun _ => true, by fun_prop, fun _ => by simp⟩)

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

/-- The parity language is Turing reducible to itself via its autoreduction. -/
example : PolyTimeTuringReducible encBits encBits paritySet paritySet :=
  paritySet_autoreducible.polyTimeTuringReducible

end ComplexityTests.TuringAutoreducible
