/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (test driver)

import Complexity.Computability.Complexity.Classes.Space.Image
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BoundedSearch

open Cslib Cslib.Complexity Cslib.GenericRAM Turing.MultiTapeTM

-- Width zero still has one candidate: the empty word.
example : BooleanSearch.run (fun (_ : Unit × List Bool) => true) ((), 0) = some [] := by decide
example : BooleanSearch.run (fun (_ : Unit × List Bool) => false) ((), 0) = none := by decide
example : BooleanSearch.run (fun p : Unit × List Bool => p.2.all id) ((), 3) =
    some [true, true, true] := by decide

private def shortInputs : Set (List Bool) := {w | w.length ≤ 2}

private theorem shortInputs_mem_PSPACE : shortInputs ∈ PSPACE encBits := by
  apply P_subset_PSPACE
  exact ⟨fun w => decide (w.length ≤ 2), by fun_prop, fun _ => by simp [shortInputs]⟩

-- The image map has collisions; the balance condition holds only on accepted source words.
example : (fun _ : List Bool => []) '' shortInputs ∈ PSPACE encBits := by
  apply bounded_image_mem_PSPACE shortInputs_mem_PSPACE (ComputableInPolyTime.const [])
    (ComputableInPolyTime.const (encOut := encUnary) 2)
  intro w hw
  exact hw

example : (fun _ : List Bool => ([] : List Bool)) [false] =
    (fun _ : List Bool => ([] : List Bool)) [true] := rfl
example : [false] ∈ shortInputs ∧ [true] ∈ shortInputs := by simp [shortInputs]
example : [false, false, false] ∉ shortInputs := by simp [shortInputs]

-- The shared search theorem can retain a test's arbitrary time bound. Its space bound is
-- still the width plus its constant workspace allowance; polynomial-time membership is unused.
example {test : Unit × List Bool → Bool} {time : Unit × List Bool → ℕ}
    (htest : ComputableInO test (encPair encUnit encBits) encBool time (fun _ => 1)) :
    ∃ overhead : Unit × ℕ → ℕ,
      PolyBounded (fun p => (encPair encUnit encUnary p).length) overhead ∧
      ComputableInO (fun p => (BitString.enumList p.2).any fun w => test (p.1, w))
        (encPair encUnit encUnary) encBool
        (fun p => (2 ^ p.2 + 1) * (overhead p +
          listMax (fun w => time (p.1, w)) (BitString.enumList p.2)))
        (fun p => overhead p + 1) := by
  exact htest.exists_bits
    (fun p w hw => le_listMax (f := fun w => time (p.1, w)) (BitString.mem_enumList.mpr hw))
    (fun _ _ _ => le_rfl)
