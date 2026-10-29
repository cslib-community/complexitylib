/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi

/-! Dependent finite tables with unbounded words, an empty alphabet, and no indices. -/

namespace ComplexityTests.DependentTable

open Turing.MultiTapeTM ComputableInPolyTime

private def Entry : Bool → Type
  | false => List Empty
  | true => List Bool

private def encEmpty : Empty ↪ List Bool := ⟨Empty.elim, fun value => value.elim⟩

private noncomputable def encoding : ∀ i, Entry i ↪ List Bool
  | false => encList encEmpty
  | true => encBits

-- This family is inhabited even though one stack's alphabet is empty. Its other stack may grow.
private def table (bits : List Bool) : ∀ i, Entry i
  | false => []
  | true => bits

example : ComputableInPolyTime table encBits (encDPi encoding) := by
  apply dpi
  intro i
  cases i
  · exact const []
  · exact id'

example : ComputableInPolyTime (fun values : ∀ i, Entry i => values true)
    (encDPi encoding) encBits := dpi_apply encoding true

-- Reading the unbounded word, reversing it, and replacing it preserves the empty-alphabet entry.
example : ComputableInPolyTime
    (fun values : ∀ i, Entry i => Function.update values true (values true).reverse)
    (encDPi encoding) (encDPi encoding) :=
  dpi_update id' (bitsReverse.comp (dpi_apply encoding true))

example (bits : List Bool) : Function.update (table bits) true bits.reverse false = [] := by
  exact Function.update_of_ne (β := Entry) (a := false) (a' := true)
    (by decide) bits.reverse (table bits)

-- The finite family with no indices still has one value and requires no entry inhabitant.
example : ComputableInPolyTime
    (fun _ : List Bool => (Empty.elim : Empty → Empty)) encBits
    (encDPi (fun i : Empty => i.elim)) := by
  apply dpi
  intro i
  exact i.elim

example : encDPi (fun i : Empty => i.elim) (Empty.elim : Empty → Empty) = [] := by
  apply List.length_eq_zero_iff.mp
  rw [length_encDPi]
  simp

end ComplexityTests.DependentTable
