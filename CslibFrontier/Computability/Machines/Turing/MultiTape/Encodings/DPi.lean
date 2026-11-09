/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Algebra.BigOperators.Fin

/-!
# Encodings of dependent finite tables

A fixed finite table may store a different type at each index. Encode each entry using its own
encoding and store the resulting words with the existing finite-table encoding `encPi`.

## Main definitions

* `Turing.MultiTapeTM.encDPi`: encode a dependent family over a fixed finite index type.

## Main results

* `Turing.MultiTapeTM.length_encDPi_le`: bound the table from the encoded sizes of its entries.
* `Turing.MultiTapeTM.length_encDPi`: the exact sum of the framed entry sizes.
* `Turing.MultiTapeTM.length_encDPi_update_le`: changing one entry only charges its size growth.

## References

Extends the finite-table encoding in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi`.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {Index : Type} {Value : Index → Type} [Fintype Index]

/-- Encode each entry separately, then store all the resulting words in a finite table. -/
noncomputable def encDPi (enc : ∀ i, Value i ↪ List Bool) : (∀ i, Value i) ↪ List Bool where
  toFun values := encPi encBits (fun i => enc i (values i))
  inj' := by
    intro values others h
    have heq := (encPi encBits).injective h
    funext i
    exact (enc i).injective (congrFun heq i)

@[simp] theorem encDPi_apply (enc : ∀ i, Value i ↪ List Bool) (values : ∀ i, Value i) :
    encDPi enc values = encPi encBits (fun i => enc i (values i)) := rfl

/-- The dependent-table encoding is the sum of its framed entry sizes. -/
theorem length_encDPi (enc : ∀ i, Value i ↪ List Bool) (values : ∀ i, Value i) :
    (encDPi enc values).length = ∑ i, (2 * (enc i (values i)).length + 1) := by
  rw [encDPi_apply, encPi_apply, length_encList]
  simp only [List.map_ofFn, encBits_apply, Function.comp_apply, List.sum_ofFn]
  exact Fintype.sum_equiv (Fintype.equivFin Index).symm _ _ (fun _ => rfl)

/-- The dependent-table encoding charges every entry and its framing. -/
theorem length_encDPi_le (enc : ∀ i, Value i ↪ List Bool) (values : ∀ i, Value i)
    {bound : ℕ} (hbound : ∀ i, (enc i (values i)).length ≤ bound) :
    (encDPi enc values).length ≤ Fintype.card Index * (2 * bound + 1) :=
  length_encPi_le encBits (fun i => enc i (values i)) hbound

/-- Updating one entry grows the full table by at most twice that entry's growth. -/
theorem length_encDPi_update_le [DecidableEq Index]
    (enc : ∀ i, Value i ↪ List Bool) (values : ∀ i, Value i) (i : Index) (value : Value i)
    {growth : ℕ} (hgrowth : (enc i value).length ≤ (enc i (values i)).length + growth) :
    (encDPi enc (Function.update values i value)).length ≤
      (encDPi enc values).length + 2 * growth := by
  rw [length_encDPi, length_encDPi]
  calc
    _ ≤ ∑ j, ((2 * (enc j (values j)).length + 1) +
        if j = i then 2 * growth else 0) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases h : j = i
      · subst j
        simp only [Function.update_self, ite_true]
        omega
      · simp only [Function.update_of_ne h, ite_eq_right h, Nat.add_zero]
        exact le_rfl
    _ = _ := by simp [Finset.sum_add_distrib]

end Turing.MultiTapeTM
