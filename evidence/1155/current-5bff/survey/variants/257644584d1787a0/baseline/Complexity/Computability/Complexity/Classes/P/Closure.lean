/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Foundations.Order.BooleanSubalgebra
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Boolean closure of P

## Main definitions

* `Cslib.Complexity.P.booleanSubalgebra`: `P` as a Boolean subalgebra of `Set α`.

## Main results

`P` is closed under intersection, union, set difference, and symmetric difference.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM
open scoped symmDiff

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- `P` is closed under intersection. -/
theorem inter_mem_P (hA : A ∈ P enc) (hB : B ∈ P enc) : A ∩ B ∈ P enc := by
  obtain ⟨f, hf, hA⟩ := hA
  obtain ⟨g, hg, hB⟩ := hB
  exact ⟨fun a => f a && g a, by fun_prop, fun a => by simp [hA a, hB a]⟩

/-- `P` as a Boolean subalgebra of `Set α`. -/
def P.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (P enc) empty_mem_P (fun _ => compl_mem_P) (fun _ _ => inter_mem_P)

@[simp]
theorem P.coe_booleanSubalgebra : (P.booleanSubalgebra enc : Set (Set α)) = P enc := rfl

@[simp]
theorem P.mem_booleanSubalgebra : A ∈ P.booleanSubalgebra enc ↔ A ∈ P enc := Iff.rfl

/-- `P` is closed under union. -/
theorem union_mem_P (hA : A ∈ P enc) (hB : B ∈ P enc) : A ∪ B ∈ P enc :=
  (P.booleanSubalgebra enc).sup_mem hA hB

/-- `P` is closed under set difference. -/
theorem diff_mem_P (hA : A ∈ P enc) (hB : B ∈ P enc) : A \ B ∈ P enc :=
  (P.booleanSubalgebra enc).sdiff_mem hA hB

/-- `P` is closed under symmetric difference. -/
theorem symmDiff_mem_P (hA : A ∈ P enc) (hB : B ∈ P enc) : A ∆ B ∈ P enc :=
  (P.booleanSubalgebra enc).symmDiff_mem hA hB

end Cslib.Complexity
