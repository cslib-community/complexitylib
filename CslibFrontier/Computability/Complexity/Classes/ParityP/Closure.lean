/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ParityP
public import CslibFrontier.Foundations.Order.BooleanSubalgebra
import CslibFrontier.Computability.Complexity.Classes.SharpP.Closure

/-!
# Boolean closure of ParityP

## Main definitions

* `Cslib.Complexity.ParityP.booleanSubalgebra`: `⊕P` as a Boolean subalgebra of `Set α`.

## Main results

`ParityP` is closed under union, intersection, set difference, and symmetric difference.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open scoped symmDiff

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- `⊕P` is closed under intersection. -/
theorem inter_mem_ParityP (hA : A ∈ ParityP enc) (hB : B ∈ ParityP enc) :
    A ∩ B ∈ ParityP enc := by
  obtain ⟨f, hf, hA⟩ := mem_ParityP_iff_exists_SharpP.mp hA
  obtain ⟨g, hg, hB⟩ := mem_ParityP_iff_exists_SharpP.mp hB
  exact mem_ParityP_iff_exists_SharpP.mpr
    ⟨f * g, SharpP.mul_mem hf hg, fun a => by simp [hA a, hB a, Nat.odd_mul]⟩

/-- `⊕P` as a Boolean subalgebra of `Set α`. -/
def ParityP.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (ParityP enc) (P_subset_ParityP empty_mem_P) (fun _ => compl_mem_ParityP)
    (fun _ _ => inter_mem_ParityP)

@[simp]
theorem ParityP.coe_booleanSubalgebra :
    (ParityP.booleanSubalgebra enc : Set (Set α)) = ParityP enc := rfl

@[simp]
theorem ParityP.mem_booleanSubalgebra : A ∈ ParityP.booleanSubalgebra enc ↔ A ∈ ParityP enc :=
  Iff.rfl

/-- `⊕P` is closed under union. -/
theorem union_mem_ParityP (hA : A ∈ ParityP enc) (hB : B ∈ ParityP enc) :
    A ∪ B ∈ ParityP enc :=
  (ParityP.booleanSubalgebra enc).sup_mem hA hB

/-- `⊕P` is closed under set difference. -/
theorem diff_mem_ParityP (hA : A ∈ ParityP enc) (hB : B ∈ ParityP enc) :
    A \ B ∈ ParityP enc :=
  (ParityP.booleanSubalgebra enc).sdiff_mem hA hB

/-- `⊕P` is closed under symmetric difference. -/
theorem symmDiff_mem_ParityP (hA : A ∈ ParityP enc) (hB : B ∈ ParityP enc) :
    A ∆ B ∈ ParityP enc :=
  (ParityP.booleanSubalgebra enc).symmDiff_mem hA hB

end Cslib.Complexity
