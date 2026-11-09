/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
import CslibFrontier.Computability.Complexity.Classes.SharpP.Closure
import CslibFrontier.Computability.Complexity.Reduction.ManyOne

/-!
# Boolean closure of NP

## Main results

`NP` and `coNP` are closed under union and intersection.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α}

/-- `NP` is closed under intersection. -/
theorem inter_mem_NP (hA : A ∈ NP enc) (hB : B ∈ NP enc) : A ∩ B ∈ NP enc := by
  obtain ⟨f, hf, hA⟩ := mem_NP_iff_exists_SharpP.mp hA
  obtain ⟨g, hg, hB⟩ := mem_NP_iff_exists_SharpP.mp hB
  exact mem_NP_iff_exists_SharpP.mpr
    ⟨f * g, SharpP.mul_mem hf hg, fun a => by simp [hA a, hB a]⟩

/-- `NP` is closed under union. -/
theorem union_mem_NP (hA : A ∈ NP enc) (hB : B ∈ NP enc) : A ∪ B ∈ NP enc := by
  obtain ⟨f, hf, hA⟩ := mem_NP_iff_exists_SharpP.mp hA
  obtain ⟨g, hg, hB⟩ := mem_NP_iff_exists_SharpP.mp hB
  exact mem_NP_iff_exists_SharpP.mpr
    ⟨f + g, SharpP.add_mem hf hg, fun a => by simp [hA a, hB a]⟩

/-- `coNP` is closed under intersection. -/
theorem inter_mem_coNP (hA : A ∈ coNP enc) (hB : B ∈ coNP enc) : A ∩ B ∈ coNP enc :=
  compl_inter_mem union_mem_NP hA hB

/-- `coNP` is closed under union. -/
theorem union_mem_coNP (hA : A ∈ coNP enc) (hB : B ∈ coNP enc) : A ∪ B ∈ coNP enc :=
  compl_union_mem inter_mem_NP hA hB


end Cslib.Complexity
