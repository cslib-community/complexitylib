/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.P
import CslibFrontier.Computability.Complexity.Classes.SharpP.Closure
import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Complexity.Reduction.ManyOne

/-!
# Boolean closure of NP

## Main results

* `Cslib.Complexity.inter_mem_NP`, `Cslib.Complexity.union_mem_NP`, `Cslib.Complexity.ite_mem_NP`:
  `NP` is closed under intersection, union and `P`-guarded `Set.ite`.
* `Cslib.Complexity.inter_mem_coNP`, `Cslib.Complexity.union_mem_coNP`,
  `Cslib.Complexity.ite_mem_coNP`: `coNP` is closed under intersection, union and `P`-guarded
  `Set.ite`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

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

/-- `NP` is closed under `P`-guarded `Set.ite`: `G.ite A B = (A ∩ G) ∪ (B ∩ Gᶜ)`. -/
theorem ite_mem_NP {G : Set α} (hG : G ∈ P enc) (hA : A ∈ NP enc) (hB : B ∈ NP enc) :
    G.ite A B ∈ NP enc := by
  have heq : G.ite A B = A ∩ G ∪ B ∩ Gᶜ := by
    ext a
    simp only [Set.ite, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff]
  exact heq ▸ union_mem_NP (inter_mem_NP hA (P_subset_NP hG))
    (inter_mem_NP hB (P_subset_NP (compl_mem_P hG)))

/-- `coNP` is closed under `P`-guarded `Set.ite`. -/
theorem ite_mem_coNP {G : Set α} (hG : G ∈ P enc) (hA : A ∈ coNP enc) (hB : B ∈ coNP enc) :
    G.ite A B ∈ coNP enc := by
  have heq : (G.ite A B)ᶜ = G.ite Aᶜ Bᶜ := by
    ext a
    by_cases ha : a ∈ G <;>
      simp [Set.ite, ha]
  change (G.ite A B)ᶜ ∈ NP enc
  rw [heq]
  exact ite_mem_NP hG hA hB


end Cslib.Complexity
