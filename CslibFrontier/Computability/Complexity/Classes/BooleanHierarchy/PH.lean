/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BooleanHierarchy
public import CslibFrontier.Computability.Complexity.Classes.PH.Closure

/-!
# The Boolean hierarchy inside the polynomial hierarchy

The intersection of matching existential and universal PH levels is closed under Boolean
operations. At level two it contains NP, hence every finite difference over NP. This gives
`BooleanHierarchy ⊆ SigmaP 2 ∩ PiP 2`, in particular for DP and coDP, using the existing
exact-length alternating verifiers [Arora and Barak, Chapter 5][AroraBarak09].
It is a containment, not a collapse of either hierarchy; Kadin's collapse theorem is not used.

## Main results

* `diff_mem_SigmaP_inter_PiP`: difference closure of matching PH levels.
* `BooleanHierarchy_subset_SigmaP_two_inter_PiP_two`: the full Boolean hierarchy lies at level two.
* `DP_subset_SigmaP_two_inter_PiP_two`, `coDP_subset_SigmaP_two_inter_PiP_two`: difference classes.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [J.-Y. Cai et al., *The Boolean Hierarchy I: Structural Properties*][CaiEtAl1988]
-/

@[expose] public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool} {A B : Set α} {k : ℕ}

/-- Matching existential and universal PH levels are jointly closed under complement. -/
theorem compl_mem_SigmaP_inter_PiP (hA : A ∈ SigmaP k enc ∩ PiP k enc) :
    Aᶜ ∈ SigmaP k enc ∩ PiP k enc :=
  ⟨compl_mem_SigmaP_of_mem_PiP hA.2, compl_mem_PiP_of_mem_SigmaP hA.1⟩

/-- Taking a difference preserves membership in both matching PH levels. -/
theorem diff_mem_SigmaP_inter_PiP (hA : A ∈ SigmaP k enc ∩ PiP k enc)
    (hB : B ∈ SigmaP k enc ∩ PiP k enc) : A \ B ∈ SigmaP k enc ∩ PiP k enc :=
  ⟨inter_mem_SigmaP hA.1 (compl_mem_SigmaP_of_mem_PiP hB.2),
    inter_mem_PiP hA.2 (compl_mem_PiP_of_mem_SigmaP hB.1)⟩

/-- Every finite Boolean combination of NP languages belongs to both second PH levels. -/
theorem BooleanHierarchy_subset_SigmaP_two_inter_PiP_two :
    BooleanHierarchy enc ⊆ SigmaP 2 enc ∩ PiP 2 enc := by
  apply BooleanHierarchy_subset
  · intro A hA
    have h : A ∈ SigmaP 1 enc := SigmaP_one (enc := enc) ▸ hA
    exact ⟨SigmaP_subset_SigmaP_succ 1 h, SigmaP_subset_PiP_succ 1 h⟩
  · exact fun _ hA _ hB => diff_mem_SigmaP_inter_PiP hA hB

/-- NP minus NP is in both second PH levels. -/
theorem DP_subset_SigmaP_two_inter_PiP_two : DP enc ⊆ SigmaP 2 enc ∩ PiP 2 enc := by
  rw [← BH_two]
  exact (BH_subset_BooleanHierarchy 2).trans BooleanHierarchy_subset_SigmaP_two_inter_PiP_two

/-- The complement difference class is in both second PH levels. -/
theorem coDP_subset_SigmaP_two_inter_PiP_two : coDP enc ⊆ SigmaP 2 enc ∩ PiP 2 enc := by
  intro A hA
  simpa only [compl_compl] using
    compl_mem_SigmaP_inter_PiP (DP_subset_SigmaP_two_inter_PiP_two hA)

end Cslib.Complexity
