/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness

/-!
# NP-complete languages reducing to their complements

A polynomial-time many-one reduction from an NP-complete language to its complement forces
`coNP ⊆ NP` for every explicit encoding, and hence collapses `PH` to `NP`.
This is the general reduction argument behind Exercise 3 of Chapter 5 of the 2007 draft of
[Arora and Barak][AroraBarak07]. The completeness hypothesis quantifies over all source encodings;
only one reduction on the fixed complete language is required.
-/

public section

namespace Cslib.Complexity

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {B : Set β}

/-- An NP-complete language reducing to its complement puts every coNP language in NP. -/
theorem NPComplete.coNP_subset_NP_of_reducible_compl (hB : NPComplete encB B)
    (h : PolyTimeReducible encB encB B Bᶜ) : coNP enc ⊆ NP enc := by
  intro A hA
  have hAB : PolyTimeReducible enc encB A Bᶜ := by
    simpa only [compl_compl] using (hB.2 enc Aᶜ hA).compl
  have hBB : PolyTimeReducible encB encB Bᶜ B := by
    simpa only [compl_compl] using h.compl
  exact (hAB.trans hBB).mem_NP hB.1

/-- An NP-complete language reducing to its complement implies NP = coNP at every encoding. -/
theorem NPComplete.NP_eq_coNP_of_reducible_compl (hB : NPComplete encB B)
    (h : PolyTimeReducible encB encB B Bᶜ) : NP enc = coNP enc :=
  NP_eq_coNP_iff_coNP_subset_NP.mpr (fun _ => hB.coNP_subset_NP_of_reducible_compl h) enc

/-- An NP-complete language reducing to its complement collapses PH at every encoding. -/
theorem NPComplete.PH_eq_NP_of_reducible_compl (hB : NPComplete encB B)
    (h : PolyTimeReducible encB encB B Bᶜ) : PH enc = NP enc :=
  PH_eq_NP_of_coNP_subset_NP fun _ => hB.coNP_subset_NP_of_reducible_compl h

end Cslib.Complexity
