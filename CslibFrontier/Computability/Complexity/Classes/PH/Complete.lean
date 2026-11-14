/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
public import CslibFrontier.Computability.Complexity.Reduction.Turing

/-!
# NP-complete languages reducing to their complements

A polynomial-time many-one reduction from an NP-complete language to its complement forces
`coNP ⊆ NP` for every explicit encoding, and hence collapses `PH` to `NP`.
This is the general reduction argument behind Exercise 3 of Chapter 5 of the 2007 draft of
[Arora and Barak][AroraBarak07]. The completeness hypothesis quantifies over all source encodings;
only one reduction on the fixed complete language is required.

Dually, `NP = coNP` at every encoding exactly when a fixed NP-complete language and a fixed
coNP-complete language reduce to each other
(`Cslib.Complexity.NPComplete.NP_eq_coNP_iff_reducible`).
This is the argument of Exercise 7, Chapter 2 of the 2007 draft, for 3SAT and TAUTOLOGY.
Because polynomial-time Turing reductions can negate the oracle answer
(`Cslib.Complexity.PolyTimeTuringReducible.compl_left`), every `coNP`-hard language is `NP`-hard
under polynomial-time Turing reductions (`Cslib.Complexity.coNPHard.npTuringHard`), and every
`NP`-hard language is `coNP`-hard under polynomial-time Turing reductions
(`Cslib.Complexity.NPHard.coNPTuringHard`).
-/

public section

namespace Cslib.Complexity

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {B : Set β}

/-- Hardness for `coNP` under polynomial-time Turing reductions. -/
abbrev coNPTuringHard (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringHard @coNP encB B

/-- Completeness for `coNP` under polynomial-time Turing reductions. -/
abbrev coNPTuringComplete (encB : β ↪ List Bool) (B : Set β) : Prop :=
  PolyTimeTuringComplete @coNP encB B

/-- Every `coNP`-hard problem is `NP`-hard under polynomial-time Turing reductions: to decide
`A ∈ NP`, query the `coNP`-hard oracle on the many-one reduction of `Aᶜ ∈ coNP` and negate the
answer. -/
theorem coNPHard.npTuringHard (hB : coNPHard encB B) : NPTuringHard encB B := by
  intro α enc A hA
  have hAc : Aᶜ ∈ coNP enc := by
    simpa only [coNP, Set.mem_ofPred_eq, compl_compl] using hA
  simpa only [compl_compl] using (hB enc Aᶜ hAc).polyTimeTuringReducible.compl_left

/-- Every `NP`-hard problem is `coNP`-hard under polynomial-time Turing reductions: to decide
`A ∈ coNP`, query the `NP`-hard oracle on the many-one reduction of `Aᶜ ∈ NP` and negate the
answer. -/
theorem NPHard.coNPTuringHard (hB : NPHard encB B) : coNPTuringHard encB B := by
  intro α enc A hA
  simpa only [compl_compl] using (hB enc Aᶜ hA).polyTimeTuringReducible.compl_left

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

/-- **`NP = coNP` through complete languages.** For an NP-complete `B` and a coNP-complete `C`,
`NP = coNP` at every encoding exactly when `B` and `C` reduce to each other in polynomial time.
Only `C ≤ₚ B` is needed for `NP = coNP`. -/
theorem NPComplete.NP_eq_coNP_iff_reducible {γ : Type} {encC : γ ↪ List Bool} {C : Set γ}
    (hB : NPComplete encB B) (hC : coNPComplete encC C) :
    (∀ {δ : Type} (encD : δ ↪ List Bool), NP encD = coNP encD) ↔
      PolyTimeReducible encB encC B C ∧ PolyTimeReducible encC encB C B := by
  refine ⟨fun h => ⟨hC.2 encB B ((h encB).subset hB.1), hB.2 encC C ((h encC).superset hC.1)⟩,
    fun ⟨_, hCB⟩ => ?_⟩
  exact NP_eq_coNP_iff_coNP_subset_NP.mpr fun encD A hA =>
      ((hC.2 encD A hA).trans hCB).mem_NP hB.1

end Cslib.Complexity
