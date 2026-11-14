/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
public import CslibFrontier.Computability.Complexity.Classes.PH.Reduction
public import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Computability.Complexity.Problems.TMSigmaSAT

/-!
# Complete problems in the polynomial hierarchy and collapse criteria

A polynomial-time many-one reduction from an NP-complete language to its complement forces
`coNP ⊆ NP` for every explicit encoding, and hence collapses `PH` to `NP`.
This is the general reduction argument behind Exercise 3 of Chapter 5 of the 2007 draft of
[Arora and Barak][AroraBarak07]. The completeness hypothesis quantifies over all source encodings;
only one reduction on the fixed complete language is required.

Dually, `NP = coNP` at every encoding exactly when a fixed NP-complete language and a fixed
coNP-complete language reduce to each other
(`Cslib.Complexity.NPComplete.NP_eq_coNP_iff_reducible`).
This is the argument of Exercise 7, Chapter 2 of the 2007 draft, for 3SAT and TAUTOLOGY.

At higher levels, `SigmaPHard k`, `SigmaPComplete k`, `PiPHard k`, `PiPComplete k`, `PHHard` and
`PHComplete` (`CslibFrontier.Computability.Complexity.Classes.PH.Reduction`) specialize
`Cslib.Complexity.PolyTimeHard` and `Cslib.Complexity.PolyTimeComplete` to `Σₖ`, `Πₖ` and `PH`
[Arora and Barak, Claim 5.7 and Chapter 5, Exercise 4][AroraBarak07]:

* Any `PH`-complete language lies in some level `Σₖ`, and reducing every `PH` problem to it pulls
  `PH` into `Σₖ` (`Cslib.Complexity.PHComplete.exists_forall_PH_eq_SigmaP`). In particular, a
  `PH`-hard language in `P` forces `PH = P` (`Cslib.Complexity.PHHard.PH_eq_P_of_mem_P`).
* Conversely, if `PH = Σₖ`, any `Σₖ`-complete language is `PH`-complete
  (`Cslib.Complexity.SigmaPComplete.phComplete_of_forall_PH_eq_SigmaP`). The level-`k` universal
  machine language `Cslib.Complexity.TMSigmaSAT` (`Cslib.Complexity.TMSigmaSAT.sigmaPComplete` in
  `CslibFrontier.Computability.Complexity.Problems.TMSigmaSAT`) is unconditionally `Σₖ`-complete for
  every `k`, yielding the unconditional equivalences
  `(∃ β encB B, PHComplete encB B) ↔ ∃ k, ∀ {α} (enc : α ↪ List Bool), PH enc = SigmaP k enc`
  (`Cslib.Complexity.exists_phComplete_iff_exists_forall_PH_eq_SigmaP`) and
  `(∃ β encB B, PHComplete encB B) ↔ ∃ k, 1 ≤ k ∧ PiP k encBits = SigmaP k encBits`
  (`Cslib.Complexity.exists_phComplete_iff_exists_PiP_encBits_eq_SigmaP`).

## Main results

* `Cslib.Complexity.NPComplete.coNP_subset_NP_of_reducible_compl`,
  `Cslib.Complexity.NPComplete.NP_eq_coNP_of_reducible_compl`,
  `Cslib.Complexity.NPComplete.PH_eq_NP_of_reducible_compl`: a reduction from an NP-complete
  language to its complement collapses `PH` to `NP`.
* `Cslib.Complexity.NPComplete.NP_eq_coNP_iff_reducible`: `NP = coNP` through NP-complete and
  coNP-complete languages.
* `Cslib.Complexity.PHHard.PH_eq_SigmaP_of_mem_SigmaP`,
  `Cslib.Complexity.PHHard.PH_eq_P_of_mem_P`,
  `Cslib.Complexity.PHComplete.exists_forall_PH_eq_SigmaP`,
  `Cslib.Complexity.PHComplete.exists_one_le_forall_PH_eq_SigmaP`,
  `Cslib.Complexity.PHComplete.exists_PiP_encBits_eq_SigmaP`: Claim 5.7 (`PH`-completeness collapses
  `PH`).
* `Cslib.Complexity.SigmaPComplete.phComplete_of_forall_PH_eq_SigmaP`,
  `Cslib.Complexity.exists_phComplete_iff_exists_forall_PH_eq_SigmaP`,
  `Cslib.Complexity.exists_phComplete_iff_exists_PH_encBits_eq_SigmaP`,
  `Cslib.Complexity.exists_phComplete_iff_exists_PiP_encBits_eq_SigmaP`: Chapter 5, Exercise 4 (`PH`
  has a complete language iff `PH = Σₖ` for some `k`).

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft 2007][AroraBarak07]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {B : Set β}

/-! ### NP-complete languages and their complements -/

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

/-! ### PH-completeness and hierarchy collapse (Arora–Barak Claim 5.7 and Chapter 5, Exercise 4) -/

/-- **Arora–Barak Claim 5.7:** if a `PH`-hard problem lies in `Σₖ`, then `PH = Σₖ` for every
instance encoding. -/
theorem PHHard.PH_eq_SigmaP_of_mem_SigmaP {k : ℕ} (hB : PHHard encB B) (hk : B ∈ SigmaP k encB)
    (enc : α ↪ List Bool) : PH enc = SigmaP k enc :=
  Set.Subset.antisymm (fun A hA => (hB enc A hA).mem_SigmaP hk) (SigmaP_subset_PH k)

/-- **Arora–Barak Claim 5.7 (`P` special case):** if a `PH`-hard problem lies in `P`, then
`PH = P` for every instance encoding. -/
theorem PHHard.PH_eq_P_of_mem_P (hB : PHHard encB B) (hP : B ∈ P encB) (enc : α ↪ List Bool) :
    PH enc = P enc := by
  rw [← SigmaP_zero] at hP ⊢
  exact PHHard.PH_eq_SigmaP_of_mem_SigmaP hB hP enc

/-- **Arora–Barak Claim 5.7 (forward direction):** if `B` is `PH`-complete, then the polynomial
hierarchy collapses to some level `Σₖ` at every instance encoding. -/
theorem PHComplete.exists_forall_PH_eq_SigmaP (hB : PHComplete encB B) :
    ∃ k, ∀ {α : Type} (enc : α ↪ List Bool), PH enc = SigmaP k enc := by
  obtain ⟨k, hk⟩ := mem_PH.mp hB.1
  exact ⟨k, fun enc => PHHard.PH_eq_SigmaP_of_mem_SigmaP hB.2 hk enc⟩

/-- **Arora–Barak Claim 5.7 (positive-level form):** if `B` is `PH`-complete, then the polynomial
hierarchy collapses to some level `Σₖ` with `1 ≤ k` at every instance encoding. -/
theorem PHComplete.exists_one_le_forall_PH_eq_SigmaP (hB : PHComplete encB B) :
    ∃ k, 1 ≤ k ∧ ∀ {α : Type} (enc : α ↪ List Bool), PH enc = SigmaP k enc := by
  obtain ⟨k, hk⟩ := hB.exists_forall_PH_eq_SigmaP
  refine ⟨max k 1, le_max_right k 1, fun enc => Set.Subset.antisymm ?_ (SigmaP_subset_PH _)⟩
  exact (hk enc).subset.trans (SigmaP_mono (le_max_left k 1))

/-- **Arora–Barak Claim 5.7 (`Πₖ = Σₖ` form):** if `B` is `PH`-complete, then
`PiP k encBits = SigmaP k encBits` for some `k ≥ 1`. -/
theorem PHComplete.exists_PiP_encBits_eq_SigmaP (hB : PHComplete encB B) :
    ∃ k, 1 ≤ k ∧ PiP k encBits = SigmaP k encBits := by
  obtain ⟨k, hk1, hk⟩ := hB.exists_one_le_forall_PH_eq_SigmaP
  exact ⟨k, hk1, (forall_PH_eq_SigmaP_iff_PiP_encBits_eq_SigmaP hk1).mp hk⟩

/-- **Converse of Claim 5.7 for any `Σₖ`-complete problem:** if `PH = Σₖ` at every encoding, then
every `Σₖ`-complete problem is `PH`-complete. -/
theorem SigmaPComplete.phComplete_of_forall_PH_eq_SigmaP {k : ℕ} (hB : SigmaPComplete k encB B)
    (h : ∀ {α : Type} (enc : α ↪ List Bool), PH enc = SigmaP k enc) : PHComplete encB B :=
  ⟨SigmaP_subset_PH k hB.1, fun _ enc A hA => hB.2 enc A ((h enc).subset hA)⟩

/-- **Converse of Claim 5.7 from fixed-domain `encBits` collapse:** if
`PH encBits = SigmaP k encBits`, then every `Σₖ`-complete problem is `PH`-complete. -/
theorem SigmaPComplete.phComplete_of_PH_encBits_eq_SigmaP {k : ℕ} (hB : SigmaPComplete k encB B)
    (h : PH encBits = SigmaP k encBits) : PHComplete encB B :=
  hB.phComplete_of_forall_PH_eq_SigmaP (PH_encBits_eq_SigmaP_iff.mp h)

/-- **Arora–Barak Claim 5.7 / Chapter 5, Exercise 4:** `PH` has a complete language under
polynomial-time many-one reductions if and only if `PH = Σₖ` for some `k` (at every instance
encoding). The reverse direction uses `TMSigmaSAT k` (`Cslib.Complexity.TMSigmaSAT.sigmaPComplete`).
-/
theorem exists_phComplete_iff_exists_forall_PH_eq_SigmaP :
    (∃ (β : Type) (encB : β ↪ List Bool) (B : Set β), PHComplete encB B) ↔
      ∃ k, ∀ {α : Type} (enc : α ↪ List Bool), PH enc = SigmaP k enc :=
  ⟨fun ⟨_, _, _, hB⟩ => hB.exists_forall_PH_eq_SigmaP,
    fun ⟨k, hk⟩ => ⟨TMSATInstance, encTMSATInstance, TMSigmaSAT k,
      (TMSigmaSAT.sigmaPComplete k).phComplete_of_forall_PH_eq_SigmaP hk⟩⟩

/-- **Arora–Barak Claim 5.7 / Chapter 5, Exercise 4 (fixed-domain `encBits` form):** `PH` has a
complete language under polynomial-time many-one reductions if and only if
`PH encBits = SigmaP k encBits` for some `k`. -/
theorem exists_phComplete_iff_exists_PH_encBits_eq_SigmaP :
    (∃ (β : Type) (encB : β ↪ List Bool) (B : Set β), PHComplete encB B) ↔
      ∃ k, PH encBits = SigmaP k encBits :=
  exists_phComplete_iff_exists_forall_PH_eq_SigmaP.trans
    (exists_congr fun _ => PH_encBits_eq_SigmaP_iff.symm)

/-- **Arora–Barak Claim 5.7 / Chapter 5, Exercise 4 (`Πₖ = Σₖ` form):** `PH` has a complete language
under polynomial-time many-one reductions if and only if `PiP k encBits = SigmaP k encBits` for some
`k ≥ 1`. -/
theorem exists_phComplete_iff_exists_PiP_encBits_eq_SigmaP :
    (∃ (β : Type) (encB : β ↪ List Bool) (B : Set β), PHComplete encB B) ↔
      ∃ k, 1 ≤ k ∧ PiP k encBits = SigmaP k encBits :=
  ⟨fun ⟨_, _, _, hB⟩ => hB.exists_PiP_encBits_eq_SigmaP,
    fun ⟨k, hk1, hk⟩ => exists_phComplete_iff_exists_forall_PH_eq_SigmaP.mpr
      ⟨k, (forall_PH_eq_SigmaP_iff_PiP_encBits_eq_SigmaP hk1).mpr hk⟩⟩

end Cslib.Complexity
