/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.PH
public import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
public import CslibFrontier.Computability.Complexity.Problems.GraphIsomorphism

import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.GraphNonIsomorphism

/-!
# coNP ⊆ AM collapses the polynomial hierarchy

The theorem of Boppana, Håstad and Zachos [BoppanaHastadZachos1987],
[Arora and Barak, Section 8.2][AroraBarak09]: if `coNP ⊆ AM`, for problems with any encoding of
their instances, then `Σ₂ = Π₂ = AM` and the polynomial hierarchy collapses to its second level,
`PH = Σ₂`. Consequently, if graph isomorphism is `NP`-complete then `PH = Σ₂`, since graph
non-isomorphism is in `AM` (`Cslib.Complexity.GraphNonIsomorphism.mem_AM`).

The proof:

* **`AM` is closed under existential quantification** over polynomially long words
  (`Cslib.Complexity.mem_AM_of_exists`, by the argument of [Babai][Babai1985], in
  `CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Amplification`; the class equality
  `MAM = AM` itself is `Cslib.Complexity.AMGameClass_merlin_arthur_merlin`, in
  `CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.RoundCollapse`).
* A problem in `Σ₂` is the projection of a problem in `Π₁ = coNP` on pairs `(a, w₁)`
  (`Cslib.Complexity.mem_SigmaP_succ_iff`), so
  `coNP ⊆ AM` gives `Σ₂ ⊆ AM` (`Cslib.Complexity.SigmaP_two_subset_AM_of_coNP_subset_AM`), and with
  `AM ⊆ Π₂` (`Cslib.Complexity.AM_subset_PiP_two`), `Σ₂ ⊆ Π₂`, hence `Π₂ ⊆ Σ₂` by complements and
  `PH = Σ₂` (`Cslib.Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`).

## Main results

* `Cslib.Complexity.SigmaP_two_subset_AM_of_coNP_subset_AM`: `coNP ⊆ AM` gives `Σ₂ ⊆ AM`.
* `Cslib.Complexity.PiP_two_subset_SigmaP_two_of_coNP_subset_AM`: `coNP ⊆ AM` gives `Π₂ ⊆ Σ₂`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_coNP_subset_AM`: **Boppana–Håstad–Zachos**.
* `Cslib.Complexity.SigmaP_two_eq_AM_of_coNP_subset_AM`,
  `Cslib.Complexity.PiP_two_eq_SigmaP_two_of_coNP_subset_AM`: `Σ₂ = Π₂ = AM`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_npComplete_GraphIsomorphism`: if graph isomorphism is
  `NP`-complete, then `PH = Σ₂`.

## References

* [R. B. Boppana, J. Håstad, S. Zachos, *Does co-NP have short interactive
  proofs?*][BoppanaHastadZachos1987]
* [L. Babai, *Trading group theory for randomness*][Babai1985]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-! ### The collapse -/

/-- **`coNP ⊆ AM` gives `Σ₂ ⊆ AM`**: a problem in `Σ₂` is the projection of the `Π₁` problem of
pairs `(a, w₁)` that the universal quantifier accepts, which is in `coNP`, hence in `AM`. -/
theorem SigmaP_two_subset_AM_of_coNP_subset_AM
    (h : coNP (encPair enc encBits) ⊆ AM (encPair enc encBits)) : SigmaP 2 enc ⊆ AM enc := by
  intro A hA
  obtain ⟨p, B, hB, rfl⟩ := mem_SigmaP_succ_iff.mp hA
  rw [PiP_one_eq_coNP] at hB
  exact mem_AM_of_exists (h hB) p

/-- If `coNP ⊆ AM` for every encoding, then `Π₂ ⊆ Σ₂`: the complement of a `Π₂` problem is in
`Σ₂ ⊆ AM ⊆ Π₂`. -/
theorem PiP_two_subset_SigmaP_two_of_coNP_subset_AM
    (h : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ AM encB) {β : Type}
    (encB : β ↪ List Bool) : PiP 2 encB ⊆ SigmaP 2 encB := fun _ hA =>
  compl_mem_PiP_iff.mp (AM_subset_PiP_two
    (SigmaP_two_subset_AM_of_coNP_subset_AM (h _) (compl_mem_SigmaP_iff.mpr hA)))

/-- **The Boppana–Håstad–Zachos theorem** [BoppanaHastadZachos1987],
[Arora and Barak, Section 8.2][AroraBarak09]: if `coNP ⊆ AM` for problems with any encoding of
their instances, then the polynomial hierarchy collapses to `Σ₂`. -/
theorem PH_eq_SigmaP_two_of_coNP_subset_AM
    (h : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ AM encB) : PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP (by norm_num) fun encB =>
    PiP_two_subset_SigmaP_two_of_coNP_subset_AM h encB

/-- If `coNP ⊆ AM` for every encoding, then `Σ₂ = AM`. -/
theorem SigmaP_two_eq_AM_of_coNP_subset_AM
    (h : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ AM encB) : SigmaP 2 enc = AM enc :=
  (SigmaP_two_subset_AM_of_coNP_subset_AM (h _)).antisymm
    (AM_subset_PiP_two.trans (PiP_two_subset_SigmaP_two_of_coNP_subset_AM h enc))

/-- If `coNP ⊆ AM` for every encoding, then `Π₂ = Σ₂`. -/
theorem PiP_two_eq_SigmaP_two_of_coNP_subset_AM
    (h : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ AM encB) : PiP 2 enc = SigmaP 2 enc :=
  PiP_eq_SigmaP_of_PiP_subset_SigmaP (PiP_two_subset_SigmaP_two_of_coNP_subset_AM h enc)

/-- **If graph isomorphism is `NP`-complete, then `PH = Σ₂`** [BoppanaHastadZachos1987],
[Arora and Barak, Section 8.2][AroraBarak09]: graph non-isomorphism is then `coNP`-hard, and it
is in `AM`, which is closed under reductions, so `coNP ⊆ AM`. -/
theorem PH_eq_SigmaP_two_of_npComplete_GraphIsomorphism
    (hGI : NPComplete encGraphIsomorphism GraphIsomorphism) : PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_coNP_subset_AM fun encB A hA =>
    (NPHard.compl hGI.2 encB A hA).mem_AM GraphNonIsomorphism.mem_AM

end Cslib.Complexity
