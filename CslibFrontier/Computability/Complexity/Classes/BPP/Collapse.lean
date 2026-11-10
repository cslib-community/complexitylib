/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.P
import CslibFrontier.Computability.Complexity.Classes.PH.Collapse
import CslibFrontier.Computability.Complexity.Classes.PH.SipserLautemann

/-!
# BPP collapses to P if NP does

By the Sipser–Gács–Lautemann theorem [Sipser][Sipser1983], [Lautemann][Lautemann1983],
[Arora and Barak, Theorem 7.15][AroraBarak09], `BPP` lies in the polynomial hierarchy
(`Cslib.Complexity.BPP_subset_PH`), and the hierarchy collapses to `P` when `NP ⊆ P` for every
encoding of instances (`Cslib.Complexity.PH_eq_P_of_NP_subset_P`). Hence `P = NP` implies
`BPP = P`.

## Main results

* `Cslib.Complexity.BPP_eq_P_of_NP_subset_P`: if `NP ⊆ P` for every encoding, then `BPP = P`.

## References

* [M. Sipser, *A complexity theoretic approach to randomness*][Sipser1983]
* [C. Lautemann, *BPP and the polynomial hierarchy*][Lautemann1983]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool}

/-- **If `P = NP` then `BPP = P`**: `BPP` lies in the polynomial hierarchy, which collapses to `P`
when `NP ⊆ P` for every encoding of instances. -/
theorem BPP_eq_P_of_NP_subset_P (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) :
    BPP enc = P enc :=
  Set.Subset.antisymm (fun _ hA => PH_eq_P_of_NP_subset_P h ▸ BPP_subset_PH hA) P_subset_BPP

end Cslib.Complexity
