/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP
public import CslibFrontier.Computability.Complexity.Classes.PH
public import CslibFrontier.Computability.Complexity.Problems.SAT
import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
import CslibFrontier.Computability.Complexity.Classes.PH.KarpLipton
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime

/-!
# If NP is in BPP, the polynomial hierarchy collapses to its second level

By Adleman's theorem [Adleman][Adleman1978], [Arora and Barak, Theorem 7.14][AroraBarak09], a
problem decided with bounded error has circuits of polynomial size
(`Cslib.Circuits.Boolean.BPP_subset_PPolyOn`). So `NP ⊆ BPP` gives `NP ⊆ P/poly`, and the
Karp–Lipton theorem [Karp and Lipton][KarpLipton1980], [Arora and Barak, Theorem
6.19][AroraBarak09] collapses the polynomial hierarchy to `Σ₂`
(`Cslib.Complexity.PH_eq_SigmaP_two_of_SAT`). It suffices that `SAT` itself is in `BPP`.

## Main results

* `Cslib.Complexity.PH_eq_SigmaP_two_of_SAT_mem_BPP`: if `SAT ∈ BPP`, then `PH = Σ₂`.
* `Cslib.Complexity.PH_eq_SigmaP_two_of_NP_subset_BPP`: if `NP ⊆ BPP` for every encoding, then
  `PH = Σ₂`.

## References

* [L. Adleman, *Two theorems on random polynomial time*][Adleman1978]
* [R. M. Karp, R. J. Lipton, *Some connections between nonuniform and uniform complexity
  classes*][KarpLipton1980]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

variable {α : Type} {enc : α ↪ List Bool}

/-- **`SAT ∈ BPP ⇒ PH = Σ₂`** (Karp–Lipton with Adleman's theorem). If satisfiability of formulas
in conjunctive normal form is decided with bounded error, then the polynomial hierarchy collapses
to its second level: `PH = Σ₂`, for every encoding of instances. -/
theorem PH_eq_SigmaP_two_of_SAT_mem_BPP (h : SAT ∈ BPP encCNF) : PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_SAT (Circuits.Boolean.BPP_subset_PPolyOn h)

/-- **`NP ⊆ BPP ⇒ PH = Σ₂`** (Karp–Lipton with Adleman's theorem). If every problem in `NP` is in
`BPP`, for every encoding of its instances, then the polynomial hierarchy collapses to its second
level: `PH = Σ₂`, for every encoding of instances. -/
theorem PH_eq_SigmaP_two_of_NP_subset_BPP
    (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ BPP encB) :
    PH enc = SigmaP 2 enc :=
  PH_eq_SigmaP_two_of_SAT_mem_BPP (h encCNF SAT.mem_NP)

end Cslib.Complexity
