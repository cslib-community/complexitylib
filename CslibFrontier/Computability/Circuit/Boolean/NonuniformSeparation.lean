/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.PolynomialTime
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable
import CslibFrontier.Computability.Complexity.Classes.Selective.Ko
import CslibFrontier.Computability.Complexity.Classes.Selective.LeftCut
import CslibFrontier.Computability.Complexity.Classes.PH.SipserLautemann
import CslibFrontier.Computability.Complexity.Classes.Inclusions
import CslibFrontier.Computability.Complexity.Classes.EXP.Decidable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Countable

/-!
# Nonuniform circuits strictly contain bounded-error polynomial time

There are uncountably many languages in `PPoly`, since P-selective sets are uncountable and
Ko's theorem places them in `P/poly`. Only countably many bit languages have a native machine
decider, so some languages in `P/poly` are undecidable. Together with Adleman's inclusion and
decidability of BPP, this proves strict containment on ordinary bit languages.

This formalizes Theorem 6.3 of [Goldreich's February 2007 draft, `r3.pdf`,
PDF p. 9/printed p. 211][Goldreich2007Draft]. The proof reuses the existing inclusion and
countability theorems. BPP decidability follows through its existing containments in PH,
PSPACE and EXP. The source uses undecidability too; no particular separating language or
circuit family is computed here. The strictness statement is for `encBits`, not for arbitrary
encoded finite instance domains. Circuit size counts gates, including constants; this
preserves the polynomial class despite the source's edge-count convention.

## Main results

* `Cslib.Circuits.Boolean.not_countable_PPoly`: nonuniform polynomial-size circuits decide
  uncountably many bit languages.
* `Cslib.Circuits.Boolean.exists_mem_PPoly_not_isDecidable`: some bit language in `P/poly`
  has no native deterministic machine decider.
* `Cslib.Circuits.Boolean.BPP_ssubset_PPoly`: strict containment for ordinary bit languages.
-/

public section

namespace Cslib.Circuits.Boolean

open Complexity Turing.MultiTapeTM

/-- The class of bit languages with polynomial-size circuits is uncountable. -/
theorem not_countable_PPoly : ¬ PPoly.Countable := by
  intro h
  exact not_countable_PSel (h.mono fun A hA =>
    mem_PPolyOn_encBits_iff.mp (PSel_subset_PPolyOn hA))

/-- Some language over bits has polynomial-size circuits and no native machine decider. -/
theorem exists_mem_PPoly_not_isDecidable :
    ∃ A ∈ PPoly, ¬ IsDecidable A encBits := by
  by_contra! h
  exact not_countable_PPoly ((countable_setOf_isDecidable encBits).mono (fun A hA => h A hA))

/-- **BPP is strictly contained in P/poly** on ordinary bit languages, using their identity
encoding. The separating witness is undecidable, not an efficient explicit construction. -/
theorem BPP_ssubset_PPoly : BPP encBits ⊂ PPoly := by
  refine ssubset_iff_subset_not_subset.mpr ⟨?_, ?_⟩
  · intro A hA
    exact mem_PPolyOn_encBits_iff.mp (BPP_subset_PPolyOn hA)
  · intro h
    obtain ⟨A, hA, hdec⟩ := exists_mem_PPoly_not_isDecidable
    exact hdec (isDecidable_of_mem_EXP
      (PSPACE_subset_EXP (PH_subset_PSPACE (BPP_subset_PH (h hA)))))

end Cslib.Circuits.Boolean
