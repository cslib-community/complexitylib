/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.AgreementTwo
import CslibFrontier.Foundations.Combinatorics.HalvingCover
import Mathlib.Tactic

/-! Theorem 1.5 of submission 865 and the halving cover, on small examples. -/

namespace CslibFrontierTests.CircuitAgreementTwo
open Cslib Cslib.Circuits Cslib.Circuits.Boolean

/-- The first bit of a two-bit string, defined everywhere: two inputs on each side. -/
def firstBit (x : BitString 2) : Option Bool := some (x 0)

private theorem card_firstBit (b : Bool) :
    2 ≤ Fintype.card {x : BitString 2 // firstBit x = some b} := by
  cases b <;> decide

/-- Theorem 1.5, depth, at `n = 2`. -/
example : partialFormulaDepth firstBit ≤ partialFormulaDepth (agreement 2 firstBit) + 1 + 1 := by
  simpa [show Nat.clog 2 2 = 1 by decide] using
    partialFormulaDepth_le_agreement_two (card_firstBit true) (card_firstBit false)

/-- Theorem 1.5, size, at `n = 2`. -/
example : partialFormulaSize firstBit ≤ 4 * partialFormulaSize (agreement 2 firstBit) := by
  simpa using partialFormulaSize_le_agreement_two (card_firstBit true) (card_firstBit false)

/-- On a total function the partial formula size is the formula size. -/
example : partialFormulaSize firstBit = formulaSize fun x : BitString 2 => x 0 :=
  partialFormulaSize_some _

/-- The halving cover on the identity matrix of `Fin 3`: the zero/one alternative is decided by the
lemma, with at most `⌈log₂ 4⌉ = 2` picks on the side it chooses. -/
example : (∃ cs : List (Fin 3), (∀ c ∈ cs, c ∈ Finset.univ) ∧ cs.length ≤ 2 ∧
      ∀ a ∈ (Finset.univ : Finset (Fin 3)), ∃ c ∈ cs, decide (a = c) = false) ∨
    ∃ rs : List (Fin 3), (∀ a ∈ rs, a ∈ Finset.univ) ∧ rs.length ≤ 2 ∧
      ∀ c ∈ (Finset.univ : Finset (Fin 3)), ∃ a ∈ rs, decide (a = c) = true := by
  simpa [show Nat.clog 2 4 = 2 by decide] using
    Finset.exists_cover_zero_or_one (fun a c : Fin 3 => decide (a = c))
    Finset.univ Finset.univ

/-- The zero cover found by hand on the identity matrix: two columns suffice. -/
example : ∀ a : Fin 3, ∃ c ∈ [(0 : Fin 3), 1], decide (a = c) = false := by decide

end CslibFrontierTests.CircuitAgreementTwo
