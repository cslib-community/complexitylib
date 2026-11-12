/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.Agreement
import Mathlib.Tactic

/-! Corollaries 1.3 and 1.4 of submission 865 on the first-bit function of two bits. -/

namespace CslibFrontierTests.CircuitAgreement
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Communication

/-- The first bit of a two-bit string, defined everywhere. -/
def firstBit (x : BitString 2) : Option Bool := some (x 0)

/-- As a total function the partial formula depth is the formula depth. -/
example : partialFormulaDepth firstBit = formulaDepth fun x : BitString 2 => x 0 :=
  partialFormulaDepth_some _

/-- Two distinct strings with first bit `1` form an input of `Agr₂(firstBit)` with value `1`. -/
example : agreement 2 firstBit (BitString.blocksEquiv.symm ![![true, false], ![true, true]]) =
    some true := by
  rw [agreement_eq_some_iff, BitString.block_blocksEquiv_symm]
  refine ⟨fun i j h => ?_, fun i => by fin_cases i <;> rfl⟩
  fin_cases i <;> fin_cases j <;> simp_all [funext_iff, Fin.forall_fin_two]

/-- Two equal strings are outside the domain of `Agr₂(firstBit)`. -/
example : agreement 2 firstBit (BitString.blocksEquiv.symm ![![true, false], ![true, false]]) =
    none := by
  cases h : agreement 2 firstBit (BitString.blocksEquiv.symm ![![true, false], ![true, false]])
  · rfl
  · rw [agreement_eq_some_iff, BitString.block_blocksEquiv_symm] at h
    exact absurd (h.1 (a₁ := 0) (a₂ := 1) rfl) (by decide)

/-- Corollary 1.3 at `k = 2`, `n = 2`: both directions. -/
example : partialFormulaDepth (agreement 2 firstBit) ≤ partialFormulaDepth firstBit ∧
    partialFormulaDepth firstBit ≤ partialFormulaDepth (agreement 2 firstBit) + 18 * 1 +
      4 * 2 + 3 :=
  ⟨partialFormulaDepth_agreement_le _, by
    simpa [show Nat.clog 2 2 = 1 by decide, show Nat.clog 2 3 = 2 by decide] using
      partialFormulaDepth_le_agreement (k := 2) firstBit⟩

/-- Corollary 1.4 at `k = 2`, `n = 2`; both preimages of `firstBit` have two elements. -/
example : partialFormulaDepth firstBit ≤ 19 * partialFormulaDepth (agreement 2 firstBit) +
    4 * 2 + 3 := by
  have hc (b : Bool) : 2 ≤ Fintype.card {x : BitString 2 // firstBit x = some b} := by
    cases b <;> decide
  simpa [show Nat.clog 2 3 = 2 by decide] using
    partialFormulaDepth_le_mul (k := 2) firstBit (hc true) (hc false)

/-- Corollary 1.4 for equality of bits at `k = 2`. -/
example : Protocol.ecomplexityFun (fun a b : Bool => decide (a = b)) ≤
    19 * Protocol.ecomplexity (OneOut.Relation (k := 2) fun (a b : Bool) z => decide (a = b) = z)
      Set.univ Set.univ + ((3 * Nat.clog 2 (1 + 1) + 4 : ℕ) : ℕ∞) :=
  OneOut.ecomplexityFun_le_mul_oneOut _ (by simp) (by simp) (by simp) (by simp)

end CslibFrontierTests.CircuitAgreement
