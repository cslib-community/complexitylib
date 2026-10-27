/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Data.Polynomial.ParityAmplifierDegree
import Mathlib.Data.Fintype.Fin

/-!
# Tests for `Complexity.Foundations.Data.Polynomial.ParityAmplifierDegree`

Concrete degree and evaluation checks for `Polynomial.parityFactor` over `R[X]`.
-/

@[expose] public noncomputable section

namespace Polynomial.ParityAmplifierDegreeTests

open Finset

example (L : Fin 2 → ℤ[X]) (hL : ∀ i ∈ (univ : Finset (Fin 2)), (L i).natDegree ≤ 3) :
    (((∏ i ∈ (univ : Finset (Fin 2)), parityFactor 2 (L i)).coeff 1).natDegree ≤ 12) ∧
      ((∏ i ∈ (univ : Finset (Fin 2)), parityFactor 2 (L i)).sumCoeffsBelow 2).natDegree ≤ 12 := by
  exact ⟨(natDegree_coeff_prod_parityFactor_le_of_lt univ 2 L hL (by decide)).trans (by decide),
    (natDegree_sumCoeffsBelow_prod_parityFactor_le univ 2 L hL).trans (by decide)⟩

end Polynomial.ParityAmplifierDegreeTests
