/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Interactive.Sumcheck
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the sumcheck protocol

The polynomial `X₀` in one variable over `ZMod 3` has individual degree `1`. Its hypercube sum is
`0 + 1 = 1`, so the initial claim `(![], 1)` is true and `(![], 0)` is false. The end-to-end
theorems apply: sumcheck with the final check is perfectly complete and has soundness error `1 / 3`.
-/

namespace ComplexityTests.Sumcheck

open Cslib Cslib.Interactive Cslib.Interactive.Sumcheck
open scoped ENNReal

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- The polynomial `X₀` over `ZMod 3`. -/
noncomputable abbrev P : MvPolynomial (Fin 1) (ZMod 3) := MvPolynomial.X 0

/-- `X₀` has individual degree at most `1`. -/
theorem degreeOf_P_le (j : Fin 1) : P.degreeOf j ≤ 1 := by
  rw [MvPolynomial.degreeOf_X]
  split_ifs <;> simp

/-- The hypercube sum of `X₀` is `1`. -/
theorem partialSum_P : partialSum P (![] : Fin 0 → ZMod 3) = 1 := by
  change ∑ b : Fin 1 → Bool, MvPolynomial.eval (point ![] b) P = 1
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp [point]

/-- The true claim. -/
example : rel P 0 (![], 1) () := partialSum_P

/-- A false claim. -/
example : ¬ rel P 0 (![], 0) () := by
  simp [rel, partialSum_P]

/-- Sumcheck with the final check is perfectly complete on this instance. -/
example : (proof 1 P).Complete World.plain (rel P 0) Accept 0 :=
  proof_complete 1 P degreeOf_P_le

/-- Sumcheck with the final check is sound with error `1 / 3` on this instance. -/
example :
    (proof 1 P).verifier.Sound (oP := OracleSpec.empty) World.plain (language (rel P 0)) Set.univ
      (1 / 3) := by
  simpa using proof_sound 1 P degreeOf_P_le

end ComplexityTests.Sumcheck
