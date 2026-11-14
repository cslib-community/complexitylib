/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Foundations.BooleanAnalysis.OrDegree
import CslibFrontier.Computability.Circuit.Boolean.ParityNC1

/-!
Regression clients for [AroraBarak07, Chapter 13, Exercises 6 and 7 (PARITY)]: the degree of `OR`
over `GF(q)`, attained by `1 - ∏ᵢ (1 - Xᵢ)` over `GF(3)`, also over `ℤ`, and parity in NC¹.
-/

set_option linter.privateModule false

open Cslib Cslib.BitString MvPolynomial

namespace OrDegreeParityNC1Tests

/-- Over `GF(3)`, the polynomial `1 - ∏ᵢ (1 - Xᵢ)` on `5` variables has degree exactly `5`, and
no polynomial agreeing with `OR` does better. -/
example : (orPoly (Fin 5) (ZMod 3)).totalDegree = 5 := by
  simpa using totalDegree_orPoly (ι := Fin 5) (R := ZMod 3)

example (p : MvPolynomial (Fin 5) (ZMod 3))
    (hp : ∀ x : Fin 5 → Bool, eval (bitPoint x) p = bitVal (ZMod 3) (decide (∃ i, x i = true))) :
    5 ≤ p.totalDegree :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  le_totalDegree_of_eval_eq_or_zmod hp

/-- The lower bound needs no field: over `ℤ` it holds for any number of variables. -/
example {ι : Type} [Fintype ι] (p : MvPolynomial ι ℤ)
    (hp : ∀ x : ι → Bool, eval (bitPoint x) p = bitVal ℤ (decide (∃ i, x i = true))) :
    Fintype.card ι ≤ p.totalDegree :=
  card_le_totalDegree_of_eval_eq_or hp

/-- Parity is in NC¹. -/
example : Language.ofSlices parity ∈ Circuits.Boolean.NC 1 :=
  Circuits.Boolean.parity_mem_NC_one

/-- Exercise 6 §10: `FormulaPoly = NC 1`, so parity has polynomial-size De Morgan formulas both by
leaf count and by operation-node count (`Formula.size`). -/
example :
    Circuits.Boolean.FormulaPoly = Circuits.Boolean.NC 1 ∧
      Language.ofSlices parity ∈ Circuits.Boolean.FormulaPoly ∧
      ∃ (F : ∀ n, Circuits.Formula Circuits.Boolean.signature n) (p : ℕ → ℕ),
        PolynomiallyBounded p ∧ ∀ n, (F n).size ≤ p n ∧
          (F n).Computes Circuits.Boolean.interpretation ((Language.ofSlices parity).slice n) :=
  ⟨Circuits.Boolean.FormulaPoly_eq_NC_one,
    Circuits.Boolean.parity_mem_FormulaPoly,
    Circuits.Boolean.mem_NC_one_iff_exists_formulas_size.mp Circuits.Boolean.parity_mem_NC_one⟩

end OrDegreeParityNC1Tests
