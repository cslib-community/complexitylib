/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: local-only (tests of Complexity.Foundations.Data.Polynomial.StagedJetArithmetic)

import Complexity.Foundations.Data.Polynomial.StagedJetArithmetic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Tests for truncated bivariate jet tables, staged denominator clearing, and integer Cramer
recovery (`Complexity.Foundations.Data.Polynomial.StagedJetArithmetic`). -/

namespace ComplexityTests.StagedJetArithmetic

open Cslib Polynomial

/-! ### 1. Concrete `2 × 2` and `3 × 3` `JetTable` convolution and `ℓ₁` norms -/

/-- `(1 + 2 V + (3 + 4 V) z) * (5 - V + (2 + 3 V) z) ≡ (5 + 9 V) + (17 + 24 V) z`
modulo `(z ^ 2, V ^ 2)`, with strict `ℓ₁`-norm drop `55 < 10 * 11` from truncated high-degree
terms. -/
example :
    let jetA2 : JetTable 2 2 ℤ := JetTable.of ![![1, 2], ![3, 4]]
    let jetB2 : JetTable 2 2 ℤ := JetTable.of ![![5, -1], ![2, 3]]
    jetA2 * jetB2 = JetTable.of ![![5, 9], ![17, 24]] ∧
      jetA2.l1Norm = 10 ∧
      jetB2.l1Norm = 11 ∧
      (jetA2.conv jetB2).l1Norm = 55 ∧
      (jetA2.conv jetB2).l1Norm ≤ jetA2.l1Norm * jetB2.l1Norm := by
  intro jetA2 jetB2
  refine ⟨?_, by decide, by decide, by decide, JetTable.l1Norm_conv_le jetA2 jetB2⟩
  ext j u
  fin_cases j <;> fin_cases u <;> decide

/-- Concrete `3 × 3` convolution and agreement with the bivariate polynomial quotient homomorphism
`JetTable.ofBivarPoly 3 3 : ℤ[V][z] →+* JetTable 3 3 ℤ`. -/
example :
    let jetA3 : JetTable 3 3 ℤ := JetTable.of ![![1, 1, 1], ![2, -1, 0], ![0, 0, 3]]
    let jetB3 : JetTable 3 3 ℤ := JetTable.of ![![2, 1, 0], ![1, 0, 2], ![0, 1, 0]]
    let p : Polynomial (Polynomial ℤ) :=
      C (1 + X + X ^ 2) + C (2 - X) * X + C (C 3 * X ^ 2) * X ^ 2
    let q : Polynomial (Polynomial ℤ) :=
      C (2 + X) + C (1 + C 2 * X ^ 2) * X + C X * X ^ 2
    jetA3 * jetB3 = JetTable.of ![![2, 3, 3], ![5, 1, 2], ![2, 0, 11]] ∧
      JetTable.ofBivarPoly 3 3 (p * q) = JetTable.of ![![2, 3, 3], ![5, 1, 2], ![2, 0, 11]] := by
  intro jetA3 jetB3 p q
  have hmul : jetA3 * jetB3 = JetTable.of ![![2, 3, 3], ![5, 1, 2], ![2, 0, 11]] := by
    ext j u
    fin_cases j <;> fin_cases u <;> decide
  refine ⟨hmul, ?_⟩
  rw [(JetTable.ofBivarPoly 3 3).map_mul p q]
  have hp : JetTable.ofBivarPoly 3 3 p = jetA3 := by
    ext j u
    fin_cases j <;> fin_cases u <;>
      norm_num [-map_pow, -map_mul, -map_add, -map_sub,
        JetTable.ofBivarPoly_apply, JetTable.of_apply, p, jetA3,
        coeff_add, coeff_sub, coeff_C_mul, coeff_C, coeff_X_pow, coeff_X, coeff_one]
  have hq : JetTable.ofBivarPoly 3 3 q = jetB3 := by
    ext j u
    fin_cases j <;> fin_cases u <;>
      norm_num [-map_pow, -map_mul, -map_add,
        JetTable.ofBivarPoly_apply, JetTable.of_apply, q, jetB3,
        coeff_add, coeff_C_mul, coeff_C, coeff_X_pow, coeff_X, coeff_one]
  rw [hp, hq]
  exact hmul

/-- Degenerate `J = 0` or `ℓ = 0` tables form the trivial zero ring with `l1Norm = 0`. -/
example : (1 : JetTable 0 3 ℤ) = 0 ∧ (JetTable.const 7 : JetTable 2 0 ℤ).l1Norm = 0 :=
  ⟨JetTable.ext fun j => j.elim0, by decide⟩

/-! ### 2. Concrete Stage-2 parity factor denominator clearing and `B₁` bound -/

/-- Rational linear jet `L(z) = 1/2 + (3/2) z` cleared by `Δ = 2` (`A_int = 1 + 3 z`), lifted
through `e_0(Y) = 1`, `e_1(Y) = -2 Y` (`ℓ = 2`, `Γ = Δ ^ 3 = 8`). -/
example :
    let L_rat : JetTable 2 2 ℚ := JetTable.of ![![1 / 2, 0], ![3 / 2, 0]]
    let A_int : JetTable 2 2 ℤ := JetTable.of ![![1, 0], ![3, 0]]
    let a : Fin 2 → ℤ := ![1, 0]
    let b : Fin 2 → ℤ := ![0, -2]
    (8 : ℤ) • JetTable.parityFactorJet L_rat a b =
        JetTable.castRingHom ℚ (JetTable.clearedParityFactorJet 2 A_int a b) ∧
      (JetTable.clearedParityFactorJet 2 A_int a b).l1Norm ≤ 2 * 2 * (4 + 2 + 2) ^ 3 := by
  intro L_rat A_int a b
  have hL : (2 : ℤ) • L_rat = JetTable.castRingHom ℚ A_int := by
    ext j u
    fin_cases j <;> fin_cases u <;> norm_num [L_rat, A_int]
  refine ⟨JetTable.cast_clearedParityFactorJet 2 L_rat A_int hL a b, ?_⟩
  exact JetTable.l1Norm_clearedParityFactorJet_le_B1 (B := 4) (E_ℓ := 2)
    (by decide) (fun s => by fin_cases s <;> decide)

/-! ### 3. Concrete integer Cramer recovery for a rational polynomial with non-integer jets -/

/-- `H(X) = 13 + (3/8) X - (5/4) X ^ 2 + (1/8) X ^ 3` has non-integer coefficients and non-integer
order-2 Taylor jets `(49/4, -7/4)` at `t = 1` and `(25/4, -15/4)` at `t = 3`, yet integer value
`H(0) = 13 ≡ 5 (mod 2 ^ 3)`. Clearing by `Ω = 8` at nodes `![1, 3]` gives `D_H = 16`,
`Ω * D_H = 128`, and `N_H = 1664`, recovering `H(0) = 1664 / 128 = 13` and `13 % 8 = 5`. -/
example :
    let testH : ℚ[X] :=
      C 13 + C (3 / 8 : ℚ) * X - C (5 / 4 : ℚ) * X ^ 2 + C (1 / 8 : ℚ) * X ^ 3
    let testScaledJet : Fin 2 → Fin 2 → ℤ := ![![98, -14], ![50, -30]]
    testH.eval 0 = 13 ∧
      (hermiteMatrix ![1, 3] 2).det = 16 ∧
      hermiteCramerNumerator ![1, 3] (by decide) (by decide) testScaledJet = 1664 ∧
      ((8 : ℤ) * (hermiteMatrix ![1, 3] 2).det) ∣
        hermiteCramerNumerator ![1, 3] (by decide) (by decide) testScaledJet ∧
      hermiteCramerNumerator ![1, 3] (by decide) (by decide) testScaledJet /
        ((8 : ℤ) * (hermiteMatrix ![1, 3] 2).det) = 13 ∧
      (hermiteCramerNumerator ![1, 3] (by decide) (by decide) testScaledJet /
        ((8 : ℤ) * (hermiteMatrix ![1, 3] 2).det)) % ((2 : ℤ) ^ 3) = 5 := by
  intro testH testScaledJet
  have hdeg : testH.natDegree < 2 * 2 := by
    dsimp only [testH]
    compute_degree!
  have hzero : testH.eval 0 = ((13 : ℤ) : ℚ) := by
    simp [testH]
  have hjet : ∀ (i : Fin 2) (j : Fin 2),
      (testScaledJet i j : ℚ) =
        (8 : ℚ) * (Polynomial.taylor ((![1, 3] : Fin 2 → ℤ) i : ℚ) testH).coeff j := by
    intro i j
    fin_cases i <;> fin_cases j
    · rw [taylor_coeff_zero]
      norm_num [testScaledJet, testH]
    · rw [taylor_coeff_one]
      norm_num [testScaledJet, testH]
    · rw [taylor_coeff_zero]
      norm_num [testScaledJet, testH]
    · rw [taylor_coeff_one]
      norm_num [testScaledJet, testH]
  have hnodes : Function.Injective (![1, 3] : Fin 2 → ℤ) := by decide
  refine ⟨by simpa using hzero, by decide, by decide,
    mul_det_hermiteMatrix_dvd_hermiteCramerNumerator ![1, 3] (by decide) (by decide)
      8 13 testScaledJet hdeg hzero hjet,
    hermiteCramerNumerator_ediv_eq hnodes (by decide) (by decide) (by decide)
      13 testScaledJet hdeg hzero hjet,
    hermiteCramerNumerator_emod_two_pow_eq (ℓ := 3) hnodes (by decide) (by decide) (by decide)
      13 5 testScaledJet hdeg hzero hjet (by decide) (by decide) (by decide)⟩

end ComplexityTests.StagedJetArithmetic
