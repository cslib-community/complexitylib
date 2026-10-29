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

/-! ### 2. Concrete Stages 1–3 fixed-denominator clearing and norm bounds -/

/-- Stage 1 (`d_den = 3, k = 2, Δ = 9`): summing the constant monomial `∅` (padded by `3 ^ 2 = 9`)
and the degree-2 monomial `{0, 1}` over `θ₀ = 1/3 + (2/3) z`, `θ₁ = 2/3 - (1/3) z` yields
`11 + 3 z` modulo `z ^ 2` with `ℓ₁` norm `14 ≤ 2 * 3 ^ 2`. -/
example :
    let θ_rat : Fin 2 → JetTable 2 2 ℚ :=
      ![JetTable.of ![![1 / 3, 0], ![2 / 3, 0]], JetTable.of ![![2 / 3, 0], ![-1 / 3, 0]]]
    let θ_int : Fin 2 → JetTable 2 2 ℤ :=
      ![JetTable.of ![![1, 0], ![2, 0]], JetTable.of ![![2, 0], ![-1, 0]]]
    let M : Fin 2 → Finset (Fin 2) := ![∅, Finset.univ]
    JetTable.clearedMonomialSumJet 3 2 θ_int Finset.univ M = JetTable.of ![![11, 0], ![3, 0]] ∧
      ((3 : ℤ) ^ 2) • (∑ m ∈ (Finset.univ : Finset (Fin 2)), ∏ v ∈ M m, θ_rat v) =
        JetTable.castRingHom ℚ (JetTable.clearedMonomialSumJet 3 2 θ_int Finset.univ M) ∧
      (JetTable.clearedMonomialSumJet 3 2 θ_int Finset.univ M).l1Norm ≤ 2 * 3 ^ 2 := by
  intro θ_rat θ_int M
  have hθ : ∀ v, (3 : ℤ) • θ_rat v = JetTable.castRingHom ℚ (θ_int v) := by
    intro v
    ext j u
    fin_cases v <;> fin_cases j <;> fin_cases u <;> norm_num [θ_rat, θ_int]
  refine ⟨?_, JetTable.cast_clearedMonomialSumJet 3 2 θ_rat θ_int hθ Finset.univ M
    (fun m _ => by fin_cases m <;> decide),
    JetTable.l1Norm_clearedMonomialSumJet_le (B₀ := 3) (M₀ := 2) (by decide)
      (fun v => by fin_cases v <;> decide) (by decide) (fun m _ => by fin_cases m <;> decide)⟩
  ext j u
  fin_cases j <;> fin_cases u <;> decide

/-- Stage 2 (`Δ = 2, ℓ = 2, Γ = Δ ^ 3 = 8`): rational linear jet `L(z) = 1/2 + (3/2) z`
(`A_int = 1 + 3 z`), lifted through `e_0(Y) = 1`, `e_1(Y) = -2 Y`. -/
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

/-- Stage 3 (`Ω = 4`, strict intermediate step `t = 2 < 3`): signed prefix accumulator over three
updates truncates strictly to the first two updates with `‖Ω • T_2‖₁ = 6 ≤ 2 * 2 ^ 1 * 3 ^ 1`. -/
example :
    let updates_rat : List (ℤ × JetTable 2 2 ℚ) :=
      [(1, JetTable.of ![![3 / 4, 1 / 4], ![0, 1 / 2]]),
       (-1, JetTable.of ![![1 / 4, 0], ![1 / 2, 1 / 4]]),
       (1, JetTable.of ![![1 / 2, 1 / 4], ![1 / 4, 1 / 4]])]
    let updates_int : List (ℤ × JetTable 2 2 ℤ) :=
      [(1, JetTable.of ![![3, 1], ![0, 2]]),
       (-1, JetTable.of ![![1, 0], ![2, 1]]),
       (1, JetTable.of ![![2, 1], ![1, 1]])]
    JetTable.signedPrefixJet updates_int 2 = JetTable.of ![![2, 1], ![-2, 1]] ∧
      (4 : ℤ) • JetTable.signedPrefixJet updates_rat 2 =
        JetTable.castRingHom ℚ (JetTable.signedPrefixJet updates_int 2) ∧
      (JetTable.signedPrefixJet updates_int 2).l1Norm ≤ 2 * 2 ^ 1 * 3 ^ 1 := by
  intro updates_rat updates_int
  have hrel : ∀ idx (hr : idx < updates_rat.length) (hi : idx < updates_int.length),
      (updates_rat[idx]).1 = (updates_int[idx]).1 ∧
        (4 : ℤ) • (updates_rat[idx]).2 = JetTable.castRingHom ℚ (updates_int[idx]).2 := by
    intro idx hr _
    match idx, hr with
    | 0, _ | 1, _ | 2, _ =>
      refine ⟨rfl, ?_⟩
      ext j u
      fin_cases j <;> fin_cases u <;> norm_num [updates_rat, updates_int]
  refine ⟨?_, JetTable.cast_signedPrefixJet 4 updates_rat updates_int rfl hrel 2,
    JetTable.l1Norm_signedPrefixJet_le (n := 1) (m_test := 1) (B₁ := 3) (M_star := 2)
      updates_int (by decide) (by decide)⟩
  ext j u
  fin_cases j <;> fin_cases u <;> decide

/-! ### 3. Concrete single- and multi-coordinate integer Cramer recovery -/

/-- `H₀(X) = 13 + (3/8) X - (5/4) X ^ 2 + (1/8) X ^ 3` (`H₀(0) = 13`) and
`H₁(X) = -19 - (1/4) X + (3/8) X ^ 2` (`H₁(0) = -19 < 0`) have non-integer coefficients and
non-integer Taylor jets at `![1, 3]`. Clearing by `Ω = 8` recovers `H₀(0) = 1664 / 128 = 13`,
`13 % 8 = 5`, and the `ℓ = 2` negative-sum wraparound `(13 + (-19)) % 4 = (-6) % 4 = 2`. -/
example :
    let testH0 : ℚ[X] :=
      C 13 + C (3 / 8 : ℚ) * X - C (5 / 4 : ℚ) * X ^ 2 + C (1 / 8 : ℚ) * X ^ 3
    let testH1 : ℚ[X] :=
      C (-19) - C (1 / 4 : ℚ) * X + C (3 / 8 : ℚ) * X ^ 2
    let H : Fin 2 → ℚ[X] := ![testH0, testH1]
    let T_int : Fin 2 → JetTable 2 2 ℤ :=
      ![JetTable.of ![![98, -151], ![-14, 4]], JetTable.of ![![50, -131], ![-30, 16]]]
    let jet0 : Fin 2 → Fin 2 → ℤ := fun i j => T_int i j 0
    (H 0).eval 0 = 13 ∧ (H 1).eval 0 = -19 ∧
      (∀ i j s,
        (T_int i j s : ℚ) =
          (8 : ℚ) * (Polynomial.taylor ((![1, 3] : Fin 2 → ℤ) i : ℚ) (H s)).coeff j) ∧
      (hermiteMatrix ![1, 3] 2).det = 16 ∧
      hermiteCramerNumerator ![1, 3] (by decide) (by decide) jet0 = 1664 ∧
      ((8 : ℤ) * (hermiteMatrix ![1, 3] 2).det) ∣
        hermiteCramerNumerator ![1, 3] (by decide) (by decide) jet0 ∧
      hermiteCramerNumerator ![1, 3] (by decide) (by decide) jet0 /
        ((8 : ℤ) * (hermiteMatrix ![1, 3] 2).det) = 13 ∧
      (hermiteCramerNumerator ![1, 3] (by decide) (by decide) jet0 /
        ((8 : ℤ) * (hermiteMatrix ![1, 3] 2).det)) % ((2 : ℤ) ^ 3) = 5 ∧
      (∑ s : Fin 2, hermiteCramerNumerator ![1, 3] (by decide) (by decide)
          (fun i j => T_int i j s) /
        ((8 : ℤ) * (hermiteMatrix ![1, 3] 2).det)) % ((2 : ℤ) ^ 2) = 2 := by
  intro testH0 testH1 H T_int jet0
  have hdeg0 : testH0.natDegree < 2 * 2 :=
    Nat.lt_succ_iff.mpr (by dsimp only [testH0]; compute_degree!)
  have hdeg1 : testH1.natDegree < 2 * 2 :=
    Nat.lt_of_le_of_lt (by dsimp only [testH1]; compute_degree! : testH1.natDegree ≤ 2) (by decide)
  have hdeg : ∀ s : Fin 2, (H s).natDegree < 2 * 2 := by
    intro s
    fin_cases s
    · exact hdeg0
    · exact hdeg1
  have hzero : ∀ s : Fin 2, (H s).eval 0 = ((![13, -19] : Fin 2 → ℤ) s : ℚ) := by
    intro s
    fin_cases s <;> norm_num [H, testH0, testH1]
  have hjet : ∀ (i : Fin 2) (j : Fin 2) (s : Fin 2),
      (T_int i j s : ℚ) =
        (8 : ℚ) * (Polynomial.taylor ((![1, 3] : Fin 2 → ℤ) i : ℚ) (H s)).coeff j := by
    intro i j s
    fin_cases i <;> fin_cases j <;> fin_cases s <;>
      first
      | (rw [taylor_coeff_zero]; norm_num [T_int, H, testH0, testH1])
      | (rw [taylor_coeff_one]; norm_num [T_int, H, testH0, testH1])
  have hnodes : Function.Injective (![1, 3] : Fin 2 → ℤ) := by decide
  refine ⟨by norm_num [H, testH0], by norm_num [H, testH1], hjet, by decide, by decide,
    mul_det_hermiteMatrix_dvd_hermiteCramerNumerator ![1, 3] (by decide) (by decide)
      8 13 jet0 (hdeg 0) (hzero 0) (fun i j => hjet i j 0),
    hermiteCramerNumerator_ediv_eq hnodes (by decide) (by decide) (by decide)
      13 jet0 (hdeg 0) (hzero 0) (fun i j => hjet i j 0),
    hermiteCramerNumerator_emod_two_pow_eq (ℓ := 3) hnodes (by decide) (by decide) (by decide)
      13 5 jet0 (hdeg 0) (hzero 0) (fun i j => hjet i j 0) (by decide) (by decide) (by decide),
    sum_hermiteCramerNumerator_emod_two_pow_eq (ℓ := 2) hnodes (by decide) (by decide) (by decide)
      ![13, -19] 2 T_int H hdeg hzero hjet (by decide) (by decide) (by decide)⟩

end ComplexityTests.StagedJetArithmetic
