/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.ReplacementDesignBridge
import Mathlib.Tactic.NormNum

/-!
# Tests for `Complexity.Foundations.Combinatorics.ReplacementDesignBridge`

Concrete smoke tests and nonvacuous witnesses for `nodeInt`, `ReplacementDesign.toCountingDesign`,
`threeTermExponent`, `Design.domainExaminationBound_le_mul_exp_threeTermExponent`, and
`exists_countingDesign_of_scopes`.
-/

@[expose] public noncomputable section

namespace Cslib.LinearAlgebra.ReplacementDesignBridgeTests

open Finset Matrix Polynomial
open scoped BigOperators
open Cslib.BalancedSchedules Cslib.ReplacementCounting

/-- Concrete check of `nodeInt` values `{1, 2, 3}` on `Fin 3` and their rational casts to
`nodePoint`. -/
example :
    nodeInt (0 : Fin 3) = 1 ∧
      nodeInt (1 : Fin 3) = 2 ∧
      nodeInt (2 : Fin 3) = 3 ∧
      (∀ t : Fin 3, (nodeInt t : ℚ) = nodePoint t) := by
  refine ⟨by decide, by decide, by decide, cast_nodeInt_rat⟩

/-- Singleton-scope family on `Fin n`, where factor `f : Fin n` has scope `{f}` (`b = 1, w = 1,
M = n`). -/
def singletonScope (n : ℕ) (f : Fin n) : Finset (Fin n) :=
  {f}

theorem sum_card_singletonScope (n : ℕ) :
    (∑ f : Fin n, #(singletonScope n f)) = n := by
  simp [singletonScope]

theorem var_deg_singletonScope (n : ℕ) (v : Fin n) :
    #{f : Fin n | v ∈ singletonScope n f} ≤ 1 := by
  have hEq : univ.filter (fun f : Fin n => v ∈ singletonScope n f) = {v} := by
    ext f
    simp [singletonScope, eq_comm]
  rw [hEq, card_singleton]

/-- Nonvacuous singleton-scope fixture on `n = 16384` variables (`b = 1, w = 1, M = 16384`) at
`Q = 3, r = 2, A₀ = 0, R = 2, τ = 1 / 2` exercising `exists_countingDesign_of_scopes`,
`toCountingDesign`, Lemma 4.6 denominator clearing, and the `ℓ₁` coefficient norm bound. -/
theorem exists_countingDesign_singletonScope {n : ℕ} (hn : n = 16384) (s : Finset (Fin n)) :
    ∃ D : ReplacementDesign (singletonScope n) 3 2 0 2 (1 / 2),
      Nonempty
        (Design (Fin n) s (fun f => {v : Fin n // v ∈ singletonScope n f})
          (fun _ v => v.1) 2 3 2 (2 ^ (2 * 3)) ((1 / 2 : ℚ) : ℝ)) ∧
      D.h * 2 ^ (2 * 3) ≤ 2 * ∑ f : Fin n, #(singletonScope n f) ∧
      (∀ (f : Fin n) (v : {v : Fin n // v ∈ singletonScope n f}) (i : Fin n),
        (varReplacementRowScaledInt 3 2 0 2 D.place (scopeVarOf (singletonScope n)) ⟨f, v⟩ i).map
            (Int.castRingHom ℚ) =
          (commonDenom 3 2 : ℚ) •
            (D.toCountingDesign s (by decide) (by decide) (by decide)
              (by norm_num) (by norm_num)).row f v i) ∧
      (∀ (f : Fin n) (v : {v : Fin n // v ∈ singletonScope n f}),
        (∑ i : Fin n,
          ((varReplacementRowScaledInt 3 2 0 2 D.place
            (scopeVarOf (singletonScope n)) ⟨f, v⟩ i).coeffNorm1 : ℤ)) ≤
          (commonDenom 3 2 : ℤ) * (1 + (1 + 2 ^ 3) * (2 : ℤ) * (4 * (3 : ℤ)) ^ (2 - 1))) := by
  have hcard : #(measurementIndices 3 2 0 2) = 10 := by
    rw [card_measurementIndices_eq]
    decide
  obtain ⟨D, hM, hhD, _, hmap, hnorm⟩ :=
    exists_countingDesign_of_scopes (singletonScope n) s
      (Q := 3) (r := 2) (A₀ := 0) (R := 2) (b := 1) (w := 1) (τ := 1 / 2)
      (by omega) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
      (by omega)
      (var_deg_singletonScope n)
      (fun f => by simp [singletonScope])
      (by rw [sum_card_singletonScope, one_mul])
      (by rw [sum_card_singletonScope]; omega)
      (by omega)
      (by rw [binomTailProb_eq_div 3 2 0 2 (by decide), hcard]; norm_num)
  exact ⟨D, hM, hhD, hmap, hnorm⟩

/-- End-to-end check that the induced `Design` on `singletonScope n` (`n = 16384`) recovers
`targetSum` at `T = 0`, satisfies the sharpened `d * (R - 1)` degree bound, and satisfies the
three-term exponential domain-examination bound of equation (3.16). -/
example {n : ℕ} (hn : n = 16384) (s : Finset (Fin n))
    (Φ : ∀ f : Fin n, MvPolynomial {v : Fin n // v ∈ singletonScope n f} ℚ)
    {d : ℕ} (hd : (liftedFactorProduct s Φ).totalDegree ≤ d)
    (hd_lin : (d : ℝ) ≤ 1 * (Fintype.card (Fin n) : ℝ)) :
    ∃ (D : ReplacementDesign (singletonScope n) 3 2 0 2 (1 / 2)),
      let M := D.toCountingDesign s (by decide) (by decide) (by decide)
        (by norm_num) (by norm_num)
      (M.targetPoly Φ).eval 0 =
        targetSum s (fun f (v : {v : Fin n // v ∈ singletonScope n f}) => v.1) Φ ∧
      (M.targetPoly Φ).natDegree ≤ d * 1 ∧
      0 < threeTermExponent 2 3 2 (2 ^ (2 * 3)) ((1 / 2 : ℚ) : ℝ) ∧
      (∑ t : Fin 3,
          (#{p : Finset (Fin n) × Finset (Fin n) | #p.1 ≤ (d * 2) / 3 ∧ p.2 ⊆ p.1} : ℝ) *
            (2 * (#(M.measurementBox t) : ℝ) *
              ∑ g : Fin 2, (Fintype.card (M.LocalCube t g) : ℝ))) ≤
        2 * ((3 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) *
          Real.exp ((1 + 4) * (Fintype.card (Fin n) : ℝ) *
            threeTermExponent 2 3 2 (2 ^ (2 * 3)) ((1 / 2 : ℚ) : ℝ)) := by
  obtain ⟨D, _, _, _, _⟩ := exists_countingDesign_singletonScope hn s
  let M := D.toCountingDesign s (by decide) (by decide) (by decide) (by norm_num) (by norm_num)
  exact ⟨D, M.eval_zero_targetPoly Φ,
    D.toCountingDesign_natDegree_targetPoly_le_mul_pred s (by decide) (by decide) (by decide)
      (by norm_num) (by norm_num) Φ hd,
    M.threeTermExponent_pos,
    M.domainExaminationBound_div_le_mul_exp_threeTermExponent (by norm_num : (0 : ℝ) ≤ 1) hd_lin⟩

end Cslib.LinearAlgebra.ReplacementDesignBridgeTests
