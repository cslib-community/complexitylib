/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

import Complexity.Computability.LogSpaceDerandomization.RowCompression.BoundedCap
import Complexity.Computability.LogSpaceDerandomization.RowCompression.SaturatedRoot
import Complexity.Computability.LogSpaceDerandomization.PolynomialAtomCutoffs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Two-signal saturated output regressions

A concrete output feeds the saturated first signal plus the signed second signal into the
existing polynomial preparatory cutoff, retaining the actual first rank. Its scalar contracts
instantiate the generic relative theorem. The second signal changes the output; arbitrary
large first entries outside singleton usage still close the full rank gate; removing the
bounded common loss premise makes the scalar cap estimate false. No hierarchy environment is
imported. This is a test output, not a normalized estimator.
-/

namespace ComplexityTests.RowCompressionSaturatedRoot

open Cslib Cslib.RowCompression Finset

private noncomputable def output (d v r : ℝ) : ℝ :=
  polynomialPrepRow4 1 (min 1 d + v) r

private theorem output_nonneg (d v r : ℝ) : 0 ≤ output d v r :=
  polynomialPrepRow4_nonneg _ _ _

private theorem output_le_one (d v r : ℝ) : output d v r ≤ 1 :=
  polynomialPrepRow4_le_one _ _ _

private theorem output_saturate (d d' v r : ℝ) (hd : 1 ≤ d) (hd' : 1 ≤ d') :
    output d v r = output d' v r := by
  simp only [output, min_eq_left hd, min_eq_left hd']

private theorem output_gate (d v r : ℝ) (hr : 1 ≤ r) : output d v r = 0 :=
  polynomialPrepRow4_eq_zero_of_rank_ge (by norm_num) (by linarith)

private theorem output_root : ∃ A : ℝ, 0 ≤ A ∧ ∀ d v r d' v' r',
    |output d v r ^ (4⁻¹ : ℝ) - output d' v' r' ^ (4⁻¹ : ℝ)| ≤
      A * (|d - d'| + |v - v'| + |r - r'|) := by
  obtain ⟨A, hA, hroot⟩ := exists_abs_polynomialPrepRow4_root_sub_le (1 : ℝ)
  refine ⟨A, hA, ?_⟩
  intro d v r d' v' r'
  have hmin : |min 1 d - min 1 d'| ≤ |d - d'| := by
    simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (d - d'))] using
      abs_min_sub_min_le_max (1 : ℝ) d 1 d'
  have hadd : |min 1 d + v - (min 1 d' + v')| ≤ |d - d'| + |v - v'| := by
    have heq : min 1 d + v - (min 1 d' + v') = (min 1 d - min 1 d') + (v - v') := by
      ring
    rw [heq]
    exact (abs_add_le _ _).trans (by linarith)
  exact (hroot _ _ _ _).trans (mul_le_mul_of_nonneg_left (by linarith) hA)

/-- Instantiate all scalar contracts for an output using both signals and the padded rank. -/
theorem two_signal_relative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type} (s : Finset ι) (n : ℕ → ℕ) (ρ : ℕ → ℝ)
    (Δ : ℕ → ι → Fin 2 → ℝ) (truth raw₀ loss : ι → Fin 2 → ℝ) (z η : ℝ) (K : ℕ),
    0 < η → η ≤ 1 / 10000 → z ≤ η → 0 < K →
    ∀ (m : ℕ), 0 < m → (∀ i < m, K ≤ n i) → (∀ i < m, ρ i ≤ η) →
    (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |truth y 1| ≤ η / 2) →
    (∀ y ∈ s, ∀ ν, |loss y ν| ≤ η / 2) →
    ∀ (ε : ℕ → ℝ), (∀ i ≤ m, 0 ≤ ε i) →
    (∀ i ≤ m, ∀ y ∈ s,
      clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw₀ i y) ≤ ε i) →
    ∀ y ∈ s,
    |stateRootError output s K
      (iterate s n (fun _ => K) ρ Δ ⟨z, raw₀ + loss⟩ m)
      (iterate s n (fun _ => K) ρ (fun _ => 0) ⟨z, truth + loss⟩ m) y| ≤
      C * prefixErrorBudget ε m := by
  apply exists_iterate_root_bound output output_saturate 1 (by norm_num) ?_
    output_root output_gate (by norm_num)
  intro ι s K a b y
  have hroot (d v r : ℝ) : 0 ≤ output d v r ^ (4⁻¹ : ℝ) ∧
      output d v r ^ (4⁻¹ : ℝ) ≤ 1 :=
    ⟨Real.rpow_nonneg (output_nonneg _ _ _) _,
      Real.rpow_le_one (output_nonneg _ _ _) (output_le_one _ _ _) (by norm_num)⟩
  have ha := hroot (a.row y 0) (a.row y 1) (firstRank s K a.defaultValue a.row)
  have hb := hroot (b.row y 0) (b.row y 1) (firstRank s K b.defaultValue b.row)
  dsimp only [stateRootError]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

-- Changing only the signed second signal changes the actual scalar output.
example : output (3 / 4) 0 0 = 1 ∧ output (3 / 4) (-1 / 4) 0 = 0 := by
  norm_num [output, polynomialPrepRow4, polynomialPrepCutoff4, polynomialRowCutoff4,
    polynomialSwitch4, polynomialTransition4]

-- The second signal is observable even within the comparison's tiny true-signal margin.
example : output (5 / 8) 0 0 ≠ output (5 / 8) (1 / 80000) 0 := by
  norm_num [output, polynomialPrepRow4, polynomialPrepCutoff4, polynomialRowCutoff4,
    polynomialSwitch4, polynomialTransition4, transitionPolynomial4]

private noncomputable def row (D : ℝ) : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![D, 0]]

-- The rows agree on usage {0}; unbounded off-usage truth changes the FULL actual rank/output.
example (D : ℝ) (hD : 1 < D) :
    row D 0 = row 0 0 ∧
    output (row 0 0 0) (row 0 0 1) (firstRank univ 2 0 (row 0)) = 1 ∧
    output (row D 0 0) (row D 0 1) (firstRank univ 2 0 (row D)) = 0 := by
  have hD0 : 0 < D := by linarith
  norm_num [row, firstRank, kthLargest, Fin.univ_succ, filter_insert, filter_singleton,
    hD, hD.le, hD0, not_le.mpr hD, output, polynomialPrepRow4, polynomialPrepCutoff4,
    polynomialRowCutoff4, polynomialSwitch4, polynomialTransition4]

-- A positive output and exact raw prefixes satisfy the small-signal/loss/margin contracts.
example :
    let truth : Fin 2 → Fin 2 → ℝ := ![![3 / 4, 0], ![0, 0]]
    let a : State (Fin 2) := ⟨0, truth⟩
    let actual := iterate univ (fun _ => 2) (fun _ => 2) (fun _ => 0) (fun _ => 0) a 1
    (∀ y ∈ (univ : Finset (Fin 2)), 0 ≤ truth y 0 ∧ |truth y 1| ≤ (1 / 20000) / 2) ∧
    (∀ i ≤ 1, ∀ y ∈ (univ : Finset (Fin 2)),
      clippedError (truth y 0) (truth y 1) (uncompressedRow (fun _ => 0) truth i y) = 0) ∧
    output (actual.row 0 0) (actual.row 0 1)
      (firstRank univ 2 actual.defaultValue actual.row) = 1 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro y _
    fin_cases y <;> norm_num
  · intro i _ y _
    simp [uncompressedRow, clippedError]
  · have huniv : (univ : Finset (Fin 2)) = {0, 1} := by decide
    rw [huniv]
    norm_num [iterate, advance, newDefault, update, threshold, kthLargest, entrySize,
      updateEntry, radius, defaultEntry, firstRank, Fin.univ_succ, filter_insert,
      filter_singleton, output, polynomialPrepRow4, polynomialPrepCutoff4,
      polynomialRowCutoff4, polynomialSwitch4, polynomialTransition4]

-- Relative raw error tends to zero, but common loss -D exposes unit capped discrepancy.
example (D : ℝ) (hD : 8 < D) :
    |(D + 1) - D| ≤ (1 + D) * (1 / (1 + D)) ∧
    ¬ |min 1 (D + 1 + -D) - min 1 (D + -D)| ≤ 9 * (1 / (1 + D)) := by
  have hpos : 0 < 1 + D := by linarith
  constructor
  · field_simp
    norm_num
  · have hsmall : 9 / (1 + D) < 1 := (div_lt_one hpos).mpr (by linarith)
    norm_num [show D + 1 + -D = 1 by ring, show D + -D = 0 by ring]
    simp only [div_eq_mul_inv] at hsmall
    linarith

end ComplexityTests.RowCompressionSaturatedRoot
