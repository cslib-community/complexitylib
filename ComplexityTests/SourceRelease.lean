/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Probability.SourceRelease
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for source release

The examples check the double-counting bound, a sharp `f / u = 2` cost with an environment-
dependent relation and error, and source release through a nonzero concrete correction atom.
-/

namespace ComplexityTests.SourceRelease

open Finset Matrix Cslib
open scoped BigOperators

-- Exactly two of three sources contribute to both targets, whose weights are `3` and `7`.
example : ∑ x : Fin 3, ∑ z ∈ (univ : Finset (Fin 2)) with x ≠ 2, (![3, 7] : Fin 2 → ℝ) z ≤
    2 * ∑ z : Fin 2, (![3, 7] : Fin 2 → ℝ) z := by
  refine sum_sum_filter_le_mul_sum_of_card_le univ univ (fun x _ => x ≠ 2) ?_ ?_
  · intro z _
    fin_cases z <;> norm_num
  · intro z _
    decide

/-- Both the support relation and the error depend on this same two-point environment. -/
private def error (σ : Fin 2) (_ _ : Fin 2) : ℝ := if σ = 0 then 2 else 3

private noncomputable def releasedTableError : ℝ :=
  (2 * (1 / 2))⁻¹ * 𝔼 σ : Fin 2, ∑ x : Fin 2,
    ∑ z ∈ ({z | z = σ} : Finset (Fin 2)) with x = σ,
      ∑ y ∈ ({y | y = 0} : Finset (Fin 2)), |error σ z y| ^ 4

-- The degree bound is one, while the rate change doubles the child's norm power.
example : releasedTableError ≤ 2 * rowNormPow 4 2 1 (fun σ z : Fin 2 => z = σ)
    (fun (_ : Fin 2) (y : Fin 2) => y = 0) error := by
  have h := sourceRelease_le_rowNormPow (s := 4) (N := 2) (u := 1 / 2) (f := 1)
    (X := fun (_ : Fin 2) (_ : Fin 2) => True) (Z := fun σ z => z = σ)
    (Y := fun _ y => y = 0) (by norm_num) (by norm_num) (by norm_num)
    (fun σ x _ => x = σ) (K := 1) (fun σ z _ => by simp [filter_eq']) error
  simpa [releasedTableError] using h

example : releasedTableError = 97 / 2 := by
  norm_num [releasedTableError, error, expect_eq_sum_div_card, sum_filter, Fin.sum_univ_two,
    filter_eq']

example : rowNormPow 4 2 1 (fun σ z : Fin 2 => z = σ)
    (fun (_ : Fin 2) (y : Fin 2) => y = 0) error = 97 / 4 := by
  norm_num [rowNormPow, error, expect_eq_sum_div_card, sum_filter, Fin.sum_univ_two, filter_eq']

-- The vector API uses the same common environment, with no independence assumptions.
example : (2 * (1 / 2) : ℝ)⁻¹ * 𝔼 σ : Fin 2, ∑ x : Fin 2,
      ∑ z ∈ ({z | z = σ} : Finset (Fin 2)) with x = σ, |error σ z 0| ^ 4 ≤
    2 * vertexNormPow 4 2 1 (fun σ z : Fin 2 => z = σ) (fun σ z => error σ z 0) := by
  have h := sourceRelease_le_vertexNormPow (s := 4) (N := 2) (u := 1 / 2) (f := 1)
    (X := fun (_ : Fin 2) (_ : Fin 2) => True) (Z := fun σ z => z = σ)
    (by norm_num) (by norm_num) (by norm_num) (fun σ x _ => x = σ) (K := 1)
    (fun σ z _ => by simp [filter_eq']) (fun σ z => error σ z 0)
  simpa using h

/-! ### A concrete correction atom -/

/-- A single nonzero entry, from vertex `0` to vertex `1`. -/
private def G (x z : Fin 2) : ℝ := if x = 0 ∧ z = 1 then 1 else 0

private noncomputable def score (v _ : ℝ) : ℝ := if v = 0 then 0 else 1

private noncomputable def gate (r : ℝ) : ℝ := if r < 1 then 1 else 0

private abbrev full (_ : Unit) (_ : Fin 2) : Prop := True

private noncomputable def atom (d : Unit × Unit) (x z : Fin 2) : ℝ :=
  correctionAtom score gate 3 2 1 G full full full id (fun _ => 1) (fun _ => 1) (fun _ => 1) d x z

private theorem score_one (v r : ℝ) (hv : id v ≠ 0) (_ : (1 : ℝ) ≠ 0) : score v r = 1 := by
  simpa only [id_eq, score, ite_eq_right_iff, zero_ne_one, imp_false] using hv

private theorem gate_zero (r : ℝ) (hr : 1 ≤ r) : gate r = 0 := by
  exact ite_eq_right (not_lt.mpr hr)

private theorem incoming_one (z : Fin 2) :
    incomingGate score gate 3 2 1 G univ univ z = 1 := by
  have hcard : #{x : Fin 2 | 1 ≤ auxScore score 3 1 G univ x z} < 2 := by
    fin_cases z <;> norm_num [auxScore, score, G, univ_fin2, filter_insert, filter_singleton]
  have hlt : kthLargest 2 univ (fun x => auxScore score 3 1 G univ x z) < 1 := by
    exact lt_of_not_ge fun h => hcard.not_ge ((le_kthLargest_iff (by decide) zero_lt_one).mp h)
  exact ite_eq_left hlt

-- The test is nonzero: the atom keeps the unique edge and its normalizer is one.
private theorem atom_eq (d : Unit × Unit) (x z : Fin 2) : atom d x z = G x z := by
  have hnorm : correctionNormalizer score gate 3 2 1 G full full full (fun _ => 1)
      (fun _ => 1) x z = 1 := by
    simp [correctionNormalizer, correctionPrep, rowGate, full, incoming_one]
  norm_num [atom, correctionAtom, rowGate, full, incoming_one, hnorm]

example : atom ((), ()) 0 1 = 1 := by rw [atom_eq]; norm_num [G]

-- An additional environment coordinate can govern the right error without changing atom seeds.
-- The incoming cap is discharged by the correction-atom theorem, not supplied as an assumption.
example : (2 * (1 / 2) : ℝ)⁻¹ * 𝔼 σ : Fin 2, ∑ x : Fin 2,
      ∑ z ∈ (univ : Finset (Fin 2)) with atom ((), ()) x z ≠ 0,
        ∑ y : Fin 2, |error σ z y| ^ 4 ≤
    4 * rowNormPow 4 2 1 (fun (_ : Fin 2) (_ : Fin 2) => True)
      (fun _ _ => True) error := by
  have h := correctionAtom_sourceRelease_le_rowNormPow (K := 3) (Kc := 2) (s := 4)
    (N := 2) (u := 1 / 2) (f := 1) (I := score) (τ := gate) (Q := id)
    (h := fun _ => 1) (ρ := fun _ => 1) (G := G) (g₀ := fun _ => 1)
    (X := full) (Y := full) (Yt := full) (fun _ : Fin 2 => ((), ())) (fun _ _ => True)
    (by norm_num) (by norm_num) (by norm_num) (by decide) score_one (g := 1) le_rfl gate_zero error
  norm_num [full, atom] at h ⊢
  exact h

example : (2 * (1 / 2) : ℝ)⁻¹ * 𝔼 σ : Fin 2, ∑ x : Fin 2,
      ∑ z ∈ (univ : Finset (Fin 2)) with atom ((), ()) x z ≠ 0, |error σ z 0| ^ 4 ≤
    4 * vertexNormPow 4 2 1 (fun (_ : Fin 2) (_ : Fin 2) => True)
      (fun σ z => error σ z 0) := by
  have h := correctionAtom_sourceRelease_le_vertexNormPow (K := 3) (Kc := 2) (s := 4)
    (N := 2) (u := 1 / 2) (f := 1) (I := score) (τ := gate) (Q := id)
    (h := fun _ => 1) (ρ := fun _ => 1) (G := G) (g₀ := fun _ => 1)
    (X := full) (Y := full) (Yt := full) (fun _ : Fin 2 => ((), ()))
    (by norm_num) (by norm_num) (by norm_num) (by decide) score_one (g := 1) le_rfl gate_zero
    (fun σ z => error σ z 0)
  norm_num [full, atom] at h ⊢
  exact h

-- The analogous vector error has positive mass, equal to `E[2^4, 3^4] = 97/2`.
example : (2 * (1 / 2) : ℝ)⁻¹ * 𝔼 σ : Fin 2, ∑ x : Fin 2,
      ∑ z ∈ (univ : Finset (Fin 2)) with atom ((), ()) x z ≠ 0, |error σ z 0| ^ 4 = 97 / 2 := by
  simp only [atom_eq]
  norm_num [error, G, expect_eq_sum_div_card, sum_filter, Fin.sum_univ_two, filter_eq']

end ComplexityTests.SourceRelease
