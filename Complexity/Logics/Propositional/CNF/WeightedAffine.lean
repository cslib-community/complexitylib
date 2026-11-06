/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.WeightedNormalization
public import Complexity.Computability.PolyTime.Int.Rectangular
import Mathlib.Data.List.GetD

/-!
# Integer affine representation of capped weighted rows

This is the affine conversion used after coefficient capping in
[ChenJiangZhu2027], Section 7.1, Theorem 7.1, PDF p. 23. Positive literals
contribute positive coefficients, negative literals negative coefficients, and
variables outside the support zero. The negative-literal constant is subtracted
from the demand. This conversion preserves every Boolean assignment; it does not
assemble direct cases or establish encoded resource bounds. The existing Gram
selector is applied to this capped matrix and its emitted indices are pulled
back to actual capped rows, with equivalence under computed rational consistency.
-/

public section

namespace Cslib.Logic.PL.WeightedRow

open scoped BigOperators
open Matrix

variable {n d : ℕ}

/-- Actual signed integer coefficient, zero outside the capped row support. -/
@[expose] def Row.coefficient (R : Row (Fin n) d) (i : Fin n) : ℤ :=
  if i ∈ R.support then if R.sign i then R.weight i else -(R.weight i : ℤ) else 0

/-- Constant contributed by the negative literals. -/
@[expose] def Row.negativeConstant (R : Row (Fin n) d) : ℤ :=
  ∑ i ∈ R.support, if R.sign i then 0 else (R.weight i : ℤ)

/-- Right hand side of the affine equation. -/
@[expose] def Row.rhs (R : Row (Fin n) d) : ℤ :=
  R.demand - R.negativeConstant

/-- Materialized integer coefficients in declared-variable order. -/
@[expose] def Row.coefficients (R : Row (Fin n) d) : List ℤ :=
  List.ofFn R.coefficient

/-- The affine value plus the extracted negative constant is the literal value. -/
theorem Row.affine_value (R : Row (Fin n) d) (σ : Fin n → Bool) :
    (∑ i, R.coefficient i * (if σ i then (1 : ℤ) else 0)) +
      R.negativeConstant = (R.value σ : ℤ) := by
  have hc : (∑ i, R.coefficient i * (if σ i then (1 : ℤ) else 0)) =
      ∑ i ∈ R.support, (if R.sign i then (R.weight i : ℤ) else -R.weight i) *
        (if σ i then (1 : ℤ) else 0) := by
    rw [← Finset.sum_subset (Finset.subset_univ R.support) (by
      intro i _ hi
      simp [coefficient, hi])]
    apply Finset.sum_congr rfl
    intro i hi
    simp [coefficient, hi]
  rw [hc]
  simp only [negativeConstant, value, active, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases R.sign i <;> cases σ i <;> simp

/-- Exact equivalence with the actual integer affine equation, on Boolean points. -/
theorem Row.affine_iff (R : Row (Fin n) d) (σ : Fin n → Bool) :
    R.value σ = R.demand ↔
      (∑ i, R.coefficient i * (if σ i then (1 : ℤ) else 0)) = R.rhs := by
  have h := R.affine_value σ
  unfold rhs
  constructor <;> intro he
  · rw [he] at h
    omega
  · have : (R.value σ : ℤ) = R.demand := by omega
    exact_mod_cast this

/-- Retained rows in input order; true rows disappear, rejection is tracked separately. -/
@[expose] def cappedRows : List (Normalized n d) → List (Row (Fin n) d)
  | [] => []
  | .reject :: ns => cappedRows ns
  | .trivial :: ns => cappedRows ns
  | .row R :: ns => R :: cappedRows ns

/-- Rejections cannot be erased semantically; all remaining rows are actual input rows. -/
theorem cappedRows_iff (ns : List (Normalized n d)) (σ : Fin n → Bool) :
    (∀ N ∈ ns, N.Holds σ) ↔
      Normalized.reject ∉ ns ∧ ∀ R ∈ cappedRows ns, R.value σ = R.demand := by
  induction ns with
  | nil => simp [cappedRows]
  | cons N ns ih => cases N <;> simp_all [cappedRows, Normalized.Holds, and_left_comm]

/-- Materialize the actual normalized capped coefficient matrix. -/
@[expose] def cappedMatrix (ns : List (Normalized n d)) : List (List ℤ) :=
  (cappedRows ns).map Row.coefficients

/-- Materialize its matching affine right hand sides. -/
@[expose] def cappedRhs (ns : List (Normalized n d)) : List ℤ :=
  (cappedRows ns).map Row.rhs

/-- Reading the emitted matrix recovers the coefficient of the original capped row. -/
theorem cappedMatrix_entry (ns : List (Normalized n d)) (i : Fin (cappedRows ns).length)
    (j : Fin n) :
    rowEntry (cappedMatrix ns) i j =
      ((cappedRows ns)[i]).coefficient j := by
  simp [cappedMatrix, Row.coefficients, rowEntry,
    List.getD_eq_getElem?_getD, i.isLt, j.isLt]

/-- Boolean solutions of the materialized affine system are exactly the capped-row solutions. -/
theorem cappedMatrix_iff (ns : List (Normalized n d)) (σ : Fin n → Bool) :
    (∀ i : Fin (cappedMatrix ns).length,
      (∑ j : Fin n, rowEntry (cappedMatrix ns) i j *
        (if σ j then (1 : ℤ) else 0)) = (cappedRhs ns).getD i 0) ↔
      ∀ R ∈ cappedRows ns, R.value σ = R.demand := by
  have hlen : (cappedMatrix ns).length = (cappedRows ns).length := by
    simp [cappedMatrix]
  constructor
  · intro h R hR
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hR
    apply (Row.affine_iff _ σ).mpr
    have he := h ⟨i, by omega⟩
    simpa [cappedMatrix, cappedRhs, rowEntry, Row.coefficients,
      List.getD_eq_getElem?_getD, hi] using he
  · intro h i
    have hi : (i : ℕ) < (cappedRows ns).length := by omega
    have he := (Row.affine_iff _ σ).mp (h _ (List.getElem_mem hi))
    simpa [cappedMatrix, cappedRhs, rowEntry, Row.coefficients,
      List.getD_eq_getElem?_getD, hi] using he

open LinearSystem

/-- Execute the existing selector on the actual capped coefficients. -/
@[expose] def cappedBasis (ns : List (Normalized n d)) : List ℕ :=
  gramRowBasis n (cappedMatrix ns)

/-- Each emitted index refers to an original row of the capped list. -/
def cappedIndex (ns : List (Normalized n d)) (i : Fin (cappedBasis ns).length) :
    Fin (cappedRows ns).length :=
  ⟨(cappedBasis ns).getD i 0, by
    have h := gramRowBasis_mem n (cappedMatrix ns) ((cappedBasis ns).getD i 0)
      (by rw [List.getD_eq_getElem _ _ i.isLt]; exact List.getElem_mem i.isLt)
    simpa [cappedMatrix] using h⟩

/-- Pull selected indices back to actual capped rows, without supplied basis advice. -/
@[expose] def selectedCappedRow (ns : List (Normalized n d))
    (i : Fin (cappedBasis ns).length) : Row (Fin n) d :=
  (cappedRows ns)[cappedIndex ns i]

/-- The executed rank test bounds the number of retained rows by the variable count. -/
theorem cappedBasis_length (ns : List (Normalized n d)) : (cappedBasis ns).length ≤ n :=
  gramRowBasis_length n (cappedMatrix ns)

/-- The selected count is the rational rank of the actual capped coefficient matrix. -/
theorem cappedBasis_rank (ns : List (Normalized n d)) :
    (cappedBasis ns).length = Module.finrank ℚ
      (Submodule.span ℚ (Set.range (fun i : Fin (cappedMatrix ns).length =>
        fun j : Fin n => (rowEntry (cappedMatrix ns) i j : ℚ)))) :=
  gramRowBasis_rank n (cappedMatrix ns)

/-- Convert the materialized integer equations to rational Boolean-point equations. -/
theorem cappedMatrix_rat_iff (ns : List (Normalized n d)) (σ : Fin n → Bool) :
    (∀ i : Fin (cappedMatrix ns).length,
      (fun j : Fin n => (rowEntry (cappedMatrix ns) i j : ℚ)) ⬝ᵥ
        (fun j => if σ j then (1 : ℚ) else 0) = (cappedRhs ns).getD i 0) ↔
      ∀ R ∈ cappedRows ns, R.value σ = R.demand := by
  rw [← cappedMatrix_iff]
  constructor <;> intro h i <;> have he := h i <;>
    simp only [dotProduct] at * <;> exact_mod_cast he

/-- Rational consistency is computed; selected original capped rows preserve all Boolean points. -/
theorem selectedCappedRow_iff (ns : List (Normalized n d))
    (hc : rectangularConsistent n (cappedMatrix ns) (cappedRhs ns) = true)
    (σ : Fin n → Bool) :
    (∀ i, (selectedCappedRow ns i).value σ = (selectedCappedRow ns i).demand) ↔
      ∀ R ∈ cappedRows ns, R.value σ = R.demand := by
  obtain ⟨x₀, hx₀⟩ := (rectangularConsistent_correct _ _ _).mp hc
  rw [← cappedMatrix_rat_iff]
  rw [← gramRowBasis_selected_iff n (cappedMatrix ns) (cappedRhs ns) x₀ hx₀]
  apply forall_congr'
  intro i
  rw [Row.affine_iff]
  have he := cappedMatrix_entry ns (cappedIndex ns i)
  have hr : (cappedRhs ns).getD ((cappedBasis ns).getD i 0) 0 =
      (selectedCappedRow ns i).rhs := by
    change (cappedRhs ns).getD (cappedIndex ns i) 0 = _
    simp [cappedRhs, selectedCappedRow, List.getD_eq_getElem?_getD,
      (cappedIndex ns i).isLt]
  change _ ↔ (∑ j : Fin n,
    (rowEntry (cappedMatrix ns) ((cappedBasis ns).getD i 0) j : ℚ) *
      (if σ j then (1 : ℚ) else 0)) = _
  rw [← hr]
  have hh (j : Fin n) : rowEntry (cappedMatrix ns)
      ((cappedBasis ns).getD i 0) j = (selectedCappedRow ns i).coefficient j := he j
  simp only [hh]
  constructor <;> intro h <;> exact_mod_cast h

/-- An inconsistent affine system has no Boolean capped-row solution. -/
theorem capped_inconsistent (ns : List (Normalized n d))
    (hc : rectangularConsistent n (cappedMatrix ns) (cappedRhs ns) = false)
    (σ : Fin n → Bool) : ¬ ∀ R ∈ cappedRows ns, R.value σ = R.demand := by
  intro h
  have ht := (rectangularConsistent_correct n (cappedMatrix ns) (cappedRhs ns)).mpr
    ⟨_, (cappedMatrix_rat_iff ns σ).mpr h⟩
  simp [hc] at ht

/-- Rejection, executed consistency and actual selected rows together preserve all solutions.
No rank, basis or consistency certificate is required as input. -/
theorem normalized_selected_iff (ns : List (Normalized n d)) (σ : Fin n → Bool) :
    (∀ N ∈ ns, N.Holds σ) ↔
      Normalized.reject ∉ ns ∧
      rectangularConsistent n (cappedMatrix ns) (cappedRhs ns) = true ∧
      ∀ i, (selectedCappedRow ns i).value σ = (selectedCappedRow ns i).demand := by
  rw [cappedRows_iff]
  constructor
  · rintro ⟨hn, hs⟩
    have hc := (rectangularConsistent_correct n (cappedMatrix ns) (cappedRhs ns)).mpr
      ⟨_, (cappedMatrix_rat_iff ns σ).mpr hs⟩
    exact ⟨hn, hc, (selectedCappedRow_iff ns hc σ).mpr hs⟩
  · rintro ⟨hn, hc, hs⟩
    exact ⟨hn, (selectedCappedRow_iff ns hc σ).mp hs⟩

end Cslib.Logic.PL.WeightedRow
