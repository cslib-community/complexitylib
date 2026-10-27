/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Combinatorics.ReplacementCounting
public import Complexity.Foundations.LinearAlgebra.ReplacementDesign
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Bridge from Section 4 replacement designs to the Section 3 counting design interface

Section 3 of `[OpenAI2026ETH]` (Definition 3.1, Lemma 3.2, and Proposition 3.4, pp. 21–26)
formulates the shared-summary Boolean-cube counting routine around an abstract
`(r, τ, D)`-replacement design (`Cslib.ReplacementCounting.Design`), while Section 4
(Lemmas 4.1–4.7, pp. 26–34) constructs the concrete auxiliary exchange-operator rows, balanced
variable/factor schedules, injective copy placements, measurement matrices, and cleared-denominator
integer polynomials bundled in `Cslib.LinearAlgebra.ReplacementDesign`.

This module bridges the two layers without introducing a third intermediate interface:

1. **Concrete-to-abstract design conversion (`ReplacementDesign.toCountingDesign`):**
   Every `D : Cslib.LinearAlgebra.ReplacementDesign scope Q r A₀ R τ` (with `2 ≤ r`, `1 ≤ R < Q`,
   and `0 < τ ≤ 1 / 2`) canonically induces a
   `Cslib.ReplacementCounting.Design (Fin n) s (fun f => {v : Fin n // v ∈ scope f})
   (fun _ v => v.1) r Q R (r ^ (2 * Q)) (τ : ℝ)` for any finite subset of active factors
   `s : Finset F`:
   - Evaluation nodes `nodeInt t = (t.1 : ℤ) + 1 ∈ {1, …, Q}` lift to `nodePoint t : ℚ`.
   - Variable groups `varGroup t v = D.varAssign v t` have group sets `varGroup D.varAssign t g` of
     cardinality at most `2 * n / r`.
   - Each group `(t, g)` has `D.h * #(measurementIndices Q r A₀ R)` integer measurement rows formed
     by restricting the columns of `varMeasurementMatrix Q r A₀ R ℤ D.place (scopeVarOf scope)` to
     `varGroup D.varAssign t g`, preserving the row `ℓ₁`-bound `≤ r ^ (2 * Q)`, total row bound
     `≤ 2 * τ * n`, and off-group kernel annihilation at `nodePoint t`.
   - Replacement polynomial rows
     `(f, v) ↦ varReplacementRow Q r A₀ R D.place (scopeVarOf scope) ⟨f, v⟩` have degree at most
     `R - 1 ≤ R`, evaluate to `δ_{v.1}` at `T = 0`, and retain the explicit cleared-denominator
     identity and `ℓ₁` coefficient norm bound of Lemma 4.6 (`commonDenom Q R = (R - 1)! * Q!`).

2. **Three-term exponential domain-examination bound (Section 3.5, eq. (3.16), p. 26):**
   `Cslib.ReplacementCounting.threeTermExponent r Q R D τ` defines the three-term counting-cost rate
   `(R / Q) log (2 Q / R) + τ log (2 D + 1) + 1 / r`, and
   `Design.domainExaminationBound_le_mul_exp_threeTermExponent` bounds Proposition 3.4's
   finite-domain examination count by
   `2 Q r exp ((c + 4) n ((R / Q) log (2 Q / R) + τ log (2 D + 1) + 1 / r))` whenever
   `q ≤ c n R / Q`.

3. **Combined Lemma 4.7 → Proposition 3.4 existence theorem (`exists_countingDesign_of_scopes`):**
   Under the algebraic Lemma 4.7 hypotheses on `scope : F → Finset (Fin n)` with `0 < τ ≤ 1 / 2`,
   there exists a concrete `D : Cslib.LinearAlgebra.ReplacementDesign scope Q r A₀ R τ` whose
   induced `D.toCountingDesign` satisfies Proposition 3.4's Hermite jet recovery, restricted-slice
   measurement-fiber factorization, and exponential domain-examination bounds while preserving all
   Lemma 4.5–4.7 incidence, copy, denominator, and coefficient-norm bounds.
   Formal bit-length and native runtime-cost bounds remain separate.

## Main definitions

* `Cslib.LinearAlgebra.nodeInt`: 1-based integer evaluation node `(t.1 : ℤ) + 1`.
* `Cslib.LinearAlgebra.measurementRowEquiv`: canonical equivalence
  `Fin (h * #(measurementIndices Q r A₀ R)) ≃ Fin h × measurementIndices Q r A₀ R`.
* `Cslib.LinearAlgebra.ReplacementDesign.groupMeasurementRow`: group-restricted integer measurement
  rows `C_{t,g}` supported on `varGroup D.varAssign t g`.
* `Cslib.LinearAlgebra.ReplacementDesign.toCountingDesign`: canonical conversion from
  `Cslib.LinearAlgebra.ReplacementDesign` to `Cslib.ReplacementCounting.Design`.
* `Cslib.ReplacementCounting.threeTermExponent`: the three-term counting-cost rate
  `(R / Q) log (2 Q / R) + τ log (2 D + 1) + 1 / r` (eq. (3.16), p. 26; eq. (4.18), p. 34).

## Main results

* `Cslib.LinearAlgebra.ReplacementDesign.toCountingDesign_row_natDegree_le_pred`,
  `Cslib.LinearAlgebra.ReplacementDesign.toCountingDesign_natDegree_targetPoly_le_mul_pred`:
  sharpened `R - 1` degree bounds for Section 4 replacement designs.
* `Cslib.LinearAlgebra.ReplacementDesign.toCountingDesign_map_replacementRowScaledInt`,
  `Cslib.LinearAlgebra.ReplacementDesign.toCountingDesign_sum_coeffNorm1_le`:
  Lemma 4.6 denominator-clearing and `ℓ₁` coefficient norm bounds on the counting design's rows.
* `Cslib.ReplacementCounting.Design.domainExaminationBound_le_mul_exp_threeTermExponent`,
  `Cslib.ReplacementCounting.Design.domainExaminationBound_div_le_mul_exp_threeTermExponent`:
  equation (3.16) exponential bound on Proposition 3.4's finite-domain examination count.
* `Cslib.LinearAlgebra.exists_countingDesign_of_scopes`: Lemma 4.7 existence of a concrete
  `ReplacementDesign` together with its induced `Cslib.ReplacementCounting.Design`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Sections 3.1–3.5 and
  4.1–4.6, Definition 3.1, Lemma 3.2, Proposition 3.4, Lemmas 4.1–4.7, pp. 21–34.
-/

@[expose] public noncomputable section

namespace Cslib.LinearAlgebra

open Finset Matrix Polynomial
open scoped BigOperators
open Cslib.BalancedSchedules

variable {Q r A₀ R n : ℕ}

/-! ### 1. Integer evaluation nodes and group-restricted measurement matrices -/

/-- The 1-based integer evaluation node `t.1 + 1 ∈ {1, …, Q}` associated to `t : Fin Q`
([OpenAI2026ETH], Definition 3.1 and Section 4.3, pp. 21, 29). -/
def nodeInt {Q : ℕ} (t : Fin Q) : ℤ :=
  (t.1 : ℤ) + 1

/-- Casting `nodeInt t` to `ℚ` recovers `nodePoint t`. -/
@[simp]
theorem cast_nodeInt_rat {Q : ℕ} (t : Fin Q) : (nodeInt t : ℚ) = nodePoint t := by
  simp only [nodeInt, nodePoint, Int.cast_add, Int.cast_natCast, Int.cast_one]

/-- `nodeInt` is strictly positive at every `t : Fin Q`. -/
theorem nodeInt_pos {Q : ℕ} (t : Fin Q) : 0 < nodeInt t := by
  unfold nodeInt
  omega

/-- `nodeInt` is nonzero at every `t : Fin Q`. -/
theorem nodeInt_ne_zero {Q : ℕ} (t : Fin Q) : nodeInt t ≠ 0 :=
  (nodeInt_pos t).ne'

/-- `nodeInt : Fin Q → ℤ` is injective. -/
theorem nodeInt_injective (Q : ℕ) : Function.Injective (nodeInt (Q := Q)) := by
  intro t₁ t₂ h
  apply Fin.ext
  unfold nodeInt at h
  omega

/-- Canonical equivalence indexing the `h * #(measurementIndices Q r A₀ R)` rows of the
pulled-back measurement matrix `varMeasurementMatrix` by
`Fin (h * #(measurementIndices Q r A₀ R))`. -/
def measurementRowEquiv (Q r A₀ R h : ℕ) :
    Fin (h * #(measurementIndices Q r A₀ R)) ≃ Fin h × measurementIndices Q r A₀ R :=
  (Fintype.equivFinOfCardEq (by simp [Fintype.card_prod, Fintype.card_coe])).symm

/-- Casting an integer entry of `varMeasurementMatrix` to `ℚ` agrees with the rational entry of
`varMeasurementMatrix`. -/
theorem cast_varMeasurementMatrix_int_eq_rat {A : Type*} [Fintype A] (Q r A₀ R : ℕ) {n h : ℕ}
    (place : A → Fin h × AuxLabel Q r) (varOf : A → Fin n)
    (p : Fin h × measurementIndices Q r A₀ R) (v : Fin n) :
    (varMeasurementMatrix Q r A₀ R ℤ place varOf p v : ℚ) =
      varMeasurementMatrix Q r A₀ R ℚ place varOf p v := by
  simp only [varMeasurementMatrix, measurementMatrix, eigenvec, Int.cast_sum, Int.cast_id]

namespace ReplacementDesign

variable {F : Type*} [Fintype F] {scope : F → Finset (Fin n)} {τ : ℚ}
  (D : ReplacementDesign scope Q r A₀ R τ)

/-- The integer measurement matrix `C_{t,g}` on group `g` at node `t`, obtained by restricting
`varMeasurementMatrix Q r A₀ R ℤ D.place (scopeVarOf scope)` to columns `v` with
`D.varAssign v t = g` and extending by `0` outside `varGroup D.varAssign t g`
([OpenAI2026ETH], Definition 3.1(3) and equation (4.15), pp. 22, 32). -/
def groupMeasurementRow (t : Fin Q) (g : Fin r)
    (k : Fin (D.h * #(measurementIndices Q r A₀ R))) (v : Fin n) : ℤ :=
  if D.varAssign v t = g then
    varMeasurementMatrix Q r A₀ R ℤ D.place (scopeVarOf scope)
      (measurementRowEquiv Q r A₀ R D.h k) v
  else 0

/-- `D.groupMeasurementRow t g k` vanishes outside `{v : Fin n | D.varAssign v t = g}`. -/
theorem groupMeasurementRow_of_ne (t : Fin Q) (g : Fin r)
    (k : Fin (D.h * #(measurementIndices Q r A₀ R))) {v : Fin n} (hv : D.varAssign v t ≠ g) :
    D.groupMeasurementRow t g k v = 0 := by
  simp only [groupMeasurementRow, hv, ↓reduceIte]

/-- On `{v : Fin n | D.varAssign v t = g}`, `D.groupMeasurementRow t g k` agrees with
`varMeasurementMatrix`. -/
theorem groupMeasurementRow_of_eq (t : Fin Q) (g : Fin r)
    (k : Fin (D.h * #(measurementIndices Q r A₀ R))) {v : Fin n} (hv : D.varAssign v t = g) :
    D.groupMeasurementRow t g k v =
      varMeasurementMatrix Q r A₀ R ℤ D.place (scopeVarOf scope)
        (measurementRowEquiv Q r A₀ R D.h k) v := by
  simp only [groupMeasurementRow, hv, ↓reduceIte]

/-- Every row of `D.groupMeasurementRow t g` has `ℓ₁`-norm at most `r ^ (2 * Q)`. -/
theorem sum_natAbs_groupMeasurementRow_le (t : Fin Q) (g : Fin r)
    (k : Fin (D.h * #(measurementIndices Q r A₀ R))) :
    (∑ v : Fin n, (D.groupMeasurementRow t g k v).natAbs) ≤ r ^ (2 * Q) := by
  let p := measurementRowEquiv Q r A₀ R D.h k
  have hle_pt : ∀ v : Fin n,
      (D.groupMeasurementRow t g k v).natAbs ≤
        (varMeasurementMatrix Q r A₀ R ℤ D.place (scopeVarOf scope) p v).natAbs := by
    intro v
    unfold groupMeasurementRow
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  have hsum_le :
      (∑ v : Fin n, (D.groupMeasurementRow t g k v).natAbs) ≤
        ∑ v : Fin n, (varMeasurementMatrix Q r A₀ R ℤ D.place (scopeVarOf scope) p v).natAbs :=
    sum_le_sum fun v _ => hle_pt v
  have hcast :
      ((∑ v : Fin n,
          (varMeasurementMatrix Q r A₀ R ℤ D.place (scopeVarOf scope) p v).natAbs : ℕ) : ℤ) ≤
        (r ^ (2 * Q) : ℤ) := by
    rw [Nat.cast_sum]
    simpa only [Int.natCast_natAbs] using D.sum_abs_measurement_row_le p
  exact hsum_le.trans (Int.ofNat_le.mp hcast)

/-- When `ξ : Fin n → ℚ` vanishes outside `varGroup D.varAssign t g`, pairing `ξ` with row `k` of
`D.groupMeasurementRow t g` equals row `measurementRowEquiv Q r A₀ R D.h k` of
`(varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec ξ`. -/
theorem sum_groupMeasurementRow_mul_eq_mulVec (t : Fin Q) (g : Fin r)
    (k : Fin (D.h * #(measurementIndices Q r A₀ R))) {ξ : Fin n → ℚ}
    (hsupp : ∀ v : Fin n, D.varAssign v t ≠ g → ξ v = 0) :
    (∑ v : Fin n, (D.groupMeasurementRow t g k v : ℚ) * ξ v) =
      (varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec ξ
        (measurementRowEquiv Q r A₀ R D.h k) := by
  simp only [Matrix.mulVec, dotProduct]
  refine sum_congr rfl fun v _ => ?_
  by_cases hv : D.varAssign v t = g
  · rw [D.groupMeasurementRow_of_eq t g k hv, cast_varMeasurementMatrix_int_eq_rat]
  · rw [D.groupMeasurementRow_of_ne t g k hv, hsupp v hv, Int.cast_zero, mul_zero, mul_zero]

/-! ### 2. Canonical conversion `ReplacementDesign → Cslib.ReplacementCounting.Design` -/

/-- Canonical conversion of a concrete Section 4 `ReplacementDesign` into a Section 3
`Cslib.ReplacementCounting.Design` over any active factor subset `s : Finset F`
([OpenAI2026ETH], Definition 3.1 and Lemma 4.7, pp. 21–22, 33–34). -/
def toCountingDesign (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q)
    (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2) :
    Cslib.ReplacementCounting.Design (Fin n) s (fun f => {v : Fin n // v ∈ scope f})
      (fun _ v => v.1) r Q R (r ^ (2 * Q)) (τ : ℝ) where
  two_le_r := hr
  one_le_D := Nat.one_le_pow (2 * Q) r (by omega)
  one_le_R := hR
  R_lt_Q := hRQ
  τ_pos := by exact_mod_cast hτ_pos
  τ_le_half := by
    have h : (τ : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hτ_le
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  nodes := nodeInt
  nodes_injective := nodeInt_injective Q
  nodes_ne_zero := nodeInt_ne_zero
  varGroup t v := D.varAssign v t
  card_varGroup_le t g := by
    have hr_pos : 0 < r := by omega
    have hdiv := D.card_varGroup_le t g
    rw [Fintype.card_fin]
    exact (Nat.le_div_iff_mul_le hr_pos).mp hdiv
  factorGroup := D.factorAssign
  numRows _ _ := D.h * #(measurementIndices Q r A₀ R)
  sum_numRows_le _ := by
    have hsum :
        (∑ _g : Fin r, D.h * #(measurementIndices Q r A₀ R)) =
          r * (D.h * #(measurementIndices Q r A₀ R)) := by
      simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    rw [hsum, Fintype.card_fin]
    exact_mod_cast D.total_measurement_rows_le
  matrix := D.groupMeasurementRow
  matrix_support t g k v hv := D.groupMeasurementRow_of_ne t g k hv
  row_l1_le t g k := D.sum_natAbs_groupMeasurementRow_le t g k
  row f v i := varReplacementRow Q r A₀ R D.place (scopeVarOf scope) ⟨f, v⟩ i
  row_eval_zero f _ v i := by
    rw [D.eval_replacementRow_zero ⟨f, v⟩ i]
    simp only [scopeVarOf, eq_comm]
  row_natDegree_le f _ v i :=
    (D.natDegree_replacementRow_le ⟨f, v⟩ i).trans (Nat.sub_le R 1)
  kernel_zero t f _ v g hg ξ hsupp hker := by
    have hsupp' : ∀ i ∉ varGroup D.varAssign t g, ξ i = 0 := by
      intro i hi
      rw [mem_varGroup] at hi
      exact hsupp i hi
    have hmulVec :
        (varMeasurementMatrix Q r A₀ R ℚ D.place (scopeVarOf scope)).mulVec ξ = 0 := by
      ext p
      let k := (measurementRowEquiv Q r A₀ R D.h).symm p
      have hk : measurementRowEquiv Q r A₀ R D.h k = p :=
        (measurementRowEquiv Q r A₀ R D.h).apply_symm_apply p
      rw [← hk, ← D.sum_groupMeasurementRow_mul_eq_mulVec t g k hsupp]
      exact hker k
    simpa only [cast_nodeInt_rat, evalVarReplacementRow] using
      D.evalReplacementRow_nodePoint_eq_zero_of_kernel ⟨f, v⟩ t g hg ξ hsupp' hmulVec

@[simp]
theorem toCountingDesign_nodes (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q)
    (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2) :
    (D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).nodes = nodeInt :=
  rfl

@[simp]
theorem toCountingDesign_varGroup (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q)
    (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2) (t : Fin Q) (v : Fin n) :
    (D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).varGroup t v = D.varAssign v t :=
  rfl

@[simp]
theorem toCountingDesign_groupSet (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q)
    (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2) (t : Fin Q) (g : Fin r) :
    (D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).groupSet t g = varGroup D.varAssign t g :=
  rfl

@[simp]
theorem toCountingDesign_factorGroup (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q)
    (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2) :
    (D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).factorGroup = D.factorAssign :=
  rfl

@[simp]
theorem toCountingDesign_numRows (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q)
    (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2) (t : Fin Q) (g : Fin r) :
    (D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).numRows t g =
      D.h * #(measurementIndices Q r A₀ R) :=
  rfl

theorem toCountingDesign_sum_numRows (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q)
    (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2) (t : Fin Q) :
    (∑ g : Fin r, (D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).numRows t g) =
      r * (D.h * #(measurementIndices Q r A₀ R)) := by
  simp only [toCountingDesign_numRows, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

@[simp]
theorem toCountingDesign_matrix (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q)
    (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2) :
    (D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).matrix = D.groupMeasurementRow :=
  rfl

@[simp]
theorem toCountingDesign_row (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q)
    (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2) (f : F) (v : {v : Fin n // v ∈ scope f}) (i : Fin n) :
    (D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).row f v i =
      varReplacementRow Q r A₀ R D.place (scopeVarOf scope) ⟨f, v⟩ i :=
  rfl

/-- Evaluating `(D.toCountingDesign ...).evalRowRat t f v x` agrees with
`evalVarReplacementRow` at `nodePoint t`. -/
theorem toCountingDesign_evalRowRat (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q)
    (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2) (t : Fin Q) (f : F) (v : {v : Fin n // v ∈ scope f})
    (x : Fin n → ℚ) :
    (D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).evalRowRat t f v x =
      evalVarReplacementRow Q r A₀ R D.place (scopeVarOf scope) ⟨f, v⟩ (nodePoint t) x := by
  simp only [Cslib.ReplacementCounting.Design.evalRowRat, toCountingDesign_row,
    toCountingDesign_nodes, cast_nodeInt_rat, evalVarReplacementRow]

/-- Section 4 replacement rows in `D.toCountingDesign` satisfy the sharper degree bound
`natDegree ≤ R - 1` (Lemma 4.3 and Section 4.5, pp. 29, 32). -/
theorem toCountingDesign_row_natDegree_le_pred (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R)
    (hRQ : R < Q) (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2) (f : F) (v : {v : Fin n // v ∈ scope f})
    (i : Fin n) :
    ((D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).row f v i).natDegree ≤ R - 1 :=
  D.natDegree_replacementRow_le ⟨f, v⟩ i

/-- Consequently, `((D.toCountingDesign ...).targetPoly Φ).natDegree ≤ d * (R - 1)` whenever
`(liftedFactorProduct s Φ).totalDegree ≤ d`. -/
theorem toCountingDesign_natDegree_targetPoly_le_mul_pred {A : Type*} [CommRing A] [Algebra ℚ A]
    (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q)
    (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2)
    (Φ : ∀ f : F, MvPolynomial {v : Fin n // v ∈ scope f} A) {d : ℕ}
    (hd : (Cslib.ReplacementCounting.liftedFactorProduct s Φ).totalDegree ≤ d) :
    ((D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).targetPoly Φ).natDegree ≤ d * (R - 1) :=
  Cslib.ReplacementCounting.natDegree_targetPolynomial_le_of_liftedTotalDegree_le s Φ
    ((D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).rowIn A) hd fun f _ v i =>
      Polynomial.natDegree_map_le.trans
        (D.toCountingDesign_row_natDegree_le_pred s hr hR hRQ hτ_pos hτ_le f v i)

/-- **Lemma 4.6 common-denominator clearing on `D.toCountingDesign`** (p. 33): multiplying
`(D.toCountingDesign ...).row f v i` by `commonDenom Q R = (R - 1)! * Q!` yields the integer
polynomial `varReplacementRowScaledInt Q r A₀ R D.place (scopeVarOf scope) ⟨f, v⟩ i`. -/
theorem toCountingDesign_map_replacementRowScaledInt (s : Finset F) (hr : 2 ≤ r) (hR : 1 ≤ R)
    (hRQ : R < Q) (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2) (f : F) (v : {v : Fin n // v ∈ scope f})
    (i : Fin n) :
    (varReplacementRowScaledInt Q r A₀ R D.place (scopeVarOf scope) ⟨f, v⟩ i).map
        (Int.castRingHom ℚ) =
      (commonDenom Q R : ℚ) • (D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).row f v i :=
  D.map_replacementRowScaledInt ⟨f, v⟩ i

/-- **Lemma 4.6 cleared-row `ℓ₁` coefficient norm bound on `D.toCountingDesign`** (p. 33): the
sum of `coeffNorm1` across all `n` entries of the cleared integer row for `(f, v)` is at most
`commonDenom Q R * (1 + (1 + 2 ^ Q) * R * (4 * Q) ^ (R - 1))`. -/
theorem toCountingDesign_sum_coeffNorm1_le (f : F)
    (v : {v : Fin n // v ∈ scope f}) :
    (∑ i : Fin n,
      ((varReplacementRowScaledInt Q r A₀ R D.place (scopeVarOf scope) ⟨f, v⟩ i).coeffNorm1 : ℤ)) ≤
      (commonDenom Q R : ℤ) * (1 + (1 + 2 ^ Q) * (R : ℤ) * (4 * (Q : ℤ)) ^ (R - 1)) :=
  D.sum_coeffNorm1_replacementRowScaledInt_le ⟨f, v⟩

end ReplacementDesign

end Cslib.LinearAlgebra

/-! ### 3. Three-term exponential domain-examination bound (Section 3.5, eq. (3.16), p. 26) -/

namespace Cslib.ReplacementCounting

open Finset

/-- The three-term counting-cost rate
`(R / Q) log (2 Q / R) + τ log (2 D + 1) + 1 / r`
governing the finite-domain examination bound of Proposition 3.4 and equation (3.16)
([OpenAI2026ETH], Section 3.5, p. 26 and Section 4.7, equation (4.18), p. 34). -/
noncomputable def threeTermExponent (r Q R D : ℕ) (τ : ℝ) : ℝ :=
  (R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R) + τ * Real.log (2 * (D : ℝ) + 1) + 1 / r

/-- When `1 ≤ R ≤ Q`, `1 ≤ 2 * log (2 * Q / R)` because `1 - 1 / 2 ≤ log 2 ≤ log (2 * Q / R)`. -/
theorem one_le_two_mul_log_two_mul_div {R Q : ℕ} (hR : 1 ≤ R) (hRQ : R ≤ Q) :
    1 ≤ 2 * Real.log (2 * (Q : ℝ) / R) := by
  have hR_pos : (0 : ℝ) < R := by exact_mod_cast hR
  have hRQ_real : (R : ℝ) ≤ Q := by exact_mod_cast hRQ
  have h2_le : (2 : ℝ) ≤ 2 * (Q : ℝ) / R := by
    rw [le_div_iff₀ hR_pos]
    linarith
  have hhalf_le_log2 : (1 : ℝ) - 2⁻¹ ≤ Real.log 2 :=
    Real.one_sub_inv_le_log_of_pos zero_lt_two
  have hlog2_le : Real.log 2 ≤ Real.log (2 * (Q : ℝ) / R) :=
    Real.log_le_log zero_lt_two h2_le
  linarith

/-- For `1 ≤ R ≤ Q` and `(q : ℝ) ≤ c * n * (R / Q)`, `subsetPairCount n q` is bounded by
`exp ((c + 4) * n * ((R / Q) * log (2 Q / R)))` ([OpenAI2026ETH], Section 3.5, p. 26). -/
theorem subsetPairCount_le_exp_mul_log_ratio {R Q n q : ℕ} {c : ℝ}
    (hR : 1 ≤ R) (hRQ : R ≤ Q)
    (hq : (q : ℝ) ≤ c * (n : ℝ) * ((R : ℝ) / Q)) :
    (subsetPairCount n q : ℝ) ≤
      Real.exp ((c + 4) * (n : ℝ) * ((R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R))) := by
  have hR_pos : (0 : ℝ) < R := by exact_mod_cast hR
  have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast hR.trans hRQ
  have hRQ_real : (R : ℝ) ≤ Q := by exact_mod_cast hRQ
  have hratio_pos : 0 < 2 * (Q : ℝ) / R := by positivity
  have hlog_nonneg : 0 ≤ Real.log (2 * (Q : ℝ) / R) := by
    refine Real.log_nonneg ((one_le_div hR_pos).mpr ?_)
    linarith
  have hpow_q : ((Q : ℝ) / R) ^ q ≤ Real.exp (c * (n : ℝ) * ((R : ℝ) / Q *
      Real.log (2 * (Q : ℝ) / R))) := by
    have hle_two : (Q : ℝ) / R ≤ 2 * (Q : ℝ) / R := by
      refine div_le_div_of_nonneg_right ?_ hR_pos.le
      linarith
    calc ((Q : ℝ) / R) ^ q
        ≤ (2 * (Q : ℝ) / R) ^ q := pow_le_pow_left₀ (by positivity) hle_two q
      _ = Real.exp ((q : ℝ) * Real.log (2 * (Q : ℝ) / R)) := by
          rw [← Real.rpow_natCast, Real.rpow_def_of_pos hratio_pos, mul_comm]
      _ ≤ Real.exp (c * (n : ℝ) * ((R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R))) := by
          refine Real.exp_le_exp.mpr ?_
          calc (q : ℝ) * Real.log (2 * (Q : ℝ) / R)
              ≤ (c * (n : ℝ) * ((R : ℝ) / Q)) * Real.log (2 * (Q : ℝ) / R) :=
                mul_le_mul_of_nonneg_right hq hlog_nonneg
            _ = c * (n : ℝ) * ((R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R)) := by ring
  have hpow_n : (1 + 2 * ((R : ℝ) / Q)) ^ n ≤
      Real.exp (4 * (n : ℝ) * ((R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R))) := by
    have h1 : 1 + 2 * ((R : ℝ) / Q) ≤ Real.exp (2 * ((R : ℝ) / Q)) := by
      linarith [Real.add_one_le_exp (2 * ((R : ℝ) / Q))]
    have hlog_one := one_le_two_mul_log_two_mul_div hR hRQ
    calc (1 + 2 * ((R : ℝ) / Q)) ^ n
        ≤ Real.exp (2 * ((R : ℝ) / Q)) ^ n := pow_le_pow_left₀ (by positivity) h1 n
      _ = Real.exp ((n : ℝ) * (2 * ((R : ℝ) / Q))) := by
          rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (4 * (n : ℝ) * ((R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R))) := by
          refine Real.exp_le_exp.mpr ?_
          have hmul := mul_le_mul_of_nonneg_left hlog_one
            (show 0 ≤ 2 * (n : ℝ) * ((R : ℝ) / Q) by positivity)
          linarith
  calc (subsetPairCount n q : ℝ)
      ≤ ((Q : ℝ) / R) ^ q * (1 + 2 * ((R : ℝ) / Q)) ^ n :=
        subsetPairCount_le_ratio_pow hR hRQ n q
    _ ≤ Real.exp (c * (n : ℝ) * ((R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R))) *
          Real.exp (4 * (n : ℝ) * ((R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R))) :=
        mul_le_mul hpow_q hpow_n (by positivity) (by positivity)
    _ = Real.exp ((c + 4) * (n : ℝ) * ((R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R))) := by
        rw [← Real.exp_add]
        congr 1
        ring

namespace Design

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] {s : Finset F} {κ : F → Type*}
  {scope : ∀ f, κ f → ι} {r Q R D : ℕ} {τ : ℝ}
  (M : Design ι s κ scope r Q R D τ)

/-- `threeTermExponent r Q R D τ` is strictly positive for any `Design`. -/
theorem threeTermExponent_pos (M : Design ι s κ scope r Q R D τ) :
    0 < threeTermExponent r Q R D τ := by
  unfold threeTermExponent
  have hR_pos : (0 : ℝ) < R := by exact_mod_cast M.one_le_R
  have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast M.Q_pos
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast M.r_pos
  have hRQ : (R : ℝ) ≤ 2 * Q := by
    have : R ≤ 2 * Q := by have := M.R_lt_Q; omega
    exact_mod_cast this
  have hlog1 : 0 ≤ Real.log (2 * (Q : ℝ) / R) :=
    Real.log_nonneg ((one_le_div hR_pos).mpr hRQ)
  have hlog2 : 0 ≤ Real.log (2 * (D : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  have hτ : 0 ≤ τ := M.τ_pos.le
  positivity

/-- **Equation (3.16) exponential bound on Proposition 3.4's domain examination count**
([OpenAI2026ETH], Section 3.5, p. 26): whenever `0 ≤ c` and
`(q : ℝ) ≤ c * Fintype.card ι * (R / Q)`, the total number of local Boolean assignments examined
across all `Q` nodes and all subset pairs `(E, U)` with `#E ≤ q` and `U ⊆ E` is at most
`2 * Q * r * exp ((c + 4) * Fintype.card ι * threeTermExponent r Q R D τ)`. -/
theorem domainExaminationBound_le_mul_exp_threeTermExponent {q : ℕ} {c : ℝ}
    (hc : 0 ≤ c) (hq : (q : ℝ) ≤ c * (Fintype.card ι : ℝ) * ((R : ℝ) / Q)) :
    (∑ t : Fin Q, (#{p : Finset ι × Finset ι | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
        (2 * (#(M.measurementBox t) : ℝ) *
          ∑ g : Fin r, (Fintype.card (M.LocalCube t g) : ℝ))) ≤
      2 * (Q : ℝ) * (r : ℝ) *
        Real.exp ((c + 4) * (Fintype.card ι : ℝ) * threeTermExponent r Q R D τ) := by
  set n := Fintype.card ι
  have hC := subsetPairCount_le_exp_mul_log_ratio M.one_le_R M.R_lt_Q.le hq
  have hD_pos : (0 : ℝ) < 2 * (D : ℝ) + 1 := by positivity
  have hlogD_nonneg : 0 ≤ Real.log (2 * (D : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg D : (0 : ℝ) ≤ D)])
  have hτ_pos : 0 ≤ τ := M.τ_pos.le
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast M.r_pos
  have hmeas_exp :
      (2 * (D : ℝ) + 1) ^ (2 * τ * (n : ℝ)) ≤
        Real.exp ((c + 4) * (n : ℝ) * (τ * Real.log (2 * (D : ℝ) + 1))) := by
    rw [Real.rpow_def_of_pos hD_pos]
    refine Real.exp_le_exp.mpr ?_
    have hle : (2 : ℝ) ≤ c + 4 := by linarith
    have hnn : 0 ≤ (n : ℝ) * (τ * Real.log (2 * (D : ℝ) + 1)) := by positivity
    calc Real.log (2 * (D : ℝ) + 1) * (2 * τ * (n : ℝ))
        = 2 * ((n : ℝ) * (τ * Real.log (2 * (D : ℝ) + 1))) := by ring
      _ ≤ (c + 4) * ((n : ℝ) * (τ * Real.log (2 * (D : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_right hle hnn
      _ = (c + 4) * (n : ℝ) * (τ * Real.log (2 * (D : ℝ) + 1)) := by ring
  have hgroup_exp :
      (2 : ℝ) ^ (2 * (n : ℝ) / r) ≤
        Real.exp ((c + 4) * (n : ℝ) * (1 / (r : ℝ))) := by
    rw [Real.rpow_def_of_pos zero_lt_two]
    refine Real.exp_le_exp.mpr ?_
    have hlog2_le : Real.log 2 ≤ 1 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hle : 2 * Real.log 2 ≤ c + 4 := by linarith
    have hnn : 0 ≤ (n : ℝ) * (1 / (r : ℝ)) := by positivity
    calc Real.log 2 * (2 * (n : ℝ) / r)
        = (2 * Real.log 2) * ((n : ℝ) * (1 / (r : ℝ))) := by ring
      _ ≤ (c + 4) * ((n : ℝ) * (1 / (r : ℝ))) :=
          mul_le_mul_of_nonneg_right hle hnn
      _ = (c + 4) * (n : ℝ) * (1 / (r : ℝ)) := by ring
  have hprod :
      (subsetPairCount n q : ℝ) * (2 * (D : ℝ) + 1) ^ (2 * τ * (n : ℝ)) *
          (2 : ℝ) ^ (2 * (n : ℝ) / r) ≤
        Real.exp ((c + 4) * (n : ℝ) * threeTermExponent r Q R D τ) := by
    calc (subsetPairCount n q : ℝ) * (2 * (D : ℝ) + 1) ^ (2 * τ * (n : ℝ)) *
            (2 : ℝ) ^ (2 * (n : ℝ) / r)
        ≤ Real.exp ((c + 4) * (n : ℝ) * ((R : ℝ) / Q * Real.log (2 * (Q : ℝ) / R))) *
            Real.exp ((c + 4) * (n : ℝ) * (τ * Real.log (2 * (D : ℝ) + 1))) *
            Real.exp ((c + 4) * (n : ℝ) * (1 / (r : ℝ))) := by
          refine mul_le_mul (mul_le_mul hC hmeas_exp (by positivity) (by positivity))
            hgroup_exp (by positivity) (by positivity)
      _ = Real.exp ((c + 4) * (n : ℝ) * threeTermExponent r Q R D τ) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          unfold threeTermExponent
          ring
  refine (M.domainExaminationBound_real q).trans ?_
  calc 2 * (Q : ℝ) * (r : ℝ) * (subsetPairCount n q : ℝ) *
          (2 * (D : ℝ) + 1) ^ (2 * τ * (n : ℝ)) * (2 : ℝ) ^ (2 * (n : ℝ) / r)
      = 2 * (Q : ℝ) * (r : ℝ) *
          ((subsetPairCount n q : ℝ) * (2 * (D : ℝ) + 1) ^ (2 * τ * (n : ℝ)) *
            (2 : ℝ) ^ (2 * (n : ℝ) / r)) := by ring
    _ ≤ 2 * (Q : ℝ) * (r : ℝ) *
          Real.exp ((c + 4) * (n : ℝ) * threeTermExponent r Q R D τ) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)

/-- Specialization of `domainExaminationBound_le_mul_exp_threeTermExponent` to the canonical
truncation order `q = (d * R) / Q = jetOrder (d * R) Q - 1` (equation (3.5), p. 24) when
`(d : ℝ) ≤ c * Fintype.card ι`. -/
theorem domainExaminationBound_div_le_mul_exp_threeTermExponent {d : ℕ} {c : ℝ}
    (hc : 0 ≤ c) (hd : (d : ℝ) ≤ c * Fintype.card ι) :
    (∑ t : Fin Q, (#{p : Finset ι × Finset ι | #p.1 ≤ (d * R) / Q ∧ p.2 ⊆ p.1} : ℝ) *
        (2 * (#(M.measurementBox t) : ℝ) *
          ∑ g : Fin r, (Fintype.card (M.LocalCube t g) : ℝ))) ≤
      2 * (Q : ℝ) * (r : ℝ) *
        Real.exp ((c + 4) * (Fintype.card ι : ℝ) * threeTermExponent r Q R D τ) := by
  have hQ_pos : (0 : ℝ) < Q := by exact_mod_cast M.Q_pos
  have hR_nn : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hq : (((d * R) / Q : ℕ) : ℝ) ≤ c * (Fintype.card ι : ℝ) * ((R : ℝ) / Q) := by
    calc (((d * R) / Q : ℕ) : ℝ)
        ≤ ((d * R : ℕ) : ℝ) / Q := Nat.cast_div_le
      _ = (d : ℝ) * ((R : ℝ) / Q) := by push_cast; ring
      _ ≤ (c * Fintype.card ι) * ((R : ℝ) / Q) :=
          mul_le_mul_of_nonneg_right hd (div_nonneg hR_nn hQ_pos.le)
  exact M.domainExaminationBound_le_mul_exp_threeTermExponent hc hq

end Design

end Cslib.ReplacementCounting

/-! ### 4. Combined Lemma 4.7 → Definition 3.1 / Proposition 3.4 existence bridge -/

namespace Cslib.LinearAlgebra

open Finset
open Cslib.BalancedSchedules

variable {Q r A₀ R n : ℕ}

/-- **Lemma 4.7 → Definition 3.1 / Proposition 3.4 existence bridge**
([OpenAI2026ETH], Definition 3.1, Proposition 3.4, and Lemma 4.7, pp. 21–25, 33–34):
Under the algebraic Lemma 4.7 hypotheses on `scope : F → Finset (Fin n)` with `0 < τ ≤ 1 / 2`,
there exists a concrete `D : ReplacementDesign scope Q r A₀ R τ` whose canonical
`D.toCountingDesign s hr hR hRQ hτ_pos hτ_le` is a valid `Cslib.ReplacementCounting.Design` for
every `s : Finset F` (automatically inheriting `Design.targetSum_eq_of_taylorJet_jetOrder`,
`Design.sum_restricted_shiftedFactor_eq_sum_measurement_fibers`, and
`Design.domainExaminationBound_le_mul_exp_threeTermExponent` while preserving all Lemma 4.5–4.7
incidence, copy, denominator, and `ℓ₁` coefficient norm bounds on `D`). -/
theorem exists_countingDesign_of_scopes {F : Type*} [Fintype F]
    (scope : F → Finset (Fin n)) (s : Finset F) {Q r A₀ R b w : ℕ} {τ : ℚ}
    (hn : 1 ≤ n) (hb_pos : 1 ≤ b) (hw_pos : 1 ≤ w)
    (hr : 2 ≤ r) (hR : 1 ≤ R) (hRQ : R < Q) (hτ_pos : 0 < τ) (hτ_le : τ ≤ 1 / 2)
    (hI : ∀ a < R - 1, A₀ + a ≤ Q)
    (hb : ∀ v : Fin n, #{f : F | v ∈ scope f} ≤ b)
    (hw : ∀ f : F, #(scope f) ≤ w)
    (hM_le : (∑ f : F, #(scope f)) ≤ b * n)
    (hincidenceSize : 2 * (b + w) * (r ^ (2 * Q)) ^ 2 ≤ ∑ f : F, #(scope f))
    (hgroupSize : 2 * Q * r ^ 2 ≤ n)
    (htail : binomTailProb Q r A₀ R ≤ τ / ((r : ℚ) * (b : ℚ))) :
    ∃ D : ReplacementDesign scope Q r A₀ R τ,
      Nonempty
        (Cslib.ReplacementCounting.Design (Fin n) s (fun f => {v : Fin n // v ∈ scope f})
          (fun _ v => v.1) r Q R (r ^ (2 * Q)) (τ : ℝ)) ∧
      D.h * r ^ (2 * Q) ≤ 2 * ∑ f : F, #(scope f) ∧
      (∀ f : F, scope f = ∅ → ∀ t : Fin Q, (D.factorAssign f t).1 = 0) ∧
      (∀ (f : F) (v : {v : Fin n // v ∈ scope f}) (i : Fin n),
        (varReplacementRowScaledInt Q r A₀ R D.place (scopeVarOf scope) ⟨f, v⟩ i).map
            (Int.castRingHom ℚ) =
          (commonDenom Q R : ℚ) •
            (D.toCountingDesign s hr hR hRQ hτ_pos hτ_le).row f v i) ∧
      (∀ (f : F) (v : {v : Fin n // v ∈ scope f}),
        (∑ i : Fin n,
          ((varReplacementRowScaledInt Q r A₀ R D.place (scopeVarOf scope) ⟨f, v⟩ i).coeffNorm1 :
            ℤ)) ≤
          (commonDenom Q R : ℤ) * (1 + (1 + 2 ^ Q) * (R : ℤ) * (4 * (Q : ℤ)) ^ (R - 1))) := by
  obtain ⟨D⟩ := exists_replacementDesign scope hn hb_pos hw_pos hr hR hRQ hτ_pos.le hI hb hw hM_le
    hincidenceSize hgroupSize htail
  exact ⟨D, ⟨D.toCountingDesign s hr hR hRQ hτ_pos hτ_le⟩, D.h_mul_D_le, D.factorAssign_of_empty,
    D.toCountingDesign_map_replacementRowScaledInt s hr hR hRQ hτ_pos hτ_le,
    D.toCountingDesign_sum_coeffNorm1_le⟩

end Cslib.LinearAlgebra
