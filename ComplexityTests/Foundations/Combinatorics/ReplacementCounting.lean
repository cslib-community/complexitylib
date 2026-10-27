/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: local-only (tests of Complexity.Foundations.Combinatorics.ReplacementCounting)

public import Complexity.Foundations.Combinatorics.ReplacementCounting
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Concrete and boundary tests for replacement designs and counting assembly

Exercises `Cslib.ReplacementCounting.subsetPairCount`, `intMeasurementBox`, `Design`,
`targetPolynomial`, restricted-slice measurement-fiber factorization, and confluent Hermite jet
recovery on concrete nonvacuous instances and boundary cases.
-/

@[expose] public section

namespace ComplexityTests.ReplacementCounting

open Finset Cslib Cslib.ReplacementCounting
open scoped BigOperators

/-! ### 1. Concrete subset-pair counts and weighted binomial inequalities -/

/-- Exact values on `n = 3`: `C_0 = 1`, strict truncation `C_1 = 7 < 27`, `C_2 = 19`, `C_3 = 27`. -/
example :
    subsetPairCount 3 0 = 1 ∧ subsetPairCount 3 1 = 7 ∧
      subsetPairCount 3 2 = 19 ∧ subsetPairCount 3 3 = 27 := by decide

/-- Concrete subset-pair enumeration on `Fin 3` at truncation `q = 1` has cardinality `7`. -/
example : #{p : Finset (Fin 3) × Finset (Fin 3) | #p.1 ≤ 1 ∧ p.2 ⊆ p.1} = 7 := by
  rw [card_subsetPairs_eq_subsetPairCount]; decide

/-- Concrete check of equation (3.15) at `η = 1 / 2` (`R = 1, Q = 2`), `n = 3`, `q = 1`. -/
example :
    ((1 / 2 : ℝ) ^ 1 * (subsetPairCount 3 1 : ℝ) ≤ (1 + 2 * (1 / 2 : ℝ)) ^ 3) ∧
      ((subsetPairCount 3 1 : ℝ) ≤ (1 / (1 / 2 : ℝ)) ^ 1 * (1 + 2 * (1 / 2 : ℝ)) ^ 3) ∧
      ((subsetPairCount 3 1 : ℝ) ≤ ((2 : ℝ) / 1) ^ 1 * (1 + 2 * ((1 : ℝ) / 2)) ^ 3) :=
  ⟨pow_mul_subsetPairCount_le (by norm_num) (by norm_num) 3 1,
    subsetPairCount_le_one_div_pow_mul (by norm_num) (by norm_num) 3 1,
    by simpa only [Nat.cast_one, Nat.cast_ofNat] using
      subsetPairCount_le_ratio_pow (R := 1) (Q := 2) (le_refl 1) (by decide) 3 1⟩

/-- Necessity of `η ≤ 1` in `pow_mul_subsetPairCount_le`: for `η = 2`, `n = 1`, `q = 2`,
`η ^ q * C_q = 4 * 3 = 12 > 5 = (1 + 2 * η) ^ n`. -/
example : ¬ ((2 : ℝ) ^ 2 * (subsetPairCount 1 2 : ℝ) ≤ (1 + 2 * (2 : ℝ)) ^ 1) := by
  rw [show subsetPairCount 1 2 = 3 by decide]; norm_num

/-! ### 2. Signed integer measurement boxes -/

/-- A signed 1-row matrix `(2, -2)` of `ℓ₁`-norm `4` maps Boolean inputs into `[-4, 4]` (size `9`),
realizing negative (`-2`) and positive (`2`) boundary summaries. -/
def signedRow : Fin 1 → Fin 2 → ℤ := fun _ => ![2, -2]

private theorem signedRow_l1 (k : Fin 1) : (∑ i : Fin 2, (signedRow k i).natAbs) ≤ 4 := by
  fin_cases k; decide

example :
    #(intMeasurementBox 4 1) = 9 ∧
      (fun k => ∑ i : Fin 2, signedRow k i * BitString.bitVal ℤ (![false, true] i)) ∈
        intMeasurementBox 4 1 ∧
      (∑ i : Fin 2, signedRow 0 i * BitString.bitVal ℤ (![false, true] i)) = -2 ∧
      (∑ i : Fin 2, signedRow 0 i * BitString.bitVal ℤ (![true, false] i)) = 2 :=
  ⟨by simp only [card_intMeasurementBox]; norm_num,
    boolean_mulVec_mem_intMeasurementBox signedRow_l1 ![false, true], by decide, by decide⟩

/-! ### 3. Concrete `r = 2, Q = 2, R = 1` replacement design with quadratic `H(T)` -/

/-- Two unary factors on `Fin 2`: factor `0` reads `x_0`, factor `1` reads `x_1`. -/
def twoScope (f : Fin 2) (_ : Unit) : Fin 2 := f

/-- Number of measurement rows per `(t, g)`: `1` when `t = g` and `0` otherwise. -/
def twoNumRows (t g : Fin 2) : ℕ := if t = g then 1 else 0

/-- Measurement matrices of `ℓ₁`-norm `1`: `C_{0,0}` measures `x_0` and `C_{1,1}` measures `x_1`. -/
def twoMatrix (t g : Fin 2) (_ : Fin (twoNumRows t g)) (i : Fin 2) : ℤ :=
  if t = g ∧ i = g then 1 else 0

/-- Degree-1 replacement rows: `P_0() = (1 + T, 0)` and `P_1() = (T, 1 + T)`. -/
noncomputable def twoRow (f : Fin 2) (_ : Unit) (i : Fin 2) : Polynomial ℚ :=
  match f, i with
  | ⟨0, _⟩, ⟨0, _⟩ => 1 + Polynomial.X
  | ⟨0, _⟩, ⟨1, _⟩ => 0
  | ⟨1, _⟩, ⟨0, _⟩ => Polynomial.X
  | ⟨1, _⟩, ⟨1, _⟩ => 1 + Polynomial.X

/-- Concrete `(r = 2, τ = 1/2, D = 1)` replacement design at `Q = 2` nodes `![1, 2]` with `R = 1`.
-/
noncomputable def twoGroupDesign :
    Design (Fin 2) (univ : Finset (Fin 2)) (fun _ => Unit) twoScope 2 2 1 1 (1 / 2) where
  two_le_r := le_refl 2
  one_le_D := le_refl 1
  one_le_R := le_refl 1
  R_lt_Q := by decide
  τ_pos := by norm_num
  τ_le_half := le_refl _
  nodes := ![1, 2]
  nodes_injective := by decide
  nodes_ne_zero t := by fin_cases t <;> decide
  varGroup _ i := i
  card_varGroup_le t g := by fin_cases t <;> fin_cases g <;> decide
  factorGroup f t :=
    match f, t with
    | ⟨0, _⟩, _ => 0
    | ⟨1, _⟩, ⟨0, _⟩ => 1
    | ⟨1, _⟩, ⟨1, _⟩ => 0
  numRows := twoNumRows
  sum_numRows_le t := by fin_cases t <;> norm_num [twoNumRows, Fin.sum_univ_two]
  matrix := twoMatrix
  matrix_support t g k i hne := by
    simp only [twoMatrix]
    split_ifs with h
    · exact absurd h.2 hne
    · rfl
  row_l1_le t g k := by fin_cases t <;> fin_cases g <;> fin_cases k <;> decide
  row := twoRow
  row_eval_zero f _ v i := by
    fin_cases v
    fin_cases f <;> fin_cases i <;>
      simp only [twoRow, twoScope, Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_X,
        Polynomial.eval_zero, add_zero, ↓reduceIte, Fin.zero_eta, Fin.mk_one, Fin.isValue,
        one_ne_zero, zero_ne_one]
  row_natDegree_le f _ v i := by
    fin_cases v
    have h1X : (1 + Polynomial.X : Polynomial ℚ).natDegree ≤ 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans ?_
      simp only [Polynomial.natDegree_one, Polynomial.natDegree_X]; omega
    fin_cases f <;> fin_cases i
    · exact h1X
    · simp only [twoRow, Polynomial.natDegree_zero, Nat.zero_le]
    · simp only [twoRow, Polynomial.natDegree_X, le_refl]
    · exact h1X
  kernel_zero t f _ v g hne ξ hsupp hmeas := by
    fin_cases v
    fin_cases f <;> fin_cases t <;> fin_cases g
    all_goals try exact absurd rfl hne
    · rw [Fin.sum_univ_two, hsupp 0 (by decide)]
      simp only [twoRow, mul_zero, Polynomial.eval_zero, zero_mul, add_zero]
    · rw [Fin.sum_univ_two, hsupp 0 (by decide)]
      simp only [twoRow, mul_zero, Polynomial.eval_zero, zero_mul, add_zero]
    · have hm := hmeas ⟨0, by decide⟩
      rw [Fin.sum_univ_two, hsupp 1 (by decide)] at hm ⊢
      norm_num [twoMatrix] at hm; rw [hm, mul_zero, mul_zero, add_zero]
    · have hm := hmeas ⟨0, by decide⟩
      rw [Fin.sum_univ_two, hsupp 0 (by decide)] at hm ⊢
      norm_num [twoMatrix] at hm; rw [hm, mul_zero, mul_zero, add_zero]

/-- Conjunction factors `Φ_0(y) = y` and `Φ_1(y) = y`, counting `{x ∈ {0,1}^2 | x_0 ∧ x_1}`. -/
noncomputable def andFactors (_ : Fin 2) : MvPolynomial Unit ℚ := MvPolynomial.X ()

private theorem totalDegree_lifted_andFactors :
    (liftedFactorProduct (univ : Finset (Fin 2)) andFactors).totalDegree ≤ 2 := by
  refine (totalDegree_liftedFactorProduct_le _ _).trans ?_
  rw [Fin.sum_univ_two]; simp only [andFactors, MvPolynomial.totalDegree_X]; decide

private theorem univ_fin2_bool :
    (univ : Finset (Fin 2 → Bool)) =
      {![false, false], ![false, true], ![true, false], ![true, true]} := by decide

/-- On `{0, 1}^2`, `targetSum` for `x_0 * x_1` equals `1`. -/
theorem targetSum_andFactors_eq_one :
    targetSum (univ : Finset (Fin 2)) twoScope andFactors = 1 := by
  unfold targetSum andFactors twoScope
  rw [univ_fin2_bool]
  repeat rw [sum_insert (by decide)]
  rw [sum_singleton]
  norm_num [Fin.prod_univ_two, BitString.bitVal]

/-- `twoGroupDesign.targetPoly andFactors` equals `1 + 4T + 3T^2`, evaluating to `1` at `0`, `8` at
`1`, and `21` at `2` with exact `natDegree = 2 = d * R`. -/
example :
    (twoGroupDesign.targetPoly andFactors).eval 0 = 1 ∧
      (twoGroupDesign.targetPoly andFactors).eval 1 = 8 ∧
      (twoGroupDesign.targetPoly andFactors).eval 2 = 21 ∧
      (twoGroupDesign.targetPoly andFactors).natDegree = 2 := by
  have h0 : (twoGroupDesign.targetPoly andFactors).eval 0 = 1 := by
    rw [twoGroupDesign.eval_zero_targetPoly, targetSum_andFactors_eq_one]
  have hpoly : twoGroupDesign.targetPoly andFactors =
      1 + Polynomial.C 4 * Polynomial.X + Polynomial.C 3 * Polynomial.X ^ 2 := by
    unfold Design.targetPoly targetPolynomial andFactors replacementEval Design.rowIn
      twoGroupDesign twoRow
    rw [univ_fin2_bool]
    repeat rw [sum_insert (by decide)]
    rw [sum_singleton]
    simp only [Fin.prod_univ_two, Fin.sum_univ_two, Fin.isValue, MvPolynomial.eval₂_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      BitString.bitVal_false, BitString.bitVal_true, map_zero, map_one,
      Polynomial.map_add, Polynomial.map_one, Polynomial.map_X, Polynomial.map_zero,
      map_ofNat]
    ring
  refine ⟨h0, ?_, ?_, ?_⟩
  · rw [hpoly]; norm_num
  · rw [hpoly]; norm_num
  · refine le_antisymm (twoGroupDesign.natDegree_targetPoly_le andFactors
      totalDegree_lifted_andFactors) ?_
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [hpoly]
    simp only [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_X_pow, ↓reduceIte, OfNat.ofNat_ne_zero]
    norm_num

/-- **End-to-end Hermite jet recovery**: `targetSum = 1` is recovered from the canonical order-`2`
Taylor jets (`jetOrder (2 * 1) 2 = 2`) at `nodes = ![1, 2]`. -/
example :
    ((Polynomial.hermiteMatrix twoGroupDesign.nodes (jetOrder (2 * 1) 2)).det : ℚ)⁻¹ •
      (((Polynomial.hermiteMatrix twoGroupDesign.nodes (jetOrder (2 * 1) 2)).map
          (Int.cast : ℤ → ℚ)).updateCol
        (⟨0, twoGroupDesign.Q_pos⟩, ⟨0, jetOrder_pos _ _⟩)
        (Polynomial.taylorJet (fun i => (twoGroupDesign.nodes i : ℚ)) (jetOrder (2 * 1) 2)
          (twoGroupDesign.targetPoly andFactors))).det = 1 := by
  rw [← twoGroupDesign.targetSum_eq_of_taylorJet_jetOrder ℚ andFactors
    totalDegree_lifted_andFactors, targetSum_andFactors_eq_one]

/-- Exact Lemma 3.2 two-pass local-cube scan count on `twoGroupDesign` at node `0`:
`2 * (2 * 1 + 1)^1 * (2^1 + 2^1) = 24`. -/
example :
    2 * #(twoGroupDesign.measurementBox 0) *
      (∑ g : Fin 2, Fintype.card (twoGroupDesign.LocalCube 0 g)) = 24 := by
  rw [twoGroupDesign.two_mul_card_measurementBox_mul_sum_card_localCube 0]
  have hg0 : #(twoGroupDesign.groupSet 0 0) = 1 := by decide
  have hg1 : #(twoGroupDesign.groupSet 0 1) = 1 := by decide
  rw [Fin.sum_univ_two, Fin.sum_univ_two, hg0, hg1]
  norm_num [twoGroupDesign, twoNumRows]

/-- Valid unrestricted representative selector for `twoGroupDesign` at node `t = 0`:
picks `false` on the unmeasured group `1` (violating `x_1 = true` when `E = {1}`) and decodes the
single bit on group `0` from `y 0 0`. -/
def nodeZeroRep (y : ∀ g : Fin 2, Fin (twoGroupDesign.numRows 0 g) → ℤ)
    (_ : ∀ g, ∃ u : twoGroupDesign.LocalCube 0 g, twoGroupDesign.localMeasure 0 g u = y g)
    (g : Fin 2) : twoGroupDesign.LocalCube 0 g :=
  match g with
  | ⟨0, _⟩ => fun _ => decide (y 0 ⟨0, by decide⟩ = 1)
  | ⟨1, _⟩ => fun _ => false

private theorem nodeZeroRep_valid (y : ∀ g : Fin 2, Fin (twoGroupDesign.numRows 0 g) → ℤ)
    (hy : ∀ g, ∃ u : twoGroupDesign.LocalCube 0 g, twoGroupDesign.localMeasure 0 g u = y g)
    (g : Fin 2) : twoGroupDesign.localMeasure 0 g (nodeZeroRep y hy g) = y g := by
  fin_cases g
  · obtain ⟨u, hu⟩ := hy 0
    funext k
    fin_cases k
    have hu0 := congrFun hu ⟨0, by decide⟩
    have hcard : (univ : Finset {i : Fin 2 // twoGroupDesign.varGroup 0 i = 0}) =
        {⟨0, rfl⟩} := by decide
    rw [Design.localMeasure, hcard, sum_singleton] at hu0 ⊢
    change twoMatrix 0 0 ⟨0, by decide⟩ 0 * BitString.bitVal ℤ (u ⟨0, rfl⟩) =
      y 0 ⟨0, by decide⟩ at hu0
    change twoMatrix 0 0 ⟨0, by decide⟩ 0 *
      BitString.bitVal ℤ (decide (y 0 ⟨0, by decide⟩ = 1)) = y 0 ⟨0, by decide⟩
    norm_num [twoMatrix] at hu0 ⊢
    cases h : u ⟨0, rfl⟩ <;>
      simp only [h, BitString.bitVal_false, BitString.bitVal_true] at hu0 <;>
      rw [← hu0] <;> decide
  · funext k; exact Fin.elim0 k

/-- Representative `nodeZeroRep` lies outside `restrictedLocalCube 0 {1} 1` (since it picks
`false` on group `1`), yet `sum_restricted_shiftedFactor_eq_sum_measurement_fibers` still computes
the exact restricted Taylor-shifted sum on `{x | x_1 = true}`. -/
example :
    nodeZeroRep (fun g k => match g with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => Fin.elim0 k)
        (fun g => by
          fin_cases g
          · refine ⟨fun _ => true, funext fun k => ?_⟩; fin_cases k; decide
          · exact ⟨fun _ => false, funext fun k => Fin.elim0 k⟩) 1 ∉
      twoGroupDesign.restrictedLocalCube 0 {1} 1 ∧
    (∑ y ∈ twoGroupDesign.measurementBox 0,
        SharedSummaries.fiberContribution (twoGroupDesign.localMeasure 0)
          (twoGroupDesign.restrictedLocalCube 0 {1})
          (twoGroupDesign.groupedFactor (twoGroupDesign.shiftedFactorEval andFactors 0 {0}) 0)
          nodeZeroRep y).eval 0 = 6 := by
  refine ⟨?_, ?_⟩
  · intro hmem
    have h1 := (mem_filter.mp hmem).2 ⟨1, rfl⟩ (mem_singleton_self 1)
    simp only [nodeZeroRep, Bool.false_eq_true] at h1
  · rw [← twoGroupDesign.sum_restricted_shiftedFactor_eq_sum_measurement_fibers andFactors 0 {1}
      {0} nodeZeroRep nodeZeroRep_valid]
    trans (∑ x ∈ ({![false, true], ![true, true]} : Finset (Fin 2 → Bool)),
        ∏ f ∈ univ, twoGroupDesign.shiftedFactorEval andFactors 0 {0} f
          (fun v => twoGroupDesign.evalRow 0 f v x)).eval 0
    · congr 2; decide
    · rw [sum_insert (by decide), sum_singleton, Polynomial.eval_add]
      simp only [Fin.prod_univ_two, Fin.isValue, Design.shiftedFactorEval, andFactors,
        MvPolynomial.eval₂_X, sum_singleton, Polynomial.eval_mul, Polynomial.eval_add,
        Polynomial.eval_C, Polynomial.eval_sub, Polynomial.taylor_eval, zero_add, sub_self,
        add_zero]
      norm_num [Design.evalRow, Design.evalRowRat, twoGroupDesign, twoRow,
        Fin.sum_univ_two, BitString.bitVal]

/-! ### 4. Boundary and degenerate cases -/

/-- Empty factor set `s = ∅`: every Boolean assignment contributes `1`, so `targetSum = 2 ^ n`. -/
example :
    targetSum (ι := Fin 3) (F := Fin 0) (A := ℚ) (κ := fun _ => Unit)
      ∅ (fun f => f.elim0) (fun f => f.elim0) = 8 := by
  simp only [targetSum, prod_empty, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, nsmul_eq_mul]
  norm_num

/-- Empty variable set `ι = Fin 0`: there is a single empty Boolean assignment `Fin.elim0`. -/
example :
    targetSum (ι := Fin 0) (F := Fin 1) (A := ℚ) (κ := fun _ => Fin 0)
      {0} (fun _ v => v.elim0) (fun _ => MvPolynomial.C 7) = 7 := by
  simp only [targetSum, prod_singleton, MvPolynomial.eval_C, sum_const, card_univ,
    Fintype.card_fun, Fintype.card_fin, pow_zero, nsmul_eq_mul]
  norm_num

/-- Zero ring `ZMod 1`: `eval_zero_targetPolynomial` holds without `[Nontrivial A]`. -/
example :
    (targetPolynomial (ι := Fin 1) (F := Fin 1) (A := ZMod 1) (κ := fun _ => Unit)
      {0} (fun _ => MvPolynomial.X ()) (fun _ _ _ => 1)).eval 0 =
    targetSum (ι := Fin 1) (F := Fin 1) (A := ZMod 1) (κ := fun _ => Unit)
      {0} (fun _ _ => 0) (fun _ => MvPolynomial.X ()) :=
  eval_zero_targetPolynomial _ _ _ _ fun _ _ _ _ => Subsingleton.elim _ _

end ComplexityTests.ReplacementCounting
