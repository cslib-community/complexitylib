/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquarePolynomialCoordinates

/-!
# Constant compensation after the determinant-square factor

This file separates the elementary compensation argument from the quantitative
estimate near permutation matrices.  The main reduction says that any uniform
upper bound for the normalized processing defect gives a nonnegative constant
whose determinant-square multiple satisfies the full one-sided DPI.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`ConstantCompensation.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators

namespace SquarePolynomial

open GeneralAsymmetricC1

/-- Invariance of a polynomial on the simplex under row permutations. -/
@[expose] def RowSymmetricOnSimplex {n : ℕ} (P : Poly n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (U : Mat n n), Simplex U →
    peval P ((fun i j => σ.permMatrix ℝ i j : Mat n n) * U) = peval P U

/-- The determinant-square compensated functional associated to `P` and `M`. -/
def compensatedEval {n : ℕ} (P : Poly n) (M : ℝ) (U : Mat n n) : ℝ :=
  Matrix.det (Matrix.of U) ^ 2 * (peval P U + M)

/-- The squared determinant contraction factor of a processing matrix. -/
@[expose] def detContraction {n : ℕ} (T : Mat n n) : ℝ :=
  Matrix.det (Matrix.of T) ^ 2

/-! ## Elementary bounds on the probability box -/

/-- The entrywise unit box containing both the simplex and all stochastic
processing matrices. -/
def InUnitBox {n m : ℕ} (U : Mat n m) : Prop :=
  ∀ i j, U i j ∈ Set.Icc (0 : ℝ) 1

/-- Entrywise `ℓ¹` distance.  We keep this explicit finite sum rather than
depending on a particular matrix norm instance. -/
def entryL1Dist {n m : ℕ} (U V : Mat n m) : ℝ :=
  ∑ i, ∑ j, |U i j - V i j|

lemma entryL1Dist_nonneg {n m : ℕ} (U V : Mat n m) :
    0 ≤ entryL1Dist U V := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _

lemma abs_entry_sub_le_entryL1Dist {n m : ℕ}
    (U V : Mat n m) (i : Fin n) (j : Fin m) :
    |U i j - V i j| ≤ entryL1Dist U V := by
  unfold entryL1Dist
  calc
    |U i j - V i j| ≤ ∑ q : Fin m, |U i q - V i q| := by
      exact Finset.single_le_sum (fun q _ => abs_nonneg (U i q - V i q))
        (Finset.mem_univ j)
    _ ≤ ∑ p : Fin n, ∑ q : Fin m, |U p q - V p q| := by
      exact Finset.single_le_sum
        (fun p _ => Finset.sum_nonneg fun q _ => abs_nonneg (U p q - V p q))
        (Finset.mem_univ i)

/-- A polynomial is uniformly bounded on the entrywise unit box.  This is
proved algebraically by multivariate-polynomial induction. -/
theorem exists_peval_bound_unitBox {n : ℕ} (P : Poly n) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ U : Mat n n, InUnitBox U → |peval P U| ≤ B := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      refine ⟨|c|, abs_nonneg c, ?_⟩
      intro U hU
      simp [peval]
  | add P Q hP hQ =>
      obtain ⟨BP, hBP, hPbound⟩ := hP
      obtain ⟨BQ, hBQ, hQbound⟩ := hQ
      refine ⟨BP + BQ, add_nonneg hBP hBQ, ?_⟩
      intro U hU
      calc
        |peval (P + Q) U| = |peval P U + peval Q U| := by simp [peval]
        _ ≤ |peval P U| + |peval Q U| := abs_add_le _ _
        _ ≤ BP + BQ := add_le_add (hPbound U hU) (hQbound U hU)
  | mul_X P ia hP =>
      obtain ⟨BP, hBP, hPbound⟩ := hP
      refine ⟨BP, hBP, ?_⟩
      intro U hU
      have hXnonneg : 0 ≤ U ia.1 ia.2 := (hU ia.1 ia.2).1
      have hXabs : |U ia.1 ia.2| ≤ 1 := by
        rw [abs_of_nonneg hXnonneg]
        exact (hU ia.1 ia.2).2
      calc
        |peval (P * MvPolynomial.X ia) U| =
            |peval P U| * |U ia.1 ia.2| := by simp [peval, abs_mul]
        _ ≤ BP * 1 := mul_le_mul (hPbound U hU) hXabs (abs_nonneg _) hBP
        _ = BP := mul_one BP

/-- A polynomial has an explicit finite Lipschitz constant on the unit box
for the entrywise `ℓ¹` distance.  The proof uses only polynomial induction and
the product rule estimate; no compactness theorem is needed. -/
theorem exists_peval_lipschitz_unitBox {n : ℕ} (P : Poly n) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ U V : Mat n n, InUnitBox U → InUnitBox V →
        |peval P U - peval P V| ≤ L * entryL1Dist U V := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      refine ⟨0, le_rfl, ?_⟩
      intro U V hU hV
      simp [peval]
  | add P Q hP hQ =>
      obtain ⟨LP, hLP, hPlip⟩ := hP
      obtain ⟨LQ, hLQ, hQlip⟩ := hQ
      refine ⟨LP + LQ, add_nonneg hLP hLQ, ?_⟩
      intro U V hU hV
      have hsplit :
          peval (P + Q) U - peval (P + Q) V =
            (peval P U - peval P V) + (peval Q U - peval Q V) := by
        simp [peval]
        ring
      rw [hsplit]
      calc
        |(peval P U - peval P V) + (peval Q U - peval Q V)| ≤
            |peval P U - peval P V| + |peval Q U - peval Q V| :=
          abs_add_le _ _
        _ ≤ LP * entryL1Dist U V + LQ * entryL1Dist U V :=
          add_le_add (hPlip U V hU hV) (hQlip U V hU hV)
        _ = (LP + LQ) * entryL1Dist U V := by ring
  | mul_X P ia hP =>
      obtain ⟨LP, hLP, hPlip⟩ := hP
      obtain ⟨B, hB, hPbound⟩ := exists_peval_bound_unitBox P
      refine ⟨LP + B, add_nonneg hLP hB, ?_⟩
      intro U V hU hV
      let D := entryL1Dist U V
      have hD : 0 ≤ D := entryL1Dist_nonneg U V
      have hUabs : |U ia.1 ia.2| ≤ 1 := by
        rw [abs_of_nonneg (hU ia.1 ia.2).1]
        exact (hU ia.1 ia.2).2
      have hcoord : |U ia.1 ia.2 - V ia.1 ia.2| ≤ D :=
        abs_entry_sub_le_entryL1Dist U V ia.1 ia.2
      have hsplit :
          peval (P * MvPolynomial.X ia) U -
              peval (P * MvPolynomial.X ia) V =
            (peval P U - peval P V) * U ia.1 ia.2 +
              peval P V * (U ia.1 ia.2 - V ia.1 ia.2) := by
        simp [peval]
        ring
      rw [hsplit]
      calc
        |(peval P U - peval P V) * U ia.1 ia.2 +
            peval P V * (U ia.1 ia.2 - V ia.1 ia.2)| ≤
          |(peval P U - peval P V) * U ia.1 ia.2| +
            |peval P V * (U ia.1 ia.2 - V ia.1 ia.2)| := abs_add_le _ _
        _ = |peval P U - peval P V| * |U ia.1 ia.2| +
            |peval P V| * |U ia.1 ia.2 - V ia.1 ia.2| := by
          rw [abs_mul, abs_mul]
        _ ≤ (LP * D) * 1 + B * D := by
          exact add_le_add
            (mul_le_mul (hPlip U V hU hV) hUabs (abs_nonneg _)
              (mul_nonneg hLP hD))
            (mul_le_mul (hPbound V hV) hcoord (abs_nonneg _) hB)
        _ = (LP + B) * entryL1Dist U V := by
          dsimp [D]
          ring

/-! ## The unsigned permutation weight -/

/-- Sum of the unsigned permutation monomials in a nonnegative matrix. -/
def permutationWeight {n : ℕ} (T : Mat n n) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ j, T (σ j) j

lemma allFunctionWeight_eq_one {n : ℕ} (T : Mat n n)
    (hT : ColumnStochastic T) :
    (∑ f : Fin n → Fin n, ∏ j, T (f j) j) = 1 := by
  rw [← Fintype.piFinset_univ]
  simpa only [Finset.mem_univ, ↓reduceIte, Finset.sum_filter,
    Finset.sum_product, Finset.prod_attach_univ, hT.2,
    Finset.prod_const_one] using
    (Finset.sum_prod_piFinset (R := ℝ) (Finset.univ : Finset (Fin n))
      (fun j i => T i j))

lemma functionWeight_nonneg {n : ℕ} (T : Mat n n)
    (hT : ColumnStochastic T) (f : Fin n → Fin n) :
    0 ≤ ∏ j, T (f j) j := by
  exact Finset.prod_nonneg fun j _ => hT.1 (f j) j

/-- After deleting one column, the weights of all choices for the remaining
columns still sum to one. -/
lemma partialFunctionWeight_eq_one {n : ℕ} (T : Mat n n)
    (hT : ColumnStochastic T) (j : Fin n) :
    (∑ f : {k : Fin n // k ≠ j} → Fin n,
      ∏ k : {k : Fin n // k ≠ j}, T (f k) k.1) = 1 := by
  rw [← Fintype.piFinset_univ]
  simpa only [Finset.mem_univ, ↓reduceIte, Finset.sum_filter,
    Finset.sum_product, Finset.prod_attach_univ, hT.2,
    Finset.prod_const_one] using
    (Finset.sum_prod_piFinset (R := ℝ) (Finset.univ : Finset (Fin n))
      (fun (k : {k : Fin n // k ≠ j}) (i : Fin n) => T i k.1))

/-- A permutation is determined by its values away from any one point. -/
def restrictPermutationEmbedding {n : ℕ} (j : Fin n) :
    Equiv.Perm (Fin n) ↪ ({k : Fin n // k ≠ j} → Fin n) := by
  let toFun : Equiv.Perm (Fin n) → ({k : Fin n // k ≠ j} → Fin n) :=
    fun σ k => σ k.1
  refine ⟨toFun, ?_⟩
  intro σ τ h
  apply Equiv.ext
  intro k
  by_cases hk : k = j
  · subst k
    obtain ⟨x, hx⟩ := τ.surjective (σ j)
    by_cases hxj : x = j
    · simpa [hxj] using hx.symm
    · have hrest := congrFun h ⟨x, hxj⟩
      have : σ x = σ j := hrest.trans hx
      exact (hxj (σ.injective this)).elim
  · exact congrFun h ⟨k, hk⟩

/-- The unsigned permutation weight is no larger than the largest entry in
any fixed column.  Delete that column and embed the remaining permutation
data into all unrestricted choices for the other columns. -/
lemma permutationWeight_le_columnMax {n : ℕ} (T : Mat n n)
    (hT : ColumnStochastic T) (j : Fin n) (a : ℝ)
    (hmax : ∀ i, T i j ≤ a) :
    permutationWeight T ≤ a := by
  let J := {k : Fin n // k ≠ j}
  let restrictPerm : Equiv.Perm (Fin n) ↪ (J → Fin n) :=
    restrictPermutationEmbedding j
  have hres_nonneg (f : J → Fin n) :
      0 ≤ ∏ k : J, T (f k) k.1 := by
    exact Finset.prod_nonneg fun k _ => hT.1 (f k) k.1
  have hres_sum : (∑ f : J → Fin n, ∏ k : J, T (f k) k.1) = 1 :=
    partialFunctionWeight_eq_one T hT j
  unfold permutationWeight
  calc
    (∑ σ : Equiv.Perm (Fin n), ∏ k, T (σ k) k) =
        ∑ σ : Equiv.Perm (Fin n),
          T (σ j) j * ∏ k : J, T (σ k.1) k.1 := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact Fintype.prod_eq_mul_prod_subtype_ne (fun k => T (σ k) k) j
    _ ≤ ∑ σ : Equiv.Perm (Fin n),
          a * ∏ k : J, T (σ k.1) k.1 := by
      apply Finset.sum_le_sum
      intro σ hσ
      exact mul_le_mul_of_nonneg_right (hmax (σ j))
        (hres_nonneg (fun k => σ k.1))
    _ = a * ∑ σ : Equiv.Perm (Fin n),
          ∏ k : J, T (σ k.1) k.1 := by rw [Finset.mul_sum]
    _ ≤ a * ∑ f : J → Fin n, ∏ k : J, T (f k) k.1 := by
      apply mul_le_mul_of_nonneg_left
      · calc
          (∑ σ : Equiv.Perm (Fin n), ∏ k : J, T (σ k.1) k.1) =
              ∑ f ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).map restrictPerm,
                ∏ k : J, T (f k) k.1 := by
            rw [Finset.sum_map]
            rfl
          _ ≤ ∑ f : J → Fin n, ∏ k : J, T (f k) k.1 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro f hf
              exact Finset.mem_univ f
            · intro f hf hnot
              exact hres_nonneg f
      · exact (hT.1 j j).trans (hmax j)
    _ = a := by rw [hres_sum, mul_one]

/-- If two distinct columns both choose the same row, the corresponding
collision event is disjoint from all permutations.  Its exact product weight
therefore subtracts from the total mass one. -/
lemma permutationWeight_le_one_sub_collision {n : ℕ} (T : Mat n n)
    (hT : ColumnStochastic T) (i j k : Fin n) (hjk : j ≠ k) :
    permutationWeight T ≤ 1 - T i j * T i k := by
  let permEmb : Equiv.Perm (Fin n) ↪ (Fin n → Fin n) :=
    ⟨fun σ => σ, fun _ _ h => Equiv.ext (congrFun h)⟩
  let permSet : Finset (Fin n → Fin n) :=
    (Finset.univ : Finset (Equiv.Perm (Fin n))).map permEmb
  let choices : Fin n → Finset (Fin n) :=
    Function.update (Function.update
      (fun _ : Fin n => (Finset.univ : Finset (Fin n))) j {i}) k {i}
  let eventSet : Finset (Fin n → Fin n) := Fintype.piFinset choices
  have hevent_mem (f : Fin n → Fin n) (hf : f ∈ eventSet) :
      f j = i ∧ f k = i := by
    have hall := Fintype.mem_piFinset.mp hf
    constructor
    · have := hall j
      simpa [eventSet, choices, hjk] using this
    · have := hall k
      simpa [eventSet, choices, hjk] using this
  have hdisj : Disjoint permSet eventSet := by
    rw [Finset.disjoint_left]
    intro f hfperm hfevent
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_map.mp hfperm
    have hev := hevent_mem σ hfevent
    exact hjk (σ.injective (hev.1.trans hev.2.symm))
  have hsum_event :
      (∑ f ∈ eventSet, ∏ q, T (f q) q) = T i j * T i k := by
    change (∑ f ∈ Fintype.piFinset choices, ∏ q, T (f q) q) = _
    calc
      (∑ f ∈ Fintype.piFinset choices, ∏ q, T (f q) q) =
          ∏ q, ∑ r ∈ choices q, T r q :=
        (Finset.prod_univ_sum choices (fun q r => T r q)).symm
      _ = T i j * T i k := by
        have hfun : (fun q => ∑ r ∈ choices q, T r q) =
            Function.update (Function.update (fun _ : Fin n => (1 : ℝ))
              j (T i j)) k (T i k) := by
          funext q
          by_cases hqk : q = k
          · subst q
            simp [choices]
          · by_cases hqj : q = j
            · subst q
              simp [choices, hjk]
            · simp [choices, hqk, hqj, hT.2]
        rw [hfun]
        simp [Finset.prod_update_of_mem, hjk, mul_comm]
  have hsum_perm :
      (∑ f ∈ permSet, ∏ q, T (f q) q) = permutationWeight T := by
    dsimp [permSet]
    rw [Finset.sum_map]
    rfl
  have htotal :
      (∑ f ∈ permSet ∪ eventSet, ∏ q, T (f q) q) ≤ 1 := by
    rw [← allFunctionWeight_eq_one T hT]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ _
    · intro f hf hnot
      exact functionWeight_nonneg T hT f
  rw [Finset.sum_union hdisj, hsum_perm, hsum_event] at htotal
  linarith

lemma det_eq_signedPermutationWeight {n : ℕ} (T : Mat n n) :
    Matrix.det (Matrix.of T) =
      ∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, T (σ j) j := by
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Units.smul_def]
  norm_num

lemma abs_det_le_permutationWeight {n : ℕ} (T : Mat n n)
    (hT : ColumnStochastic T) :
    |Matrix.det (Matrix.of T)| ≤ permutationWeight T := by
  rw [det_eq_signedPermutationWeight]
  calc
    |∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, T (σ j) j| ≤
        ∑ σ : Equiv.Perm (Fin n),
          |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ j, T (σ j) j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = permutationWeight T := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [abs_mul, ← Int.cast_abs, Equiv.Perm.sign_abs]
      simp only [Int.cast_one, one_mul]
      rw [abs_of_nonneg (functionWeight_nonneg T hT σ)]

/-- The permanent-like unsigned permutation weight is at most one for a
column-stochastic matrix, because its monomials form a subset of all column
choices, whose total weight is one. -/
lemma permutationWeight_le_one {n : ℕ} (T : Mat n n)
    (hT : ColumnStochastic T) : permutationWeight T ≤ 1 := by
  rw [← allFunctionWeight_eq_one T hT]
  unfold permutationWeight
  let emb : Equiv.Perm (Fin n) ↪ (Fin n → Fin n) :=
    ⟨fun σ => σ, fun _ _ h => Equiv.ext (congrFun h)⟩
  calc
    (∑ σ : Equiv.Perm (Fin n), ∏ j, T (σ j) j) =
        ∑ f ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).map emb,
          ∏ j, T (f j) j := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ f : Fin n → Fin n, ∏ j, T (f j) j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro f hf
        exact Finset.mem_univ f
      · intro f hf hnot
        exact functionWeight_nonneg T hT f

/-- Hadamard's determinant bound specialized to column-stochastic matrices,
proved here directly from the determinant expansion. -/
theorem detContraction_le_one {n : ℕ} (T : Mat n n)
    (hT : ColumnStochastic T) : detContraction T ≤ 1 := by
  have habs : |Matrix.det (Matrix.of T)| ≤ 1 :=
    (abs_det_le_permutationWeight T hT).trans (permutationWeight_le_one T hT)
  unfold detContraction
  have hsq := (sq_le_sq₀ (abs_nonneg (Matrix.det (Matrix.of T)))
    (by norm_num : (0 : ℝ) ≤ 1)).mpr habs
  simpa [sq_abs] using hsq

lemma detContraction_nonneg {n : ℕ} (T : Mat n n) :
    0 ≤ detContraction T := by
  exact sq_nonneg _

/-- Squaring the absolute determinant loses no more than the unsigned
permutation mass, since both are at most one. -/
lemma detContraction_le_permutationWeight {n : ℕ} (T : Mat n n)
    (hT : ColumnStochastic T) :
    detContraction T ≤ permutationWeight T := by
  have habsW := abs_det_le_permutationWeight T hT
  have habsOne : |Matrix.det (Matrix.of T)| ≤ 1 :=
    habsW.trans (permutationWeight_le_one T hT)
  have hsq : |Matrix.det (Matrix.of T)| ^ 2 ≤
      |Matrix.det (Matrix.of T)| := by
    nlinarith [abs_nonneg (Matrix.det (Matrix.of T))]
  simpa [detContraction, sq_abs] using hsq.trans habsW

/-- A permutation matrix is column-stochastic. -/
lemma permMatrix_columnStochastic {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ColumnStochastic (fun i j => (σ.permMatrix ℝ i j : ℝ)) := by
  constructor
  · intro i j
    change 0 ≤ ((σ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) ℝ) i j)
    rw [PEquiv.toMatrix_apply]
    split_ifs <;> norm_num
  · intro j
    simp [Equiv.Perm.permMatrix, ← Equiv.eq_symm_apply]

/-- The exact columnwise `ℓ¹` distance from a stochastic matrix to a
permutation matrix. -/
lemma columnL1Dist_permMatrix {n : ℕ} (T : Mat n n)
    (hT : ColumnStochastic T) (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    (∑ i, |T i j - (σ.permMatrix ℝ i j : ℝ)|) =
      2 * (1 - T (σ.symm j) j) := by
  have hentry_le : T (σ.symm j) j ≤ 1 := by
    calc
      T (σ.symm j) j ≤ ∑ i, T i j := by
        exact Finset.single_le_sum (fun i _ => hT.1 i j) (Finset.mem_univ _)
      _ = 1 := hT.2 j
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (σ.symm j))]
  have hother :
      (∑ i ∈ (Finset.univ : Finset (Fin n)).erase (σ.symm j),
        |T i j - (σ.permMatrix ℝ i j : ℝ)|) = 1 - T (σ.symm j) j := by
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin n)).erase (σ.symm j),
          |T i j - (σ.permMatrix ℝ i j : ℝ)|) =
          ∑ i ∈ (Finset.univ : Finset (Fin n)).erase (σ.symm j), T i j := by
        apply Finset.sum_congr rfl
        intro i hi
        have hine : i ≠ σ.symm j := Finset.ne_of_mem_erase hi
        have hσine : σ i ≠ j := by
          simpa [← Equiv.eq_symm_apply] using hine
        simp [Equiv.Perm.permMatrix, hσine, abs_of_nonneg (hT.1 i j)]
      _ = 1 - T (σ.symm j) j := by
        have hsum := hT.2 j
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (σ.symm j))] at hsum
        linarith
  rw [hother]
  simp [Equiv.Perm.permMatrix, abs_of_nonpos (sub_nonpos.mpr hentry_le)]
  ring

/-- Elementary stability of the determinant bound.  If the squared
determinant is at least `3/4`, choose a largest entry in every column.  The
collision estimate forces the chosen rows to be distinct, hence to form a
permutation, and the column-sum identities give an explicit `ℓ¹` bound. -/
theorem exists_permMatrix_close_of_detContraction_ge
    {n : ℕ} (hn : 1 ≤ n) (T : Mat n n) (hT : ColumnStochastic T)
    (hlarge : (3 : ℝ) / 4 ≤ detContraction T) :
    ∃ σ : Equiv.Perm (Fin n),
      entryL1Dist T (fun i j => (σ.permMatrix ℝ i j : ℝ)) ≤
        2 * (n : ℝ) * (1 - detContraction T) := by
  have : Nonempty (Fin n) :=
    Fin.pos_iff_nonempty.mp (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hmax_exists (j : Fin n) :
      ∃ i : Fin n, ∀ q, T q j ≤ T i j := by
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image
      (Finset.univ : Finset (Fin n)) (fun q => T q j) Finset.univ_nonempty
    exact ⟨i, fun q => hmax q (Finset.mem_univ q)⟩
  choose r hrmax using hmax_exists
  let d := detContraction T
  have hd0 : 0 ≤ d := detContraction_nonneg T
  have hdW : d ≤ permutationWeight T := detContraction_le_permutationWeight T hT
  have hdr (j : Fin n) : d ≤ T (r j) j :=
    hdW.trans (permutationWeight_le_columnMax T hT j (T (r j) j) (hrmax j))
  have hrinj : Function.Injective r := by
    intro j k hrjk
    by_contra hjk
    have hcollision := permutationWeight_le_one_sub_collision T hT (r j) j k hjk
    have hdrk : d ≤ T (r j) k := by simpa [hrjk] using hdr k
    have hprod : d * d ≤ T (r j) j * T (r j) k := by
      exact mul_le_mul (hdr j) hdrk hd0 (hT.1 (r j) j)
    have : d ≤ 1 - d * d := hdW.trans (hcollision.trans (sub_le_sub_left hprod 1))
    nlinarith
  let e : Equiv.Perm (Fin n) :=
    Equiv.ofBijective r (Finite.injective_iff_bijective.1 hrinj)
  let σ : Equiv.Perm (Fin n) := e.symm
  refine ⟨σ, ?_⟩
  have hσr (j : Fin n) : σ.symm j = r j := rfl
  unfold entryL1Dist
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ i, |T i j - (σ.permMatrix ℝ i j : ℝ)|) =
        ∑ j, 2 * (1 - T (σ.symm j) j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact columnL1Dist_permMatrix T hT σ j
    _ ≤ ∑ _j : Fin n, 2 * (1 - d) := by
      apply Finset.sum_le_sum
      intro j hj
      have := hdr j
      rw [hσr]
      linarith
    _ = 2 * (n : ℝ) * (1 - detContraction T) := by
      simp [d]
      ring

/-- Equality in the determinant contraction bound forces a stochastic matrix
to be a permutation matrix. -/
lemma exists_eq_permMatrix_of_detContraction_eq_one
    {n : ℕ} (hn : 1 ≤ n) (T : Mat n n) (hT : ColumnStochastic T)
    (hdet : detContraction T = 1) :
    ∃ σ : Equiv.Perm (Fin n),
      T = (fun i j => (σ.permMatrix ℝ i j : ℝ)) := by
  have hlarge : (3 : ℝ) / 4 ≤ detContraction T := by rw [hdet]; norm_num
  obtain ⟨σ, hclose⟩ :=
    exists_permMatrix_close_of_detContraction_ge hn T hT hlarge
  refine ⟨σ, ?_⟩
  let Q : Mat n n := fun i j => (σ.permMatrix ℝ i j : ℝ)
  have hdist_nonneg : 0 ≤ entryL1Dist T Q := entryL1Dist_nonneg T Q
  have hdist_le : entryL1Dist T Q ≤ 0 := by
    simpa [Q, hdet] using hclose
  have hdist : entryL1Dist T Q = 0 := le_antisymm hdist_le hdist_nonneg
  ext i j
  have habs := abs_entry_sub_le_entryL1Dist T Q i j
  rw [hdist] at habs
  have habszero : |T i j - Q i j| = 0 :=
    le_antisymm habs (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp habszero)

/-- A paper-facing predicate for permutation processing matrices. -/
def IsPermutationChannel {n : ℕ} (T : Mat n n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n),
    T = (fun i j => (σ.permMatrix ℝ i j : ℝ))

/-- For a column-stochastic matrix, squared determinant one is equivalent to
being a permutation channel. -/
lemma detContraction_eq_one_iff_isPermutationChannel
    {n : ℕ} (hn : 1 ≤ n) (T : Mat n n) (hT : ColumnStochastic T) :
    detContraction T = 1 ↔ IsPermutationChannel T := by
  constructor
  · exact exists_eq_permMatrix_of_detContraction_eq_one hn T hT
  · rintro ⟨σ, rfl⟩
    unfold detContraction
    change Matrix.det (σ.permMatrix ℝ) ^ 2 = 1
    rw [Matrix.det_permutation]
    have habs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
      rw [← Int.cast_abs, Equiv.Perm.sign_abs]
      norm_num
    nlinarith [sq_abs (((Equiv.Perm.sign σ : ℤ) : ℝ))]

/-! ## Passing the stochastic estimate through the simplex -/

/-- Every column-stochastic matrix lies in the entrywise unit box. -/
lemma columnStochastic_inUnitBox {n : ℕ} (T : Mat n n)
    (hT : ColumnStochastic T) : InUnitBox T := by
  intro i j
  refine ⟨hT.1 i j, ?_⟩
  calc
    T i j ≤ ∑ r, T r j :=
      Finset.single_le_sum (fun r _ => hT.1 r j) (Finset.mem_univ i)
    _ = 1 := hT.2 j

/-- Every probability-simplex matrix lies in the entrywise unit box. -/
lemma simplex_inUnitBox {n m : ℕ} (U : Mat n m) (hU : Simplex U) :
    InUnitBox U := by
  intro i a
  refine ⟨hU.1 i a, ?_⟩
  calc
    U i a ≤ ∑ q, U i q :=
      Finset.single_le_sum (fun q _ => hU.1 i q) (Finset.mem_univ a)
    _ ≤ ∑ r, ∑ q, U r q :=
      Finset.single_le_sum
        (fun r _ => Finset.sum_nonneg fun q _ => hU.1 r q)
        (Finset.mem_univ i)
    _ = 1 := hU.2

/-- Right multiplication by a simplex matrix contracts the entrywise `ℓ¹`
distance.  Only nonnegativity and total mass one are used. -/
lemma entryL1Dist_mul_le {n m : ℕ} (T Q : Mat n n) (U : Mat n m)
    (hU : Simplex U) :
    entryL1Dist (T * U) (Q * U) ≤ entryL1Dist T Q := by
  have hpoint (i : Fin n) (a : Fin m) :
      |(T * U) i a - (Q * U) i a| ≤
        ∑ j, |T i j - Q i j| * U j a := by
    have heq : (T * U) i a - (Q * U) i a =
        ∑ j, (T i j - Q i j) * U j a := by
      simp only [mat_mul_apply]
      calc
        (∑ j, T i j * U j a) - ∑ j, Q i j * U j a =
            ∑ j, (T i j * U j a - Q i j * U j a) :=
          (Finset.sum_sub_distrib
            (fun j => T i j * U j a) (fun j => Q i j * U j a)).symm
        _ = ∑ j, (T i j - Q i j) * U j a := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    rw [heq]
    calc
      |∑ j, (T i j - Q i j) * U j a| ≤
          ∑ j, |(T i j - Q i j) * U j a| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |T i j - Q i j| * U j a := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, abs_of_nonneg (hU.1 j a)]
  unfold entryL1Dist
  calc
    (∑ i, ∑ a, |(T * U) i a - (Q * U) i a|) ≤
        ∑ i, ∑ a, ∑ j, |T i j - Q i j| * U j a := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro a ha
      exact hpoint i a
    _ = ∑ i, ∑ j, |T i j - Q i j| * (∑ a, U j a) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, |T i j - Q i j| * 1 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left
      · calc
          (∑ a, U j a) ≤ ∑ r, ∑ a, U r a :=
            Finset.single_le_sum
              (fun r _ => Finset.sum_nonneg fun a _ => hU.1 r a)
              (Finset.mem_univ j)
          _ = 1 := hU.2
      · exact abs_nonneg _
    _ = ∑ i, ∑ j, |T i j - Q i j| := by simp

/-- `M` is a uniform upper bound for the normalized processing defect.  The
cross-multiplied formulation avoids division and remains meaningful at
permutation matrices. -/
def CompensationBound {n : ℕ} (P : Poly n) (M : ℝ) : Prop :=
  ∀ (T U : Mat n n), ColumnStochastic T → Simplex U →
    detContraction T * peval P (T * U) - peval P U ≤
      M * (1 - detContraction T)

lemma matrixOf_mat_mul {n : ℕ} (T U : Mat n n) :
    Matrix.of (T * U) = Matrix.of T * Matrix.of U := by
  ext i j
  rfl

lemma det_mat_mul {n : ℕ} (T U : Mat n n) :
    Matrix.det (Matrix.of (T * U)) =
      Matrix.det (Matrix.of T) * Matrix.det (Matrix.of U) := by
  rw [matrixOf_mat_mul, Matrix.det_mul]

/-- The algebraic heart of constant compensation: after multiplying by the
nonnegative determinant square of `U`, a normalized defect bound is exactly
the desired data-processing inequality. -/
theorem compensatedEval_dpi_of_bound
    {n : ℕ} (P : Poly n) {M : ℝ}
    (hbound : CompensationBound P M) :
    DPI (compensatedEval P M) := by
  intro T U hT hU
  have hdefect := hbound T U hT hU
  have hnormalized :
      detContraction T * (peval P (T * U) + M) ≤ peval P U + M := by
    dsimp [detContraction] at hdefect ⊢
    linarith
  have hdetU : 0 ≤ Matrix.det (Matrix.of U) ^ 2 := sq_nonneg _
  unfold compensatedEval
  rw [det_mat_mul]
  dsimp [detContraction] at hnormalized
  nlinarith [mul_le_mul_of_nonneg_left hnormalized hdetU]

/-- Enlarging a valid nonnegative compensation constant preserves the bound,
provided squared determinants of stochastic matrices are at most one. -/
lemma compensationBound_mono
    {n : ℕ} {P : Poly n} {M M' : ℝ}
    (hdet : ∀ T : Mat n n, ColumnStochastic T → detContraction T ≤ 1)
    (hMM' : M ≤ M') (hbound : CompensationBound P M) :
    CompensationBound P M' := by
  intro T U hT hU
  have h := hbound T U hT hU
  have hfactor : 0 ≤ 1 - detContraction T := sub_nonneg.mpr (hdet T hT)
  exact h.trans (mul_le_mul_of_nonneg_right hMM' hfactor)

/-! ## The constant-compensation theorem -/

/-- A completely algebraic uniform compensation bound.  The proof splits at
`det(T)^2 = 3/4`.  Below that threshold boundedness of `P` suffices; above it,
the explicit nearby-permutation estimate and row symmetry give a factor of
`1 - det(T)^2`. -/
theorem exists_compensationBound_of_rowSymmetric
    {n : ℕ} (hn : 1 ≤ n) (P : Poly n)
    (hsymm : RowSymmetricOnSimplex P) :
    ∃ M : ℝ, 0 ≤ M ∧ CompensationBound P M := by
  obtain ⟨B, hB, hPbound⟩ := exists_peval_bound_unitBox P
  obtain ⟨L, hL, hPlip⟩ := exists_peval_lipschitz_unitBox P
  let M : ℝ := 8 * B + B + 2 * (n : ℝ) * L
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨M, hM, ?_⟩
  intro T U hT hU
  let d := detContraction T
  have hd0 : 0 ≤ d := detContraction_nonneg T
  have hd1 : d ≤ 1 := detContraction_le_one T hT
  have hfactor : 0 ≤ 1 - d := sub_nonneg.mpr hd1
  have hTU : Simplex (T * U) := stochastic_mul_simplex hT hU
  have hUbox : InUnitBox U := simplex_inUnitBox U hU
  have hTUbox : InUnitBox (T * U) := simplex_inUnitBox (T * U) hTU
  have hPU := hPbound U hUbox
  have hPTU := hPbound (T * U) hTUbox
  by_cases hsmall : d < (3 : ℝ) / 4
  · have hPTUupper : peval P (T * U) ≤ B :=
      (le_abs_self _).trans hPTU
    have hPUlower : -B ≤ peval P U := by
      exact (neg_le_of_abs_le hPU)
    have hdefect :
        d * peval P (T * U) - peval P U ≤ 2 * B := by
      have hmul : d * peval P (T * U) ≤ d * B :=
        mul_le_mul_of_nonneg_left hPTUupper hd0
      nlinarith
    have hdenom : (1 : ℝ) / 4 < 1 - d := by linarith
    have h8B : 8 * B ≤ M := by
      dsimp [M]
      nlinarith [mul_nonneg hn0 hL]
    have h2B : 2 * B ≤ (8 * B) * (1 - d) := by
      nlinarith
    exact hdefect.trans
      (h2B.trans (mul_le_mul_of_nonneg_right h8B hfactor))
  · have hlarge : (3 : ℝ) / 4 ≤ d := le_of_not_gt hsmall
    obtain ⟨σ, hTclose⟩ :=
      exists_permMatrix_close_of_detContraction_ge hn T hT hlarge
    let Q : Mat n n := fun i j => (σ.permMatrix ℝ i j : ℝ)
    have hQ : ColumnStochastic Q := permMatrix_columnStochastic σ
    have hQU : Simplex (Q * U) := stochastic_mul_simplex hQ hU
    have hQUbox : InUnitBox (Q * U) := simplex_inUnitBox (Q * U) hQU
    have hdistMul : entryL1Dist (T * U) (Q * U) ≤
        2 * (n : ℝ) * (1 - d) := by
      exact (entryL1Dist_mul_le T Q U hU).trans hTclose
    have hlip := hPlip (T * U) (Q * U) hTUbox hQUbox
    have hCnonneg : 0 ≤ 2 * (n : ℝ) * L * (1 - d) := by positivity
    have hdelta :
        peval P (T * U) - peval P (Q * U) ≤
          2 * (n : ℝ) * L * (1 - d) := by
      calc
        peval P (T * U) - peval P (Q * U) ≤
            |peval P (T * U) - peval P (Q * U)| := le_abs_self _
        _ ≤ L * entryL1Dist (T * U) (Q * U) := hlip
        _ ≤ L * (2 * (n : ℝ) * (1 - d)) :=
          mul_le_mul_of_nonneg_left hdistMul hL
        _ = 2 * (n : ℝ) * L * (1 - d) := by ring
    have hd_delta :
        d * (peval P (T * U) - peval P (Q * U)) ≤
          2 * (n : ℝ) * L * (1 - d) := by
      by_cases hdelta0 : 0 ≤ peval P (T * U) - peval P (Q * U)
      · have := mul_le_mul hd1 hdelta hdelta0 (by norm_num : (0 : ℝ) ≤ 1)
        simpa using this
      · have hnonpos :
            d * (peval P (T * U) - peval P (Q * U)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hd0 (le_of_not_ge hdelta0)
        exact hnonpos.trans hCnonneg
    have hsymm : peval P (Q * U) = peval P U := hsymm σ U hU
    have hPUlower : -B ≤ peval P U := neg_le_of_abs_le hPU
    have hcoef : d - 1 ≤ 0 := by linarith
    have hconstant :
        (d - 1) * peval P U ≤ B * (1 - d) := by
      calc
        (d - 1) * peval P U ≤ (d - 1) * (-B) :=
          mul_le_mul_of_nonpos_left hPUlower hcoef
        _ = B * (1 - d) := by ring
    have hsplit :
        d * peval P (T * U) - peval P U =
          d * (peval P (T * U) - peval P (Q * U)) +
            (d - 1) * peval P U := by
      rw [hsymm]
      ring
    rw [hsplit]
    have hcore := add_le_add hd_delta hconstant
    have hcore' :
        d * (peval P (T * U) - peval P (Q * U)) +
            (d - 1) * peval P U ≤
          (2 * (n : ℝ) * L + B) * (1 - d) := by
      calc
        _ ≤ 2 * (n : ℝ) * L * (1 - d) + B * (1 - d) := hcore
        _ = (2 * (n : ℝ) * L + B) * (1 - d) := by ring
    have hcoreM : 2 * (n : ℝ) * L + B ≤ M := by
      dsimp [M]
      nlinarith
    exact hcore'.trans (mul_le_mul_of_nonneg_right hcoreM hfactor)

/-- The set of normalized defects appearing in the paper's definition of
`M_*(P)`. -/
def compensationRatioSet {n : ℕ} (P : Poly n) : Set ℝ :=
  {x | ∃ (T U : Mat n n), ColumnStochastic T ∧ Simplex U ∧
    ¬ IsPermutationChannel T ∧
    x = (detContraction T * peval P (T * U) - peval P U) /
      (1 - detContraction T)}

/-- The paper's explicit threshold `M_*(P)`, as a real supremum. -/
def compensationSup {n : ℕ} (P : Poly n) : ℝ :=
  sSup (compensationRatioSet P)

/-- The normalized-defect set is bounded above.  This is the formal
finiteness statement for `M_*(P)`. -/
theorem compensationRatioSet_bddAbove
    {n : ℕ} (hn : 1 ≤ n) (P : Poly n)
    (hsymm : RowSymmetricOnSimplex P) :
    BddAbove (compensationRatioSet P) := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_compensationBound_of_rowSymmetric hn P hsymm
  refine ⟨M, ?_⟩
  intro x hx
  obtain ⟨T, U, hT, hU, hnotperm, rfl⟩ := hx
  have hd1 : detContraction T ≤ 1 := detContraction_le_one T hT
  have hdne : detContraction T ≠ 1 := by
    intro heq
    exact hnotperm ((detContraction_eq_one_iff_isPermutationChannel hn T hT).mp heq)
  have hdenom : 0 < 1 - detContraction T := sub_pos.mpr (lt_of_le_of_ne hd1 hdne)
  exact (div_le_iff₀ hdenom).2 (hbound T U hT hU)

/-- The paper's supremum is bounded by the explicit algebraic compensation
constant constructed above. -/
theorem compensationSup_le_some_bound
    {n : ℕ} (hn : 1 ≤ n) (P : Poly n)
    (hsymm : RowSymmetricOnSimplex P) :
    ∃ M : ℝ, 0 ≤ M ∧ compensationSup P ≤ M := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_compensationBound_of_rowSymmetric hn P hsymm
  refine ⟨M, hM, ?_⟩
  apply Real.sSup_le
  · intro x hx
    obtain ⟨T, U, hT, hU, hnotperm, rfl⟩ := hx
    have hd1 : detContraction T ≤ 1 := detContraction_le_one T hT
    have hdne : detContraction T ≠ 1 := by
      intro heq
      exact hnotperm ((detContraction_eq_one_iff_isPermutationChannel hn T hT).mp heq)
    have hdenom : 0 < 1 - detContraction T := sub_pos.mpr (lt_of_le_of_ne hd1 hdne)
    exact (div_le_iff₀ hdenom).2 (hbound T U hT hU)
  · exact hM

/-- Any constant at least `max 0 M_*(P)` satisfies the cross-multiplied
compensation bound. -/
theorem compensationBound_of_compensationSup_le
    {n : ℕ} (hn : 1 ≤ n) (P : Poly n)
    (hsymm : RowSymmetricOnSimplex P) {M : ℝ}
    (hM : max 0 (compensationSup P) ≤ M) :
    CompensationBound P M := by
  have hbdd : BddAbove (compensationRatioSet P) :=
    compensationRatioSet_bddAbove hn P hsymm
  intro T U hT hU
  by_cases hperm : IsPermutationChannel T
  · obtain ⟨σ, rfl⟩ := hperm
    have hd : detContraction
        (fun i j => (σ.permMatrix ℝ i j : ℝ)) = 1 :=
      (detContraction_eq_one_iff_isPermutationChannel hn _
        (permMatrix_columnStochastic σ)).2 ⟨σ, rfl⟩
    have heval := hsymm σ U hU
    rw [hd]
    simpa using heval.le
  · have hd1 : detContraction T ≤ 1 := detContraction_le_one T hT
    have hdne : detContraction T ≠ 1 := by
      intro heq
      exact hperm ((detContraction_eq_one_iff_isPermutationChannel hn T hT).mp heq)
    have hdenom : 0 < 1 - detContraction T := sub_pos.mpr (lt_of_le_of_ne hd1 hdne)
    let x := (detContraction T * peval P (T * U) - peval P U) /
      (1 - detContraction T)
    have hxmem : x ∈ compensationRatioSet P :=
      ⟨T, U, hT, hU, hperm, rfl⟩
    have hxSup : x ≤ compensationSup P :=
      le_csSup hbdd hxmem
    have hSupM : compensationSup P ≤ M :=
      (le_max_right 0 (compensationSup P)).trans hM
    have hxM : x ≤ M := hxSup.trans hSupM
    exact (div_le_iff₀ hdenom).mp hxM

/-- Explicit paper version: every `M ≥ max {0, M_*(P)}` gives DPI. -/
theorem compensatedEval_dpi_of_compensationSup_le
    {n : ℕ} (hn : 1 ≤ n) (P : Poly n)
    (hsymm : RowSymmetricOnSimplex P) {M : ℝ}
    (hM : max 0 (compensationSup P) ≤ M) :
    DPI (compensatedEval P M) :=
  compensatedEval_dpi_of_bound P
    (compensationBound_of_compensationSup_le hn P hsymm hM)

/-- Paper-facing existence theorem: after adding a nonnegative constant
inside the determinant-square factor, every row-symmetric polynomial obeys
the full one-sided data-processing inequality on the square simplex. -/
theorem exists_constantCompensation_dpi
    {n : ℕ} (hn : 1 ≤ n) (P : Poly n)
    (hsymm : RowSymmetricOnSimplex P) :
    ∃ M : ℝ, 0 ≤ M ∧ DPI (compensatedEval P M) := by
  obtain ⟨M, hM, hbound⟩ :=
    exists_compensationBound_of_rowSymmetric hn P hsymm
  exact ⟨M, hM, compensatedEval_dpi_of_bound P hbound⟩


end SquarePolynomial

end

end Cslib.FiniteSampleInformation
