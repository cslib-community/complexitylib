/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Arithmetic.RelativeRank

/-!
# Set-multilinear polynomials and relative rank

The inner product `∑ i, x_i y_i` on two blocks of `n` variables has full relative rank `1`. The
monomial `x y`, with one row variable and two column variables, has relative rank `√(1 / 2)`, so
the imbalance bound is attained. Further tests check both sides of the set-multilinearity
predicate and that the hypotheses of subadditivity and multiplicativity can be met.
-/

namespace ComplexityTests.ArithmeticRelativeRank

open Cslib.Circuits.Arithmetic MvPolynomial

/-! ### Two blocks of `n` variables -/

/-- The inner product `∑ i, x_i y_i`, with `x_i = (0, i)` and `y_i = (1, i)`. -/
private noncomputable def innerProduct (K : Type*) [CommSemiring K] (n : ℕ) :
    MvPolynomial (Fin 2 × Fin n) K :=
  ∑ i, X (0, i) * X (1, i)

/-- The choice of the `k`-th variable in block `b`. -/
private def pick {n : ℕ} (b : Fin 2) (k : Fin n) :
    BlockChoice (Prod.fst : Fin 2 × Fin n → Fin 2) {b} :=
  fun i => ⟨(i, k), rfl⟩

private theorem blockMonomial_pick {n : ℕ} (b : Fin 2) (k : Fin n) :
    blockMonomial Prod.fst {b} (pick b k) = Finsupp.single (b, k) 1 := by
  classical
  ext v
  rw [blockMonomial_apply, Finsupp.single_apply]
  by_cases hv : v.1 = b
  · obtain ⟨v₁, v₂⟩ := v
    simp only at hv
    subst hv
    simp [pick]
  · simp only [Finset.mem_singleton, hv, dite_false]
    exact (ite_eq_right fun h => hv (by rw [← h])).symm

private theorem card_block (n : ℕ) (b : Fin 2) :
    Fintype.card {x : Fin 2 × Fin n // x.1 = b} = n :=
  (Fintype.card_congr
    { toFun := fun x => x.1.2
      invFun := fun k => ⟨(b, k), rfl⟩
      left_inv := fun x => Subtype.ext (Prod.ext x.2.symm rfl)
      right_inv := fun _ => rfl }).trans (Fintype.card_fin n)

private theorem card_blockChoice_singleton (n : ℕ) (b : Fin 2) :
    Fintype.card (BlockChoice (Prod.fst : Fin 2 × Fin n → Fin 2) {b}) = n := by
  rw [card_blockChoice, Finset.prod_singleton, card_block]

private theorem coeff_innerProduct {K : Type*} [CommSemiring K] {n : ℕ} (i j : Fin n) :
    (innerProduct K n).coeff (Finsupp.single (0, i) 1 + Finsupp.single (1, j) 1) =
      if i = j then 1 else 0 := by
  classical
  simp only [innerProduct, coeff_sum, X, monomial_mul_monomial, one_mul, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp [Finsupp.single_left_inj]
  · intro k _ hk
    simp [Finsupp.single_add_single_eq_single_add_single, hk]
  · simp

/-- The relative-rank matrix of the inner product contains the identity matrix. -/
private theorem relMatrix_innerProduct_submatrix {K : Type*} [Field K] (n : ℕ) :
    (relMatrix Prod.fst {0} {1} (innerProduct K n)).submatrix (pick 0) (pick 1) = 1 := by
  ext i j
  rw [Matrix.submatrix_apply, relMatrix_apply, blockMonomial_pick, blockMonomial_pick,
    coeff_innerProduct, Matrix.one_apply]

/-- **Full rank**: the inner product has relative rank `1`. -/
theorem relRank_innerProduct {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) :
    relRank Prod.fst {0} {1} (innerProduct K n) = 1 := by
  have hrank : (relMatrix Prod.fst {0} {1} (innerProduct K n)).rank = n := by
    refine le_antisymm ?_ ?_
    · exact (Matrix.rank_le_card_height _).trans (card_blockChoice_singleton n 0).le
    · calc n = (1 : Matrix (Fin n) (Fin n) K).rank := by simp
        _ ≤ _ := by
          rw [← relMatrix_innerProduct_submatrix]
          exact Matrix.rank_submatrix_le _ _ _
  rw [relRank, hrank, card_blockChoice_singleton, card_blockChoice_singleton, Nat.cast_mul,
    Real.sqrt_mul_self (Nat.cast_nonneg n), div_self (by exact_mod_cast hn.ne')]

/-- The inner product is set-multilinear on both blocks. -/
example {K : Type*} [CommSemiring K] (n : ℕ) :
    IsSetMultilinear Prod.fst {0, 1} (innerProduct K n) := by
  refine Finset.sum_induction _ _ (fun f g => IsSetMultilinear.add) IsSetMultilinear.zero ?_
  intro i _
  exact (isSetMultilinear_X Prod.fst (0, i)).mul (isSetMultilinear_X Prod.fst (1, i))
    (by simp)

/-- A square is not set-multilinear: its variable has exponent two. -/
example (v : Fin 2 × Fin 3) : ¬ IsSetMultilinear Prod.fst {v.1} (X v * X v : MvPolynomial _ ℚ) := by
  classical
  intro h
  obtain ⟨x, hx⟩ := h (Finsupp.single v 2) (by simp [X, coeff_monomial, ← Finsupp.single_add])
  have hv := congrArg (· v) hx
  simp only [blockMonomial_apply, Finsupp.single_eq_same] at hv
  split_ifs at hv
  omega

private theorem card_blockChoice_empty (n : ℕ) :
    Fintype.card (BlockChoice (Prod.fst : Fin 2 × Fin n → Fin 2) ∅) = 1 := by
  rw [card_blockChoice, Finset.prod_empty]

/-- **Multiplicativity** with imbalance gives an evaluated bound: each factor of a term `x_i y_i`
of the inner product lives on one block, so its relative rank is at most `√(1 / n)` by imbalance,
and the term has relative rank at most `1 / n`. -/
example {K : Type*} [Field K] {n : ℕ} (i : Fin n) :
    relRank Prod.fst {0} {1} (X (0, i) * X (1, i) : MvPolynomial (Fin 2 × Fin n) K) ≤ 1 / n := by
  have h := relRank_mul_le (blk := (Prod.fst : Fin 2 × Fin n → Fin 2)) (A := {0}) (B := {1})
    (S := {0}) (T := {1}) (isSetMultilinear_X (K := K) Prod.fst (0, i))
    (isSetMultilinear_X (K := K) Prod.fst (1, i)) (by decide) (by decide) (by decide)
  have e₀ : ({0} ∩ {0} : Finset (Fin 2)) = {0} := by decide
  have e₁ : ({1} ∩ {0} : Finset (Fin 2)) = ∅ := by decide
  have e₂ : ({0} ∩ {1} : Finset (Fin 2)) = ∅ := by decide
  have e₃ : ({1} ∩ {1} : Finset (Fin 2)) = {1} := by decide
  rw [e₀, e₁, e₂, e₃] at h
  have h₁ := relRank_le_sqrt_cols_div_rows Prod.fst {0} ∅
    (X (0, i) : MvPolynomial (Fin 2 × Fin n) K)
  have h₂ := relRank_le_sqrt_rows_div_cols Prod.fst ∅ {1}
    (X (1, i) : MvPolynomial (Fin 2 × Fin n) K)
  rw [card_blockChoice_singleton, card_blockChoice_empty, Nat.cast_one] at h₁ h₂
  calc _ ≤ _ := h
    _ ≤ √(1 / (n : ℝ)) * √(1 / (n : ℝ)) :=
      mul_le_mul h₁ h₂ (relRank_nonneg _ _ _ _) (Real.sqrt_nonneg _)
    _ = 1 / n := Real.mul_self_sqrt (by positivity)

/-- **Multiplicativity for finite products**: `x_k y_k`, as a product over the two blocks, has
relative rank at most the product of the relative ranks of its factors on their blocks. -/
example {K : Type*} [Field K] {n : ℕ} (k : Fin n) :
    relRank Prod.fst {0} {1} (∏ b : Fin 2, X (b, k) : MvPolynomial (Fin 2 × Fin n) K) ≤
      ∏ b : Fin 2, relRank Prod.fst ({0} ∩ {b}) ({1} ∩ {b})
        (X (b, k) : MvPolynomial (Fin 2 × Fin n) K) :=
  relRank_prod_le Finset.univ (T := fun b => {b})
    (fun _ _ _ _ hbc => Finset.disjoint_singleton.2 hbc)
    (fun b _ => isSetMultilinear_X Prod.fst (b, k)) (by decide) (by decide)

/-- **Subadditivity**: the full-rank inner product of length two is the sum of its two terms. -/
example {K : Type*} [Field K] :
    (1 : ℝ) ≤ relRank Prod.fst {0} {1} (X (0, 0) * X (1, 0) : MvPolynomial (Fin 2 × Fin 2) K) +
      relRank Prod.fst {0} {1} (X (0, 1) * X (1, 1) : MvPolynomial (Fin 2 × Fin 2) K) := by
  rw [← relRank_innerProduct (K := K) (by decide : 0 < 2)]
  refine (le_of_eq ?_).trans (relRank_add_le _ _ _ _ _)
  simp [innerProduct, Fin.sum_univ_two]

/-- Scaling by a nonzero constant keeps full rank. -/
example {K : Type*} [Field K] {n : ℕ} (hn : 0 < n) {c : K} (hc : c ≠ 0) :
    relRank Prod.fst {0} {1} (c • innerProduct K n) = 1 := by
  rw [relRank_smul _ _ _ hc, relRank_innerProduct hn]

/-! ### Tight imbalance: one row variable and two column variables -/

/-- Block `0` holds variable `0`; block `1` holds variables `1` and `2`. -/
private def blk3 : Fin 3 → Fin 2 := ![0, 1, 1]

/-- **Tight imbalance**: `x y` has a nonzero `1 × 2` matrix, so its relative rank `1 / √2` equals
the imbalance bound `√(rows / columns)`. -/
example : relRank blk3 {0} {1} (X 0 * X 1 : MvPolynomial (Fin 3) ℚ) =
    √((Fintype.card (BlockChoice blk3 {0}) : ℝ) / Fintype.card (BlockChoice blk3 {1})) := by
  have hrows : Fintype.card (BlockChoice blk3 {0}) = 1 := by
    rw [card_blockChoice]
    decide
  have hcols : Fintype.card (BlockChoice blk3 {1}) = 2 := by
    rw [card_blockChoice]
    decide
  let r : BlockChoice blk3 {0} := fun i => ⟨0, by
    obtain ⟨i, hi⟩ := i
    obtain rfl := Finset.mem_singleton.mp hi
    rfl⟩
  let c : BlockChoice blk3 {1} := fun i => ⟨1, by
    obtain ⟨i, hi⟩ := i
    obtain rfl := Finset.mem_singleton.mp hi
    rfl⟩
  have hentry : relMatrix blk3 {0} {1} (X 0 * X 1 : MvPolynomial (Fin 3) ℚ) r c = 1 := by
    classical
    have hr : blockMonomial blk3 {0} r = Finsupp.single 0 1 := by
      ext v
      rw [blockMonomial_apply, Finsupp.single_apply]
      fin_cases v <;> simp [blk3, r]
    have hc : blockMonomial blk3 {1} c = Finsupp.single 1 1 := by
      ext v
      rw [blockMonomial_apply, Finsupp.single_apply]
      fin_cases v <;> simp [blk3, c]
    rw [relMatrix_apply, hr, hc]
    simp [X, coeff_monomial]
  have hrank : (relMatrix blk3 {0} {1} (X 0 * X 1 : MvPolynomial (Fin 3) ℚ)).rank = 1 := by
    refine le_antisymm ((Matrix.rank_le_card_height _).trans hrows.le) ?_
    have hsub : (relMatrix blk3 {0} {1} (X 0 * X 1 : MvPolynomial (Fin 3) ℚ)).submatrix
        (fun _ : Fin 1 => r) (fun _ : Fin 1 => c) = 1 := by
      ext i j
      rw [Matrix.submatrix_apply, hentry, Subsingleton.elim i j, Matrix.one_apply_eq]
    calc 1 = (1 : Matrix (Fin 1) (Fin 1) ℚ).rank := by simp
      _ ≤ _ := by
        rw [← hsub]
        exact Matrix.rank_submatrix_le _ _ _
  rw [relRank, hrank, hrows, hcols]
  norm_num [Real.sqrt_div', Real.sqrt_one]

end ComplexityTests.ArithmeticRelativeRank
