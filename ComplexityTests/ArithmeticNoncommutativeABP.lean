/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Noncommutative.Nisan

/-!
# Non-commutative ABPs and Nisan's theorem

A concrete width-one ABP of degree `1` computing `x₀ + x₁` (nonvacuity of `NoncommABP`), its size,
homogeneity holding and failing, and two entries of Nisan's matrix `M_1(x₀ x₁)` showing that the
order of the variables matters. A width-one ABP of degree `2` computes `x₀ x₁`. With
`one_le_rank_nisanMatrix` this gives `rank M_k(x₀ x₁) = 1` for `k ≤ 2`, so the least ABP size for
`x₀ x₁` is exactly `3`: Nisan's theorem with the bound attained. For `x₀ x₀ + x₁ x₁` the middle
matrix `M_1` is the `2 × 2` identity, so the least ABP size is exactly `1 + 2 + 1 = 4`, attained
by the construction with a middle layer of width `2`.
-/

namespace ComplexityTests.ArithmeticNoncommutativeABP

open Cslib.Circuits.Arithmetic FreeAlgebra

/-- The width-one ABP of degree `1` with every edge coefficient `1`. -/
private noncomputable abbrev sumABP : NoncommABP ℚ (Fin 2) 1 where
  width _ := 1
  width_zero := rfl
  width_deg := rfl
  weight _ _ _ _ := 1

/-- It computes `x₀ + x₁`. -/
example : sumABP.polynomial = ι ℚ 0 + ι ℚ 1 := by
  rw [NoncommABP.polynomial, Fintype.sum_unique, NoncommABP.pre_succ, Fintype.sum_unique,
    NoncommABP.pre_zero, one_mul, NoncommABP.edge, Fin.sum_univ_two]
  simp

/-- Its size counts the source and the sink. -/
example : sumABP.size = 2 := by
  simp [NoncommABP.size]

/-- A variable is homogeneous of degree `1` ... -/
example : (ι ℚ (0 : Fin 2)).IsHomogeneous 1 := isHomogeneous_ι 0

/-- ... and not of degree `2`. -/
example : ¬ (ι ℚ (0 : Fin 2)).IsHomogeneous 2 := by
  intro h
  have := h (FreeMonoid.of 0) (by simp [coeff_ι])
  simp at this

/-- `x₀ x₁`. -/
private noncomputable def f01 : FreeAlgebra ℚ (Fin 2) := ι ℚ 0 * ι ℚ 1

private theorem isHomogeneous_f01 : f01.IsHomogeneous 2 :=
  (isHomogeneous_ι 0).mul (isHomogeneous_ι 1)

private theorem coeff_f01 (a b : Fin 2) :
    coeff (FreeMonoid.of a * FreeMonoid.of b) f01 = if a = 0 ∧ b = 1 then 1 else 0 := by
  rw [f01, coeff_mul_mul_of_isHomogeneous _ _ _ (by simpa using isHomogeneous_ι (R := ℚ) 0),
    coeff_ι, coeff_ι]
  fin_cases a <;> fin_cases b <;> simp [FreeMonoid.of_injective.eq_iff]

private theorem f01_ne_zero : f01 ≠ 0 := by
  intro h
  have := coeff_f01 0 1
  simp [h] at this

/-- The entry of `M_1(x₀ x₁)` at `(x₀, x₁)` is `1` ... -/
example : nisanMatrix 1 1 f01 ![0] ![1] = 1 := by
  simpa [FreeMonoid.ofFn] using coeff_f01 0 1

/-- ... but at `(x₁, x₀)` it is `0`: the variables do not commute. -/
example : nisanMatrix 1 1 f01 ![1] ![0] = 0 := by
  simpa [FreeMonoid.ofFn] using coeff_f01 1 0

/-- The width-one ABP of degree `2` reading `x₀` and then `x₁`. -/
private noncomputable abbrev prodABP : NoncommABP ℚ (Fin 2) 2 where
  width _ := 1
  width_zero := rfl
  width_deg := rfl
  weight k x _ _ := if (x : ℕ) = k then 1 else 0

private theorem polynomial_prodABP : prodABP.polynomial = f01 := by
  rw [NoncommABP.polynomial, Fintype.sum_unique, NoncommABP.pre_succ, Fintype.sum_unique,
    NoncommABP.pre_succ, Fintype.sum_unique, NoncommABP.pre_zero, one_mul, NoncommABP.edge,
    NoncommABP.edge, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [f01]

/-- Every Nisan matrix of `x₀ x₁` has rank `1`: at least `1` since `x₀ x₁ ≠ 0`, at most the width
`1` of `prodABP`. -/
private theorem rank_f01 (k : ℕ) (hk : k ≤ 2) : (nisanMatrix k (2 - k) f01).rank = 1 := by
  have hk' : k + (2 - k) = 2 := by omega
  refine le_antisymm ?_ (one_le_rank_nisanMatrix (by rw [hk']; exact isHomogeneous_f01) f01_ne_zero)
  have := prodABP.rank_nisanMatrix_le_width k (2 - k) hk'
  rwa [polynomial_prodABP] at this

/-- `rank M_1(x₀ x₁) = 1`. -/
example : (nisanMatrix 1 1 f01).rank = 1 := rank_f01 1 (by norm_num)

/-- `prodABP` has size `3` ... -/
example : prodABP.size = 3 := by simp [NoncommABP.size]

/-- ... which is optimal: by Nisan's theorem the least size of an ABP for `x₀ x₁` is
`1 + 1 + 1 = 3`. -/
example : IsLeast {s | ∃ A : NoncommABP ℚ (Fin 2) 2, A.polynomial = f01 ∧ A.size = s} 3 := by
  have h := NoncommABP.isLeast_size isHomogeneous_f01 f01_ne_zero two_ne_zero
  rwa [Finset.sum_congr rfl fun k hk => rank_f01 k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
    Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h

/-- `x₀ x₀ + x₁ x₁`. -/
private noncomputable def g : FreeAlgebra ℚ (Fin 2) := ι ℚ 0 * ι ℚ 0 + ι ℚ 1 * ι ℚ 1

private theorem isHomogeneous_g : g.IsHomogeneous 2 :=
  ((isHomogeneous_ι 0).mul (isHomogeneous_ι 0)).add ((isHomogeneous_ι 1).mul (isHomogeneous_ι 1))

private theorem coeff_g (a b : Fin 2) :
    coeff (FreeMonoid.of a * FreeMonoid.of b) g = if a = b then 1 else 0 := by
  have h1 : ∀ x : Fin 2, (ι ℚ x).IsHomogeneous (FreeMonoid.of a).length := fun x => by
    simpa using isHomogeneous_ι (R := ℚ) x
  rw [g, map_add, coeff_mul_mul_of_isHomogeneous _ _ _ (h1 0),
    coeff_mul_mul_of_isHomogeneous _ _ _ (h1 1), coeff_ι, coeff_ι, coeff_ι, coeff_ι]
  fin_cases a <;> fin_cases b <;> simp [FreeMonoid.of_injective.eq_iff]

private theorem g_ne_zero : g ≠ 0 := by
  intro h
  have := coeff_g 0 0
  simp [h] at this

/-- `M_1(x₀ x₀ + x₁ x₁)` is the identity matrix. -/
private theorem nisanMatrix_g : nisanMatrix 1 1 g = 1 := by
  ext u v
  have hu : FreeMonoid.ofFn u = FreeMonoid.of (u 0) := rfl
  have hv : FreeMonoid.ofFn v = FreeMonoid.of (v 0) := rfl
  rw [nisanMatrix_apply, hu, hv, coeff_g, Matrix.one_apply]
  refine if_congr ⟨fun h => funext fun i => ?_, fun h => congrFun h 0⟩ rfl rfl
  rwa [Subsingleton.elim i 0]

/-- `rank M_1(x₀ x₀ + x₁ x₁) = 2`: the optimal ABP has a middle layer of width `2`. -/
example : (nisanMatrix 1 1 g).rank = 2 := by
  rw [nisanMatrix_g, Matrix.rank_one, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  rfl

private theorem rank_outer (k : ℕ) (hk : k = 0 ∨ k = 2) : (nisanMatrix k (2 - k) g).rank = 1 := by
  have hk' : k + (2 - k) = 2 := by omega
  have hf : g.IsHomogeneous (k + (2 - k)) := by rw [hk']; exact isHomogeneous_g
  refine le_antisymm ?_ (one_le_rank_nisanMatrix hf g_ne_zero)
  rcases hk with rfl | rfl
  · exact (Matrix.rank_le_card_height _).trans (by simp)
  · exact (Matrix.rank_le_card_width _).trans (by simp)

/-- The least ABP size for `x₀ x₀ + x₁ x₁` is `1 + 2 + 1 = 4`. -/
example : IsLeast {s | ∃ A : NoncommABP ℚ (Fin 2) 2, A.polynomial = g ∧ A.size = s} 4 := by
  have h := NoncommABP.isLeast_size isHomogeneous_g g_ne_zero two_ne_zero
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    rank_outer 0 (Or.inl rfl), rank_outer 2 (Or.inr rfl), show 2 - 1 = 1 from rfl, nisanMatrix_g,
    Matrix.rank_one, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  exact h

/-- Nisan's theorem at `x₀ x₁`: an ABP with optimal widths exists. -/
example : ∃ A : NoncommABP ℚ (Fin 2) 2, A.polynomial = f01 ∧
    ∀ k m, k + m = 2 → A.width k = (nisanMatrix k m f01).rank :=
  NoncommABP.exists_width_eq_rank isHomogeneous_f01 f01_ne_zero two_ne_zero

/-- The lower bound applies to every ABP computing `x₀ x₁`. -/
example (A : NoncommABP ℚ (Fin 2) 2) (hA : A.polynomial = f01) :
    (nisanMatrix 1 1 f01).rank ≤ A.width 1 :=
  hA ▸ A.rank_nisanMatrix_le_width 1 1 rfl

end ComplexityTests.ArithmeticNoncommutativeABP
