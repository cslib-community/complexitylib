/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Arithmetic.WordPolynomial

/-!
# Word polynomials and iterated matrix multiplication

For the word `(1, -1)` the word polynomial with sink `0` is the inner product
`x₀ y₀ + x₁ y₁` of the two blocks: its coefficients are computed for two monomials, its relative
rank is `1`, and it is a projection of `IMM_{2,2}`. For the word `(2, -1, 1)`, with sum `2`, the
relative rank is `1 / 2`, and the word is `2`-unbiased, so the word polynomial with any sink of
length `2` is a projection of `IMM_{4,3}`.
-/

namespace ComplexityTests.ArithmeticWordPolynomial

open Cslib.Circuits.Arithmetic MvPolynomial

/-! ### The word `(1, -1)` -/

/-- The word `(1, -1)`: one positive and one negative block of two variables each. -/
private def w₁ : Fin 2 → ℤ := ![1, -1]

/-- The monomial `x₀ y₀`: the first variable of each block. -/
private def pick₀₀ : WordChoice w₁ := fun _ => ⟨0, Nat.two_pow_pos _⟩

/-- The monomial `x₀ y₁`: the first variable of block `0` and the second of block `1`. -/
private def pick₀₁ : WordChoice w₁ := fun i => ⟨i, by fin_cases i <;> decide⟩

/-- The monomial `x₀ y₀` has equal strings: its coefficient is `1`. -/
example : (wordPoly ℚ w₁ 0).coeff (wordMono pick₀₀) = 1 := by
  rw [coeff_wordPoly, ite_eq_left (by decide)]

/-- The monomial `x₀ y₁` has different strings: its coefficient is `0`. -/
example : (wordPoly ℚ w₁ 0).coeff (wordMono pick₀₁) = 0 := by
  rw [coeff_wordPoly, ite_eq_right (by decide)]

/-- The positive blocks of `(1, -1)` are `{0}`. -/
example : wordPos w₁ = {0} := by decide

/-- **Full rank**: the word polynomial of `(1, -1)` has relative rank `1`. -/
example : relRank Sigma.fst (wordPos w₁) (wordNeg w₁) (wordPoly ℚ w₁ 0) = 1 := by
  rw [relRank_wordPoly (by decide)]
  norm_num [w₁, Fin.sum_univ_two]

/-- `(1, -1)` is `1`-unbiased. -/
private theorem isUnbiased_w₁ : IsUnbiased w₁ 1 := by
  unfold IsUnbiased
  decide

/-- **Lemma 8** on a tiny instance: the inner product of two blocks of two variables is a
projection of `IMM_{2,2}`. -/
example : IsProjection (wordPoly ℚ w₁ 0) (imm ℚ 2 2) :=
  isProjection_wordPoly_imm isUnbiased_w₁ le_rfl (by decide)

/-- The substitution of Lemma 8 maps the variable `(i, a, c)` of `IMM_{2,2}` into block `i`. -/
example (i : Fin 2) (a c : Fin 2) (v : WordVar w₁) (h : wordSubst w₁ 0 2 ℚ (i, a, c) = .inl v) :
    v.1 = i :=
  wordSubst_eq_inl h

/-! ### The word `(2, -1, 1)` -/

/-- The word `(2, -1, 1)`, with sum `2`: blocks of four, two and two variables. -/
private def w₂ : Fin 3 → ℤ := ![2, -1, 1]

/-- **Imbalance attained**: the word polynomial of `(2, -1, 1)` has relative rank `2 ^ (-1)`. -/
example (τ : ℕ) (hτ : τ < 4) :
    relRank Sigma.fst (wordPos w₂) (wordNeg w₂) (wordPoly ℚ w₂ τ) = 1 / 2 := by
  rw [relRank_wordPoly (by simpa [w₂, Fin.sum_univ_three] using hτ)]
  norm_num [w₂, Fin.sum_univ_three]

/-- `(2, -1, 1)` is `2`-unbiased: its prefix sums are `0, 2, 1, 2`. -/
private theorem isUnbiased_w₂ : IsUnbiased w₂ 2 := by
  unfold IsUnbiased
  decide

/-- **Lemma 8**: each word polynomial of `(2, -1, 1)` is a projection of `IMM_{4,3}`. -/
example (τ : ℕ) (hτ : τ < 4) : IsProjection (wordPoly ℚ w₂ τ) (imm ℚ 4 3) :=
  isProjection_wordPoly_imm isUnbiased_w₂ le_rfl (by simpa [w₂, Fin.sum_univ_three] using hτ)

end ComplexityTests.ArithmeticWordPolynomial
