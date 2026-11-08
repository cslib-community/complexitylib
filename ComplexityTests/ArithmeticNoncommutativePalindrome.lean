/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Noncommutative.Nisan
import Complexity.Computability.Circuit.Arithmetic.Noncommutative.Palindrome

/-!
# The palindrome and the double

* `Pal_2 = x₀ x₀ + x₁ x₁` over two variables.
* `Pal_4` and `Doub_4` differ: `x₀ x₁ x₁ x₀` occurs in the first and not in the second.
* `rank M_2(Pal_4) = 9` over three variables.
* The least ABP size for `Pal_2` over two variables is exactly `1 + 2 + 1 = 4`.
* The palindrome circuit has `8` gates for `n = 2`, `m = 1`.
* The separation for `n = 10`, `m = 10`: the circuit has `311` gates, every ABP at least `10¹⁰`
  vertices.
-/

namespace ComplexityTests.ArithmeticNoncommutativePalindrome

open Cslib.Circuits Cslib.Circuits.Arithmetic FreeAlgebra

/-- `Pal_2 = x₀ x₀ + x₁ x₁`. -/
example : palindrome ℚ (Fin 2) 1 = ι ℚ 0 * ι ℚ 0 + ι ℚ 1 * ι ℚ 1 := by
  rw [palindrome_succ, palindrome_zero, Fin.sum_univ_two, mul_one, mul_one]

/-- `x₀ x₁ x₁ x₀` occurs in `Pal_4` ... -/
example : coeff (FreeMonoid.ofFn ![0, 1] * FreeMonoid.ofFn ![1, 0])
    (palindrome ℚ (Fin 2) 2) = 1 := by
  rw [palindrome, coeff_pairedWordPoly, ite_eq_left_iff.mpr]
  intro h
  exact absurd (funext fun i => by fin_cases i <;> rfl) h

/-- ... but not in `Doub_4`. -/
example : coeff (FreeMonoid.ofFn ![0, 1] * FreeMonoid.ofFn ![1, 0])
    (doubled ℚ (Fin 2) 2) = 0 := by
  rw [doubled, coeff_pairedWordPoly, ite_eq_right_iff.mpr]
  intro h
  have := congrFun h 0
  simp at this

/-- `rank M_2(Pal_4) = 3 ^ 2` over three variables. -/
example : (nisanMatrix 2 2 (palindrome ℚ (Fin 3) 2)).rank = 9 := by
  rw [rank_nisanMatrix_palindrome, Fintype.card_fin]
  norm_num

/-- The outer Nisan matrices of a nonzero polynomial homogeneous of degree `d` have rank `1`. -/
private theorem rank_nisanMatrix_zero_left {f : FreeAlgebra ℚ (Fin 2)} {d : ℕ}
    (hf : f.IsHomogeneous (0 + d)) (hf0 : f ≠ 0) : (nisanMatrix 0 d f).rank = 1 :=
  le_antisymm ((Matrix.rank_le_card_height _).trans (by simp))
    (one_le_rank_nisanMatrix hf hf0)

private theorem rank_nisanMatrix_zero_right {f : FreeAlgebra ℚ (Fin 2)} {d : ℕ}
    (hf : f.IsHomogeneous (d + 0)) (hf0 : f ≠ 0) : (nisanMatrix d 0 f).rank = 1 :=
  le_antisymm ((Matrix.rank_le_card_width _).trans (by simp))
    (one_le_rank_nisanMatrix hf hf0)

/-- The least ABP size for `Pal_2` over two variables is `1 + 2 + 1 = 4`. -/
example : IsLeast {s | ∃ A : NoncommABP ℚ (Fin 2) (1 + 1),
    A.polynomial = palindrome ℚ (Fin 2) 1 ∧ A.size = s} 4 := by
  have hf := isHomogeneous_pairedWordPoly (K := ℚ) fun u : Fin 1 → Fin 2 => u ∘ Fin.rev
  have hf0 := pairedWordPoly_ne_zero (K := ℚ) fun u : Fin 1 → Fin 2 => u ∘ Fin.rev
  have h := NoncommABP.isLeast_size hf hf0 two_ne_zero
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [rank_nisanMatrix_zero_left hf hf0, rank_nisanMatrix_zero_right hf hf0] at h
  have h1 := rank_nisanMatrix_palindrome (K := ℚ) (X := Fin 2) (m := 1)
  rw [palindrome, Fintype.card_fin] at h1
  rwa [show 1 + 1 - 1 = 1 from rfl, h1] at h

/-- The palindrome circuit has `7 · 1 + 1 = 8` gates for `n = 2`, `m = 1`. -/
example : (palCircuit ℚ 2 1).size = 8 := size_palCircuit 2 1

/-- Evaluated over `ℤ` at `(2, 3)`, the palindrome circuit for `m = 1` gives `2² + 3² = 13`. -/
example : (palCircuit ℤ 2 1).eval (arithInterpretationWith ℤ (algebraMap ℤ ℤ)) ![2, 3] 0 = 13 := by
  rw [eval_palCircuit, palindrome_succ, palindrome_zero]
  simp [Fin.sum_univ_two]

/-- The separation for `n = m = 10`: `311` gates against at least `10¹⁰` vertices. -/
example : (∃ c : Circuit (arithSignature ℚ) 10 1, c.size = 311 ∧
      c.noncommPolynomial 0 = palindrome ℚ (Fin 10) 10) ∧
    ∀ A : NoncommABP ℚ (Fin 10) (10 + 10), A.polynomial = palindrome ℚ (Fin 10) 10 →
      10 ^ 10 ≤ A.size :=
  palindrome_separation 10 10

end ComplexityTests.ArithmeticNoncommutativePalindrome
