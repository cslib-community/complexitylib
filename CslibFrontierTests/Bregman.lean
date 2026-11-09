/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Combinatorics.Bregman

/-!
# Tests for Brégman's theorem

Concrete instances of `Matrix.permanent_le_prod_factorial_rpow` and its equality case: the all-ones
matrix `J₃` attains the bound with `per J₃ = 6 = (3!) ^ (3 / 3)`, the upper triangular all-ones
`2 × 2` matrix has permanent `1 < √2`, a zero row gives `0 ≤ 1`, and the block-diagonal matrix
`K_{2,2} ⊕ K_{1,1}` attains the bound `2`.
-/

open Finset Matrix

namespace CslibFrontierTests.Bregman

/-- `(3!) ^ (1 / 3)` cubed is `3! = 6`. -/
private theorem factorial_three_rpow_cube :
    (((3 : ℕ).factorial : ℝ) ^ (1 / ((3 : ℕ) : ℝ))) ^ 3 = 6 := by
  rw [one_div, Real.rpow_inv_natCast_pow (by positivity) (by norm_num)]
  norm_num [Nat.factorial]

/-- The all-ones `3 × 3` matrix. -/
def J₃ : Matrix (Fin 3) (Fin 3) ℕ := Matrix.of fun _ _ => 1

/-- The all-ones matrix is a single block `K_{3,3}`: Brégman's bound `(3!) ^ (3 / 3) = 6` is
attained. -/
example : (J₃.permanent : ℝ) = 6 := by
  rw [permanent_eq_prod_factorial_rpow_of_eq_ite (A := J₃) (fun _ => ()) fun _ _ => rfl]
  have hrow : ∀ i, ∑ j, J₃ i j = 3 := fun i => by decide +revert
  simp only [hrow, Fin.prod_univ_three]
  rw [← factorial_three_rpow_cube]
  ring

/-- Directly, `per J₃ = 3! = 6`. -/
example : J₃.permanent = 6 := by decide

/-- The upper triangular all-ones `2 × 2` matrix. -/
def U₂ : Matrix (Fin 2) (Fin 2) ℕ := !![1, 1; 0, 1]

example : U₂.permanent = 1 := by decide

/-- For `U₂` Brégman's bound is `2! ^ (1 / 2) * 1! ^ (1 / 1) = √2`, strictly above `per U₂ = 1`. -/
example : (U₂.permanent : ℝ) <
    ∏ i, ((∑ j, U₂ i j).factorial : ℝ) ^ (1 / ((∑ j, U₂ i j : ℕ) : ℝ)) := by
  have hU : U₂.permanent = 1 := by decide
  have hs : (∑ j, U₂ 0 j) = 2 ∧ (∑ j, U₂ 1 j) = 1 := by decide
  have h2 : ((2 : ℕ).factorial : ℝ) ^ (1 / ((2 : ℕ) : ℝ)) = √2 := by
    rw [Real.sqrt_eq_rpow]; norm_num [Nat.factorial]
  have h1 : ((1 : ℕ).factorial : ℝ) ^ (1 / ((1 : ℕ) : ℝ)) = 1 := by norm_num
  rw [hU, Fin.prod_univ_two, hs.1, hs.2, h2, h1, mul_one, Nat.cast_one]
  exact Real.lt_sqrt zero_le_one |>.2 (by norm_num)

example : (U₂.permanent : ℝ) ≤
    ∏ i, ((∑ j, U₂ i j).factorial : ℝ) ^ (1 / ((∑ j, U₂ i j : ℕ) : ℝ)) :=
  permanent_le_prod_factorial_rpow fun i j => by fin_cases i <;> fin_cases j <;> decide

/-- A zero row: the permanent is `0` and the row's factor is `0! ^ (1 / 0) = 1`. -/
def Z₂ : Matrix (Fin 2) (Fin 2) ℕ := !![0, 0; 1, 1]

example : Z₂.permanent = 0 := by decide

example : ((∑ j, Z₂ 0 j).factorial : ℝ) ^ (1 / ((∑ j, Z₂ 0 j : ℕ) : ℝ)) = 1 := by
  have : (∑ j, Z₂ 0 j) = 0 := by decide
  simp [this]

example : (Z₂.permanent : ℝ) ≤
    ∏ i, ((∑ j, Z₂ i j).factorial : ℝ) ^ (1 / ((∑ j, Z₂ i j : ℕ) : ℝ)) :=
  permanent_le_prod_factorial_rpow fun i j => by fin_cases i <;> fin_cases j <;> decide

/-- The block-diagonal matrix of `K_{2,2} ⊕ K_{1,1}`, with blocks `{0, 1}` and `{2}`. -/
def B₃ : Matrix (Fin 3) (Fin 3) ℕ := !![1, 1, 0; 1, 1, 0; 0, 0, 1]

example : B₃.permanent = 2 := by decide

/-- `B₃` attains Brégman's bound: `per B₃ = (2!) ^ (1/2) * (2!) ^ (1/2) * 1! ^ 1 = 2`. -/
example : (B₃.permanent : ℝ) =
    ∏ i, ((∑ j, B₃ i j).factorial : ℝ) ^ (1 / ((∑ j, B₃ i j : ℕ) : ℝ)) :=
  permanent_eq_prod_factorial_rpow_of_eq_ite (fun i : Fin 3 => decide (i = 2))
    fun i j => by fin_cases i <;> fin_cases j <;> rfl

/-- A `2`-regular `4 × 4` 0/1 matrix (`K_{2,2} ⊕ K_{2,2}`) has permanent at most
`2! ^ (4 / 2) = 4`, attained here. -/
def R₄ : Matrix (Fin 4) (Fin 4) ℕ := !![1, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, 1]

example : R₄.permanent = 4 := by decide

/-- The regular bound for `R₄` evaluates to `2! ^ (4 / 2) = 4`. -/
example : ((2 : ℕ).factorial : ℝ) ^ ((Fintype.card (Fin 4) : ℝ) / (2 : ℕ)) = 4 := by
  rw [Fintype.card_fin, show ((4 : ℕ) : ℝ) / (2 : ℕ) = (2 : ℕ) by norm_num, Real.rpow_natCast]
  norm_num [Nat.factorial]

example :
    (R₄.permanent : ℝ) ≤ ((2 : ℕ).factorial : ℝ) ^ ((Fintype.card (Fin 4) : ℝ) / (2 : ℕ)) :=
  permanent_le_factorial_rpow_card_div (fun i j => by fin_cases i <;> fin_cases j <;> decide)
    (by decide)

/-- Brégman's bound for perfect matchings of a bipartite graph given by a Boolean adjacency
function, as in `Cslib.Circuits.BipartiteMatching.HasPerfectMatching`. -/
example {V : Type*} [Fintype V] [DecidableEq V] (G : V × V → Bool) :
    (#{σ : V ≃ V | ∀ v, G (v, σ v) = true} : ℝ) ≤
      ∏ v, ((#{w | G (v, w) = true} : ℕ).factorial : ℝ) ^
        (1 / (#{w | G (v, w) = true} : ℝ)) :=
  Equiv.card_filter_forall_rel_le_prod_factorial_rpow fun v w => G (v, w) = true

end CslibFrontierTests.Bregman
