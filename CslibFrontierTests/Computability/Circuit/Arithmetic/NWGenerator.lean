/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.NWGenerator

/-!
# The Nisan–Wigderson generator for formulas

Over `ℚ`, with `f = X 0` in one variable: the generator of one block is the seed variable, the
formula `x₀` is nonzero on the grid `{0, 1}`, and the hitting set has at most two points. With two
copies of the same block, the formula `x₀ - x₁` vanishes at the generator, and the hybrid
argument returns a formula of product-depth at most one with `f` as a root. Assigning constants
to part of the variables of `x₀ * y₀` keeps it nonzero.
-/

public section

namespace CslibFrontierTests.NWGenerator

open Cslib.Circuits Cslib.Circuits.Arithmetic Finset MvPolynomial

/-- One block: the single variable is the single seed variable. -/
def block : Fin 1 ↪ Fin 1 :=
  Function.Embedding.refl _

/-- The generator of `X 0` on one block is the seed variable. -/
theorem nwGenerator_X :
    nwGenerator (X 0 : MvPolynomial (Fin 1) ℚ) (fun _ : Fin 1 => block) 0 = X 0 := by
  simp [block]

/-- The formula `x₀`. -/
def input : SPFormula ℚ 1 :=
  .input 0

/-- The formula `x₀` composed with the generator is nonzero at a point of `{0, 1}`. -/
theorem exists_grid_point :
    ∃ z : Fin 1 → ℚ, (∀ l, ∃ k ≤ input.nodeCount * 1, z l = k) ∧
      eval (fun i => eval z (nwGenerator (X 0) (fun _ => block) i))
        input.polynomial ≠ 0 :=
  exists_eval_nwGenerator_ne_zero (totalDegree_X_le 0) (by simp [input, block])

/-- The hitting set of the generator of `X 0` hits `x₀`. -/
theorem exists_mem_hittingSet :
    ∃ x ∈ generatorHittingSet (X 0 : MvPolynomial (Fin 1) ℚ) (fun _ => block)
      (input.nodeCount * 1),
      eval x input.polynomial ≠ 0 :=
  exists_mem_generatorHittingSet_eval_ne_zero (totalDegree_X_le 0)
    (by simp [input, block])

/-- On a grid `{0, 1}` with one seed variable the hitting set has at most two points. -/
theorem card_hittingSet_le :
    #(generatorHittingSet (X 0 : MvPolynomial (Fin 1) ℚ) (fun _ : Fin 1 => block) 1) ≤ 2 := by
  simpa using card_generatorHittingSet_le (X 0 : MvPolynomial (Fin 1) ℚ) (fun _ => block) 1

/-- The formula `x₀ - x₁`. -/
def difference : SPFormula ℚ 2 :=
  SPFormula.add ![1, -1] ![.input 0, .input 1]

/-- `x₀ - x₁` vanishes at the generator of `X 0` with two copies of one block, so the hybrid
argument gives a nonzero formula of product-depth at most one that has `X 0` as a root. -/
theorem exists_root_formula_difference :
    ∃ F : SPFormula ℚ (1 + 1), F.productDepth ≤ 0 + 1 ∧
      F.nodeCount ≤ difference.nodeCount * (2 ^ 1 * (1 + 1) + 2) ∧
      F.polynomial ≠ 0 ∧
      aeval (Fin.lastCases (X 0) X : Fin 2 → MvPolynomial (Fin 1) ℚ) F.polynomial = 0 := by
  classical
  refine exists_root_formula_of_generator_vanishing (L := Fin 1)
    (fun i => by rw [degreeOf_X]; split_ifs <;> simp) (S := fun _ => block)
    (fun _ _ _ => ?_) ?_ ?_ ?_
  · exact (Finset.card_le_univ _).trans (by simp)
  · exact Nat.le_zero.2 (by simp [difference])
  · simp only [difference, SPFormula.polynomial_add, Fin.sum_univ_two]
    intro h
    have := congrArg (eval ![1, 0]) h
    simp at this
  · simp [difference, Fin.sum_univ_two, block]

/-- Assigning a constant to `x₀` in `x₀ * y₀` keeps it nonzero. -/
theorem exists_partial_eval :
    ∃ v : Unit → ℚ, aeval (Sum.elim (fun a => C (v a)) X)
      (X (.inl ()) * X (.inr ()) : MvPolynomial (Unit ⊕ Unit) ℚ) ≠ 0 :=
  exists_aeval_sumElim_ne_zero (mul_ne_zero (X_ne_zero _) (X_ne_zero _))

end CslibFrontierTests.NWGenerator
