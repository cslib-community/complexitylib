/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Foundations.Data.MvPolynomial.SetMultilinearProjection
import Mathlib.Algebra.BigOperators.Fin

/-!
# The set-multilinear projection on small polynomials

The variables `x₀, x₁, x₂` are split into the blocks `{x₀, x₁}` and `{x₂}`. The projection of
`(1 + x₀)(2 + x₂)` onto both blocks is `x₀ x₂`, computed term by term; its projection onto the
first block is `2 x₀`, computed through both product formulas; its projection onto no blocks is the
constant coefficient `2`. Ordered splits are checked on both sides. The monomial
`x₀ x₁`, two variables of one block, is set-multilinear on no set of blocks. Merging `x₀` and `x₁`
into one variable is a renaming along the blocks, and commutes with the projection.
-/

namespace ComplexityTests.SetMultilinearProjection

open MvPolynomial

/-- The blocks `{x₀, x₁}` and `{x₂}`. -/
private def blk : Fin 3 → Fin 2 := ![0, 0, 1]

/-- The polynomial `(1 + x₀)(2 + x₂)`. -/
private noncomputable def f : MvPolynomial (Fin 3) ℚ := (1 + X 0) * (C 2 + X 2)

/-- Term by term: only `x₀ x₂` takes one variable from each block. -/
example : smProj blk Finset.univ f = X 0 * X 2 := by
  have hf : f = C 2 + C 2 * X 0 + X 2 + X 0 * X 2 := by
    rw [f]
    ring
  have h02 : IsSetMultilinear blk Finset.univ (X 0 * X 2 : MvPolynomial (Fin 3) ℚ) := by
    have h := (isSetMultilinear_X (K := ℚ) blk 0).mul (isSetMultilinear_X blk 2)
      (by decide)
    exact (by decide : ({blk 0} ∪ {blk 2} : Finset (Fin 2)) = Finset.univ) ▸ h
  rw [hf, map_add, map_add, map_add, smProj_C_mul, smProj_C, smProj_X, smProj_X,
    h02.smProj_eq_self, ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide)]
  ring

/-- Through the product formula `smProj_mul`, summing over the two subsets of the first block:
the projection of `f` onto the first block is `2 x₀`. -/
example : smProj blk {0} f = C 2 * X 0 := by
  have hP : ({0} : Finset (Fin 2)).powerset = {∅, {0}} := by decide
  rw [f, smProj_mul, hP, Finset.sum_pair (by decide), Finset.sdiff_empty, Finset.sdiff_self,
    smProj_empty, smProj_empty]
  simp [smProj_one, smProj_C, smProj_X, blk, mul_comm]

/-- Through the finite product formula `smProj_prod`, summing over the two ordered splits of the
first block into two parts. -/
example : smProj blk {0} (∏ j, ![1 + X 0, C 2 + X 2] j : MvPolynomial (Fin 3) ℚ) = C 2 * X 0 := by
  have hB : blockSplits (Fin 2) ({0} : Finset (Fin 2)) = {![{0}, ∅], ![∅, {0}]} := by decide
  rw [smProj_prod, hB, Finset.sum_pair (by decide)]
  simp [Fin.prod_univ_two, smProj_one, smProj_C, smProj_X, smProj_empty, blk, mul_comm]

/-- On no blocks the projection is the constant coefficient. -/
example : smProj blk ∅ f = C 2 := by
  simp [smProj_empty, f]

/-- The monomial `x₀ x₁` takes two variables from the first block, so it is set-multilinear on
no set of blocks. -/
example (S : Finset (Fin 2)) :
    Finsupp.single 0 1 + Finsupp.single 1 1 ∉ Set.range (blockMonomial blk S) := by
  intro h
  have h0 := DFunLike.congr_fun (mem_range_blockMonomial_iff.1 h) 0
  have h2 : (Finsupp.mapDomain blk (Finsupp.single 0 1 + Finsupp.single 1 1)) 0 = 2 := by
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    simp [blk]
  have h1 : (∑ i ∈ S, Finsupp.single i 1 : Fin 2 →₀ ℕ) 0 ≤ 1 := by
    rw [Finsupp.finsetSum_apply]
    simp only [Finsupp.single_apply, Finset.sum_ite_eq']
    split_ifs <;> omega
  omega

/-- A split of the two blocks into two parts, and a family that is not a split. -/
example : (![{0}, {1}] : Fin 2 → Finset (Fin 2)) ∈ blockSplits (Fin 2) Finset.univ := by
  refine mem_blockSplits.2 ⟨fun i j hij => ?_, by decide⟩
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

example : (![{0}, {0}] : Fin 2 → Finset (Fin 2)) ∉ blockSplits (Fin 2) Finset.univ := by
  rw [mem_blockSplits]
  rintro ⟨-, h⟩
  exact absurd h (by decide)

/-- Renaming each variable to its block merges `x₀` and `x₁`; it is a renaming along the blocks,
so it commutes with the projection, although it is not injective. -/
example (g : MvPolynomial (Fin 3) ℚ) (S : Finset (Fin 2)) :
    rename blk (smProj blk S g) = smProj id S (rename blk g) :=
  rename_smProj (blk := blk) (blk' := id) blk (fun _ => rfl) S g

end ComplexityTests.SetMultilinearProjection
