/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Defs
public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.NWGenerator
public import CslibFrontier.Computability.Circuit.Arithmetic.RootFormula

/-!
# Hardness of a multilinear polynomial gives hitting sets for constant-depth formulas

Let `f` be a multilinear polynomial in `m` variables of degree at most `d`, and let the blocks
`S i ⊆ L`, `i < n`, of a design pairwise meet in at most `a` points. If `f` has no formula of
product-depth `Δ + 2` with at most `rootCost (s (2 ^ a (a + 1) + 2)) d` nodes, then the values
of the Nisan–Wigderson generator `nwGenerator f S` on the grid `{0, …, s d} ^ L` form a hitting
set for the polynomials in `n` variables computed by formulas of product-depth `Δ` with at most
`s` nodes (`isHittingSet_generatorHittingSet_of_hard`). This is the hardness-to-randomness
theorem of Kabanets and Impagliazzo [KabanetsImpagliazzo2004] for constant-depth formulas, in
the form of Chou, Kumar and Solomon [ChouKumarSolomon2019, Theorem 2.3] and of Bhattacharjee,
Kumar, Rai, Ramanathan, Saptharishi and Saraf [BhattacharjeeEtAl2025, Theorem 6.1].

## Proof

Let `C` be such a formula with a nonzero polynomial. If the composition of `C` with the
generator is nonzero, it is nonzero at a point of the grid
(`exists_mem_generatorHittingSet_eval_ne_zero`). Otherwise the hybrid argument
(`exists_root_formula_of_generator_vanishing`) gives a nonzero polynomial in `m + 1` variables,
computed by a formula of product-depth `Δ + 1`, with root `f`; by
`SPFormula.exists_formula_of_root`, `f` has a formula of product-depth `Δ + 2` and at most
`rootCost (s (2 ^ a (a + 1) + 2)) d` nodes, against the hypothesis.

## Main results

* `isHittingSet_generatorHittingSet_of_hard`: hardness gives a hitting set.

## References

* [V. Kabanets, R. Impagliazzo, *Derandomizing polynomial identity tests means proving circuit
  lower bounds*][KabanetsImpagliazzo2004]
* [C.-N. Chou, M. Kumar, N. Solomon, *Closure results for polynomial
  factorization*][ChouKumarSolomon2019], Theorem 2.3 and Lemma 7.1 (arXiv:1803.05933 numbering)
* [S. Bhattacharjee, M. Kumar, S. Rai, V. Ramanathan, R. Saptharishi, S. Saraf, *Closure under
  factorization from a result of Furstenberg*][BhattacharjeeEtAl2025], Theorem 6.1 (unrefereed
  preprint)
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable {K L : Type*} [Field K] [CharZero K] [Fintype L] [DecidableEq L] {m n : ℕ}

/-- `rootCost` is monotone in both arguments. -/
theorem SPFormula.rootCost_mono {s s' D D' : ℕ} (hs : s ≤ s') (hD : D ≤ D') :
    SPFormula.rootCost s D ≤ SPFormula.rootCost s' D' := by
  unfold SPFormula.rootCost
  gcongr

/-- **Hardness gives hitting sets for constant-depth formulas.** If the multilinear polynomial
`f`, of degree at most `d`, has no formula of product-depth at most `Δ + 2` with at most
`rootCost (s (2 ^ a (a + 1) + 2)) d` nodes, and the blocks `S i` pairwise meet in at most `a`
points, then `generatorHittingSet f S (s d)` hits every polynomial in `n` variables computed by
a formula of product-depth at most `Δ` with at most `s` nodes. -/
theorem isHittingSet_generatorHittingSet_of_hard {f : MvPolynomial (Fin m) K}
    (hmul : ∀ i, f.degreeOf i ≤ 1) {d : ℕ} (hd : f.totalDegree ≤ d)
    {S : Fin n → (Fin m ↪ L)} {a : ℕ}
    (hS : ∀ i j, i ≠ j → #(univ.map (S i) ∩ univ.map (S j)) ≤ a) {Δ s : ℕ}
    (hhard : ∀ G : SPFormula K m, G.polynomial = f → G.productDepth ≤ Δ + 2 →
      SPFormula.rootCost (s * (2 ^ a * (a + 1) + 2)) d < G.nodeCount) :
    IsHittingSet (generatorHittingSet f S (s * d))
      {p | ∃ C : SPFormula K n, C.polynomial = p ∧ C.productDepth ≤ Δ ∧ C.nodeCount ≤ s} := by
  classical
  rintro _ ⟨C, rfl, hΔ, hs⟩ hC0
  by_cases hvan : aeval (nwGenerator f S) C.polynomial = 0
  · exfalso
    have : Infinite K := Infinite.of_injective Nat.cast Nat.cast_injective
    obtain ⟨F, hFΔ, hFsize, hF0, hFroot⟩ :=
      exists_root_formula_of_generator_vanishing hmul hS hΔ hC0 hvan
    obtain ⟨G, hGf, hGΔ, hGsize⟩ := SPFormula.exists_formula_of_root hFΔ hF0 hFroot
    refine (hhard G hGf hGΔ).not_ge (hGsize.trans (SPFormula.rootCost_mono ?_ hd))
    exact hFsize.trans (Nat.mul_le_mul_right _ hs)
  · obtain ⟨x, hx, hne⟩ := exists_mem_generatorHittingSet_eval_ne_zero hd hvan
    refine ⟨x, ?_, hne⟩
    rw [generatorHittingSet] at hx ⊢
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hx
    refine mem_image.2 ⟨z, Fintype.mem_piFinset.2 fun l => ?_, rfl⟩
    obtain ⟨k, hk, hzk⟩ := mem_image.1 (Fintype.mem_piFinset.1 hz l)
    exact mem_image.2 ⟨k, mem_range.2 (lt_of_lt_of_le (mem_range.1 hk)
      (Nat.succ_le_succ (Nat.mul_le_mul_right _ hs))), hzk⟩

end Cslib.Circuits.Arithmetic
