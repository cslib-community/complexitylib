/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.SetMultilinearLowerBound
public import Complexity.Computability.Circuit.Arithmetic.Setmultilinearize

/-!
# Lower bound for constant-depth formulas computing IMM over any field

The lower bound of Limaye, Srinivasan and Tavenas [LimayeSrinivasanTavenas2021] for formulas of
unbounded fan-in, in explicit form, over any field and with no set-multilinearity or homogeneity
hypothesis (`SPFormula.two_rpow_le_of_imm`): let `10 d ≤ k`, `2 ^ k ≤ n` and `1 ≤ Δ`. A formula
of product-depth at most `Δ` computing `IMM_{n,d}` (with its variables renamed) satisfies

`2 ^ (k (d ^ (1 / (4 ^ Δ - 1)) / 20 - 1 / 2)) ≤ smCost d ^ Δ * nodeCount F`,

where `smCost d = 4 * (2 * (d + 1) ^ 2) ^ (d + 1)` (`SPFormula.smCost`). For fixed `d` and `Δ`
with `d ^ (1 / (4 ^ Δ - 1)) > 10`, the left side grows exponentially in `k`, so the bound is
nontrivial once `k` is large enough; small instances, where `smCost d` dominates, are trivial.

**Proof.** Set-multilinearize `F` by gate simulation [Forbes2024, Cor. 27]: on the blocks of
`IMM_{n,d}` (block `i` holds the entries of the `i`-th matrix), the formula
`G = SPFormula.smPart blk univ F` is syntactically set-multilinear on all blocks, has
product-depth at most `2 Δ` and at most `smCost d ^ Δ * nodeCount F` nodes, and computes the
set-multilinear part of the polynomial of `F`. The set-multilinear projection commutes with
renaming the variables along their blocks (`MvPolynomial.rename_smProj`) and fixes `IMM_{n,d}`,
which is set-multilinear (`smProj_imm`), so `G` computes `IMM_{n,d}` after the same renaming. The
lower bound for set-multilinear formulas, LST Lemma 15
(`SPFormula.IsSetMultilinear.two_rpow_le_nodeCount_of_imm`), at product-depth `2 Δ` gives the
bound, since `2 ^ (2 Δ) = 4 ^ Δ`.

The source derives Theorem 1 from Lemma 15 through its Proposition 9 (§3, p. 8), which
set-multilinearizes circuits at the cost of doubling the product-depth and needs characteristic
`0` or larger than `d`. Forbes's gate simulation, used here, also doubles the product-depth but
works over any field.

**Original.** The explicit non-asymptotic statement, its constant, the formula-level gate
simulation and the composition with LST Lemma 15.

## Main results

* `Cslib.Circuits.Arithmetic.smProj_imm`: `IMM_{n,d}` is its own set-multilinear part on all
  blocks.
* `Cslib.Circuits.Arithmetic.SPFormula.two_rpow_le_of_imm`: the lower bound for formulas over any
  field.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], ECCC TR21-081 revision 1: Theorem 1 (p. 1),
  Proposition 9 (§3, p. 8), Lemma 15 (§5, p. 11)
* [M. A. Forbes, *Low-depth algebraic circuit lower bounds over any field*][Forbes2024],
  Corollary 27 (p. 31:14)
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

variable {K : Type*} {n d : ℕ}

/-- **`IMM_{n,d}` is set-multilinear**: its part on all blocks, block `i` holding the entries of
the `i`-th matrix, is itself. -/
theorem smProj_imm [CommSemiring K] [NeZero n] :
    smProj Prod.fst Finset.univ (imm K n d) = imm K n d := by
  rw [← rename_polynomial_immFormula n,
    ← rename_smProj (blk := fun v => (immVarEquiv n d v).1) (blk' := Prod.fst) _ fun _ => rfl,
    ((isSetMultilinear_immFormula n).isSetMultilinear_polynomial).smProj_eq_self]

namespace SPFormula

variable {N : ℕ}

/-- **Lower bound for formulas computing `IMM_{n,d}` over any field** (LST Theorem 1 for
formulas, ECCC TR21-081 rev. 1, p. 1, through [Forbes2024, Cor. 27]; explicit form original): let
`10 d ≤ k`, `2 ^ k ≤ n` and `1 ≤ Δ`. If a formula `F` over a field, of product-depth at most `Δ`,
computes `IMM_{n,d}` with its variables renamed by `e`, then
`2 ^ (k (d ^ (1 / (4 ^ Δ - 1)) / 20 - 1 / 2)) ≤ smCost d ^ Δ * nodeCount F`. There is no
assumption on the characteristic, on homogeneity or on set-multilinearity. -/
theorem two_rpow_le_of_imm [Field K] [NeZero n] (e : Fin N → Fin d × Fin n × Fin n) {k Δ : ℕ}
    (hk : 10 * d ≤ k) (hn : 2 ^ k ≤ n) (hΔ : 1 ≤ Δ) {F : SPFormula K N}
    (hFΔ : F.productDepth ≤ Δ) (hFP : rename e F.polynomial = imm K n d) :
    (2 : ℝ) ^ ((k : ℝ) * ((d : ℝ) ^ (1 / (4 ^ Δ - 1 : ℝ)) / 20 - 1 / 2)) ≤
      smCost d ^ Δ * F.nodeCount := by
  classical
  set blk : Fin N → Fin d := fun v => (e v).1
  set G := smPart blk Finset.univ F
  have hG : G.IsSetMultilinear blk Finset.univ := isSetMultilinear_smPart _ F
  have hGΔ : G.productDepth ≤ 2 * Δ :=
    (productDepth_smPart_le _ F).trans (Nat.mul_le_mul_left 2 hFΔ)
  have hGP : rename e G.polynomial = imm K n d := by
    rw [polynomial_smPart, rename_smProj (blk' := Prod.fst) e fun _ => rfl, hFP, smProj_imm]
  have h := hG.two_rpow_le_nodeCount_of_imm e hk hn (by omega) hGΔ hGP
  have h4 : (2 : ℝ) ^ (2 * Δ) = 4 ^ Δ := by
    rw [pow_mul]
    norm_num
  rw [h4] at h
  refine h.trans ?_
  have hsize : G.nodeCount ≤ smCost d ^ Δ * F.nodeCount :=
    (nodeCount_smPart_le _ F).trans
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (one_le_smCost d) hFΔ))
  exact_mod_cast hsize

end SPFormula

end Cslib.Circuits.Arithmetic
