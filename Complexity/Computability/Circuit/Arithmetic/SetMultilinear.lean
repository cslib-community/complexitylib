/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.SigmaPi
public import Complexity.Foundations.Data.MvPolynomial.SetMultilinear

/-!
# Set-multilinear formulas compute set-multilinear polynomials

A formula of unbounded fan-in that is set-multilinear on a set `S` of blocks
(`Cslib.Circuits.Arithmetic.SPFormula.IsSetMultilinear`, a syntactic condition on the formula)
computes a polynomial that is set-multilinear on `S` (`MvPolynomial.IsSetMultilinear`, a condition
on its support), so the relative-rank bounds of [LimayeSrinivasanTavenas2021] apply to it. The
proof is by induction on the formula predicate: inputs and constants are set-multilinear on their
own block and on no block, sum gates are closed under scaling and sums, and product gates under
products over pairwise disjoint sets of blocks.

## Main results

* `Cslib.Circuits.Arithmetic.SPFormula.IsSetMultilinear.isSetMultilinear_polynomial`: a
  set-multilinear formula on `S` computes a set-multilinear polynomial on `S`.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], §1, p. 2, define set-multilinear circuits semantically,
  by the polynomials their gates compute, so for them the statement here holds by definition. The
  syntactic predicate `SPFormula.IsSetMultilinear` strengthens that definition; the statement and
  proof here, which connect the two, are original.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.SPFormula

open MvPolynomial

variable {K : Type*} [CommSemiring K] {n d : ℕ}

/-- A formula that is set-multilinear on the set `S` of blocks computes a polynomial that is
set-multilinear on `S` (original). -/
theorem IsSetMultilinear.isSetMultilinear_polynomial {blk : Fin n → Fin d} {F : SPFormula K n}
    {S : Finset (Fin d)} (h : F.IsSetMultilinear blk S) :
    MvPolynomial.IsSetMultilinear blk S F.polynomial := by
  induction h with
  | input i => exact isSetMultilinear_X blk i
  | const a => exact isSetMultilinear_C blk a
  | add c F S _ ih =>
    rw [polynomial_add]
    refine MvPolynomial.IsSetMultilinear.sum _ fun j _ => ?_
    rw [C_mul']
    exact (ih j).smul _
  | mul F T hT _ ih =>
    rw [polynomial_mul]
    exact MvPolynomial.IsSetMultilinear.prod _ (fun _ _ _ _ hij => hT hij) fun j _ => ih j

end Cslib.Circuits.Arithmetic.SPFormula
