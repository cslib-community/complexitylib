/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.SetMultilinearGadget

/-!
# Set-multilinearization of formulas over any field

Let the variables of a formula `F` over a field be split into `d` blocks by `blk`. For a set `S`
of blocks, the formula `SPFormula.smPart blk S F` computes the set-multilinear part on `S` of the
polynomial computed by `F` (`SPFormula.polynomial_smPart`), and is syntactically set-multilinear
on `S` (`SPFormula.isSetMultilinear_smPart`). It is built by gate simulation
[Forbes2024, Cor. 27], one node of `F` and one set of blocks at a time:

* an input is kept on its own block and replaced by `0` on the others;
* a constant is kept on no block and replaced by `0` on the others;
* a sum gate is simulated by the same sum gate over the parts of its children on `S`
  ([Forbes2024, Lemma 25]);
* a product gate is simulated by the product gadget `SPFormula.mulGadget` over the parts of its
  children on all sets of blocks ([Forbes2024, Lemma 26]).

Sum gates keep the product-depth and the product gadget adds two, so `smPart` at most doubles the
product-depth (`SPFormula.productDepth_smPart_le`). The size of the product gadget is linear in the
sizes of its inputs with a factor depending only on `d`; since a formula is a tree, the inputs are
copied, and the size grows by at most the factor `smCost d` per level of product gates
(`SPFormula.nodeCount_smPart_le`):

`nodeCount (smPart blk S F) ≤ smCost d ^ productDepth F * nodeCount F`, with
`smCost d = 4 * (2 * (d + 1) ^ 2) ^ (d + 1)`.

There is no assumption on the characteristic of the field, on homogeneity or on the formula.

## Main definitions

* `Cslib.Circuits.Arithmetic.SPFormula.smPart`: the set-multilinear part of a formula on a set of
  blocks.
* `Cslib.Circuits.Arithmetic.SPFormula.smCost`: the size factor per level of product gates.

## Main results

* `Cslib.Circuits.Arithmetic.SPFormula.polynomial_smPart`: it computes the set-multilinear part.
* `Cslib.Circuits.Arithmetic.SPFormula.isSetMultilinear_smPart`: it is set-multilinear.
* `Cslib.Circuits.Arithmetic.SPFormula.productDepth_smPart_le`: product-depth at most doubles.
* `Cslib.Circuits.Arithmetic.SPFormula.nodeCount_smPart_le`: the size bound.

## References

* [M. A. Forbes, *Low-depth algebraic circuit lower bounds over any field*][Forbes2024],
  Lemmas 24–26 and Corollary 27, pp. 31:13–31:14. Forbes simulates the gates of a circuit and
  bounds the size by `poly(s, Θ(d / ln d) ^ d)`; the simulation here is done on formulas, with the
  product gadget `SPFormula.mulGadget`, the explicit factor `smCost d` and the bound linear in
  the size, and is original in this form.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.SPFormula

open MvPolynomial

variable {K : Type*} [Field K] [DecidableEq K] {n d : ℕ}

/-- **The set-multilinear part of a formula** on the set `S` of blocks, by gate simulation
([Forbes2024, Cor. 27], original on formulas): inputs and constants are kept on their own sets of
blocks and replaced by `0` on the others, a sum gate is simulated by the same sum gate over the
parts on `S` of its children, and a product gate by the product gadget over the parts of its
children on all sets of blocks. -/
noncomputable def smPart (blk : Fin n → Fin d) : Finset (Fin d) → SPFormula K n → SPFormula K n
  | S, .input i => if S = {blk i} then .input i else zero
  | S, .gate (.add _ c) args => add c fun j => smPart blk S (args j)
  | S, .gate (.mul _) args =>
    mulGadget S (fun j => constantCoeff (polynomial (args j))) fun j T => smPart blk T (args j)
  | S, .gate (.const a) _ => if S = ∅ then const a else zero

/-- The size factor of `smPart` per level of product gates: `4 * (2 * (d + 1) ^ 2) ^ (d + 1)`,
twice the size factor of the product gadget. -/
def smCost (d : ℕ) : ℕ :=
  2 * gadgetCost d

/-- The size factor is positive. -/
theorem one_le_smCost (d : ℕ) : 1 ≤ smCost d := by
  unfold smCost gadgetCost
  have : 0 < (2 * (d + 1) ^ 2) ^ (d + 1) := by positivity
  omega

variable {blk : Fin n → Fin d}

/-- **`smPart` computes the set-multilinear part** (original on formulas; [Forbes2024, Cor. 27]):
`smPart blk S F` computes the part on `S` of the polynomial computed by `F`. -/
theorem polynomial_smPart (S : Finset (Fin d)) (F : SPFormula K n) :
    (smPart blk S F).polynomial = smProj blk S F.polynomial := by
  induction F generalizing S with
  | input i =>
    rw [smPart, polynomial_input, smProj_X]
    split_ifs
    · rfl
    · exact polynomial_zero
  | gate op args ih =>
    cases op with
    | add m c =>
      rw [smPart, polynomial_add, polynomial_add, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [ih, smProj_C_mul]
    | mul m =>
      rw [smPart, polynomial_mul]
      exact polynomial_mulGadget (fun j => rfl) fun j T => ih j T
    | const a =>
      have h : polynomial (Formula.gate (SigmaPiOp.const a) args : SPFormula K n) = C a := rfl
      rw [smPart, h, smProj_C]
      split_ifs
      · rfl
      · exact polynomial_zero

/-- **`smPart` is set-multilinear** (original on formulas): `smPart blk S F` is syntactically
set-multilinear on `S`. -/
theorem isSetMultilinear_smPart (S : Finset (Fin d)) (F : SPFormula K n) :
    (smPart blk S F).IsSetMultilinear blk S := by
  induction F generalizing S with
  | input i =>
    rw [smPart]
    split_ifs with h
    · rw [h]
      exact .input i
    · exact isSetMultilinear_zero S
  | gate op args ih =>
    cases op with
    | add m c =>
      rw [smPart]
      exact .add c _ S fun j => ih j S
    | mul m =>
      rw [smPart]
      exact isSetMultilinear_mulGadget fun j T => ih j T
    | const a =>
      rw [smPart]
      split_ifs with h
      · rw [h]
        exact .const a
      · exact isSetMultilinear_zero S

/-- **`smPart` at most doubles the product-depth** (original on formulas; [Forbes2024, Cor. 27]):
sum gates keep it and the product gadget adds two. -/
theorem productDepth_smPart_le (S : Finset (Fin d)) (F : SPFormula K n) :
    (smPart blk S F).productDepth ≤ 2 * F.productDepth := by
  induction F generalizing S with
  | input i =>
    rw [smPart]
    split_ifs
    · exact Nat.zero_le _
    · rw [productDepth_zero]
      exact Nat.zero_le _
  | gate op args ih =>
    have hle (j : Fin _) (T : Finset (Fin d)) : (smPart blk T (args j)).productDepth ≤
        2 * Finset.univ.sup fun j => productDepth (args j) :=
      (ih j T).trans (Nat.mul_le_mul_left 2
        (Finset.le_sup (f := fun j => productDepth (args j)) (Finset.mem_univ j)))
    cases op with
    | add m c =>
      rw [smPart, productDepth_add, productDepth_add]
      exact Finset.sup_le fun j _ => hle j S
    | mul m =>
      rw [smPart, productDepth_mul]
      exact (productDepth_mulGadget_le fun j T => hle j T).trans_eq
        (by rw [Nat.mul_add, Nat.mul_one])
    | const a =>
      rw [smPart]
      split_ifs
      · rw [productDepth_const]
        exact Nat.zero_le _
      · rw [productDepth_zero]
        exact Nat.zero_le _

/-- **The size of `smPart`** (original; [Forbes2024, Cor. 27] bounds the size of the simulating
circuit by `poly(s, Θ(d / ln d) ^ d)`): `smPart blk S F` has at most
`smCost d ^ productDepth F * nodeCount F` nodes. -/
theorem nodeCount_smPart_le (S : Finset (Fin d)) (F : SPFormula K n) :
    (smPart blk S F).nodeCount ≤ smCost d ^ F.productDepth * F.nodeCount := by
  have hc := one_le_smCost d
  have hpos (G : SPFormula K n) : 1 ≤ smCost d ^ G.productDepth * G.nodeCount :=
    Nat.mul_pos (Nat.one_le_pow _ _ hc) (Formula.nodeCount_pos G)
  induction F generalizing S with
  | input i =>
    rw [smPart, productDepth_input, pow_zero, one_mul, Formula.nodeCount_input]
    split_ifs
    · exact le_rfl
    · exact le_of_eq nodeCount_zero
  | gate op args ih =>
    set p := Finset.univ.sup fun j => productDepth (args j)
    have hle (j : Fin _) (T : Finset (Fin d)) :
        (smPart blk T (args j)).nodeCount ≤ smCost d ^ p * (args j).nodeCount :=
      (ih j T).trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hc
        (Finset.le_sup (f := fun j => productDepth (args j)) (Finset.mem_univ j))))
    have hcp : 1 ≤ smCost d ^ p := Nat.one_le_pow _ _ hc
    cases op with
    | add m c =>
      rw [smPart, productDepth_add, Formula.nodeCount_gate, Formula.nodeCount_gate]
      calc ∑ j, (smPart blk S (args j)).nodeCount + 1
          ≤ ∑ j, smCost d ^ p * (args j).nodeCount + smCost d ^ p :=
            Nat.add_le_add (Finset.sum_le_sum fun j _ => hle j S) hcp
        _ = smCost d ^ p * (∑ j, (args j).nodeCount + 1) := by
            rw [← Finset.mul_sum]
            ring
    | mul m =>
      rw [smPart, productDepth_mul, Formula.nodeCount_gate]
      set s := ∑ j, (args j).nodeCount
      have hm : m ≤ s := by
        calc m = ∑ _j : Fin m, 1 := by simp
          _ ≤ s := Finset.sum_le_sum fun j _ => Formula.nodeCount_pos (args j)
      refine (nodeCount_mulGadget_le (w := fun j => smCost d ^ p * (args j).nodeCount)
        fun j T _ => hle j T).trans ?_
      rw [← Finset.mul_sum, Fintype.card_fin, pow_succ]
      have h1 : 1 + m + smCost d ^ p * s ≤ 2 * (smCost d ^ p * (s + 1)) := by nlinarith
      calc gadgetCost d * (1 + m + smCost d ^ p * s)
          ≤ gadgetCost d * (2 * (smCost d ^ p * (s + 1))) := Nat.mul_le_mul_left _ h1
        _ = smCost d ^ p * smCost d * (s + 1) := by
            unfold smCost
            ring
    | const a =>
      rw [smPart]
      split_ifs
      · exact hpos _
      · exact nodeCount_zero.trans_le (hpos _)

end Cslib.Circuits.Arithmetic.SPFormula
