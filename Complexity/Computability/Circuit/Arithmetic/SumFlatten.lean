/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.SigmaPi
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Flattening the sums of an unbounded fan-in formula

A formula of unbounded fan-in may nest sum gates arbitrarily deep, so its size is not bounded by
its product-depth and the fan-in of its gates. Merging consecutive sum gates repairs this
(original): every maximal block of sum gates of `F` computes a linear combination, with
coefficients the products of the edge constants along the paths, of the non-sum formulas below it
(`SPFormula.linComb F`, a finitely supported function from formulas to coefficients). Equal
formulas merge into one term. `SPFormula.flatten F` is one sum gate over that combination, in
which every product gate has its arguments flattened in turn.

`flatten F` computes the polynomial of `F` (`SPFormula.polynomial_flatten`), its product-depth is
at most that of `F` (`SPFormula.productDepth_flatten_le`), and its size is bounded by the number of
distinct subformulas of `F`: if `F` lies in a set `S` of formulas closed under taking arguments,
with `#S ≤ B` and every product gate in `S` of fan-in at most `B`, then `flatten F` has at most
`(B + 1) ^ (2 * F.productDepth + 1)` nodes (`SPFormula.nodeCount_flatten_le`). Along a path of
`flatten F` the sum and product gates alternate, a sum gate has at most `#S` arguments, one for
each distinct non-sum subformula, and a product gate at most `B`.

This is the step, left implicit in the proof of [LimayeSrinivasanTavenas2021, Lemma 15, §5, p. 12]
("by expanding it, we can transform it to a set-multilinear formula of size at most `s ^ (2Δ)`"),
that turns a circuit of product-depth `Δ` into a formula of polynomial size; the circuits are
unfolded in `Complexity.Computability.Circuit.Arithmetic.SPCircuit`.

## Main definitions

* `Cslib.Circuits.Arithmetic.SPFormula.ofFinsupp`: the sum gate over a finitely supported linear
  combination of formulas.
* `Cslib.Circuits.Arithmetic.SPFormula.linComb`: the linear combination of non-sum formulas that a
  formula computes, with flattened arguments.
* `Cslib.Circuits.Arithmetic.SPFormula.flatten`: the flattened formula.

## Main results

* `Cslib.Circuits.Arithmetic.SPFormula.polynomial_flatten`: the flattened formula computes the
  same polynomial.
* `Cslib.Circuits.Arithmetic.SPFormula.productDepth_flatten_le`: it is no deeper in products.
* `Cslib.Circuits.Arithmetic.SPFormula.nodeCount_flatten_le` (original): its size is at most
  `(B + 1) ^ (2 * F.productDepth + 1)`.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], ECCC TR21-081 revision 1, proof of Lemma 15 (§5,
  p. 12)
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.SPFormula

open MvPolynomial

variable {K : Type*} {n : ℕ}

section Semiring

variable [Semiring K]

/-- The sum gate over the finitely supported linear combination `f` of formulas: each formula `H`
of the support is an argument, with edge constant `f H`. -/
noncomputable def ofFinsupp (f : SPFormula K n →₀ K) : SPFormula K n :=
  add (fun j => f (f.support.equivFin.symm j)) fun j => f.support.equivFin.symm j

/-- The linear combination of non-sum formulas computed by a formula: an input or a constant is
itself, a sum gate is the combination of those of its arguments with its edge constants, and a
product gate is itself with flattened arguments. -/
noncomputable def linComb : SPFormula K n → (SPFormula K n →₀ K)
  | .input i => Finsupp.single (.input i) 1
  | .gate (.add _ c) args => ∑ j, c j • linComb (args j)
  | .gate (.mul _) args => Finsupp.single (mul fun j => ofFinsupp (linComb (args j))) 1
  | .gate (.const a) _ => Finsupp.single (const a) 1

/-- **The flattened formula**: one sum gate over the linear combination of non-sum formulas that
`F` computes, the arguments of every product gate flattened in turn. -/
noncomputable def flatten (F : SPFormula K n) : SPFormula K n :=
  ofFinsupp (linComb F)

/-- An input is a combination of itself. -/
@[simp] theorem linComb_input (i : Fin n) :
    linComb (.input i : SPFormula K n) = Finsupp.single (.input i) 1 :=
  rfl

/-- A sum gate is the combination of its arguments with its edge constants. -/
@[simp] theorem linComb_add {m : ℕ} (c : Fin m → K) (F : Fin m → SPFormula K n) :
    linComb (add c F) = ∑ j, c j • linComb (F j) :=
  rfl

/-- A product gate is a combination of itself, with flattened arguments. -/
@[simp] theorem linComb_mul {m : ℕ} (F : Fin m → SPFormula K n) :
    linComb (mul F) = Finsupp.single (mul fun j => flatten (F j)) 1 :=
  rfl

/-- A constant is a combination of itself. -/
@[simp] theorem linComb_const (a : K) :
    linComb (const a : SPFormula K n) = Finsupp.single (const a) 1 :=
  rfl

/-- The sum gate over a combination has one more node than the formulas of its support. -/
theorem nodeCount_ofFinsupp (f : SPFormula K n →₀ K) :
    (ofFinsupp f).nodeCount = (∑ H ∈ f.support, H.nodeCount) + 1 := by
  rw [ofFinsupp, add, Formula.nodeCount_gate]
  congr 1
  exact (f.support.equivFin.symm.sum_comp fun H : f.support => (H : SPFormula K n).nodeCount).trans
    (Finset.sum_coe_sort _ _)

/-- The sum gate over a combination is no deeper in products than the formulas of its support. -/
theorem productDepth_ofFinsupp_le {f : SPFormula K n →₀ K} {t : ℕ}
    (h : ∀ H ∈ f.support, H.productDepth ≤ t) : (ofFinsupp f).productDepth ≤ t := by
  rw [ofFinsupp, productDepth_add]
  exact Finset.sup_le fun j _ => h _ (f.support.equivFin.symm j).2

/-- The formulas of the combination of `F` are no deeper in products than `F`. -/
theorem productDepth_le_of_mem_support_linComb (F : SPFormula K n) :
    ∀ H ∈ (linComb F).support, H.productDepth ≤ F.productDepth := by
  classical
  induction F with
  | input i =>
    intro H hH
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hH)]
  | gate op args ih =>
    intro H hH
    cases op with
    | add m c =>
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hH)
      refine (ih j H (Finsupp.support_smul hj)).trans ?_
      rw [productDepth_add]
      exact Finset.le_sup (f := fun j => productDepth (args j)) (Finset.mem_univ j)
    | mul m =>
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hH), productDepth_mul,
        productDepth_mul]
      refine Nat.add_le_add_right (Finset.sup_mono_fun fun j _ => ?_) 1
      exact productDepth_ofFinsupp_le (ih j)
    | const a =>
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hH), productDepth_const]
      exact Nat.zero_le _

/-- **Flattening does not increase the product-depth.** -/
theorem productDepth_flatten_le (F : SPFormula K n) : (flatten F).productDepth ≤ F.productDepth :=
  productDepth_ofFinsupp_le (productDepth_le_of_mem_support_linComb F)

/-! ### Size -/

/-- The non-sum formula standing for `F` in a combination: an input or a constant is itself, a
product gate is itself with flattened arguments. Sum gates are never used. -/
private noncomputable def key : SPFormula K n → SPFormula K n
  | .input i => .input i
  -- A placeholder: sum gates of `S` are never in a combination, and `S.image key` still has at
  -- most `#S` elements, so the bound of `card_support_linComb_le` is unaffected.
  | .gate (.add _ _) _ => zero
  | .gate (.mul _) args => mul fun j => flatten (args j)
  | .gate (.const a) _ => const a

variable {S : Finset (SPFormula K n)}

/-- If `F` lies in a set `S` of formulas closed under taking arguments, every formula of its
combination stands for a formula of `S`. -/
private theorem support_linComb_subset [DecidableEq (SPFormula K n)]
    (hS : ∀ op args, Formula.gate op args ∈ S → ∀ j, args j ∈ S) {F : SPFormula K n}
    (hF : F ∈ S) : (linComb F).support ⊆ S.image key := by
  induction F with
  | input i =>
    refine (Finsupp.support_single_subset).trans ?_
    rw [Finset.singleton_subset_iff]
    exact Finset.mem_image_of_mem key hF
  | gate op args ih =>
    cases op with
    | add m c =>
      refine (Finsupp.support_finsetSum).trans (Finset.biUnion_subset.mpr fun j _ => ?_)
      exact (Finsupp.support_smul).trans (ih j (hS _ _ hF j))
    | mul m =>
      refine (Finsupp.support_single_subset).trans ?_
      rw [Finset.singleton_subset_iff]
      exact Finset.mem_image_of_mem key hF
    | const a =>
      refine (Finsupp.support_single_subset).trans ?_
      rw [Finset.singleton_subset_iff]
      exact Finset.mem_image_of_mem key hF

/-- If `F` lies in a set `S` of formulas closed under taking arguments, its combination has at
most `#S` formulas. -/
theorem card_support_linComb_le (hS : ∀ op args, Formula.gate op args ∈ S → ∀ j, args j ∈ S)
    {F : SPFormula K n} (hF : F ∈ S) : (linComb F).support.card ≤ S.card := by
  classical
  exact (Finset.card_le_card (support_linComb_subset hS hF)).trans Finset.card_image_le

/-- A sum gate over at most `B` formulas of at most `(B + 1) ^ e` nodes each has at most
`(B + 1) ^ (e + 1)` nodes. -/
theorem nodeCount_ofFinsupp_le {f : SPFormula K n →₀ K} {B e : ℕ} (hf : f.support.card ≤ B)
    (h : ∀ H ∈ f.support, H.nodeCount ≤ (B + 1) ^ e) :
    (ofFinsupp f).nodeCount ≤ (B + 1) ^ (e + 1) := by
  rw [nodeCount_ofFinsupp]
  have hsum : ∑ H ∈ f.support, H.nodeCount ≤ B * (B + 1) ^ e :=
    (Finset.sum_le_card_nsmul _ _ _ h).trans (by rw [smul_eq_mul]; gcongr)
  have hpos : 1 ≤ (B + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos B)
  rw [pow_succ]
  nlinarith

variable {B : ℕ}

/-- **Size of the terms of a combination** (original): let `F` lie in a set `S` of formulas closed
under taking arguments, with `#S ≤ B` and every product gate of `S` of fan-in at most `B`. Every
formula of the combination of `F` has at most `(B + 1) ^ (2 * F.productDepth)` nodes. -/
theorem nodeCount_le_of_mem_support_linComb
    (hS : ∀ op args, Formula.gate op args ∈ S → ∀ j, args j ∈ S) (hB : S.card ≤ B)
    (hmul : ∀ m args, Formula.gate (SigmaPiOp.mul m) args ∈ S → m ≤ B) {F : SPFormula K n}
    (hF : F ∈ S) : ∀ H ∈ (linComb F).support, H.nodeCount ≤ (B + 1) ^ (2 * F.productDepth) := by
  classical
  have hone (e : ℕ) : 1 ≤ (B + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos B)
  induction F with
  | input i =>
    intro H hH
    rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hH), Formula.nodeCount_input]
    exact hone _
  | gate op args ih =>
    intro H hH
    cases op with
    | add m c =>
      obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hH)
      refine (ih j (hS _ _ hF j) H (Finsupp.support_smul hj)).trans
        (Nat.pow_le_pow_right (Nat.succ_pos B) (Nat.mul_le_mul_left 2 ?_))
      rw [productDepth_add]
      exact Finset.le_sup (f := fun j => productDepth (args j)) (Finset.mem_univ j)
    | mul m =>
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hH), productDepth_mul]
      set s := Finset.univ.sup fun j => productDepth (args j)
      have hj (j : Fin m) : (flatten (args j)).nodeCount ≤ (B + 1) ^ (2 * s + 1) := by
        have hargs := hS _ _ hF j
        refine (nodeCount_ofFinsupp_le (card_support_linComb_le hS hargs |>.trans hB)
          (ih j hargs)).trans (Nat.pow_le_pow_right (Nat.succ_pos B) ?_)
        have : productDepth (args j) ≤ s :=
          Finset.le_sup (f := fun j => productDepth (args j)) (Finset.mem_univ j)
        omega
      rw [mul, Formula.nodeCount_gate]
      have hsum : ∑ j, (flatten (args j)).nodeCount ≤ B * (B + 1) ^ (2 * s + 1) :=
        (Finset.sum_le_card_nsmul _ _ _ fun j _ => hj j).trans (by
          rw [Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          exact Nat.mul_le_mul_right _ (hmul m args hF))
      have h1 := hone (2 * s + 1)
      refine (Nat.add_le_add_right hsum 1).trans ?_
      rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring, pow_succ (B + 1) (2 * s + 1)]
      nlinarith
    | const a =>
      rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hH), nodeCount_const]
      exact hone _

/-- **Size of the flattened formula** (original): if `F` lies in a set `S` of formulas closed
under taking arguments, with `#S ≤ B` and every product gate of `S` of fan-in at most `B`, then
`flatten F` has at most `(B + 1) ^ (2 * F.productDepth + 1)` nodes. -/
theorem nodeCount_flatten_le (hS : ∀ op args, Formula.gate op args ∈ S → ∀ j, args j ∈ S)
    (hB : S.card ≤ B) (hmul : ∀ m args, Formula.gate (SigmaPiOp.mul m) args ∈ S → m ≤ B)
    {F : SPFormula K n} (hF : F ∈ S) :
    (flatten F).nodeCount ≤ (B + 1) ^ (2 * F.productDepth + 1) :=
  nodeCount_ofFinsupp_le ((card_support_linComb_le hS hF).trans hB)
    (nodeCount_le_of_mem_support_linComb hS hB hmul hF)

end Semiring

/-! ### The computed polynomial -/

section CommSemiring

variable [CommSemiring K]

/-- The sum gate over a combination computes the combination of the polynomials of its support. -/
theorem polynomial_ofFinsupp (f : SPFormula K n →₀ K) :
    (ofFinsupp f).polynomial = Finsupp.linearCombination K polynomial f := by
  rw [ofFinsupp, polynomial_add, Finsupp.linearCombination_apply, Finsupp.sum]
  refine (f.support.equivFin.symm.sum_comp
    fun H : f.support => C (f H) * (H : SPFormula K n).polynomial).trans
    ((Finset.sum_coe_sort f.support fun H => C (f H) * H.polynomial).trans ?_)
  exact Finset.sum_congr rfl fun H _ => (smul_eq_C_mul _ _).symm

/-- The combination of the polynomials of the combination of `F` is the polynomial of `F`. -/
theorem linearCombination_linComb (F : SPFormula K n) :
    Finsupp.linearCombination K polynomial (linComb F) = F.polynomial := by
  induction F with
  | input i => rw [linComb_input, Finsupp.linearCombination_single, one_smul]
  | gate op args ih =>
    cases op with
    | add m c =>
      rw [linComb_add, map_sum, polynomial_add]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, ih j, smul_eq_C_mul]
    | mul m =>
      rw [linComb_mul, Finsupp.linearCombination_single, one_smul, polynomial_mul,
        polynomial_mul]
      exact Finset.prod_congr rfl fun j _ => by rw [flatten, polynomial_ofFinsupp, ih j]
    | const a =>
      obtain rfl : args = Fin.elim0 := Subsingleton.elim (α := Fin 0 → SPFormula K n) _ _
      rw [linComb_const, Finsupp.linearCombination_single, one_smul, polynomial_const]

/-- **The flattened formula computes the same polynomial.** -/
@[simp] theorem polynomial_flatten (F : SPFormula K n) : (flatten F).polynomial = F.polynomial :=
  (polynomial_ofFinsupp _).trans (linearCombination_linComb F)

end CommSemiring

end Cslib.Circuits.Arithmetic.SPFormula
