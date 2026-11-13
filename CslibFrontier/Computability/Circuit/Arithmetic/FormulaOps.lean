/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.SetMultilinearGadget
public import CslibFrontier.Foundations.Data.MvPolynomial.CoefficientDegree

/-!
# Substitution into arithmetic formulas of unbounded fan-in

Operations on the formulas `Cslib.Circuits.Arithmetic.SPFormula` of sum and product gates of
unbounded fan-in, each with the polynomial it computes, a bound on its product-depth and a bound on
its number of nodes.

`SPFormula.substFormula G F` replaces every input `i` of `F` by the formula `G i`; it computes the
polynomial of `F` with the polynomials of the `G i` substituted for the variables. The
product-depths add, and the number of nodes is at most the product of that of `F` and a common
bound for the `G i`. Two families of formulas of product-depth zero are provided for `G`, so that
substituting them does not increase the product-depth: `SPFormula.constInput`, an input or a
constant for every input, and `SPFormula.affineInput`, the sum gate `a i * x_{ρ i} + b i` for
every input `i`.

`SPFormula.ofSparse p` is the formula of product-depth at most one that writes a polynomial `p`
as the sum of its monomials: a sum gate over the support of `p`, with the coefficients on its
edges, of product gates of inputs, an input being repeated as often as its exponent.

Linear combinations of formulas indexed by a finite set are the sum gates
`Cslib.Circuits.Arithmetic.SPFormula.sumOn`; no separate operation is defined for them.

The total degree of the polynomial of a formula is at most its number of nodes
(`SPFormula.totalDegree_polynomial_le_nodeCount`).

## Main definitions

* `Cslib.Circuits.Arithmetic.SPFormula.substFormula`: substitution of formulas for the inputs.
* `Cslib.Circuits.Arithmetic.SPFormula.constInput`,
  `Cslib.Circuits.Arithmetic.SPFormula.affineInput`: formulas of product-depth zero to
  substitute.
* `Cslib.Circuits.Arithmetic.SPFormula.ofSparse`: the sum of monomials of a polynomial.

## Main results

* `Cslib.Circuits.Arithmetic.SPFormula.polynomial_substFormula`,
  `Cslib.Circuits.Arithmetic.SPFormula.productDepth_substFormula_le`,
  `Cslib.Circuits.Arithmetic.SPFormula.nodeCount_substFormula_le`: substitution.
* `Cslib.Circuits.Arithmetic.SPFormula.polynomial_ofSparse`,
  `Cslib.Circuits.Arithmetic.SPFormula.productDepth_ofSparse_le`,
  `Cslib.Circuits.Arithmetic.SPFormula.nodeCount_ofSparse_le`: the sum of monomials.
* `Cslib.Circuits.Arithmetic.SPFormula.totalDegree_polynomial_le_nodeCount`: the degree is at
  most the size.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth
  algebraic circuits*][LimayeSrinivasanTavenas2021], ECCC TR21-081 Revision 1, §1, p. 1: the
  model. The operations and their explicit bounds are original.
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.SPFormula

open Finset MvPolynomial

variable {K : Type*} {n m : ℕ}

/-! ### Substitution of formulas -/

/-- Substitute the formula `G i` for every input `i` of `F`: the substitution
`Cslib.Circuits.Formula.bind` of formulas. -/
def substFormula (G : Fin n → SPFormula K m) (F : SPFormula K n) : SPFormula K m :=
  F.bind G

/-- **The substituted formula computes the substituted polynomial.** -/
theorem polynomial_substFormula [CommSemiring K] (G : Fin n → SPFormula K m)
    (F : SPFormula K n) :
    (substFormula G F).polynomial = aeval (fun i => (G i).polynomial) F.polynomial := by
  rw [aeval_polynomial, algebraMap_eq, polynomial, substFormula, Formula.eval_bind]
  rfl

/-- Substituting formulas of product-depth at most `B` adds at most `B` to the product-depth. -/
theorem productDepth_substFormula_le {G : Fin n → SPFormula K m} {B : ℕ}
    (hG : ∀ i, (G i).productDepth ≤ B) (F : SPFormula K n) :
    (substFormula G F).productDepth ≤ F.productDepth + B := by
  induction F with
  | input i => simpa [substFormula] using hG i
  | gate op args ih =>
    simp only [productDepth, substFormula, Formula.gate_bind, Formula.depthWith_gate] at ih ⊢
    have h : (univ.sup fun j => ((args j).bind G).depthWith SigmaPiOp.mulCost) ≤
        (univ.sup fun j => (args j).depthWith SigmaPiOp.mulCost) + B :=
      Finset.sup_le fun j _ => (ih j).trans <| Nat.add_le_add_right
        (Finset.le_sup (f := fun j => (args j).depthWith SigmaPiOp.mulCost) (mem_univ j)) B
    exact (Nat.add_le_add_right h _).trans_eq (Nat.add_right_comm _ _ _)

/-- Substituting formulas of at most `S` nodes, with `1 ≤ S`, multiplies the number of nodes by
at most `S`. -/
theorem nodeCount_substFormula_le {G : Fin n → SPFormula K m} {S : ℕ}
    (hG : ∀ i, (G i).nodeCount ≤ S) (hS : 1 ≤ S) (F : SPFormula K n) :
    (substFormula G F).nodeCount ≤ F.nodeCount * S := by
  induction F with
  | input i => simpa [substFormula] using hG i
  | gate op args ih =>
    simp only [substFormula, Formula.gate_bind, Formula.nodeCount_gate] at ih ⊢
    rw [add_mul, sum_mul, one_mul]
    exact Nat.add_le_add (sum_le_sum fun j _ => ih j) hS

/-! ### Formulas of product-depth zero to substitute -/

/-- An input or a constant for every input: the input `j` where `ρ i = .inl j` and the constant
`a` where `ρ i = .inr a`. -/
def constInput (ρ : Fin n → Fin m ⊕ K) (i : Fin n) : SPFormula K m :=
  (ρ i).elim .input const

/-- `constInput ρ i` computes the variable or the constant `ρ i`. -/
@[simp] theorem polynomial_constInput [CommSemiring K] (ρ : Fin n → Fin m ⊕ K) (i : Fin n) :
    (constInput ρ i).polynomial = (ρ i).elim X C := by
  rw [constInput]
  cases ρ i <;> rfl

/-- An input or a constant has product-depth zero. -/
@[simp] theorem productDepth_constInput (ρ : Fin n → Fin m ⊕ K) (i : Fin n) :
    (constInput ρ i).productDepth = 0 := by
  rw [constInput]
  cases ρ i <;> simp

/-- An input or a constant is one node. -/
@[simp] theorem nodeCount_constInput (ρ : Fin n → Fin m ⊕ K) (i : Fin n) :
    (constInput ρ i).nodeCount = 1 := by
  rw [constInput]
  cases ρ i <;> rfl

/-- The affine form `a i * x_{ρ i} + b i` for every input `i`: a sum gate over the input `ρ i`,
with edge constant `a i`, and the constant `1`, with edge constant `b i`. -/
def affineInput [One K] (ρ : Fin n → Fin m) (a b : Fin n → K) (i : Fin n) : SPFormula K m :=
  add ![a i, b i] ![.input (ρ i), const 1]

/-- `affineInput ρ a b i` computes `a i * x_{ρ i} + b i`. -/
@[simp] theorem polynomial_affineInput [CommSemiring K] (ρ : Fin n → Fin m) (a b : Fin n → K)
    (i : Fin n) : (affineInput ρ a b i).polynomial = C (a i) * X (ρ i) + C (b i) := by
  simp [affineInput, Fin.sum_univ_two]

/-- An affine form has product-depth zero. -/
@[simp] theorem productDepth_affineInput [One K] (ρ : Fin n → Fin m) (a b : Fin n → K)
    (i : Fin n) : (affineInput ρ a b i).productDepth = 0 := by
  rw [affineInput, productDepth_add]
  exact Nat.le_zero.1 (Finset.sup_le fun j _ => by fin_cases j <;> simp)

/-- An affine form has three nodes: the sum gate, the input and the constant `1`. -/
@[simp] theorem nodeCount_affineInput [One K] (ρ : Fin n → Fin m) (a b : Fin n → K)
    (i : Fin n) : (affineInput ρ a b i).nodeCount = 3 := by
  simp [affineInput, Fin.sum_univ_two]

/-! ### The sum of monomials -/

section OfSparse

variable [CommSemiring K]

/-- The sum of the monomials of `p`: a sum gate over the support of `p`, with the coefficients of
`p` as edge constants, of product gates of inputs, the input `i` occurring `s i` times in the
product gate of the monomial `s`. -/
noncomputable def ofSparse (p : MvPolynomial (Fin n) K) : SPFormula K n :=
  sumOn p.support (fun s => p.coeff s) fun s =>
    prodOn (s.support.sigma fun i => range (s i)) fun x => .input x.1

/-- **The sum of monomials of `p` computes `p`.** -/
@[simp] theorem polynomial_ofSparse (p : MvPolynomial (Fin n) K) : (ofSparse p).polynomial = p := by
  rw [ofSparse, polynomial_sumOn]
  refine Eq.trans (sum_congr rfl fun s _ => ?_) p.support_sum_monomial_coeff
  rw [polynomial_prodOn, prod_sigma]
  simp only [polynomial_input, prod_const, card_range, prod_X_pow_eq_monomial, C_mul_monomial,
    mul_one]

/-- The sum of monomials has product-depth at most one. -/
theorem productDepth_ofSparse_le (p : MvPolynomial (Fin n) K) : (ofSparse p).productDepth ≤ 1 :=
  productDepth_sumOn_le _ fun _ _ => productDepth_prodOn_le fun _ _ => (productDepth_input _).le

/-- The sum of monomials of `p` has at most `#p.support * (p.totalDegree + 1) + 1` nodes: one
product gate and at most `p.totalDegree` inputs for each monomial, and the sum gate. -/
theorem nodeCount_ofSparse_le (p : MvPolynomial (Fin n) K) :
    (ofSparse p).nodeCount ≤ #p.support * (p.totalDegree + 1) + 1 := by
  rw [ofSparse, nodeCount_sumOn, ← smul_eq_mul, ← sum_const]
  refine Nat.add_le_add_right (sum_le_sum fun s hs => ?_) 1
  rw [nodeCount_prodOn]
  simp only [Formula.nodeCount_input, sum_const, card_sigma, card_range, smul_eq_mul, mul_one]
  exact Nat.add_le_add_right (le_totalDegree hs) 1

end OfSparse

/-! ### Degree and size -/

/-- **The total degree of the polynomial of a formula is at most its number of nodes.** -/
theorem totalDegree_polynomial_le_nodeCount [CommSemiring K] (F : SPFormula K n) :
    F.polynomial.totalDegree ≤ F.nodeCount := by
  induction F with
  | input i => exact (totalDegree_X_le i).trans_eq (Formula.nodeCount_input i).symm
  | gate op args ih =>
    rw [Formula.nodeCount_gate]
    cases op with
    | add k c =>
      refine (congrArg totalDegree (polynomial_add c args)).trans_le ?_
      refine (totalDegree_finsetSum_le fun j _ => ?_).trans (Nat.le_succ _)
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      exact (ih j).trans
        (single_le_sum (f := fun j => (args j).nodeCount) (fun _ _ => Nat.zero_le _) (mem_univ j))
    | mul k =>
      refine (congrArg totalDegree (polynomial_mul args)).trans_le ?_
      exact ((totalDegree_finsetProd _ _).trans (sum_le_sum fun j _ => ih j)).trans
        (Nat.le_succ _)
    | const a => exact (totalDegree_C a).le.trans (Nat.zero_le _)

end Cslib.Circuits.Arithmetic.SPFormula
