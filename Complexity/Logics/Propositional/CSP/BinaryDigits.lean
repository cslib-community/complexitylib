/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.PartitionFunction
public import Complexity.Foundations.Data.Polynomial.BinaryDigits
public import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Fintype.BigOperators

/-!
# Exact weighted counting through binary-digit polynomials

Replace each natural local weight by its binary-digit polynomial and take the same partition
function over `ℕ[X]`. Evaluation at `2` gives the original weighted count. If the weights of
relation `r` have at most `b r` bits, the polynomial has degree at most
`∑ (r, _) ∈ F, (b r - 1)` and coefficient sum at most `2 ^ F.numVars * ∏ (r, _) ∈ F, b r`.

The coefficient precision is therefore logarithmic in each bit-length bound, even when the
weights themselves are large. The explicit choice
`F.numVars + ∑ (r, _) ∈ F, (b r).size + 1` suffices for exact natural coefficient recovery.
This is an algebraic reduction; the tensor-contraction runtime is a separate theorem.

## Main definitions

* `Cslib.Logic.PL.CSP.binaryPartitionPolynomial`: the partition function of binary-digit weights.
* `Cslib.Logic.PL.CSP.binaryDegreeBound`: the sum of the local degree bounds.
* `Cslib.Logic.PL.CSP.binaryPrecision`: precision sufficient for exact coefficient recovery.

## Main results

* `Cslib.Logic.PL.CSP.eval_two_binaryPartitionPolynomial`: evaluation at `2` is the weighted count.
* `Cslib.Logic.PL.CSP.natDegree_binaryPartitionPolynomial_le`: the degree bound.
* `Cslib.Logic.PL.CSP.eval_one_binaryPartitionPolynomial_le`: the coefficient-sum bound.
* `Cslib.Logic.PL.CSP.eval_one_binaryPartitionPolynomial_lt_two_pow`: the precision suffices.
* `Cslib.Logic.PL.CSP.recover_binaryPartitionPolynomial`: exact recovery from coefficient residues.
* `Cslib.Logic.PL.CSP.evalCoeffList_binaryPartitionPolynomial_residues`: the decoded residues
  evaluate to the original partition function.
-/

public section

namespace Cslib.Logic.PL.CSP

open Polynomial

variable {Rel V D : Type*} [DecidableEq V] [Fintype D] [Inhabited D]

/-- Evaluating polynomial weights commutes with the partition function. -/
theorem eval_partitionFunction {R : Type*} [CommSemiring R]
    (wt : Rel → List D → R[X]) (F : CSP Rel V) (z : R) :
    (F.partitionFunction wt).eval z = F.partitionFunction (fun r w => (wt r w).eval z) :=
  map_partitionFunction (evalRingHom z) wt F

/-- The degree of a polynomial partition function is at most the sum of the local degree
bounds. -/
theorem natDegree_partitionFunction_le {R : Type*} [Semiring R]
    {wt : Rel → List D → R[X]} {F : CSP Rel V} {d : Rel → ℕ}
    (hd : ∀ c ∈ F, ∀ w : List D, w.length = c.2.length → (wt c.1 w).natDegree ≤ d c.1) :
    (F.partitionFunction wt).natDegree ≤ (F.map fun c => d c.1).sum := by
  rw [partitionFunction]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  rw [weight]
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_map]
  exact List.sum_le_sum fun c hc => hd c hc _ (List.length_map _)

/-- The partition function with each local natural weight replaced by its binary-digit
polynomial. -/
@[expose] noncomputable def binaryPartitionPolynomial (wt : Rel → List Bool → ℕ)
    (F : CSP Rel V) : ℕ[X] :=
  F.partitionFunction fun r w => binaryDigits (wt r w)

/-- The degree bound from a bit-length bound for each relation. -/
@[expose] def binaryDegreeBound (b : Rel → ℕ) (F : CSP Rel V) : ℕ :=
  (F.map fun c => b c.1 - 1).sum

/-- The precision for recovering the natural coefficients: the number of variables, plus the
sum of the binary lengths of the local bit-length bounds, plus one. -/
@[expose] def binaryPrecision (b : Rel → ℕ) (F : CSP Rel V) : ℕ :=
  F.numVars + (F.map fun c => (b c.1).size).sum + 1

/-- Evaluating the binary-digit partition polynomial at `2` gives the original weighted
partition function. -/
@[simp] theorem eval_two_binaryPartitionPolynomial (wt : Rel → List Bool → ℕ)
    (F : CSP Rel V) : (F.binaryPartitionPolynomial wt).eval 2 = F.partitionFunction wt := by
  simp only [binaryPartitionPolynomial, eval_partitionFunction, eval_two_binaryDigits]

variable {wt : Rel → List Bool → ℕ} {F : CSP Rel V} {b : Rel → ℕ}

/-- The polynomial's degree is at most the sum of the local bit-length bounds less one. -/
theorem natDegree_binaryPartitionPolynomial_le
    (hb : ∀ c ∈ F, ∀ w : List Bool, w.length = c.2.length → (wt c.1 w).size ≤ b c.1) :
    (F.binaryPartitionPolynomial wt).natDegree ≤ F.binaryDegreeBound b := by
  exact natDegree_partitionFunction_le
    (wt := fun r w => binaryDigits (wt r w)) (d := fun r => b r - 1) fun c hc w hw =>
    (natDegree_binaryDigits_le _).trans (Nat.sub_le_sub_right (hb c hc w hw) 1)

/-- The coefficient sum is at most the number of assignments times the product of the local
bit-length bounds. -/
theorem eval_one_binaryPartitionPolynomial_le
    (hb : ∀ c ∈ F, ∀ w : List Bool, w.length = c.2.length → (wt c.1 w).size ≤ b c.1) :
    (F.binaryPartitionPolynomial wt).eval 1 ≤
      2 ^ F.numVars * (F.map fun c => b c.1).prod := by
  rw [binaryPartitionPolynomial, eval_partitionFunction]
  simpa only [Fintype.card_bool] using partitionFunction_le_prod
    (wt := fun r w => (binaryDigits (wt r w)).eval 1)
    (fun c hc w hw => (eval_one_binaryDigits_le _).trans (hb c hc w hw))

/-- The explicit precision strictly exceeds the coefficient sum. -/
theorem eval_one_binaryPartitionPolynomial_lt_two_pow
    (hb : ∀ c ∈ F, ∀ w : List Bool, w.length = c.2.length → (wt c.1 w).size ≤ b c.1) :
    (F.binaryPartitionPolynomial wt).eval 1 < 2 ^ F.binaryPrecision b := by
  have hprod : (F.map fun c => b c.1).prod ≤ 2 ^ (F.map fun c => (b c.1).size).sum := by
    clear hb
    induction F with
    | nil => simp
    | cons c F ih =>
      simpa only [List.map_cons, List.prod_cons, List.sum_cons, pow_add] using
        Nat.mul_le_mul (Nat.lt_size_self (b c.1)).le ih
  calc (F.binaryPartitionPolynomial wt).eval 1
      ≤ 2 ^ F.numVars * (F.map fun c => b c.1).prod :=
        eval_one_binaryPartitionPolynomial_le hb
    _ ≤ 2 ^ F.numVars * 2 ^ (F.map fun c => (b c.1).size).sum :=
        Nat.mul_le_mul_left _ hprod
    _ = 2 ^ (F.numVars + (F.map fun c => (b c.1).size).sum) := (pow_add _ _ _).symm
    _ < 2 ^ F.binaryPrecision b := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)

/-- Recovering enough coefficients modulo the explicit power of two gives the entire
binary-digit partition polynomial. -/
theorem recover_binaryPartitionPolynomial
    (hb : ∀ c ∈ F, ∀ w : List Bool, w.length = c.2.length → (wt c.1 w).size ≤ b c.1) :
    ofCoeffList ((List.range (F.binaryDegreeBound b + 1)).map fun i =>
      (F.binaryPartitionPolynomial wt).coeff i % 2 ^ F.binaryPrecision b) =
        F.binaryPartitionPolynomial wt :=
  ofCoeffList_coeffsBelow_mod (Nat.lt_succ_of_le (natDegree_binaryPartitionPolynomial_le hb))
    (eval_one_binaryPartitionPolynomial_lt_two_pow hb)

/-- Evaluating the decoded coefficient residues at `2` recovers the weighted count. -/
theorem evalCoeffList_binaryPartitionPolynomial_residues
    (hb : ∀ c ∈ F, ∀ w : List Bool, w.length = c.2.length → (wt c.1 w).size ≤ b c.1) :
    evalCoeffList 2 ((List.range (F.binaryDegreeBound b + 1)).map fun i =>
      (F.binaryPartitionPolynomial wt).coeff i % 2 ^ F.binaryPrecision b) =
        F.partitionFunction wt := by
  rw [← eval_ofCoeffList, recover_binaryPartitionPolynomial hb, eval_two_binaryPartitionPolynomial]

end Cslib.Logic.PL.CSP
