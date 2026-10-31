/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Determinant
public import Complexity.Computability.Circuit.SumOfTerms
public import Complexity.Foundations.LinearAlgebra.Matrix.PartialDerivatives
public import Mathlib.Data.Nat.Choose.Central
import Complexity.Computability.Circuit.Simulation

/-!
# Depth-three circuits for the determinant and permanent

A depth-three circuit with product fan-in at most `d` adds products of at most `d` affine forms.
The partial-derivative method of Nisan and Wigderson [NisanWigderson1996] bounds such circuits by
a subadditive measure, the dimension of a span of partial derivatives. Here the measure is the
span of the `k`-th order partial derivatives (`MvPolynomial.partialDerivatives`), as in
[Kayal and Saptharishi, §5.2][KayalSaptharishi2014]. A product of `d` affine forms has measure at
most `choose d k` (`MvPolynomial.rank_partialDerivatives_prod_le`), the order-`k` form of
[Nisan and Wigderson, Lemma 3][NisanWigderson1996]. The generic `n × n` determinant and permanent
have measure at least `choose n k ^ 2`, by the minors argument of
[Kayal and Saptharishi, §5.2][KayalSaptharishi2014]
(`Matrix.choose_sq_le_rank_partialDerivatives_det_mvPolynomialX`). So every such circuit computing
either one has at least `choose n k ^ 2 / choose d k` product gates. For product fan-in at most
`2 * n` on the `2n × 2n` determinant or permanent, the middle split gives more than `4 ^ n / n`
product gates. This covers homogeneous circuits, whose product fan-in is at most the degree
[Nisan and Wigderson, §3][NisanWigderson1996]. Exponential lower bounds for the determinant
against homogeneous depth-three circuits are due to Nisan [Nisan1991NonCommutative], as
[Nisan and Wigderson, §2.2][NisanWigderson1996] record.

A `Term K σ d` is a product of exactly `d` affine forms. For `d > 0` it covers every scalar
multiple of a product of at most `d` affine forms: pad with the constant form `1` and absorb the
scalar into a factor. At `d = 0` its polynomial is the empty product `1`. Circuits add terms
(`Cslib.Circuits.SumOfTerms`): additions and wiring are free and a reused product gate is charged
once, so the cost counts product gates and is at most the size of the circuit. The field is
arbitrary, and the premise is equality of formal polynomials. These are bounds for this restricted
model, not for unrestricted arithmetic circuits.

## Main definitions

* `Cslib.Circuits.DepthThree.Term`: a product of `d` affine forms.

## Main results

* `Cslib.Circuits.DepthThree.rank_partialDerivatives_le_mul_cost`: every output has `k`-th order
  partial-derivative dimension at most `choose d k` times the number of product gates.
* `Cslib.Circuits.DepthThree.choose_sq_le_mul_cost_det`,
  `Cslib.Circuits.DepthThree.choose_sq_le_mul_cost_permanent`: product-gate lower bounds for the
  generic determinant and permanent; `choose_sq_le_mul_cost_detFamily` and
  `choose_sq_le_mul_cost_permFamily` state them for `Cslib.Circuits.Arithmetic.detFamily` and
  `Cslib.Circuits.Arithmetic.permFamily`.
* `Cslib.Circuits.DepthThree.four_pow_lt_mul_cost_det`,
  `Cslib.Circuits.DepthThree.four_pow_lt_mul_cost_permanent`: depth-three circuits with product
  fan-in at most `2 * n`, in particular homogeneous ones, for the `2n × 2n` determinant and
  permanent need more than `4 ^ n / n` product gates.

## References

* [N. Nisan, A. Wigderson, *Lower bounds on arithmetic circuits via partial
  derivatives*][NisanWigderson1996], §2.2, §3 and Lemma 3
* [N. Kayal, R. Saptharishi, *A selection of lower bounds for arithmetic
  circuits*][KayalSaptharishi2014], §5.2
* [N. Nisan, *Lower bounds for non-commutative computation*][Nisan1991NonCommutative]
-/

@[expose] public section

namespace Cslib.Circuits.DepthThree

open MvPolynomial

/-- A product of exactly `d` affine forms in the variables `σ`: one product gate of a
depth-three circuit with product fan-in at most `d`, fewer factors being padded with the constant
form `1`. -/
structure Term (K σ : Type*) (d : ℕ) where
  /-- The coefficient of each variable in each factor. -/
  coefficients : Fin d → σ → K
  /-- The constant term of each factor. -/
  constants : Fin d → K

variable {K σ : Type*} {d : ℕ}

/-- The polynomial represented by a depth-three term. -/
noncomputable def Term.polynomial [CommSemiring K] [Fintype σ] (t : Term K σ d) :
    MvPolynomial σ K :=
  ∏ i, (∑ v, t.coefficients i v • X v + C (t.constants i))

variable [Field K]

/-- Every output of a depth-three circuit with product fan-in at most `d` has `k`-th order
partial-derivative dimension at most `choose d k` times the number of product gates: the order-`k`
form of [Nisan and Wigderson, Lemma 3][NisanWigderson1996]. Additions and wiring are free, and
shared gates are charged once. -/
theorem rank_partialDerivatives_le_mul_cost [Fintype σ] {m : ℕ}
    (c : Circuit (SumOfTerms.signature (Term K σ d)) 0 m) (k : ℕ) (j : Fin m) :
    (partialDerivatives k (c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j)).rank ≤
      (d.choose k * c.program.cost SumOfTerms.termCost : ℕ) := by
  have hcost : c.program.cost (SumOfTerms.dictionaryCost fun _ : Term K σ d => d.choose k) =
      d.choose k * c.program.cost SumOfTerms.termCost := by
    rw [Program.cost_eq_sum, Program.cost_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by cases (c.program.lines i).op <;> simp
  rw [← hcost]
  exact SumOfTerms.rank_trace_le c.program Term.polynomial (partialDerivatives k) _
    (fun t => rank_partialDerivatives_prod_le t.coefficients t.constants k) Fin.elim0
    (fun i => i.elim0) (c.outputs j)

variable {n m : ℕ}

/-- A depth-three circuit with product fan-in at most `d` computing the generic `n × n`
determinant has at least `choose n k ^ 2 / choose d k` product gates, for every `k`. -/
theorem choose_sq_le_mul_cost_det
    (c : Circuit (SumOfTerms.signature (Term K (Fin n × Fin n) d)) 0 m) (k : ℕ) (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      (Matrix.mvPolynomialX (Fin n) (Fin n) K).det) :
    n.choose k ^ 2 ≤ d.choose k * c.program.cost SumOfTerms.termCost := by
  have h := rank_partialDerivatives_le_mul_cost c k j
  rw [hcompute] at h
  exact_mod_cast (Matrix.choose_sq_le_rank_partialDerivatives_det_mvPolynomialX k).trans h

/-- A depth-three circuit with product fan-in at most `d` computing the generic `n × n` permanent
has at least `choose n k ^ 2 / choose d k` product gates, for every `k`. -/
theorem choose_sq_le_mul_cost_permanent
    (c : Circuit (SumOfTerms.signature (Term K (Fin n × Fin n) d)) 0 m) (k : ℕ) (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      (Matrix.mvPolynomialX (Fin n) (Fin n) K).permanent) :
    n.choose k ^ 2 ≤ d.choose k * c.program.cost SumOfTerms.termCost := by
  have h := rank_partialDerivatives_le_mul_cost c k j
  rw [hcompute] at h
  exact_mod_cast (Matrix.choose_sq_le_rank_partialDerivatives_permanent_mvPolynomialX k).trans h

/-- The generic matrix of `Cslib.Circuits.Arithmetic.genericMatrix` renames the variables of
`Matrix.mvPolynomialX` to row-major order. -/
private theorem genericMatrix_eq_map_rename :
    Arithmetic.genericMatrix K n =
      (Matrix.mvPolynomialX (Fin n) (Fin n) K).map (rename finProdFinEquiv) := by
  ext i j
  simp [Arithmetic.genericMatrix]

/-- The bound of `choose_sq_le_mul_cost_det` for the `n`-th member of the determinant family
`Cslib.Circuits.Arithmetic.detFamily`. -/
theorem choose_sq_le_mul_cost_detFamily
    (c : Circuit (SumOfTerms.signature (Term K (Fin (n * n)) d)) 0 m) (k : ℕ) (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      (Arithmetic.detFamily K).poly n) :
    n.choose k ^ 2 ≤ d.choose k * c.program.cost SumOfTerms.termCost := by
  have hpoly : (Arithmetic.detFamily K).poly n =
      rename finProdFinEquiv (Matrix.mvPolynomialX (Fin n) (Fin n) K).det := by
    rw [AlgHom.map_det, AlgHom.mapMatrix_apply, ← genericMatrix_eq_map_rename]
    rfl
  have h := rank_partialDerivatives_le_mul_cost c k j
  rw [hcompute, hpoly] at h
  exact_mod_cast ((Matrix.choose_sq_le_rank_partialDerivatives_det_mvPolynomialX k).trans
    (rank_partialDerivatives_le_rename finProdFinEquiv.injective k _)).trans h

/-- The bound of `choose_sq_le_mul_cost_permanent` for the `n`-th member of the permanent family
`Cslib.Circuits.Arithmetic.permFamily`. -/
theorem choose_sq_le_mul_cost_permFamily
    (c : Circuit (SumOfTerms.signature (Term K (Fin (n * n)) d)) 0 m) (k : ℕ) (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      (Arithmetic.permFamily K).poly n) :
    n.choose k ^ 2 ≤ d.choose k * c.program.cost SumOfTerms.termCost := by
  have hpoly : (Arithmetic.permFamily K).poly n =
      rename finProdFinEquiv (Matrix.mvPolynomialX (Fin n) (Fin n) K).permanent := by
    change (Arithmetic.genericMatrix K n).permanent = _
    simp [genericMatrix_eq_map_rename, Matrix.permanent, map_sum, map_prod]
  have h := rank_partialDerivatives_le_mul_cost c k j
  rw [hcompute, hpoly] at h
  exact_mod_cast ((Matrix.choose_sq_le_rank_partialDerivatives_permanent_mvPolynomialX k).trans
    (rank_partialDerivatives_le_rename finProdFinEquiv.injective k _)).trans h

/-- The middle split of a bound `choose (2n) n ^ 2 ≤ choose (2n) n * s`, with the
central-binomial estimate. -/
private theorem four_pow_lt_mul_of_sq_le {s : ℕ} (hn : 4 ≤ n)
    (h : (2 * n).choose n ^ 2 ≤ (2 * n).choose n * s) : 4 ^ n < n * s := by
  rw [sq] at h
  have hle := Nat.le_of_mul_le_mul_left h (Nat.choose_pos (by omega))
  exact (Nat.four_pow_lt_mul_centralBinom n hn).trans_le
    (Nat.mul_le_mul_left n (Nat.centralBinom_eq_two_mul_choose n ▸ hle))

/-- Depth-three circuits with product fan-in at most `2 * n`, in particular homogeneous ones,
computing the generic `2n × 2n` determinant need more than `4 ^ n / n` product gates. -/
theorem four_pow_lt_mul_cost_det (hn : 4 ≤ n)
    (c : Circuit (SumOfTerms.signature (Term K (Fin (2 * n) × Fin (2 * n)) (2 * n))) 0 m)
    (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      (Matrix.mvPolynomialX (Fin (2 * n)) (Fin (2 * n)) K).det) :
    4 ^ n < n * c.program.cost SumOfTerms.termCost :=
  four_pow_lt_mul_of_sq_le hn (choose_sq_le_mul_cost_det c n j hcompute)

/-- Depth-three circuits with product fan-in at most `2 * n`, in particular homogeneous ones,
computing the generic `2n × 2n` permanent need more than `4 ^ n / n` product gates. -/
theorem four_pow_lt_mul_cost_permanent (hn : 4 ≤ n)
    (c : Circuit (SumOfTerms.signature (Term K (Fin (2 * n) × Fin (2 * n)) (2 * n))) 0 m)
    (j : Fin m)
    (hcompute : c.eval (SumOfTerms.interpretation Term.polynomial) Fin.elim0 j =
      (Matrix.mvPolynomialX (Fin (2 * n)) (Fin (2 * n)) K).permanent) :
    4 ^ n < n * c.program.cost SumOfTerms.termCost :=
  four_pow_lt_mul_of_sq_le hn (choose_sq_le_mul_cost_permanent c n j hcompute)

end Cslib.Circuits.DepthThree
