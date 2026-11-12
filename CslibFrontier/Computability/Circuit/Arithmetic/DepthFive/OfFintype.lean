/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Model

/-!
# Depth-five circuits with gates indexed by finite types

`Cslib.Circuits.DepthFive.Circuit` numbers its gates by `Fin`. A construction usually has
natural gate names: tuples, paths, pairs of a block and an entry. `Circuit.ofFintype` builds a
circuit from gate data indexed by arbitrary finite types, numbering the gates by
`Fintype.equivFin`. The polynomial it computes is the same nested sum and product over the gate
names, and its size is the total number of names.

## Main definitions

* `Cslib.Circuits.DepthFive.Circuit.ofFintype`: a circuit from gates indexed by finite types.

## Main results

* `Circuit.polynomial_ofFintype`: the polynomial of `Circuit.ofFintype`.
* `Circuit.size_ofFintype`: its size.
-/

@[expose] public section

namespace Cslib.Circuits.DepthFive.Circuit

open MvPolynomial

variable {K σ L M U : Type*} [Fintype L] [Fintype M] [Fintype U]

/-- The circuit with lower product gates `L`, middle sum gates `M` and upper product gates `U`,
numbered by `Fintype.equivFin`. -/
noncomputable def ofFintype [Zero K] (degree : ℕ) (lowerDeg : L → ℕ)
    (lowerForms : (l : L) → Fin (lowerDeg l) → σ → K) (middleDeg : M → ℕ)
    (middleCoeff : M → L → K)
    (middle_hom : ∀ m l, middleCoeff m l ≠ 0 → lowerDeg l = middleDeg m)
    (upperArity : U → ℕ) (upperInputs : (u : U) → Fin (upperArity u) → M) (outCoeff : U → K)
    (out_hom : ∀ u, outCoeff u ≠ 0 → ∑ a, middleDeg (upperInputs u a) = degree) :
    Circuit K σ where
  lower := Fintype.card L
  middle := Fintype.card M
  upper := Fintype.card U
  degree := degree
  lowerDeg i := lowerDeg ((Fintype.equivFin L).symm i)
  lowerForms i := lowerForms ((Fintype.equivFin L).symm i)
  middleDeg j := middleDeg ((Fintype.equivFin M).symm j)
  middleCoeff j i := middleCoeff ((Fintype.equivFin M).symm j) ((Fintype.equivFin L).symm i)
  middle_hom _ _ := middle_hom _ _
  upperArity t := upperArity ((Fintype.equivFin U).symm t)
  upperInputs t a := Fintype.equivFin M (upperInputs ((Fintype.equivFin U).symm t) a)
  outCoeff t := outCoeff ((Fintype.equivFin U).symm t)
  out_hom t h := by simpa using out_hom _ h

variable [CommSemiring K] [Fintype σ] (degree : ℕ) (lowerDeg : L → ℕ)
  (lowerForms : (l : L) → Fin (lowerDeg l) → σ → K) (middleDeg : M → ℕ)
  (middleCoeff : M → L → K)
  (middle_hom : ∀ m l, middleCoeff m l ≠ 0 → lowerDeg l = middleDeg m)
  (upperArity : U → ℕ) (upperInputs : (u : U) → Fin (upperArity u) → M) (outCoeff : U → K)
  (out_hom : ∀ u, outCoeff u ≠ 0 → ∑ a, middleDeg (upperInputs u a) = degree)

/-- The polynomial of `Circuit.ofFintype` is the nested sum and product over the gate names. -/
theorem polynomial_ofFintype :
    (ofFintype degree lowerDeg lowerForms middleDeg middleCoeff middle_hom upperArity upperInputs
      outCoeff out_hom).polynomial =
      ∑ u, C (outCoeff u) * ∏ a, ∑ l, C (middleCoeff (upperInputs u a) l) *
        ∏ b, ∑ v, C (lowerForms l b v) * X v := by
  refine Fintype.sum_equiv (Fintype.equivFin U).symm _ _ fun t => ?_
  refine congrArg (C _ * ·) (Finset.prod_congr rfl fun a _ => ?_)
  refine Fintype.sum_equiv (Fintype.equivFin L).symm _ _ fun i => ?_
  simp only [ofFintype, lowerPoly, Equiv.symm_apply_apply]
  rfl

omit [Fintype σ] in
/-- The size of `Circuit.ofFintype` is the total number of gate names. -/
theorem size_ofFintype :
    (ofFintype degree lowerDeg lowerForms middleDeg middleCoeff middle_hom upperArity upperInputs
      outCoeff out_hom).size = Fintype.card L + Fintype.card M + Fintype.card U :=
  rfl

end Cslib.Circuits.DepthFive.Circuit
