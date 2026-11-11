/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Homogeneous depth-five circuits

A syntactically homogeneous `ΣΠΣΠΣ` circuit computes a sum of products of sums of products of
linear forms, in which every gate computes a homogeneous polynomial of its formal degree
[OpenAI, §1.1][OpenAI2026DepthFive]. `Cslib.Circuits.DepthFive.Circuit` records such a circuit in
a normalized form with three layers of gates:

* a *lower product gate* is a product of homogeneous linear forms in the variables;
* a *middle sum gate* is a linear combination of lower product gates of one common degree;
* an *upper product gate* is a product of middle sum gates, with repetition allowed;
* the output is a linear combination of upper product gates of one common degree.

Gates are shared freely: a lower product gate may feed any number of middle sums, and a middle
sum any number of upper products. The size `Circuit.size` counts the lower product, middle sum
and upper product gates.

## Relation to the source model

The source counts every gate of a layered circuit, including the bottom sum gates, the variable
leaves and the output gate. A circuit of that model with `S` gates gives a `Circuit` computing
the same polynomial with `size ≤ S`: its bottom sum gates become the linear forms stored in the
lower product gates, the scalars on its wires become the coefficients of the middle sums and of
the output, and its lower product, middle sum and upper product gates are kept. A lower bound
on `Circuit.size` is therefore a lower bound on the gate count of the source. Wires with
coefficient zero are unconstrained, so a gate may be listed without being used.

## Main definitions

* `Cslib.Circuits.DepthFive.Circuit`: a normalized homogeneous `ΣΠΣΠΣ` circuit.
* `Cslib.Circuits.DepthFive.Circuit.size`: its number of product and middle sum gates.
* `Cslib.Circuits.DepthFive.Circuit.polynomial`: the polynomial it computes.

## Main results

* `Cslib.Circuits.DepthFive.Circuit.isHomogeneous_polynomial`: the output is homogeneous of the
  formal degree of the circuit.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §1.1 (unrefereed preprint)
-/

@[expose] public section

namespace Cslib.Circuits.DepthFive

open MvPolynomial

/-- A syntactically homogeneous `ΣΠΣΠΣ` circuit in the variables `σ`, in normalized form. -/
structure Circuit (K σ : Type*) [Zero K] where
  /-- The number of lower product gates. -/
  lower : ℕ
  /-- The number of middle sum gates. -/
  middle : ℕ
  /-- The number of upper product gates. -/
  upper : ℕ
  /-- The formal degree of the output. -/
  degree : ℕ
  /-- The number of linear forms multiplied by each lower product gate. -/
  lowerDeg : Fin lower → ℕ
  /-- The coefficients of the linear forms multiplied by each lower product gate. -/
  lowerForms : (i : Fin lower) → Fin (lowerDeg i) → σ → K
  /-- The formal degree of each middle sum gate. -/
  middleDeg : Fin middle → ℕ
  /-- The coefficient of each lower product gate in each middle sum gate. -/
  middleCoeff : Fin middle → Fin lower → K
  /-- A middle sum gate only adds lower product gates of its own formal degree. -/
  middle_hom : ∀ j i, middleCoeff j i ≠ 0 → lowerDeg i = middleDeg j
  /-- The number of inputs of each upper product gate. -/
  upperArity : Fin upper → ℕ
  /-- The middle sum gates multiplied by each upper product gate. -/
  upperInputs : (t : Fin upper) → Fin (upperArity t) → Fin middle
  /-- The coefficient of each upper product gate in the output. -/
  outCoeff : Fin upper → K
  /-- The output only adds upper product gates of the formal degree of the circuit. -/
  out_hom : ∀ t, outCoeff t ≠ 0 → ∑ a, middleDeg (upperInputs t a) = degree

namespace Circuit

variable {K σ : Type*} [CommSemiring K] [Fintype σ] (c : Circuit K σ)

/-- The number of gates: lower products, middle sums and upper products. -/
def size : ℕ := c.lower + c.middle + c.upper

/-- The polynomial computed by a lower product gate. -/
noncomputable def lowerPoly (i : Fin c.lower) : MvPolynomial σ K :=
  ∏ a, ∑ v, C (c.lowerForms i a v) * X v

/-- The polynomial computed by a middle sum gate. -/
noncomputable def middlePoly (j : Fin c.middle) : MvPolynomial σ K :=
  ∑ i, C (c.middleCoeff j i) * c.lowerPoly i

/-- The polynomial computed by an upper product gate. -/
noncomputable def upperPoly (t : Fin c.upper) : MvPolynomial σ K :=
  ∏ a, c.middlePoly (c.upperInputs t a)

/-- The polynomial computed by the circuit. -/
noncomputable def polynomial : MvPolynomial σ K :=
  ∑ t, C (c.outCoeff t) * c.upperPoly t

theorem isHomogeneous_lowerPoly (i : Fin c.lower) :
    (c.lowerPoly i).IsHomogeneous (c.lowerDeg i) := by
  have h := IsHomogeneous.prod Finset.univ (fun a => ∑ v, C (c.lowerForms i a v) * X v)
    (fun _ => 1) fun a _ => IsHomogeneous.sum _ _ _ fun v _ => isHomogeneous_C_mul_X _ v
  simpa [lowerPoly] using h

theorem isHomogeneous_middlePoly (j : Fin c.middle) :
    (c.middlePoly j).IsHomogeneous (c.middleDeg j) := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  by_cases h : c.middleCoeff j i = 0
  · simpa [h] using isHomogeneous_zero σ K _
  · exact (c.middle_hom j i h ▸ c.isHomogeneous_lowerPoly i).C_mul _

theorem isHomogeneous_upperPoly (t : Fin c.upper) :
    (c.upperPoly t).IsHomogeneous (∑ a, c.middleDeg (c.upperInputs t a)) :=
  IsHomogeneous.prod _ _ _ fun _ _ => c.isHomogeneous_middlePoly _

/-- The circuit computes a homogeneous polynomial of its formal degree. -/
theorem isHomogeneous_polynomial : c.polynomial.IsHomogeneous c.degree := by
  refine IsHomogeneous.sum _ _ _ fun t _ => ?_
  by_cases h : c.outCoeff t = 0
  · simpa [h] using isHomogeneous_zero σ K _
  · exact (c.out_hom t h ▸ c.isHomogeneous_upperPoly t).C_mul _

end Circuit

end Cslib.Circuits.DepthFive
