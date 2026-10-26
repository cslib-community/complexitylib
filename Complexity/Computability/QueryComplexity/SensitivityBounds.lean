/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.QueryComplexity.Midrijanis

/-!
# Polynomial bounds in terms of sensitivity

Huang's theorem `deg(f) ≤ s(f)²` [Huang2019] and the Nisan–Szegedy bound `bs(f) ≤ 2 deg(f)²`
[NisanSzegedy1994] give `bs(f) ≤ 2 s(f)⁴`
(`QueryComplexity.blockSensitivity_le_two_mul_sensitivity_pow_four`). Combined with Nisan's
`C(f) ≤ s(f) bs(f)` [Nisan1991], this gives `C(f) ≤ 2 s(f)⁵`. Midrijanis's cubic degree bound
`D(f) ≤ 2 deg(f)³` [Midrijanis2004] and Huang's theorem give the sharper decision tree bound
`D(f) ≤ 2 s(f)⁶`.

## Main results

* `Cslib.QueryComplexity.certificateComplexity_le_two_mul_sensitivity_pow_five`:
  `C(f) ≤ 2 s(f)⁵`.
* `Cslib.DecisionTree.complexity_le_two_mul_sensitivity_pow_six`: `D(f) ≤ 2 s(f)⁶`.

## References

* [H. Huang, *Induced subgraphs of hypercubes and a proof of the Sensitivity
  Conjecture*][Huang2019]
* [N. Nisan, M. Szegedy, *On the degree of Boolean functions as real polynomials*][NisanSzegedy1994]
* [N. Nisan, *CREW PRAMs and decision trees*][Nisan1991]
* [G. Midrijanis, *Exact quantum query complexity for total Boolean functions*][Midrijanis2004]
-/

@[expose] public section

namespace Cslib

open BitString

variable {n : ℕ}

namespace QueryComplexity

/-- `C(f) ≤ 2 s(f)⁵`, from Nisan's `C(f) ≤ s(f) bs(f)` and `bs(f) ≤ 2 s(f)⁴`. -/
theorem certificateComplexity_le_two_mul_sensitivity_pow_five (f : BooleanFunction n) :
    certificateComplexity f ≤ 2 * sensitivity f ^ 5 :=
  (certificateComplexity_le_sensitivity_mul_blockSensitivity f).trans
    ((Nat.mul_le_mul_left _ (blockSensitivity_le_two_mul_sensitivity_pow_four f)).trans_eq
      (by ring))

end QueryComplexity

namespace DecisionTree

open QueryComplexity

/-- **Decision tree complexity is polynomial in sensitivity**: `D(f) ≤ 2 s(f)⁶`, from
Midrijanis's `D(f) ≤ 2 deg(f)³` and Huang's `deg(f) ≤ s(f)²`. -/
theorem complexity_le_two_mul_sensitivity_pow_six (f : BooleanFunction n) :
    complexity f ≤ 2 * sensitivity f ^ 6 :=
  (complexity_le_two_mul_degree_pow_three f).trans
    ((Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (degree_le_sensitivity_sq f) 3)).trans_eq
      (by rw [← pow_mul]))

end DecisionTree

end Cslib
