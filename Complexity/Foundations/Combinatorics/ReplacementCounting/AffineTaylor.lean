/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.ReplacementCounting
public import Complexity.Foundations.Data.MvPolynomial.AffineTaylor

/-!
# Replacement counting and affine Taylor substitution

This bridge identifies the Boolean replacement polynomial in the counting interface with the
polynomial used by the affine-Taylor cancellation theorem. Both rational measurement-fiber
recovery and finite-field streaming recovery can use this identity without importing each
other's specialized constructions.

## Main results

* `Cslib.ReplacementCounting.targetPolynomial_eq_replacedSum`: the two replacement-polynomial
  interfaces agree over every commutative ring.
-/

public section

open Finset

namespace Cslib.ReplacementCounting

/-- `ReplacementCounting.targetPolynomial` coincides with `AffineTaylor.replacedSum`
([OpenAI2026ETH], equation (3.3), pp. 21, 24). -/
theorem targetPolynomial_eq_replacedSum {ι F A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing A] {κ : F → Type*} (s : Finset F) (Φ : ∀ f, MvPolynomial (κ f) A)
    (P : ∀ f, κ f → ι → Polynomial A) :
    targetPolynomial s Φ P = Cslib.AffineTaylor.replacedSum s Φ P := by
  unfold targetPolynomial Cslib.AffineTaylor.replacedSum replacementEval
  exact sum_congr (Finset.ext fun _ => by simp only [mem_univ]) fun x _ =>
    prod_congr rfl fun f _ => rfl

end Cslib.ReplacementCounting
