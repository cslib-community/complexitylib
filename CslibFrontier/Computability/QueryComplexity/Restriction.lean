/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.QueryComplexity.Measures
public import CslibFrontier.Foundations.Data.BitString.PartialAssignment

/-!
# Certificates and functional restrictions

CSLib's `QueryComplexity.PartialAssignment n` is definitionally the arbitrary-coordinate
`BitString.PartialAssignment (Fin n)`. The two agreement and support predicates also agree
definitionally, so the generic restriction operations apply without conversions.

## Main results

* `Cslib.QueryComplexity.fill_restrict`: filling a coordinate certificate is a piecewise input.
* `Cslib.QueryComplexity.forces_iff_forall_fill`: a forcing assignment makes the restricted
  function constant.

## References

* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

namespace Cslib.QueryComplexity

open BitString.PartialAssignment

variable {n : ℕ}

/-- Filling a partial assignment read from `x` uses `x` on its support and `y` elsewhere. -/
@[simp] theorem fill_restrict (x : BitString n) (S : Finset (Fin n)) (y : BitString n) :
    fill (restrict x S) y = S.piecewise x y := by
  funext i
  by_cases hi : i ∈ S <;> simp [fill, restrict, hi]

/-- An assignment forces `b` precisely when filling arbitrary inputs always produces value `b`. -/
theorem forces_iff_forall_fill (f : BooleanFunction n) (C : PartialAssignment n) (b : Bool) :
    Forces f C b ↔ ∀ x, f (fill C x) = b := by
  constructor
  · intro h x
    exact h _ (agrees_fill C x)
  · intro h x hx
    rw [← agrees_iff_fill_eq.mp hx]
    exact h x

end Cslib.QueryComplexity
