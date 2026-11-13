/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Advice
public import CslibFrontier.Computability.Complexity.Classes.Advice.Hierarchy

/-!
# Constant advice is strictly weaker than polynomial advice

The exact-advice hierarchy supplies a language requiring one more bit than any fixed advice
length. Its advice is polynomially bounded, so the existing advice/circuit equivalence puts it
in P/poly. At one bit this gives the strict containment in Goldreich's January 2007 draft
Theorem 3.7 (`r2.pdf`, PDF6/printed122) [Goldreich2007DraftR2], using the native complete-pair
clock and unrestricted nonuniform advice.

## Main results

* `Cslib.Circuits.Boolean.PWithAdvice_const_ssubset_PPoly`: every constant advice class is
  strictly contained in P/poly.
-/

public section

namespace Cslib.Circuits.Boolean

open Complexity

/-- Polynomial advice strictly contains every constant exact-advice class, including P/1. -/
theorem PWithAdvice_const_ssubset_PPoly (k : ℕ) :
    PWithAdvice (fun _ => k) ⊂ PPoly := by
  have hnext := PWithAdvice_const_ssubset_succ k
  have hpoly := PWithAdvice_subset_PPoly
    (show PolynomiallyBounded (fun _ : ℕ => k + 1) by fun_prop)
  exact hnext.trans_subset hpoly

end Cslib.Circuits.Boolean
