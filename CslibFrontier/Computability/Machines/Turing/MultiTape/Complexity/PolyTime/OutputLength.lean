/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import Mathlib.Algebra.Polynomial.Eval.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Polynomials of the output length of a polynomial-time map

A verifier, counting function or ambiguity bound for `B` reads a resource of size `q(|f a|)` on
the reduced instance `f a`. Transporting it along a polynomial-time reduction `f` from `A` needs
one polynomial `P` with `q(|f a|) ≤ P(|a|)` for every instance `a` of `A`.
`Turing.MultiTapeTM.ComputableInPolyTime.exists_polynomial_eval_length_le` supplies it.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.exists_polynomial_eval_length_le`: a polynomial of the
  encoded output length is bounded by a polynomial of the encoded input length.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- **Polynomials of the output length.** For a polynomial-time map `f` and a polynomial `q`, some
polynomial `P` bounds `q(|f a|)` by `P(|a|)`. -/
theorem exists_polynomial_eval_length_le {f : α → β} (hf : ComputableInPolyTime f encIn encOut)
    (q : Polynomial ℕ) :
    ∃ P : Polynomial ℕ, ∀ a, q.eval (encOut (f a)).length ≤ P.eval (encIn a).length :=
  (PolyBounded.of_polynomiallyBounded_comp (Cslib.PolynomiallyBounded.polynomial_eval q)
    hf.polyBounded_length).exists_polynomial

end Turing.MultiTapeTM.ComputableInPolyTime
