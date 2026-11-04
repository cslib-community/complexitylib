/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
public import Mathlib.Data.Nat.Sqrt

/-!
# Compositional polynomial resource bounds

`growth_poly` proves `Turing.MultiTapeTM.PolyBounded size cost` by the existing constant,
input-size, addition, multiplication and fixed-power rules, together with logarithm and square
root bounds. Local polynomial-bound hypotheses supply the leaves. It also accepts
`Cslib.PolynomiallyBounded` goals through the existing `fun_prop` rules.

This proves polynomial growth only. Word admission, exact time bounds and signed overflow
conditions remain separate obligations. For substitution, use `PolyBounded.comp` with the outer
bound and run `growth_poly` on the inner size expression; the tactic does not guess an
intermediate size measure.

The closure layer adapts Samuel Schlesinger's existing polynomial-bound API. The new
input-size logarithm and square-root rules and the `growth_poly` tactic are by Erik Demaine.
-/

public section

namespace Turing.MultiTapeTM.PolyBounded

variable {α : Type*} {size u : α → ℕ}

/-- Natural logarithms preserve polynomial growth in any input-size measure. -/
theorem log (b : ℕ) (hu : PolyBounded size u) :
    PolyBounded size (fun a => Nat.log b (u a)) :=
  hu.mono fun a => Nat.log_le_self b (u a)

/-- Natural square roots preserve polynomial growth in any input-size measure. -/
theorem sqrt (hu : PolyBounded size u) : PolyBounded size (fun a => Nat.sqrt (u a)) :=
  hu.mono fun a => Nat.sqrt_le_self (u a)

end Turing.MultiTapeTM.PolyBounded

/-- Prove a polynomial resource-growth expression using local bounds and compositional rules.
Substitution uses an explicit `PolyBounded.comp`; no resource model or degree is inferred. -/
macro (name := growthPoly) "growth_poly" : tactic => `(tactic|
  solve
  | repeat' first
    | assumption
    | exact Turing.MultiTapeTM.PolyBounded.self
    | exact Turing.MultiTapeTM.PolyBounded.const _
    | apply Turing.MultiTapeTM.PolyBounded.add
    | apply Turing.MultiTapeTM.PolyBounded.mul
    | apply Turing.MultiTapeTM.PolyBounded.pow
    | apply Turing.MultiTapeTM.PolyBounded.log
    | apply Turing.MultiTapeTM.PolyBounded.sqrt
    | fun_prop)
