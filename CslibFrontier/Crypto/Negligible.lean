/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: submitted #1069 @1d14c55a10cfe3fe4463cffa61a7f02f0d56f502

public import CslibFrontier.Init
public import Cslib.Crypto.Negligible

/-!
# Negligible function automation

The negligible-bound definitions and closure lemmas are supplied by CSLib's merged PR #1068.
This module registers the remaining `fun_prop` automation from PR #1069, so composite bounds such
as a polynomial loss times a negligible advantage plus a negligible error are discharged directly.
The upstream declarations retain their existing public names and nonnegative-real semantics.
The pointwise addition and multiplication lemmas expose lambda expressions to `fun_prop`.

## Main results

* `fun_prop` registrations for `Cslib.Crypto.Negligible` and its zero, addition, multiplication
  and polynomial-loss closure lemmas.
* `Cslib.Crypto.Negligible.add_fun`, `Cslib.Crypto.Negligible.mul_fun`: pointwise automation rules.

## References

Automation registrations copied from cslib PR #1069 at
`1d14c55a10cfe3fe4463cffa61a7f02f0d56f502`. The base API is imported from cslib PR #1068.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal

attribute [fun_prop] Negligible negligible_zero Negligible.add Negligible.mul
  Negligible.polynomiallyBounded_mul

-- upstream: candidate

/-- The pointwise form of negligible addition, for `fun_prop` automation. -/
@[fun_prop] theorem Negligible.add_fun {ε δ : ℕ → ℝ≥0} (hε : Negligible ε)
    (hδ : Negligible δ) : Negligible (fun n => ε n + δ n) :=
  hε.add hδ

/-- The pointwise form of negligible multiplication, for `fun_prop` automation. -/
@[fun_prop] theorem Negligible.mul_fun {ε δ : ℕ → ℝ≥0} (hε : Negligible ε)
    (hδ : Negligible δ) : Negligible (fun n => ε n * δ n) :=
  hε.mul hδ

end Cslib.Crypto
