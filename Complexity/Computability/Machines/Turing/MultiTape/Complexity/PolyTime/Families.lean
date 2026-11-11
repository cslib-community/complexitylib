/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives

/-!
# Polynomially bounded families under polynomial-time maps

A polynomial-time function on encoded pairs preserves polynomially bounded encoded lengths of
input families. The families themselves need not be computable. This is useful when transporting
witnesses or nonuniform advice through deterministic reductions.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.polynomiallyBounded_length_prod`: map two
  polynomially bounded input families through a polynomial-time function.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

open Cslib

universe u

/-- A polynomial-time function of a pair preserves polynomial bounds on the encoded lengths of
both input families, without requiring the families themselves to be computable. -/
theorem polynomiallyBounded_length_prod {α β : Type u} {γ : Type*} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {g : α × β → γ}
    (hg : ComputableInPolyTime g (encPair encA encB) encC)
    {a : ℕ → α} {b : ℕ → β} (ha : PolynomiallyBounded fun n => (encA (a n)).length)
    (hb : PolynomiallyBounded fun n => (encB (b n)).length) :
    PolynomiallyBounded fun n => (encC (g (a n, b n))).length := by
  have hin : PolyBounded id fun n => (encPair encA encB (a n, b n)).length := by
    refine (((PolyBounded.const 2).mul (PolyBounded.of_polynomiallyBounded id ha)).add
      (PolyBounded.const 1) |>.add (PolyBounded.of_polynomiallyBounded id hb)).mono fun n => ?_
    simp only [length_encPair, id]
    lia
  exact (hg.polyBounded_length.comp hin).polynomiallyBounded

end Turing.MultiTapeTM.ComputableInPolyTime
