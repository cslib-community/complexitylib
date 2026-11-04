/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract foundations)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
import Cslib.Foundations.Data.Nat.PolynomialBound

/-! # Polynomial-time functions and verifiers

One deterministic binary multi-tape Turing machine, with finitely many states, computes the
function on every encoded input. Its time and work space are polynomially bounded in input bit
length. Input is read-only and output is write-only. The machine is uniform: its code and its
bounds are fixed before the input is chosen. No condition is imposed on words outside an
encoding's image.

A verifier receives an instance and a certificate. Its running time is polynomial in their
combined encoded length, not just the instance length. The pair encoding has length
`2 * |enc x| + 1 + |w|`, so it gives the usual polynomial bound in `|enc x| + |w|`.
-/

namespace ComplexityTests.Abstracts.Computation

/-- Total polynomial-time computation on encoded inputs, with explicit time and space bounds. -/
def PolyTime {α β : Type} (f : α → β) (a : α ↪ List Bool) (b : β ↪ List Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength f a b t s

/-- One total polynomial-time deterministic verifier, on an instance and a binary certificate. -/
def PolyTimeVerifier {α : Type} (enc : α ↪ List Bool) (V : α × List Bool → Bool) : Prop :=
  PolyTime V (Encoding.encPair enc Encoding.encBits) Encoding.encBool

end ComplexityTests.Abstracts.Computation

/--
info: abstract audit passed for `ComplexityTests.Abstracts.Computation`:
2 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.Computation allowing [ComplexityAbstracts.Encoding]
