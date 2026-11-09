/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import ComplexityAbstracts.PrimesBridge

/-! # PRIMES is in P

Agrawal, Kayal and Saxena showed that primality can be decided in deterministic polynomial time:
a fixed deterministic machine, given a natural number `n` by its binary digits, decides whether
`n` is prime in time polynomial in the number of digits, that is, in `log n`. Trial division takes
time polynomial in `n` itself, which is exponential in the length of the input.

The statement concerns deterministic binary multi-tape Turing machines with finitely many states,
with time and work space polynomially bounded in the input length (the shared foundation
`Computation.PolyTime`), and the binary encoding of naturals, least significant digit first
(`Encoding.encNat`). No bound on the degree of the polynomial is stated.

A reader only needs to inspect the definitions and the theorem statement in this file, and the
displayed shared foundations, to verify that it states the intended claim. Lean checks the proof
through `PrimesBridge`, and `#check_abstract` audits that the public statements depend only on this
file, the shared foundations, Lean, Mathlib and upstream CSLib. The library's decider is the AKS
algorithm on the word RAM, with the integer thresholds `⌈log₂ n⌉` in place of `log₂ n`, simulated
by a Turing machine.

## References

* [M. Agrawal, N. Kayal, N. Saxena, *PRIMES is in P*][AKS2004]
-/

namespace ComplexityAbstracts.PrimesAbstract

/-- The class `P` with respect to an encoding `enc`: the problems `A` decided by a Boolean
function computable in polynomial time, that is, `a ∈ A` exactly when `f a = true`. -/
def P {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f : α → Bool,
    ComplexityTests.Abstracts.Computation.PolyTime f enc
      ComplexityTests.Abstracts.Encoding.encBool ∧
    ∀ a, a ∈ A ↔ f a = true}

/-- **PRIMES is in P** [Agrawal, Kayal, Saxena][AKS2004]: the set of primes, with naturals
encoded by their binary digits, is decidable in deterministic polynomial time. -/
theorem primes_mem_P : {n : ℕ | n.Prime} ∈ P ComplexityTests.Abstracts.Encoding.encNat :=
  PrimesBridge.primes_mem_P

/--
info: abstract audit passed for `ComplexityAbstracts.PrimesAbstract`: 2 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.PrimesAbstract allowing [
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation
]

end ComplexityAbstracts.PrimesAbstract
