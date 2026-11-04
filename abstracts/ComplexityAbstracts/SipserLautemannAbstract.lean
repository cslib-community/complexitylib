/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.SipserLautemannBridge

/-! # Sipser–Lautemann: bounded-error randomness lies in the second polynomial level

Every bounded-error randomized polynomial-time language admits both existential–universal
and universal–existential descriptions by polynomially long binary blocks and a deterministic
polynomial-time test: BPP ⊆ Σ₂ ∩ Π₂.

Lautemann's proof amplifies the randomized algorithm. For a yes-instance, polynomially many
xor shifts of its accepting seeds cover every seed; for a no-instance, no such cover exists.
Guessing the shifts and checking every seed yields the existential–universal description.
Complement closure yields the reverse order.

Lean checks the proof bridge and audits the abstract's statement dependencies.

## References

* [M. Sipser, *A complexity theoretic approach to randomness*][Sipser1983].
* [C. Lautemann, *BPP and the polynomial hierarchy*][Lautemann1983].
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Theorem 7.15.
-/

namespace ComplexityAbstracts.SipserLautemannAbstract

/-! ## Bit strings and deterministic polynomial-time tests

Inputs are bit strings. A test reads an instance `x` and a second string `w` of random bits
or certificates. Encode the pair by framing each bit `b` of `x` as `[true, b]`, terminating
with `[false]`, then appending `w`. The separator preserves the boundary.

-/

/-- Encode a pair `(x, w)` by the self-delimiting frame of `x`, followed by `w`. -/
def encodeInput (z : List Bool × List Bool) : List Bool :=
  z.1.flatMap (fun b => [true, b]) ++ [false] ++ z.2

theorem encodeInput_injective : Function.Injective encodeInput :=
  SipserLautemannBridge.encInput.injective

/-- Injective binary encoding of the two input strings. -/
def encInput : (List Bool × List Bool) ↪ List Bool := ⟨encodeInput, encodeInput_injective⟩

/-- A Boolean answer is encoded as its single bit. -/
def encAnswer : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/-- One deterministic binary multi-tape machine halts on every encoded pair and writes
`V`'s answer, within time and work-space bounds polynomial in the pair's encoded length.
`Cslib.PolynomiallyBounded` means bounded above by a polynomial. -/
def PolyTimePredicate (V : List Bool × List Bool → Bool) : Prop :=
  ∃ t s : ℕ → ℕ, Cslib.PolynomiallyBounded t ∧ Cslib.PolynomiallyBounded s ∧
    Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength V encInput encAnswer t s

/-! ## Randomness and two quantifier blocks -/

/-- BPP languages have a polynomial-time test with `p(|x|)` fair independent random bits,
correct on at least two thirds of seeds for each input. The inequalities count correct seeds
out of `2 ^ p(|x|)`. A function `Fin m → Bool` represents an `m`-bit seed;
`List.ofFn` lists its bits. -/
def BPP : Set (Set (List Bool)) :=
  {A | ∃ (p : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    PolyTimePredicate V ∧ ∀ x,
      (x ∈ A → 2 * 2 ^ p.eval x.length ≤
        3 * (Finset.univ.filter fun r : Fin (p.eval x.length) → Bool =>
          V (x, List.ofFn r) = true).card) ∧
      (x ∉ A → 2 * 2 ^ p.eval x.length ≤
        3 * (Finset.univ.filter fun r : Fin (p.eval x.length) → Bool =>
          V (x, List.ofFn r) = false).card)}

/-- Σ₂ uses an existential block `u` followed by a universal block `v`, with polynomial lengths
and a total polynomial-time test of `u ++ v`. Block lengths depend only on the input length. -/
def SigmaTwo : Set (Set (List Bool)) :=
  {A | ∃ (p q : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    PolyTimePredicate V ∧ ∀ x, x ∈ A ↔
      ∃ u : List Bool, u.length = p.eval x.length ∧
        ∀ v : List Bool, v.length = q.eval x.length → V (x, u ++ v) = true}

/-- Π₂ reverses the order: every polynomial-length block `u` has a polynomial-length response
`v` passing the test. The response may depend on the instance and `u`. The two classes may
use different tests and length polynomials. -/
def PiTwo : Set (Set (List Bool)) :=
  {A | ∃ (p q : Polynomial ℕ) (V : List Bool × List Bool → Bool),
    PolyTimePredicate V ∧ ∀ x, x ∈ A ↔
      ∀ u : List Bool, u.length = p.eval x.length →
        ∃ v : List Bool, v.length = q.eval x.length ∧ V (x, u ++ v) = true}

/-- **Sipser–Gács–Lautemann.** Every bounded-error randomized polynomial-time language has both
polynomial two-block descriptions: BPP ⊆ Σ₂ ∩ Π₂. -/
theorem sipserLautemann : BPP ⊆ SigmaTwo ∩ PiTwo :=
  SipserLautemannBridge.sipserLautemann

/--
info: 'ComplexityAbstracts.SipserLautemannAbstract.sipserLautemann' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sipserLautemann

/--
info: abstract audit passed for `ComplexityAbstracts.SipserLautemannAbstract`: 10 root
declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.SipserLautemannAbstract

end ComplexityAbstracts.SipserLautemannAbstract
