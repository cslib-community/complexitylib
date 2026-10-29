/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.BravermanBridge

/-! # Braverman: polylogarithmic independence fools AC⁰

A distribution on `n`-bit strings is `k`-wise independent if any `k` of its bits are uniformly
distributed. Such distributions can have far smaller support than the uniform distribution, yet
they look uniform to every small circuit of constant depth built from NOT gates and AND and OR
gates of unbounded fan-in: the probability that the circuit outputs `true` is close to the
fraction of all inputs on which it does, once `k` is polylogarithmic in the size of the circuit and
in the inverse of the error. This settles a conjecture of Linial and Nisan.

The theorem below takes one parameter `q ≥ 1` for the size, the fan-in and the error: a circuit of
depth at most `d`, with at most `2 ^ q` gates, each of fan-in less than `2 ^ q`, is fooled with
error `2 ^ (-q)` by every `(64 q) ^ ((2 d + 3) (d + 7) + 1)`-wise independent distribution. Taking
`q ≥ log₂ (fan-in + 1)` and `q` at least `log₂` of the size and of the inverse of the error `ε`,
this is `k = (log (m / ε)) ^ O(d²)` for circuits of size `m` with fan-in at most `m`, the form of
Braverman's theorem. The explicit constants and exponent are our own and are weaker than
Braverman's: the proof uses a Linial–Mansour–Nisan bound with exponent `1 / (d + 1)`.

The circuit model is the elementary unbounded fan-in basis, whose model module is explicitly
allowed below: unary NOT and AND and OR of every arity, with nullary AND and OR the two constants.
A circuit's size counts every gate, including NOT gates and constants, and its depth counts every
gate on a path, including NOT gates. Probabilities are those of Mathlib's discrete distributions
`PMF`, read as real numbers with `toReal`. The result is nonuniform and information-theoretic: no
running time is asserted.

A reader only needs to inspect the definitions and theorem statements in this file to verify that
they state the intended claim. Lean checks the proofs through `BravermanBridge`, and
`#check_abstract` audits that every statement depends only on this file, the allowed circuit basis
and background libraries.

## References

* [M. Braverman, *Polylogarithmic independence fools AC⁰ circuits*, Main Theorem][Braverman2010]
* [A. Tal, *Tight bounds on the Fourier spectrum of AC⁰*, Theorem 20][Tal2017]
* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
-/

namespace ComplexityAbstracts.BravermanAbstract

/-- The elementary unbounded fan-in basis has unary NOT and AND and OR of every arity. Nullary AND
and OR are the two constants. Its model module is explicitly allowed below. -/
abbrev ACBasis := Cslib.Circuits.Boolean.Unbounded.signature

/-- The ordinary Boolean meaning of unbounded AND, OR and NOT. -/
def meaning : Cslib.Circuits.Interpretation ACBasis Bool :=
  Cslib.Circuits.Boolean.Unbounded.interpretation

/-- A distribution `X` on `n`-bit strings is **`k`-wise independent** if any `k` of its bits are
uniformly distributed: for every set `T` of at most `k` positions, the restriction of a sample to
`T` takes each of its `2 ^ |T|` values with probability `2 ^ (-|T|)`. -/
def KWiseIndependent {n : ℕ} (k : ℕ) (X : PMF (Fin n → Bool)) : Prop :=
  ∀ T : Finset (Fin n), T.card ≤ k → ∀ y : T → Bool, X.map T.restrict y = (2 ^ T.card)⁻¹

/-- The probability that the circuit `C` outputs `true` on an input drawn from `X`. -/
noncomputable def probabilityTrue {n : ℕ} (X : PMF (Fin n → Bool))
    (C : Cslib.Circuits.Circuit ACBasis n 1) : ℝ :=
  (Finset.univ.filter fun x => C.eval meaning x 0 = true).sum fun x => (X x).toReal

/-- The fraction of the `2 ^ n` inputs on which the circuit `C` outputs `true`: its probability
of outputting `true` on a uniformly random input. -/
noncomputable def fractionTrue {n : ℕ} (C : Cslib.Circuits.Circuit ACBasis n 1) : ℝ :=
  ((Finset.univ.filter fun x => C.eval meaning x 0 = true).card : ℝ) / 2 ^ n

/-- **Braverman.** Let `C` be a circuit of NOT gates and unbounded fan-in AND and OR gates of depth
at most `d`, with at most `2 ^ q` gates, each of fan-in less than `2 ^ q`, where `q ≥ 1`. Then for
every `k`-wise independent distribution `X` with `k ≥ (64 q) ^ ((2 d + 3) (d + 7) + 1)`, the
probability that `C` outputs `true` on a sample of `X` is within `2 ^ (-q)` of the fraction of
inputs on which `C` outputs `true`. Size and depth count NOT gates. -/
theorem braverman {n d q k : ℕ} (hq : 1 ≤ q) (C : Cslib.Circuits.Circuit ACBasis n 1)
    (fanIn : C.FanInAtMost (2 ^ q - 1)) (size : C.size ≤ 2 ^ q) (depth : C.depth ≤ d)
    (X : PMF (Fin n → Bool)) (independent : KWiseIndependent k X)
    (hk : (64 * q) ^ ((2 * d + 3) * (d + 7) + 1) ≤ k) :
    |probabilityTrue X C - fractionTrue C| ≤ 1 / 2 ^ q :=
  BravermanBridge.braverman hq C fanIn size depth X independent hk

/--
info: abstract audit passed for `ComplexityAbstracts.BravermanAbstract`: 8 root
declarations, 111 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.BravermanAbstract allowing [
  Complexity.Computability.Circuit.Boolean.Unbounded
]

end ComplexityAbstracts.BravermanAbstract
