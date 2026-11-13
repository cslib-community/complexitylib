/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiscreteLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.FieldTheory.Finite.Basic

/-!
# Discrete-logarithm extraction from two linear relations

Several discrete-logarithm reductions end the same way: two answers give two linear relations
`z = w + c * x` and `z' = w + c' * x` modulo the prime group order `q` with `c ≠ c'`, and the
reduction outputs the witness `x = (c - c')⁻¹ (z - z')`. Schnorr's extractor
([BonehShoup2023], Example 19.2) reads `c, c'` as the two challenges and `z, z'` as the two
responses. Two Pedersen openings `(m₀, r₀) ≠ (m₁, r₁)` of one commitment under `h = α • g` satisfy
`m₀ + r₀ * α = m₁ + r₁ * α`, so `α = extractNat q r₁ m₀ r₀ m₁` ([Pedersen1991], Section 3,
Theorem 3.1; [BonehShoup2023], Section 10.6.1, Fact 10.3); the discrete-logarithm hash of
[KatzLindell2020], Theorem 9.79, reuses that extraction.

`extractNat` computes the witness on natural numbers, inverting by Fermat's little theorem as a
`(q - 2)`nd power, so a polynomial-time machine can output it.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.extractNat`: the witness `(c - c')⁻¹ (z - z')` modulo `q`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.extractNat_cast`: modulo a prime `q`, `extractNat` is
  `(c - c')⁻¹ (z - z')` whenever `c` and `c'` are distinct modulo `q`.
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_extractNat`: the witness is computable
  in polynomial time from the group description and the four binary numbers.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Example 19.2 and Section 10.6.1.
* [T. P. Pedersen, *Non-Interactive and Information-Theoretic Secure Verifiable Secret
  Sharing*][Pedersen1991], Section 3, Theorem 3.1.
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Theorem 9.79.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Turing.MultiTapeTM

/-- The witness `(c - c')⁻¹ (z - z')` modulo `q`, computed on natural numbers with the inverse as a
`(q - 2)`nd power. -/
@[expose] def extractNat (q c z c' z' : ℕ) : ℕ :=
  ((c % q + q - c' % q) % q) ^ (q - 2) % q * ((z % q + q - z' % q) % q) % q

/-- Fermat's little theorem gives the inverse in `extractNat`: modulo a prime `q`, it is
`(c - c')⁻¹ (z - z')` whenever `c` and `c'` are distinct modulo `q`. -/
theorem extractNat_cast {q : ℕ} [Fact q.Prime] {c z c' z' : ℕ}
    (hc : (c : ZMod q) ≠ c') :
    (extractNat q c z c' z' : ZMod q) = ((c : ZMod q) - c')⁻¹ * ((z : ZMod q) - z') := by
  have hsub (a b : ℕ) : (((a % q + q - b % q) % q : ℕ) : ZMod q) = (a : ZMod q) - b := by
    rw [ZMod.natCast_mod, Nat.cast_sub ((Nat.mod_lt _ (Fact.out : q.Prime).pos).le.trans
      (Nat.le_add_left _ _)), Nat.cast_add, ZMod.natCast_mod, ZMod.natCast_mod, ZMod.natCast_self,
      add_zero]
  have hne : (c : ZMod q) - c' ≠ 0 := sub_ne_zero.mpr hc
  have hinv : ((c : ZMod q) - c') ^ (q - 2) = ((c : ZMod q) - c')⁻¹ :=
    ZMod.pow_card_sub_two_eq_inv hne
  simp only [extractNat, Nat.cast_mul, ZMod.natCast_mod, Nat.cast_pow, hsub, hinv]

variable {F : PrimeOrderGroupFamily}

/-- The witness `extractNat` is computable in polynomial time from the group description and the
four binary numbers. -/
@[fun_prop]
theorem computableInPolyTime_extractNat {α : Type} {input : α ↪ List Bool}
    {d : α → F.Desc} {c z c' z' : α → ℕ} (hd : ComputableInPolyTime d input F.encDesc)
    (hc : ComputableInPolyTime c input encNat) (hz : ComputableInPolyTime z input encNat)
    (hc' : ComputableInPolyTime c' input encNat) (hz' : ComputableInPolyTime z' input encNat) :
    ComputableInPolyTime (fun a => extractNat (F.order (d a)) (c a) (z a) (c' a) (z' a))
      input encNat := by
  refine .of_tidy ?_
  have hq : ComputableTidilyInPolyTime (fun a => F.order (d a)) input encNat :=
    F.computableInPolyTime_order.tidy.comp hd.tidy
  have hdiff {x y : α → ℕ} (hx : ComputableTidilyInPolyTime x input encNat)
      (hy : ComputableTidilyInPolyTime y input encNat) :
      ComputableTidilyInPolyTime
        (fun a => (x a % F.order (d a) + F.order (d a) - y a % F.order (d a)) % F.order (d a))
        input encNat :=
    .binary_mod' (.binary_sub' (.binary_add' (.binary_mod' hx hq) hq) (.binary_mod' hy hq)) hq
  have hpow := (ComputableInPolyTime.binary_powMod
    (ComputableInPolyTime.of_tidy (hdiff hc.tidy hc'.tidy))
    (ComputableInPolyTime.of_tidy (.binary_sub' hq (.const 2)))
    (ComputableInPolyTime.of_tidy hq) fun a => (F.prime_order (d a)).pos).tidy
  exact .binary_mod' (.binary_mul' hpow (hdiff hz.tidy hz'.tidy)) hq

end Cslib.Crypto.PrimeOrderGroupFamily
