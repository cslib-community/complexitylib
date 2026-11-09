/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Computational.Paillier.Algebra
public import CslibFrontier.Crypto.Game
import CslibFrontier.Probability.PMF

/-!
# The decisional composite residuosity assumption

A balanced modulus is a product `N = p * q` of distinct odd primes of the same bit length. An
element of `(ZMod (N ^ 2))ˣ` is an `N`-th residue when it equals `r ^ N` for some unit `r`. The
decisional composite residuosity (DCR) problem asks to distinguish a uniform `N`-th residue modulo
`N ^ 2` from a uniform unit modulo `N ^ 2`, given only `N`. The DCR assumption relative to a law
on moduli says that every uniform strict PPT distinguisher has negligible advantage.

A description of a balanced modulus is its pair of prime factors `(p, q)`, with validity part of
the type, as for Schnorr groups. Nothing here claims that valid descriptions can be generated
efficiently; the assumption is stated relative to an arbitrary law on descriptions.

## Main definitions

* `Cslib.Crypto.BalancedModulus.Valid`, `Cslib.Crypto.BalancedModulus.Desc`: valid factor pairs
  `(p, q)` of balanced moduli.
* `Cslib.Crypto.dcrRealGame`, `Cslib.Crypto.dcrIdealGame`: the two DCR experiments.
* `Cslib.Crypto.DCR`: the decisional composite residuosity assumption.

## Main results

* `Cslib.Crypto.BalancedModulus.Desc.coprime_totient`: `gcd(N, φ(N)) = 1` for every valid
  description ([KatzLindell2020], Claim 15.7).
* `Cslib.Crypto.BalancedModulus.Desc.totient_eq`: the computed totient `(p - 1) * (q - 1)` is
  `φ(N)`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Chapter 15,
  Claim 15.7 and Definition 15.10.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace BalancedModulus

/-- A valid pair `(p, q)` of prime factors of a balanced modulus `N = p * q`: distinct odd primes
of the same bit length. -/
structure Valid (d : ℕ × ℕ) : Prop where
  /-- The first factor is prime. -/
  prime_fst : d.1.Prime
  /-- The second factor is prime. -/
  prime_snd : d.2.Prime
  /-- The factors are distinct. -/
  fst_ne_snd : d.1 ≠ d.2
  /-- The first factor is odd. -/
  two_lt_fst : 2 < d.1
  /-- The second factor is odd. -/
  two_lt_snd : 2 < d.2
  /-- The factors have the same bit length. -/
  size_eq : d.1.size = d.2.size

/-- Valid factor pairs `(p, q)` of balanced moduli. -/
abbrev Desc : Type := {d : ℕ × ℕ // Valid d}

/-- The first prime factor `p` of a valid description `(p, q)`. -/
abbrev Desc.p (d : Desc) : ℕ := d.val.1

/-- The second prime factor `q` of a valid description `(p, q)`. -/
abbrev Desc.q (d : Desc) : ℕ := d.val.2

/-- The modulus `N = p * q` of a valid description `(p, q)`. -/
abbrev Desc.modulus (d : Desc) : ℕ := d.p * d.q

/-- The totient `φ(N) = (p - 1) * (q - 1)`, computed from the factors. -/
abbrev Desc.totient (d : Desc) : ℕ := (d.p - 1) * (d.q - 1)

/-- The modulus is greater than `1`. -/
theorem Desc.one_lt_modulus (d : Desc) : 1 < d.modulus := by
  have hp := d.2.two_lt_fst
  have hq := d.2.two_lt_snd
  change 1 < d.val.1 * d.val.2
  nlinarith

instance (d : Desc) : NeZero d.modulus := ⟨by have := d.one_lt_modulus; lia⟩

instance (d : Desc) : NeZero (d.modulus ^ 2) := ⟨pow_ne_zero 2 (NeZero.ne _)⟩

/-- The computed totient `(p - 1) * (q - 1)` is Euler's totient of `N = p * q`. -/
theorem Desc.totient_eq (d : Desc) : d.totient = d.modulus.totient := by
  rw [Desc.totient, Desc.modulus,
    Nat.totient_mul ((Nat.coprime_primes d.2.prime_fst d.2.prime_snd).mpr d.2.fst_ne_snd),
    Nat.totient_prime d.2.prime_fst, Nat.totient_prime d.2.prime_snd]

/-- **Claim 15.7** ([KatzLindell2020]) for a valid description: `gcd(N, φ(N)) = 1`. -/
theorem Desc.coprime_totient (d : Desc) : d.modulus.Coprime d.modulus.totient :=
  Paillier.coprime_totient d.2.prime_fst d.2.prime_snd d.2.fst_ne_snd d.2.two_lt_fst
    d.2.two_lt_snd d.2.size_eq

/-- Descriptions are encoded as the binary pair `(p, q)`. -/
def encDesc : Desc ↪ List Bool :=
  (Function.Embedding.subtype _).trans (encPair encNat encNat)

end BalancedModulus

open BalancedModulus

/-- The real experiment of the decisional composite residuosity problem ([KatzLindell2020],
Definition 15.10): draw `(p, q) ← setup n`, set `N = p * q`, draw a uniform unit `r` modulo
`N ^ 2`, and give the distinguisher `N` and the residue of `r ^ N` modulo `N ^ 2`. -/
noncomputable def dcrRealGame (setup : ℕ → PMF Desc)
    (distinguisher : ℕ → ℕ × ℕ → ProbComp Bool) (n : ℕ) : Game := do
  let d ← setup n
  let r ← PMF.uniformOfFintype (ZMod (d.modulus ^ 2))ˣ
  ProbComp.eval (distinguisher n (d.modulus, ((r ^ d.modulus : (ZMod (d.modulus ^ 2))ˣ) :
    ZMod (d.modulus ^ 2)).val))

/-- The ideal experiment of the decisional composite residuosity problem ([KatzLindell2020],
Definition 15.10): draw `(p, q) ← setup n`, set `N = p * q`, draw a uniform unit `r` modulo
`N ^ 2`, and give the distinguisher `N` and the residue of `r` itself. -/
noncomputable def dcrIdealGame (setup : ℕ → PMF Desc)
    (distinguisher : ℕ → ℕ × ℕ → ProbComp Bool) (n : ℕ) : Game := do
  let d ← setup n
  let r ← PMF.uniformOfFintype (ZMod (d.modulus ^ 2))ˣ
  ProbComp.eval (distinguisher n (d.modulus, (r : ZMod (d.modulus ^ 2)).val))

/-- The **decisional composite residuosity assumption** relative to a law `setup` on balanced
moduli ([KatzLindell2020], Definition 15.10): every uniform strict PPT distinguisher, given `N`,
has negligible advantage in telling a uniform `N`-th residue modulo `N ^ 2` from a uniform unit
modulo `N ^ 2`. -/
def DCR (setup : ℕ → PMF Desc) : Prop :=
  Game.Indistinguishable (dcrRealGame setup) (dcrIdealGame setup) fun distinguisher =>
    IsPPTOn (encPair encUnary (encPair encNat encNat)) encBool
      (fun input => distinguisher input.1 input.2)

end Cslib.Crypto
