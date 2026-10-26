/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.NaturalProof
public import Complexity.Crypto.Computational.GGM.Circuit
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# The natural proofs barrier from pseudorandom generators

Razborov and Rudich derive the hypothesis of the natural proofs barrier, an exponentially secure
keyed family of Boolean functions with members of polynomial circuit size, from a pseudorandom
generator secure against circuits of size `2 ^ (k ^ ε)`, by the construction of Goldreich,
Goldwasser and Micali [RazborovRudich1997, Section 4], [GGM1986]. With the GGM family of
`Cslib.Crypto.GGM.booleanFamily`, whose members have circuits of polynomial size
(`Cslib.Crypto.GGM.complexity_booleanFamily_le`) and which is exponentially secure for
subexponentially secure generators (`Cslib.Crypto.GGM.isExponentiallySecure_booleanFamily`), the
barrier `Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural` applies.

## Main results

* `Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural_of_generator`: if some family of
  length-doubling generators of polynomial circuit complexity is subexponentially secure, no
  `P/poly`-natural property is useful against `P/poly`.

## References

* [A. A. Razborov, S. Rudich, *Natural proofs*][RazborovRudich1997]
* [O. Goldreich, S. Goldwasser, S. Micali, *How to construct random functions*][GGM1986]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open NaturalProof

/-- **The natural proofs barrier from pseudorandom generators** [RazborovRudich1997, Section 4].
If a family of length-doubling generators of polynomial circuit complexity is subexponentially
secure against circuits, then no `P/poly`-natural property is useful against `P/poly`. The GGM
functions with keys of length polynomial in the number of inputs form an exponentially secure keyed
family whose members have circuits of polynomial size
(`Cslib.Crypto.GGM.isExponentiallySecure_booleanFamily`,
`Cslib.Crypto.GGM.complexity_booleanFamily_le`). -/
theorem not_isUseful_PPoly_of_isNatural_of_generator
    {G : ∀ k, Crypto.PRG.Generator (BitString k) (BitString (2 * k))} {d : ℕ}
    (hsize : PolynomiallyBounded fun k => complexity interpretation ⇑(G k))
    (hG : Crypto.PRG.IsSubexponentiallySecure G d) {C : ∀ n, Set (BooleanFunction n)}
    (hC : IsNatural PPoly C) : ¬ IsUseful PPoly C := by
  have hkey : PolynomiallyBounded fun n => (n + 1) ^ (2 * d + 1) := by fun_prop
  have hcomp := hsize.comp hkey
  exact not_isUseful_PPoly_of_isNatural (s := fun n =>
      n * (complexity interpretation ⇑(G ((n + 1) ^ (2 * d + 1))) + 4 * (n + 1) ^ (2 * d + 1)) + 2)
    (by fun_prop) (fun n => Crypto.GGM.complexity_booleanFamily_le _ n)
    (Crypto.GGM.isExponentiallySecure_booleanFamily hsize hG) hC

end Cslib.Circuits.Boolean
