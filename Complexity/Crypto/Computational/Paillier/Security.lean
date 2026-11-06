/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Paillier
import Complexity.Probability.PMF

/-!
# Paillier encryption is IND-CPA secure under DCR (work in progress)

WORK IN PROGRESS, NOT FOR REVIEW: the statements below are the intended interface of the
follow-up to the Paillier scheme PR; the proofs are not written yet (`sorry`).

[KatzLindell2020], Theorem 15.13: if the decisional composite residuosity problem is hard relative
to the modulus generator, Paillier encryption is IND-CPA secure.

## Proof plan

For a chosen-message adversary `A` and a challenge bit `b`, the DCR distinguisher `D_b` on input
`(N, y)` runs `A.choose n (encNat N)` and, for an admissible pair, gives `A.guess` the word of
`(1 + N) ^ m_b * y mod N ^ 2`. The four hops are:

1. `gameOn ... A b` and `dcrRealGame setup (dcrDistinguisher A b)` are within statistical distance
   `2⁻ⁿ + (N - φ(N)) / N`. In the DCR real game `y = s ^ N` for `s` uniform in `(ZMod (N ^ 2))ˣ`,
   and `s ^ N` depends only on `s mod N` (`Paillier.natCast_pow_self_mod`); reduction modulo `N`
   pushes the uniform law on `(ZMod (N ^ 2))ˣ` to the uniform law on `(ZMod N)ˣ`. The encryption
   randomness is `unitOrOne N r` for `r` from `ProbComp.sampleModNat`, which is within
   `2⁻ⁿ + (N - φ(N)) / N` of uniform on the units.
2. `dcrRealGame` and `dcrIdealGame` for `D_b` differ by the DCR advantage of `D_b`.
3. `dcrIdealGame setup (dcrDistinguisher A false) = dcrIdealGame setup (dcrDistinguisher A true)`:
   multiplying a uniform unit by the unit `(1 + N) ^ m` gives a uniform unit, whatever `m` is.
4. Symmetric to hops 1 and 2 for `b = true`.

`(N - φ(N)) / N ≤ 1 / p + 1 / q`, which is negligible when the generator's primes have at least
`n` bits; this is the hypothesis `hsize` below, faithful to the book's `n`-bit primes.
-/

@[expose] public section

namespace Cslib.Crypto.Paillier

open Probability Turing.MultiTapeTM BalancedModulus Encryption

/-- Admissible challenge pairs: both messages are below the modulus `N` of the public key. -/
def validMessages (_n : ℕ) (pk : List Bool) (m₀ m₁ : ℕ) : Bool :=
  decide (m₀ < ofBits pk ∧ m₁ < ofBits pk)

/-- The DCR distinguisher built from a chosen-message adversary and a challenge bit: on `(N, y)`,
it runs the adversary on the public key `N` and answers its challenge with
`(1 + N) ^ m * y mod N ^ 2`. -/
noncomputable def dcrDistinguisher (adversary : AdversaryOf ℕ) (bit : Bool) (n : ℕ)
    (input : ℕ × ℕ) : ProbComp Bool := do
  let choice ← adversary.choose n (encNat input.1)
  if validMessages n (encNat input.1) choice.1.1 choice.1.2 then
    let m := if bit then choice.1.2 else choice.1.1
    adversary.guess n choice.2
      (encNat (powMod (input.1 ^ 2) (1 + input.1) m * input.2 % input.1 ^ 2))
  else
    return false

/-- WIP: the reduction distinguishers are uniform strict PPT. -/
theorem isPPTOn_dcrDistinguisher {adversary : AdversaryOf ℕ} (hA : adversary.IsPPT encNat)
    (bit : Bool) :
    IsPPTOn (encPair encUnary (encPair encNat encNat)) encBool
      (fun input => dcrDistinguisher adversary bit input.1 input.2) := by
  sorry

/-- WIP ([KatzLindell2020], Theorem 15.13): DCR relative to the generator's law implies IND-CPA
security of Paillier encryption, for generators whose primes have at least `n` bits. -/
theorem DCR.indcpaOn_paillier {gen : ℕ → ProbComp Desc} (hgen : IsPPTOn encUnary encDesc gen)
    (hsize : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, n ≤ d.p.size ∧ n ≤ d.q.size)
    (hDCR : DCR fun n => ProbComp.eval (gen n)) :
    INDCPAOn validMessages encNat (keyGen gen) encrypt := by
  sorry

end Cslib.Crypto.Paillier
