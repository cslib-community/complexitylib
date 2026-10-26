/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Homomorphic.Leveled.Basic
public import Complexity.Crypto.Computational.Homomorphic.KeyChain.Reduction

/-!
# Chosen-message experiments for the leveled construction

The public-artifact experiment lets the adversary choose its messages after receiving the entire
serialized key chain. The zero-link reduction places the base challenge public key first and
generates every later key itself. A generated secret supplies the first zero link's length;
when the chain has no links, that length is unused. Its guessing stage retains the adversary's
exact state and adds the ordinary fresh-ciphertext tag to the base challenge.

`leveledAdversary` combines the two encrypted-link hybrid reductions (`E.linkAdversary` for the
`false` and message-swapped `true` challenge worlds) and the dyadically weighted `zeroLinkAdversary`
into a single two-stage base IND-CPA adversary, realizing Gentry's Theorem 4 concrete-security
reduction up to a constant factor ([Gentry2009], Section 2, Theorem 4, p. 171): writing
`d = budget n` and `ℓ = capacity n`, the exact loss is `4 * dyadicSize (2 * d) * dyadicSize ℓ`
(between `4 * (2 * d + 1) * (ℓ + 1)` and `16 * (2 * d + 1) * (ℓ + 1)`, so within a constant factor
of Gentry's `ℓ * (d + 1)`). `isPPT_leveledAdversary` proves the asymptotic efficiency consequence
that the reduction is uniform strict PPT whenever the adversary, base scheme, depth and capacity
are; the multiplicative runtime bound (`poly(ℓ, d)` times that of the adversary) is not proved here.

## Main definitions

* `Cslib.Crypto.Homomorphic.Leveled.publicKeyGame`: adaptive message selection on a public artifact.
* `Cslib.Crypto.Homomorphic.Leveled.zeroLinkAdversary`: the zero-link two-stage base reduction.
* `Cslib.Crypto.Homomorphic.Leveled.leveledAdversary`: the unified two-stage base reduction for the
  full leveled construction.

## References

* [C. Gentry, *Fully homomorphic encryption using ideal lattices*, Section 2, Theorem 4][Gentry2009]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Section 11.2][BonehShoup2023]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.Leveled

open ProbComp Probability

/-- Choose both messages after seeing every public key and encrypted link, then give the tagged
challenge ciphertext to the guessing stage together with its unchanged saved state. -/
def publicKeyGame (E : Scheme) (adversary : Encryption.Adversary) (bit : Bool) (n : ℕ)
    (artifact : List (List Bool) × List (List (List Bool))) : ProbComp Bool := do
  let choice ← adversary.choose n (encPublicKey artifact)
  let ciphertext ← E.encrypt n (artifact.1.getD 0 [])
    (if bit then choice.1.2 else choice.1.1)
  adversary.guess n choice.2 (false :: ciphertext)

/-- Simulate the all-zero chain using the challenge key as its initial public key. The unknown
challenge secret is never read or saved; only independently generated secrets supply lengths. -/
def zeroLinkAdversary (E : Scheme) (depth : ℕ → ℕ)
    (adversary : Encryption.Adversary) : Encryption.Adversary where
  choose n challengePk := do
    let rest ← OracleComp.replicate (depth n) (E.keyGen n)
    let links ← E.encryptZeroKeyLinks n
      ((challengePk, (rest.headD ([], [])).2) :: rest)
    adversary.choose n (encPublicKey (challengePk :: rest.map Prod.fst, links))
  guess n state ciphertext := adversary.guess n state (false :: ciphertext)

/-- Prefix two selector bits onto the saved state of a chosen-message choice. -/
def tagLeveledChoice (first second : Bool) (choice : (Bool × Bool) × List Bool) :
    (Bool × Bool) × List Bool :=
  (choice.1, first :: second :: choice.2)

/-- Swap the two challenge messages of a chosen-message choice while keeping its saved state. -/
def swapLeveledChoice (choice : (Bool × Bool) × List Bool) :
    (Bool × Bool) × List Bool :=
  ((choice.1.2, choice.1.1), choice.2)

/-- Fixed inactive choice for rejected dyadic coordinates or the unused selector branch. -/
def rejectLeveledChoice : (Bool × Bool) × List Bool :=
  ((false, false), [true, true])

/-- Unified two-stage base IND-CPA reduction for the acyclic leveled construction
([Gentry2009], Section 2, Theorem 4, p. 171, up to a constant factor in the loss;
the running-time clause is not formalized). Two fair selector bits choose between:
* `(false, false)`: the `false`-world encrypted-link reduction `E.linkAdversary`,
* `(false, true)`: the message-swapped `true`-world encrypted-link reduction `E.linkAdversary`,
* `(true, false)`: the zero-link reduction `zeroLinkAdversary`, weighted by the inverse dyadic
  grid size `(dyadicSize (depth n) * dyadicSize (capacity n))⁻¹` via `sampleDyadicCoin`,
* `(true, true)`: an inactive branch returning `false`. -/
noncomputable def leveledAdversary (E : Scheme) (depth capacity : ℕ → ℕ)
    (adversary : Encryption.Adversary) : Encryption.Adversary where
  choose n challengePk := do
    let first ← ProbComp.uniform Bool
    let second ← ProbComp.uniform Bool
    if first then
      if second then
        pure rejectLeveledChoice
      else
        let keepLink ← sampleDyadicCoin (depth n) 1
        let keepBit ← sampleDyadicCoin (capacity n) 1
        if keepLink then
          if keepBit then
            tagLeveledChoice true false <$>
              (zeroLinkAdversary E depth adversary).choose n challengePk
          else
            pure rejectLeveledChoice
        else
          pure rejectLeveledChoice
    else
      if second then
        (tagLeveledChoice false true ∘ swapLeveledChoice) <$>
          (E.linkAdversary depth capacity (publicKeyGame E adversary true)).choose n challengePk
      else
        tagLeveledChoice false false <$>
          (E.linkAdversary depth capacity (publicKeyGame E adversary false)).choose n challengePk
  guess n state ciphertext :=
    if state.headD true then
      if state.tail.headD true then
        pure false
      else
        (zeroLinkAdversary E depth adversary).guess n state.tail.tail ciphertext
    else
      if state.tail.headD true then
        (E.linkAdversary depth capacity (publicKeyGame E adversary true)).guess n
          state.tail.tail ciphertext
      else
        (E.linkAdversary depth capacity (publicKeyGame E adversary false)).guess n
          state.tail.tail ciphertext

end Cslib.Crypto.Homomorphic.Leveled
