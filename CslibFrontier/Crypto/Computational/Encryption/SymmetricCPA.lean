/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic
public import CslibFrontier.Crypto.Computational.PseudorandomFunction

/-!
# Symmetric chosen-plaintext security on a message space

A symmetric cipher in [BonehShoup2023] is defined over a message space `M`. Its CPA attack game
(Section 5.3, Attack Game 5.2, printed pp. 181–182) lets the adversary submit any number of pairs
`m₀, m₁ ∈ M` of the same length, and the challenger answers all of them under one key.
`SymmetricCipher.cpaGame` fixes `M` to the `n`-bit words at security parameter `n`. Block-cipher
modes need longer messages; randomized counter mode (Section 5.4.2, printed p. 189), for example,
encrypts sequences of blocks.

This module states the attack game for raw key-generation and encryption algorithms with an
admissibility predicate `valid n m₀ m₁` on challenge pairs, as `Encryption.INDCPAOn` does for
public-key encryption. A request whose pair is inadmissible is answered with the empty word and
does not invoke `encrypt`. `SymmetricINDCPAOn` asks that every uniform strict oracle-PPT
distinguisher have negligible advantage between the two challenge bits. Correctness and efficiency
of the honest algorithms are separate properties.

`SymmetricCipher.cpaGame` and `SymmetricCipher.INDCPA` in `Authenticated.lean` are the special
case of `n`-bit pairs; that module proves it (`SymmetricCipher.cpaGame_eq_symmetricCPAGameOn`,
`SymmetricCipher.indcpa_iff`).
`blockPairValid` admits equal-length pairs made of whole `n`-bit blocks: the message space
`Y^{≤ℓ}` of Section 5.4.2 without the cap `ℓ` on the number of blocks.

## Main definitions

* `Cslib.Crypto.symmetricCPAReplyOn`: the left-or-right encryption oracle for a pair predicate.
* `Cslib.Crypto.symmetricCPAGameOn`: the many-query left-or-right experiment.
* `Cslib.Crypto.SymmetricINDCPAOn`: adaptive chosen-plaintext security against uniform strict
  oracle-PPT distinguishers.
* `Cslib.Crypto.blockPairValid`: equal-length pairs of whole `n`-bit blocks.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 5.3 (Attack Game 5.2 and Definition 5.2, printed pp. 181–182) and Section 5.4.2
  (printed p. 189).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- The left-or-right encryption oracle with challenge-pair predicate `valid`
([BonehShoup2023], Section 5.3, Attack Game 5.2): decode `m₀ = unframe request.2` and
`m₁ = dropFrame request.2`; if `valid n m₀ m₁` holds, encrypt `if bit then m₁ else m₀` under `k`,
and otherwise answer `[]` without encrypting. -/
@[expose]
noncomputable def symmetricCPAReplyOn (valid : ℕ → List Bool → List Bool → Bool)
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)) (n : ℕ) (k : List Bool)
    (bit : Bool) (request : Unit × List Bool) : ProbComp (List Bool) :=
  let m0 := unframe request.2
  let m1 := dropFrame request.2
  if valid n m0 m1 then encrypt n k (if bit then m1 else m0) else pure []

/-- The many-query left-or-right CPA experiment with challenge-pair predicate `valid`
([BonehShoup2023], Section 5.3, Attack Game 5.2): sample `k ← keyGen n` and run
`adversary n []` with oracle `symmetricCPAReplyOn valid encrypt n k bit`. -/
@[expose]
noncomputable def symmetricCPAGameOn (valid : ℕ → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let k ← keyGen n
  (adversary n []).run (symmetricCPAReplyOn valid encrypt n k bit)

/-- Adaptive chosen-plaintext security on the challenge pairs admitted by `valid`
([BonehShoup2023], Section 5.3, Definition 5.2): every uniform strict `IsOraclePPT encBool`
distinguisher has negligible advantage between the experiments with challenge bits `false` and
`true`. The negligible bound may depend on the distinguisher, which is fixed before the parameter.
-/
@[expose]
def SymmetricINDCPAOn (valid : ℕ → List Bool → List Bool → Bool)
    (keyGen : ℕ → ProbComp (List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (symmetricCPAGameOn valid keyGen encrypt adversary false n))
    (fun adversary n => ProbComp.eval (symmetricCPAGameOn valid keyGen encrypt adversary true n))
    (IsOraclePPT encBool)

/-- Equal-length challenge pairs made of whole `n`-bit blocks. At `n = 0` only the pair of empty
messages is admitted. -/
@[expose]
def blockPairValid (n : ℕ) (m₀ m₁ : List Bool) : Bool :=
  (m₀.length == m₁.length) && (m₀.length % n == 0)

end Cslib.Crypto
