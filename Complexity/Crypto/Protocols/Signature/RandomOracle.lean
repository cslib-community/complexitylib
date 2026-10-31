/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Control.Monad.Memoize
public import Complexity.Languages.Probabilistic.QueryCount
public import Complexity.Languages.Probabilistic.Sum
public import Cslib.Probability.PMF
import Complexity.Probability.PMF

/-!
# Signatures in the random-oracle model

A signature scheme in the random-oracle model ([BonehShoup2023], Section 13.2.1) signs and
verifies with oracle access to a function `H : Query → Digest`, which the security experiment
draws uniformly at random. Signing draws its coins and then runs an `OracleComp` program against
`H`; verification is a deterministic `OracleComp` program. The oracle is sampled lazily: each new
point gets a uniform answer, remembered in an association list (`oracle`), so the query and digest
types need not be finite beyond the digests.

The existential-unforgeability experiment (`eufCmaGame`, [BonehShoup2023], Attack Game 13.1 in
its random-oracle version) gives a forger the public key and oracle access to the signer and to
`H`; the forger wins with a valid signature on a message it never asked to have signed. A
`Forger` has explicit coins, drawn first, and is otherwise a deterministic `OracleComp` program;
this is the form in which a forger can be rerun on the same coins, as forking needs. Its signing
and hash calls are counted separately (`Forger.CallBounded`), as security bounds depend on them
differently.

These are exact probability laws for one scheme and one forger, with no efficiency claim. The
oracle interface is the library's `OracleComp`; it is meant to be re-expressed in the shared
interactive-protocol core of #643 once that core exists.

This interface is separate from the computational `Cslib.Crypto.SignatureScheme`, which packages
word encodings, strict PPT certificates and verification without an oracle. Here the key and
signing coins are arbitrary typed laws, and signing and verification share the hash oracle. A
computational statement about a scheme of this form needs encodings, an efficient realization of
the oracle and resource certificates on top of the exact bound; the two notions are not competing
computational interfaces.

## Main definitions

* `Cslib.Crypto.Protocols.ROMSignature.Scheme`: key generation, signing and verification.
* `Cslib.Crypto.Protocols.ROMSignature.Forger`: a forger with explicit coins.
* `Cslib.Crypto.Protocols.ROMSignature.Forger.CallBounded`: bounds on a forger's signing and hash
  calls.
* `Cslib.Crypto.Protocols.ROMSignature.oracle`: the lazily sampled uniform random oracle.
* `Cslib.Crypto.Protocols.ROMSignature.eufCmaGame`: the random-oracle EUF-CMA experiment.
* `Cslib.Crypto.Protocols.ROMSignature.Scheme.Correct`: honest signatures verify.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 13.1 and 13.2.1.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.ROMSignature

open Probability OracleComp

/-- The calls of a forger: a signing call names a message and returns a signature, and a hash call
names a point and returns its digest. -/
abbrev ForgerSpec (M Query Sig Digest : Type) : OracleSpec (M ⊕ Query) :=
  (fun _ : M => Sig) ⊕ₒ (fun _ : Query => Digest)

/-- A signature scheme in the random-oracle model, with public keys `PK`, secret keys `SK`,
messages `M`, signatures `Sig`, and oracle `H : Query → Digest`. Signing first draws coins. -/
structure Scheme (PK SK M Sig Query Digest : Type) where
  /-- Draw a public key and a secret key. -/
  keyGen : PMF (PK × SK)
  /-- The signer's coins. -/
  SignCoins : Type
  /-- Draw the signer's coins for a message. -/
  signCoins : SK → M → PMF SignCoins
  /-- Sign, querying the oracle. -/
  sign : SK → M → SignCoins → OracleComp (fun _ : Query => Digest) Sig
  /-- Verify, querying the oracle. -/
  verify : PK → M → Sig → OracleComp (fun _ : Query => Digest) Bool

/-- A forger with explicit coins: it draws its coins, then, given the public key, calls the signer
and the oracle and outputs a message and a signature. -/
structure Forger (PK M Sig Query Digest : Type) where
  /-- The forger's coins. -/
  Coins : Type
  /-- Draw the forger's coins. -/
  coins : PMF Coins
  /-- Forge, calling the signer and the oracle. -/
  forge : PK → Coins → OracleComp (ForgerSpec M Query Sig Digest) (M × Sig)

variable {PK SK M Sig Query Digest : Type}

/-- A forger's call costs one when it is a signing call. -/
def signingCost : M ⊕ Query → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- A forger's call costs one when it is a hash call. -/
def hashCost : M ⊕ Query → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- The forger makes at most `signs` signing calls and at most `hashes` hash calls on every path,
for every public key and every choice of its coins. -/
def Forger.CallBounded (A : Forger PK M Sig Query Digest) (signs hashes : ℕ) : Prop :=
  ∀ pk coins, IsCostBounded signingCost (A.forge pk coins) signs ∧
    IsCostBounded hashCost (A.forge pk coins) hashes

/-- A forger making at most `signs` signing and `hashes` hash calls makes at most
`signs + hashes` calls. -/
theorem Forger.CallBounded.isQueryBounded {A : Forger PK M Sig Query Digest} {signs hashes : ℕ}
    (h : A.CallBounded signs hashes) (pk : PK) (coins : A.Coins) :
    IsQueryBounded (A.forge pk coins) (signs + hashes) :=
  ((h pk coins).1.add (h pk coins).2).of_le fun q => by cases q <;> simp [signingCost, hashCost]

variable [DecidableEq Query] [Fintype Digest] [Nonempty Digest]

variable (Digest) in
/-- The random oracle: a uniform digest for each new point, remembered thereafter. -/
noncomputable def oracle (q : Query) : StateT (List (Query × Digest)) PMF Digest :=
  memoize (fun _ => PMF.uniformOfFintype Digest) q

/-- Answer a forger's calls: sign with the secret key, recording the message, or query the
oracle. Signing and the forger share the oracle. -/
noncomputable def handler (scheme : Scheme PK SK M Sig Query Digest) (sk : SK) :
    (q : M ⊕ Query) → StateT (List (Query × Digest) × List M) PMF (ForgerSpec M Query Sig Digest q)
  | .inl m => fun state => do
    let coins ← scheme.signCoins sk m
    let signed ← (interpret (oracle Digest) (scheme.sign sk m coins)).run state.1
    return (signed.1, (signed.2, m :: state.2))
  | .inr x => fun state => do
    let answer ← oracle Digest x state.1
    return (answer.1, (answer.2, state.2))

/-- The random-oracle EUF-CMA experiment ([BonehShoup2023], Attack Game 13.1): the forger wins with
a valid signature, under the same oracle, on a message it never had signed. -/
noncomputable def eufCmaGame [DecidableEq M] (scheme : Scheme PK SK M Sig Query Digest)
    (forger : Forger PK M Sig Query Digest) : PMF Bool := do
  let keys ← scheme.keyGen
  let s ← forger.coins
  let forged ← (interpret (handler scheme keys.2) (forger.forge keys.1 s)).run ([], [])
  let msig := forged.1
  let state := forged.2
  let verified ← (interpret (oracle Digest) (scheme.verify keys.1 msig.1 msig.2)).run
    state.1
  return (verified.1 && !(state.2.contains msig.1))

/-- A scheme is correct when every honest signature verifies under the same oracle, from every
state of the oracle. -/
def Scheme.Correct (scheme : Scheme PK SK M Sig Query Digest) : Prop :=
  ∀ keys ∈ scheme.keyGen.support, ∀ m coins, coins ∈ (scheme.signCoins keys.2 m).support →
    ∀ cache, ∀ signed ∈ ((interpret (oracle Digest) (scheme.sign keys.2 m coins)).run
      cache).support, ∀ verified ∈ ((interpret (oracle Digest)
        (scheme.verify keys.1 m signed.1)).run signed.2).support, verified.1 = true

end Cslib.Crypto.Protocols.ROMSignature
