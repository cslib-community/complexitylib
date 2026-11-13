/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Forgery

/-!
# Signature schemes

A signature scheme `Signature.Scheme PK SK M Sig` has typed public keys, secret keys, messages and
signatures. Key generation and signing are probabilistic programs and verification is a Boolean
test ([BonehShoup2023], Section 13.1). Correctness is a separate property (`Scheme.Correct`).

The security experiments are instances of the forgery experiment `forgeExperiment`: the forger
receives the public key, queries a signing oracle and outputs a candidate `(m, σ)`. In
`eufCmaExperiment` the oracle signs every query and `m` must never have been signed
([BonehShoup2023], Attack Game 13.1). `sufCmaExperiment` only asks that `(m, σ)` was never an
answer ([BonehShoup2023], Section 13.1.1). `oneTimeEufCmaExperiment` is the one-time variant of
Attack Game 13.1, whose oracle answers the first query only. Asymptotic security over a family of
schemes and the efficiency of the forger are stated on top of these experiments.

## Main definitions

* `Cslib.Crypto.Signature.Scheme`: a signature scheme with typed keys, messages and signatures.
* `Cslib.Crypto.Signature.Forger`: a forger with oracle access to a signer.
* `Cslib.Crypto.Signature.Scheme.Correct`: every honest signature verifies.
* `Cslib.Crypto.Signature.Scheme.restrict`: the scheme that accepts signatures only on admissible
  messages.
* `Cslib.Crypto.Signature.Scheme.eufCmaExperiment`, `sufCmaExperiment`,
  `oneTimeEufCmaExperiment`: the existential, strong and one-time forgery experiments.

## Main results

* `Cslib.Crypto.Signature.Scheme.succProbability_eufCmaExperiment_le`: a forger wins the existential
  experiment at most as often as the strong one.
* `Cslib.Crypto.Signature.Scheme.sufCmaExperiment_eq_eufCmaExperiment`: for a correct scheme with
  unique signatures the two experiments coincide.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 13.1 (Definition 13.1, Attack Game 13.1 and Section 13.1.1).
-/

@[expose] public section

namespace Cslib.Crypto.Signature

open Probability

/-- A signature scheme ([BonehShoup2023], Section 13.1) with public keys `PK`, secret keys `SK`,
messages `M` and signatures `Sig`. -/
structure Scheme (PK SK M Sig : Type) where
  /-- Key generation: draw a public key and its secret key. -/
  keyGen : ProbComp (PK × SK)
  /-- Sign a message with the secret key. -/
  sign : SK → M → ProbComp Sig
  /-- Verify a candidate signature on a message under the public key. -/
  verify : PK → M → Sig → Bool

/-- A forger receives the public key, queries a signing oracle on messages and outputs a candidate
message and signature. -/
abbrev Forger (PK M Sig : Type) := PK → ProbOracleComp (fun _ : M => Sig) (M × Sig)

namespace Scheme

variable {PK SK M Sig : Type}

/-- A scheme is correct when every signature that signing can output verifies, for every key pair
that key generation can output and every message. -/
def Correct (S : Scheme PK SK M Sig) : Prop :=
  ∀ keys ∈ (ProbComp.eval S.keyGen).support, ∀ m,
    ∀ σ ∈ (ProbComp.eval (S.sign keys.2 m)).support, S.verify keys.1 m σ = true

/-- The scheme `S` restricted to the messages accepted by `adm`: signing is unchanged and a
signature verifies only on an admissible message. -/
def restrict (S : Scheme PK SK M Sig) (adm : M → Bool) : Scheme PK SK M Sig where
  keyGen := S.keyGen
  sign := S.sign
  verify pk m σ := adm m && S.verify pk m σ

@[simp] theorem restrict_keyGen (S : Scheme PK SK M Sig) (adm : M → Bool) :
    (S.restrict adm).keyGen = S.keyGen := rfl

@[simp] theorem restrict_sign (S : Scheme PK SK M Sig) (adm : M → Bool) :
    (S.restrict adm).sign = S.sign := rfl

@[simp] theorem restrict_verify (S : Scheme PK SK M Sig) (adm : M → Bool) (pk : PK) (m : M)
    (σ : Sig) : (S.restrict adm).verify pk m σ = (adm m && S.verify pk m σ) := rfl

variable [Inhabited Sig]

/-- The existential forgery experiment under adaptive chosen-message attack ([BonehShoup2023],
Attack Game 13.1): draw a key pair, run the forger on the public key with a signing oracle for
every query, and accept a valid signature on a message that was never queried. -/
abbrev eufCmaExperiment [DecidableEq M] (S : Scheme PK SK M Sig) (A : Forger PK M Sig) :
    Experiment :=
  forgeExperiment S.keyGen (.ofSign S.sign) (fun pk _ => S.verify pk) freshMessage A

/-- The strong forgery experiment ([BonehShoup2023], Section 13.1.1): as `eufCmaExperiment`, but
a valid pair `(m, σ)` wins whenever the oracle never answered `m` with `σ`. -/
abbrev sufCmaExperiment [DecidableEq M] [DecidableEq Sig] (S : Scheme PK SK M Sig)
    (A : Forger PK M Sig) : Experiment :=
  forgeExperiment S.keyGen (.ofSign S.sign) (fun pk _ => S.verify pk) freshPair A

/-- The one-time existential forgery experiment: as `eufCmaExperiment`, but the signing oracle
answers only the first query and refuses every later one. -/
abbrev oneTimeEufCmaExperiment [DecidableEq M] (S : Scheme PK SK M Sig) (A : Forger PK M Sig) :
    Experiment :=
  forgeExperiment S.keyGen (Signer.ofSign S.sign).oneTime (fun pk _ => S.verify pk) freshMessage A

/-- **Strong unforgeability implies existential unforgeability**: a forger wins the existential
experiment at most as often as the strong one. -/
theorem succProbability_eufCmaExperiment_le [DecidableEq M] [DecidableEq Sig]
    (S : Scheme PK SK M Sig) (A : Forger PK M Sig) :
    (S.eufCmaExperiment A).succProbability ≤ (S.sufCmaExperiment A).succProbability :=
  succProbability_forgeExperiment_freshMessage_le A

/-- **Unique signatures**: for a correct scheme in which each message has at most one valid
signature under each supported key pair, the strong and existential forgery experiments have the
same distribution. -/
theorem sufCmaExperiment_eq_eufCmaExperiment [DecidableEq M] [DecidableEq Sig]
    {S : Scheme PK SK M Sig} (hS : S.Correct)
    (hunique : ∀ keys ∈ (ProbComp.eval S.keyGen).support, ∀ m σ σ',
      S.verify keys.1 m σ = true → S.verify keys.1 m σ' = true → σ = σ')
    (A : Forger PK M Sig) :
    ProbComp.eval (S.sufCmaExperiment A) = ProbComp.eval (S.eufCmaExperiment A) :=
  forgeExperiment_freshPair_eq_freshMessage (signer := .ofSign S.sign)
    (fun keys hkeys _ m _ hprog σ hσ => hS keys hkeys m σ (Option.some.inj hprog ▸ hσ))
    hunique A

end Scheme

end Cslib.Crypto.Signature
