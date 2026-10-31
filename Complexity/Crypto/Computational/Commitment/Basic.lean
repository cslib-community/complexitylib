/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.Encryption.Basic

/-!
# Public-parameter commitment schemes

A `CommitmentScheme` specifies the exact commitment distribution and verification rule under
public parameters. Its injective public encoding makes every honest operation depend on the
parameters shown to the adversary. Efficient evaluation and realization of the ideal distributions
are separate properties. `Commitment/PublicOperations` supplies certificates for deterministic
evaluation on supplied randomness and verification, using exactly this public encoding.

Chosen-message hiding reuses `Encryption.WordAdversary`, with its explicit saved state and uniform
strict-PPT certificates. Binding asks an adversary for two distinct messages and openings of the
same commitment.

## Main definitions

* `Cslib.Crypto.CommitmentScheme`: a public-parameter commitment scheme with exact distributional
  correctness.
* `Cslib.Crypto.CommitmentScheme.hidingForKey`, `Cslib.Crypto.CommitmentScheme.hidingGame`:
  chosen-message hiding experiments at a fixed key and under a setup distribution.
* `Cslib.Crypto.CommitmentScheme.StatisticalHiding`,
  `Cslib.Crypto.CommitmentScheme.ComputationalHiding`: statistical and computational hiding.
* `Cslib.Crypto.CommitmentScheme.isBindingCollision`, `Cslib.Crypto.CommitmentScheme.bindingGame`,
  `Cslib.Crypto.CommitmentScheme.Binding`: the binding predicate, experiment and security notion.

## Main results

* `Cslib.Crypto.CommitmentScheme.hidingForKey_eq_of_map_fst_commitDist_eq`,
  `Cslib.Crypto.CommitmentScheme.advantage_hidingForKey_eq_zero`: a commitment-string marginal
  independent of the message gives exact hiding.
* `Cslib.Crypto.CommitmentScheme.StatisticalHiding.computationalHiding`: statistical hiding
  implies computational hiding.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 8.12 (Definition 8.8, p. 344).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- A commitment scheme `(C, V)` with public parameters ([BonehShoup2023], Section 8.12, p. 344,
and Definition 8.8):
* `encodeKey k`: the encoded public parameter string presented to the adversary for key `k`.
  This encoding is injective: equal public strings determine the same key and hence the same
  valid messages, commitment distributions, and verification results.
  Injectivity is an information-theoretic condition; decoding and evaluating honest operations
  from this string need separate efficiency certificates.
* `ValidMessage k m`: predicate characterizing valid message words `m` in the message space for key
  `k`.
* `commitDist k msg`: the distribution of `(c, o)` (encoded commitment string `c` and encoded
  opening string `o`) produced by `C(msg)` under key `k`. `commitDist` is modeled as a `PMF` rather
  than a `ProbComp` so that group-based schemes such as Pedersen commitment can use the exact
  uniform distribution on `ZMod q` (matching `DiscreteLog`'s `PMF` setup; strict-PPT `ProbComp`
  machines sample `ZMod q` only approximately via `sampleModNat`).
* `verify k m c o`: the deterministic verification algorithm `V(m, c, o)` returning `true` to accept
  or `false` to reject. Neither `commitDist` nor `verify` bundles a polynomial-time complexity
  certificate in `CommitmentScheme`, keeping the general scheme interface at the distributional
  layer; concrete instantiations certify their encoded evaluation and reduction algorithms
  separately (e.g., `computableInPolyTime_encodePedersenCommit` and
  `isPPTOn_pedersenToDLAdversary`).
* `validMessage_of_verify` and `verify_of_mem_support`: `verify` accepts only valid message words
  and accepts every `(c, o)` in the support of `commitDist k m` for any valid message word `m`.

Chosen-message hiding reuses `Encryption.WordAdversary` (`Encryption.AdversaryOf (List Bool)` from
`Complexity/Crypto/Computational/Encryption/Basic.lean`), matching Boneh–Shoup's semantic-security
formulation of commitment hiding. -/
structure CommitmentScheme (Key : Type) where
  /-- Faithful encoding of the entire public parameter presented to the adversary. -/
  encodeKey : Key ↪ List Bool
  /-- Predicate characterizing valid message words in the message space for key `k`. -/
  ValidMessage : Key → List Bool → Prop
  /-- Distribution of `(c, o)` (encoded commitment string and encoded opening string) for message
  word `msg` under key `k`. -/
  commitDist : Key → List Bool → PMF (List Bool × List Bool)
  /-- Verification algorithm `V(m, c, o)` ([BonehShoup2023], Section 8.12, p. 344). -/
  verify : Key → List Bool → List Bool → List Bool → Bool
  /-- Only valid message words are accepted by `verify`. -/
  validMessage_of_verify : ∀ k m c o, verify k m c o = true → ValidMessage k m
  /-- Correctness: every `(c, o)` in the support of `commitDist k m` for a valid message word `m`
  is accepted by `verify k m co.1 co.2`. -/
  verify_of_mem_support : ∀ k m co, ValidMessage k m → co ∈ (commitDist k m).support →
    verify k m co.1 co.2 = true

/-- The chosen-message hiding experiment ([BonehShoup2023], Section 8.12, p. 344, and
Definition 8.8) at a fixed commitment key `k : Key` for hidden bit `bit : Bool`: the adversary
receives `S.encodeKey k`, chooses `((m₀, m₁), st)`, and receives the commitment string `c = co.1`
(without the opening `co.2`) for `co ← S.commitDist k m_bit`. Following Boneh–Shoup Section 8.12
(`m₀, m₁ ∈ M`), the challenger commits to `m_bit` when both chosen words satisfy `S.ValidMessage k`,
and defaults to `m₀` otherwise so that invalid challenge pairs produce identical distributions in
both worlds. -/
noncomputable def CommitmentScheme.hidingForKey {Key : Type}
    (S : CommitmentScheme Key) (k : Key)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : Game := do
  let choice ← ProbComp.eval (adversary.choose n (S.encodeKey k))
  let msg := open Classical in
    if bit ∧ S.ValidMessage k choice.1.1 ∧ S.ValidMessage k choice.1.2 then choice.1.2
    else choice.1.1
  let co ← S.commitDist k msg
  ProbComp.eval (adversary.guess n choice.2 co.1)

/-- If the commitment-string marginal `(S.commitDist k msg).map Prod.fst` is independent of the
message word, then `S.hidingForKey k` produces the exact same output distribution for any two hidden
bits `b₁` and `b₂`, against every (even computationally unbounded) `Encryption.WordAdversary`. -/
theorem CommitmentScheme.hidingForKey_eq_of_map_fst_commitDist_eq {Key : Type}
    (S : CommitmentScheme Key) {k : Key}
    (hk : ∀ msg₁ msg₂ : List Bool,
      (S.commitDist k msg₁).map Prod.fst = (S.commitDist k msg₂).map Prod.fst)
    (adversary : Encryption.WordAdversary) (b₁ b₂ : Bool) (n : ℕ) :
    S.hidingForKey k adversary b₁ n = S.hidingForKey k adversary b₂ n := by
  simp only [CommitmentScheme.hidingForKey, PMF.monad_bind_eq_bind]
  congr 1; funext choice
  have hbind (msg : List Bool) :
      (S.commitDist k msg).bind (fun co => ProbComp.eval (adversary.guess n choice.2 co.1)) =
        ((S.commitDist k msg).map Prod.fst).bind
          (fun c => ProbComp.eval (adversary.guess n choice.2 c)) := by
    rw [PMF.bind_map]
    rfl
  rw [hbind, hbind, hk]

/-- When `(S.commitDist k msg).map Prod.fst` is independent of the message word, the hiding
advantage of any (computationally unbounded) adversary at key `k` between `bit = false` and
`bit = true` is `0`. -/
theorem CommitmentScheme.advantage_hidingForKey_eq_zero {Key : Type}
    (S : CommitmentScheme Key) {k : Key}
    (hk : ∀ msg₁ msg₂ : List Bool,
      (S.commitDist k msg₁).map Prod.fst = (S.commitDist k msg₂).map Prod.fst)
    (adversary : Encryption.WordAdversary) (n : ℕ) :
    Game.advantage (S.hidingForKey k adversary false n)
      (S.hidingForKey k adversary true n) = 0 := by
  rw [S.hidingForKey_eq_of_map_fst_commitDist_eq hk adversary false true n, Game.advantage_self]

/-- The chosen-message hiding experiment ([BonehShoup2023], Section 8.12, p. 344, and
Definition 8.8) under a key distribution `keyDist : ℕ → PMF Key`. -/
noncomputable def CommitmentScheme.hidingGame {Key : Type}
    (S : CommitmentScheme Key) (keyDist : ℕ → PMF Key)
    (adversary : Encryption.WordAdversary) (bit : Bool) (n : ℕ) : Game := do
  let k ← keyDist n
  S.hidingForKey k adversary bit n

/-- Statistical hiding ([BonehShoup2023], Section 8.12, p. 344, and Definition 8.8): every (even
computationally unbounded) `Encryption.WordAdversary` has negligible distinguishing advantage in
`S.hidingGame keyDist`. -/
def CommitmentScheme.StatisticalHiding {Key : Type}
    (S : CommitmentScheme Key) (keyDist : ℕ → PMF Key) : Prop :=
  Game.Indistinguishable
    (fun adversary n => S.hidingGame keyDist adversary false n)
    (fun adversary n => S.hidingGame keyDist adversary true n)
    (fun _ => True)

/-- Computational hiding ([BonehShoup2023], Section 8.12, p. 344, and Definition 8.8): every
uniform strict PPT `Encryption.WordAdversary` has negligible distinguishing advantage in
`S.hidingGame keyDist`. -/
def CommitmentScheme.ComputationalHiding {Key : Type}
    (S : CommitmentScheme Key) (keyDist : ℕ → PMF Key) : Prop :=
  Game.Indistinguishable
    (fun adversary n => S.hidingGame keyDist adversary false n)
    (fun adversary n => S.hidingGame keyDist adversary true n)
    Encryption.WordAdversary.IsPPT

/-- Statistical hiding implies computational hiding against uniform strict PPT adversaries. -/
theorem CommitmentScheme.StatisticalHiding.computationalHiding {Key : Type}
    {S : CommitmentScheme Key} {keyDist : ℕ → PMF Key}
    (h : S.StatisticalHiding keyDist) :
    S.ComputationalHiding keyDist :=
  fun adversary _ => h adversary trivial

/-- Boolean predicate testing whether `(c, (m₀, o₀), (m₁, o₁))` is a valid binding collision under
`S.verify k` ([BonehShoup2023], Section 8.12, p. 344, and Definition 8.8): `m₀ ≠ m₁` and both
openings `(m₀, o₀)` and `(m₁, o₁)` are accepted by `S.verify k` for the commitment string `c`. -/
def CommitmentScheme.isBindingCollision {Key : Type} (S : CommitmentScheme Key) (k : Key)
    (out : List Bool × (List Bool × List Bool) × (List Bool × List Bool)) : Bool :=
  decide (out.2.1.1 ≠ out.2.2.1) &&
    S.verify k out.2.1.1 out.1 out.2.1.2 &&
    S.verify k out.2.2.1 out.1 out.2.2.2

/-- The commitment binding experiment ([BonehShoup2023], Section 8.12, p. 344, and
Definition 8.8): draw `k ← keyDist n`, give `S.encodeKey k` to `adversary`, and accept when the
output `(c, (m₀, o₀), (m₁, o₁))` satisfies `S.isBindingCollision k` (`m₀ ≠ m₁` and both openings
verify under `S.verify k`). -/
noncomputable def CommitmentScheme.bindingGame {Key : Type}
    (S : CommitmentScheme Key) (keyDist : ℕ → PMF Key)
    (adversary : ℕ → List Bool →
      ProbComp (List Bool × (List Bool × List Bool) × (List Bool × List Bool)))
    (n : ℕ) : Game := do
  let k ← keyDist n
  let out ← ProbComp.eval (adversary n (S.encodeKey k))
  return S.isBindingCollision k out

/-- Computational binding ([BonehShoup2023], Section 8.12, p. 344, and Definition 8.8): every
uniform strict PPT adversary has negligible success probability in `S.bindingGame keyDist`. -/
def CommitmentScheme.Binding {Key : Type}
    (S : CommitmentScheme Key) (keyDist : ℕ → PMF Key) : Prop :=
  ∀ adversary : ℕ → List Bool →
      ProbComp (List Bool × (List Bool × List Bool) × (List Bool × List Bool)),
    IsPPTOn (encPair encUnary encBits)
      (encPair encBits (encPair (encPair encBits encBits) (encPair encBits encBits)))
      (fun input => adversary input.1 input.2) →
    Negligible fun n => Game.succProbability (S.bindingGame keyDist adversary n)

end Cslib.Crypto
