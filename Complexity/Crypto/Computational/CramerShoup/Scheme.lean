/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.CollisionResistant
public import Complexity.Crypto.Computational.CramerShoup.ProjectiveHash
public import Complexity.Crypto.Computational.DiffieHellman
public import Complexity.Crypto.Computational.ElGamal
public import Complexity.Crypto.Computational.Encryption.CCA
public import Complexity.Crypto.Game.UntilBad
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Crypto.Game.Statistical
import Complexity.Probability.PMF
import Complexity.Probability.StatisticalDistance
import Complexity.Tactic.PolyTime

/-!
# Multiplicative Cramer–Shoup Encryption Scheme and Adaptive Projective-Hash Rejection

This module formalizes the **Multiplicative Cramer–Shoup public-key encryption scheme**
($\mathcal{E}_{\mathrm{MCS}}$, [Boneh and Shoup, Section 12.5.3, Section 12.7, and Exercise 12.27,
printed pp. 488–493, 501–502, 521–522][BonehShoup2023], over an arbitrary associated-data type
`AD : Type`) over a `PrimeOrderGroupFamily`, proves its algebraic and word-level
decryption correctness and polynomial-time computability certificates, and establishes the
**adaptive Lemma 12.8 projective-hash rejection bound** and **Lemma 12.6 one-time group-mask
challenge blindness** (Games 3 $\to$ 3.5 $\to$ 4 $\to$ 5 of Theorem 12.9, printed pp. 492–493)
against an adaptive `ADCCA2AdversaryOf Msg AD`. Groups are written additively as
`ZMod (F.order d)`-modules (matching `DiscreteLog`, `DiffieHellman`, `ElGamal`, and
`ProjectiveHash`).

## Source Statements ([BonehShoup2023], Sections 12.5.1–12.5.3, 12.7 & Exercise 12.27)

Verbatim from [BonehShoup2023], Section 12.7, Definition 12.7 (printed pp. 501–502):
> **Definition 12.7 (CCA and 1CCA security with associated data).** The definition of CCA
> security for ordinary public-key encryption schemes carries over naturally to AD public-key
> encryption schemes. Attack Game 12.1 is modified as follows. For encryption queries, in
> addition to a pair of messages $(m_{i0}, m_{i1})$, the adversary also submits associated data
> $d_i$, and the challenger computes $c_i \xleftarrow{R} E(pk, m_{ib}, d_i)$. For decryption
> queries, in addition to a ciphertext $\hat{c}_j$, the adversary submits associated data
> $\hat{d}_j$, and the challenger computes $\hat{m}_j \leftarrow D(sk, \hat{c}_j, \hat{d}_j)$.
> The restriction is that the pair $(\hat{c}_j, \hat{d}_j)$ may not be among the pairs
> $(c_1, d_1), (c_2, d_2), \ldots$ corresponding to previous encryption queries. An adversary
> $\mathcal{A}$'s advantage in this game is denoted
> $\text{CCA}^{\text{ad}}\text{adv}[\mathcal{A}, \mathcal{E}]$, and the scheme is said to be CCA
> secure if this advantage is negligible for all efficient adversaries $\mathcal{A}$. If we
> restrict the adversary to a single encryption query, as in Definition 12.2, the advantage is
> denoted $\text{1CCA}^{\text{ad}}\text{adv}[\mathcal{A}, \mathcal{E}]$, and the scheme is said
> to be 1CCA secure if this advantage is negligible for all efficient adversaries $\mathcal{A}$.

Verbatim from [BonehShoup2023], Sections 12.5.1–12.5.2 (Lemma 12.6 in §12.5.1, printed p. 486;
Lemma 12.8 in §12.5.2, printed p. 488):
> **Lemma 12.6.** In Attack Game 12.4, $\Pr[W_0] = \Pr[W_1]$ for all adversaries $\mathcal{A}$.
> …
> **Lemma 12.8.** In Attack Game 12.5, for any adversary $\mathcal{A}$ that outputs at most $Q$
> tuples, the probability that it wins is at most $Q/q$.

Verbatim from [BonehShoup2023], Section 12.5.3 (printed pp. 488–493):
> - the key generation algorithm runs as follows:
>   $$\begin{aligned}
>   G() :=\quad & \alpha \xleftarrow{R} \mathbb{Z}_q,\; u \leftarrow g^\alpha,\;
>     \sigma, \tau \xleftarrow{R} \mathbb{Z}_q,\; h \leftarrow g^\sigma u^\tau \\
>   & \sigma_1, \tau_1, \sigma_2, \tau_2 \xleftarrow{R} \mathbb{Z}_q,\;
>     h_1 \leftarrow g^{\sigma_1} u^{\tau_1},\; h_2 \leftarrow g^{\sigma_2} u^{\tau_2} \\
>   & pk \leftarrow (u, h, h_1, h_2),\;
>     sk \leftarrow (\sigma, \tau, \sigma_1, \tau_1, \sigma_2, \tau_2),\;
>     \text{output } (pk, sk);
>   \end{aligned}$$
> …
> **Game 5.** We again widen the rejection rule at line (5), replacing it with:
> $$(5) \qquad \text{if } \hat{v}^\alpha \ne \hat{w} \text{ or }
>   \mathit{Coll}_{u,v}(\hat{u}, \hat{v}) \text{ or } z' \ne f'(\hat{v}, \hat{w}, \hat{\rho})$$
> So this rule will reject the ciphertext if $(\hat{v}, \hat{w}) \notin L_u$.
> Let $Z_5$ be the event that in Game 5, some decryption query, which would not have triggered the
> rejection rule of Game 4, does trigger the wider rejection rule in Game 5. Clearly, Games 4 and 5
> proceed identically unless event $Z_5$ occurs. By the Difference Lemma, we have
> $$|\Pr[W_4] - \Pr[W_5]| \le \Pr[Z_5]. \quad (12.26)$$
> We will argue that $\Pr[Z_5] \le Q_d / q$. $(12.27)$
> …
> **Game 6.** Everything we did so far was leading to this point, which is the crux of the proof. We
> replace line (2) in Fig. 12.3 with $z \xleftarrow{R} \mathbb{G}$. We claim that
> $\Pr[W_6] = \Pr[W_5]$. $(12.28)$ This follows from Lemma 12.6, and the fact that in processing
> decryption queries in Game 5, we only need to evaluate $f(\hat{v}, \hat{w})$ at points
> $(\hat{v}, \hat{w}) \in L_u$.
> …
> **Remark 12.3 (Group membership verification).** For reasons similar to that discussed in
> Remark 12.1, it is essential that given a ciphertext $(v, w, z', c)$, the decryption algorithm for
> $\mathcal{E}_{\mathrm{CS}}$ verifies that $v$ and $w$ are in $\mathbb{G}$. It is not necessary to
> explicitly check that $z'$ is in $\mathbb{G}$, since the check that
> $v^{\sigma_1 + \rho \sigma_2} w^{\tau_1 + \rho \tau_2} = z'$ implies that $z'$ is in $\mathbb{G}$.

Verbatim from [BonehShoup2023], Exercise 12.27 (printed pp. 521–522):
> **12.27 (Multiplicative Cramer-Shoup encryption).** Consider the following multiplicative version
> of the Cramer-Shoup encryption scheme (presented in Section 12.5) that supports associated data
> (see Section 12.7) coming from a set $\mathcal{D}$. Let $\mathbb{G}$ be a cyclic group of prime
> order $q$ with generator $g \in \mathbb{G}$. Let
> $H' : \mathbb{G}^3 \times \mathcal{D} \to \mathbb{Z}_q$ be a hash function. The encryption scheme
> $\mathcal{E}_{\mathrm{MCS}} = (G, E, D)$ is defined over $(\mathbb{G}, \mathcal{D}, \mathbb{G}^4)$
> as follows. Key generation is exactly as in $\mathcal{E}_{\mathrm{CS}}$. For a given public key
> $pk = (u, h, h_1, h_2) \in \mathbb{G}^4$ message $m \in \mathbb{G}$, and associated data
> $d \in \mathcal{D}$, the encryption algorithm runs as follows:
> $$E(pk, m, d) := \beta \xleftarrow{R} \mathbb{Z}_q,\; v \leftarrow g^\beta,\;
>   w \leftarrow u^\beta,\; e \leftarrow h^\beta \cdot m,\;
>   \rho \leftarrow H'(v, w, e, d),\; z' \leftarrow (h_1 h_2^\rho)^\beta,\;
>   \text{output } (v, w, e, z').$$
> For a given secret key
> $sk = (\sigma, \tau, \sigma_1, \tau_1, \sigma_2, \tau_2) \in \mathbb{Z}_q^6$ and a ciphertext
> $(v, w, e, z') \in \mathbb{G}^4$, and associated data $d \in \mathcal{D}$, the decryption
> algorithm runs as follows:
> $$D(sk, (v, w, e, z', d)) := \rho \leftarrow H'(v, w, e, d);\;
>   \text{if } v^{\sigma_1 + \rho \sigma_2} w^{\tau_1 + \rho \tau_2} = z'
>   \text{ then output } e / (v^\sigma w^\tau) \text{ else output reject}.$$
> Show that $\mathcal{E}_{\mathrm{MCS}}$ is CCA secure, provided $H'$ is collision resistant and the
> DDH assumption holds for $\mathbb{G}$.

## Existing Notions Considered

* `Cslib.Crypto.PrimeOrderGroupFamily` (`DiffieHellman.lean`) and `ElGamal` (`ElGamal.lean`):
  reused for group descriptions, carriers, generators, encodings, and word-level group operations.
* `Cslib.Crypto.ProjectiveHash`
  (`Complexity/Crypto/Computational/CramerShoup/ProjectiveHash.lean`): reused for `projHash`,
  `projHashAux`, `projHash2`, `projHash2Aux`, fiber identities, `projHashFiberEquiv`,
  `projHash2QueryFiberEquiv`, and `uniform_projHash_fiber_add`.
* `Cslib.Crypto.Encryption.CCA2AdversaryOf`
  (`Complexity/Crypto/Computational/Encryption/CCA.lean`) and
  `Cslib.Crypto.isCollisionFor` (`CollisionResistant.lean`): reused for adaptive 1CCA adversaries
  and Phase 2 hash collisions in `ZMod (F.order d)`.
* `Cslib.Crypto.Game` (`Game.lean`, `Complexity/Crypto/Game/UntilBad.lean`):
  reused for `runStatelessOracle`,
  `advantage_runStatelessOracle_bind_le`, `bind_runStatelessOracle_comm`,
  `advantage_runStatelessOracle_le_of_support`, `advantage_bind_le_nnreal`,
  `advantage_bind_le_of_support`, `advantage_bind_comm`, and
  `advantage_uniform_bind_of_eq_of_ne`.

## Main definitions and results

* `cramerShoupHashMod`, `cramerShoupPublicKey`, `cramerShoupEncrypt`, `cramerShoupDecrypt`,
  `encodeCramerShoupPublicKey`, `encodeCramerShoupEncrypt`, `encodeCramerShoupChallenge`,
  `decodeCramerShoup`: algebraic and word-level Multiplicative Cramer–Shoup operations.
* `cramerShoupDecrypt_cramerShoupEncrypt`, `decodeCramerShoup_encode`,
  `decodeCramerShoup_cramerShoupEncrypt`, `computableInPolyTime_encodeCramerShoupPublicKey`,
  `computableInPolyTime_encodeCramerShoupEncrypt`,
  `computableInPolyTime_encodeCramerShoupChallenge`, `computableInPolyTime_decodeCramerShoup`:
  decryption correctness and polynomial-time computability certificates.
* `cramerShoupGame3`, `cramerShoupGame3Half`, `cramerShoupGame4`, `cramerShoupGame5`,
  `advantage_cramerShoupGame3_game3Half_le`, `advantage_cramerShoupGame3Half_game4_le`,
  `advantage_cramerShoupGame3_game4_le`, `cramerShoupGame5_false_eq_true`,
  `advantage_cramerShoupGame4_game5_le`: the adaptive Lemma 12.8 projective-hash rejection bounds
  (`Q₁ / m`, `Q₂ / m`, `(Q₁ + Q₂) / m`) and Lemma 12.6 one-time group-mask bound (`1 / m`).
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- A single-challenge adaptive chosen-ciphertext adversary with associated data
(1CCA with associated data, [BonehShoup2023], Section 12.7, Definition 12.7, printed
pp. 501–502) over message space `Msg` and associated-data space `AD`.
Both stages have access to the single-channel decryption oracle (`Operation = Unit`), where each
decryption query is a framed pair `encPair encBits encBits (ct, ad)`. -/
structure ADCCA2AdversaryOf (Msg AD : Type) where
  /-- Phase 1: given the unary security parameter `n` and encoded public key `pk`, make decryption
  queries, choose two challenge messages `(m₀, m₁) : Msg × Msg` together with challenge associated
  data `ad : AD`, and save a state word. -/
  choose : ℕ → List Bool → WordOracleComp Unit (((Msg × Msg) × AD) × List Bool)
  /-- Phase 2: given `n`, the saved state word, and the challenge ciphertext `ct`, make decryption
  queries (where querying `(ct, encAD ad)` is rejected) and output a guess bit. -/
  guess : ℕ → List Bool → List Bool → WordOracleComp Unit Bool

/-- Uniform strict oracle PPT admissibility of both stages of an `ADCCA2AdversaryOf Msg AD` with
respect to message encoding `encMsg` and associated-data encoding `encAD`. -/
structure ADCCA2AdversaryOf.IsPPT {Msg AD : Type} (encMsg : Msg ↪ List Bool)
    (encAD : AD ↪ List Bool) (adversary : ADCCA2AdversaryOf Msg AD) : Prop where
  /-- Phase 1 message and associated-data selection is uniform strict oracle PPT on `(n, pk)`. -/
  choose : IsOraclePPT (Operation := Unit)
    (encPair (encPair (encPair encMsg encMsg) encAD) encBits) adversary.choose
  /-- Phase 2 guessing is uniform strict oracle PPT on `(n, state, ct)`. -/
  guess : IsOraclePPTOn (Operation := Unit) (encPair encUnary (encPair encBits encBits)) encBool
    (fun p => adversary.guess p.1 p.2.1 p.2.2)

/-- Per-stage decryption-query bound `(Q₁ n, Q₂ n)` for an `ADCCA2AdversaryOf Msg AD`. -/
def ADCCA2AdversaryOf.IsQueryBounded {Msg AD : Type} (adversary : ADCCA2AdversaryOf Msg AD)
    (Q₁ Q₂ : ℕ → ℕ) : Prop :=
  (∀ n pk, (adversary.choose n pk).IsQueryBounded (Q₁ n)) ∧
  (∀ n state ct, (adversary.guess n state ct).IsQueryBounded (Q₂ n))

/-- Every strict oracle PPT `ADCCA2AdversaryOf Msg AD` has polynomial bounds on its Phase 1
queries, Phase 2 queries, and saved-state length in terms of `(n, pk.length, ct.length)`. -/
theorem ADCCA2AdversaryOf.IsPPT.query_bounds {Msg AD : Type} {encMsg : Msg ↪ List Bool}
    {encAD : AD ↪ List Bool} {adversary : ADCCA2AdversaryOf Msg AD}
    (hA : adversary.IsPPT encMsg encAD) :
    ∃ c₁ d₁ c₂ d₂ cs ds : ℕ,
      (∀ n pk, (adversary.choose n pk).IsQueryBounded (c₁ * (n + pk.length + 2) ^ d₁)) ∧
      (∀ n state ct,
        (adversary.guess n state ct).IsQueryBounded
          (c₂ * (n + state.length + ct.length + 2) ^ d₂)) ∧
      (∀ n pk (State : Type)
        (oracle : Unit × List Bool → StateT State PMF (List Bool)) s s' choice,
        (choice, s') ∈ ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifOracle m)) oracle)
            (adversary.choose n pk)).run s).support →
        choice.2.length ≤ cs * (n + pk.length + 2) ^ ds) := by
  obtain ⟨c₁, d₁, hchoose⟩ := hA.choose.query_bounds
  obtain ⟨c₂, d₂, hguess⟩ := hA.guess.query_bounds
  obtain ⟨cs, ds, hlen⟩ := hA.choose.on.length_le
  refine ⟨c₁, d₁, c₂ * 4 ^ d₂, d₂, cs * 2 ^ ds, ds, fun n pk => (hchoose n pk).1,
    fun n state ct => ?_, fun n pk State oracle s s' choice hmem => ?_⟩
  · have hsize : (encPair encUnary (encPair encBits encBits) (n, state, ct)).length + 1 ≤
        4 * (n + state.length + ct.length + 2) := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
      lia
    have hpoly := Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left hsize d₂)
    rw [Nat.mul_pow, ← Nat.mul_assoc] at hpoly
    exact (hguess (n, state, ct)).1.mono hpoly
  · have hbound := hlen (n, pk) State oracle s s' choice hmem
    have hstate : choice.2.length ≤
        (encPair (encPair (encPair encMsg encMsg) encAD) encBits choice).length := by
      simp only [length_encPair, encBits_apply]
      lia
    have hsize : (encPair encUnary encBits (n, pk)).length + 1 ≤
        2 * (n + pk.length + 2) := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
      lia
    have hpoly := Nat.mul_le_mul_left cs (Nat.pow_le_pow_left hsize ds)
    rw [Nat.mul_pow, ← Nat.mul_assoc] at hpoly
    exact (hstate.trans hbound).trans hpoly

/-- Single-bit 1CCA adversary with associated data `AD` (`Msg = Bool`). -/
abbrev ADCCA2Adversary (AD : Type) : Type := ADCCA2AdversaryOf Bool AD

/-- Native uniform strict oracle PPT admissibility for a bit 1CCA adversary with associated data. -/
abbrev ADCCA2Adversary.IsPPT {AD : Type} (encAD : AD ↪ List Bool)
    (adversary : ADCCA2Adversary AD) : Prop :=
  ADCCA2AdversaryOf.IsPPT encBool encAD adversary

/-- Bit-string 1CCA adversary with associated data `AD` (`Msg = List Bool`). -/
abbrev WordADCCA2Adversary (AD : Type) : Type := ADCCA2AdversaryOf (List Bool) AD

/-- Native uniform strict oracle PPT admissibility for a bit-string 1CCA adversary with associated
data. -/
abbrev WordADCCA2Adversary.IsPPT {AD : Type} (encAD : AD ↪ List Bool)
    (adversary : WordADCCA2Adversary AD) : Prop :=
  ADCCA2AdversaryOf.IsPPT encBits encAD adversary

/-- Embed an associated-data-free `CCA2AdversaryOf Msg` as an `ADCCA2AdversaryOf Msg Unit` with
trivial associated data `() : Unit`. -/
def CCA2AdversaryOf.toADUnit {Msg : Type} (adversary : CCA2AdversaryOf Msg) :
    ADCCA2AdversaryOf Msg Unit where
  choose n pk := (fun p => ((p.1, ()), p.2)) <$> adversary.choose n pk
  guess := adversary.guess

/-- `CCA2AdversaryOf.toADUnit` preserves uniform strict oracle PPT admissibility. -/
theorem CCA2AdversaryOf.IsPPT.toADUnit {Msg : Type} {encMsg : Msg ↪ List Bool}
    {adversary : CCA2AdversaryOf Msg} (hA : adversary.IsPPT encMsg) :
    adversary.toADUnit.IsPPT encMsg (encFinEnum Unit) where
  choose := (hA.choose.on.map (by fun_prop)).isOraclePPT
  guess := hA.guess

/-- `CCA2AdversaryOf.toADUnit` preserves per-stage decryption-query bounds. -/
theorem CCA2AdversaryOf.IsQueryBounded.toADUnit {Msg : Type} {adversary : CCA2AdversaryOf Msg}
    {Q₁ Q₂ : ℕ → ℕ} (hQ : adversary.IsQueryBounded Q₁ Q₂) :
    adversary.toADUnit.IsQueryBounded Q₁ Q₂ :=
  ⟨fun n pk => by
    simp only [CCA2AdversaryOf.toADUnit, ProbOracleComp.IsQueryBounded,
      OracleComp.isCostBounded_map_iff]
    exact hQ.1 n pk,
   hQ.2⟩

/-- Phase 1 decryption oracle with associated data ([BonehShoup2023], Section 12.7,
Definition 12.7, printed pp. 501–502): unpack `request.2` into ciphertext `unframe request.2` and
associated data `dropFrame request.2`, and reply with
`encOption encOut (decrypt n sk (unframe request.2) (dropFrame request.2))`. -/
def cca2ADPhase1Oracle {Out : Type} (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → List Bool → Option Out)
    (n : ℕ) (sk : List Bool) (request : Unit × List Bool) :
    StateT Unit ProbComp (List Bool) :=
  fun s => pure (encOption encOut (decrypt n sk (unframe request.2) (dropFrame request.2)), s)

/-- Phase 2 decryption oracle with associated data ([BonehShoup2023], Section 12.7,
Definition 12.7, printed pp. 501–502): unpack `request.2` into `(unframe request.2,
dropFrame request.2)`, reject the challenge pair `(ct, ad)` with `[]` (`encOption encOut none`),
and answer all other queries with
`encOption encOut (decrypt n sk (unframe request.2) (dropFrame request.2))`. -/
def cca2ADPhase2Oracle {Out : Type} (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → List Bool → Option Out)
    (n : ℕ) (sk ct ad : List Bool) (request : Unit × List Bool) :
    StateT Unit ProbComp (List Bool) :=
  fun s =>
    if (unframe request.2 == ct) && (dropFrame request.2 == ad) then
      pure ([], s)
    else
      pure (encOption encOut (decrypt n sk (unframe request.2) (dropFrame request.2)), s)

/-- Single-challenge 1CCA experiment with associated data ([BonehShoup2023], Section 12.7,
Definition 12.7, printed pp. 501–502) and challenge-pair admissibility predicate
`valid : ℕ → List Bool → Msg → Msg → Bool`: sample `(pk, sk) ← keyGen n`, run Phase 1 (`choose`)
against `cca2ADPhase1Oracle`, check `valid n pk m₀ m₁`, encrypt `(if bit then m₁ else m₀)` with
associated data `ad` to obtain `ct`, and run Phase 2 (`guess`) against `cca2ADPhase2Oracle`
rejecting `(ct, encAD ad)`. -/
noncomputable def cca2ADGameOn {Msg AD Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encAD : AD ↪ List Bool) (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → AD → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → List Bool → Option Out)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choiceOut ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2ADPhase1Oracle encOut decrypt n keys.2))
    (adversary.choose n keys.1)).run ()
  let choice := choiceOut.1
  if valid n keys.1 choice.1.1.1 choice.1.1.2 then
    let ct ← encrypt n keys.1 (if bit then choice.1.1.2 else choice.1.1.1) choice.1.2
    let guessOut ← (OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2ADPhase2Oracle encOut decrypt n keys.2 ct (encAD choice.1.2)))
      (adversary.guess n choice.2 ct)).run ()
    return guessOut.1
  else
    return false

/-- Unconditional single-challenge 1CCA experiment with associated data
(`valid := fun _ _ _ _ => true`). -/
noncomputable abbrev cca2ADGame {Msg AD Out : Type}
    (encAD : AD ↪ List Bool) (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → AD → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → List Bool → Option Out)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  cca2ADGameOn (fun _ _ _ _ => true) encAD encOut keyGen encrypt decrypt adversary bit n

/-- Single-challenge 1CCA security with associated data ([BonehShoup2023], Section 12.7,
Definition 12.7, printed pp. 501–502) with respect to challenge-pair admissibility predicate
`valid`, message encoding `encMsg`, associated-data encoding `encAD`, and decryption output
encoding `encOut`. -/
def INDCCA2ADOn {Msg AD Out : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encMsg : Msg ↪ List Bool) (encAD : AD ↪ List Bool) (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → AD → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → List Bool → Option Out) : Prop :=
  Game.Indistinguishable
    (fun adversary n =>
      ProbComp.eval (cca2ADGameOn valid encAD encOut keyGen encrypt decrypt adversary false n))
    (fun adversary n =>
      ProbComp.eval (cca2ADGameOn valid encAD encOut keyGen encrypt decrypt adversary true n))
    (ADCCA2AdversaryOf.IsPPT encMsg encAD)

/-- Single-challenge 1CCA security with associated data over a fixed-length message space `Msg`
(`valid := fun _ _ _ _ => true`). -/
abbrev INDCCA2ADOf {Msg AD Out : Type} (encMsg : Msg ↪ List Bool) (encAD : AD ↪ List Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → AD → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → List Bool → Option Out) : Prop :=
  INDCCA2ADOn (fun _ _ _ _ => true) encMsg encAD encOut keyGen encrypt decrypt

/-- Single-challenge 1CCA security with associated data for bit encryption (`Msg = Bool`,
`Out = Bool`). -/
abbrev INDCCA2AD {AD : Type} (encAD : AD ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → AD → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → List Bool → Option Bool) : Prop :=
  INDCCA2ADOf encBool encAD encBool keyGen encrypt decrypt

/-- Single-challenge 1CCA security with associated data for bit-string encryption
(`Msg = List Bool`, `Out = List Bool`) under Attack Game 12.1's equal-length challenge rule
`m₀.length == m₁.length`. -/
abbrev WordINDCCA2AD {AD : Type} (encAD : AD ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → AD → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → List Bool → Option (List Bool)) : Prop :=
  INDCCA2ADOn (fun _ _ m₀ m₁ => m₀.length == m₁.length) encBits encAD encBits keyGen encrypt decrypt

end Cslib.Crypto.Encryption

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM ProjectiveHash Encryption Game
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)
/-! ### Framing for 3-tuples and 4-tuples of bit strings -/

/-- Canonical framing of a 3-tuple of bit strings. -/
def encBits3 : (List Bool × List Bool × List Bool) ↪ List Bool :=
  encPair encBits (encPair encBits encBits)

/-- Unpack a canonically framed 3-tuple of bit strings. -/
def decodeBits3 (w : List Bool) : List Bool × List Bool × List Bool :=
  let r1 := dropFrame w
  (unframe w, unframe r1, dropFrame r1)

@[simp]
theorem decodeBits3_encBits3 (p : List Bool × List Bool × List Bool) :
    decodeBits3 (encBits3 p) = p := by
  rcases p with ⟨a, b, c⟩
  simp [encBits3, decodeBits3, encPair_apply, unframe_frame_append, dropFrame_frame_append]

/-- Canonical framing of a 4-tuple of bit strings. -/
def encBits4 : (List Bool × List Bool × List Bool × List Bool) ↪ List Bool :=
  encPair encBits (encPair encBits (encPair encBits encBits))

/-- Unpack a canonically framed 4-tuple of bit strings. -/
def decodeBits4 (w : List Bool) : List Bool × List Bool × List Bool × List Bool :=
  let r1 := dropFrame w
  let r2 := dropFrame r1
  (unframe w, unframe r1, unframe r2, dropFrame r2)

@[simp]
theorem decodeBits4_encBits4 (p : List Bool × List Bool × List Bool × List Bool) :
    decodeBits4 (encBits4 p) = p := by
  rcases p with ⟨a, b, c, d⟩
  simp [encBits4, decodeBits4, encPair_apply, unframe_frame_append, dropFrame_frame_append]

/-- Extract the framed `(v, w, e, ad)` 4-tuple from an encoded 4-tuple ciphertext `ct` and
associated-data bit string `ad`. -/
def extractCramerShoupTuple (ct ad : List Bool) : List Bool :=
  let parts := decodeBits4 ct
  encBits4 (parts.1, parts.2.1, parts.2.2.1, ad)

@[simp]
theorem extractCramerShoupTuple_encBits4 (v w e z' ad : List Bool) :
    extractCramerShoupTuple (encBits4 (v, w, e, z')) ad = encBits4 (v, w, e, ad) := by
  simp [extractCramerShoupTuple]

/-- Unpack a decryption-oracle query `req` into `(ct, ad)`: when `hasAD = true`, unpack the framed
pair `(unframe req, dropFrame req)`; when `hasAD = false`, treat `req` as `ct` with empty associated
data `[]`. -/
def splitCramerShoupQuery (hasAD : Bool) (req : List Bool) : List Bool × List Bool :=
  if hasAD then (unframe req, dropFrame req) else (req, [])

@[local fun_prop]
private theorem computableTidilyInPolyTime_decodeBits4 :
    ComputableTidilyInPolyTime decodeBits4 encBits
      (encPair encBits (encPair encBits (encPair encBits encBits))) := by
  unfold decodeBits4; fun_prop

@[local fun_prop]
private theorem computableTidilyInPolyTime_extractCramerShoupTuple :
    ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => extractCramerShoupTuple p.1 p.2)
      (encPair encBits encBits) encBits := by
  have h := computableTidilyInPolyTime_decodeBits4.comp
    (ComputableTidilyInPolyTime.fst encBits encBits)
  have had := ComputableTidilyInPolyTime.snd encBits encBits
  exact (ComputableTidilyInPolyTime.encode encBits4).comp
    (h.fst'.prod (h.snd'.fst'.prod (h.snd'.snd'.fst'.prod had)))

@[local fun_prop]
private theorem computableTidilyInPolyTime_splitCramerShoupQuery (hasAD : Bool) :
    ComputableTidilyInPolyTime (splitCramerShoupQuery hasAD) encBits
      (encPair encBits encBits) := by
  cases hasAD
  · change ComputableTidilyInPolyTime (fun req : List Bool => (req, ([] : List Bool)))
      encBits (encPair encBits encBits)
    fun_prop
  · change ComputableTidilyInPolyTime (fun req : List Bool => (unframe req, dropFrame req))
      encBits (encPair encBits encBits)
    fun_prop

/-- `decodeBits4` is computable in polynomial time. -/
theorem computableInPolyTime_decodeBits4 :
    ComputableInPolyTime decodeBits4 encBits
      (encPair encBits (encPair encBits (encPair encBits encBits))) :=
  .of_tidy computableTidilyInPolyTime_decodeBits4

/-- `extractCramerShoupTuple` is computable in polynomial time. -/
theorem computableInPolyTime_extractCramerShoupTuple :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => extractCramerShoupTuple p.1 p.2)
      (encPair encBits encBits) encBits :=
  .of_tidy computableTidilyInPolyTime_extractCramerShoupTuple

/-- `splitCramerShoupQuery` is computable in polynomial time. -/
theorem computableInPolyTime_splitCramerShoupQuery (hasAD : Bool) :
    ComputableInPolyTime (splitCramerShoupQuery hasAD) encBits (encPair encBits encBits) :=
  .of_tidy (computableTidilyInPolyTime_splitCramerShoupQuery hasAD)

/-! ### Algebraic Multiplicative Cramer–Shoup ([BonehShoup2023], Section 12.5.3 & Exercise 12.27) -/

/-- The $\mathbb{Z}_q$-valued hash family $H'_d(x) = (\mathrm{ofBits}(H(d, x)) : \mathbb{Z}_q)$
induced by a word-level hash function `H : F.Desc × List Bool → List Bool`
([BonehShoup2023], Exercise 12.27, printed p. 521). -/
def cramerShoupHashMod (H : F.Desc × List Bool → List Bool) (d : F.Desc) (x : List Bool) :
    ZMod (F.order d) :=
  (ofBits (H (d, x)) : ZMod (F.order d))

/-- Encode a triple of group elements `(v, w, e) : F.Carrier d × F.Carrier d × F.Carrier d` together
with an encoded associated-data word `ad : List Bool` as a framed 4-tuple bit string. -/
def encodeCramerShoupTuple (d : F.Desc) (v w e : F.Carrier d) (ad : List Bool) : List Bool :=
  encBits4 (F.encode d v, F.encode d w, F.encode d e, ad)

/-- Algebraic Cramer–Shoup public key `pk = (u, h, h₁, h₂) ∈ G⁴` generated from secret exponents
`(α, σ, τ, σ₁, τ₁, σ₂, τ₂)` ([BonehShoup2023], Section 12.5.3, printed p. 489). -/
def cramerShoupPublicKey (d : F.Desc) (α σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) :
    F.Carrier d × F.Carrier d × F.Carrier d × F.Carrier d :=
  let u := α • F.generator d; let h := projHashAux F d σ τ u
  let h₁₂ := projHash2Aux F d σ₁ τ₁ σ₂ τ₂ u
  (u, h, h₁₂.1, h₁₂.2)

/-- Algebraic Multiplicative Cramer–Shoup encryption $E(pk, m, ad; \beta) = (v, w, e, z')$
([BonehShoup2023], Exercise 12.27, printed p. 521). -/
def cramerShoupEncrypt (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (pk : F.Carrier d × F.Carrier d × F.Carrier d × F.Carrier d)
    (m : F.Carrier d) (ad : List Bool) (β : ZMod (F.order d)) :
    F.Carrier d × F.Carrier d × F.Carrier d × F.Carrier d :=
  let v := β • F.generator d; let w := β • pk.1; let e := β • pk.2.1 + m
  let ρ := F.cramerShoupHashMod H d (F.encodeCramerShoupTuple d v w e ad)
  (v, w, e, β • (pk.2.2.1 + ρ • pk.2.2.2))

/-- Under a genuine public key `cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂`, the components of
`cramerShoupEncrypt` coincide with projective hash evaluation (`Game 0 = Game 1`,
[BonehShoup2023], Section 12.5.3, equation (12.21), printed p. 490). -/
theorem cramerShoupEncrypt_cramerShoupPublicKey (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α σ τ σ₁ τ₁ σ₂ τ₂ β : ZMod (F.order d)) (m : F.Carrier d) (ad : List Bool) :
    F.cramerShoupEncrypt H d (F.cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂) m ad β =
      let v := β • F.generator d
      let w := (α * β) • F.generator d
      let e := projHash F d σ τ v w + m
      let ρ := F.cramerShoupHashMod H d (F.encodeCramerShoupTuple d v w e ad)
      let z' := projHash2 F d σ₁ τ₁ σ₂ τ₂ ρ v w
      (v, w, e, z') := by
  dsimp only [cramerShoupEncrypt, cramerShoupPublicKey]
  have hw : β • (α • F.generator d) = (α * β) • F.generator d := by rw [smul_smul, mul_comm]
  have he : projHash F d σ τ (β • F.generator d) ((α * β) • F.generator d) =
      β • projHashAux F d σ τ (α • F.generator d) := by rw [← hw, projHash_smul_generator]
  have hz' (ρ : ZMod (F.order d)) :
      projHash2 F d σ₁ τ₁ σ₂ τ₂ ρ (β • F.generator d) ((α * β) • F.generator d) =
        β • ((projHash2Aux F d σ₁ τ₁ σ₂ τ₂ (α • F.generator d)).1 +
          ρ • (projHash2Aux F d σ₁ τ₁ σ₂ τ₂ (α • F.generator d)).2) := by
    rw [← hw, projHash2_smul_generator]
  rw [hw, ← he, ← hz']

/-- Algebraic Multiplicative Cramer–Shoup decryption $D(sk, (v, w, e, z'), ad)$
([BonehShoup2023], Exercise 12.27, printed p. 522): check
$f'_{\sigma_1,\tau_1,\sigma_2,\tau_2}(v, w, \rho) = z'$ where $\rho = H'(v, w, e, ad)$, and if so
output `some (e - f_{σ,τ}(v, w))`. -/
def cramerShoupDecrypt [∀ d, DecidableEq (F.Carrier d)]
    (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (sk : (ZMod (F.order d) × ZMod (F.order d)) ×
      ((ZMod (F.order d) × ZMod (F.order d)) × (ZMod (F.order d) × ZMod (F.order d))))
    (ct : F.Carrier d × F.Carrier d × F.Carrier d × F.Carrier d) (ad : List Bool) :
    Option (F.Carrier d) :=
  let ρ := F.cramerShoupHashMod H d (F.encodeCramerShoupTuple d ct.1 ct.2.1 ct.2.2.1 ad)
  if projHash2 F d sk.2.1.1 sk.2.1.2 sk.2.2.1 sk.2.2.2 ρ ct.1 ct.2.1 = ct.2.2.2 then
    some (ct.2.2.1 - projHash F d sk.1.1 sk.1.2 ct.1 ct.2.1)
  else
    none

/-- **Algebraic Cramer–Shoup decryption correctness** ([BonehShoup2023], Section 12.5.3 &
Exercise 12.27, printed pp. 489, 521–522): decrypting an honest encryption under
`cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂` with `((σ, τ), ((σ₁, τ₁), (σ₂, τ₂)))` and the same
associated data `ad` recovers `some m`. -/
@[simp]
theorem cramerShoupDecrypt_cramerShoupEncrypt [∀ d, DecidableEq (F.Carrier d)]
    (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α σ τ σ₁ τ₁ σ₂ τ₂ β : ZMod (F.order d)) (m : F.Carrier d) (ad : List Bool) :
    F.cramerShoupDecrypt H d ((σ, τ), ((σ₁, τ₁), (σ₂, τ₂)))
      (F.cramerShoupEncrypt H d (F.cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂) m ad β) ad =
      some m := by
  rw [F.cramerShoupEncrypt_cramerShoupPublicKey]; simp [cramerShoupDecrypt]

/-! ### Word-level polynomial-time Cramer–Shoup operations -/

/-- Encoding of a 6-tuple secret key `((s, t), ((s₁, t₁), (s₂, t₂)))` of natural-number
exponents. -/
abbrev encCramerShoupSK : ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) ↪ List Bool :=
  encPair (encPair encNat encNat) (encPair (encPair encNat encNat) (encPair encNat encNat))

/-- Encoded group negation `-x = (q - 1) • x` computed via `F.smul (d, F.order d - 1, z)`. -/
def encodeGroupNeg (d : F.Desc) (z : List Bool) : List Bool :=
  F.smul (d, F.order d - 1, z)

@[simp]
theorem encodeGroupNeg_encode (d : F.Desc) (x : F.Carrier d) :
    F.encodeGroupNeg d (F.encode d x) = F.encode d (-x) := by
  have hneg : ((F.order d - 1 : ℕ) : ZMod (F.order d)) = -1 := by
    rw [Nat.cast_sub (F.prime_order d).pos, ZMod.natCast_self, Nat.cast_one, zero_sub]
  simp only [encodeGroupNeg, F.smul_encode, hneg, neg_one_smul]

/-- Word-level universal projective hash `f_{s,t}(v, w) = s • v + t • w`. -/
def encodeProjHash (d : F.Desc) (s t : ℕ) (v w : List Bool) : List Bool :=
  F.add (d, F.smul (d, s, v), F.smul (d, t, w))

@[simp]
theorem encodeProjHash_encode (d : F.Desc) (s t : ℕ) (v w : F.Carrier d) :
    F.encodeProjHash d s t (F.encode d v) (F.encode d w) =
      F.encode d (projHash F d (s : ZMod (F.order d)) (t : ZMod (F.order d)) v w) := by
  simp only [encodeProjHash, F.smul_encode, F.add_encode, projHash]

/-- Word-level public projection `h = f_{s,t}(g, u) = s • g + t • u`. -/
def encodeProjHashAux (d : F.Desc) (s t : ℕ) (u : List Bool) : List Bool :=
  F.encodeProjHash d s t (F.encode d (F.generator d)) u

@[simp]
theorem encodeProjHashAux_encode (d : F.Desc) (s t : ℕ) (u : F.Carrier d) :
    F.encodeProjHashAux d s t (F.encode d u) =
      F.encode d (projHashAux F d (s : ZMod (F.order d)) (t : ZMod (F.order d)) u) := by
  simp only [encodeProjHashAux, encodeProjHash_encode, projHashAux]

/-- Word-level $\text{universal}_2$ projective hash
`f'_{s₁,t₁,s₂,t₂}(v, w, r) = f_{s₁,t₁}(v, w) + r • f_{s₂,t₂}(v, w)`. -/
def encodeProjHash2 (d : F.Desc) (s₁ t₁ s₂ t₂ r : ℕ) (v w : List Bool) : List Bool :=
  F.add (d, F.encodeProjHash d s₁ t₁ v w, F.smul (d, r, F.encodeProjHash d s₂ t₂ v w))

@[simp]
theorem encodeProjHash2_encode (d : F.Desc) (s₁ t₁ s₂ t₂ r : ℕ) (v w : F.Carrier d) :
    F.encodeProjHash2 d s₁ t₁ s₂ t₂ r (F.encode d v) (F.encode d w) =
      F.encode d (projHash2 F d (s₁ : ZMod (F.order d)) (t₁ : ZMod (F.order d))
        (s₂ : ZMod (F.order d)) (t₂ : ZMod (F.order d)) (r : ZMod (F.order d)) v w) := by
  simp only [encodeProjHash2, encodeProjHash_encode, F.smul_encode, F.add_encode,
    projHash2_eq_projHash_add]

/-- Encode a 4-tuple of group elements `(u, h, h₁, h₂)` together with `d : F.Desc` as the public
key word presented to a 1CCA adversary. -/
def encodeCramerShoupPublicKeyValues (d : F.Desc)
    (pk : F.Carrier d × F.Carrier d × F.Carrier d × F.Carrier d) : List Bool :=
  encPair F.encDesc encBits4
    (d, (F.encode d pk.1, F.encode d pk.2.1, F.encode d pk.2.2.1, F.encode d pk.2.2.2))

/-- Word-level Cramer–Shoup public key generation from `d : F.Desc`, an encoded
`u = encode (α • g)`, and natural-number secret exponents
`sk = ((s, t), ((s₁, t₁), (s₂, t₂)))`. -/
def encodeCramerShoupPublicKey (d : F.Desc) (u : List Bool)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) : List Bool :=
  encPair F.encDesc encBits4 (d, (u, F.encodeProjHashAux d sk.1.1 sk.1.2 u,
    F.encodeProjHashAux d sk.2.1.1 sk.2.1.2 u, F.encodeProjHashAux d sk.2.2.1 sk.2.2.2 u))

@[simp]
theorem encodeCramerShoupPublicKey_encode (d : F.Desc) (α : ZMod (F.order d))
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d)) sk =
      F.encodeCramerShoupPublicKeyValues d
        (F.cramerShoupPublicKey d α sk.1.1 sk.1.2 sk.2.1.1 sk.2.1.2 sk.2.2.1 sk.2.2.2) := by
  simp only [encodeCramerShoupPublicKey, encodeCramerShoupPublicKeyValues,
    encodeProjHashAux_encode, cramerShoupPublicKey, projHash2Aux]

/-- Encode a 4-tuple ciphertext `(v, w, e, z') : (F.Carrier d)⁴` as a canonically framed bit
string. -/
def encodeCramerShoupCiphertext (d : F.Desc)
    (ct : F.Carrier d × F.Carrier d × F.Carrier d × F.Carrier d) : List Bool :=
  encBits4 (F.encode d ct.1, F.encode d ct.2.1, F.encode d ct.2.2.1, F.encode d ct.2.2.2)

/-- Word-level Cramer–Shoup encryption from the public key `(u, h, h₁, h₂)`, encoded message `m`,
encoded associated data `ad`, and randomness `b : ℕ`. -/
def encodeCramerShoupEncrypt (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (pk : List Bool × List Bool × List Bool × List Bool) (m ad : List Bool) (b : ℕ) : List Bool :=
  let v := F.smul (d, b, F.encode d (F.generator d)); let w := F.smul (d, b, pk.1)
  let e := F.add (d, F.smul (d, b, pk.2.1), m)
  let r := ofBits (H (d, encBits4 (v, w, e, ad)))
  encBits4 (v, w, e, F.smul (d, b, F.add (d, pk.2.2.1, F.smul (d, r, pk.2.2.2))))

@[simp]
theorem encodeCramerShoupEncrypt_encode (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (pk : F.Carrier d × F.Carrier d × F.Carrier d × F.Carrier d)
    (m : F.Carrier d) (ad : List Bool) (b : ℕ) :
    F.encodeCramerShoupEncrypt H d
      (F.encode d pk.1, F.encode d pk.2.1, F.encode d pk.2.2.1, F.encode d pk.2.2.2)
      (F.encode d m) ad b =
      F.encodeCramerShoupCiphertext d
        (F.cramerShoupEncrypt H d pk m ad (b : ZMod (F.order d))) := by
  simp only [encodeCramerShoupEncrypt, encodeCramerShoupCiphertext, cramerShoupEncrypt,
    encodeCramerShoupTuple, cramerShoupHashMod, F.smul_encode, F.add_encode]

/-- Word-level Game 1 challenge encryption from `(v, w)` (encoded group elements), secret key
`sk`, encoded message `m`, and encoded associated data `ad` ([BonehShoup2023], Section 12.5.3,
Game 1, printed p. 490, and Exercise 12.27, printed pp. 521–522). -/
def encodeCramerShoupChallenge (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (v w m ad : List Bool) : List Bool :=
  let e := F.add (d, F.encodeProjHash d sk.1.1 sk.1.2 v w, m)
  let r := ofBits (H (d, encBits4 (v, w, e, ad)))
  encBits4 (v, w, e, F.encodeProjHash2 d sk.2.1.1 sk.2.1.2 sk.2.2.1 sk.2.2.2 r v w)

@[simp]
theorem encodeCramerShoupChallenge_encode (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (v w m : F.Carrier d) (ad : List Bool) :
    F.encodeCramerShoupChallenge H d sk (F.encode d v) (F.encode d w) (F.encode d m) ad =
      let e := projHash F d sk.1.1 sk.1.2 v w + m
      let ρ := F.cramerShoupHashMod H d (F.encodeCramerShoupTuple d v w e ad)
      let z' := projHash2 F d sk.2.1.1 sk.2.1.2 sk.2.2.1 sk.2.2.2 ρ v w
      F.encodeCramerShoupCiphertext d (v, w, e, z') := by
  simp only [encodeCramerShoupChallenge, encodeProjHash_encode, F.add_encode,
    encodeProjHash2_encode, encodeCramerShoupTuple, cramerShoupHashMod,
    encodeCramerShoupCiphertext]

/-- Word-level Cramer–Shoup decryption ([BonehShoup2023], Section 12.5.3, Remark 12.3, and
Exercise 12.27, printed pp. 489, 493, 522): given `(d, sk, ct, ad)`, unpack `(v, w, e, z') :=
decodeBits4 ct`, check canonical framing `encBits4 (v, w, e, z') == ct`, check group membership
`isElem (d, v) && isElem (d, w) && isElem (d, e)`, and check
`encodeProjHash2 d s₁ t₁ s₂ t₂ r v w == z'` where `r = ofBits (H (d, encBits4 (v, w, e, ad)))`; if
all pass, return `some (encode (e - f_{s,t}(v, w)))`, else `none`. -/
def decodeCramerShoup (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (d : F.Desc)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct ad : List Bool) : Option (List Bool) :=
  let parts := decodeBits4 ct
  let v := parts.1; let w := parts.2.1; let e := parts.2.2.1; let z' := parts.2.2.2
  let r := ofBits (H (d, encBits4 (v, w, e, ad)))
  if (encBits4 parts == ct) && isElem (d, v) && isElem (d, w) && isElem (d, e) &&
      (F.encodeProjHash2 d sk.2.1.1 sk.2.1.2 sk.2.2.1 sk.2.2.2 r v w == z') then
    some (F.add (d, e, F.encodeGroupNeg d (F.encodeProjHash d sk.1.1 sk.1.2 v w)))
  else
    none

/-- **Word-level Cramer–Shoup decryption matches algebraic `cramerShoupDecrypt` on encoded
ciphertexts**. -/
theorem decodeCramerShoup_encode [∀ d, DecidableEq (F.Carrier d)]
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))
    (ct : F.Carrier d × F.Carrier d × F.Carrier d × F.Carrier d) (ad : List Bool) :
    F.decodeCramerShoup H isElem d sk (F.encodeCramerShoupCiphertext d ct) ad =
      (F.cramerShoupDecrypt H d
        (((sk.1.1 : ZMod (F.order d)), (sk.1.2 : ZMod (F.order d))),
          (((sk.2.1.1 : ZMod (F.order d)), (sk.2.1.2 : ZMod (F.order d))),
            ((sk.2.2.1 : ZMod (F.order d)), (sk.2.2.2 : ZMod (F.order d))))) ct ad).map
        (F.encode d) := by
  rcases ct with ⟨v, w, e, z'⟩
  have hv : isElem (d, F.encode d v) = true := (hmem d _).mpr ⟨v, rfl⟩
  have hw : isElem (d, F.encode d w) = true := (hmem d _).mpr ⟨w, rfl⟩
  have he : isElem (d, F.encode d e) = true := (hmem d _).mpr ⟨e, rfl⟩
  have hinj : ∀ a b : F.Carrier d, (F.encode d a == F.encode d b) = decide (a = b) := fun a b => by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]; exact (F.encode_injective d).eq_iff
  simp only [decodeCramerShoup, encodeCramerShoupCiphertext, decodeBits4_encBits4, beq_self_eq_true,
    hv, hw, he, Bool.true_and, encodeProjHash2_encode, hinj, encodeProjHash_encode,
    encodeGroupNeg_encode, F.add_encode, cramerShoupDecrypt, encodeCramerShoupTuple,
    cramerShoupHashMod, sub_eq_add_neg, decide_eq_true_eq]
  split_ifs <;> rfl

/-- **Word-level Cramer–Shoup decryption of an honest encryption recovers
`some (F.encode d m)`**. -/
@[simp]
theorem decodeCramerShoup_cramerShoupEncrypt
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (α β : ZMod (F.order d))
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (m : F.Carrier d) (ad : List Bool) :
    F.decodeCramerShoup H isElem d sk
      (F.encodeCramerShoupCiphertext d
        (F.cramerShoupEncrypt H d
          (F.cramerShoupPublicKey d α sk.1.1 sk.1.2 sk.2.1.1 sk.2.1.2 sk.2.2.1 sk.2.2.2)
          m ad β)) ad = some (F.encode d m) := by
  classical
  rw [F.decodeCramerShoup_encode H isElem hmem, F.cramerShoupDecrypt_cramerShoupEncrypt]; rfl

/-! ### Polynomial-time certificates for word-level operations -/

@[local fun_prop]
private theorem computableTidilyInPolyTime_encodeGroupNeg
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc} {z : γ → List Bool}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hz : ComputableTidilyInPolyTime z encIn encBits) :
    ComputableTidilyInPolyTime (fun a => F.encodeGroupNeg (d a) (z a)) encIn encBits :=
  F.computableInPolyTime_smul.tidy.comp
    (hd.prod ((ComputableTidilyInPolyTime.binary_sub'
      (F.computableInPolyTime_order.tidy.comp hd) (.const 1)).prod hz))

@[local fun_prop]
private theorem computableTidilyInPolyTime_encodeProjHash
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc} {s t : γ → ℕ} {v w : γ → List Bool}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hs : ComputableTidilyInPolyTime s encIn encNat)
    (ht : ComputableTidilyInPolyTime t encIn encNat)
    (hv : ComputableTidilyInPolyTime v encIn encBits)
    (hw : ComputableTidilyInPolyTime w encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => F.encodeProjHash (d a) (s a) (t a) (v a) (w a)) encIn encBits :=
  F.computableInPolyTime_add.tidy.comp (hd.prod
    ((F.computableInPolyTime_smul.tidy.comp (hd.prod (hs.prod hv))).prod
      (F.computableInPolyTime_smul.tidy.comp (hd.prod (ht.prod hw)))))

@[local fun_prop]
private theorem computableTidilyInPolyTime_encodeProjHashAux
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc} {s t : γ → ℕ} {u : γ → List Bool}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hs : ComputableTidilyInPolyTime s encIn encNat)
    (ht : ComputableTidilyInPolyTime t encIn encNat)
    (hu : ComputableTidilyInPolyTime u encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => F.encodeProjHashAux (d a) (s a) (t a) (u a)) encIn encBits :=
  F.computableTidilyInPolyTime_encodeProjHash hd hs ht
    (F.computableInPolyTime_generator.tidy.comp hd) hu

@[local fun_prop]
private theorem computableTidilyInPolyTime_encodeProjHash2
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {s₁ t₁ s₂ t₂ r : γ → ℕ} {v w : γ → List Bool}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hs₁ : ComputableTidilyInPolyTime s₁ encIn encNat)
    (ht₁ : ComputableTidilyInPolyTime t₁ encIn encNat)
    (hs₂ : ComputableTidilyInPolyTime s₂ encIn encNat)
    (ht₂ : ComputableTidilyInPolyTime t₂ encIn encNat)
    (hr : ComputableTidilyInPolyTime r encIn encNat)
    (hv : ComputableTidilyInPolyTime v encIn encBits)
    (hw : ComputableTidilyInPolyTime w encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => F.encodeProjHash2 (d a) (s₁ a) (t₁ a) (s₂ a) (t₂ a) (r a) (v a) (w a))
      encIn encBits :=
  F.computableInPolyTime_add.tidy.comp (hd.prod
    ((F.computableTidilyInPolyTime_encodeProjHash hd hs₁ ht₁ hv hw).prod
      (F.computableInPolyTime_smul.tidy.comp (hd.prod (hr.prod
        (F.computableTidilyInPolyTime_encodeProjHash hd hs₂ ht₂ hv hw))))))

@[local fun_prop]
private theorem computableTidilyInPolyTime_encodeCramerShoupPublicKey
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc} {u : γ → List Bool}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hu : ComputableTidilyInPolyTime u encIn encBits)
    (hsk : ComputableTidilyInPolyTime sk encIn encCramerShoupSK) :
    ComputableTidilyInPolyTime
      (fun a => F.encodeCramerShoupPublicKey (d a) (u a) (sk a)) encIn encBits :=
  (ComputableTidilyInPolyTime.encode (encPair F.encDesc encBits4)).comp (hd.prod (hu.prod
    ((F.computableTidilyInPolyTime_encodeProjHashAux hd hsk.fst'.fst' hsk.fst'.snd' hu).prod
      ((F.computableTidilyInPolyTime_encodeProjHashAux hd
        hsk.snd'.fst'.fst' hsk.snd'.fst'.snd' hu).prod
        (F.computableTidilyInPolyTime_encodeProjHashAux hd
          hsk.snd'.snd'.fst' hsk.snd'.snd'.snd' hu)))))

/-- Word-level Cramer–Shoup public key generation is computable in polynomial time. -/
theorem computableInPolyTime_encodeCramerShoupPublicKey :
    ComputableInPolyTime
      (fun p : F.Desc × List Bool × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) =>
        F.encodeCramerShoupPublicKey p.1 p.2.1 p.2.2)
      (encPair F.encDesc (encPair encBits encCramerShoupSK)) encBits :=
  .of_tidy (F.computableTidilyInPolyTime_encodeCramerShoupPublicKey
    (by fun_prop) (by fun_prop) (by fun_prop))

@[local fun_prop]
private theorem computableTidilyInPolyTime_encodeCramerShoupChallenge
    {H : F.Desc × List Bool → List Bool}
    (hH : ComputableTidilyInPolyTime H (encPair F.encDesc encBits) encBits)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {v w m ad : γ → List Bool}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hsk : ComputableTidilyInPolyTime sk encIn encCramerShoupSK)
    (hv : ComputableTidilyInPolyTime v encIn encBits)
    (hw : ComputableTidilyInPolyTime w encIn encBits)
    (hm : ComputableTidilyInPolyTime m encIn encBits)
    (had : ComputableTidilyInPolyTime ad encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => F.encodeCramerShoupChallenge H (d a) (sk a) (v a) (w a) (m a) (ad a))
      encIn encBits := by
  have he := F.computableInPolyTime_add.tidy.comp (hd.prod
    ((F.computableTidilyInPolyTime_encodeProjHash hd hsk.fst'.fst' hsk.fst'.snd' hv hw).prod hm))
  have hr := ComputableTidilyInPolyTime.bitsToNat.comp (hH.comp (hd.prod
    ((ComputableTidilyInPolyTime.encode encBits4).comp (hv.prod (hw.prod (he.prod had))))))
  exact (ComputableTidilyInPolyTime.encode encBits4).comp (hv.prod (hw.prod (he.prod
    (F.computableTidilyInPolyTime_encodeProjHash2 hd
      hsk.snd'.fst'.fst' hsk.snd'.fst'.snd' hsk.snd'.snd'.fst' hsk.snd'.snd'.snd' hr hv hw))))

/-- Word-level Cramer–Shoup secret-key challenge encryption `encodeCramerShoupChallenge` is
computable in polynomial time whenever `H` is. -/
theorem computableInPolyTime_encodeCramerShoupChallenge
    {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits) :
    ComputableInPolyTime
      (fun p : F.Desc × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) ×
          List Bool × List Bool × List Bool × List Bool =>
        F.encodeCramerShoupChallenge H p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
      (encPair F.encDesc (encPair encCramerShoupSK
        (encPair encBits (encPair encBits (encPair encBits encBits)))))
      encBits :=
  .of_tidy (F.computableTidilyInPolyTime_encodeCramerShoupChallenge hH.tidy
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))

@[local fun_prop]
private theorem computableTidilyInPolyTime_encodeCramerShoupEncrypt
    {H : F.Desc × List Bool → List Bool}
    (hH : ComputableTidilyInPolyTime H (encPair F.encDesc encBits) encBits)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {pk : γ → List Bool × List Bool × List Bool × List Bool} {m ad : γ → List Bool} {b : γ → ℕ}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hpk : ComputableTidilyInPolyTime pk encIn
      (encPair encBits (encPair encBits (encPair encBits encBits))))
    (hm : ComputableTidilyInPolyTime m encIn encBits)
    (had : ComputableTidilyInPolyTime ad encIn encBits)
    (hb : ComputableTidilyInPolyTime b encIn encNat) :
    ComputableTidilyInPolyTime
      (fun a => F.encodeCramerShoupEncrypt H (d a) (pk a) (m a) (ad a) (b a)) encIn encBits := by
  have hv := F.computableInPolyTime_smul.tidy.comp
    (hd.prod (hb.prod (F.computableInPolyTime_generator.tidy.comp hd)))
  have hw := F.computableInPolyTime_smul.tidy.comp (hd.prod (hb.prod hpk.fst'))
  have he := F.computableInPolyTime_add.tidy.comp
    (hd.prod ((F.computableInPolyTime_smul.tidy.comp (hd.prod (hb.prod hpk.snd'.fst'))).prod hm))
  have hr := ComputableTidilyInPolyTime.bitsToNat.comp (hH.comp (hd.prod
    ((ComputableTidilyInPolyTime.encode encBits4).comp (hv.prod (hw.prod (he.prod had))))))
  have hz' := F.computableInPolyTime_smul.tidy.comp (hd.prod (hb.prod
    (F.computableInPolyTime_add.tidy.comp (hd.prod (hpk.snd'.snd'.fst'.prod
      (F.computableInPolyTime_smul.tidy.comp (hd.prod (hr.prod hpk.snd'.snd'.snd'))))))))
  exact (ComputableTidilyInPolyTime.encode encBits4).comp (hv.prod (hw.prod (he.prod hz')))

/-- Word-level Cramer–Shoup encryption is computable in polynomial time whenever `H` is. -/
theorem computableInPolyTime_encodeCramerShoupEncrypt
    {H : F.Desc × List Bool → List Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits) :
    ComputableInPolyTime
      (fun p : F.Desc × (List Bool × List Bool × List Bool × List Bool) ×
          List Bool × List Bool × ℕ =>
        F.encodeCramerShoupEncrypt H p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
      (encPair F.encDesc (encPair encBits4 (encPair encBits (encPair encBits encNat)))) encBits :=
  .of_tidy (F.computableTidilyInPolyTime_encodeCramerShoupEncrypt hH.tidy
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))

@[local fun_prop]
private theorem computableTidilyInPolyTime_decodeCramerShoup
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableTidilyInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableTidilyInPolyTime isElem (encPair F.encDesc encBits) encBool)
    {γ : Type} {encIn : γ ↪ List Bool} {d : γ → F.Desc}
    {sk : γ → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))} {ct ad : γ → List Bool}
    (hd : ComputableTidilyInPolyTime d encIn F.encDesc)
    (hsk : ComputableTidilyInPolyTime sk encIn encCramerShoupSK)
    (hct : ComputableTidilyInPolyTime ct encIn encBits)
    (had : ComputableTidilyInPolyTime ad encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => F.decodeCramerShoup H isElem (d a) (sk a) (ct a) (ad a))
      encIn (encOption encBits) := by
  have hparts := computableTidilyInPolyTime_decodeBits4.comp hct
  have hv := hparts.fst'; have hw := hparts.snd'.fst'
  have he := hparts.snd'.snd'.fst'; have hz' := hparts.snd'.snd'.snd'
  have hr := ComputableTidilyInPolyTime.bitsToNat.comp (hH.comp (hd.prod
    ((ComputableTidilyInPolyTime.encode encBits4).comp (hv.prod (hw.prod (he.prod had))))))
  have hbeq : ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool => p.1 == p.2) (encPair encBits encBits) encBool := by polytime
  have hand : ComputableTidilyInPolyTime
      (fun p : Bool × Bool => p.1 && p.2) (encPair encBool encBool) encBool := by polytime
  have hframe := hbeq.comp (((ComputableTidilyInPolyTime.encode encBits4).comp hparts).prod hct)
  have htagEq := hbeq.comp ((F.computableTidilyInPolyTime_encodeProjHash2 hd
    hsk.snd'.fst'.fst' hsk.snd'.fst'.snd' hsk.snd'.snd'.fst' hsk.snd'.snd'.snd' hr hv hw).prod hz')
  have hcond := hand.comp ((hand.comp ((hand.comp ((hand.comp
    (hframe.prod (hisElem.comp (hd.prod hv)))).prod (hisElem.comp (hd.prod hw)))).prod
    (hisElem.comp (hd.prod he)))).prod htagEq)
  have hmsg := F.computableInPolyTime_add.tidy.comp (hd.prod (he.prod
    (F.computableTidilyInPolyTime_encodeGroupNeg hd
      (F.computableTidilyInPolyTime_encodeProjHash hd hsk.fst'.fst' hsk.fst'.snd' hv hw))))
  have hsome : ComputableTidilyInPolyTime
      (fun x : List Bool => (some x : Option (List Bool))) encBits (encOption encBits) := by
    polytime
  exact .cond hcond (hsome.comp hmsg) (.const none)

/-- **Word-level Cramer–Shoup decryption is computable in polynomial time** whenever `H` and
`isElem` are computable in polynomial time. -/
theorem computableInPolyTime_decodeCramerShoup
    {H : F.Desc × List Bool → List Bool} {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool) :
    ComputableInPolyTime
      (fun p : F.Desc × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) × List Bool × List Bool =>
        F.decodeCramerShoup H isElem p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair F.encDesc (encPair encCramerShoupSK (encPair encBits encBits)))
      (encOption encBits) :=
  .of_tidy (F.computableTidilyInPolyTime_decodeCramerShoup hH.tidy hisElem.tidy
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))

/-- Change of variables `σ ↦ δ - α * τ` under two independent uniform draws in `ZMod q`. -/
private theorem uniform_sub_mul_bind {α_out : Type*} (q : ℕ) [NeZero q] (α : ZMod q)
    (f : ZMod q → ZMod q → PMF α_out) :
    ((PMF.uniformOfFintype (ZMod q)).bind fun σ =>
      (PMF.uniformOfFintype (ZMod q)).bind fun τ => f σ τ) =
    ((PMF.uniformOfFintype (ZMod q)).bind fun δ =>
      (PMF.uniformOfFintype (ZMod q)).bind fun τ => f (δ - α * τ) τ) := by
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  refine congrArg _ (funext fun τ => ?_)
  change (PMF.uniformOfFintype (ZMod q)).bind (fun σ => f σ τ) =
    (PMF.uniformOfFintype (ZMod q)).bind ((fun σ => f σ τ) ∘ Equiv.subRight (α * τ))
  rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]

/-- Change of variables `τ ↦ ξ - c` under a uniform draw in `ZMod q`. -/
private theorem uniform_sub_bind {α_out : Type*} (q : ℕ) [NeZero q] (c : ZMod q)
    (f : ZMod q → PMF α_out) :
    ((PMF.uniformOfFintype (ZMod q)).bind fun τ => f τ) =
    ((PMF.uniformOfFintype (ZMod q)).bind fun ξ => f (ξ - c)) := by
  change (PMF.uniformOfFintype (ZMod q)).bind f =
    (PMF.uniformOfFintype (ZMod q)).bind (f ∘ Equiv.subRight c)
  rw [← PMF.bind_map, PMF.uniformOfFintype_map_equiv]


/-! ### Collision detection and decryption oracle replies -/

/-- Test whether a Phase 2 ciphertext query `(ct_q, ad_q)` yields a `cramerShoupHashMod H d`
collision with the challenge `(ct, ad)` on their `(v, w, e, ad)` tuples. -/
def isCramerShoupCollision
    (H : F.Desc × List Bool → List Bool)
    (d : F.Desc) (ct_q ad_q ct ad : List Bool) : Bool :=
  let x := extractCramerShoupTuple ct_q ad_q
  let y := extractCramerShoupTuple ct ad
  (x != y) && ((ofBits (H (d, x)) % F.order d) == (ofBits (H (d, y)) % F.order d))

/-- `isCramerShoupCollision` coincides with `isCollisionFor (F.cramerShoupHashMod H)` on the
extracted `(v, w, e, ad)` tuples. -/
theorem isCramerShoupCollision_eq_isCollisionFor
    (H : F.Desc × List Bool → List Bool)
    (n : ℕ) (d : F.Desc) (ct_q ad_q ct ad : List Bool) :
    F.isCramerShoupCollision H d ct_q ad_q ct ad =
      isCollisionFor (F.cramerShoupHashMod H) (fun _ _ _ => true) n d
        (extractCramerShoupTuple ct_q ad_q) (extractCramerShoupTuple ct ad) := by
  rw [Bool.eq_iff_iff]
  simp only [isCramerShoupCollision, isCollisionFor, cramerShoupHashMod,
    Bool.true_and, Bool.and_eq_true, bne_iff_ne, beq_iff_eq, decide_eq_true_eq,
    ZMod.natCast_eq_natCast_iff']


/-- Stateless Phase 1 decryption reply for Cramer–Shoup (`hasAD = true` for `cca2ADPhase1Oracle`,
`hasAD = false` for `cca2Phase1Oracle`). -/
def cramerShoupPhase1Reply
    (hasAD : Bool) (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (req : List Bool) : List Bool :=
  let q := splitCramerShoupQuery hasAD req
  encOption encBits (F.decodeCramerShoup H isElem d sk q.1 q.2)

/-- Stateless Phase 2 decryption reply that rejects the challenge `(ct, ad)` and any query
`(ct_q, ad_q)` colliding with `(ct, ad)` under `cramerShoupHashMod H d`. -/
def cramerShoupCollisionPhase2Reply
    (hasAD : Bool) (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct ad req : List Bool) : List Bool :=
  let q := splitCramerShoupQuery hasAD req
  if ((q.1 == ct) && (q.2 == ad)) || F.isCramerShoupCollision H d q.1 q.2 ct ad then
    []
  else
    encOption encBits (F.decodeCramerShoup H isElem d sk q.1 q.2)

/-! ### Canonical secret-key conversion and hybrid Games 3–5 -/

/-- Convert six `ZMod (F.order d)` exponents `(σ, τ, σ₁, τ₁, σ₂, τ₂)` into their canonical natural
number representatives `((σ.val, τ.val), ((σ₁.val, τ₁.val), (σ₂.val, τ₂.val)))`. -/
def skNatOfZMod (d : F.Desc) (σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) :
    (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((σ.val, τ.val), ((σ₁.val, τ₁.val), (σ₂.val, τ₂.val)))

/-- **Game 3** (corresponding to Game 4 of [BonehShoup2023], Section 12.5.3, printed p. 492,
adapted to $\mathcal{E}_{\mathrm{MCS}}$ with associated data): Phase 1 uses `cramerShoupPhase1Reply`
and Phase 2 rejects both `(ct, ad)` and any ciphertext query `(ct_q, ad_q)` whose `(v, w, e, ad)`
tuple collides with `(ct, ad)` under `cramerShoupHashMod H d`
(`cramerShoupCollisionPhase2Reply`). -/
noncomputable def cramerShoupGame3
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n; let U := PMF.uniformOfFintype (ZMod (F.order d))
  let α ← U; let β ← U; let γ ← U; let σ ← U; let τ ← U; let σ₁ ← U; let τ₁ ← U; let σ₂ ← U
  let τ₂ ← U
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let u := F.encode d (α • F.generator d); let v := F.encode d (β • F.generator d)
  let w := F.encode d (γ • F.generator d)
  let pk := F.encodeCramerShoupPublicKey d u sk
  runStatelessOracle (F.cramerShoupPhase1Reply hasAD H isElem d sk)
    (adversary.choose n pk) fun choice =>
    let m₀ := encodeMsg (d, choice.1.1.1); let m₁ := encodeMsg (d, choice.1.1.2)
    let ad := encodeAD (d, choice.1.2)
    if isElem (d, m₀) && isElem (d, m₁) then
      let m := if bit then m₁ else m₀
      let ct := F.encodeCramerShoupChallenge H d sk v w m ad
      runStatelessOracle (F.cramerShoupCollisionPhase2Reply hasAD H isElem d sk ct ad)
        (adversary.guess n choice.2 ct) PMF.pure
    else
      PMF.pure false

/-! ### Projective-hash rejection (Games 3.5, 4, and 5) and concrete 1CCA bound -/

/-- Decryption helper for Game 4 ([BonehShoup2023], Section 12.5.3, printed p. 492): on the fiber
`σ = δ - α * τ`, `σ₁ = δ₁ - α * τ₁`, `σ₂ = δ₂ - α * τ₂`, reject any ciphertext whose `(v', w')`
pair does not satisfy `w' == F.smul (d, α.val, v')`, and otherwise decrypt using
`(δ, 0, δ₁, 0, δ₂, 0)` (which agrees with `(σ, τ, σ₁, τ₁, σ₂, τ₂)` on all Diffie–Hellman queries
by `projHash_fiber_eq` and `projHash2_fiber_dh`). -/
def decodeCramerShoupDH
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (α δ δ₁ δ₂ : ZMod (F.order d)) (ct ad : List Bool) : Option (List Bool) :=
  let parts := decodeBits4 ct
  if parts.2.1 == F.smul (d, α.val, parts.1) then
    F.decodeCramerShoup H isElem d (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0) ct ad
  else
    none

/-- Stateless Phase 1 decryption reply for Game 3.5 and Game 4, rejecting non-DH queries. -/
def cramerShoupDHPhase1Reply
    (hasAD : Bool) (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (α δ δ₁ δ₂ : ZMod (F.order d)) (req : List Bool) : List Bool :=
  let q := splitCramerShoupQuery hasAD req
  encOption encBits (F.decodeCramerShoupDH H isElem d α δ δ₁ δ₂ q.1 q.2)

/-- Stateless Phase 2 decryption reply for Game 4, rejecting `(ct, ad)`, `H'`-collisions with
`(ct, ad)`, and non-DH queries. -/
def cramerShoupDHPhase2Reply
    (hasAD : Bool) (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (α δ δ₁ δ₂ : ZMod (F.order d)) (ct ad req : List Bool) : List Bool :=
  let q := splitCramerShoupQuery hasAD req
  if ((q.1 == ct) && (q.2 == ad)) || F.isCramerShoupCollision H d q.1 q.2 ct ad then
    []
  else
    encOption encBits (F.decodeCramerShoupDH H isElem d α δ δ₁ δ₂ q.1 q.2)

/-- Bad-event predicate for Game 3 $\to$ Game 4 ([BonehShoup2023], Section 12.5.3, equations
(12.26)–(12.27), printed pp. 492–493): `ct_q = encBits4 (v', w', e', z')` is a syntactically
well-formed non-DH ciphertext (`w' != F.smul (d, α.val, v')`) whose tag `z'` matches
`encodeProjHash2` on `(v', w', e', ad_q)`. -/
def isCramerShoupBadDH
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (α : ZMod (F.order d))
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) (ct_q ad_q : List Bool) : Bool :=
  let parts := decodeBits4 ct_q
  let v := parts.1; let w := parts.2.1; let e := parts.2.2.1; let z' := parts.2.2.2
  let r := ofBits (H (d, encBits4 (v, w, e, ad_q)))
  (encBits4 parts == ct_q) && isElem (d, v) && isElem (d, w) && isElem (d, e) &&
    (w != F.smul (d, α.val, v)) &&
    (F.encodeProjHash2 d sk.2.1.1 sk.2.1.2 sk.2.2.1 sk.2.2.2 r v w == z')

private theorem encodeCramerShoupPublicKey_fiber_eq (d : F.Desc)
    (α δ τ δ₁ τ₁ δ₂ τ₂ : ZMod (F.order d)) :
    F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d))
      (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂) =
    F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d))
      (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0) := by
  simp only [encodeCramerShoupPublicKey_encode, cramerShoupPublicKey, skNatOfZMod,
    ZMod.natCast_zmod_val, projHash2Aux, projHashAux_generator_smul, sub_add_cancel,
    mul_zero, add_zero]

private theorem encodeCramerShoupChallenge_fiber_eq
    (H : F.Desc × List Bool → List Bool) (d : F.Desc)
    (α β γ δ τ δ₁ δ₂ ξ τ₂ : ZMod (F.order d)) (m ad : List Bool) :
    let v := F.encode d (β • F.generator d); let w := F.encode d (γ • F.generator d)
    let e := F.add (d, F.encodeProjHash d (δ - α * τ).val τ.val v w, m)
    let ρ := F.cramerShoupHashMod H d (encBits4 (v, w, e, ad))
    F.encodeCramerShoupChallenge H d
      (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂)
        (δ₂ - α * τ₂) τ₂) v w m ad =
      encBits4 (v, w, e, F.encode d ((β * (δ₁ + ρ * δ₂) + (γ - α * β) * ξ) • F.generator d)) := by
  simp only [encodeCramerShoupChallenge, skNatOfZMod, encodeProjHash2_encode,
    ZMod.natCast_zmod_val, cramerShoupHashMod, projHash2_fiber_challenge_eq]

private theorem decodeCramerShoup_fiber_eq_decodeCramerShoupDH_of_not_bad
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (α δ τ δ₁ τ₁ δ₂ τ₂ : ZMod (F.order d)) (ct_q ad_q : List Bool)
    (hbad : F.isCramerShoupBadDH H isElem d α
      (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂) ct_q ad_q = false) :
    F.decodeCramerShoup H isElem d
      (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂) ct_q ad_q =
    F.decodeCramerShoupDH H isElem d α δ δ₁ δ₂ ct_q ad_q := by
  unfold decodeCramerShoupDH
  by_cases hdh : ((decodeBits4 ct_q).2.1 == F.smul (d, α.val, (decodeBits4 ct_q).1)) = true
  · simp only [hdh, ↓reduceIte]
    unfold decodeCramerShoup
    by_cases hv : isElem (d, (decodeBits4 ct_q).1) = true
    · obtain ⟨vElem, hvElem⟩ := (hmem d _).mp hv
      obtain ⟨β', rfl⟩ := F.smul_generator_surjective d vElem
      have hwElem : (decodeBits4 ct_q).2.1 = F.encode d ((α * β') • F.generator d) := by
        rw [beq_iff_eq.mp hdh, ← hvElem, F.smul_encode, ZMod.natCast_zmod_val, smul_smul]
      have hproj1 :
          F.encodeProjHash d (δ - α * τ).val τ.val (decodeBits4 ct_q).1 (decodeBits4 ct_q).2.1 =
            F.encodeProjHash d δ.val 0 (decodeBits4 ct_q).1 (decodeBits4 ct_q).2.1 := by
        rw [← hvElem, hwElem, encodeProjHash_encode, encodeProjHash_encode]
        simp only [ZMod.natCast_zmod_val, Nat.cast_zero]
        have hfib1 := projHash_fiber_eq F d α β' (α * β') δ τ
        have hfib0 := projHash_fiber_eq F d α β' (α * β') δ 0
        rw [sub_self, zero_mul, add_zero] at hfib1 hfib0
        rw [mul_zero, sub_zero] at hfib0
        rw [hfib1, hfib0]
      have hproj2 (r : ℕ) :
          F.encodeProjHash2 d (δ₁ - α * τ₁).val τ₁.val (δ₂ - α * τ₂).val τ₂.val r
            (decodeBits4 ct_q).1 (decodeBits4 ct_q).2.1 =
          F.encodeProjHash2 d δ₁.val 0 δ₂.val 0 r
            (decodeBits4 ct_q).1 (decodeBits4 ct_q).2.1 := by
        rw [← hvElem, hwElem, encodeProjHash2_encode, encodeProjHash2_encode]
        simp only [ZMod.natCast_zmod_val, Nat.cast_zero]
        have hfib2 := projHash2_fiber_dh F d α β' δ₁ δ₂ τ₁ τ₂ (r : ZMod (F.order d))
        have hfib0 := projHash2_fiber_dh F d α β' δ₁ δ₂ 0 0 (r : ZMod (F.order d))
        simp only [mul_zero, sub_zero] at hfib0
        rw [hfib2, hfib0]
      simp only [skNatOfZMod, ZMod.val_zero, hproj1, hproj2]
    · simp only [Bool.not_eq_true] at hv; simp [hv]
  · simp only [Bool.not_eq_true] at hdh
    simp only [hdh, Bool.false_eq_true, ↓reduceIte]
    have hne : ((decodeBits4 ct_q).2.1 != F.smul (d, α.val, (decodeBits4 ct_q).1)) = true := by
      simpa [bne] using hdh
    unfold decodeCramerShoup; dsimp only; rw [ite_eq_right_iff]
    intro h; exfalso; revert h hbad; simp [isCramerShoupBadDH, hne]

private theorem cramerShoupPhase1Reply_fiber_eq_of_not_bad
    (hasAD : Bool) (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (α δ τ δ₁ τ₁ δ₂ τ₂ : ZMod (F.order d)) (req : List Bool)
    (hbad : F.isCramerShoupBadDH H isElem d α
      (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂)
      (splitCramerShoupQuery hasAD req).1 (splitCramerShoupQuery hasAD req).2 = false) :
    F.cramerShoupPhase1Reply hasAD H isElem d
      (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂) req =
    F.cramerShoupDHPhase1Reply hasAD H isElem d α δ δ₁ δ₂ req := by
  simp only [cramerShoupPhase1Reply, cramerShoupDHPhase1Reply,
    F.decodeCramerShoup_fiber_eq_decodeCramerShoupDH_of_not_bad
      H isElem hmem d α δ τ δ₁ τ₁ δ₂ τ₂ _ _ hbad]

private theorem cramerShoupCollisionPhase2Reply_fiber_eq_of_not_bad
    (hasAD : Bool) (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (α δ τ δ₁ τ₁ δ₂ τ₂ : ZMod (F.order d)) (ct ad req : List Bool)
    (hbad : (let q := splitCramerShoupQuery hasAD req
      !(((q.1 == ct) && (q.2 == ad)) || F.isCramerShoupCollision H d q.1 q.2 ct ad) &&
      F.isCramerShoupBadDH H isElem d α
        (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂) q.1 q.2) = false) :
    F.cramerShoupCollisionPhase2Reply hasAD H isElem d
      (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂) ct ad req =
    F.cramerShoupDHPhase2Reply hasAD H isElem d α δ δ₁ δ₂ ct ad req := by
  unfold cramerShoupCollisionPhase2Reply cramerShoupDHPhase2Reply
  dsimp only
  let q := splitCramerShoupQuery hasAD req
  by_cases hrej :
      (((q.1 == ct) && (q.2 == ad)) || F.isCramerShoupCollision H d q.1 q.2 ct ad) = true
  · simp [q, hrej]
  · simp only [Bool.not_eq_true] at hrej
    have hbad' : F.isCramerShoupBadDH H isElem d α
        (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂) q.1 q.2 = false := by
      simpa [q, hrej] using hbad
    simp [q, hrej, F.decodeCramerShoup_fiber_eq_decodeCramerShoupDH_of_not_bad
      H isElem hmem d α δ τ δ₁ τ₁ δ₂ τ₂ q.1 q.2 hbad']

private theorem tsum_uniform_smul_generator_eq {d : F.Desc}
    (e : ZMod (F.order d) ≃ ZMod (F.order d)) (z' : List Bool) :
    (∑' τ : ZMod (F.order d), PMF.uniformOfFintype (ZMod (F.order d)) τ *
      if F.encode d (e τ • F.generator d) == z' then (1 : ℝ≥0∞) else 0) ≤
      (F.order d : ℝ≥0∞)⁻¹ := by
  by_cases hz : z' ∈ Set.range (F.encode d)
  · obtain ⟨tElem, rfl⟩ := hz; obtain ⟨ζ, rfl⟩ := F.smul_generator_surjective d tElem
    have heq (τ : ZMod (F.order d)) :
        (F.encode d (e τ • F.generator d) == F.encode d (ζ • F.generator d)) =
          decide (τ = e.symm ζ) := by
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq,
        (F.encode_injective d).eq_iff, (F.smul_generator_bijective d).1.eq_iff, ← e.eq_symm_apply]
    simp_rw [heq, decide_eq_true_eq, mul_ite, mul_one, mul_zero, tsum_ite_eq,
      PMF.uniformOfFintype_apply, ZMod.card]
    exact le_rfl
  · have hfalse (τ : ZMod (F.order d)) : (F.encode d (e τ • F.generator d) == z') = false :=
      beq_eq_false_iff_ne.mpr fun h => hz ⟨e τ • F.generator d, h⟩
    simp [hfalse]

private theorem exists_nonDH_of_badDH_pre
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (α : ZMod (F.order d)) (ct_q : List Bool)
    (hpre : ((encBits4 (decodeBits4 ct_q) == ct_q) && isElem (d, (decodeBits4 ct_q).1) &&
      isElem (d, (decodeBits4 ct_q).2.1) && isElem (d, (decodeBits4 ct_q).2.2.1) &&
      ((decodeBits4 ct_q).2.1 != F.smul (d, α.val, (decodeBits4 ct_q).1))) = true) :
    ∃ β' γ' : ZMod (F.order d), F.encode d (β' • F.generator d) = (decodeBits4 ct_q).1 ∧
      F.encode d (γ' • F.generator d) = (decodeBits4 ct_q).2.1 ∧ γ' ≠ α * β' := by
  have hvw : isElem (d, (decodeBits4 ct_q).1) = true ∧
      isElem (d, (decodeBits4 ct_q).2.1) = true ∧
      ((decodeBits4 ct_q).2.1 != F.smul (d, α.val, (decodeBits4 ct_q).1)) = true := by
    revert hpre
    cases encBits4 (decodeBits4 ct_q) == ct_q <;> cases isElem (d, (decodeBits4 ct_q).1) <;>
      cases isElem (d, (decodeBits4 ct_q).2.1) <;> cases isElem (d, (decodeBits4 ct_q).2.2.1) <;>
      cases (decodeBits4 ct_q).2.1 != F.smul (d, α.val, (decodeBits4 ct_q).1) <;> simp
  obtain ⟨vElem, hvElem⟩ := (hmem d _).mp hvw.1; obtain ⟨wElem, hwElem⟩ := (hmem d _).mp hvw.2.1
  obtain ⟨β', rfl⟩ := F.smul_generator_surjective d vElem
  obtain ⟨γ', rfl⟩ := F.smul_generator_surjective d wElem
  refine ⟨β', γ', hvElem, hwElem, fun hEq => (bne_iff_ne.mp hvw.2.2) ?_⟩
  rw [← hvElem, ← hwElem, hEq, F.smul_encode, ZMod.natCast_zmod_val, smul_smul]

private theorem tsum_and_isCramerShoupBadDH_le
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (α : ZMod (F.order d))
    (sk : ZMod (F.order d) → (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))
    (cond : Bool) (ct_q ad_q : List Bool)
    (hequiv : ∀ β' γ' : ZMod (F.order d), γ' ≠ α * β' →
      ∃ e : ZMod (F.order d) ≃ ZMod (F.order d), ∀ τ,
        projHash2 F d ((sk τ).2.1.1 : ZMod (F.order d)) ((sk τ).2.1.2 : ZMod (F.order d))
          ((sk τ).2.2.1 : ZMod (F.order d)) ((sk τ).2.2.2 : ZMod (F.order d))
          (ofBits (H (d, encBits4 ((decodeBits4 ct_q).1, (decodeBits4 ct_q).2.1,
            (decodeBits4 ct_q).2.2.1, ad_q))) : ZMod (F.order d))
          (β' • F.generator d) (γ' • F.generator d) = e τ • F.generator d) :
    (∑' τ : ZMod (F.order d), PMF.uniformOfFintype (ZMod (F.order d)) τ *
      if (cond && F.isCramerShoupBadDH H isElem d α (sk τ) ct_q ad_q)
      then (1 : ℝ≥0∞) else 0) ≤ (F.order d : ℝ≥0∞)⁻¹ := by
  let parts := decodeBits4 ct_q
  let r := ofBits (H (d, encBits4 (parts.1, parts.2.1, parts.2.2.1, ad_q)))
  by_cases hpre :
      ((encBits4 parts == ct_q) && isElem (d, parts.1) && isElem (d, parts.2.1) &&
        isElem (d, parts.2.2.1) && (parts.2.1 != F.smul (d, α.val, parts.1))) = true
  · obtain ⟨β', γ', hvElem, hwElem, hγ'⟩ :=
      F.exists_nonDH_of_badDH_pre isElem hmem d α ct_q hpre
    obtain ⟨e_equiv, he_equiv⟩ := hequiv β' γ' hγ'
    have hle (τ : ZMod (F.order d)) :
        (if (cond && F.isCramerShoupBadDH H isElem d α (sk τ) ct_q ad_q)
        then (1 : ℝ≥0∞) else 0) ≤
        if F.encode d (e_equiv τ • F.generator d) == parts.2.2.2 then 1 else 0 := by
      have hbad_eq :
          F.isCramerShoupBadDH H isElem d α (sk τ) ct_q ad_q =
            (F.encode d (e_equiv τ • F.generator d) == parts.2.2.2) := by
        change (((encBits4 parts == ct_q) && isElem (d, parts.1) && isElem (d, parts.2.1) &&
          isElem (d, parts.2.2.1) && (parts.2.1 != F.smul (d, α.val, parts.1))) &&
          (F.encodeProjHash2 d (sk τ).2.1.1 (sk τ).2.1.2 (sk τ).2.2.1 (sk τ).2.2.2 r
            parts.1 parts.2.1 == parts.2.2.2)) = _
        rw [hpre, Bool.true_and, ← hvElem, ← hwElem, encodeProjHash2_encode, he_equiv τ]
      rw [hbad_eq]
      cases cond <;> cases F.encode d (e_equiv τ • F.generator d) == parts.2.2.2 <;> simp
    exact (tsum_le_tsum fun τ =>
      mul_le_mul_of_nonneg_left (hle τ) zero_le).trans
        (F.tsum_uniform_smul_generator_eq e_equiv parts.2.2.2)
  · simp only [Bool.not_eq_true] at hpre
    have hfalse (τ : ZMod (F.order d)) :
        (cond && F.isCramerShoupBadDH H isElem d α (sk τ) ct_q ad_q) = false := by
      rw [Bool.and_eq_false_iff]; right
      change (((encBits4 parts == ct_q) && isElem (d, parts.1) && isElem (d, parts.2.1) &&
        isElem (d, parts.2.2.1) && (parts.2.1 != F.smul (d, α.val, parts.1))) && _) = false
      simp [hpre]
    simp_rw [hfalse]; simp

private theorem tsum_isCramerShoupBadDH_phase1_le
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (α δ τ δ₁ δ₂ τ₂ : ZMod (F.order d)) (ct_q ad_q : List Bool) :
    (∑' τ₁ : ZMod (F.order d), PMF.uniformOfFintype (ZMod (F.order d)) τ₁ *
      if F.isCramerShoupBadDH H isElem d α
        (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂) ct_q ad_q
      then (1 : ℝ≥0∞) else 0) ≤ (F.order d : ℝ≥0∞)⁻¹ := by
  simpa only [Bool.true_and] using F.tsum_and_isCramerShoupBadDH_le H isElem hmem d α
    (fun τ₁ => F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂) true ct_q ad_q
    fun β' γ' hγ' => by
      let ρ' : ZMod (F.order d) :=
        (ofBits (H (d, encBits4 ((decodeBits4 ct_q).1, (decodeBits4 ct_q).2.1,
          (decodeBits4 ct_q).2.2.1, ad_q))) : ZMod (F.order d))
      refine ⟨(Equiv.addRight (ρ' * τ₂)).trans (projHashFiberEquiv F d hγ' (δ₁ + ρ' * δ₂)),
        fun τ₁ => ?_⟩
      simp only [skNatOfZMod, ZMod.natCast_zmod_val, projHash2_fiber_eq, Equiv.trans_apply,
        Equiv.coe_addRight, projHashFiberEquiv_apply, ρ']

private theorem tsum_isCramerShoupBadDH_phase2_le
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (α β γ δ τ δ₁ δ₂ ξ : ZMod (F.order d)) (e ad ct_q ad_q : List Bool) :
    let v := F.encode d (β • F.generator d); let w := F.encode d (γ • F.generator d)
    let ρ := F.cramerShoupHashMod H d (encBits4 (v, w, e, ad))
    let ct := encBits4 (v, w, e,
      F.encode d ((β * (δ₁ + ρ * δ₂) + (γ - α * β) * ξ) • F.generator d))
    (∑' τ₂ : ZMod (F.order d), PMF.uniformOfFintype (ZMod (F.order d)) τ₂ *
      if (!(((ct_q == ct) && (ad_q == ad)) || F.isCramerShoupCollision H d ct_q ad_q ct ad) &&
        F.isCramerShoupBadDH H isElem d α
          (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂)
            (δ₂ - α * τ₂) τ₂) ct_q ad_q)
      then (1 : ℝ≥0∞) else 0) ≤ (F.order d : ℝ≥0∞)⁻¹ := by
  intro v w ρ ct
  let parts := decodeBits4 ct_q
  let r' := ofBits (H (d, encBits4 (parts.1, parts.2.1, parts.2.2.1, ad_q)))
  let ρ' : ZMod (F.order d) := (r' : ZMod (F.order d))
  by_cases hρ : ρ' = ρ
  · have hfalse (τ₂ : ZMod (F.order d)) :
        (!(((ct_q == ct) && (ad_q == ad)) || F.isCramerShoupCollision H d ct_q ad_q ct ad) &&
          F.isCramerShoupBadDH H isElem d α
            (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂)
              (δ₂ - α * τ₂) τ₂) ct_q ad_q) = false := by
      rw [Bool.and_eq_false_iff]
      by_cases hrej :
          (((ct_q == ct) && (ad_q == ad)) || F.isCramerShoupCollision H d ct_q ad_q ct ad) = true
      · left; simp [hrej]
      · right
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hrej
        rcases hrej with ⟨hne_ct_ad, hnot_coll⟩
        by_cases hframe : (encBits4 parts == ct_q) = true
        · have hreq_eq : encBits4 (parts.1, parts.2.1, parts.2.2.1, parts.2.2.2) = ct_q :=
            beq_iff_eq.mp hframe
          have htuple_eq :
              encBits4 (parts.1, parts.2.1, parts.2.2.1, ad_q) = encBits4 (v, w, e, ad) := by
            by_contra hne_tuple
            have hcoll : F.isCramerShoupCollision H d ct_q ad_q ct ad = true := by
              rw [F.isCramerShoupCollision_eq_isCollisionFor H 0 d ct_q ad_q ct ad,
                isCollisionFor_eq_true_iff]
              refine ⟨rfl, rfl, ?_, ?_⟩
              · simpa [extractCramerShoupTuple, parts, ct, decodeBits4_encBits4] using hne_tuple
              · simpa [extractCramerShoupTuple, parts, ct, decodeBits4_encBits4,
                  cramerShoupHashMod, ρ', ρ, r'] using hρ
            exact Bool.false_ne_true (hnot_coll.symm.trans hcoll)
          rcases Prod.mk.inj (encBits4.injective htuple_eq) with ⟨hv_eq, hrest1⟩
          rcases Prod.mk.inj hrest1 with ⟨hw_eq, hrest2⟩
          rcases Prod.mk.inj hrest2 with ⟨he_eq, had_eq⟩
          have hne_ct : ct_q ≠ ct := by
            intro hct_eq
            have htrue : ((ct_q == ct) && (ad_q == ad)) = true := by simp [hct_eq, had_eq]
            exact Bool.false_ne_true (hne_ct_ad.symm.trans htrue)
          have htag_eq :
              F.encodeProjHash2 d (δ₁ - α * (ξ - ρ * τ₂)).val (ξ - ρ * τ₂).val
                (δ₂ - α * τ₂).val τ₂.val r' parts.1 parts.2.1 =
              F.encode d ((β * (δ₁ + ρ * δ₂) + (γ - α * β) * ξ) • F.generator d) := by
            have hr'_eq : (r' : ZMod (F.order d)) = ρ := hρ
            rw [hv_eq, hw_eq, encodeProjHash2_encode]
            simp only [ZMod.natCast_zmod_val, hr'_eq, projHash2_fiber_challenge_eq]
          have hz_ne :
              (F.encodeProjHash2 d (δ₁ - α * (ξ - ρ * τ₂)).val (ξ - ρ * τ₂).val
                (δ₂ - α * τ₂).val τ₂.val r' parts.1 parts.2.1 == parts.2.2.2) = false := by
            rw [htag_eq, beq_eq_false_iff_ne]
            exact fun hz_eq => hne_ct (by rw [← hreq_eq, hv_eq, hw_eq, he_eq, ← hz_eq])
          simp only [isCramerShoupBadDH, parts, r', skNatOfZMod, hz_ne, Bool.and_false]
        · simp only [Bool.not_eq_true] at hframe
          unfold isCramerShoupBadDH; simp [parts, hframe]
    simp_rw [hfalse]; simp
  · exact F.tsum_and_isCramerShoupBadDH_le H isElem hmem d α
      (fun τ₂ => F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂)
        (δ₂ - α * τ₂) τ₂)
      (!(((ct_q == ct) && (ad_q == ad)) || F.isCramerShoupCollision H d ct_q ad_q ct ad)) ct_q ad_q
      fun β' γ' hγ' => ⟨projHash2QueryFiberEquiv F d hγ' hρ δ₁ δ₂ ξ, fun τ₂ => by
        simp only [skNatOfZMod, ZMod.natCast_zmod_val, projHash2_fiber_query_eq,
          projHash2QueryFiberEquiv_apply, ρ', r', parts]⟩

theorem div_order_le_div_of_le {d : F.Desc} {Q m : ℕ} (hm0 : 0 < m) (hm : m ≤ F.order d) :
    (Q : ℝ≥0) / (F.order d : ℝ≥0) ≤ (Q : ℝ≥0) / (m : ℝ≥0) := by
  have hm_pos : (0 : ℝ≥0) < (m : ℝ≥0) := Nat.cast_pos.mpr hm0
  have hm_le : (m : ℝ≥0) ≤ (F.order d : ℝ≥0) := Nat.cast_le.mpr hm
  gcongr

/-- Phase 1 query bound on honest public keys at security parameter `n`. -/
def HonestPhase1QueryBound {Msg AD : Type} (setup : ℕ → PMF F.Desc)
    (adversary : ADCCA2AdversaryOf Msg AD) (n Q₁ : ℕ) : Prop :=
  ∀ d ∈ (setup n).support, ∀ α δ δ₁ δ₂ : ZMod (F.order d),
    (adversary.choose n
      (F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d))
        (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0))).IsQueryBounded Q₁

/-- Phase 2 query bound on honest Phase 1 states and challenge ciphertexts at parameter `n`. -/
def HonestPhase2QueryBound (hasAD : Bool) {Msg AD : Type}
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (n Q₂ : ℕ) : Prop :=
  ∀ d ∈ (setup n).support, ∀ α β γ δ τ δ₁ δ₂ ξ : ZMod (F.order d),
    ∀ choiceOut ∈ (ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
        (fun req (s : Unit) =>
          pure (F.cramerShoupDHPhase1Reply hasAD H isElem d α δ δ₁ δ₂ req.2, s)))
      (adversary.choose n
        (F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d))
          (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0)))).run ())).support,
    ∀ mElem : F.Carrier d,
      let v := F.encode d (β • F.generator d); let w := F.encode d (γ • F.generator d)
      let e := F.encode d (projHash F d (δ - α * τ) τ (β • F.generator d) (γ • F.generator d) +
        mElem)
      let ad := encodeAD (d, choiceOut.1.1.2)
      let ρ := F.cramerShoupHashMod H d (encBits4 (v, w, e, ad))
      let ct := encBits4 (v, w, e,
        F.encode d ((β * (δ₁ + ρ * δ₂) + (γ - α * β) * ξ) • F.generator d))
      (adversary.guess n choiceOut.1.2 ct).IsQueryBounded Q₂

/-- **Game 3.5** (intermediate hybrid between Game 3 and Game 4 of [BonehShoup2023],
Section 12.5.3, printed pp. 491–492): under the fiber change of variables
`σ = δ - α * τ`, `σ₁ = δ₁ - α * τ₁`, `σ₂ = δ₂ - α * τ₂`, replace Phase 1's decryption oracle
`cramerShoupPhase1Reply` with `cramerShoupDHPhase1Reply` (rejecting non-DH queries in Phase 1). -/
noncomputable def cramerShoupGame3Half
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n; let U := PMF.uniformOfFintype (ZMod (F.order d))
  let α ← U; let β ← U; let γ ← U; let δ ← U; let τ ← U; let δ₁ ← U; let τ₁ ← U; let δ₂ ← U
  let τ₂ ← U
  let sk := F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂
  let u := F.encode d (α • F.generator d); let v := F.encode d (β • F.generator d)
  let w := F.encode d (γ • F.generator d)
  let pk := F.encodeCramerShoupPublicKey d u (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0)
  runStatelessOracle (F.cramerShoupDHPhase1Reply hasAD H isElem d α δ δ₁ δ₂)
    (adversary.choose n pk) fun choice =>
    let m₀ := encodeMsg (d, choice.1.1.1); let m₁ := encodeMsg (d, choice.1.1.2)
    let ad := encodeAD (d, choice.1.2)
    if isElem (d, m₀) && isElem (d, m₁) then
      let m := if bit then m₁ else m₀
      let ct := F.encodeCramerShoupChallenge H d sk v w m ad
      runStatelessOracle (F.cramerShoupCollisionPhase2Reply hasAD H isElem d sk ct ad)
        (adversary.guess n choice.2 ct) PMF.pure
    else
      PMF.pure false

/-- **Game 3 $\to$ Game 3.5 bound**: replacing `cramerShoupPhase1Reply` with
`cramerShoupDHPhase1Reply` changes the game advantage by at most `Q₁ / m` whenever Phase 1 makes at
most `Q₁` queries on every honest public key. -/
theorem advantage_cramerShoupGame3_game3Half_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n Q₁ m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d)
    (hQ₁ : F.HonestPhase1QueryBound setup adversary n Q₁) :
    Game.advantage
      (F.cramerShoupGame3 hasAD encodeMsg encodeAD setup H isElem adversary bit n)
      (F.cramerShoupGame3Half hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      (Q₁ : ℝ≥0) / (m : ℝ≥0) := by
  unfold cramerShoupGame3 cramerShoupGame3Half; simp only [PMF.monad_bind_eq_bind]
  refine advantage_bind_le_of_support (setup n) _ _ fun d hd => ?_
  let U := PMF.uniformOfFintype (ZMod (F.order d))
  refine advantage_bind_le_nnreal _ _ _ fun α =>
    advantage_bind_le_nnreal _ _ _ fun β =>
      advantage_bind_le_nnreal _ _ _ fun γ => ?_
  rw [uniform_sub_mul_bind (F.order d) α]
  refine advantage_bind_le_nnreal _ _ _ fun δ =>
    advantage_bind_le_nnreal _ _ _ fun τ => ?_
  rw [uniform_sub_mul_bind (F.order d) α]
  refine advantage_bind_le_nnreal U _ _ fun δ₁ => ?_
  conv_lhs => enter [1, 2, τ₁]; rw [uniform_sub_mul_bind (F.order d) α]
  simp only [F.encodeCramerShoupPublicKey_fiber_eq]
  rw [advantage_bind_comm U U]
  refine advantage_bind_le_nnreal U _ _ fun δ₂ => ?_
  rw [advantage_bind_comm U U]
  refine advantage_bind_le_nnreal U _ _ fun τ₂ => ?_
  exact (advantage_runStatelessOracle_bind_le U
    (fun τ₁ => F.cramerShoupPhase1Reply hasAD H isElem d
      (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂))
    (F.cramerShoupDHPhase1Reply hasAD H isElem d α δ δ₁ δ₂)
    (fun τ₁ req => F.isCramerShoupBadDH H isElem d α
      (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂)
      (splitCramerShoupQuery hasAD req).1 (splitCramerShoupQuery hasAD req).2)
    _ (hQ₁ d hd α δ δ₁ δ₂)
    (fun τ₁ req hbad =>
      F.cramerShoupPhase1Reply_fiber_eq_of_not_bad hasAD H isElem hmem d α δ τ δ₁ τ₁ δ₂ τ₂ req hbad)
    (fun req => F.tsum_isCramerShoupBadDH_phase1_le H isElem hmem d α δ τ δ₁ δ₂ τ₂
      (splitCramerShoupQuery hasAD req).1 (splitCramerShoupQuery hasAD req).2)).trans
      (F.div_order_le_div_of_le hm0 (hm d hd))

/-- **Game 4** (corresponding to Game 5 of [BonehShoup2023], Section 12.5.3, printed p. 492,
adapted to $\mathcal{E}_{\mathrm{MCS}}$ with associated data): both Phase 1 and Phase 2 decryption
oracles reject any non-DH ciphertext query (`w' != F.smul (d, α.val, v')`) via
`decodeCramerShoupDH`. -/
noncomputable def cramerShoupGame4
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n; let U := PMF.uniformOfFintype (ZMod (F.order d))
  let α ← U; let β ← U; let γ ← U; let δ ← U; let τ ← U; let δ₁ ← U; let τ₁ ← U; let δ₂ ← U
  let τ₂ ← U
  let sk := F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂
  let u := F.encode d (α • F.generator d); let v := F.encode d (β • F.generator d)
  let w := F.encode d (γ • F.generator d)
  let pk := F.encodeCramerShoupPublicKey d u (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0)
  runStatelessOracle (F.cramerShoupDHPhase1Reply hasAD H isElem d α δ δ₁ δ₂)
    (adversary.choose n pk) fun choice =>
    let m₀ := encodeMsg (d, choice.1.1.1); let m₁ := encodeMsg (d, choice.1.1.2)
    let ad := encodeAD (d, choice.1.2)
    if isElem (d, m₀) && isElem (d, m₁) then
      let m := if bit then m₁ else m₀
      let ct := F.encodeCramerShoupChallenge H d sk v w m ad
      runStatelessOracle (F.cramerShoupDHPhase2Reply hasAD H isElem d α δ δ₁ δ₂ ct ad)
        (adversary.guess n choice.2 ct) PMF.pure
    else
      PMF.pure false

/-- **Game 3.5 $\to$ Game 4 bound**: replacing `cramerShoupCollisionPhase2Reply` with
`cramerShoupDHPhase2Reply` changes the game advantage by at most `Q₂ / m` whenever Phase 2 makes at
most `Q₂` queries on every honest Phase 1 state and challenge ciphertext. -/
theorem advantage_cramerShoupGame3Half_game4_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n Q₂ m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d)
    (hQ₂ : F.HonestPhase2QueryBound hasAD encodeAD setup H isElem adversary n Q₂) :
    Game.advantage
      (F.cramerShoupGame3Half hasAD encodeMsg encodeAD setup H isElem adversary bit n)
      (F.cramerShoupGame4 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      (Q₂ : ℝ≥0) / (m : ℝ≥0) := by
  unfold cramerShoupGame3Half cramerShoupGame4; simp only [PMF.monad_bind_eq_bind]
  refine advantage_bind_le_of_support (setup n) _ _ fun d hd => ?_
  let U := PMF.uniformOfFintype (ZMod (F.order d))
  refine advantage_bind_le_nnreal _ _ _ fun α =>
    advantage_bind_le_nnreal _ _ _ fun β =>
      advantage_bind_le_nnreal _ _ _ fun γ => ?_
  refine advantage_bind_le_nnreal _ _ _ fun δ =>
    advantage_bind_le_nnreal _ _ _ fun τ => ?_
  refine advantage_bind_le_nnreal U _ _ fun δ₁ => ?_
  rw [advantage_bind_comm U U]
  refine advantage_bind_le_nnreal U _ _ fun δ₂ => ?_
  have hcomm (k : ZMod (F.order d) → ZMod (F.order d) → ((Msg × Msg) × AD) × List Bool → Game) :
      (U.bind fun τ₁ => U.bind fun τ₂ =>
        runStatelessOracle (F.cramerShoupDHPhase1Reply hasAD H isElem d α δ δ₁ δ₂)
          (adversary.choose n (F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d))
            (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0))) (k τ₁ τ₂)) =
      runStatelessOracle (F.cramerShoupDHPhase1Reply hasAD H isElem d α δ δ₁ δ₂)
        (adversary.choose n (F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d))
          (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0))) fun choice =>
        U.bind fun τ₁ => U.bind fun τ₂ => k τ₁ τ₂ choice := by
    rw [show (fun τ₁ => U.bind fun τ₂ => _) = _ from
      funext fun τ₁ => bind_runStatelessOracle_comm _ _ _ (k τ₁)]
    exact bind_runStatelessOracle_comm _ _ _ _
  rw [hcomm, hcomm]
  refine advantage_runStatelessOracle_le_of_support _ _ _ _ fun choiceOut hchoice => ?_
  by_cases hvalid : (isElem (d, encodeMsg (d, choiceOut.1.1.1.1)) &&
      isElem (d, encodeMsg (d, choiceOut.1.1.1.2))) = true
  · simp only [hvalid, ↓reduceIte]
    have hm_mem : isElem (d, if bit then encodeMsg (d, choiceOut.1.1.1.2)
        else encodeMsg (d, choiceOut.1.1.1.1)) = true := by
      rcases Bool.and_eq_true_iff.mp hvalid with ⟨h0, h1⟩; cases bit <;> assumption
    obtain ⟨mElem, hmElem⟩ := (hmem d _).mp hm_mem
    let v := F.encode d (β • F.generator d); let w := F.encode d (γ • F.generator d)
    let m_msg := if bit then encodeMsg (d, choiceOut.1.1.1.2) else encodeMsg (d, choiceOut.1.1.1.1)
    let ad := encodeAD (d, choiceOut.1.1.2)
    let e := F.add (d, F.encodeProjHash d (δ - α * τ).val τ.val v w, m_msg)
    let ρ := F.cramerShoupHashMod H d (encBits4 (v, w, e, ad))
    let ct₀ (ξ : ZMod (F.order d)) :=
      encBits4 (v, w, e, F.encode d ((β * (δ₁ + ρ * δ₂) + (γ - α * β) * ξ) • F.generator d))
    have hshift_one (f : ZMod (F.order d) → ZMod (F.order d) → Game) :
        (U.bind fun τ₁ => U.bind fun τ₂ => f τ₁ τ₂) =
        U.bind fun ξ => U.bind fun τ₂ => f (ξ - ρ * τ₂) τ₂ := by
      rw [PMF.bind_comm]; conv_rhs => rw [PMF.bind_comm]
      exact congrArg _ (funext fun τ₂ => uniform_sub_bind (F.order d) (ρ * τ₂) (fun τ₁ => f τ₁ τ₂))
    conv_lhs => enter [1]; rw [hshift_one]
    conv_lhs => enter [2]; rw [hshift_one]
    refine advantage_bind_le_nnreal U _ _ fun ξ => ?_
    have hct_eq : ∀ τ₂ : ZMod (F.order d),
        F.encodeCramerShoupChallenge H d
          (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂)
            (δ₂ - α * τ₂) τ₂) v w m_msg ad = ct₀ ξ :=
      fun τ₂ => F.encodeCramerShoupChallenge_fiber_eq H d α β γ δ τ δ₁ δ₂ ξ τ₂ m_msg ad
    dsimp only [v, w, m_msg, ad] at hct_eq; simp_rw [hct_eq]
    have he_eq :
        e = F.encode d
          (projHash F d (δ - α * τ) τ (β • F.generator d) (γ • F.generator d) + mElem) := by
      simp only [e, v, w, m_msg, ← hmElem, encodeProjHash_encode, F.add_encode,
        ZMod.natCast_zmod_val]
    have hq2 : (adversary.guess n choiceOut.1.2 (ct₀ ξ)).IsQueryBounded Q₂ := by
      simpa only [ct₀, v, w, ad, ρ, he_eq] using
        hQ₂ d hd α β γ δ τ δ₁ δ₂ ξ choiceOut hchoice mElem
    exact (advantage_runStatelessOracle_bind_le U
      (fun τ₂ => F.cramerShoupCollisionPhase2Reply hasAD H isElem d
        (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂)
          (δ₂ - α * τ₂) τ₂) (ct₀ ξ) ad)
      (F.cramerShoupDHPhase2Reply hasAD H isElem d α δ δ₁ δ₂ (ct₀ ξ) ad)
      (fun τ₂ req =>
        let q := splitCramerShoupQuery hasAD req
        !(((q.1 == ct₀ ξ) && (q.2 == ad)) || F.isCramerShoupCollision H d q.1 q.2 (ct₀ ξ) ad) &&
          F.isCramerShoupBadDH H isElem d α
            (F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * (ξ - ρ * τ₂)) (ξ - ρ * τ₂)
              (δ₂ - α * τ₂) τ₂) q.1 q.2)
      (fun _ => PMF.pure) hq2
      (fun τ₂ req hbad =>
        F.cramerShoupCollisionPhase2Reply_fiber_eq_of_not_bad hasAD H isElem hmem d
          α δ τ δ₁ (ξ - ρ * τ₂) δ₂ τ₂ (ct₀ ξ) ad req hbad)
      (fun req =>
        F.tsum_isCramerShoupBadDH_phase2_le H isElem hmem d α β γ δ τ δ₁ δ₂ ξ e ad
          (splitCramerShoupQuery hasAD req).1 (splitCramerShoupQuery hasAD req).2)).trans
      (F.div_order_le_div_of_le hm0 (hm d hd))
  · simp only [hvalid, Bool.false_eq_true, ↓reduceIte, PMF.bind_const, Game.advantage_self, zero_le]

/-- **Game 3 $\to$ Game 4 bound** ([BonehShoup2023], Section 12.5.3, equations (12.26)–(12.27),
printed pp. 492–493, using Lemma 12.8, printed p. 488): replacing both Phase 1 and Phase 2
decryption oracles with their DH-restricted counterparts changes the game advantage by at most
`(Q₁ + Q₂) / m`. -/
theorem advantage_cramerShoupGame3_game4_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n Q₁ Q₂ m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d)
    (hQ₁ : F.HonestPhase1QueryBound setup adversary n Q₁)
    (hQ₂ : F.HonestPhase2QueryBound hasAD encodeAD setup H isElem adversary n Q₂) :
    Game.advantage
      (F.cramerShoupGame3 hasAD encodeMsg encodeAD setup H isElem adversary bit n)
      (F.cramerShoupGame4 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      ((Q₁ + Q₂ : ℕ) : ℝ≥0) / (m : ℝ≥0) := by
  refine (Game.advantage_triangle _
    (F.cramerShoupGame3Half hasAD encodeMsg encodeAD setup H isElem adversary bit n) _).trans ?_
  refine (add_le_add
    (F.advantage_cramerShoupGame3_game3Half_le hasAD encodeMsg encodeAD setup H isElem hmem
      adversary bit n Q₁ m hm0 hm hQ₁)
    (F.advantage_cramerShoupGame3Half_game4_le hasAD encodeMsg encodeAD setup H isElem hmem
      adversary bit n Q₂ m hm0 hm hQ₂)).trans_eq ?_
  push_cast; ring

/-- **Game 5** (corresponding to Game 6 of [BonehShoup2023], Section 12.5.3, printed p. 493, adapted
to $\mathcal{E}_{\mathrm{MCS}}$ with associated data): replace the masked challenge component
`e = projHash F d (δ - α * τ) τ v w + m` by a uniform independent group element `ζ • g`, making the
entire experiment independent of the challenge bit `bit`. -/
noncomputable def cramerShoupGame5
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (_bit : Bool) (n : ℕ) : Game := do
  let d ← setup n; let U := PMF.uniformOfFintype (ZMod (F.order d))
  let α ← U; let β ← U; let γ ← U; let δ ← U; let ζ ← U; let δ₁ ← U; let τ₁ ← U; let δ₂ ← U
  let τ₂ ← U
  let u := F.encode d (α • F.generator d); let v := F.encode d (β • F.generator d)
  let w := F.encode d (γ • F.generator d)
  let pk := F.encodeCramerShoupPublicKey d u (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0)
  runStatelessOracle (F.cramerShoupDHPhase1Reply hasAD H isElem d α δ δ₁ δ₂)
    (adversary.choose n pk) fun choice =>
    let m₀ := encodeMsg (d, choice.1.1.1); let m₁ := encodeMsg (d, choice.1.1.2)
    let ad := encodeAD (d, choice.1.2)
    if isElem (d, m₀) && isElem (d, m₁) then
      let e := F.encode d (ζ • F.generator d)
      let r := ofBits (H (d, encBits4 (v, w, e, ad)))
      let z' := F.encodeProjHash2 d (δ₁ - α * τ₁).val τ₁.val (δ₂ - α * τ₂).val τ₂.val r v w
      let ct := encBits4 (v, w, e, z')
      runStatelessOracle (F.cramerShoupDHPhase2Reply hasAD H isElem d α δ δ₁ δ₂ ct ad)
        (adversary.guess n choice.2 ct) PMF.pure
    else
      PMF.pure false

/-- In `cramerShoupGame5`, the challenge bit is unused, so the `false` and `true` experiments are
identical. -/
theorem cramerShoupGame5_false_eq_true
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (n : ℕ) :
    F.cramerShoupGame5 hasAD encodeMsg encodeAD setup H isElem adversary false n =
      F.cramerShoupGame5 hasAD encodeMsg encodeAD setup H isElem adversary true n :=
  rfl

/-- **Game 4 $\to$ Game 5 bound** ([BonehShoup2023], Section 12.5.3, equations (12.23) and (12.28),
printed pp. 492–493, using Lemma 12.6, printed p. 486):
whenever `γ ≠ α * β`, `projHash F d (δ - α * τ) τ (β • g) (γ • g) + m` is uniformly distributed
over `F.Carrier d` by `uniform_projHash_fiber_add` (Lemma 12.6), so `cramerShoupGame4` and
`cramerShoupGame5` differ only on the event `γ = α * β` of probability `1 / F.order d ≤ 1 / m`. -/
theorem advantage_cramerShoupGame4_game5_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage
      (F.cramerShoupGame4 hasAD encodeMsg encodeAD setup H isElem adversary bit n)
      (F.cramerShoupGame5 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      1 / (m : ℝ≥0) := by
  unfold cramerShoupGame4 cramerShoupGame5; simp only [PMF.monad_bind_eq_bind]
  refine advantage_bind_le_of_support (setup n) _ _ fun d hd => ?_
  refine advantage_bind_le_nnreal _ _ _ fun α =>
    advantage_bind_le_nnreal _ _ _ fun β => ?_
  refine (advantage_uniform_bind_of_eq_of_ne (α * β) _ _ fun γ hγ => ?_).trans
    (by simpa only [Nat.cast_one] using F.div_order_le_div_of_le (Q := 1) hm0 (hm d hd))
  refine congrArg _ (funext fun δ => ?_)
  rw [PMF.bind_comm]; conv_rhs => rw [PMF.bind_comm]
  refine congrArg _ (funext fun δ₁ => ?_)
  rw [PMF.bind_comm]; conv_rhs => rw [PMF.bind_comm]
  refine congrArg _ (funext fun τ₁ => ?_)
  rw [PMF.bind_comm]; conv_rhs => rw [PMF.bind_comm]
  refine congrArg _ (funext fun δ₂ => ?_)
  rw [PMF.bind_comm]; conv_rhs => rw [PMF.bind_comm]
  refine congrArg _ (funext fun τ₂ => ?_)
  rw [bind_runStatelessOracle_comm, bind_runStatelessOracle_comm]
  refine congrArg _ (funext fun choice => ?_)
  by_cases hvalid : (isElem (d, encodeMsg (d, choice.1.1.1)) &&
      isElem (d, encodeMsg (d, choice.1.1.2))) = true
  · simp only [hvalid, ↓reduceIte]
    have hm_mem : isElem (d, if bit then encodeMsg (d, choice.1.1.2)
        else encodeMsg (d, choice.1.1.1)) = true := by
      rcases Bool.and_eq_true_iff.mp hvalid with ⟨h0, h1⟩; cases bit <;> assumption
    obtain ⟨mElem, hmElem⟩ := (hmem d _).mp hm_mem
    let v := F.encode d (β • F.generator d); let w := F.encode d (γ • F.generator d)
    let ad := encodeAD (d, choice.1.2)
    let k (e_elem : F.Carrier d) : Game :=
      let e := F.encode d e_elem
      let r := ofBits (H (d, encBits4 (v, w, e, ad)))
      let z' := F.encodeProjHash2 d (δ₁ - α * τ₁).val τ₁.val (δ₂ - α * τ₂).val τ₂.val r v w
      let ct := encBits4 (v, w, e, z')
      runStatelessOracle (F.cramerShoupDHPhase2Reply hasAD H isElem d α δ δ₁ δ₂ ct ad)
        (adversary.guess n choice.2 ct) PMF.pure
    have h4 :
        (fun τ : ZMod (F.order d) =>
          let sk := F.skNatOfZMod d (δ - α * τ) τ (δ₁ - α * τ₁) τ₁ (δ₂ - α * τ₂) τ₂
          let m_msg := if bit then encodeMsg (d, choice.1.1.2) else encodeMsg (d, choice.1.1.1)
          let ct := F.encodeCramerShoupChallenge H d sk v w m_msg ad
          runStatelessOracle (F.cramerShoupDHPhase2Reply hasAD H isElem d α δ δ₁ δ₂ ct ad)
            (adversary.guess n choice.2 ct) PMF.pure) =
        fun τ : ZMod (F.order d) =>
          k (projHash F d (δ - α * τ) τ (β • F.generator d) (γ • F.generator d) + mElem) := by
      funext τ
      simp only [encodeCramerShoupChallenge, skNatOfZMod, v, w, ad, ← hmElem, encodeProjHash_encode,
        F.add_encode, ZMod.natCast_zmod_val, k]
    rw [h4]; exact uniform_projHash_fiber_add F d hγ δ mElem k
  · simp only [hvalid, Bool.false_eq_true, ↓reduceIte]

end Cslib.Crypto.PrimeOrderGroupFamily
