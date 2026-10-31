/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Crypto.Computational.CramerShoup.Scheme
public import Complexity.Crypto.Computational.CramerShoup.Reductions
public import Complexity.Crypto.Computational.DiffieHellman.EncodingBounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Probabilistic.UniformNat
import Complexity.Crypto.Game.Statistical
import Complexity.Crypto.Negligible.Basic
import Complexity.Crypto.Negligible.Dyadic
import Complexity.Probability.PMF
import Complexity.Probability.StatisticalDistance
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# The Cramer–Shoup public-key encryption scheme and 1CCA security under DDH

This module completes the single-challenge adaptive chosen-ciphertext (**1CCA / IND-CCA2** and
**1CCA with associated data**, Definition 12.2, printed p. 468, and Section 12.7, Definition 12.7,
printed pp. 501–502) security proof for the **Multiplicative Cramer–Shoup public-key encryption
scheme** ($\mathcal{E}_{\mathrm{MCS}}$, [Boneh and Shoup, Exercise 12.27, printed
pp. 521–522][BonehShoup2023], over an arbitrary associated-data type `AD : Type` as well as the
associated-data-free specialization) defined in `Complexity.Crypto.Computational.CramerShoup.Scheme`
over a `PrimeOrderGroupFamily`, in the standard model under:
1. the Decisional Diffie–Hellman (`DDH`) assumption,
2. collision resistance (`CollisionResistantFor`) of the $\mathbb{Z}_q$-valued hash family $H'$
   (`cramerShoupHashMod`), and
3. a positive group-order lower bound $m(n) > 0$ with $m(n) \le q$ and negligible inverse order
   $1 / m(n)$,

following the Games 0–6 proof template of [Boneh and Shoup, Section 12.5.3, Theorem 12.9 and
Remark 12.3, printed pp. 488–493][BonehShoup2023].

We first prove the concrete and asymptotic 1CCA bounds for the **ideal exact-uniform PMF** games
(`cramerShoupMsgCCA2Game`, `cramerShoupADGroupCCA2Game`, `cramerShoupADGroupINDCCA2`,
`cramerShoupGroupCCA2Game`, `cramerShoupGroupINDCCA2`, `cramerShoupADCCA2Game`,
`cramerShoupADINDCCA2`, `cramerShoupCCA2Game`, `cramerShoupINDCCA2`), in which key and challenge
exponents are drawn from `PMF.uniformOfFintype (ZMod (F.order d))` and the `42 / 2 ^ n` dyadic loss
arises solely from the `sampleModNat` exponent draws inside the strict-PPT DDH and CRHF reductions.
We then bridge these ideal games to the library's **native strict-PPT PKE 1CCA notions**
(`Encryption.cca2ADGameOn`, `Encryption.INDCCA2ADOn`, `Encryption.cca2GameOn`, and
`Encryption.INDCCA2On`) via `advantage_cca2ADGameOn_cramerShoupADGroupCCA2Game_le` and
`advantage_cca2GameOn_cramerShoupGroupCCA2Game_le` (which account for the additional `8 / 2 ^ n`
per-bit `sampleModNat` approximation loss of `cramerShoupKeyGenProb`, `cramerShoupADEncryptProb`,
and `cramerShoupEncryptProb`), yielding `DDH.indcca2ADOn_cramerShoup` and
`DDH.indcca2On_cramerShoup`.

## Source Statements ([BonehShoup2023], Section 12.5.3 & Exercise 12.27)

Verbatim from [BonehShoup2023], Section 12.5.3 (printed pp. 489–492):

> **Theorem 12.9.** If the DDH assumption holds in $\mathbb{G}$, $\mathcal{E}_s$ is 1CCA secure,
> $H$ is a secure KDF, and $H'$ is collision resistant, then $\mathcal{E}_{\mathrm{CS}}$ is CCA
> secure.
>
> In particular, for every 1CCA adversary $\mathcal{A}$ that attacks $\mathcal{E}_{\mathrm{CS}}$ as
> in Definition 12.2, and makes at most $Q_d$ decryption queries, there exist a DDH adversary
> $\mathcal{B}_{\mathrm{ddh}}$ for $\mathbb{G}$ as in Attack Game 10.6, a 1CCA adversary
> $\mathcal{B}_s$ that attacks $\mathcal{E}_s$ as in Definition 9.6, a KDF adversary
> $\mathcal{B}_{\mathrm{kdf}}$ that attacks $H$ as in Attack Game 11.3, and a collision-finding
> adversary $\mathcal{B}_{\mathrm{cr}}$ that attacks $H'$ as in Attack Game 8.1, where
> $\mathcal{B}_{\mathrm{ddh}}, \mathcal{B}_s, \mathcal{B}_{\mathrm{kdf}}, \mathcal{B}_{\mathrm{cr}}$
> are elementary wrappers around $\mathcal{A}$, such that
> $$\text{1CCAadv}[\mathcal{A}, \mathcal{E}_{\mathrm{CS}}] \le
> 2\left(\text{DDHadv}[\mathcal{B}_{\mathrm{ddh}}, \mathbb{G}] +
> \text{KDFadv}[\mathcal{B}_{\mathrm{kdf}}, H] +
> \text{CRadv}[\mathcal{B}_{\mathrm{cr}}, H'] + \frac{Q_d + 1}{q}\right) +
> \text{1CCAadv}[\mathcal{B}_s, \mathcal{E}_s]. \quad (12.19)$$
> …
> **Game 1.** We replace the lines marked (2) and (3) in Fig. 12.3 as follows:
> $$(2) \qquad z \leftarrow f(v, w)$$
> $$(3) \qquad z' \leftarrow f'(v, w, \rho)$$
> Here, instead of using the auxiliary information that allows us to compute $f$ on $L_u$ and $f'$
> on $L_u \times \mathbb{Z}_q$, we compute them directly, using the secret key $\mathit{sk}$. This
> does not change the result of the computation in any way. Therefore,
> $$\Pr[W_1] = \Pr[W_0]. \quad (12.21)$$
> …
> **Game 2.** We replace the line marked (1) in Fig. 12.3 with
> $$(1) \qquad \gamma \xleftarrow{R} \mathbb{Z}_q$$
> …
> It is easy to see that
> $$|\Pr[W_1] - \Pr[W_2]| \le \text{DDHadv}[\mathcal{B}_{\mathrm{ddh}}, \mathbb{G}] \quad (12.22)$$
> for an efficient DDH adversary $\mathcal{B}_{\mathrm{ddh}}$ …
>
> **Game 3.** We replace the line marked (1) in Fig. 12.3 with
> $$(1) \qquad \gamma \xleftarrow{R} \mathbb{Z}_q \setminus \{\alpha\beta\}$$
> Since the statistical distance between the uniform distribution on all triples and the uniform
> distribution on all non-DH-triples is $1/q$ (see Exercise 10.7), it follows that:
> $$|\Pr[W_2] - \Pr[W_3]| \le \frac{1}{q}. \quad (12.23)$$
>
> **Game 4.** We now play our “CR card”. Let us define $\mathit{Coll}_{u,v}(\hat{v}, \hat{w})$ to
> be true if $(\hat{v}, \hat{w}) \ne (v, w)$ and $H'(\hat{v}, \hat{w}) = H'(v, w)$, and to be
> false, otherwise. In this game, we “widen” the rejection rule at line (5), replacing it with
> $$(5) \qquad \text{if } \mathit{Coll}_{u,v}(\hat{u}, \hat{v}) \text{ or }
>   z' \ne f'(\hat{v}, \hat{w}, \hat{\rho})$$
> Let $Z_4$ be the event that in Game 4, some decryption query, which would not have triggered the
> rejection rule of Game 3, does trigger the wider rejection rule in Game 4. Clearly, Games 3 and 4
> proceed identically unless event $Z_4$ occurs. By the Difference Lemma, we have
> $$|\Pr[W_3] - \Pr[W_4]| \le \Pr[Z_4]. \quad (12.24)$$
> It should be clear that
> $$\Pr[Z_4] \le \text{CRadv}[\mathcal{B}_{\mathrm{cr}}, H']. \quad (12.25)$$
> for an efficient collision-finding adversary $\mathcal{B}_{\mathrm{cr}}$. Indeed, adversary
> $\mathcal{B}_{\mathrm{cr}}$ just plays Game 4 and waits for the event $Z_4$ to happen.

Verbatim from [BonehShoup2023], Exercise 12.27 (printed pp. 521–522):
> … Show that $\mathcal{E}_{\mathrm{MCS}}$ is CCA secure, provided $H'$ is collision resistant and
> the DDH assumption holds for $\mathbb{G}$.

## Scope and Quantitative Adaptation

* **Associated data $\mathcal{D}$** ([BonehShoup2023], Section 12.7, Definition 12.7, printed
  pp. 501–502, and Exercise 12.27, printed pp. 521–522) and **single-challenge 1CCA
  (`Definition 12.2` / `Definition 12.7`)**.
* **Adaptation of Game 4 from $\mathcal{E}_{\mathrm{CS}}$ to $\mathcal{E}_{\mathrm{MCS}}$**: in
  Theorem 12.9 ($\mathcal{E}_{\mathrm{CS}}$), $H'$ hashes the pair $(v, w)$ and
  $\mathit{Coll}_{u,v}(\hat{v}, \hat{w})$ tests $(\hat{v}, \hat{w}) \ne (v, w) \land
  H'(\hat{v}, \hat{w}) = H'(v, w)$. In Multiplicative Cramer–Shoup $\mathcal{E}_{\mathrm{MCS}}$
  with associated data (Exercise 12.27, printed pp. 521–522), $H'$ hashes the 4-tuple
  $(v, w, e, d) \in \mathbb{G}^3 \times \mathcal{D}$ (`encBits4`), so the Game 4 collision
  predicate tests $(\hat{v}, \hat{w}, \hat{e}, \hat{d}) \ne (v, w, e, d) \land
  H'(\hat{v}, \hat{w}, \hat{e}, \hat{d}) = H'(v, w, e, d)$ (while Phase 2 decryption rejects the
  full challenge pair $((\hat{v}, \hat{w}, \hat{e}, \hat{z}'), \hat{d}) = ((v, w, e, z'), d)$).
* **Ideal exact-uniform PMF games vs. native `Encryption.INDCCA2ADOn` / `Encryption.INDCCA2On`**:
  `cramerShoupMsgCCA2Game`, `cramerShoupADGroupCCA2Game`, `cramerShoupADGroupINDCCA2`,
  `cramerShoupGroupCCA2Game`, `cramerShoupGroupINDCCA2`, `cramerShoupADCCA2Game`,
  `cramerShoupADINDCCA2`, `cramerShoupCCA2Game`, and `cramerShoupINDCCA2` are **ideal exact-uniform
  PMF** 1CCA experiments and security definitions, in which the challenger samples exponents from
  `PMF.uniformOfFintype (ZMod (F.order d))`. In `advantage_cramerShoupADGroupCCA2Game_le` and
  `advantage_cramerShoupGroupCCA2Game_le` (original quantitative adaptations of `(12.19)` to
  $\mathcal{E}_{\mathrm{MCS}}$ in the uniform strict-PPT model), the two fixed-bit DDH
  distinguishers and two fixed-bit collision finders contribute `42 / 2 ^ n` from their internal
  `sampleModNat` exponent draws, and `(2 * Q₁ n + 2 * Q₂ n + 2) / m` combines the non-DH triple
  exclusion (`1 / m`) and the adaptive Lemma 12.8 bound (`(Q₁ n + Q₂ n) / m`) across `bit = false`
  and `bit = true`. The **native strict-PPT** security theorems `DDH.indcca2ADOn_cramerShoup` and
  `DDH.indcca2On_cramerShoup` instantiate `Encryption.INDCCA2ADOn` and `Encryption.INDCCA2On`,
  bridging from `cramerShoupKeyGenProb`, `cramerShoupADEncryptProb`, and `cramerShoupEncryptProb`
  to the ideal games with an additional `8 / 2 ^ n` statistical loss per challenge bit (`16 / 2 ^ n`
  across both bits).
* **Group-order growth premise**: the asymptotic theorems assume a positive lower bound `m : ℕ → ℕ`
  on the group order `F.order` with `Negligible (fun n => (1 / m n : ℝ≥0))` so that the
  information-theoretic projective-hash and non-DH-triple terms `(2 * Q₁ n + 2 * Q₂ n + 2) / m n`
  are negligible for polynomial query bounds `Q₁, Q₂`.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM ProjectiveHash Encryption Game
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)


/-- The **ideal exact-uniform PMF** single-challenge 1CCA experiment for Multiplicative Cramer–Shoup
parameterized by `hasAD : Bool`, a message-to-group-word encoding `encodeMsg : F.Desc × Msg →
List Bool`, and an associated-data encoding `encodeAD : F.Desc × AD → List Bool`
([BonehShoup2023], Section 12.1, Attack Game 12.1 and Definition 12.2, printed pp. 467–468; Section
12.7, Definition 12.7, printed pp. 501–502; and Exercise 12.27, printed pp. 521–522; Game 0 of
Section 12.5.3, printed pp. 490–491). Key and challenge exponents are sampled from the exact uniform
distribution `PMF.uniformOfFintype (ZMod (F.order d))`. -/
noncomputable def cramerShoupMsgCCA2Game
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let pkVal := F.cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂
  let pk := F.encodeCramerShoupPublicKeyValues d pkVal
  let choiceOut ← ProbComp.eval ((OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())
  let choice := choiceOut.1
  let m₀ := encodeMsg (d, choice.1.1.1)
  let m₁ := encodeMsg (d, choice.1.1.2)
  let ad := encodeAD (d, choice.1.2)
  if isElem (d, m₀) && isElem (d, m₁) then
    let m := if bit then m₁ else m₀
    let β ← PMF.uniformOfFintype (ZMod (F.order d))
    let ct := F.encodeCramerShoupEncrypt H d
      (F.encode d pkVal.1, F.encode d pkVal.2.1, F.encode d pkVal.2.2.1, F.encode d pkVal.2.2.2)
      m ad β.val
    let guessOut ← ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
        (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct ad))
      (adversary.guess n choice.2 ct)).run ())
    return guessOut.1
  else
    return false

/-- The **ideal exact-uniform PMF** single-challenge 1CCA experiment with associated data for
Multiplicative Cramer–Shoup over encoded group-element messages (`Msg = List Bool`, `encodeMsg =
Prod.snd`) and associated-data type `AD` encoded via `encAD : AD ↪ List Bool`. -/
noncomputable abbrev cramerShoupADGroupCCA2Game
    {AD : Type} (encAD : AD ↪ List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (adversary : WordADCCA2Adversary AD)
    (bit : Bool) (n : ℕ) : Game :=
  F.cramerShoupMsgCCA2Game true Prod.snd (fun p => encAD p.2) setup H isElem adversary bit n

/-- Ideal exact-uniform PMF single-challenge 1CCA security with associated data of Multiplicative
Cramer–Shoup over encoded group-element messages (`WordADCCA2Adversary AD`). -/
def cramerShoupADGroupINDCCA2
    {AD : Type} (encAD : AD ↪ List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) : Prop :=
  Game.Indistinguishable
    (fun adversary n => F.cramerShoupADGroupCCA2Game encAD setup H isElem adversary false n)
    (fun adversary n => F.cramerShoupADGroupCCA2Game encAD setup H isElem adversary true n)
    (WordADCCA2Adversary.IsPPT encAD)

/-- The **ideal exact-uniform PMF** single-challenge 1CCA experiment for Multiplicative Cramer–Shoup
over encoded group-element messages (`Msg = List Bool`, `encodeMsg = Prod.snd`, associated-data-free
specialization `ad = []`), enforcing the group-membership challenge admissibility check
`isElem (d, m₀) && isElem (d, m₁)`. -/
noncomputable abbrev cramerShoupGroupCCA2Game
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (adversary : WordCCA2Adversary)
    (bit : Bool) (n : ℕ) : Game :=
  F.cramerShoupMsgCCA2Game false Prod.snd (fun _ => []) setup H isElem adversary.toADUnit bit n

/-- Ideal exact-uniform PMF single-challenge 1CCA security of Multiplicative Cramer–Shoup over
encoded group-element messages (`WordCCA2Adversary`). -/
def cramerShoupGroupINDCCA2
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) : Prop :=
  Game.Indistinguishable
    (fun adversary n => F.cramerShoupGroupCCA2Game setup H isElem adversary false n)
    (fun adversary n => F.cramerShoupGroupCCA2Game setup H isElem adversary true n)
    WordCCA2Adversary.IsPPT

/-- The **ideal exact-uniform PMF** single-challenge 1CCA experiment with associated data for
Multiplicative Cramer–Shoup over single-bit messages (`Msg = Bool`, embedded into `F.Carrier d` via
`F.encodeBit`) and associated-data type `AD` encoded via `encAD : AD ↪ List Bool`. -/
noncomputable abbrev cramerShoupADCCA2Game
    {AD : Type} (encAD : AD ↪ List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (adversary : ADCCA2Adversary AD)
    (bit : Bool) (n : ℕ) : Game :=
  F.cramerShoupMsgCCA2Game true (fun p => F.encodeBit p.1 p.2) (fun p => encAD p.2)
    setup H isElem adversary bit n

/-- Ideal exact-uniform PMF single-challenge 1CCA security with associated data of Multiplicative
Cramer–Shoup over single-bit messages (`ADCCA2Adversary AD`). -/
def cramerShoupADINDCCA2
    {AD : Type} (encAD : AD ↪ List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) : Prop :=
  Game.Indistinguishable
    (fun adversary n => F.cramerShoupADCCA2Game encAD setup H isElem adversary false n)
    (fun adversary n => F.cramerShoupADCCA2Game encAD setup H isElem adversary true n)
    (ADCCA2Adversary.IsPPT encAD)

/-- The **ideal exact-uniform PMF** single-challenge 1CCA experiment for Multiplicative Cramer–Shoup
over single-bit messages (`Msg = Bool`, embedded into `F.Carrier d` via `F.encodeBit`,
associated-data-free specialization `ad = []`). -/
noncomputable abbrev cramerShoupCCA2Game
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (adversary : CCA2Adversary) (bit : Bool) (n : ℕ) : Game :=
  F.cramerShoupMsgCCA2Game false (fun p => F.encodeBit p.1 p.2) (fun _ => [])
    setup H isElem adversary.toADUnit bit n

/-- Ideal exact-uniform PMF single-challenge 1CCA security of Multiplicative Cramer–Shoup over
single-bit messages (`CCA2Adversary`). -/
def cramerShoupINDCCA2
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) : Prop :=
  Game.Indistinguishable
    (fun adversary n => F.cramerShoupCCA2Game setup H isElem adversary false n)
    (fun adversary n => F.cramerShoupCCA2Game setup H isElem adversary true n)
    CCA2Adversary.IsPPT

/-- **Game 1** ([BonehShoup2023], Section 12.5.3, printed p. 490, adapted to
$\mathcal{E}_{\mathrm{MCS}}$ with associated data): draw `(α, β)` and `sk` uniformly from `ZMod q`,
and compute the challenge ciphertext from `(v, w) = (β • g, (α * β) • g)` using the secret key via
`encodeCramerShoupChallenge`. -/
noncomputable def cramerShoupGame1
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let u := F.encode d (α • F.generator d)
  let v := F.encode d (β • F.generator d)
  let w := F.encode d ((α * β) • F.generator d)
  let pk := F.encodeCramerShoupPublicKey d u sk
  let choiceOut ← ProbComp.eval ((OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())
  let choice := choiceOut.1
  let m₀ := encodeMsg (d, choice.1.1.1)
  let m₁ := encodeMsg (d, choice.1.1.2)
  let ad := encodeAD (d, choice.1.2)
  if isElem (d, m₀) && isElem (d, m₁) then
    let m := if bit then m₁ else m₀
    let ct := F.encodeCramerShoupChallenge H d sk v w m ad
    let guessOut ← ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
        (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct ad))
      (adversary.guess n choice.2 ct)).run ())
    return guessOut.1
  else
    return false

/-- **Game 0 = Game 1** ([BonehShoup2023], Section 12.5.3, equation (12.21), printed p. 490):
computing the challenge ciphertext from `(v, w) = (β • g, (α * β) • g)` using the secret key
produces the exact same distribution as public-key encryption. -/
theorem cramerShoupMsgCCA2Game_eq_game1
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) :
    F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary bit n =
      F.cramerShoupGame1 hasAD encodeMsg encodeAD setup H isElem adversary bit n := by
  simp only [cramerShoupMsgCCA2Game, cramerShoupGame1, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, encodeCramerShoupPublicKey_encode, skNatOfZMod,
    ZMod.natCast_zmod_val, encodeCramerShoupEncrypt_publicKey_eq_challenge]
  refine congrArg _ (funext fun d => congrArg _ (funext fun α => ?_))
  conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))]
  refine congrArg _ (funext fun σ => ?_)
  conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))]
  refine congrArg _ (funext fun τ => ?_)
  conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))]
  refine congrArg _ (funext fun σ₁ => ?_)
  conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))]
  refine congrArg _ (funext fun τ₁ => ?_)
  conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))]
  refine congrArg _ (funext fun σ₂ => ?_)
  conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))]
  refine congrArg _ (funext fun τ₂ => ?_)
  conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))]
  refine congrArg _ (funext fun choiceOut => ?_)
  by_cases h : (isElem (d, encodeMsg (d, choiceOut.1.1.1.1)) &&
      isElem (d, encodeMsg (d, choiceOut.1.1.1.2))) = true
  · simp only [h, ↓reduceIte]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, PMF.bind_const]

/-- **Game 2** ([BonehShoup2023], Section 12.5.3, printed p. 490, adapted to
$\mathcal{E}_{\mathrm{MCS}}$ with associated data): replace the Diffie–Hellman challenge pair
`(v, w) = (β • g, (α * β) • g)` by an independent random pair `(v, w) = (β • g, γ • g)` with
uniform `γ : ZMod (F.order d)`. -/
noncomputable def cramerShoupGame2
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let u := F.encode d (α • F.generator d)
  let v := F.encode d (β • F.generator d)
  let w := F.encode d (γ • F.generator d)
  let pk := F.encodeCramerShoupPublicKey d u sk
  let choiceOut ← ProbComp.eval ((OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())
  let choice := choiceOut.1
  let m₀ := encodeMsg (d, choice.1.1.1)
  let m₁ := encodeMsg (d, choice.1.1.2)
  let ad := encodeAD (d, choice.1.2)
  if isElem (d, m₀) && isElem (d, m₁) then
    let m := if bit then m₁ else m₀
    let ct := F.encodeCramerShoupChallenge H d sk v w m ad
    let guessOut ← ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
        (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct ad))
      (adversary.guess n choice.2 ct)).run ())
    return guessOut.1
  else
    return false

private theorem advantage_ddhRealGame_cramerShoupGame1_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) :
    Game.advantage
      (F.ddhRealGame setup
        (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit) n)
      (F.cramerShoupGame1 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      6 / 2 ^ n := by
  unfold ddhRealGame cramerShoupGame1 cramerShoupMsgToDDHDistinguisher
  simp only [ProbComp.eval_bind, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
  refine advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun α => ?_
  refine advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun β => ?_
  refine F.advantage_bind_sampleCramerShoupSK_le n d _ _ fun s t s₁ t₁ s₂ t₂ => ?_
  rw [F.encodeCramerShoupPublicKey_eq_skNatOfZMod d α ((s, t), ((s₁, t₁), (s₂, t₂))),
    F.cramerShoupPhase1Oracle_eq_skNatOfZMod hasAD H isElem hmem d
      ((s, t), ((s₁, t₁), (s₂, t₂)))]
  refine congrArg _ (funext fun choiceOut => ?_)
  by_cases h : (isElem (d, encodeMsg (d, choiceOut.1.1.1.1)) &&
      isElem (d, encodeMsg (d, choiceOut.1.1.1.2))) = true
  · simp only [h, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure]
    rw [F.encodeCramerShoupChallenge_eq_skNatOfZMod H d ((s, t), ((s₁, t₁), (s₂, t₂))),
      F.cramerShoupPhase2Oracle_eq_skNatOfZMod hasAD H isElem hmem d
        ((s, t), ((s₁, t₁), (s₂, t₂)))]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]

private theorem advantage_ddhIdealGame_cramerShoupGame2_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) :
    Game.advantage
      (F.ddhIdealGame setup
        (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit) n)
      (F.cramerShoupGame2 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      6 / 2 ^ n := by
  unfold ddhIdealGame cramerShoupGame2 cramerShoupMsgToDDHDistinguisher
  simp only [ProbComp.eval_bind, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
  refine advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun α => ?_
  refine advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun β => ?_
  refine advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun γ => ?_
  refine F.advantage_bind_sampleCramerShoupSK_le n d _ _ fun s t s₁ t₁ s₂ t₂ => ?_
  rw [F.encodeCramerShoupPublicKey_eq_skNatOfZMod d α ((s, t), ((s₁, t₁), (s₂, t₂))),
    F.cramerShoupPhase1Oracle_eq_skNatOfZMod hasAD H isElem hmem d
      ((s, t), ((s₁, t₁), (s₂, t₂)))]
  refine congrArg _ (funext fun choiceOut => ?_)
  by_cases h : (isElem (d, encodeMsg (d, choiceOut.1.1.1.1)) &&
      isElem (d, encodeMsg (d, choiceOut.1.1.1.2))) = true
  · simp only [h, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure]
    rw [F.encodeCramerShoupChallenge_eq_skNatOfZMod H d ((s, t), ((s₁, t₁), (s₂, t₂))),
      F.cramerShoupPhase2Oracle_eq_skNatOfZMod hasAD H isElem hmem d
        ((s, t), ((s₁, t₁), (s₂, t₂)))]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]

private theorem advantage_four_le (g₁ g₂ g₃ g₄ : Game) {n : ℕ}
    (h₁ : Game.advantage g₂ g₁ ≤ 6 / 2 ^ n) (h₂ : Game.advantage g₃ g₄ ≤ 6 / 2 ^ n) :
    Game.advantage g₁ g₄ ≤ Game.advantage g₂ g₃ + 12 / 2 ^ n := by
  have htri1 := Game.advantage_triangle g₁ g₂ g₄
  have htri2 := Game.advantage_triangle g₂ g₃ g₄
  rw [Game.advantage_comm g₁ g₂] at htri1
  exact ((htri1.trans (add_le_add le_rfl htri2)).trans
    (add_le_add h₁ (add_le_add le_rfl h₂))).trans_eq (by ring)

/-- **Game 1 $\to$ Game 2 bound** ([BonehShoup2023], Section 12.5.3, equation (12.22), printed
p. 492): the distinguishing advantage between `cramerShoupGame1` and `cramerShoupGame2` is at
most the DDH advantage of `cramerShoupMsgToDDHDistinguisher` plus `12 / 2 ^ n` (six approximate
`sampleModNat` secret-key exponent draws in `ddhRealGame` and six in `ddhIdealGame`). -/
theorem advantage_cramerShoupGame1_game2_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) :
    Game.advantage
      (F.cramerShoupGame1 hasAD encodeMsg encodeAD setup H isElem adversary bit n)
      (F.cramerShoupGame2 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit) n)
        (F.ddhIdealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      12 / 2 ^ n :=
  advantage_four_le _ _ _ _
    (F.advantage_ddhRealGame_cramerShoupGame1_le hasAD encodeMsg encodeAD setup H isElem hmem
      adversary bit n)
    (F.advantage_ddhIdealGame_cramerShoupGame2_le hasAD encodeMsg encodeAD setup H isElem hmem
      adversary bit n)

/-- Exact-exponent collision game matching the collision event between `cramerShoupGame2` and
`cramerShoupGame3`. -/
private noncomputable def cramerShoupExactCollisionGame
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let u := F.encode d (α • F.generator d)
  let v := F.encode d (β • F.generator d)
  let w := F.encode d (γ • F.generator d)
  let pk := F.encodeCramerShoupPublicKey d u sk
  let choiceOut ← ProbComp.eval ((OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())
  let choice := choiceOut.1
  let m₀ := encodeMsg (d, choice.1.1.1)
  let m₁ := encodeMsg (d, choice.1.1.2)
  let ad := encodeAD (d, choice.1.2)
  if isElem (d, m₀) && isElem (d, m₁) then
    let m := if bit then m₁ else m₀
    let ct := F.encodeCramerShoupChallenge H d sk v w m ad
    runFinderOracle (F.cramerShoupCollisionPhase2Reply hasAD H isElem d sk ct ad)
      (fun req =>
        let q := splitCramerShoupQuery hasAD req
        F.isCramerShoupCollision H d q.1 q.2 ct ad)
      (fun req =>
        let q := splitCramerShoupQuery hasAD req
        extractCramerShoupTuple q.1 q.2)
      (adversary.guess n choice.2 ct) none
      (fun cand => isCollisionFor (F.cramerShoupHashMod H) (fun _ _ _ => true) n d
        cand (extractCramerShoupTuple ct ad))
  else
    return false

private theorem advantage_cramerShoupGame2_game3_le_exactCollision
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) :
    Game.advantage
      (F.cramerShoupGame2 hasAD encodeMsg encodeAD setup H isElem adversary bit n)
      (F.cramerShoupGame3 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      Game.succProbability
        (F.cramerShoupExactCollisionGame hasAD encodeMsg encodeAD setup H isElem adversary
          bit n) := by
  unfold cramerShoupGame2 cramerShoupGame3 cramerShoupExactCollisionGame
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine advantage_bind_le_succProbability_bind (setup n) _ _ _ fun d => ?_
  refine bind_apply_le_add_bind_apply _ _ _ _ true fun α => ?_
  refine bind_apply_le_add_bind_apply _ _ _ _ true fun β => ?_
  refine bind_apply_le_add_bind_apply _ _ _ _ true fun γ => ?_
  refine bind_apply_le_add_bind_apply _ _ _ _ true fun σ => ?_
  refine bind_apply_le_add_bind_apply _ _ _ _ true fun τ => ?_
  refine bind_apply_le_add_bind_apply _ _ _ _ true fun σ₁ => ?_
  refine bind_apply_le_add_bind_apply _ _ _ _ true fun τ₁ => ?_
  refine bind_apply_le_add_bind_apply _ _ _ _ true fun σ₂ => ?_
  refine bind_apply_le_add_bind_apply _ _ _ _ true fun τ₂ => ?_
  refine bind_apply_le_add_bind_apply _ _ _ _ true fun choiceOut => ?_
  by_cases h : (isElem (d, encodeMsg (d, choiceOut.1.1.1.1)) &&
      isElem (d, encodeMsg (d, choiceOut.1.1.1.2))) = true
  · simp only [h, ↓reduceIte]
    let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
    let v := F.encode d (β • F.generator d)
    let w := F.encode d (γ • F.generator d)
    let m := if bit then encodeMsg (d, choiceOut.1.1.1.2) else encodeMsg (d, choiceOut.1.1.1.1)
    let ad := encodeAD (d, choiceOut.1.1.2)
    let ct := F.encodeCramerShoupChallenge H d sk v w m ad
    have hrun :
        (ProbComp.eval ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct ad))
          (adversary.guess n choiceOut.1.2 ct)).run ())).bind
            (fun guessOut => PMF.pure guessOut.1) =
        runStatelessOracle (F.cramerShoupPhase2Reply hasAD H isElem d sk ct ad)
          (adversary.guess n choiceOut.1.2 ct) PMF.pure := rfl
    rw [hrun]
    refine runStatelessOracle_le_runFinderOracle
      (F.cramerShoupPhase2Reply hasAD H isElem d sk ct ad)
      (F.cramerShoupCollisionPhase2Reply hasAD H isElem d sk ct ad)
      (fun req =>
        let q := splitCramerShoupQuery hasAD req
        F.isCramerShoupCollision H d q.1 q.2 ct ad)
      (fun req =>
        let q := splitCramerShoupQuery hasAD req
        extractCramerShoupTuple q.1 q.2)
      (fun cand => isCollisionFor (F.cramerShoupHashMod H) (fun _ _ _ => true) n d
        cand (extractCramerShoupTuple ct ad))
      (fun req hbad => by
        simp [cramerShoupPhase2Reply, cramerShoupCollisionPhase2Reply, hbad])
      (fun req hbad => by
        rw [← F.isCramerShoupCollision_eq_isCollisionFor H n d _ _ ct ad]; exact hbad)
      (adversary.guess n choiceOut.1.2 ct) PMF.pure true
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact ⟨le_self_add, le_self_add⟩

private theorem succProbability_cramerShoupExactCollisionGame_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) :
    Game.succProbability
      (F.cramerShoupExactCollisionGame hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      9 / 2 ^ n := by
  let C := F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary bit
  have hadv :
      Game.advantage
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true) C n)
        (F.cramerShoupExactCollisionGame hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      9 / 2 ^ n := by
    unfold collisionGameFor cramerShoupExactCollisionGame C cramerShoupMsgToCollisionFinder
    simp only [ProbComp.eval_bind, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
      F.smul_encode]
    refine advantage_bind_le_nnreal (setup n) _ _ fun d => ?_
    let kZMod (α β γ σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) : Game :=
      let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
      let u := F.encode d (α • F.generator d)
      let v := F.encode d (β • F.generator d)
      let w := F.encode d (γ • F.generator d)
      let pk := F.encodeCramerShoupPublicKey d u sk
      (ProbComp.eval ((OracleComp.interpret
        (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
          (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
        (adversary.choose n pk)).run ())).bind fun choiceOut =>
        let choice := choiceOut.1
        if isElem (d, encodeMsg (d, choice.1.1.1)) &&
            isElem (d, encodeMsg (d, choice.1.1.2)) then
          let m := if bit then encodeMsg (d, choice.1.1.2) else encodeMsg (d, choice.1.1.1)
          let ad := encodeAD (d, choice.1.2)
          let ct := F.encodeCramerShoupChallenge H d sk v w m ad
          runFinderOracle (F.cramerShoupCollisionPhase2Reply hasAD H isElem d sk ct ad)
            (fun req =>
              let q := splitCramerShoupQuery hasAD req
              F.isCramerShoupCollision H d q.1 q.2 ct ad)
            (fun req =>
              let q := splitCramerShoupQuery hasAD req
              extractCramerShoupTuple q.1 q.2)
            (adversary.guess n choice.2 ct) none
            (fun cand => isCollisionFor (F.cramerShoupHashMod H) (fun _ _ _ => true) n d
              cand (extractCramerShoupTuple ct ad))
        else PMF.pure false
    let kTriple (α β γ : ZMod (F.order d)) : Game :=
      (ProbComp.eval (F.sampleCramerShoupSK n d)).bind fun sk =>
        let u := F.encode d (α • F.generator d)
        let v := F.encode d (β • F.generator d)
        let w := F.encode d (γ • F.generator d)
        let pk := F.encodeCramerShoupPublicKey d u sk
        (ProbComp.eval ((OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
          (adversary.choose n pk)).run ())).bind fun choiceOut =>
          let choice := choiceOut.1
          (ProbComp.eval
            (if isElem (d, encodeMsg (d, choice.1.1.1)) &&
                isElem (d, encodeMsg (d, choice.1.1.2)) then
              let m := if bit then encodeMsg (d, choice.1.1.2) else encodeMsg (d, choice.1.1.1)
              let ad := encodeAD (d, choice.1.2)
              let ct := F.encodeCramerShoupChallenge H d sk v w m ad
              ((OracleComp.interpret
                (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
                  (F.cramerShoupCollisionPhase2Oracle hasAD H isElem d sk ct ad))
                (adversary.guess n choice.2 ct)).run none) >>= fun out =>
                let target := extractCramerShoupTuple ct ad
                pure (out.2.getD target, target)
            else pure ([], []))).bind fun pair =>
            PMF.pure
              (isCollisionFor (F.cramerShoupHashMod H) (fun _ _ _ => true) n d pair.1 pair.2)
    have hstep1 := F.advantage_bind_sampleCramerShoupTripleExponents_le n d kTriple
    have hstep2 :
        Game.advantage
          ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
              (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ => kTriple α β γ)
          ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
              (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
                (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
                  (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ =>
                    (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ₁ =>
                      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ₁ =>
                        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ₂ =>
                          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ₂ =>
                            kZMod α β γ σ τ σ₁ τ₁ σ₂ τ₂) ≤
          6 / 2 ^ n := by
      refine advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun α => ?_
      refine advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun β => ?_
      refine advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun γ => ?_
      refine F.advantage_bind_sampleCramerShoupSK_le n d _ (kZMod α β γ)
        fun s t s₁ t₁ s₂ t₂ => ?_
      dsimp only [kZMod]
      rw [F.encodeCramerShoupPublicKey_eq_skNatOfZMod d α ((s, t), ((s₁, t₁), (s₂, t₂))),
        F.cramerShoupPhase1Oracle_eq_skNatOfZMod hasAD H isElem hmem d
          ((s, t), ((s₁, t₁), (s₂, t₂)))]
      refine congrArg _ (funext fun choiceOut => ?_)
      by_cases h : (isElem (d, encodeMsg (d, choiceOut.1.1.1.1)) &&
          isElem (d, encodeMsg (d, choiceOut.1.1.1.2))) = true
      · simp only [h, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind,
          PMF.pure_bind]
        rw [F.encodeCramerShoupChallenge_eq_skNatOfZMod H d ((s, t), ((s₁, t₁), (s₂, t₂))),
          F.cramerShoupCollisionPhase2Oracle_eq_skNatOfZMod hasAD H isElem hmem d
            ((s, t), ((s₁, t₁), (s₂, t₂)))]
        unfold runFinderOracle cramerShoupCollisionPhase2Oracle
        refine congrArg _ (funext fun out => ?_)
        cases out.2 with
        | none => simp
        | some cand => rfl
      · simp only [h, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind]
        rfl
    exact ((Game.advantage_triangle _ _ _).trans (add_le_add hstep1 hstep2)).trans_eq (by ring)
  have htri := Game.advantage_triangle
    (F.cramerShoupExactCollisionGame hasAD encodeMsg encodeAD setup H isElem adversary bit n)
    (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true) C n)
    (PMF.pure false)
  rw [Game.advantage_pure_false, Game.advantage_pure_false,
    Game.advantage_comm
      (F.cramerShoupExactCollisionGame hasAD encodeMsg encodeAD setup H isElem adversary bit n),
    add_comm] at htri
  exact htri.trans (add_le_add le_rfl hadv)

/-- **Game 2 $\to$ Game 3 bound** ([BonehShoup2023], Section 12.5.3, equations (12.24)–(12.25),
printed p. 492, adapted to $\mathcal{E}_{\mathrm{MCS}}$ with associated data): the distinguishing
advantage between `cramerShoupGame2` and `cramerShoupGame3` is bounded by the collision-finding
success probability of `cramerShoupMsgToCollisionFinder` plus `9 / 2 ^ n` (from the nine approximate
`sampleModNat` exponent draws in `cramerShoupMsgToCollisionFinder`). -/
theorem advantage_cramerShoupGame2_game3_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) :
    Game.advantage
      (F.cramerShoupGame2 hasAD encodeMsg encodeAD setup H isElem adversary bit n)
      (F.cramerShoupGame3 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      9 / 2 ^ n :=
  (F.advantage_cramerShoupGame2_game3_le_exactCollision
    hasAD encodeMsg encodeAD setup H isElem adversary bit n).trans
    (F.succProbability_cramerShoupExactCollisionGame_le
      hasAD encodeMsg encodeAD setup H isElem hmem adversary bit n)

/-! ### Concrete and asymptotic 1CCA security bounds ([BonehShoup2023], Theorem 12.9 & Ex. 12.27) -/

/-- **Combined Game 0 $\to$ Game 5 bound for a single challenge bit**: under honest query bounds
`(Q₁, Q₂)`, the distinguishing advantage between `cramerShoupMsgCCA2Game` and `cramerShoupGame5` is
at most the DDH advantage of `cramerShoupMsgToDDHDistinguisher` plus the collision-finding success
probability of `cramerShoupMsgToCollisionFinder` plus `(Q₁ + Q₂ + 1) / m + 21 / 2 ^ n`. -/
theorem advantage_cramerShoupMsgCCA2Game_game5_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n Q₁ Q₂ m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d)
    (hQ₁ : F.HonestPhase1QueryBound setup adversary n Q₁)
    (hQ₂ : F.HonestPhase2QueryBound hasAD encodeAD setup H isElem adversary n Q₂) :
    Game.advantage
      (F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary bit n)
      (F.cramerShoupGame5 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit) n)
        (F.ddhIdealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      ((Q₁ + Q₂ + 1 : ℕ) : ℝ≥0) / (m : ℝ≥0) +
      21 / 2 ^ n := by
  rw [F.cramerShoupMsgCCA2Game_eq_game1]
  have h12 := F.advantage_cramerShoupGame1_game2_le hasAD encodeMsg encodeAD setup H isElem hmem
    adversary bit n
  have h23 := F.advantage_cramerShoupGame2_game3_le hasAD encodeMsg encodeAD setup H isElem hmem
    adversary bit n
  have h34 := F.advantage_cramerShoupGame3_game4_le hasAD encodeMsg encodeAD setup H isElem hmem
    adversary bit n Q₁ Q₂ m hm0 hm hQ₁ hQ₂
  have h45 := F.advantage_cramerShoupGame4_game5_le hasAD encodeMsg encodeAD setup H isElem hmem
    adversary bit n m hm0 hm
  refine ((Game.advantage_triangle _
    (F.cramerShoupGame2 hasAD encodeMsg encodeAD setup H isElem adversary bit n) _).trans
    (add_le_add h12 ((Game.advantage_triangle _
      (F.cramerShoupGame3 hasAD encodeMsg encodeAD setup H isElem adversary bit n) _).trans
      (add_le_add h23 ((Game.advantage_triangle _
        (F.cramerShoupGame4 hasAD encodeMsg encodeAD setup H isElem adversary bit n) _).trans
        (add_le_add h34 h45)))))).trans_eq ?_
  push_cast
  ring

/-- **Concrete ideal-game 1CCA security bound under honest query bounds**: combining the Game 0
$\to$ Game 5 bounds for `bit = false` and `bit = true` via `cramerShoupGame5_false_eq_true` (where
`42 / 2 ^ n` is the reduction loss from the `sampleModNat` exponent draws inside the reductions). -/
theorem advantage_cramerShoupMsgCCA2Game_le_of_honest_bounds
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (n Q₁ Q₂ m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d)
    (hQ₁ : F.HonestPhase1QueryBound setup adversary n Q₁)
    (hQ₂ : F.HonestPhase2QueryBound hasAD encodeAD setup H isElem adversary n Q₂) :
    Game.advantage
      (F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary false n)
      (F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary false) n)
        (F.ddhIdealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary false)
          n) +
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary true) n)
        (F.ddhIdealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary true)
          n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary false)
          n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary true) n) +
      ((2 * Q₁ + 2 * Q₂ + 2 : ℕ) : ℝ≥0) / (m : ℝ≥0) +
      42 / 2 ^ n := by
  have hfalse := F.advantage_cramerShoupMsgCCA2Game_game5_le hasAD encodeMsg encodeAD setup H
    isElem hmem adversary false n Q₁ Q₂ m hm0 hm hQ₁ hQ₂
  have htrue := F.advantage_cramerShoupMsgCCA2Game_game5_le hasAD encodeMsg encodeAD setup H
    isElem hmem adversary true n Q₁ Q₂ m hm0 hm hQ₁ hQ₂
  have htri := Game.advantage_triangle
    (F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary false n)
    (F.cramerShoupGame5 hasAD encodeMsg encodeAD setup H isElem adversary false n)
    (F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary true n)
  rw [F.cramerShoupGame5_false_eq_true,
    Game.advantage_comm
      (F.cramerShoupGame5 hasAD encodeMsg encodeAD setup H isElem adversary true n)] at htri
  refine (htri.trans (add_le_add hfalse htrue)).trans_eq ?_
  push_cast
  ring

/-- **Concrete ideal-game 1CCA security bound for `cramerShoupMsgCCA2Game`**: for any adversary with
decryption-query bounds `(Q₁ n, Q₂ n)`, the ideal 1CCA advantage at parameter `n` is bounded by the
DDH advantages of `cramerShoupMsgToDDHDistinguisher` (`false` and `true`), the collision-finding
success probabilities of `cramerShoupMsgToCollisionFinder` (`false` and `true`), plus
`(2 * Q₁ n + 2 * Q₂ n + 2) / m + 42 / 2 ^ n`. -/
theorem advantage_cramerShoupMsgCCA2Game_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (Q₁ Q₂ : ℕ → ℕ)
    (hQ : adversary.IsQueryBounded Q₁ Q₂) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage
      (F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary false n)
      (F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary false) n)
        (F.ddhIdealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary false)
          n) +
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary true) n)
        (F.ddhIdealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary true)
          n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary false)
          n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary true) n) +
      ((2 * Q₁ n + 2 * Q₂ n + 2 : ℕ) : ℝ≥0) / (m : ℝ≥0) +
      42 / 2 ^ n :=
  F.advantage_cramerShoupMsgCCA2Game_le_of_honest_bounds hasAD encodeMsg encodeAD setup H isElem
    hmem adversary n (Q₁ n) (Q₂ n) m hm0 hm
    (fun _ _ _ _ _ _ => hQ.1 n _)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => hQ.2 n _ _)

/-- **Theorem 12.9 & Exercise 12.27 concrete ideal-game bound (group-element messages with
associated data `AD`)** ([BonehShoup2023], Section 12.5.3, Theorem 12.9 and Remark 12.3, printed
pp. 488–493, Section 12.7, printed pp. 501–502, and Exercise 12.27, printed pp. 521–522):
concrete bound (12.19) for the ideal exact-uniform PMF 1CCA game `cramerShoupADGroupCCA2Game` for
Multiplicative Cramer–Shoup $\mathcal{E}_{\mathrm{MCS}}$ with associated data in the two-run
single-bit reduction style (with `42 / 2 ^ n` from the approximate `sampleModNat` exponent draws in
the reductions). -/
theorem advantage_cramerShoupADGroupCCA2Game_le
    {AD : Type} (encAD : AD ↪ List Bool)
    (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : WordADCCA2Adversary AD) (Q₁ Q₂ : ℕ → ℕ)
    (hQ : adversary.IsQueryBounded Q₁ Q₂) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage
      (F.cramerShoupADGroupCCA2Game encAD setup H isElem adversary false n)
      (F.cramerShoupADGroupCCA2Game encAD setup H isElem adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupADToDDHDistinguisher encAD H isElem adversary false) n)
        (F.ddhIdealGame setup
          (F.cramerShoupADToDDHDistinguisher encAD H isElem adversary false) n) +
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupADToDDHDistinguisher encAD H isElem adversary true) n)
        (F.ddhIdealGame setup
          (F.cramerShoupADToDDHDistinguisher encAD H isElem adversary true) n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupADToCollisionFinder encAD H isElem adversary false) n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupADToCollisionFinder encAD H isElem adversary true) n) +
      ((2 * Q₁ n + 2 * Q₂ n + 2 : ℕ) : ℝ≥0) / (m : ℝ≥0) +
      42 / 2 ^ n :=
  F.advantage_cramerShoupMsgCCA2Game_le true Prod.snd (fun p => encAD p.2) setup H isElem hmem
    adversary Q₁ Q₂ hQ n m hm0 hm

/-- **Theorem 12.9 & Exercise 12.27 concrete ideal-game bound (group-element messages)**
([BonehShoup2023], Section 12.5.3, Theorem 12.9 and Remark 12.3, printed pp. 488–493, and
Exercise 12.27, printed pp. 521–522): original adaptation of the concrete bound (12.19) to the
ideal exact-uniform PMF 1CCA game `cramerShoupGroupCCA2Game` for Multiplicative Cramer–Shoup
$\mathcal{E}_{\mathrm{MCS}}$ in the two-run single-bit reduction style (with `42 / 2 ^ n` from the
approximate `sampleModNat` exponent draws in the reductions). -/
theorem advantage_cramerShoupGroupCCA2Game_le
    (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : WordCCA2Adversary) (Q₁ Q₂ : ℕ → ℕ)
    (hQ : adversary.IsQueryBounded Q₁ Q₂) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage
      (F.cramerShoupGroupCCA2Game setup H isElem adversary false n)
      (F.cramerShoupGroupCCA2Game setup H isElem adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupToDDHDistinguisher H isElem adversary false) n)
        (F.ddhIdealGame setup
          (F.cramerShoupToDDHDistinguisher H isElem adversary false) n) +
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupToDDHDistinguisher H isElem adversary true) n)
        (F.ddhIdealGame setup
          (F.cramerShoupToDDHDistinguisher H isElem adversary true) n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupToCollisionFinder H isElem adversary false) n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupToCollisionFinder H isElem adversary true) n) +
      ((2 * Q₁ n + 2 * Q₂ n + 2 : ℕ) : ℝ≥0) / (m : ℝ≥0) +
      42 / 2 ^ n :=
  F.advantage_cramerShoupMsgCCA2Game_le false Prod.snd (fun _ => []) setup H isElem hmem
    adversary.toADUnit Q₁ Q₂ hQ.toADUnit n m hm0 hm

/-- **Concrete ideal-game 1CCA security bound for single-bit messages with associated data
(`cramerShoupADCCA2Game`)**. -/
theorem advantage_cramerShoupADCCA2Game_le
    {AD : Type} (encAD : AD ↪ List Bool)
    (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2Adversary AD) (Q₁ Q₂ : ℕ → ℕ)
    (hQ : adversary.IsQueryBounded Q₁ Q₂) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage
      (F.cramerShoupADCCA2Game encAD setup H isElem adversary false n)
      (F.cramerShoupADCCA2Game encAD setup H isElem adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher true (fun p => F.encodeBit p.1 p.2)
            (fun p => encAD p.2) H isElem adversary false) n)
        (F.ddhIdealGame setup
          (F.cramerShoupMsgToDDHDistinguisher true (fun p => F.encodeBit p.1 p.2)
            (fun p => encAD p.2) H isElem adversary false) n) +
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher true (fun p => F.encodeBit p.1 p.2)
            (fun p => encAD p.2) H isElem adversary true) n)
        (F.ddhIdealGame setup
          (F.cramerShoupMsgToDDHDistinguisher true (fun p => F.encodeBit p.1 p.2)
            (fun p => encAD p.2) H isElem adversary true) n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder true (fun p => F.encodeBit p.1 p.2)
            (fun p => encAD p.2) H isElem adversary false) n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder true (fun p => F.encodeBit p.1 p.2)
            (fun p => encAD p.2) H isElem adversary true) n) +
      ((2 * Q₁ n + 2 * Q₂ n + 2 : ℕ) : ℝ≥0) / (m : ℝ≥0) +
      42 / 2 ^ n :=
  F.advantage_cramerShoupMsgCCA2Game_le true (fun p => F.encodeBit p.1 p.2) (fun p => encAD p.2)
    setup H isElem hmem adversary Q₁ Q₂ hQ n m hm0 hm

/-- **Concrete ideal-game 1CCA security bound for single-bit messages (`cramerShoupCCA2Game`)**. -/
theorem advantage_cramerShoupCCA2Game_le
    (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : CCA2Adversary) (Q₁ Q₂ : ℕ → ℕ)
    (hQ : adversary.IsQueryBounded Q₁ Q₂) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage
      (F.cramerShoupCCA2Game setup H isElem adversary false n)
      (F.cramerShoupCCA2Game setup H isElem adversary true n) ≤
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher false (fun p => F.encodeBit p.1 p.2) (fun _ => [])
            H isElem adversary.toADUnit false) n)
        (F.ddhIdealGame setup
          (F.cramerShoupMsgToDDHDistinguisher false (fun p => F.encodeBit p.1 p.2) (fun _ => [])
            H isElem adversary.toADUnit false) n) +
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher false (fun p => F.encodeBit p.1 p.2) (fun _ => [])
            H isElem adversary.toADUnit true) n)
        (F.ddhIdealGame setup
          (F.cramerShoupMsgToDDHDistinguisher false (fun p => F.encodeBit p.1 p.2) (fun _ => [])
            H isElem adversary.toADUnit true) n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder false (fun p => F.encodeBit p.1 p.2) (fun _ => [])
            H isElem adversary.toADUnit false) n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder false (fun p => F.encodeBit p.1 p.2) (fun _ => [])
            H isElem adversary.toADUnit true) n) +
      ((2 * Q₁ n + 2 * Q₂ n + 2 : ℕ) : ℝ≥0) / (m : ℝ≥0) +
      42 / 2 ^ n :=
  F.advantage_cramerShoupMsgCCA2Game_le false (fun p => F.encodeBit p.1 p.2) (fun _ => []) setup H
    isElem hmem adversary.toADUnit Q₁ Q₂ hQ.toADUnit n m hm0 hm

/-! ### Polynomial length bounds and asymptotic 1CCA security -/

private theorem length_encBits4_encode_le {d : F.Desc} {B : ℕ}
    (hB : ∀ x : F.Carrier d, (F.encode d x).length ≤ B)
    (x₁ x₂ x₃ x₄ : F.Carrier d) :
    (encBits4 (F.encode d x₁, F.encode d x₂, F.encode d x₃, F.encode d x₄)).length ≤
      22 * B + 14 := by
  have h1 := hB x₁; have h2 := hB x₂; have h3 := hB x₃; have h4 := hB x₄
  simp only [encBits4, length_encPair, encBits_apply]
  lia

private theorem length_encodeCramerShoupPublicKey_le {d : F.Desc} {B : ℕ}
    (hB : ∀ x : F.Carrier d, (F.encode d x).length ≤ B)
    (α : ZMod (F.order d)) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    (F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d)) sk).length ≤
      2 * (F.encDesc d).length + 44 * B + 30 := by
  rw [F.encodeCramerShoupPublicKey_encode]
  unfold encodeCramerShoupPublicKeyValues
  have h4 := F.length_encBits4_encode_le hB
    (F.cramerShoupPublicKey d α sk.1.1 sk.1.2 sk.2.1.1 sk.2.1.2 sk.2.2.1 sk.2.2.2).1
    (F.cramerShoupPublicKey d α sk.1.1 sk.1.2 sk.2.1.1 sk.2.1.2 sk.2.2.1 sk.2.2.2).2.1
    (F.cramerShoupPublicKey d α sk.1.1 sk.1.2 sk.2.1.1 sk.2.1.2 sk.2.2.1 sk.2.2.2).2.2.1
    (F.cramerShoupPublicKey d α sk.1.1 sk.1.2 sk.2.1.1 sk.2.1.2 sk.2.2.1 sk.2.2.2).2.2.2
  simp only [length_encPair]
  lia

/-- **Asymptotic ideal-game 1CCA security of Multiplicative Cramer–Shoup for general message and
associated-data encodings** ([BonehShoup2023], Theorem 12.9, Section 12.7 & Exercise 12.27,
printed pp. 488–493, 501–502, 521–522): if DDH holds for `setup`, `cramerShoupHashMod H` is
collision-resistant for `setup`, every supported group at parameter `n` has order at least
`m n > 0` with `1 / m n` negligible, and supported group descriptions have polynomially bounded
bit-length, then the ideal exact-uniform PMF game `cramerShoupMsgCCA2Game` is indistinguishable
between `bit = false` and `bit = true` against all strict oracle PPT adversaries. -/
theorem DDH.cramerShoupMsgINDCCA2
    {F : PrimeOrderGroupFamily}
    (hasAD : Bool)
    {Msg AD : Type} {encMsg : Msg ↪ List Bool} {encAD : AD ↪ List Bool}
    {encodeMsg : F.Desc × Msg → List Bool}
    {encodeAD : F.Desc × AD → List Bool}
    (hencMsg : ComputableInPolyTime encodeMsg (encPair F.encDesc encMsg) encBits)
    (hencAD : ComputableInPolyTime encodeAD (encPair F.encDesc encAD) encBits)
    {setup : ℕ → PMF F.Desc}
    {H : F.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH setup)
    (hCR : CollisionResistantFor F.encDesc setup (F.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0))
    (hdesc : ∃ c k : ℕ, ∀ n, ∀ d ∈ (setup n).support,
      (F.encDesc d).length ≤ c * (n + 1) ^ k) :
    Game.Indistinguishable
      (fun adversary n =>
        F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary false n)
      (fun adversary n =>
        F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary true n)
      (ADCCA2AdversaryOf.IsPPT encMsg encAD) := by
  intro adversary hA
  obtain ⟨cd, kd, hdesc_le⟩ := hdesc
  obtain ⟨ce, ke, henc_le⟩ := F.exists_length_encode_le
  obtain ⟨c₁, d₁, c₂, d₂, cs, ds, hQ₁_raw, hQ₂_raw, hstate⟩ := hA.query_bounds
  let Ld (n : ℕ) : ℕ := cd * (n + 1) ^ kd
  let B (n : ℕ) : ℕ := ce * (Ld n + 1) ^ ke
  let Lpk (n : ℕ) : ℕ := 2 * Ld n + 44 * B n + 30
  let Lct (n : ℕ) : ℕ := 22 * B n + 14
  let Lst (n : ℕ) : ℕ := cs * (n + Lpk n + 2) ^ ds
  let Q₁ (n : ℕ) : ℕ := c₁ * (n + Lpk n + 2) ^ d₁
  let Q₂ (n : ℕ) : ℕ := c₂ * (n + Lst n + Lct n + 2) ^ d₂
  have hddh0 : Negligible fun n =>
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary false) n)
        (F.ddhIdealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary false)
          n) :=
    hDDH _ (F.isPPTOn_cramerShoupMsgToDDHDistinguisher hasAD hencMsg hencAD hH hisElem hA false)
  have hddh1 : Negligible fun n =>
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary true) n)
        (F.ddhIdealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary true)
          n) :=
    hDDH _ (F.isPPTOn_cramerShoupMsgToDDHDistinguisher hasAD hencMsg hencAD hH hisElem hA true)
  have hcr0 : Negligible fun n =>
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary false)
          n) :=
    hCR.negligible _
      (F.isPPTOn_cramerShoupMsgToCollisionFinder hasAD hencMsg hencAD hH hisElem hA false)
  have hcr1 : Negligible fun n =>
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary true) n) :=
    hCR.negligible _
      (F.isPPTOn_cramerShoupMsgToCollisionFinder hasAD hencMsg hencAD hH hisElem hA true)
  have hpoly_Q : PolynomiallyBounded (fun n => 2 * Q₁ n + 2 * Q₂ n + 2) := by
    dsimp only [Q₁, Q₂, Lst, Lct, Lpk, B, Ld]
    fun_prop
  have hq_neg : Negligible fun n =>
      ((2 * Q₁ n + 2 * Q₂ n + 2 : ℕ) : ℝ≥0) / (m n : ℝ≥0) := by
    have heq : (fun n => ((2 * Q₁ n + 2 * Q₂ n + 2 : ℕ) : ℝ≥0) / (m n : ℝ≥0)) =
        fun n => ((2 * Q₁ n + 2 * Q₂ n + 2 : ℕ) : ℝ≥0) * (1 / m n : ℝ≥0) := by
      funext n
      rw [div_eq_mul_inv, one_div]
    rw [heq]
    exact hinv.polynomiallyBounded_mul hpoly_Q
  have h42_neg : Negligible fun n => (42 : ℝ≥0) / 2 ^ n :=
    negligible_const_div_two_pow 42
  refine negligible_of_le
    (((((hddh0.add hddh1).add hcr0).add hcr1).add hq_neg).add h42_neg) (fun n => ?_)
  refine F.advantage_cramerShoupMsgCCA2Game_le_of_honest_bounds hasAD encodeMsg encodeAD setup H
    isElem hmem adversary n (Q₁ n) (Q₂ n) (m n) (hm0 n) (hm n) ?_ ?_
  · intro d hd α δ δ₁ δ₂
    have hd_le : (F.encDesc d).length ≤ Ld n := hdesc_le n d hd
    have hB_le : ∀ x : F.Carrier d, (F.encode d x).length ≤ B n :=
      fun x => (henc_le d x).trans (by dsimp only [B]; gcongr)
    have hpk :
        (F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d))
          (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0)).length ≤ Lpk n :=
      (F.length_encodeCramerShoupPublicKey_le hB_le α _).trans (by dsimp only [Lpk]; gcongr)
    exact (hQ₁_raw n _).mono (by dsimp only [Q₁]; gcongr)
  · intro d hd α β γ δ τ δ₁ δ₂ ξ choiceOut hchoice mElem
    rw [ProbOracleComp.eval_run_interpret] at hchoice
    have hd_le : (F.encDesc d).length ≤ Ld n := hdesc_le n d hd
    have hB_le : ∀ x : F.Carrier d, (F.encode d x).length ≤ B n :=
      fun x => (henc_le d x).trans (by dsimp only [B]; gcongr)
    have hpk :
        (F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d))
          (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0)).length ≤ Lpk n :=
      (F.length_encodeCramerShoupPublicKey_le hB_le α _).trans (by dsimp only [Lpk]; gcongr)
    have hst : choiceOut.1.2.length ≤ Lst n :=
      (hstate n _ Unit _ () choiceOut.2 choiceOut.1 hchoice).trans (by dsimp only [Lst]; gcongr)
    have hct :
        (encBits4
          (F.encode d (β • F.generator d),
           F.encode d (γ • F.generator d),
           F.encode d (projHash F d (δ - α * τ) τ (β • F.generator d) (γ • F.generator d) + mElem),
           F.encode d ((β * (δ₁ + F.cramerShoupHashMod H d
             (encBits4 (F.encode d (β • F.generator d),
               F.encode d (γ • F.generator d),
               F.encode d (projHash F d (δ - α * τ) τ (β • F.generator d) (γ • F.generator d) +
                 mElem),
               encodeAD (d, choiceOut.1.1.2))) * δ₂) + (γ - α * β) * ξ) •
             F.generator d))).length ≤ Lct n :=
      F.length_encBits4_encode_le hB_le _ _ _ _
    exact (hQ₂_raw n choiceOut.1.2 _).mono (by dsimp only [Q₂]; gcongr)

/-- **Theorem 12.9 & Exercise 12.27 (asymptotic ideal-game 1CCA security for group-element
messages with associated data `AD`)**: Multiplicative Cramer–Shoup satisfies the ideal
exact-uniform PMF 1CCA notion `cramerShoupADGroupINDCCA2` under DDH, collision resistance of
`cramerShoupHashMod H`, a positive group-order lower bound `m n > 0` with `1 / m n` negligible,
and polynomially bounded group description bit-length. -/
theorem DDH.cramerShoupADGroupINDCCA2
    {F : PrimeOrderGroupFamily}
    {AD : Type} (encAD : AD ↪ List Bool)
    {setup : ℕ → PMF F.Desc}
    {H : F.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH setup)
    (hCR : CollisionResistantFor F.encDesc setup (F.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0))
    (hdesc : ∃ c k : ℕ, ∀ n, ∀ d ∈ (setup n).support,
      (F.encDesc d).length ≤ c * (n + 1) ^ k) :
    F.cramerShoupADGroupINDCCA2 encAD setup H isElem :=
  hDDH.cramerShoupMsgINDCCA2 true (by fun_prop) (by fun_prop) hH hisElem hmem hCR hm0 hm hinv
    hdesc

/-- **Theorem 12.9 & Exercise 12.27 (asymptotic ideal-game 1CCA security for group-element
messages)**: Multiplicative Cramer–Shoup satisfies the ideal exact-uniform PMF 1CCA notion
`cramerShoupGroupINDCCA2` under DDH, collision resistance of `cramerShoupHashMod H`, a positive
group-order lower bound `m n > 0` with `1 / m n` negligible, and polynomially bounded group
description bit-length. -/
theorem DDH.cramerShoupGroupINDCCA2
    {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc}
    {H : F.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH setup)
    (hCR : CollisionResistantFor F.encDesc setup (F.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0))
    (hdesc : ∃ c k : ℕ, ∀ n, ∀ d ∈ (setup n).support,
      (F.encDesc d).length ≤ c * (n + 1) ^ k) :
    F.cramerShoupGroupINDCCA2 setup H isElem := by
  intro adversary hA
  exact hDDH.cramerShoupMsgINDCCA2 false (by fun_prop) (by fun_prop) hH hisElem hmem hCR hm0 hm
    hinv hdesc adversary.toADUnit hA.toADUnit

/-- **Asymptotic ideal-game 1CCA security for single-bit messages with associated data
(`cramerShoupADINDCCA2`)**: Multiplicative Cramer–Shoup with bit embedding `encodeBit` satisfies
the ideal exact-uniform PMF 1CCA notion `cramerShoupADINDCCA2` under DDH, collision resistance of
`cramerShoupHashMod H`, a positive group-order lower bound `m n > 0` with `1 / m n` negligible, and
polynomially bounded group description bit-length. -/
theorem DDH.cramerShoupADINDCCA2
    {F : PrimeOrderGroupFamily}
    {AD : Type} (encAD : AD ↪ List Bool)
    {setup : ℕ → PMF F.Desc}
    {H : F.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH setup)
    (hCR : CollisionResistantFor F.encDesc setup (F.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0))
    (hdesc : ∃ c k : ℕ, ∀ n, ∀ d ∈ (setup n).support,
      (F.encDesc d).length ≤ c * (n + 1) ^ k) :
    F.cramerShoupADINDCCA2 encAD setup H isElem :=
  hDDH.cramerShoupMsgINDCCA2 true F.computableInPolyTime_encodeBit (by fun_prop) hH hisElem hmem
    hCR hm0 hm hinv hdesc

/-- **Asymptotic ideal-game 1CCA security for single-bit messages (`cramerShoupINDCCA2`)**:
Multiplicative Cramer–Shoup with bit embedding `encodeBit` satisfies the ideal exact-uniform PMF
1CCA notion `cramerShoupINDCCA2` under DDH, collision resistance of `cramerShoupHashMod H`, a
positive group-order lower bound `m n > 0` with `1 / m n` negligible, and polynomially bounded group
description bit-length. -/
theorem DDH.cramerShoupINDCCA2
    {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc}
    {H : F.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH setup)
    (hCR : CollisionResistantFor F.encDesc setup (F.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0))
    (hdesc : ∃ c k : ℕ, ∀ n, ∀ d ∈ (setup n).support,
      (F.encDesc d).length ≤ c * (n + 1) ^ k) :
    F.cramerShoupINDCCA2 setup H isElem := by
  intro adversary hA
  exact hDDH.cramerShoupMsgINDCCA2 false F.computableInPolyTime_encodeBit (by fun_prop) hH hisElem
    hmem hCR hm0 hm hinv hdesc adversary.toADUnit hA.toADUnit


/-! ### `Encryption.cca2ADGameOn`, `Encryption.INDCCA2ADOn`, `Encryption.cca2GameOn`, and
`Encryption.INDCCA2On` instantiations -/

private theorem advantage_four_le_eight (g₁ g₂ g₃ g₄ : Game) {n : ℕ}
    (h₁ : Game.advantage g₁ g₂ ≤ 1 / 2 ^ n)
    (h₂ : Game.advantage g₂ g₃ ≤ 6 / 2 ^ n)
    (h₃ : Game.advantage g₃ g₄ ≤ 1 / 2 ^ n) :
    Game.advantage g₁ g₄ ≤ 8 / 2 ^ n := by
  have htri1 := Game.advantage_triangle g₁ g₂ g₄
  have htri2 := Game.advantage_triangle g₂ g₃ g₄
  calc Game.advantage g₁ g₄
      ≤ Game.advantage g₁ g₂ + (Game.advantage g₂ g₃ + Game.advantage g₃ g₄) :=
        htri1.trans (add_le_add le_rfl htri2)
    _ ≤ 1 / 2 ^ n + (6 / 2 ^ n + 1 / 2 ^ n) :=
        add_le_add h₁ (add_le_add h₂ h₃)
    _ = 8 / 2 ^ n := by ring

private theorem eval_run_interpret_map_bind
    {α β γ State : Type}
    (oracle : Unit × List Bool → StateT State ProbComp (List Bool))
    (f : α → β) (oa : WordOracleComp Unit α) (s : State)
    (k : β × State → PMF γ) :
    (ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m)) oracle)
      (f <$> oa)).run s)).bind k =
    (ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m)) oracle)
      oa).run s)).bind (fun p => k (f p.1, p.2)) := by
  rw [OracleComp.interpret_map, StateT.run_map]
  simp only [← bind_pure_comp, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.bind_bind, PMF.pure_bind]

private noncomputable def cramerShoupCCA2InnerB
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ)
    (α σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d))
    (choiceOut : (((List Bool × List Bool) × AD) × List Bool) × Unit)
    (β : ZMod (F.order d)) : Game :=
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let pkVal := F.cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂
  let m := if bit then choiceOut.1.1.1.2 else choiceOut.1.1.1.1
  let adBits := encodeAD (d, choiceOut.1.1.2)
  let ct := F.encodeCramerShoupEncrypt H d
    (F.encode d pkVal.1, F.encode d pkVal.2.1,
      F.encode d pkVal.2.2.1, F.encode d pkVal.2.2.2) m adBits β.val
  (ProbComp.eval ((OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct adBits))
    (adversary.guess n choiceOut.1.2 ct)).run ())).bind (fun guessOut => PMF.pure guessOut.1)

private noncomputable def cramerShoupCCA2InnerSK
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ)
    (α σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) (useExactB : Bool) : Game :=
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let pk := F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d)) sk
  (ProbComp.eval ((OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())).bind fun choiceOut =>
    if isElem (d, choiceOut.1.1.1.1) && isElem (d, choiceOut.1.1.1.2) then
      if useExactB then
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          F.cramerShoupCCA2InnerB hasAD encodeAD H isElem d adversary bit n
            α σ τ σ₁ τ₁ σ₂ τ₂ choiceOut β
      else
        (ProbComp.eval (F.sampleExp n d)).bind fun b =>
          F.cramerShoupCCA2InnerB hasAD encodeAD H isElem d adversary bit n
            α σ τ σ₁ τ₁ σ₂ τ₂ choiceOut (b : ZMod (F.order d))
    else
      PMF.pure false

private theorem advantage_cramerShoupCCA2InnerSK_le
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ) :
    Game.advantage
      ((ProbComp.eval (F.sampleExp n d)).bind fun a =>
        (ProbComp.eval (F.sampleCramerShoupSK n d)).bind fun sk =>
          F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n
            (a : ZMod (F.order d))
            (sk.1.1 : ZMod (F.order d)) (sk.1.2 : ZMod (F.order d))
            (sk.2.1.1 : ZMod (F.order d)) (sk.2.1.2 : ZMod (F.order d))
            (sk.2.2.1 : ZMod (F.order d)) (sk.2.2.2 : ZMod (F.order d)) false)
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ₁ =>
              (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ₁ =>
                (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ₂ =>
                  (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ₂ =>
                    F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n
                      α σ τ σ₁ τ₁ σ₂ τ₂ true) ≤
      8 / 2 ^ n := by
  refine advantage_four_le_eight _
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (ProbComp.eval (F.sampleCramerShoupSK n d)).bind fun sk =>
        F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n α
          (sk.1.1 : ZMod (F.order d)) (sk.1.2 : ZMod (F.order d))
          (sk.2.1.1 : ZMod (F.order d)) (sk.2.1.2 : ZMod (F.order d))
          (sk.2.2.1 : ZMod (F.order d)) (sk.2.2.2 : ZMod (F.order d)) false)
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ₁ =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ₁ =>
              (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ₂ =>
                (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ₂ =>
                  F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n
                    α σ τ σ₁ τ₁ σ₂ τ₂ false) _
    (F.advantage_bind_sampleExp_le n d (fun α =>
      (ProbComp.eval (F.sampleCramerShoupSK n d)).bind fun sk =>
        F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n α
          (sk.1.1 : ZMod (F.order d)) (sk.1.2 : ZMod (F.order d))
          (sk.2.1.1 : ZMod (F.order d)) (sk.2.1.2 : ZMod (F.order d))
          (sk.2.2.1 : ZMod (F.order d)) (sk.2.2.2 : ZMod (F.order d)) false))
    (advantage_bind_le_nnreal _ _ _ fun α =>
      F.advantage_bind_sampleCramerShoupSK_le n d _ (fun σ τ σ₁ τ₁ σ₂ τ₂ =>
        F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n
          α σ τ σ₁ τ₁ σ₂ τ₂ false) (fun _ _ _ _ _ _ => rfl)) ?_
  refine advantage_bind_le_nnreal _ _ _ fun α => ?_
  refine advantage_bind_le_nnreal _ _ _ fun σ => ?_
  refine advantage_bind_le_nnreal _ _ _ fun τ => ?_
  refine advantage_bind_le_nnreal _ _ _ fun σ₁ => ?_
  refine advantage_bind_le_nnreal _ _ _ fun τ₁ => ?_
  refine advantage_bind_le_nnreal _ _ _ fun σ₂ => ?_
  refine advantage_bind_le_nnreal _ _ _ fun τ₂ => ?_
  dsimp only [cramerShoupCCA2InnerSK]
  refine advantage_bind_le_nnreal _ _ _ fun choiceOut => ?_
  by_cases h : (isElem (d, choiceOut.1.1.1.1) && isElem (d, choiceOut.1.1.1.2)) = true
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    exact F.advantage_bind_sampleExp_le n d
      (F.cramerShoupCCA2InnerB hasAD encodeAD H isElem d adversary bit n
        α σ τ σ₁ τ₁ σ₂ τ₂ choiceOut)
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Game.advantage_self, zero_le]

/-- The native `Encryption.cca2ADGameOn` experiment for `(cramerShoupValid, cramerShoupKeyGenProb,
cramerShoupADEncryptProb, cramerShoupADDecryptOpt)` is within statistical distance `8 / 2 ^ n` of
the ideal exact-uniform PMF game `cramerShoupADGroupCCA2Game encAD (fun n => PMF.pure (d n))`
(accounting for the eight `sampleModNat` exponent draws in `cramerShoupKeyGenProb` and
`cramerShoupADEncryptProb`). -/
theorem advantage_cca2ADGameOn_cramerShoupADGroupCCA2Game_le
    {AD : Type} (encAD : AD ↪ List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : ℕ → F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ) :
    Game.advantage
      (ProbComp.eval
        (cca2ADGameOn (F.cramerShoupValid isElem d) encAD encBits (F.cramerShoupKeyGenProb d)
          (F.cramerShoupADEncryptProb encAD H d) (F.cramerShoupADDecryptOpt H isElem d)
          adversary bit n))
      (F.cramerShoupADGroupCCA2Game encAD (fun n => PMF.pure (d n)) H isElem
        adversary bit n) ≤
      8 / 2 ^ n := by
  have hgame0 :
      ProbComp.eval
        (cca2ADGameOn (F.cramerShoupValid isElem d) encAD encBits (F.cramerShoupKeyGenProb d)
          (F.cramerShoupADEncryptProb encAD H d) (F.cramerShoupADDecryptOpt H isElem d)
          adversary bit n) =
      (ProbComp.eval (F.sampleExp n (d n))).bind fun a =>
        (ProbComp.eval (F.sampleCramerShoupSK n (d n))).bind fun sk =>
          F.cramerShoupCCA2InnerSK true (fun p => encAD p.2) H isElem (d n) adversary bit n
            (a : ZMod (F.order (d n)))
            (sk.1.1 : ZMod (F.order (d n))) (sk.1.2 : ZMod (F.order (d n)))
            (sk.2.1.1 : ZMod (F.order (d n))) (sk.2.1.2 : ZMod (F.order (d n)))
            (sk.2.2.1 : ZMod (F.order (d n))) (sk.2.2.2 : ZMod (F.order (d n))) false := by
    simp only [cca2ADGameOn, cramerShoupKeyGenProb, cramerShoupADEncryptProb, cramerShoupValid,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, F.smul_encode,
      F.cca2ADPhase1Oracle_cramerShoupADDecryptOpt]
    refine congrArg _ (funext fun a => congrArg _ (funext fun sk => ?_))
    dsimp only [cramerShoupCCA2InnerSK]
    rw [F.encodeCramerShoupPublicKey_eq_skNatOfZMod (d n) (a : ZMod (F.order (d n))) sk,
      F.cramerShoupPhase1Oracle_eq_skNatOfZMod true H isElem hmem (d n) sk]
    refine congrArg _ (funext fun choiceOut => ?_)
    by_cases h : (isElem (d n, choiceOut.1.1.1.1) && isElem (d n, choiceOut.1.1.1.2)) = true
    · simp only [h, ↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.bind_bind, PMF.pure_bind, F.cca2ADPhase2Oracle_cramerShoupADDecryptOpt,
        F.decodeBits4_dropFrame_encodeCramerShoupPublicKey, cramerShoupCCA2InnerB]
      refine congrArg _ (funext fun b => ?_)
      have hct :=
        F.encodeCramerShoupEncrypt_skNatOfZMod H (d n) (a : ZMod (F.order (d n)))
          (sk.1.1 : ZMod (F.order (d n))) (sk.1.2 : ZMod (F.order (d n)))
          (sk.2.1.1 : ZMod (F.order (d n))) (sk.2.1.2 : ZMod (F.order (d n)))
          (sk.2.2.1 : ZMod (F.order (d n))) (sk.2.2.2 : ZMod (F.order (d n)))
          (if bit then choiceOut.1.1.1.2 else choiceOut.1.1.1.1) (encAD choiceOut.1.1.2) b
      rw [hct, F.cramerShoupPhase2Oracle_eq_skNatOfZMod true H isElem hmem (d n) sk]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]
  have hgame1 :
      F.cramerShoupADGroupCCA2Game encAD (fun n => PMF.pure (d n)) H isElem
        adversary bit n =
      (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun σ =>
          (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun τ =>
            (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun σ₁ =>
              (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun τ₁ =>
                (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun σ₂ =>
                  (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun τ₂ =>
                    F.cramerShoupCCA2InnerSK true (fun p => encAD p.2) H isElem (d n) adversary
                      bit n α σ τ σ₁ τ₁ σ₂ τ₂ true := by
    simp only [cramerShoupADGroupCCA2Game, cramerShoupMsgCCA2Game, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.pure_bind]
    refine congrArg _ (funext fun α => congrArg _ (funext fun σ =>
      congrArg _ (funext fun τ => congrArg _ (funext fun σ₁ =>
        congrArg _ (funext fun τ₁ => congrArg _ (funext fun σ₂ =>
          congrArg _ (funext fun τ₂ => ?_)))))))
    simp only [cramerShoupCCA2InnerSK, cramerShoupCCA2InnerB, ↓reduceIte,
      encodeCramerShoupPublicKey_encode, skNatOfZMod, ZMod.natCast_zmod_val]
  rw [hgame0, hgame1]
  exact F.advantage_cramerShoupCCA2InnerSK_le true (fun p => encAD p.2) H isElem (d n)
    adversary bit n

/-- **Theorem 12.9 & Exercise 12.27 via `Encryption.INDCCA2ADOn`**: for any associated-data
encoding `encAD : AD ↪ List Bool` and polynomial-time group description family `d : ℕ → F.Desc`,
the probabilistic polynomial-time Multiplicative Cramer–Shoup encryption scheme with associated
data `(cramerShoupKeyGenProb d, cramerShoupADEncryptProb encAD H d, cramerShoupADDecryptOpt H
isElem d)` satisfies the native `Encryption.INDCCA2ADOn` notion with respect to the
group-membership admissibility predicate `cramerShoupValid isElem d` under DDH, collision
resistance of `cramerShoupHashMod H`, and a positive group-order lower bound `m n > 0` with
`1 / m n` negligible. -/
theorem DDH.indcca2ADOn_cramerShoup
    {F : PrimeOrderGroupFamily}
    {AD : Type} (encAD : AD ↪ List Bool)
    {H : F.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantFor F.encDesc (fun n => PMF.pure (d n)) (F.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2ADOn (F.cramerShoupValid isElem d) encBits encAD encBits
      (F.cramerShoupKeyGenProb d) (F.cramerShoupADEncryptProb encAD H d)
      (F.cramerShoupADDecryptOpt H isElem d) := by
  have hdesc : ∃ c k : ℕ, ∀ n, ∀ d' ∈ (PMF.pure (d n)).support,
      (F.encDesc d').length ≤ c * (n + 1) ^ k := by
    obtain ⟨c, k, hck⟩ := hd.tidy.polyBounded_length.exists_le
    refine ⟨c, k, fun n d' hd' => ?_⟩
    rw [PMF.support_pure, Set.mem_singleton_iff] at hd'
    subst hd'
    simpa only [encUnary_apply, List.length_replicate] using hck n
  have hgroup :
      F.cramerShoupADGroupINDCCA2 encAD (fun n => PMF.pure (d n)) H isElem :=
    hDDH.cramerShoupADGroupINDCCA2 encAD hH hisElem hmem hCR hm0
      (fun n d' hd' => by
        rw [PMF.support_pure, Set.mem_singleton_iff] at hd'
        subst hd'
        exact hm n)
      hinv hdesc
  intro adversary hA
  have hmid := hgroup adversary hA
  have h8 : Negligible fun n => (8 : ℝ≥0) / 2 ^ n := negligible_const_div_two_pow 8
  refine negligible_of_le ((h8.add hmid).add h8) fun n => ?_
  have h0 := F.advantage_cca2ADGameOn_cramerShoupADGroupCCA2Game_le encAD H isElem hmem d
    adversary false n
  have h1 := F.advantage_cca2ADGameOn_cramerShoupADGroupCCA2Game_le encAD H isElem hmem d
    adversary true n
  rw [Game.advantage_comm] at h1
  have htri1 := Game.advantage_triangle
    (ProbComp.eval
      (cca2ADGameOn (F.cramerShoupValid isElem d) encAD encBits (F.cramerShoupKeyGenProb d)
        (F.cramerShoupADEncryptProb encAD H d) (F.cramerShoupADDecryptOpt H isElem d)
        adversary false n))
    (F.cramerShoupADGroupCCA2Game encAD (fun n => PMF.pure (d n)) H isElem
      adversary false n)
    (ProbComp.eval
      (cca2ADGameOn (F.cramerShoupValid isElem d) encAD encBits (F.cramerShoupKeyGenProb d)
        (F.cramerShoupADEncryptProb encAD H d) (F.cramerShoupADDecryptOpt H isElem d)
        adversary true n))
  have htri2 := Game.advantage_triangle
    (F.cramerShoupADGroupCCA2Game encAD (fun n => PMF.pure (d n)) H isElem
      adversary false n)
    (F.cramerShoupADGroupCCA2Game encAD (fun n => PMF.pure (d n)) H isElem
      adversary true n)
    (ProbComp.eval
      (cca2ADGameOn (F.cramerShoupValid isElem d) encAD encBits (F.cramerShoupKeyGenProb d)
        (F.cramerShoupADEncryptProb encAD H d) (F.cramerShoupADDecryptOpt H isElem d)
        adversary true n))
  exact (htri1.trans (add_le_add le_rfl htri2)).trans
    (by rw [add_assoc]; exact add_le_add h0 (add_le_add le_rfl h1))

/-- The native `Encryption.cca2GameOn` experiment for `(cramerShoupValid, cramerShoupKeyGenProb,
cramerShoupEncryptProb, cramerShoupDecryptOpt)` is within statistical distance `8 / 2 ^ n` of the
ideal exact-uniform PMF game `cramerShoupGroupCCA2Game (fun n => PMF.pure (d n))` (accounting for
the eight `sampleModNat` exponent draws in `cramerShoupKeyGenProb` and `cramerShoupEncryptProb`). -/
theorem advantage_cca2GameOn_cramerShoupGroupCCA2Game_le
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : ℕ → F.Desc) (adversary : WordCCA2Adversary) (bit : Bool) (n : ℕ) :
    Game.advantage
      (ProbComp.eval
        (cca2GameOn (F.cramerShoupValid isElem d) encBits (F.cramerShoupKeyGenProb d)
          (F.cramerShoupEncryptProb H d) (F.cramerShoupDecryptOpt H isElem d) adversary bit n))
      (F.cramerShoupGroupCCA2Game (fun n => PMF.pure (d n)) H isElem adversary bit n) ≤
      8 / 2 ^ n := by
  have hgame0 :
      ProbComp.eval
        (cca2GameOn (F.cramerShoupValid isElem d) encBits (F.cramerShoupKeyGenProb d)
          (F.cramerShoupEncryptProb H d) (F.cramerShoupDecryptOpt H isElem d) adversary bit n) =
      (ProbComp.eval (F.sampleExp n (d n))).bind fun a =>
        (ProbComp.eval (F.sampleCramerShoupSK n (d n))).bind fun sk =>
          F.cramerShoupCCA2InnerSK false (fun _ => []) H isElem (d n) adversary.toADUnit bit n
            (a : ZMod (F.order (d n)))
            (sk.1.1 : ZMod (F.order (d n))) (sk.1.2 : ZMod (F.order (d n)))
            (sk.2.1.1 : ZMod (F.order (d n))) (sk.2.1.2 : ZMod (F.order (d n)))
            (sk.2.2.1 : ZMod (F.order (d n))) (sk.2.2.2 : ZMod (F.order (d n))) false := by
    simp only [cca2GameOn, cramerShoupKeyGenProb, cramerShoupEncryptProb, cramerShoupValid,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, F.smul_encode,
      F.cca2Phase1Oracle_cramerShoupDecryptOpt]
    refine congrArg _ (funext fun a => congrArg _ (funext fun sk => ?_))
    dsimp only [cramerShoupCCA2InnerSK, CCA2AdversaryOf.toADUnit]
    rw [eval_run_interpret_map_bind,
      F.encodeCramerShoupPublicKey_eq_skNatOfZMod (d n) (a : ZMod (F.order (d n))) sk,
      F.cramerShoupPhase1Oracle_eq_skNatOfZMod false H isElem hmem (d n) sk]
    refine congrArg _ (funext fun choiceOut => ?_)
    by_cases h : (isElem (d n, choiceOut.1.1.1) && isElem (d n, choiceOut.1.1.2)) = true
    · simp only [h, ↓reduceIte, Bool.false_eq_true, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.bind_bind, PMF.pure_bind, F.cca2Phase2Oracle_cramerShoupDecryptOpt,
        F.decodeBits4_dropFrame_encodeCramerShoupPublicKey, cramerShoupCCA2InnerB]
      refine congrArg _ (funext fun b => ?_)
      have hct :=
        F.encodeCramerShoupEncrypt_skNatOfZMod H (d n) (a : ZMod (F.order (d n)))
          (sk.1.1 : ZMod (F.order (d n))) (sk.1.2 : ZMod (F.order (d n)))
          (sk.2.1.1 : ZMod (F.order (d n))) (sk.2.1.2 : ZMod (F.order (d n)))
          (sk.2.2.1 : ZMod (F.order (d n))) (sk.2.2.2 : ZMod (F.order (d n)))
          (if bit then choiceOut.1.1.2 else choiceOut.1.1.1) [] b
      rw [hct, F.cramerShoupPhase2Oracle_eq_skNatOfZMod false H isElem hmem (d n) sk]
    · simp only [h, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]
  have hgame1 :
      F.cramerShoupGroupCCA2Game (fun n => PMF.pure (d n)) H isElem adversary bit n =
      (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun σ =>
          (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun τ =>
            (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun σ₁ =>
              (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun τ₁ =>
                (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun σ₂ =>
                  (PMF.uniformOfFintype (ZMod (F.order (d n)))).bind fun τ₂ =>
                    F.cramerShoupCCA2InnerSK false (fun _ => []) H isElem (d n) adversary.toADUnit
                      bit n α σ τ σ₁ τ₁ σ₂ τ₂ true := by
    simp only [cramerShoupGroupCCA2Game, cramerShoupMsgCCA2Game, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.pure_bind]
    refine congrArg _ (funext fun α => congrArg _ (funext fun σ =>
      congrArg _ (funext fun τ => congrArg _ (funext fun σ₁ =>
        congrArg _ (funext fun τ₁ => congrArg _ (funext fun σ₂ =>
          congrArg _ (funext fun τ₂ => ?_)))))))
    simp only [cramerShoupCCA2InnerSK, cramerShoupCCA2InnerB, ↓reduceIte,
      encodeCramerShoupPublicKey_encode, skNatOfZMod, ZMod.natCast_zmod_val]
  rw [hgame0, hgame1]
  exact F.advantage_cramerShoupCCA2InnerSK_le false (fun _ => []) H isElem (d n)
    adversary.toADUnit bit n

/-- **Theorem 12.9 & Exercise 12.27 via `Encryption.INDCCA2On`**: for any polynomial-time group
description family `d : ℕ → F.Desc`, the probabilistic polynomial-time Cramer–Shoup encryption
scheme `(cramerShoupKeyGenProb d, cramerShoupEncryptProb H d, cramerShoupDecryptOpt H isElem d)`
satisfies the native `Encryption.INDCCA2On` notion with respect to the group-membership
admissibility predicate `cramerShoupValid isElem d` under DDH, collision resistance of
`cramerShoupHashMod H`, and a positive group-order lower bound `m n > 0` with `1 / m n`
negligible. -/
theorem DDH.indcca2On_cramerShoup
    {F : PrimeOrderGroupFamily}
    {H : F.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantFor F.encDesc (fun n => PMF.pure (d n)) (F.cramerShoupHashMod H))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2On (F.cramerShoupValid isElem d) encBits encBits
      (F.cramerShoupKeyGenProb d) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H isElem d) := by
  have hdesc : ∃ c k : ℕ, ∀ n, ∀ d' ∈ (PMF.pure (d n)).support,
      (F.encDesc d').length ≤ c * (n + 1) ^ k := by
    obtain ⟨c, k, hck⟩ := hd.tidy.polyBounded_length.exists_le
    refine ⟨c, k, fun n d' hd' => ?_⟩
    rw [PMF.support_pure, Set.mem_singleton_iff] at hd'
    subst hd'
    simpa only [encUnary_apply, List.length_replicate] using hck n
  have hgroup : F.cramerShoupGroupINDCCA2 (fun n => PMF.pure (d n)) H isElem :=
    hDDH.cramerShoupGroupINDCCA2 hH hisElem hmem hCR hm0
      (fun n d' hd' => by
        rw [PMF.support_pure, Set.mem_singleton_iff] at hd'
        subst hd'
        exact hm n)
      hinv hdesc
  intro adversary hA
  have hmid := hgroup adversary hA
  have h8 : Negligible fun n => (8 : ℝ≥0) / 2 ^ n := negligible_const_div_two_pow 8
  refine negligible_of_le ((h8.add hmid).add h8) fun n => ?_
  have h0 := F.advantage_cca2GameOn_cramerShoupGroupCCA2Game_le H isElem hmem d adversary false n
  have h1 := F.advantage_cca2GameOn_cramerShoupGroupCCA2Game_le H isElem hmem d adversary true n
  rw [Game.advantage_comm] at h1
  have htri1 := Game.advantage_triangle
    (ProbComp.eval
      (cca2GameOn (F.cramerShoupValid isElem d) encBits (F.cramerShoupKeyGenProb d)
        (F.cramerShoupEncryptProb H d) (F.cramerShoupDecryptOpt H isElem d) adversary false n))
    (F.cramerShoupGroupCCA2Game (fun n => PMF.pure (d n)) H isElem adversary false n)
    (ProbComp.eval
      (cca2GameOn (F.cramerShoupValid isElem d) encBits (F.cramerShoupKeyGenProb d)
        (F.cramerShoupEncryptProb H d) (F.cramerShoupDecryptOpt H isElem d) adversary true n))
  have htri2 := Game.advantage_triangle
    (F.cramerShoupGroupCCA2Game (fun n => PMF.pure (d n)) H isElem adversary false n)
    (F.cramerShoupGroupCCA2Game (fun n => PMF.pure (d n)) H isElem adversary true n)
    (ProbComp.eval
      (cca2GameOn (F.cramerShoupValid isElem d) encBits (F.cramerShoupKeyGenProb d)
        (F.cramerShoupEncryptProb H d) (F.cramerShoupDecryptOpt H isElem d) adversary true n))
  exact (htri1.trans (add_le_add le_rfl htri2)).trans
    (by rw [add_assoc]; exact add_le_add h0 (add_le_add le_rfl h1))

end Cslib.Crypto.PrimeOrderGroupFamily
