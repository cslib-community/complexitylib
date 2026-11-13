/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CramerShoup.Scheme
public import CslibFrontier.Crypto.Computational.CramerShoup.Reductions
public import CslibFrontier.Crypto.Computational.DiffieHellman.EncodingBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Tactic.GameHop

/-!
# The Cramer–Shoup public-key encryption scheme and 1CCA security under DDH

This module completes the single-challenge adaptive chosen-ciphertext (**1CCA / IND-CCA2** and
**1CCA with associated data**, Definition 12.2, printed p. 468, and Section 12.7, Definition 12.7,
printed pp. 501–502) security proof for the **Multiplicative Cramer–Shoup public-key encryption
scheme** ($\mathcal{E}_{\mathrm{MCS}}$, [Boneh and Shoup, Exercise 12.27, printed
pp. 521–522][BonehShoup2023], over an arbitrary associated-data type `AD : Type` as well as the
associated-data-free specialization) defined in
`CslibFrontier.Crypto.Computational.CramerShoup.Scheme`
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
and `cramerShoupEncryptProb`), yielding `DDH.indcca2ADOn_cramerShoup`,
`DDH.indcca2On_cramerShoup`, and (via the Theorem 12.1 batch-challenge hybrid reduction
`INDCCA2On.indcca2MultiOn`) batch-challenge multi-challenge CCA security
`DDH.indcca2MultiOn_cramerShoup`.

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
* **Fixed group description family in the native theorems**: the ideal-game theorems
  (`DDH.cramerShoupADGroupINDCCA2`, `DDH.cramerShoupGroupINDCCA2`) hold for an arbitrary setup law
  `setup : ℕ → PMF F.Desc`. The native theorems `DDH.indcca2ADOn_cramerShoup`,
  `DDH.indcca2On_cramerShoup`, and `DDH.indcca2MultiOn_cramerShoup` instead fix a polynomial-time
  computable family `d : ℕ → F.Desc`: the group at parameter `n` is `d n` and is not sampled, and
  DDH and collision resistance are assumed for the point-mass setup `fun n => PMF.pure (d n)`.
  Their hypotheses therefore make `n ↦ F.order (d n)` a sequence of primes that is computable in
  polynomial time from the unary parameter and has negligible inverse.
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
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())
  let choice := choiceOut.1
  let m₀ := encodeMsg (d, csChoiceMsg₀ choice)
  let m₁ := encodeMsg (d, csChoiceMsg₁ choice)
  let ad := encodeAD (d, csChoiceAD choice)
  if isElem (d, m₀) && isElem (d, m₁) then
    let m := if bit then m₁ else m₀
    let β ← PMF.uniformOfFintype (ZMod (F.order d))
    let ct := F.encodeCramerShoupEncrypt H d
      (F.encode d (csPkU pkVal), F.encode d (csPkH pkVal),
        F.encode d (csPkH₁ pkVal), F.encode d (csPkH₂ pkVal))
      m ad β.val
    let guessOut ← ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
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

/-- Shared challenge experiment for **Games 1 and 2** ([BonehShoup2023], Section 12.5.3, printed
p. 490) at fixed group `d` and triple exponents `(α, β, γ)`: sample the six secret-key exponents
uniformly from `ZMod (F.order d)` and compute the challenge ciphertext from
`(u, v, w) = (α • g, β • g, γ • g)` using the secret key via `encodeCramerShoupChallenge`. -/
noncomputable def cramerShoupChallengeGame
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ)
    (d : F.Desc) (α β γ : ZMod (F.order d)) : Game := do
  let U := PMF.uniformOfFintype (ZMod (F.order d))
  let σ ← U; let τ ← U; let σ₁ ← U; let τ₁ ← U; let σ₂ ← U; let τ₂ ← U
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let u := F.encode d (α • F.generator d)
  let v := F.encode d (β • F.generator d)
  let w := F.encode d (γ • F.generator d)
  let pk := F.encodeCramerShoupPublicKey d u sk
  let choiceOut ← ProbComp.eval ((OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())
  let choice := choiceOut.1
  let m₀ := encodeMsg (d, csChoiceMsg₀ choice)
  let m₁ := encodeMsg (d, csChoiceMsg₁ choice)
  let ad := encodeAD (d, csChoiceAD choice)
  if isElem (d, m₀) && isElem (d, m₁) then
    let m := if bit then m₁ else m₀
    let ct := F.encodeCramerShoupChallenge H d sk v w m ad
    let guessOut ← ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct ad))
      (adversary.guess n choice.2 ct)).run ())
    return guessOut.1
  else
    return false

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
  F.cramerShoupChallengeGame hasAD encodeMsg encodeAD H isElem adversary bit n d α β (α * β)

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
  simp only [cramerShoupMsgCCA2Game, cramerShoupGame1, cramerShoupChallengeGame,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, encodeCramerShoupPublicKey_encode, skNatOfZMod,
    csSkS, csSkT, csSkS₁, csSkT₁, csSkS₂, csSkT₂, csChoiceMsg₀, csChoiceMsg₁, csChoiceAD,
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
  by_cases h : (isElem (d, encodeMsg (d, csChoiceMsg₀ choiceOut.1)) &&
      isElem (d, encodeMsg (d, csChoiceMsg₁ choiceOut.1))) = true
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
  F.cramerShoupChallengeGame hasAD encodeMsg encodeAD H isElem adversary bit n d α β γ

private theorem advantage_eval_cramerShoupMsgToDDHDistinguisher_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ)
    (d : F.Desc) (α β γ : ZMod (F.order d)) :
    Game.advantage
      (ProbComp.eval
        (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit n d
          (α • F.generator d) (β • F.generator d) (γ • F.generator d)))
      (F.cramerShoupChallengeGame hasAD encodeMsg encodeAD H isElem adversary bit n d α β γ) ≤
      6 / 2 ^ n := by
  unfold cramerShoupChallengeGame cramerShoupMsgToDDHDistinguisher
  simp only [pmf_norm]
  refine F.advantage_bind_sampleCramerShoupSK_le n d _ _ fun s t s₁ t₁ s₂ t₂ => ?_
  rw [F.encodeCramerShoupPublicKey_eq_skNatOfZMod d α ((s, t), ((s₁, t₁), (s₂, t₂))),
    F.cramerShoupPhase1Oracle_eq_skNatOfZMod hasAD H isElem hmem d ((s, t), ((s₁, t₁), (s₂, t₂)))]
  refine congrArg _ (funext fun choiceOut => ?_)
  by_cases h : (isElem (d, encodeMsg (d, csChoiceMsg₀ choiceOut.1)) &&
      isElem (d, encodeMsg (d, csChoiceMsg₁ choiceOut.1))) = true
  · simp only [h, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure]
    rw [F.encodeCramerShoupChallenge_eq_skNatOfZMod H d ((s, t), ((s₁, t₁), (s₂, t₂))),
      F.cramerShoupPhase2Oracle_eq_skNatOfZMod hasAD H isElem hmem d ((s, t), ((s₁, t₁), (s₂, t₂)))]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]

private theorem advantage_four_le (g₁ g₂ g₃ g₄ : Game) {n : ℕ}
    (h₁ : Game.advantage g₂ g₁ ≤ 6 / 2 ^ n) (h₂ : Game.advantage g₃ g₄ ≤ 6 / 2 ^ n) :
    Game.advantage g₁ g₄ ≤ Game.advantage g₂ g₃ + 12 / 2 ^ n := by
  game_trans [g₂, g₃] using [h₁, le_rfl, h₂]

/-- **Game 1 $\to$ Game 2 bound** ([BonehShoup2023], Section 12.5.3, equation (12.22), printed
p. 492): the distinguishing advantage between `cramerShoupGame1` and `cramerShoupGame2` is at
most the DDH advantage of `cramerShoupMsgToDDHDistinguisher` plus `12 / 2 ^ n` (six approximate
`sampleModNat` secret-key exponent draws in `ddhRealGame` and six in `ddhRandomGame`). -/
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
        (F.ddhRandomGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      12 / 2 ^ n := by
  refine advantage_four_le _ _ _ _ ?_ ?_
  · unfold ddhRealGame cramerShoupGame1
    simp only [eval_ddhRealExperiment, PMF.monad_bind_eq_bind]
    peel_binds d α β
    exact F.advantage_eval_cramerShoupMsgToDDHDistinguisher_le hasAD encodeMsg encodeAD H isElem
      hmem adversary bit n d α β (α * β)
  · unfold ddhRandomGame cramerShoupGame2
    simp only [eval_ddhRandomExperiment, PMF.monad_bind_eq_bind]
    peel_binds d α β γ
    exact F.advantage_eval_cramerShoupMsgToDDHDistinguisher_le hasAD encodeMsg encodeAD H isElem
      hmem adversary bit n d α β γ

private noncomputable def cramerShoupExactCollisionInner
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (adversary : ADCCA2AdversaryOf Msg AD)
    (bit : Bool) (n : ℕ) (d : F.Desc)
    (α β γ σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) : Game := do
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let u := F.encode d (α • F.generator d)
  let v := F.encode d (β • F.generator d)
  let w := F.encode d (γ • F.generator d)
  let pk := F.encodeCramerShoupPublicKey d u sk
  let choiceOut ← ProbComp.eval ((OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())
  let choice := choiceOut.1
  if isElem (d, encodeMsg (d, csChoiceMsg₀ choice)) &&
      isElem (d, encodeMsg (d, csChoiceMsg₁ choice)) then
    let m := if bit then encodeMsg (d, csChoiceMsg₁ choice) else encodeMsg (d, csChoiceMsg₀ choice)
    let ad := encodeAD (d, csChoiceAD choice)
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
  else pure false

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
  F.cramerShoupExactCollisionInner hasAD encodeMsg encodeAD H isElem adversary bit n d
    α β γ σ τ σ₁ τ₁ σ₂ τ₂

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
  unfold cramerShoupGame2 cramerShoupChallengeGame cramerShoupGame3 cramerShoupExactCollisionGame
    cramerShoupExactCollisionInner
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
  by_cases h : (isElem (d, encodeMsg (d, csChoiceMsg₀ choiceOut.1)) &&
      isElem (d, encodeMsg (d, csChoiceMsg₁ choiceOut.1))) = true
  · simp only [h, ↓reduceIte]
    let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
    let v := F.encode d (β • F.generator d)
    let w := F.encode d (γ • F.generator d)
    let m := if bit then encodeMsg (d, csChoiceMsg₁ choiceOut.1)
      else encodeMsg (d, csChoiceMsg₀ choiceOut.1)
    let ad := encodeAD (d, csChoiceAD choiceOut.1)
    let ct := F.encodeCramerShoupChallenge H d sk v w m ad
    have hrun :
        (ProbComp.eval ((OracleComp.interpret
          (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
            (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct ad))
          (adversary.guess n (csChoiceState choiceOut.1) ct)).run ())).bind
            (fun guessOut => PMF.pure guessOut.1) =
        runStatelessOracle (F.cramerShoupPhase2Reply hasAD H isElem d sk ct ad)
          (adversary.guess n (csChoiceState choiceOut.1) ct) PMF.pure := rfl
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
      (adversary.guess n (csChoiceState choiceOut.1) ct) PMF.pure true
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
    unfold collisionGameFor Game.withSetup collisionExperiment cramerShoupExactCollisionGame C
      cramerShoupMsgToCollisionFinder
    simp only [pmf_norm, F.smul_encode]
    peel_binds d
    let kSK (α β γ : ZMod (F.order d)) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) : Game :=
      let u := F.encode d (α • F.generator d)
      let v := F.encode d (β • F.generator d)
      let w := F.encode d (γ • F.generator d)
      let pk := F.encodeCramerShoupPublicKey d u sk
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
        (adversary.choose n pk)).run ())).bind fun choiceOut =>
        let choice := choiceOut.1
        (ProbComp.eval
          (if isElem (d, encodeMsg (d, csChoiceMsg₀ choice)) &&
              isElem (d, encodeMsg (d, csChoiceMsg₁ choice)) then
            let m := if bit then encodeMsg (d, csChoiceMsg₁ choice)
              else encodeMsg (d, csChoiceMsg₀ choice)
            let ad := encodeAD (d, csChoiceAD choice)
            let ct := F.encodeCramerShoupChallenge H d sk v w m ad
            ((OracleComp.interpret
              (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
                (F.cramerShoupCollisionPhase2Oracle hasAD H isElem d sk ct ad))
              (adversary.guess n choice.2 ct)).run none) >>= fun out =>
              let target := extractCramerShoupTuple ct ad
              pure (out.2.getD target, target)
          else pure ([], []))).bind fun pair =>
          PMF.pure
            (isCollisionFor (F.cramerShoupHashMod H) (fun _ _ _ => true) n d pair.1 pair.2)
    have hstep1 := F.advantage_bind_sampleCramerShoupTripleExponents_le n d
      (fun α β γ => (ProbComp.eval (F.sampleCramerShoupSK n d)).bind (kSK α β γ))
    refine ((Game.advantage_triangle _ _ _).trans
      (add_le_add hstep1 (d := 6 / 2 ^ n) ?_)).trans_eq (by ring)
    peel_binds α β γ
    refine F.advantage_bind_sampleCramerShoupSK_le n d (kSK α β γ)
      (F.cramerShoupExactCollisionInner hasAD encodeMsg encodeAD H isElem adversary
        bit n d α β γ)
      fun s t s₁ t₁ s₂ t₂ => ?_
    dsimp only [kSK, cramerShoupExactCollisionInner]
    rw [F.encodeCramerShoupPublicKey_eq_skNatOfZMod d α ((s, t), ((s₁, t₁), (s₂, t₂))),
      F.cramerShoupPhase1Oracle_eq_skNatOfZMod hasAD H isElem hmem d
        ((s, t), ((s₁, t₁), (s₂, t₂)))]
    refine congrArg _ (funext fun choiceOut => ?_)
    by_cases h : (isElem (d, encodeMsg (d, csChoiceMsg₀ choiceOut.1)) &&
        isElem (d, encodeMsg (d, csChoiceMsg₁ choiceOut.1))) = true
    · simp only [pmf_norm, h, ↓reduceIte]
      rw [F.encodeCramerShoupChallenge_eq_skNatOfZMod H d
          ((s, t), ((s₁, t₁), (s₂, t₂))),
        F.cramerShoupCollisionPhase2Oracle_eq_skNatOfZMod hasAD H isElem hmem d
          ((s, t), ((s₁, t₁), (s₂, t₂)))]
      unfold runFinderOracle cramerShoupCollisionPhase2Oracle
      refine congrArg _ (funext fun out => ?_)
      cases out.2 with
      | none => simp
      | some cand => rfl
    · simp only [h, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind]
      rfl
  game_trans using [hadv]

/-- **Game 2 $\to$ Game 3 bound** (the collision-rejection hop into Game 4 of [BonehShoup2023],
Section 12.5.3, equations (12.24)–(12.25), printed p. 492, adapted to $\mathcal{E}_{\mathrm{MCS}}$
with associated data): if `isElem` accepts exactly the encodings of group elements, the
distinguishing advantage between `cramerShoupGame2` and `cramerShoupGame3` is bounded by the
collision-finding success probability of `cramerShoupMsgToCollisionFinder` plus `9 / 2 ^ n` (from
the nine approximate `sampleModNat` exponent draws in `cramerShoupMsgToCollisionFinder`). -/
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
        (F.ddhRandomGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      ((Q₁ + Q₂ + 1 : ℕ) : ℝ≥0) / (m : ℝ≥0) +
      21 / 2 ^ n := by
  game_trans [
    F.cramerShoupGame1 hasAD encodeMsg encodeAD setup H isElem adversary bit n,
    F.cramerShoupGame2 hasAD encodeMsg encodeAD setup H isElem adversary bit n,
    F.cramerShoupGame3 hasAD encodeMsg encodeAD setup H isElem adversary bit n,
    F.cramerShoupGame4 hasAD encodeMsg encodeAD setup H isElem adversary bit n]
    using [
      F.cramerShoupMsgCCA2Game_eq_game1 hasAD encodeMsg encodeAD setup H isElem adversary bit n,
      F.advantage_cramerShoupGame1_game2_le hasAD encodeMsg encodeAD setup H isElem hmem
        adversary bit n,
      F.advantage_cramerShoupGame2_game3_le hasAD encodeMsg encodeAD setup H isElem hmem
        adversary bit n,
      F.advantage_cramerShoupGame3_game4_le hasAD encodeMsg encodeAD setup H isElem hmem
        adversary bit n Q₁ Q₂ m hm0 hm hQ₁ hQ₂,
      F.advantage_cramerShoupGame4_game5_le hasAD encodeMsg encodeAD setup H isElem hmem
        adversary bit n m hm0 hm]
  exact le_of_eq (by push_cast; ring)

/-- Concrete upper-bound expression for the two-run single-bit Theorem 12.9 / Exercise 12.27 1CCA
reduction ([BonehShoup2023], equation (12.19), printed p. 489): the DDH advantages of
`cramerShoupMsgToDDHDistinguisher` at `false` and `true`, the collision-finding success
probabilities of `cramerShoupMsgToCollisionFinder` at `false` and `true`, plus
`(2 * Q₁ + 2 * Q₂ + 2) / m + 42 / 2 ^ n`. -/
noncomputable abbrev cramerShoupCCA2Bound
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (n Q₁ Q₂ m : ℕ) : ℝ≥0 :=
  Game.advantage
    (F.ddhRealGame setup
      (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary false) n)
    (F.ddhRandomGame setup
      (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary false) n) +
  Game.advantage
    (F.ddhRealGame setup
      (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary true) n)
    (F.ddhRandomGame setup
      (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary true) n) +
  Game.succProbability
    (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
      (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary false) n) +
  Game.succProbability
    (collisionGameFor setup (F.cramerShoupHashMod H) (fun _ _ _ => true)
      (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary true) n) +
  ((2 * Q₁ + 2 * Q₂ + 2 : ℕ) : ℝ≥0) / (m : ℝ≥0) +
  42 / 2 ^ n

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
      F.cramerShoupCCA2Bound hasAD encodeMsg encodeAD setup H isElem adversary n Q₁ Q₂ m := by
  have hfalse := F.advantage_cramerShoupMsgCCA2Game_game5_le hasAD encodeMsg encodeAD setup H
    isElem hmem adversary false n Q₁ Q₂ m hm0 hm hQ₁ hQ₂
  have htrue := F.advantage_cramerShoupMsgCCA2Game_game5_le hasAD encodeMsg encodeAD setup H
    isElem hmem adversary true n Q₁ Q₂ m hm0 hm hQ₁ hQ₂
  game_trans [
    F.cramerShoupGame5 hasAD encodeMsg encodeAD setup H isElem adversary false n,
    F.cramerShoupGame5 hasAD encodeMsg encodeAD setup H isElem adversary true n]
    using [hfalse,
      F.cramerShoupGame5_false_eq_true hasAD encodeMsg encodeAD setup H isElem adversary n,
      htrue]
  dsimp only [cramerShoupCCA2Bound]
  exact le_of_eq (by push_cast; ring)

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
      F.cramerShoupCCA2Bound hasAD encodeMsg encodeAD setup H isElem adversary
        n (Q₁ n) (Q₂ n) m :=
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
      F.cramerShoupCCA2Bound true Prod.snd (fun p => encAD p.2) setup H isElem adversary
        n (Q₁ n) (Q₂ n) m :=
  F.advantage_cramerShoupMsgCCA2Game_le true Prod.snd (fun p => encAD p.2) setup H isElem
    hmem adversary Q₁ Q₂ hQ n m hm0 hm

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
      F.cramerShoupCCA2Bound false Prod.snd (fun _ => []) setup H isElem adversary.toADUnit
        n (Q₁ n) (Q₂ n) m :=
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
      F.cramerShoupCCA2Bound true (fun p => F.encodeBit p.1 p.2) (fun p => encAD p.2) setup H
        isElem adversary n (Q₁ n) (Q₂ n) m :=
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
      F.cramerShoupCCA2Bound false (fun p => F.encodeBit p.1 p.2) (fun _ => []) setup H
        isElem adversary.toADUnit n (Q₁ n) (Q₂ n) m :=
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
  suffices h : ∀ pk, (F.encodeCramerShoupPublicKeyValues d pk).length ≤
      2 * (F.encDesc d).length + 44 * B + 30 by exact h _
  intro pk
  unfold encodeCramerShoupPublicKeyValues
  have h4 := F.length_encBits4_encode_le hB (csPkU pk) (csPkH pk) (csPkH₁ pk) (csPkH₂ pk)
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
  have hddh (bit : Bool) :=
    hDDH _ (F.isPPT_cramerShoupMsgToDDHDistinguisher hasAD hencMsg hencAD hH hisElem hA bit)
  have hcr (bit : Bool) :=
    hCR.negligible _
      (F.isPPTOn_cramerShoupMsgToCollisionFinder hasAD hencMsg hencAD hH hisElem hA bit)
  have hLd : PolynomiallyBounded Ld :=
    .mul (.const cd) (.pow (.add .id (.const 1)) kd)
  have hB : PolynomiallyBounded B :=
    .mul (.const ce) (.pow (.add hLd (.const 1)) ke)
  have hLpk : PolynomiallyBounded Lpk :=
    .add (.add (.mul (.const 2) hLd) (.mul (.const 44) hB)) (.const 30)
  have hLct : PolynomiallyBounded Lct :=
    .add (.mul (.const 22) hB) (.const 14)
  have hLst : PolynomiallyBounded Lst :=
    .mul (.const cs) (.pow (.add (.add .id hLpk) (.const 2)) ds)
  have hQ₁ : PolynomiallyBounded Q₁ :=
    .mul (.const c₁) (.pow (.add (.add .id hLpk) (.const 2)) d₁)
  have hQ₂ : PolynomiallyBounded Q₂ :=
    .mul (.const c₂) (.pow (.add (.add (.add .id hLst) hLct) (.const 2)) d₂)
  have hpoly_Q : PolynomiallyBounded (fun n => 2 * Q₁ n + 2 * Q₂ n + 2) :=
    .add (.add (.mul (.const 2) hQ₁) (.mul (.const 2) hQ₂)) (.const 2)
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
    ((((((hddh false).add (hddh true)).add (hcr false)).add (hcr true)).add hq_neg).add h42_neg)
    (fun n => ?_)
  have hB_le : ∀ {d}, d ∈ (setup n).support → ∀ x : F.Carrier d, (F.encode d x).length ≤ B n :=
    fun hd x => (henc_le _ x).trans (by have := hdesc_le n _ hd; dsimp only [B]; gcongr)
  have hpk_le : ∀ {d}, d ∈ (setup n).support → ∀ α δ δ₁ δ₂,
      (F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d))
        (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0)).length ≤ Lpk n :=
    fun hd α _ _ _ => (F.length_encodeCramerShoupPublicKey_le (hB_le hd) α _).trans
      (by have := hdesc_le n _ hd; dsimp only [Lpk]; gcongr)
  refine F.advantage_cramerShoupMsgCCA2Game_le_of_honest_bounds hasAD encodeMsg encodeAD setup H
    isElem hmem adversary n (Q₁ n) (Q₂ n) (m n) (hm0 n) (hm n)
    (fun d hd α δ δ₁ δ₂ => by
      refine (hQ₁_raw n _).mono ?_
      have := hpk_le hd α δ δ₁ δ₂; dsimp only [Q₁]; gcongr)
    ?_
  intro d hd α β γ δ τ δ₁ δ₂ ξ choiceOut hchoice mElem
  rw [ProbOracleComp.eval_run_interpret_eq_runWith] at hchoice
  have hpk := hpk_le hd α δ δ₁ δ₂
  have hst : (csChoiceState choiceOut.1).length ≤ Lst n :=
    (hstate n _ Unit _ () choiceOut.2 choiceOut.1 hchoice).trans (by dsimp only [Lst]; gcongr)
  have hct := F.length_encBits4_encode_le (hB_le hd)
    (β • F.generator d) (γ • F.generator d)
    (projHash F d (δ - α * τ) τ (β • F.generator d) (γ • F.generator d) + mElem)
    ((β * (δ₁ + F.cramerShoupHashMod H d
      (encBits4 (F.encode d (β • F.generator d), F.encode d (γ • F.generator d),
        F.encode d (projHash F d (δ - α * τ) τ (β • F.generator d) (γ • F.generator d) + mElem),
        encodeAD (d, csChoiceAD choiceOut.1))) * δ₂) + (γ - α * β) * ξ) • F.generator d)
  refine (hQ₂_raw n (csChoiceState choiceOut.1) _).mono ?_
  dsimp only [Q₂, Lct] at hct ⊢; gcongr

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
    F.cramerShoupADGroupINDCCA2 encAD setup H isElem := by
  have h := hDDH.cramerShoupMsgINDCCA2 true (encodeAD := fun p => encAD p.2)
    (.of_tidy (ComputableTidilyInPolyTime.snd F.encDesc encBits))
    (.of_tidy ((ComputableTidilyInPolyTime.encode encAD).comp
      (ComputableTidilyInPolyTime.snd F.encDesc encAD)))
    hH hisElem hmem hCR hm0 hm hinv hdesc
  exact h

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
  have h := hDDH.cramerShoupMsgINDCCA2 false (encodeAD := fun _ : F.Desc × Unit => [])
    (.of_tidy (ComputableTidilyInPolyTime.snd F.encDesc encBits))
    (.of_tidy (.const (encIn := encPair F.encDesc encUnit) []))
    hH hisElem hmem hCR hm0 hm hinv hdesc
  intro adversary hA
  exact h adversary.toADUnit hA.toADUnit

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
    F.cramerShoupADINDCCA2 encAD setup H isElem := by
  have h := hDDH.cramerShoupMsgINDCCA2 true (encodeAD := fun p => encAD p.2)
    F.computableInPolyTime_encodeBit
    (.of_tidy ((ComputableTidilyInPolyTime.encode encAD).comp
      (ComputableTidilyInPolyTime.snd F.encDesc encAD)))
    hH hisElem hmem hCR hm0 hm hinv hdesc
  exact h

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
  have h := hDDH.cramerShoupMsgINDCCA2 false (encodeAD := fun _ : F.Desc × Unit => [])
    F.computableInPolyTime_encodeBit
    (.of_tidy (.const (encIn := encPair F.encDesc encUnit) []))
    hH hisElem hmem hCR hm0 hm hinv hdesc
  intro adversary hA
  exact h adversary.toADUnit hA.toADUnit


/-! ### `Encryption.cca2ADGameOn`, `Encryption.INDCCA2ADOn`, `Encryption.cca2GameOn`, and
`Encryption.INDCCA2On` instantiations -/

private theorem advantage_four_le_eight (g₁ g₂ g₃ g₄ : Game) {n : ℕ}
    (h₁ : Game.advantage g₁ g₂ ≤ 1 / 2 ^ n)
    (h₂ : Game.advantage g₂ g₃ ≤ 6 / 2 ^ n)
    (h₃ : Game.advantage g₃ g₄ ≤ 1 / 2 ^ n) :
    Game.advantage g₁ g₄ ≤ 8 / 2 ^ n := by
  game_trans [g₂, g₃] using [h₁, h₂, h₃]

private theorem eval_run_interpret_map_bind
    {α β γ State : Type}
    (oracle : Unit × List Bool → StateT State ProbComp (List Bool))
    (f : α → β) (oa : WordOracleComp Unit α) (s : State)
    (k : β × State → PMF γ) :
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) oracle)
      (f <$> oa)).run s)).bind k =
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) oracle)
      oa).run s)).bind (fun p => k (f p.1, p.2)) := by
  rw [OracleComp.interpret_map, StateT.run_map]
  simp only [pmf_norm, ← bind_pure_comp]

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
  let m := if bit then csChoiceMsg₁ choiceOut.1 else csChoiceMsg₀ choiceOut.1
  let adBits := encodeAD (d, csChoiceAD choiceOut.1)
  let ct := F.encodeCramerShoupEncrypt H d
    (F.encode d (csPkU pkVal), F.encode d (csPkH pkVal),
      F.encode d (csPkH₁ pkVal), F.encode d (csPkH₂ pkVal)) m adBits β.val
  (ProbComp.eval ((OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct adBits))
    (adversary.guess n (csChoiceState choiceOut.1) ct)).run ())).bind
    (fun guessOut => PMF.pure guessOut.1)

private noncomputable def cramerShoupCCA2InnerSK
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ)
    (α σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) (useExactB : Bool) : Game := do
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let pk := F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d)) sk
  let choiceOut ← ProbComp.eval ((OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())
  if isElem (d, csChoiceMsg₀ choiceOut.1) && isElem (d, csChoiceMsg₁ choiceOut.1) then
    if useExactB then
      let β ← PMF.uniformOfFintype (ZMod (F.order d))
      F.cramerShoupCCA2InnerB hasAD encodeAD H isElem d adversary bit n
        α σ τ σ₁ τ₁ σ₂ τ₂ choiceOut β
    else
      let b ← ProbComp.eval (F.sampleExp n d)
      F.cramerShoupCCA2InnerB hasAD encodeAD H isElem d adversary bit n
        α σ τ σ₁ τ₁ σ₂ τ₂ choiceOut (b : ZMod (F.order d))
  else
    pure false

private noncomputable def cramerShoupCCA2SampledSK
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ)
    (α : ZMod (F.order d)) : Game :=
  (ProbComp.eval (F.sampleCramerShoupSK n d)).bind fun sk =>
    F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n α
      ((csSkS sk : ℕ) : ZMod (F.order d)) ((csSkT sk : ℕ) : ZMod (F.order d))
      ((csSkS₁ sk : ℕ) : ZMod (F.order d)) ((csSkT₁ sk : ℕ) : ZMod (F.order d))
      ((csSkS₂ sk : ℕ) : ZMod (F.order d)) ((csSkT₂ sk : ℕ) : ZMod (F.order d)) false

private noncomputable def cramerShoupCCA2UniformSK
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ)
    (useExactB : Bool) : Game := do
  let U := PMF.uniformOfFintype (ZMod (F.order d))
  let α ← U; let σ ← U; let τ ← U; let σ₁ ← U; let τ₁ ← U; let σ₂ ← U; let τ₂ ← U
  F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n
    α σ τ σ₁ τ₁ σ₂ τ₂ useExactB

private theorem advantage_cramerShoupCCA2InnerSK_le
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ) :
    Game.advantage
      ((ProbComp.eval (F.sampleExp n d)).bind fun a =>
        F.cramerShoupCCA2SampledSK hasAD encodeAD H isElem d adversary bit n
          (a : ZMod (F.order d)))
      (F.cramerShoupCCA2UniformSK hasAD encodeAD H isElem d adversary bit n true) ≤
      8 / 2 ^ n := by
  unfold cramerShoupCCA2UniformSK
  simp only [PMF.monad_bind_eq_bind]
  refine advantage_four_le_eight _
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind
      (F.cramerShoupCCA2SampledSK hasAD encodeAD H isElem d adversary bit n))
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ₁ =>
            (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ₁ =>
              (PMF.uniformOfFintype (ZMod (F.order d))).bind fun σ₂ =>
                (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ₂ =>
                  F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n
                    α σ τ σ₁ τ₁ σ₂ τ₂ false) _
    (F.advantage_bind_sampleExp_le n d
      (F.cramerShoupCCA2SampledSK hasAD encodeAD H isElem d adversary bit n))
    (advantage_bind_le_nnreal _ _ _ fun α =>
      F.advantage_bind_sampleCramerShoupSK_le n d _ (fun σ τ σ₁ τ₁ σ₂ τ₂ =>
        F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n
          α σ τ σ₁ τ₁ σ₂ τ₂ false) (fun _ _ _ _ _ _ => rfl)) ?_
  peel_binds α σ τ σ₁ τ₁ σ₂ τ₂
  dsimp only [cramerShoupCCA2InnerSK]
  peel_binds choiceOut
  by_cases h : (isElem (d, csChoiceMsg₀ choiceOut.1) && isElem (d, csChoiceMsg₁ choiceOut.1)) = true
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    exact F.advantage_bind_sampleExp_le n d
      (F.cramerShoupCCA2InnerB hasAD encodeAD H isElem d adversary bit n
        α σ τ σ₁ τ₁ σ₂ τ₂ choiceOut)
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Game.advantage_self, zero_le]

private theorem cramerShoupMsgCCA2Game_pure_eq_innerSK
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (d : ℕ → F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ) :
    F.cramerShoupMsgCCA2Game hasAD (fun p => p.2) encodeAD (fun n => PMF.pure (d n)) H isElem
      adversary bit n =
    F.cramerShoupCCA2UniformSK hasAD encodeAD H isElem (d n) adversary bit n true := by
  simp only [pmf_norm, cramerShoupMsgCCA2Game, cramerShoupCCA2UniformSK]
  refine congrArg _ (funext fun α => congrArg _ (funext fun σ =>
    congrArg _ (funext fun τ => congrArg _ (funext fun σ₁ =>
      congrArg _ (funext fun τ₁ => congrArg _ (funext fun σ₂ =>
        congrArg _ (funext fun τ₂ => ?_)))))))
  simp only [cramerShoupCCA2InnerSK, cramerShoupCCA2InnerB, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, ↓reduceIte,
    encodeCramerShoupPublicKey_encode, skNatOfZMod,
    csPkU, csPkH, csPkH₁, csPkH₂, csSkS, csSkT, csSkS₁, csSkT₁, csSkS₂, csSkT₂,
    csChoiceMsg₀, csChoiceMsg₁, csChoiceAD, ZMod.natCast_zmod_val]

private theorem cramerShoupCCA2InnerSK_false_eq
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n a : ℕ)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    let pk := F.encodeCramerShoupPublicKey d
      (F.encode d ((a : ZMod (F.order d)) • F.generator d)) sk
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
      (adversary.choose n pk)).run ())).bind (fun choiceOut =>
        ProbComp.eval
          (if (isElem (d, csChoiceMsg₀ choiceOut.1) &&
              isElem (d, csChoiceMsg₁ choiceOut.1)) = true then do
            let b ← F.sampleExp n d
            let ct := F.encodeCramerShoupEncrypt H d (decodeBits4 (dropFrame pk))
              (if bit then csChoiceMsg₁ choiceOut.1 else csChoiceMsg₀ choiceOut.1)
              (encodeAD (d, csChoiceAD choiceOut.1)) b
            let guessOut ← (OracleComp.interpret
              (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
                (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct
                  (encodeAD (d, csChoiceAD choiceOut.1))))
              (adversary.guess n (csChoiceState choiceOut.1) ct)).run ()
            return guessOut.1
          else
            return false)) =
    F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n
      (a : ZMod (F.order d))
      ((csSkS sk : ℕ) : ZMod (F.order d)) ((csSkT sk : ℕ) : ZMod (F.order d))
      ((csSkS₁ sk : ℕ) : ZMod (F.order d)) ((csSkT₁ sk : ℕ) : ZMod (F.order d))
      ((csSkS₂ sk : ℕ) : ZMod (F.order d)) ((csSkT₂ sk : ℕ) : ZMod (F.order d)) false := by
  dsimp only [cramerShoupCCA2InnerSK]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [F.encodeCramerShoupPublicKey_eq_skNatOfZMod d (a : ZMod (F.order d)) sk,
    F.cramerShoupPhase1Oracle_eq_skNatOfZMod hasAD H isElem hmem d sk]
  refine congrArg _ (funext fun choiceOut => ?_)
  by_cases h : (isElem (d, csChoiceMsg₀ choiceOut.1) && isElem (d, csChoiceMsg₁ choiceOut.1)) = true
  · simp only [pmf_norm, h, ↓reduceIte, Bool.false_eq_true,
      F.decodeBits4_dropFrame_encodeCramerShoupPublicKey, cramerShoupCCA2InnerB]
    refine congrArg _ (funext fun b => ?_)
    have hct :=
      F.encodeCramerShoupEncrypt_skNatOfZMod H d (a : ZMod (F.order d))
        ((csSkS sk : ℕ) : ZMod (F.order d)) ((csSkT sk : ℕ) : ZMod (F.order d))
        ((csSkS₁ sk : ℕ) : ZMod (F.order d)) ((csSkT₁ sk : ℕ) : ZMod (F.order d))
        ((csSkS₂ sk : ℕ) : ZMod (F.order d)) ((csSkT₂ sk : ℕ) : ZMod (F.order d))
        (if bit then csChoiceMsg₁ choiceOut.1 else csChoiceMsg₀ choiceOut.1)
        (encodeAD (d, csChoiceAD choiceOut.1)) b
    rw [hct, F.cramerShoupPhase2Oracle_eq_skNatOfZMod hasAD H isElem hmem d sk]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]

private theorem exists_length_encDesc_pure_le {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ∃ c k : ℕ, ∀ n, ∀ d' ∈ (PMF.pure (d n)).support,
      (F.encDesc d').length ≤ c * (n + 1) ^ k := by
  obtain ⟨c, k, hck⟩ := hd.tidy.polyBounded_length.exists_le
  refine ⟨c, k, fun n d' hd' => ?_⟩
  rw [PMF.support_pure, Set.mem_singleton_iff] at hd'
  subst hd'
  simpa only [encUnary_apply, List.length_replicate] using hck n

private theorem order_pure_ge {d : ℕ → F.Desc} {m : ℕ → ℕ}
    (hm : ∀ n, m n ≤ F.order (d n)) :
    ∀ n, ∀ d' ∈ (PMF.pure (d n)).support, m n ≤ F.order d' := by
  intro n d' hd'
  rw [PMF.support_pure, Set.mem_singleton_iff] at hd'
  exact hd' ▸ hm n

private theorem negligible_advantage_of_eight_le {g₀ g₁ h₀ h₁ : ℕ → Game}
    (hmid : Negligible fun n => Game.advantage (h₀ n) (h₁ n))
    (hle₀ : ∀ n, Game.advantage (g₀ n) (h₀ n) ≤ 8 / 2 ^ n)
    (hle₁ : ∀ n, Game.advantage (g₁ n) (h₁ n) ≤ 8 / 2 ^ n) :
    Negligible fun n => Game.advantage (g₀ n) (g₁ n) := by
  have h8 : Negligible fun n => (8 : ℝ≥0) / 2 ^ n := negligible_const_div_two_pow 8
  refine negligible_of_le ((h8.add hmid).add h8) fun n => ?_
  have h0 := hle₀ n
  have h1 := hle₁ n
  rw [Game.advantage_comm] at h1
  exact ((Game.advantage_triangle (g₀ n) (h₀ n) (g₁ n)).trans
    (add_le_add le_rfl (Game.advantage_triangle (h₀ n) (h₁ n) (g₁ n)))).trans
    (by rw [add_assoc]; exact add_le_add h0 (add_le_add le_rfl h1))

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
        F.cramerShoupCCA2SampledSK true (fun p => encAD p.2) H isElem (d n) adversary bit n
          (a : ZMod (F.order (d n))) := by
    simp only [pmf_norm, cca2ADGameOn, cramerShoupKeyGenProb, cramerShoupADEncryptProb,
      cramerShoupValid, F.smul_encode, F.cca2ADPhase1Oracle_cramerShoupADDecryptOpt,
      F.cca2ADPhase2Oracle_cramerShoupADDecryptOpt, cramerShoupCCA2SampledSK, bind_assoc, pure_bind]
    exact congrArg _ (funext fun a => congrArg _ (funext fun sk =>
      F.cramerShoupCCA2InnerSK_false_eq true (fun p => encAD p.2) H isElem hmem (d n)
        adversary bit n a sk))
  rw [hgame0, cramerShoupADGroupCCA2Game,
    F.cramerShoupMsgCCA2Game_pure_eq_innerSK true (fun p => encAD p.2) H isElem d adversary bit n]
  exact F.advantage_cramerShoupCCA2InnerSK_le true (fun p => encAD p.2) H isElem (d n)
    adversary bit n

/-- **Theorem 12.9 & Exercise 12.27 via `Encryption.INDCCA2ADOn`**: for any associated-data
encoding `encAD : AD ↪ List Bool`, polynomial-time group description family `d : ℕ → F.Desc`, and
polynomial-time `H` and `isElem` such that `isElem` accepts exactly the encodings of group
elements, the probabilistic polynomial-time Multiplicative Cramer–Shoup encryption scheme with
associated data `(cramerShoupKeyGenProb d, cramerShoupADEncryptProb encAD H d,
cramerShoupADDecryptOpt H isElem d)` satisfies the native `Encryption.INDCCA2ADOn` notion with
respect to the group-membership admissibility predicate `cramerShoupValid isElem d` under DDH and
collision resistance of `cramerShoupHashMod H`, both for the point-mass setup
`fun n => PMF.pure (d n)`, and a positive lower bound `m n ≤ F.order (d n)` with `1 / m n`
negligible. The group at parameter `n` is the fixed description `d n`; it is not sampled. -/
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
  have hgroup : F.cramerShoupADGroupINDCCA2 encAD (fun n => PMF.pure (d n)) H isElem :=
    hDDH.cramerShoupADGroupINDCCA2 encAD hH hisElem hmem hCR hm0 (F.order_pure_ge hm)
      hinv (F.exists_length_encDesc_pure_le hd)
  intro adversary hA
  dsimp only [INDCCA2ADOn, Game.Indistinguishable]
  exact negligible_advantage_of_eight_le (hgroup adversary hA)
    (F.advantage_cca2ADGameOn_cramerShoupADGroupCCA2Game_le encAD H isElem hmem d adversary false)
    (F.advantage_cca2ADGameOn_cramerShoupADGroupCCA2Game_le encAD H isElem hmem d adversary true)

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
        F.cramerShoupCCA2SampledSK false (fun _ => []) H isElem (d n) adversary.toADUnit bit n
          (a : ZMod (F.order (d n))) := by
    simp only [pmf_norm, cca2GameOn, cramerShoupKeyGenProb, cramerShoupEncryptProb,
      cramerShoupValid, F.smul_encode, F.cca2Phase1Oracle_cramerShoupDecryptOpt,
      F.cca2Phase2Oracle_cramerShoupDecryptOpt, cramerShoupCCA2SampledSK, bind_assoc, pure_bind]
    refine congrArg _ (funext fun a => congrArg _ (funext fun sk => ?_))
    rw [← F.cramerShoupCCA2InnerSK_false_eq false (fun _ => []) H isElem hmem (d n)
      adversary.toADUnit bit n a sk]
    dsimp only [CCA2AdversaryOf.toADUnit]
    rw [eval_run_interpret_map_bind]
  rw [hgame0, cramerShoupGroupCCA2Game,
    F.cramerShoupMsgCCA2Game_pure_eq_innerSK false (fun _ => []) H isElem d adversary.toADUnit
      bit n]
  exact F.advantage_cramerShoupCCA2InnerSK_le false (fun _ => []) H isElem (d n)
    adversary.toADUnit bit n

/-- **Theorem 12.9 & Exercise 12.27 via `Encryption.INDCCA2On`**: for any polynomial-time group
description family `d : ℕ → F.Desc` and polynomial-time `H` and `isElem` such that `isElem`
accepts exactly the encodings of group elements, the probabilistic polynomial-time Cramer–Shoup
encryption scheme `(cramerShoupKeyGenProb d, cramerShoupEncryptProb H d,
cramerShoupDecryptOpt H isElem d)` satisfies the native `Encryption.INDCCA2On` notion with respect
to the group-membership admissibility predicate `cramerShoupValid isElem d` under DDH and
collision resistance of `cramerShoupHashMod H`, both for the point-mass setup
`fun n => PMF.pure (d n)`, and a positive lower bound `m n ≤ F.order (d n)` with `1 / m n`
negligible. The group at parameter `n` is the fixed description `d n`; it is not sampled. -/
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
  have hgroup : F.cramerShoupGroupINDCCA2 (fun n => PMF.pure (d n)) H isElem :=
    hDDH.cramerShoupGroupINDCCA2 hH hisElem hmem hCR hm0 (F.order_pure_ge hm)
      hinv (F.exists_length_encDesc_pure_le hd)
  intro adversary hA
  dsimp only [INDCCA2On, Game.Indistinguishable]
  exact negligible_advantage_of_eight_le (hgroup adversary hA)
    (F.advantage_cca2GameOn_cramerShoupGroupCCA2Game_le H isElem hmem d adversary false)
    (F.advantage_cca2GameOn_cramerShoupGroupCCA2Game_le H isElem hmem d adversary true)

/-- **Batch-challenge multi-challenge CCA security of Multiplicative Cramer–Shoup
(`Encryption.INDCCA2MultiOn`)** (batch-challenge specialization of [BonehShoup2023], Theorem 12.1,
together with Theorem 12.9 and Exercise 12.27, printed pp. 468, 490–491, 521–522): for any
polynomial-time group description family `d : ℕ → F.Desc` and polynomial-time `H` and `isElem`
such that `isElem` accepts exactly the encodings of group elements, the probabilistic
polynomial-time Cramer–Shoup encryption scheme `(cramerShoupKeyGenProb d,
cramerShoupEncryptProb H d, cramerShoupDecryptOpt H isElem d)` satisfies the two-phase
batch-challenge multi-challenge `Encryption.INDCCA2MultiOn` notion with respect to
`cramerShoupValid isElem d` under DDH and collision resistance of `cramerShoupHashMod H`, both for
the point-mass setup `fun n => PMF.pure (d n)`, and a positive lower bound `m n ≤ F.order (d n)`
with `1 / m n` negligible. The group at parameter `n` is the fixed description `d n`; it is not
sampled. -/
theorem DDH.indcca2MultiOn_cramerShoup
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
    INDCCA2MultiOn (F.cramerShoupValid isElem d) encBits encBits
      (F.cramerShoupKeyGenProb d) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H isElem d) :=
  (hDDH.indcca2On_cramerShoup hH hisElem hd hmem hCR hm0 hm hinv).indcca2MultiOn
    (F.computableInPolyTime_cramerShoupValid hisElem hd)
    (F.isPPTOn_cramerShoupKeyGenProb hd)
    (F.isPPTOn_cramerShoupEncryptProb hH hd)
    (F.computableInPolyTime_cramerShoupDecryptOpt hH hisElem hd)

end Cslib.Crypto.PrimeOrderGroupFamily
