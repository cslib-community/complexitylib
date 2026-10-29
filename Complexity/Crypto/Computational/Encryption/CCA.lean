/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle.Parameter
public import Complexity.Crypto.Computational.Encryption.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT

/-!
# Chosen-ciphertext security for public-key encryption (1CCA / IND-CCA2)

This module defines the single-challenge adaptive chosen-ciphertext security experiment (**1CCA**,
also called **IND-CCA2**) for public-key encryption over an arbitrary message type `Msg` and
decryption output type `Out`, following [Boneh and Shoup, Section 12.1, Attack Game 12.1 and
Definition 12.2, printed pp. 467–469][BonehShoup2023].

## Source Statements ([BonehShoup2023], Section 12.1, printed pp. 467–469)

Verbatim from [BonehShoup2023], Section 12.1 (printed pp. 467–468):

> **Attack Game 12.1 (CCA security).** For a given public-key encryption scheme
> $\mathcal{E} = (G, E, D)$, defined over $(\mathcal{M}, \mathcal{C})$, and for a given adversary
> $\mathcal{A}$, we define two experiments.
> **Experiment $b$** ($b = 0, 1$):
> - The challenger computes $(pk, sk) \xleftarrow{R} G()$ and sends $pk$ to the adversary.
> - $\mathcal{A}$ then makes a series of queries to the challenger. Each query can be one of two
>   types:
>   - **Encryption query:** for $i = 1, 2, \ldots$, the $i$th encryption query consists of a pair
>     of messages $(m_{i0}, m_{i1}) \in \mathcal{M}^2$, of the same length. The challenger computes
>     $c_i \xleftarrow{R} E(pk, m_{ib})$ and sends $c_i$ to $\mathcal{A}$.
>   - **Decryption query:** for $j = 1, 2, \ldots$, the $j$th decryption query consists of a
>     ciphertext $\hat{c}_j \in \mathcal{C}$ that is not among the responses to the previous
>     encryption queries, i.e.,
>     $$\hat{c}_j \notin \{c_1, c_2, \ldots\}.$$
>     The challenger computes $\hat{m}_j \leftarrow D(sk, \hat{c}_j)$, and sends $\hat{m}_j$ to
>     $\mathcal{A}$.
> - At the end of the game, the adversary outputs a bit $\hat{b} \in \{0, 1\}$.
>
> Let $W_b$ be the event that $\mathcal{A}$ outputs $1$ in Experiment $b$ and define
> $\mathcal{A}$'s advantage with respect to $\mathcal{E}$ as
> $$\text{CCAadv}[\mathcal{A}, \mathcal{E}] := |\Pr[W_0] - \Pr[W_1]|.$$
>
> **Definition 12.1 (CCA Security).** A public-key encryption scheme $\mathcal{E}$ is called
> **semantically secure against a chosen ciphertext attack**, or simply **CCA secure**, if for all
> efficient adversaries $\mathcal{A}$, the value $\text{CCAadv}[\mathcal{A}, \mathcal{E}]$ is
> negligible.
>
> Just as we did in the symmetric-key setting, we can consider a restricted attack game in which
> the adversary makes only a single encryption query:
>
> **Definition 12.2 (1CCA security).** In Attack Game 12.1, if the adversary $\mathcal{A}$ is
> restricted to making a single encryption query, we denote its advantage by
> $\text{1CCAadv}[\mathcal{A}, \mathcal{E}]$. A public-key encryption scheme $\mathcal{E}$ is
> **one-time semantically secure against chosen ciphertext attack**, or simply, **1CCA secure**, if
> for all efficient adversaries $\mathcal{A}$, the value $\text{1CCAadv}[\mathcal{A}, \mathcal{E}]$
> is negligible.

And the two-phase decomposition of the 1CCA experiment (printed pp. 468–469):

> **Initialization phase:** the challenger generates $(pk, sk) \xleftarrow{R} G()$ and sends $pk$
> to the adversary.
> **Phase 1:** the adversary submits a series of decryption queries to the challenger; each such
> query is a ciphertext $\hat{c} \in \mathcal{C}$, to which the challenger responds with
> $\hat{m} \leftarrow D(sk, \hat{c})$.
> **Encryption query:** the adversary submits a single encryption query $(m_0, m_1)$ to the
> challenger; in Experiment $b$ (where $b = 0, 1$), the challenger responds with
> $c \xleftarrow{R} E(pk, m_b)$.
> **Phase 2:** the adversary again submits a series of decryption queries to the challenger; each
> such query is a ciphertext $\hat{c} \in \mathcal{C}$, subject to the restriction that
> $\hat{c} \ne c$, to which the challenger responds with $\hat{m} \leftarrow D(sk, \hat{c})$.
> **Finish:** at the end of the game, the adversary outputs a bit $\hat{b} \in \{0, 1\}$.

## Scope and Specializations

* **Single-challenge 1CCA (`Definition 12.2`) vs. symmetric `SymmetricCipher.INDCCA`
  (`Definition 9.5`)**:
  `CCA2AdversaryOf Msg`, `cca2Game`, and `INDCCA2Of` formalize the single-challenge public-key
  1CCA experiment (Definition 12.2, printed p. 468). Unlike `SymmetricCipher.INDCCA` and
  `SymmetricCipher.CCAAdversary` in `Complexity/Crypto/Computational/Encryption/Authenticated.lean`
  (which model multi-query symmetric-key CCA, Definition 9.5, using a single-stage adversary with a
  two-channel encryption/decryption oracle `Operation = Bool`), a public-key 1CCA adversary receives
  the public key `pk` directly and interacts with a single-channel decryption oracle
  (`Operation = Unit`) across two stages (`choose` and `guess`) around one challenge encryption.
  Because anyone can encrypt under `pk`, public-key 1CCA is equivalent to multi-challenge CCA by a
  hybrid argument ([BonehShoup2023], Theorem 12.1, printed p. 468); that multi-challenge equivalence
  is not formalized here.
* **Phase 2 challenge-rejection convention**: in Phase 2, querying the challenge ciphertext
  (`request.2 == ct`) returns `[] = encOption encOut none` (the encoding of decryption rejection
  `none`) rather than syntactically restricting the oracle domain to `ĉ ≠ c`. Because the adversary
  is given `ct` as input to `guess` and could simulate the constant `[]` reply on `ct` itself, this
  convention is equivalent to forbidding `ĉ = c` and matches `SymmetricCipher.ccaOracle` in
  `Complexity/Crypto/Computational/Encryption/Authenticated.lean`.
* **No associated data ($\mathcal{D} = \mathrm{Unit}$)**: encryption and decryption queries carry no
  separate associated-data argument (corresponding to $\mathcal{D} = \mathrm{Unit}$ in schemes with
  associated data such as Exercise 12.27).
* **Generic message and output types with challenge-pair admissibility**:
  `CCA2AdversaryOf (Msg : Type)` is generic in the challenge message type `Msg` (`CCA2Adversary`
  specializes to `Bool`, and `WordCCA2Adversary` to `List Bool`). `cca2GameOn` and `INDCCA2On`
  parameterize the experiment by a challenge-pair admissibility predicate
  `valid : ℕ → List Bool → Msg → Msg → Bool` (returning `false` in both experiments when
  `valid n pk m₀ m₁ = false`), while `cca2Game` and `INDCCA2Of` specialize to `fun _ _ _ _ => true`
  for fixed-length message spaces (such as `Bool`) and `WordINDCCA2` specializes to Attack Game
  12.1's equal-length rule `fun _ _ m₀ m₁ => m₀.length == m₁.length`.

## Main definitions

* `Cslib.Crypto.Encryption.CCA2AdversaryOf`, `Cslib.Crypto.Encryption.CCA2Adversary`,
  `Cslib.Crypto.Encryption.WordCCA2Adversary`: two-stage 1CCA adversaries with
  `WordOracleComp Unit` decryption-oracle access in Phase 1 (`choose`) and Phase 2 (`guess`).
* `Cslib.Crypto.Encryption.CCA2AdversaryOf.IsPPT`,
  `Cslib.Crypto.Encryption.CCA2AdversaryOf.IsQueryBounded`: uniform strict oracle PPT admissibility
  and per-stage decryption-query bounds.
* `Cslib.Crypto.Encryption.cca2Phase1Oracle`, `Cslib.Crypto.Encryption.cca2Phase2Oracle`,
  `Cslib.Crypto.Encryption.cca2GameOn`, `Cslib.Crypto.Encryption.cca2Game`: Phase 1 and Phase 2
  decryption oracles and the 1CCA experiment (with and without an explicit challenge-pair
  admissibility guard).
* `Cslib.Crypto.Encryption.INDCCA2On`, `Cslib.Crypto.Encryption.INDCCA2Of`,
  `Cslib.Crypto.Encryption.INDCCA2`, `Cslib.Crypto.Encryption.WordINDCCA2`: single-challenge 1CCA
  security (Definition 12.2).
* `Cslib.Crypto.Encryption.CCA2AdversaryOf.restrict`: embedding of an adversary for the
  admissibility-restricted `cca2GameOn valid` inside the unrestricted `cca2Game`.
* `Cslib.Crypto.Encryption.CCA2AdversaryOf.ofCPA`,
  `Cslib.Crypto.Encryption.CCA2Adversary.ofCPA`: embedding of a chosen-plaintext `AdversaryOf Msg`
  as a 0-query `CCA2AdversaryOf Msg`.

## Main results

* `Cslib.Crypto.Encryption.CCA2AdversaryOf.IsPPT.query_bounds`: polynomial query and saved-state
  length bounds for every strict oracle PPT `CCA2AdversaryOf Msg`.
* `Cslib.Crypto.Encryption.isPPTOn_run_cca2Phase1Oracle`,
  `Cslib.Crypto.Encryption.isPPTOn_run_cca2Phase2Oracle`,
  `Cslib.Crypto.Encryption.isPPTOn_cca2GameOn`,
  `Cslib.Crypto.Encryption.isPPTOn_cca2Game`: closed strict PPT compilation of Phase 1, Phase 2,
  and the complete 1CCA experiment via `IsOraclePPTOn.run_interpret_preprocess`.
* `Cslib.Crypto.Encryption.eval_cca2Game_restrict`,
  `Cslib.Crypto.Encryption.CCA2AdversaryOf.IsPPT.restrict`,
  `Cslib.Crypto.Encryption.INDCCA2Of.indcca2On`,
  `Cslib.Crypto.Encryption.INDCCA2Of.wordINDCCA2`: unrestricted 1CCA security (`INDCCA2Of`) implies
  admissibility-restricted 1CCA security (`INDCCA2On`, including `WordINDCCA2`).
* `Cslib.Crypto.Encryption.CCA2AdversaryOf.isPPT_ofCPA`,
  `Cslib.Crypto.Encryption.CCA2AdversaryOf.isQueryBounded_ofCPA`,
  `Cslib.Crypto.Encryption.eval_cca2GameOn_ofCPA`,
  `Cslib.Crypto.Encryption.eval_cca2Game_ofCPA`,
  `Cslib.Crypto.Encryption.INDCCA2On.indcpaOn`,
  `Cslib.Crypto.Encryption.INDCCA2Of.indcpaOf`,
  `Cslib.Crypto.Encryption.INDCCA2Of.indcpa`,
  `Cslib.Crypto.Encryption.INDCCA2.indcpa`,
  `Cslib.Crypto.Encryption.WordINDCCA2.wordINDCPA`: 1CCA security implies IND-CPA security under
  any challenge-pair admissibility predicate.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 12.1 (Attack Game 12.1, Definitions 12.1–12.2,
  printed pp. 467–469).
-/

@[expose] public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- A single-challenge adaptive chosen-ciphertext (1CCA, [BonehShoup2023], Section 12.1,
Attack Game 12.1 and Definition 12.2, printed pp. 467–469) adversary over message space `Msg`.
Both stages have access to the single-channel decryption oracle (`Operation = Unit`). -/
structure CCA2AdversaryOf (Msg : Type) where
  /-- Phase 1: given the unary security parameter `n` and encoded public key `pk`, make decryption
  queries, choose two challenge messages `(m₀, m₁) : Msg × Msg`, and save a state word. -/
  choose : ℕ → List Bool → WordOracleComp Unit ((Msg × Msg) × List Bool)
  /-- Phase 2: given `n`, the saved state word, and the challenge ciphertext `ct`, make decryption
  queries (where querying `ct` is rejected) and output a guess bit. -/
  guess : ℕ → List Bool → List Bool → WordOracleComp Unit Bool

/-- Uniform strict oracle PPT admissibility of both stages of a `CCA2AdversaryOf Msg` with respect
to message encoding `encMsg`. -/
structure CCA2AdversaryOf.IsPPT {Msg : Type} (encMsg : Msg ↪ List Bool)
    (adversary : CCA2AdversaryOf Msg) : Prop where
  /-- Phase 1 message selection is uniform strict oracle PPT on `(n, pk)`. -/
  choose : IsOraclePPT (Operation := Unit) (encPair (encPair encMsg encMsg) encBits)
    adversary.choose
  /-- Phase 2 guessing is uniform strict oracle PPT on `(n, state, ct)`. -/
  guess : IsOraclePPTOn (Operation := Unit) (encPair encUnary (encPair encBits encBits)) encBool
    (fun p => adversary.guess p.1 p.2.1 p.2.2)

/-- Per-stage decryption-query bound `(Q₁ n, Q₂ n)` for a `CCA2AdversaryOf Msg`. -/
def CCA2AdversaryOf.IsQueryBounded {Msg : Type} (adversary : CCA2AdversaryOf Msg)
    (Q₁ Q₂ : ℕ → ℕ) : Prop :=
  (∀ n pk, (adversary.choose n pk).IsQueryBounded (Q₁ n)) ∧
  (∀ n state ct, (adversary.guess n state ct).IsQueryBounded (Q₂ n))

/-- Every strict oracle PPT `CCA2AdversaryOf Msg` has polynomial bounds on its Phase 1 queries,
Phase 2 queries, and saved-state length in terms of `(n, pk.length, ct.length)`. -/
theorem CCA2AdversaryOf.IsPPT.query_bounds {Msg : Type} {encMsg : Msg ↪ List Bool}
    {adversary : CCA2AdversaryOf Msg} (hA : adversary.IsPPT encMsg) :
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
    have hstate : choice.2.length ≤ (encPair (encPair encMsg encMsg) encBits choice).length := by
      simp only [length_encPair, encBits_apply]
      lia
    have hsize : (encPair encUnary encBits (n, pk)).length + 1 ≤
        2 * (n + pk.length + 2) := by
      simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
      lia
    have hpoly := Nat.mul_le_mul_left cs (Nat.pow_le_pow_left hsize ds)
    rw [Nat.mul_pow, ← Nat.mul_assoc] at hpoly
    exact (hstate.trans hbound).trans hpoly

/-- Single-bit 1CCA adversary (`Msg = Bool`). -/
abbrev CCA2Adversary : Type := CCA2AdversaryOf Bool

/-- Native uniform strict oracle PPT admissibility for a bit 1CCA adversary. -/
abbrev CCA2Adversary.IsPPT (adversary : CCA2Adversary) : Prop :=
  CCA2AdversaryOf.IsPPT encBool adversary

/-- Bit-string 1CCA adversary (`Msg = List Bool`). -/
abbrev WordCCA2Adversary : Type := CCA2AdversaryOf (List Bool)

/-- Native uniform strict oracle PPT admissibility for a bit-string 1CCA adversary. -/
abbrev WordCCA2Adversary.IsPPT (adversary : WordCCA2Adversary) : Prop :=
  CCA2AdversaryOf.IsPPT encBits adversary

/-- Phase 1 decryption oracle ([BonehShoup2023], Section 12.1, Attack Game 12.1 and Definition 12.2,
printed pp. 467–468): answer every decryption query `request.2` with
`encOption encOut (decrypt n sk request.2)`. -/
def cca2Phase1Oracle {Out : Type} (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (sk : List Bool) (request : Unit × List Bool) :
    StateT Unit ProbComp (List Bool) :=
  fun s => pure (encOption encOut (decrypt n sk request.2), s)

/-- Phase 2 decryption oracle ([BonehShoup2023], Section 12.1, Attack Game 12.1 and Definition 12.2,
printed pp. 467–468): reject the challenge ciphertext (`request.2 == ct`) with `[]`
(`encOption encOut none`), and answer all other queries `request.2 ≠ ct` with
`encOption encOut (decrypt n sk request.2)`. Since the adversary receives `ct` as input to `guess`
and can simulate the constant `[]` reply on `ct` itself, returning `[]` on `ct` is equivalent to
forbidding the query `ĉ = c` (matching `SymmetricCipher.ccaOracle` in
`Complexity/Crypto/Computational/Encryption/Authenticated.lean`). -/
def cca2Phase2Oracle {Out : Type} (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (n : ℕ) (sk ct : List Bool) (request : Unit × List Bool) :
    StateT Unit ProbComp (List Bool) :=
  fun s =>
    if request.2 == ct then
      pure ([], s)
    else
      pure (encOption encOut (decrypt n sk request.2), s)

/-- Single-challenge 1CCA experiment ([BonehShoup2023], Section 12.1, Attack Game 12.1 and
Definition 12.2, printed pp. 467–468) with challenge-pair admissibility predicate
`valid : ℕ → List Bool → Msg → Msg → Bool`: sample `(pk, sk) ← keyGen n`, run Phase 1 (`choose`)
against `cca2Phase1Oracle`, check `valid n pk m₀ m₁` (returning `false` in both experiments when
invalid), encrypt `if bit then m₁ else m₀` to obtain `ct`, and run Phase 2 (`guess`) against
`cca2Phase2Oracle` rejecting `ct`. -/
noncomputable def cca2GameOn {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : CCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choiceOut ← (OracleComp.interpret
    (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2Phase1Oracle encOut decrypt n keys.2))
    (adversary.choose n keys.1)).run ()
  let choice := choiceOut.1
  if valid n keys.1 choice.1.1 choice.1.2 then
    let ct ← encrypt n keys.1 (if bit then choice.1.2 else choice.1.1)
    let guessOut ← (OracleComp.interpret
      (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase2Oracle encOut decrypt n keys.2 ct))
      (adversary.guess n choice.2 ct)).run ()
    return guessOut.1
  else
    return false

/-- Unconditional single-challenge 1CCA experiment (`valid := fun _ _ _ _ => true`), for
fixed-length message spaces `Msg` where every pair `(m₀, m₁) : Msg × Msg` is admissible. -/
noncomputable abbrev cca2Game {Msg Out : Type} (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : CCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) : ProbComp Bool :=
  cca2GameOn (fun _ _ _ _ => true) encOut keyGen encrypt decrypt adversary bit n

/-- Single-challenge 1CCA security ([BonehShoup2023], Section 12.1, Definition 12.2, printed p. 468)
with respect to challenge-pair admissibility predicate `valid`, message encoding `encMsg`, and
decryption output encoding `encOut`. -/
def INDCCA2On {Msg Out : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encMsg : Msg ↪ List Bool) (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out) : Prop :=
  Game.Indistinguishable
    (fun adversary n =>
      ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary false n))
    (fun adversary n =>
      ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary true n))
    (CCA2AdversaryOf.IsPPT encMsg)

/-- Single-challenge 1CCA security ([BonehShoup2023], Section 12.1, Definition 12.2, printed p. 468)
over a fixed-length message space `Msg` (`valid := fun _ _ _ _ => true`). -/
abbrev INDCCA2Of {Msg Out : Type} (encMsg : Msg ↪ List Bool) (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out) : Prop :=
  INDCCA2On (fun _ _ _ _ => true) encMsg encOut keyGen encrypt decrypt

/-- Single-challenge 1CCA security for bit encryption (`Msg = Bool`, `Out = Bool`). -/
abbrev INDCCA2 (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Bool) : Prop :=
  INDCCA2Of encBool encBool keyGen encrypt decrypt

/-- Single-challenge 1CCA security for bit-string encryption (`Msg = List Bool`, `Out = List Bool`)
under Attack Game 12.1's equal-length challenge rule `m₀.length == m₁.length`. -/
abbrev WordINDCCA2 (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option (List Bool)) : Prop :=
  INDCCA2On (fun _ _ m₀ m₁ => m₀.length == m₁.length) encBits encBits keyGen encrypt decrypt

/-- Running Phase 1 (`adversary.choose`) against `cca2Phase1Oracle` is uniformly strict PPT in
`(n, pk, sk)` whenever `decrypt` is computable in polynomial time. -/
@[program_certificate]
theorem isPPTOn_run_cca2Phase1Oracle {Msg Out : Type} {encMsg : Msg ↪ List Bool}
    {encOut : Out ↪ List Bool} {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : CCA2AdversaryOf Msg}
    (hdec : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) (encOption encOut))
    (hA : adversary.IsPPT encMsg) :
    IsPPTOn (encPair encUnary (encPair encBits encBits))
      (encPair (encPair (encPair encMsg encMsg) encBits) (encFinEnum Unit))
      (fun caller : ℕ × List Bool × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2Phase1Oracle encOut decrypt caller.1 caller.2.2))
          (adversary.choose caller.1 caller.2.1)).run ()) := by
  let ECaller := encPair encUnary (encPair encBits encBits)
  let EIn := encPair ECaller (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hdecArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × ((Unit × List Bool) × Unit) =>
        (p.1.1, p.1.2.2, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by fun_prop
  have hdecWord : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool × List Bool) × ((Unit × List Bool) × Unit) =>
        encOption encOut (decrypt p.1.1 p.1.2.2 p.2.1.2))
      EIn encBits :=
    (ComputableTidilyInPolyTime.encode (encOption encOut)).comp (hdec.tidy.comp hdecArg)
  have hhandler : IsPPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool × List Bool) × ((Unit × List Bool) × Unit) =>
        cca2Phase1Oracle encOut decrypt pair.1.1 pair.1.2.2 pair.2.1 pair.2.2) :=
    (ComputableTidilyInPolyTime.prod hdecWord (by fun_prop)).isPPTOn
  have hres : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool × List Bool) × List Bool =>
        (encOption encOut (decrypt pair.1.1 pair.1.2.2 pair.2)).length)
      (encPair ECaller encBits) encUnary := by
    have harg : ComputableTidilyInPolyTime
        (fun pair : (ℕ × List Bool × List Bool) × List Bool =>
          (pair.1.1, pair.1.2.2, pair.2))
        (encPair ECaller encBits) (encPair encUnary (encPair encBits encBits)) := by fun_prop
    exact ComputableTidilyInPolyTime.length_bits.comp
      ((ComputableTidilyInPolyTime.encode (encOption encOut)).comp (hdec.tidy.comp harg))
  exact hA.choose.on.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool × List Bool => (caller.1, caller.2.1))
    (initial := fun _ => ())
    (resources := fun caller req => (encOption encOut (decrypt caller.1 caller.2.2 req)).length)
    (by fun_prop)
    hhandler
    (ComputableTidilyInPolyTime.const ())
    (fun _ _ => True)
    (fun _ => trivial)
    hres
    (fun caller request state _ result hresult => by
      have hresEq : result = (encOption encOut (decrypt caller.1 caller.2.2 request.2), state) := by
        simpa [cca2Phase1Oracle] using hresult
      subst hresEq
      exact ⟨trivial, le_rfl, Nat.le_add_right _ _⟩)

/-- Running Phase 2 (`adversary.guess`) against `cca2Phase2Oracle` is uniformly strict PPT in
`(n, sk, state, ct)` whenever `decrypt` is computable in polynomial time. -/
@[program_certificate]
theorem isPPTOn_run_cca2Phase2Oracle {Msg Out : Type} {encMsg : Msg ↪ List Bool}
    {encOut : Out ↪ List Bool} {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : CCA2AdversaryOf Msg}
    (hdec : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) (encOption encOut))
    (hA : adversary.IsPPT encMsg) :
    IsPPTOn (encPair encUnary (encPair encBits (encPair encBits encBits)))
      (encPair encBool (encFinEnum Unit))
      (fun caller : ℕ × List Bool × List Bool × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2Phase2Oracle encOut decrypt caller.1 caller.2.1 caller.2.2.2))
          (adversary.guess caller.1 caller.2.2.1 caller.2.2.2)).run ()) := by
  let ECaller := encPair encUnary (encPair encBits (encPair encBits encBits))
  let EIn := encPair ECaller (encPair (encPair (encFinEnum Unit) encBits) (encFinEnum Unit))
  have hdecArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool × List Bool × List Bool) × ((Unit × List Bool) × Unit) =>
        (p.1.1, p.1.2.1, p.2.1.2))
      EIn (encPair encUnary (encPair encBits encBits)) := by fun_prop
  have hdecWord : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool × List Bool × List Bool) × ((Unit × List Bool) × Unit) =>
        encOption encOut (decrypt p.1.1 p.1.2.1 p.2.1.2))
      EIn encBits :=
    (ComputableTidilyInPolyTime.encode (encOption encOut)).comp (hdec.tidy.comp hdecArg)
  have heqCt : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool × List Bool × List Bool) × ((Unit × List Bool) × Unit) =>
        p.2.1.2 == p.1.2.2.2)
      EIn encBool := by polytime
  have hnoReply : IsPPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun p : (ℕ × List Bool × List Bool × List Bool) × ((Unit × List Bool) × Unit) =>
        pure ([], p.2.2)) :=
    (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const [])
      (by fun_prop)).isPPTOn
  have hhandler : IsPPTOn EIn (encPair encBits (encFinEnum Unit))
      (fun pair : (ℕ × List Bool × List Bool × List Bool) × ((Unit × List Bool) × Unit) =>
        cca2Phase2Oracle encOut decrypt pair.1.1 pair.1.2.1 pair.1.2.2.2 pair.2.1 pair.2.2) :=
    IsPPTOn.cond heqCt hnoReply
      ((ComputableTidilyInPolyTime.prod hdecWord (by fun_prop)).isPPTOn)
  have hres : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool × List Bool × List Bool) × List Bool =>
        (encOption encOut (decrypt pair.1.1 pair.1.2.1 pair.2)).length)
      (encPair ECaller encBits) encUnary := by
    have harg : ComputableTidilyInPolyTime
        (fun pair : (ℕ × List Bool × List Bool × List Bool) × List Bool =>
          (pair.1.1, pair.1.2.1, pair.2))
        (encPair ECaller encBits) (encPair encUnary (encPair encBits encBits)) := by fun_prop
    exact ComputableTidilyInPolyTime.length_bits.comp
      ((ComputableTidilyInPolyTime.encode (encOption encOut)).comp (hdec.tidy.comp harg))
  exact hA.guess.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool × List Bool × List Bool =>
      (caller.1, caller.2.2.1, caller.2.2.2))
    (initial := fun _ => ())
    (resources := fun caller req => (encOption encOut (decrypt caller.1 caller.2.1 req)).length)
    (by fun_prop)
    hhandler
    (ComputableTidilyInPolyTime.const ())
    (fun _ _ => True)
    (fun _ => trivial)
    hres
    (fun caller request state _ result hresult => by
      dsimp only [cca2Phase2Oracle] at hresult
      split_ifs at hresult with hct
      · have hresEq : result = ([], state) := by simpa using hresult
        subst hresEq
        exact ⟨trivial, Nat.zero_le _, Nat.le_add_right _ _⟩
      · have hresEq :
            result = (encOption encOut (decrypt caller.1 caller.2.1 request.2), state) := by
          simpa using hresult
        subst hresEq
        exact ⟨trivial, le_rfl, Nat.le_add_right _ _⟩)

/-- The complete `cca2GameOn` experiment is uniformly strict PPT on the unary security parameter
whenever `valid`, `keyGen`, `encrypt`, `decrypt`, and `adversary` are admissible. -/
@[program_certificate]
theorem isPPTOn_cca2GameOn {Msg Out : Type} {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : CCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) (encOption encOut))
    (hA : adversary.IsPPT encMsg) (bit : Bool) :
    IsPPTOn encUnary encBool (cca2GameOn valid encOut keyGen encrypt decrypt adversary bit) := by
  let E1 := encPair encUnary (encPair encBits encBits)
  let EChoice := encPair (encPair (encPair encMsg encMsg) encBits) (encFinEnum Unit)
  let E2 := encPair E1 EChoice
  let E3 := encPair E2 encBits
  have hphase1 : IsPPTOn E1 EChoice
      (fun p : ℕ × (List Bool × List Bool) =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2Phase1Oracle encOut decrypt p.1 p.2.2))
          (adversary.choose p.1 p.2.1)).run ()) :=
    isPPTOn_run_cca2Phase1Oracle hdecrypt hA
  have hm0 : ComputableTidilyInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × (((Msg × Msg) × List Bool) × Unit) => p.2.1.1.1)
      E2 encMsg :=
    (ComputableTidilyInPolyTime.fst _ _).comp
      ((ComputableTidilyInPolyTime.fst _ _).comp
        ((ComputableTidilyInPolyTime.fst _ _).comp (ComputableTidilyInPolyTime.snd _ _)))
  have hm1 : ComputableTidilyInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × (((Msg × Msg) × List Bool) × Unit) => p.2.1.1.2)
      E2 encMsg :=
    (ComputableTidilyInPolyTime.snd _ _).comp
      ((ComputableTidilyInPolyTime.fst _ _).comp
        ((ComputableTidilyInPolyTime.fst _ _).comp (ComputableTidilyInPolyTime.snd _ _)))
  have hvalidArg : ComputableTidilyInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × (((Msg × Msg) × List Bool) × Unit) =>
        (p.1.1, p.1.2.1, p.2.1.1.1, p.2.1.1.2))
      E2 (encPair encUnary (encPair encBits (encPair encMsg encMsg))) :=
    ComputableTidilyInPolyTime.prod (by fun_prop)
      (ComputableTidilyInPolyTime.prod (by fun_prop)
        (ComputableTidilyInPolyTime.prod hm0 hm1))
  have hvalidStep : ComputableTidilyInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × (((Msg × Msg) × List Bool) × Unit) =>
        valid p.1.1 p.1.2.1 p.2.1.1.1 p.2.1.1.2)
      E2 encBool :=
    hvalid.tidy.comp hvalidArg
  have hmsg : ComputableTidilyInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × (((Msg × Msg) × List Bool) × Unit) =>
        if bit then p.2.1.1.2 else p.2.1.1.1)
      E2 encMsg := by
    cases bit
    · exact hm0
    · exact hm1
  have hencArg : ComputableInPolyTime
      (fun p : (ℕ × (List Bool × List Bool)) × (((Msg × Msg) × List Bool) × Unit) =>
        (p.1.1, p.1.2.1, if bit then p.2.1.1.2 else p.2.1.1.1))
      E2 (encPair encUnary (encPair encBits encMsg)) :=
    (ComputableTidilyInPolyTime.prod (by fun_prop)
      (ComputableTidilyInPolyTime.prod (by fun_prop) hmsg)).computableInPolyTime
  have hencStep : IsPPTOn E2 encBits
      (fun p => encrypt p.1.1 p.1.2.1 (if bit then p.2.1.1.2 else p.2.1.1.1)) :=
    hencrypt.preprocess hencArg
  have hphase2Arg : ComputableInPolyTime
      (fun p : ((ℕ × (List Bool × List Bool)) × (((Msg × Msg) × List Bool) × Unit)) × List Bool =>
        (p.1.1.1, p.1.1.2.2, p.1.2.1.2, p.2))
      E3 (encPair encUnary (encPair encBits (encPair encBits encBits))) := by fun_prop
  have hphase2 : IsPPTOn E3 (encPair encBool (encFinEnum Unit))
      (fun p : ((ℕ × (List Bool × List Bool)) × (((Msg × Msg) × List Bool) × Unit)) × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2Phase2Oracle encOut decrypt p.1.1.1 p.1.1.2.2 p.2))
          (adversary.guess p.1.1.1 p.1.2.1.2 p.2)).run ()) :=
    (isPPTOn_run_cca2Phase2Oracle hdecrypt hA).preprocess hphase2Arg
  have hphase2Bool : IsPPTOn E3 encBool
      (fun p :
        ((ℕ × (List Bool × List Bool)) × (((Msg × Msg) × List Bool) × Unit)) × List Bool => do
        let guessOut ← (OracleComp.interpret
          (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
            (cca2Phase2Oracle encOut decrypt p.1.1.1 p.1.1.2.2 p.2))
          (adversary.guess p.1.1.1 p.1.2.1.2 p.2)).run ()
        return guessOut.1) :=
    hphase2.bind (ComputableTidilyInPolyTime.fst _ _).isPPTOn
  have hbranch : IsPPTOn E2 encBool
      (fun p : (ℕ × (List Bool × List Bool)) × (((Msg × Msg) × List Bool) × Unit) =>
        if valid p.1.1 p.1.2.1 p.2.1.1.1 p.2.1.1.2 then do
          let ct ← encrypt p.1.1 p.1.2.1 (if bit then p.2.1.1.2 else p.2.1.1.1)
          let guessOut ← (OracleComp.interpret
            (ProbOracleComp.handler (fun m => StateT.lift (ProbComp.unifFin m))
              (cca2Phase2Oracle encOut decrypt p.1.1 p.1.2.2 ct))
            (adversary.guess p.1.1 p.2.1.2 ct)).run ()
          return guessOut.1
        else
          return false) :=
    IsPPTOn.cond hvalidStep (hencStep.bind_with hphase2Bool)
      (ComputableTidilyInPolyTime.const false).isPPTOn
  exact hkeyGen.bind_with (hphase1.bind_with hbranch)

/-- The complete `cca2Game` experiment is uniformly strict PPT on the unary security parameter
whenever `keyGen`, `encrypt`, `decrypt`, and `adversary` are admissible. -/
@[program_certificate]
theorem isPPTOn_cca2Game {Msg Out : Type} {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {adversary : CCA2AdversaryOf Msg}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encPair encUnary (encPair encBits encMsg)) encBits
      (fun p => encrypt p.1 p.2.1 p.2.2))
    (hdecrypt : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => decrypt p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) (encOption encOut))
    (hA : adversary.IsPPT encMsg) (bit : Bool) :
    IsPPTOn encUnary encBool (cca2Game encOut keyGen encrypt decrypt adversary bit) :=
  isPPTOn_cca2GameOn (ComputableTidilyInPolyTime.const true).computableInPolyTime
    hkeyGen hencrypt hdecrypt hA bit

/-! ### Playing a restricted 1CCA game inside the unrestricted one -/

/-- The adversary that plays `cca2GameOn valid` inside the unrestricted `cca2Game`. Its `choose`
runs `adversary.choose n pk` and puts the bit `valid n pk m₀ m₁` in front of the saved state; its
`guess` returns `false` when that bit is `false` and otherwise runs `adversary.guess` on the rest of
the state. The challenge pair itself is passed on unchanged. -/
def CCA2AdversaryOf.restrict {Msg : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (adversary : CCA2AdversaryOf Msg) : CCA2AdversaryOf Msg where
  choose n pk := do
    let choice ← adversary.choose n pk
    return (choice.1, valid n pk choice.1.1 choice.1.2 :: choice.2)
  guess n state ct :=
    if state.headD false then adversary.guess n state.tail ct else pure false

/-- Running the unrestricted `cca2Game` on `adversary.restrict valid` has the same output
distribution as running `cca2GameOn valid` on `adversary`. -/
theorem eval_cca2Game_restrict {Msg Out : Type} (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : CCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval (cca2Game encOut keyGen encrypt decrypt (adversary.restrict valid) bit n) =
      ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt adversary bit n) := by
  simp only [cca2Game, cca2GameOn, CCA2AdversaryOf.restrict, ↓reduceIte,
    OracleComp.interpret_bind, OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, apply_ite ProbComp.eval]
  congr 1; funext keys
  congr 1; funext choiceOut
  cases valid n keys.1 choiceOut.1.1.1 choiceOut.1.1.2 <;>
    simp [OracleComp.interpret_pure, StateT.run_pure, ProbComp.eval_pure, PMF.bind_const]

/-- Restricting a uniform strict oracle PPT 1CCA adversary by a polynomial-time admissibility
predicate keeps it uniform strict oracle PPT: `choose` additionally evaluates `valid` and prepends
one bit to the saved state, and `guess` branches on that bit without querying the oracle when it is
`false`. -/
theorem CCA2AdversaryOf.IsPPT.restrict {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool)
    {adversary : CCA2AdversaryOf Msg} (hadversary : CCA2AdversaryOf.IsPPT encMsg adversary) :
    CCA2AdversaryOf.IsPPT encMsg (adversary.restrict valid) where
  choose := by
    let EIn := encPair (encPair encUnary encBits) (encPair (encPair encMsg encMsg) encBits)
    have hm0 : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Msg × Msg) × List Bool) => p.2.1.1) EIn encMsg :=
      (ComputableTidilyInPolyTime.fst _ _).comp
        ((ComputableTidilyInPolyTime.fst _ _).comp (ComputableTidilyInPolyTime.snd _ _))
    have hm1 : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Msg × Msg) × List Bool) => p.2.1.2) EIn encMsg :=
      (ComputableTidilyInPolyTime.snd _ _).comp
        ((ComputableTidilyInPolyTime.fst _ _).comp (ComputableTidilyInPolyTime.snd _ _))
    have hvalidArg : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Msg × Msg) × List Bool) =>
          (p.1.1, p.1.2, p.2.1.1, p.2.1.2))
        EIn (encPair encUnary (encPair encBits (encPair encMsg encMsg))) :=
      ComputableTidilyInPolyTime.prod (by fun_prop)
        (ComputableTidilyInPolyTime.prod (by fun_prop)
          (ComputableTidilyInPolyTime.prod hm0 hm1))
    have hvalidBit : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Msg × Msg) × List Bool) =>
          valid p.1.1 p.1.2 p.2.1.1 p.2.1.2) EIn encBool :=
      hvalid.tidy.comp hvalidArg
    have hpost : ComputableTidilyInPolyTime
        (fun p : (ℕ × List Bool) × ((Msg × Msg) × List Bool) =>
          (p.2.1, valid p.1.1 p.1.2 p.2.1.1 p.2.1.2 :: p.2.2))
        EIn (encPair (encPair encMsg encMsg) encBits) := by
      have hpair : ComputableTidilyInPolyTime
          (fun p : (ℕ × List Bool) × ((Msg × Msg) × List Bool) => p.2.1)
          EIn (encPair encMsg encMsg) :=
        (ComputableTidilyInPolyTime.fst _ _).comp (ComputableTidilyInPolyTime.snd _ _)
      have hstate : ComputableTidilyInPolyTime
          (fun p : (ℕ × List Bool) × ((Msg × Msg) × List Bool) =>
            valid p.1.1 p.1.2 p.2.1.1 p.2.1.2 :: p.2.2)
          EIn encBits := by polytime
      exact ComputableTidilyInPolyTime.prod hpair hstate
    exact (hadversary.choose.on.bind_with hpost.isOraclePPTOn).isOraclePPT
  guess := by
    let EGuess := encPair encUnary (encPair encBits encBits)
    have hcond : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => p.2.1.headD false) EGuess encBool := by polytime
    have hprep : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => (p.1, p.2.1.tail, p.2.2)) EGuess EGuess := by
      polytime
    exact IsOraclePPTOn.cond' hcond (hadversary.guess.preprocess' hprep)
      (ComputableInPolyTime.const false).isOraclePPTOn

/-- Unrestricted 1CCA security implies 1CCA security under every polynomial-time admissibility
predicate. -/
theorem INDCCA2Of.indcca2On {Msg Out : Type} {encMsg : Msg ↪ List Bool}
    {encOut : Out ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2Of encMsg encOut keyGen encrypt decrypt)
    (hvalid : ComputableInPolyTime
      (fun p : ℕ × List Bool × Msg × Msg => valid p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encUnary (encPair encBits (encPair encMsg encMsg))) encBool) :
    INDCCA2On valid encMsg encOut keyGen encrypt decrypt := by
  intro adversary hadversary
  simpa only [eval_cca2Game_restrict] using
    h (adversary.restrict valid) (hadversary.restrict hvalid)

/-- Unrestricted bit-word 1CCA security implies `WordINDCCA2`. -/
theorem INDCCA2Of.wordINDCCA2
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (h : INDCCA2Of encBits encBits keyGen encrypt decrypt) :
    WordINDCCA2 keyGen encrypt decrypt :=
  h.indcca2On (ComputableInPolyTime.of_tidy (by polytime))

/-! ### 1CCA implies IND-CPA -/

/-- Lift a chosen-plaintext `AdversaryOf Msg` to a 0-query `CCA2AdversaryOf Msg`. -/
def CCA2AdversaryOf.ofCPA {Msg : Type} (adversary : AdversaryOf Msg) : CCA2AdversaryOf Msg where
  choose n pk := ProbOracleComp.sample (adversary.choose n pk)
  guess n state ct := ProbOracleComp.sample (adversary.guess n state ct)

/-- Lift a chosen-plaintext bit `Adversary` to a 0-query `CCA2Adversary`. -/
abbrev CCA2Adversary.ofCPA (adversary : Adversary) : CCA2Adversary :=
  CCA2AdversaryOf.ofCPA adversary

/-- Lifting a strict PPT `AdversaryOf Msg` yields a strict oracle PPT `CCA2AdversaryOf Msg`. -/
theorem CCA2AdversaryOf.isPPT_ofCPA {Msg : Type} {encMsg : Msg ↪ List Bool}
    {adversary : AdversaryOf Msg} (hA : adversary.IsPPT encMsg) :
    (CCA2AdversaryOf.ofCPA adversary).IsPPT encMsg where
  choose := hA.choose.on.isOraclePPTOn.isOraclePPT
  guess := hA.guess.isOraclePPTOn

/-- Lifting a strict PPT bit `Adversary` yields a strict oracle PPT `CCA2Adversary`. -/
theorem CCA2Adversary.isPPT_ofCPA {adversary : Adversary} (hA : adversary.IsPPT) :
    (CCA2Adversary.ofCPA adversary).IsPPT :=
  CCA2AdversaryOf.isPPT_ofCPA hA

/-- A lifted CPA adversary makes `0` decryption queries in both stages. -/
theorem CCA2AdversaryOf.isQueryBounded_ofCPA {Msg : Type} (adversary : AdversaryOf Msg) :
    (CCA2AdversaryOf.ofCPA adversary).IsQueryBounded (fun _ => 0) (fun _ => 0) :=
  ⟨fun n pk => ProbOracleComp.IsQueryBounded.sample (adversary.choose n pk),
    fun n state ct => ProbOracleComp.IsQueryBounded.sample (adversary.guess n state ct)⟩

/-- A lifted bit CPA adversary makes `0` decryption queries in both stages. -/
theorem CCA2Adversary.isQueryBounded_ofCPA (adversary : Adversary) :
    (CCA2Adversary.ofCPA adversary).IsQueryBounded (fun _ => 0) (fun _ => 0) :=
  CCA2AdversaryOf.isQueryBounded_ofCPA adversary

/-- Running a lifted CPA adversary in `cca2GameOn` has the same output distribution as the CPA
`gameOn` with the same challenge-pair admissibility predicate `valid`. -/
theorem eval_cca2GameOn_ofCPA {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (cca2GameOn valid encOut keyGen encrypt decrypt (CCA2AdversaryOf.ofCPA adversary) bit n) =
      ProbComp.eval (gameOn valid keyGen encrypt adversary bit n) := by
  simp only [cca2GameOn, gameOn, CCA2AdversaryOf.ofCPA, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbOracleComp.eval_run_interpret, ProbOracleComp.run_interpret_sample, PMF.bind_map,
    PMF.bind_pure, Function.comp_def, apply_ite ProbComp.eval]

/-- Running a lifted CPA adversary in `cca2Game` has the same output distribution as the CPA
`game`. -/
theorem eval_cca2Game_ofCPA {Msg Out : Type} (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (cca2Game encOut keyGen encrypt decrypt (CCA2AdversaryOf.ofCPA adversary) bit n) =
      ProbComp.eval (game keyGen encrypt adversary bit n) :=
  eval_cca2GameOn_ofCPA (fun _ _ _ _ => true) encOut keyGen encrypt decrypt adversary bit n

/-- **1CCA security implies IND-CPA security** under any challenge-pair admissibility predicate
`valid`: any encryption scheme satisfying `INDCCA2On valid` also satisfies `INDCPAOn valid`. -/
theorem INDCCA2On.indcpaOn {Msg Out : Type} {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2On valid encMsg encOut keyGen encrypt decrypt) :
    INDCPAOn valid encMsg keyGen encrypt := by
  intro adversary hA
  simpa only [eval_cca2GameOn_ofCPA] using h (CCA2AdversaryOf.ofCPA adversary)
    (CCA2AdversaryOf.isPPT_ofCPA hA)

/-- **Unrestricted 1CCA security implies unrestricted IND-CPA security**: any encryption scheme
satisfying `INDCCA2Of encMsg encOut` also satisfies `INDCPAOf encMsg`. -/
theorem INDCCA2Of.indcpaOf {Msg Out : Type} {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2Of encMsg encOut keyGen encrypt decrypt) :
    INDCPAOf encMsg keyGen encrypt :=
  INDCCA2On.indcpaOn h

/-- **1CCA security implies IND-CPA security**: any bit encryption scheme satisfying `INDCCA2Of`
also satisfies `INDCPA`. -/
theorem INDCCA2Of.indcpa {Out : Type} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (h : INDCCA2Of encBool encOut keyGen encrypt decrypt) :
    INDCPA keyGen encrypt :=
  INDCCA2On.indcpaOn h

/-- Specialization of `INDCCA2Of.indcpa` to `INDCCA2`. -/
theorem INDCCA2.indcpa {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Bool}
    (h : INDCCA2 keyGen encrypt decrypt) :
    INDCPA keyGen encrypt :=
  INDCCA2On.indcpaOn h

/-- **Word 1CCA security implies word IND-CPA security**: any bit-string encryption scheme
satisfying `WordINDCCA2` also satisfies `WordINDCPA`. -/
theorem WordINDCCA2.wordINDCPA {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (h : WordINDCCA2 keyGen encrypt decrypt) :
    WordINDCPA keyGen encrypt :=
  INDCCA2On.indcpaOn h

end Cslib.Crypto.Encryption
