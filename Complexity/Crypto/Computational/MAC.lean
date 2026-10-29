/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GeneratorReindex
public import Complexity.Crypto.Computational.PseudorandomFunction
public import Complexity.Crypto.Computational.Signature
import Complexity.Probability.PMF.Bind
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Computability.Probabilistic.Oracle.Tidy
import Complexity.Crypto.Negligible.Basic
import Complexity.Languages.Probabilistic.Oracle.Simulation
import Complexity.Probability.PMF
import Complexity.Tactic.PolyTime
import Complexity.Tactic.PPT
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Uniform message authentication codes and PRF-based MACs

A uniform symmetric message authentication code (`MACScheme`) consists of a polynomial-time
message-length schedule `msgLen : ℕ → ℕ` (defaulting to `id`), a strict probabilistic
polynomial-time key generator `keyGen`, a strict probabilistic polynomial-time tag generator `sign`,
and a deterministic polynomial-time tag verifier `verify` that accepts every tag produced by `sign`
on a `msgLen n`-bit message under a secret key sampled at security parameter `n`. Unlike digital
signatures (`SignatureScheme`), verification uses the same secret key as tag generation, and the
adversary receives no public key.

We formalize both strong (fresh-pair) existential unforgeability under adaptive chosen-message
attack (`sufCmaGame`, `SUFCMA`) as in
[Boneh and Shoup, Attack Game 6.1 / Definition 6.2][BonehShoup2023],
and ordinary fresh-message existential unforgeability under adaptive chosen-message attack
(`eufCmaGame`, `EUFCMA`) and under one-time adaptive chosen-message attack (`eufOneTimeGame`,
`OneTimeEUFCMA`) against uniform strict oracle-PPT forgers (`IsOraclePPT`). Both adaptive games
share the pair-logging execution core `signingPairOracle`: `sufCmaGame` records returned
`(msg, tag)` pairs and accepts any valid `msgLen n`-bit forgery pair `(msg, tag)` that was never
returned (`!queriedPairs.contains (msg, tag)`), even on a previously queried message, whereas
`eufCmaGame` rejects any candidate forgery whose message was previously queried
(`!queried.contains msg`). We also provide schedule reindexing (`MACScheme.reindex`,
`MACScheme.reindexForger`, `SUFCMA.reindex`, `EUFCMA.reindex`, `OneTimeEUFCMA.reindex`), which
adapts any `MACScheme` along a strictly monotone polynomial-time parameter schedule `ℓ : ℕ → ℕ` so
that at security parameter `n` it authenticates `M.msgLen (ℓ n)`-bit messages.
We prove the quantitative bound
$$\Pr[\text{EUF-CMA}] \le \Pr[\text{SUF-CMA}]$$
(`succProbability_eufCmaGame_le_sufCmaGame`) and the security implication `SUFCMA → EUFCMA`
(`SUFCMA.eufCma`). For randomized `MACScheme.sign` algorithms the two notions differ; for MACs with
a unique valid tag per `(sk, msg)` (`eval_sufCmaGame_eq_eufCmaGame_of_unique_tag`,
`sufCma_iff_eufCma_of_unique_tag`), including `prfMAC`, fresh-message and fresh-pair
unforgeability coincide.

We then prove that any uniform `PseudorandomFunction` yields a `SUFCMA`- and `EUFCMA`-secure
deterministic MAC (`prfMAC`, `PseudorandomFunction.sufCma_prfMAC`,
`PseudorandomFunction.eufCma_prfMAC`), with the quantitative security reduction of
[Boneh and Shoup, Section 6.3, Theorem 6.2][BonehShoup2023]:
$$\Pr[\text{Forge}] \le \mathrm{Adv}_{\mathrm{PRF}}(B(\mathcal{A}), n) + 2^{-n}.$$

## Main definitions

* `Cslib.Crypto.MACScheme`: uniform symmetric message authentication code on `msgLen n`-bit
  messages (defaulting to `n`-bit messages).
* `Cslib.Crypto.MACScheme.signingPairOracle`, `sufCmaGame`, `SUFCMA`: pair-logging tagging oracle
  and strong (fresh-pair) adaptive SUF-CMA experiment and security predicate
  ([Boneh and Shoup, Attack Game 6.1 / Definition 6.2][BonehShoup2023]).
* `Cslib.Crypto.MACScheme.signingOracle`, `eufCmaGame`, `EUFCMA`: fresh-message adaptive EUF-CMA
  experiment and security predicate.
* `Cslib.Crypto.MACScheme.oneTimeSigningOracle`, `eufOneTimeGame`, `OneTimeEUFCMA`: one-time
  fresh-message adaptive EUF-CMA experiment and security predicate.
* `Cslib.Crypto.MACScheme.reindex`, `Cslib.Crypto.MACScheme.reindexForger`: schedule reindexing of
  a `MACScheme` and its adaptive forger reduction (via `GeneratorReindex.parameter`).
* `Cslib.Crypto.prfMAC`: canonical deterministic MAC constructed from a keyed function family
  ([Boneh and Shoup, Section 6.3][BonehShoup2023]).
* `Cslib.Crypto.macLogHandler`, `Cslib.Crypto.macToPrfDistinguisher`: oracle logging handler and
  reduction turning a MAC forger into a PRF distinguisher.
* `Cslib.Crypto.NonceMACForger`, `Cslib.Crypto.NonceMACScheme`: uniform nonce-based message
  authentication code (`sign : Key → Msg → Nonce → ProbComp Tag`) and adaptive forger
  ([Boneh and Shoup, Section 7.5, Attack Game 7.4][BonehShoup2023]).
* `Cslib.Crypto.NonceMACScheme.signingPairOracle`, `sufCmaGame`, `eufCmaGame`, `SUFCMA`,
  `EUFCMA`: nonce-respecting adaptive chosen-message security experiments and predicates requiring
  distinct queried nonces (`(tr.map (fun e => e.1.2)).Nodup`).

## Main results

* `Cslib.Crypto.MACScheme.isPPTOn_sufCmaGame`, `isPPT_sufCmaGame`, `isPPTOn_eufCmaGame`,
  `isPPT_eufCmaGame`: strict PPT certificates for the MAC SUF-CMA and EUF-CMA experiments.
* `Cslib.Crypto.MACScheme.eval_run_signingOracle_eq_map_fst_signingPairOracle`,
  `eval_eufCmaGame_eq_signingPairOracle`, `succProbability_eufCmaGame_le_sufCmaGame`,
  `SUFCMA.eufCma`, `SUFCMA.oneTimeEUFCMA`: shared pair-history representation and quantitative /
  asymptotic implication from strong to ordinary unforgeability.
* `Cslib.Crypto.MACScheme.eval_sufCmaGame_eq_eufCmaGame_of_unique_tag`,
  `sufCma_iff_eufCma_of_unique_tag`: equivalence of SUF-CMA and EUF-CMA for MACs with a unique
  valid tag per message.
* `Cslib.Crypto.MACScheme.isPPTOn_eufOneTimeGame`, `isPPT_eufOneTimeGame`: strict PPT certificates
  for the one-time MAC EUF-CMA experiment.
* `Cslib.Crypto.MACScheme.EUFCMA.oneTimeEUFCMA`: full EUF-CMA security implies one-time EUF-CMA
  security.
* `Cslib.Crypto.MACScheme.isOraclePPT_reindexForger`,
  `Cslib.Crypto.MACScheme.sufCmaGame_reindex`,
  `Cslib.Crypto.MACScheme.eufCmaGame_reindex`,
  `Cslib.Crypto.MACScheme.eufOneTimeGame_reindex`,
  `Cslib.Crypto.MACScheme.SUFCMA.reindex`,
  `Cslib.Crypto.MACScheme.EUFCMA.reindex`,
  `Cslib.Crypto.MACScheme.OneTimeEUFCMA.reindex`: schedule reindexing preserves `SUFCMA`, `EUFCMA`,
  and `OneTimeEUFCMA` along any strictly monotone polynomial-time schedule.
* `Cslib.Crypto.eval_sufCmaGame_prfMAC`, `Cslib.Crypto.sufCma_prfMAC_iff_eufCma`,
  `Cslib.Crypto.isOraclePPT_macToPrfDistinguisher`,
  `Cslib.Crypto.eval_prfRealGame_macToPrfDistinguisher`,
  `Cslib.Crypto.eval_prfRealGame_macToPrfDistinguisher_eq_sufCmaGame`,
  `Cslib.Crypto.succProbability_prfIdealGame_macToPrfDistinguisher_le`,
  `Cslib.Crypto.succProbability_eufCmaGame_prfMAC_le`,
  `Cslib.Crypto.succProbability_sufCmaGame_prfMAC_le`: quantitative PRF-to-MAC forgery reduction
  ([Boneh and Shoup, Theorem 6.2][BonehShoup2023]).
* `Cslib.Crypto.PseudorandomFunction.sufCma_prfMAC`,
  `Cslib.Crypto.PseudorandomFunction.eufCma_prfMAC`,
  `Cslib.Crypto.PseudorandomFunction.oneTimeEUFCMA_prfMAC`: any secure uniform
  `PseudorandomFunction` yields a `SUFCMA`-, `EUFCMA`-, and `OneTimeEUFCMA`-secure `MACScheme`.
* `Cslib.Crypto.NonceMACScheme.isPPTOn_run_signingPairOracle`,
  `Cslib.Crypto.NonceMACScheme.isPPTOn_sufCmaGame`, `isPPT_sufCmaGame`, `isPPTOn_eufCmaGame`,
  `isPPT_eufCmaGame`, `succProbability_eufCmaGame_le_sufCmaGame`, `SUFCMA.eufCma`,
  `eval_sufCmaGame_eq_freshPair_of_unique_tag`: strict PPT certificates, quantitative /
  asymptotic implication from `SUFCMA` to `EUFCMA`, and unique-tag pair-freshness characterization
  for nonce-based MACs.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 6,
  Sections 6.1–6.3 (Definitions 6.1–6.2 and Theorem 6.2) and Chapter 7, Section 7.5 (Attack Game
  7.4).
* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986].
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- A uniform symmetric message authentication code (MAC) on `msgLen n`-bit messages at security
parameter `n` (defaulting to `msgLen = id`, i.e., `n`-bit messages), with plain polynomial-time
message-length schedule, strict polynomial-time key generation and tag generation, deterministic
polynomial-time verification, and perfect completeness on supported keys, `msgLen n`-bit messages,
and tags [Boneh and Shoup, Definition 6.1][BonehShoup2023]. -/
structure MACScheme where
  /-- Message length authenticated at unary security parameter `n` (defaults to `n`). -/
  msgLen : ℕ → ℕ := fun n => n
  /-- The message-length schedule is computable in plain polynomial time in unary. -/
  msgLen_polyTime : ComputableInPolyTime msgLen encUnary encUnary := by
    exact ComputableInPolyTime.id'
  /-- Sample a secret MAC key `sk` at unary security parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool)
  /-- Compute a MAC tag on message `msg` using the secret key `sk`. -/
  sign : List Bool → List Bool → ProbComp (List Bool)
  /-- Deterministically verify a candidate `tag` on `msg` under secret key `sk`. -/
  verify : List Bool → List Bool → List Bool → Bool
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary encBits keyGen
  /-- Tag generation is uniformly strict PPT in the encoded secret key and message. -/
  sign_ppt : IsPPTOn (encPair encBits encBits) encBits (fun p => sign p.1 p.2)
  /-- Verification is computable in plain polynomial time on `(sk, msg, tag)`. -/
  verify_polyTime : ComputableInPolyTime
    (fun p : List Bool × List Bool × List Bool => verify p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encBits encBits)) encBool
  /-- Every tag produced by `sign` on a `msgLen n`-bit message under a supported secret key at
  security parameter `n` is accepted by `verify`. -/
  verify_sign : ∀ n sk, sk ∈ (ProbComp.eval (keyGen n)).support →
    ∀ msg, msg.length = msgLen n →
    ∀ tag, tag ∈ (ProbComp.eval (sign sk msg)).support →
    verify sk msg tag = true

/-- The equivalent tidy verification certificate used internally by compositional proofs. -/
private theorem MACScheme.verify_polyTime_tidy (M : MACScheme) :
    ComputableTidilyInPolyTime
      (fun p : List Bool × List Bool × List Bool => M.verify p.1 p.2.1 p.2.2)
      (encPair encBits (encPair encBits encBits)) encBool := by
  simpa only [← computableInPolyTime_iff_computableTidilyInPolyTime] using M.verify_polyTime

@[local fun_prop]
private theorem computableTidilyInPolyTime_contains {γ α : Type} [BEq α] [LawfulBEq α]
    {encIn : γ ↪ List Bool} {encElem : α ↪ List Bool}
    {list : γ → List α} {elem : γ → α}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encElem))
    (helem : ComputableTidilyInPolyTime elem encIn encElem) :
    ComputableTidilyInPolyTime (fun a => (list a).contains (elem a)) encIn encBool := by
  have heq : (fun a => (list a).contains (elem a)) =
      (fun a => (list a).any (fun x => elem a == x)) := by
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.any_eq_true]
    simp only [beq_iff_eq]
    exact ⟨fun h => ⟨elem a, h, rfl⟩, fun ⟨_, h, heq⟩ => heq ▸ h⟩
  rw [heq]
  exact ComputableTidilyInPolyTime.anyWithInput (test := fun a x => elem a == x) hlist
    (ComputableTidilyInPolyTime.beq (encB := encElem)
      (helem.comp (ComputableTidilyInPolyTime.fst _ _))
      (ComputableTidilyInPolyTime.snd _ _))

namespace MACScheme

attribute [program_certificate] msgLen_polyTime keyGen_ppt sign_ppt verify_polyTime

@[local fun_prop]
private theorem computableTidilyInPolyTime_msgLen_comp (M : MACScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ}
    (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    ComputableTidilyInPolyTime (fun a => M.msgLen (n a)) encIn encUnary :=
  M.msgLen_polyTime.tidy.comp hn

/-- Composing `M.msgLen` with a plain polynomial-time unary parameter function is plain
polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_msgLen_comp (M : MACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun a => M.msgLen (n a)) encIn encUnary :=
  M.msgLen_polyTime.comp hn

@[local fun_prop]
private theorem isPPTOn_keyGen_comp_tidy (M : MACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    IsPPTOn encIn encBits (fun a => M.keyGen (n a)) :=
  M.keyGen_ppt.preprocess (ComputableInPolyTime.of_tidy hn)

/-- Composing `M.keyGen` with a plain polynomial-time unary parameter function is strict PPT. -/
@[program_certificate]
theorem isPPTOn_keyGen_comp (M : MACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    IsPPTOn encIn encBits (fun a => M.keyGen (n a)) :=
  M.keyGen_ppt.preprocess hn

@[local fun_prop]
private theorem isPPTOn_sign_comp_tidy (M : MACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {sk msg : γ → List Bool}
    (hsk : ComputableTidilyInPolyTime sk encIn encBits)
    (hmsg : ComputableTidilyInPolyTime msg encIn encBits) :
    IsPPTOn encIn encBits (fun a => M.sign (sk a) (msg a)) :=
  M.sign_ppt.preprocess (ComputableInPolyTime.of_tidy (hsk.prod hmsg))

/-- Composing `M.sign` with plain polynomial-time key and message selectors is strict PPT. -/
@[program_certificate]
theorem isPPTOn_sign_comp (M : MACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {sk msg : γ → List Bool}
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits) :
    IsPPTOn encIn encBits (fun a => M.sign (sk a) (msg a)) :=
  M.sign_ppt.preprocess (hsk.prod hmsg)

@[local fun_prop]
private theorem computableTidilyInPolyTime_verify_comp (M : MACScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {sk msg tag : γ → List Bool}
    (hsk : ComputableTidilyInPolyTime sk encIn encBits)
    (hmsg : ComputableTidilyInPolyTime msg encIn encBits)
    (htag : ComputableTidilyInPolyTime tag encIn encBits) :
    ComputableTidilyInPolyTime (fun a => M.verify (sk a) (msg a) (tag a)) encIn encBool :=
  M.verify_polyTime.tidy.comp (hsk.prod (hmsg.prod htag))

/-- Composing `M.verify` with plain polynomial-time key, message, and tag selectors is plain
polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_verify_comp (M : MACScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {sk msg tag : γ → List Bool}
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits)
    (htag : ComputableInPolyTime tag encIn encBits) :
    ComputableInPolyTime (fun a => M.verify (sk a) (msg a) (tag a)) encIn encBool :=
  M.verify_polyTime.comp (hsk.prod (hmsg.prod htag))

/-! ### Full adaptive chosen-message security (`EUFCMA`) -/

/-- Stateful MAC tagging oracle that tags the requested message under `sk` and prepends the
message to the list of queried messages. -/
noncomputable def signingOracle (M : MACScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried => do
    let tag ← M.sign sk request.2
    return (tag, request.2 :: queried)

/-- The fresh-message MAC EUF-CMA experiment: sample `sk ← M.keyGen n`, run the adaptive forger on
`(n, [])` with oracle access to `M.signingOracle sk`, and accept when the forger outputs a valid
`(msg, tag)` pair on a `M.msgLen n`-bit message `msg` that was never queried to the tagging oracle.

Unlike [Boneh and Shoup, Attack Game 6.1 / Definition 6.2][BonehShoup2023], which logs `(msg, tag)`
pairs and rejects only previously returned pairs, this experiment logs queried messages and rejects
any previously queried message (`!out.2.contains out.1.1`). The two notions differ for randomized
`sign` algorithms, and coincide for deterministic canonical MACs such as `prfMAC`. -/
noncomputable def eufCmaGame (M : MACScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.signingOracle sk)) (adversary n [])).run []
  return (out.1.1.length == M.msgLen n) && !out.2.contains out.1.1 &&
    M.verify sk out.1.1 out.1.2

/-- Run the complete MAC EUF-CMA experiment on its unary security parameter for any oracle-PPT
forger. -/
@[program_certificate]
theorem isPPTOn_eufCmaGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (M.eufCmaGame adversary) := by
  obtain ⟨c, d, hlen⟩ := M.sign_ppt.length_le
  have hhandler : IsPPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encList encBits)))
      (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        M.signingOracle pair.1.2 pair.2.1 pair.2.2) := by
    unfold signingOracle
    ppt
  have hrun : IsPPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.signingOracle caller.2)) (adversary caller.1 [])).run []) := by
    apply hadversary.run_interpret_preprocess
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => ([] : List (List Bool)))
      (resources := fun caller query =>
        c * (2 * caller.2.length + query.length + 2) ^ d + 2 * query.length + 2)
      (by fun_prop) hhandler (by fun_prop)
      (fun _ _ => True) (fun _ => trivial) (by fun_prop)
    intro caller request queried _ result hresult
    simp only [signingOracle, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨tag, htag, rfl⟩ := hresult
    have htagLen := hlen (caller.2, request.2) tag htag
    simp only [encBits_apply, length_encPair] at htagLen
    refine ⟨trivial, by lia, ?_⟩
    simp only [encList_cons, List.length_append, length_frame, encBits_apply]
    lia
  have hpost : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool)) =>
        (pair.2.1.1.length == M.msgLen pair.1.1) && !pair.2.2.contains pair.2.1.1 &&
          M.verify pair.1.2 pair.2.1.1 pair.2.1.2)
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBits encBits) (encList encBits))) encBool := by
    polytime
  exact M.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-- The MAC EUF-CMA experiment is uniformly strict PPT, independently of unused auxiliary input. -/
@[program_certificate]
theorem isPPT_eufCmaGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => M.eufCmaGame adversary n) :=
  ((M.isPPTOn_eufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Fresh-message existential unforgeability under adaptive chosen-message attack (`EUFCMA`) for a
symmetric MAC against uniform strict oracle-PPT adversaries.

Note that `eufCmaGame` enforces fresh-message unforgeability (`msg ∉ queried`), whereas
[Boneh and Shoup, Attack Game 6.1 / Definition 6.2][BonehShoup2023] defines the stronger fresh-pair
variant (`(msg, tag) ∉ queriedPairs`) for general (possibly randomized) signing algorithms. -/
def EUFCMA (M : MACScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.eufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Full EUF-CMA security gives negligible forgery probability for every oracle-PPT forger. -/
theorem EUFCMA.negligible {M : MACScheme} (h : M.EUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish EUF-CMA security by bounding every oracle-PPT forger's success probability. -/
theorem EUFCMA.of_negligible {M : MACScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)))) :
    M.EUFCMA := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-! ### One-time adaptive chosen-message security (`OneTimeEUFCMA`) -/

/-- One-time MAC oracle that answers at most the first tagging query using `M.sign sk` and returns
the empty word without tagging on any subsequent query. -/
noncomputable def oneTimeSigningOracle (M : MACScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool)) ProbComp (List Bool) :=
  fun queried =>
    if queried.isEmpty then do
      let tag ← M.sign sk request.2
      return (tag, [request.2])
    else
      return ([], queried)

/-- The one-time MAC EUF-CMA experiment: sample `sk ← M.keyGen n`, run the adaptive forger on
`(n, [])` with oracle access to `M.oneTimeSigningOracle sk`, and accept when the forger outputs a
valid tag on a `M.msgLen n`-bit message distinct from the queried message (if any). -/
noncomputable def eufOneTimeGame (M : MACScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.oneTimeSigningOracle sk)) (adversary n [])).run []
  return (out.1.1.length == M.msgLen n) && !out.2.contains out.1.1 &&
    M.verify sk out.1.1 out.1.2

/-- Running an oracle-PPT forger against `oneTimeSigningOracle` is uniformly strict PPT in the
unary security parameter and secret key. -/
@[program_certificate]
theorem isPPTOn_run_oneTimeSigningOracle (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.oneTimeSigningOracle caller.2)) (adversary caller.1 [])).run []) := by
  obtain ⟨c, d, hlen⟩ := M.sign_ppt.length_le
  have hhandler : IsPPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encList encBits)))
      (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        M.oneTimeSigningOracle pair.1.2 pair.2.1 pair.2.2) := by
    unfold oneTimeSigningOracle
    ppt
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List (List Bool)))
    (resources := fun caller query =>
      c * (2 * caller.2.length + query.length + 2) ^ d + 2 * query.length + 2)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request queried _ result hresult
  unfold oneTimeSigningOracle at hresult
  split_ifs at hresult with hempty
  · simp only [ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
    obtain ⟨tag, htag, rfl⟩ := hresult
    have htagLen := hlen (caller.2, request.2) tag htag
    simp only [encBits_apply, length_encPair] at htagLen
    refine ⟨trivial, by lia, ?_⟩
    rw [List.isEmpty_iff.mp hempty]
    simp only [encList_cons, encList_nil, List.length_append, List.length_nil, length_frame,
      encBits_apply]
    lia
  · simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hresult
    subst result
    exact ⟨trivial, by simp, by lia⟩

/-- Run the complete one-time MAC EUF-CMA experiment on its unary security parameter for any
oracle-PPT forger. -/
@[program_certificate]
theorem isPPTOn_eufOneTimeGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (M.eufOneTimeGame adversary) := by
  have hrun := M.isPPTOn_run_oneTimeSigningOracle hadversary
  have hpost : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool)) =>
        (pair.2.1.1.length == M.msgLen pair.1.1) && !pair.2.2.contains pair.2.1.1 &&
          M.verify pair.1.2 pair.2.1.1 pair.2.1.2)
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBits encBits) (encList encBits))) encBool := by
    polytime
  exact M.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-- The one-time MAC EUF-CMA experiment is uniformly strict PPT, independently of unused auxiliary
input. -/
@[program_certificate]
theorem isPPT_eufOneTimeGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => M.eufOneTimeGame adversary n) :=
  ((M.isPPTOn_eufOneTimeGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Existential unforgeability under one-time adaptive chosen-message attack for a symmetric MAC. -/
def OneTimeEUFCMA (M : MACScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.eufOneTimeGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- One-time EUF-CMA security gives negligible forgery probability for every oracle-PPT forger. -/
theorem OneTimeEUFCMA.negligible {M : MACScheme} (h : M.OneTimeEUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (M.eufOneTimeGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish one-time EUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem OneTimeEUFCMA.of_negligible {M : MACScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (M.eufOneTimeGame adversary n)))) :
    M.OneTimeEUFCMA := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

private theorem run_limitToOneQuery_eq_oneTimeSigningOracle (M : MACScheme)
    (bound : ℕ → ℕ → ℕ) (n : ℕ) (sk : List Bool)
    (hbound : ∀ msg tag, tag ∈ (ProbComp.eval (M.sign sk msg)).support →
      tag.length ≤ bound n msg.length)
    (prog : WordOracleComp Unit (List Bool × List Bool)) :
    ProbComp.eval (Prod.map Prod.fst id <$> ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.signingOracle sk))
      ((OracleComp.interpret
        (ProbOracleComp.handler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (SignatureScheme.oneTimeFilterHandler bound (n, [])))
        prog).run false)).run [])) =
    ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.oneTimeSigningOracle sk)) prog).run []) := by
  rw [ProbComp.eval_map, ProbOracleComp.eval_run_interpret, ProbOracleComp.eval_run_interpret,
    ProbOracleComp.run_interpret_run_interpret, PMF.map_comp]
  -- Reconstruct the filter flag from the query log, so no state invariant is needed.
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := fun q s => ProbComp.eval (M.oneTimeSigningOracle sk q s))
    (oracle' := fun q (state : Bool × List (List Bool)) =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun q s => ProbComp.eval (M.signingOracle sk q s)))
        ((SignatureScheme.oneTimeFilterHandler bound (n, []) q).run state.1)).run state.2).map
          (fun result => (result.1.1, result.1.2, result.2)))
    (represent := fun queried => (!queried.isEmpty, queried))
    (step := by
      intro ⟨⟨⟩, msg⟩ queried
      change _ = ((OracleComp.interpret (m := StateT (List (List Bool)) PMF) _
        (SignatureScheme.oneTimeFilterHandler bound (n, []) ((), msg)
          (!queried.isEmpty))).run queried).map _
      cases queried with
      | nil =>
        simp only [oneTimeSigningOracle, List.isEmpty_nil, ↓reduceIte, Bool.not_true,
          SignatureScheme.oneTimeFilterHandler, Bool.false_eq_true, Functor.map_map,
          OracleComp.interpret_map, StateT.run_map, ProbOracleComp.interpret_query,
          PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def, signingOracle,
          ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind]
        simp only [StateT.run, PMF.map_bind]
        refine PMF.bind_congr_on_support _ _ _ fun tag htag => ?_
        simp [List.take_of_length_le (hbound msg tag htag)]
      | cons head tail =>
        simp [oneTimeSigningOracle, SignatureScheme.oneTimeFilterHandler, OracleComp.interpret_pure,
          StateT.run_pure, ProbComp.eval_pure])
    prog []
  have hproj := congrArg (PMF.map (fun result => (result.1, result.2.2))) hsim
  rw [PMF.map_comp] at hproj
  exact hproj.symm.trans (PMF.map_id _)

/-- Full EUF-CMA security implies one-time EUF-CMA security for any `MACScheme`. -/
theorem EUFCMA.oneTimeEUFCMA {M : MACScheme} (h : M.EUFCMA) : M.OneTimeEUFCMA := by
  obtain ⟨ck, dk, hlenk⟩ := M.keyGen_ppt.length_le
  obtain ⟨cs, ds, hlens⟩ := M.sign_ppt.length_le
  let skBound (n : ℕ) : ℕ := ck * (n + 1) ^ dk
  let bound (n msgLen : ℕ) : ℕ := cs * (2 * skBound n + msgLen + 2) ^ ds
  have hbound_poly : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => bound p.1 p.2)
      (encPair encUnary encUnary) encUnary := by
    dsimp [bound, skBound]
    polytime
  apply OneTimeEUFCMA.of_negligible
  intro adversary hadversary
  have hred := h.negligible (SignatureScheme.limitToOneQuery bound adversary)
    (SignatureScheme.isOraclePPT_limitToOneQuery (.of_tidy hbound_poly) hadversary)
  refine hred.congr fun n => ?_
  congr 1
  simp only [eufOneTimeGame, eufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  have hskLen_raw := hlenk n sk hsk
  simp only [encUnary_apply, List.length_replicate, encBits_apply] at hskLen_raw
  have htagBound : ∀ msg tag, tag ∈ (ProbComp.eval (M.sign sk msg)).support →
      tag.length ≤ bound n msg.length := by
    intro msg tag htag
    have h1 := hlens (sk, msg) tag htag
    simp only [length_encPair, encBits_apply] at h1
    have h2 : 2 * sk.length + 1 + msg.length + 1 ≤ 2 * skBound n + msg.length + 2 := by
      dsimp [skBound]
      lia
    exact h1.trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left h2 ds))
  have hrun := run_limitToOneQuery_eq_oneTimeSigningOracle M bound n sk htagBound
    (adversary n [])
  have hmap : ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.signingOracle sk))
      (SignatureScheme.limitToOneQuery bound adversary n [])).run []) =
    Prod.map Prod.fst id <$> ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.signingOracle sk))
      ((OracleComp.interpret
        (ProbOracleComp.handler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (SignatureScheme.oneTimeFilterHandler bound (n, [])))
        (adversary n [])).run false)).run []) := by
    unfold SignatureScheme.limitToOneQuery
    rw [OracleComp.interpret_map, StateT.run_map]
    rfl
  rw [hmap]
  exact congrArg (fun p : PMF ((List Bool × List Bool) × List (List Bool)) =>
    p.bind fun x => PMF.pure
      ((x.1.1.length == M.msgLen n) && !x.2.contains x.1.1 && M.verify sk x.1.1 x.1.2)) hrun

/-! ### Strong adaptive chosen-message security (`SUFCMA`, Boneh–Shoup Attack Game 6.1) -/

/-- Stateful MAC tagging oracle that tags the requested message under `sk` and prepends the
returned `(msg, tag)` pair to the transcript of queried message/tag pairs
([Boneh and Shoup, Attack Game 6.1][BonehShoup2023]). -/
noncomputable def signingPairOracle (M : MACScheme) (sk : List Bool)
    (request : Unit × List Bool) : StateT (List (List Bool × List Bool)) ProbComp (List Bool) :=
  fun queriedPairs => do
    let tag ← M.sign sk request.2
    return (tag, (request.2, tag) :: queriedPairs)

/-- The strong (fresh-pair) MAC SUF-CMA experiment
([Boneh and Shoup, Attack Game 6.1 / Definition 6.2][BonehShoup2023]): sample `sk ← M.keyGen n`,
run the adaptive forger on `(n, [])` with oracle access to `M.signingPairOracle sk`, and accept when
the forger outputs a valid `(msg, tag)` pair on a `M.msgLen n`-bit message `msg` such that
`(msg, tag)` was never returned by the tagging oracle (`!out.2.contains out.1`). -/
noncomputable def sufCmaGame (M : MACScheme) (adversary : Forger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.signingPairOracle sk)) (adversary n [])).run []
  return (out.1.1.length == M.msgLen n) && !out.2.contains out.1 &&
    M.verify sk out.1.1 out.1.2

/-- Running an oracle-PPT forger against `signingPairOracle` is uniformly strict PPT in the unary
security parameter and secret key. -/
@[program_certificate]
theorem isPPTOn_run_signingPairOracle (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) (encList (encPair encBits encBits)))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.signingPairOracle caller.2)) (adversary caller.1 [])).run []) := by
  obtain ⟨c, d, hlen⟩ := M.sign_ppt.length_le
  have hhandler : IsPPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encList (encPair encBits encBits))))
      (encPair encBits (encList (encPair encBits encBits)))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool × List Bool)) =>
        M.signingPairOracle pair.1.2 pair.2.1 pair.2.2) := by
    unfold signingPairOracle
    ppt
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List (List Bool × List Bool)))
    (resources := fun caller query =>
      2 * (c * (2 * caller.2.length + query.length + 2) ^ d) + 4 * query.length + 6)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request queriedPairs _ result hresult
  simp only [signingPairOracle, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
  obtain ⟨tag, htag, rfl⟩ := hresult
  have htagLen := hlen (caller.2, request.2) tag htag
  simp only [encBits_apply, length_encPair] at htagLen
  refine ⟨trivial, by lia, ?_⟩
  simp only [encList_cons, List.length_append, length_frame, length_encPair, encBits_apply]
  lia

/-- Run the complete MAC SUF-CMA experiment on its unary security parameter for any oracle-PPT
forger. -/
@[program_certificate]
theorem isPPTOn_sufCmaGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPTOn encUnary encBool (M.sufCmaGame adversary) := by
  have hrun := M.isPPTOn_run_signingPairOracle hadversary
  have hcontains : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool × List Bool)) =>
        pair.2.2.contains pair.2.1)
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBits encBits) (encList (encPair encBits encBits)))) encBool := by
    have hlist : ComputableInPolyTime
        (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool × List Bool)) =>
          pair.2.2)
        (encPair (encPair encUnary encBits)
          (encPair (encPair encBits encBits) (encList (encPair encBits encBits))))
        (encList (encPair encBits encBits)) := by polytime
    have helem : ComputableInPolyTime
        (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool × List Bool)) =>
          pair.2.1)
        (encPair (encPair encUnary encBits)
          (encPair (encPair encBits encBits) (encList (encPair encBits encBits))))
        (encPair encBits encBits) := by polytime
    classical
    convert ComputableInPolyTime.decide_mem hlist helem using 1
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, decide_eq_true_eq]
  have hverify : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool × List Bool)) =>
        M.verify pair.1.2 pair.2.1.1 pair.2.1.2)
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBits encBits) (encList (encPair encBits encBits)))) encBool :=
    M.verify_polyTime.comp (show ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool × List Bool)) =>
        (pair.1.2, pair.2.1.1, pair.2.1.2))
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBits encBits) (encList (encPair encBits encBits))))
      (encPair encBits (encPair encBits encBits)) by fun_prop)
  have hsize : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool × List Bool)) =>
        pair.2.1.1.length == M.msgLen pair.1.1)
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBits encBits) (encList (encPair encBits encBits)))) encBool :=
    ComputableInPolyTime.beq (encB := encUnary)
      (ComputableInPolyTime.length_bits.comp (show ComputableInPolyTime
        (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool × List Bool)) =>
          pair.2.1.1)
        (encPair (encPair encUnary encBits)
          (encPair (encPair encBits encBits) (encList (encPair encBits encBits))))
        encBits by fun_prop))
      (M.msgLen_polyTime.comp (show ComputableInPolyTime
        (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool × List Bool)) =>
          pair.1.1)
        (encPair (encPair encUnary encBits)
          (encPair (encPair encBits encBits) (encList (encPair encBits encBits))))
        encUnary by fun_prop))
  have hpost : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool × List Bool)) =>
        (pair.2.1.1.length == M.msgLen pair.1.1) && !pair.2.2.contains pair.2.1 &&
          M.verify pair.1.2 pair.2.1.1 pair.2.1.2)
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBits encBits) (encList (encPair encBits encBits)))) encBool := by
    exact ComputableInPolyTime.bool_and.comp
      ((ComputableInPolyTime.bool_and.comp
        (hsize.prod (ComputableInPolyTime.bool_not.comp hcontains))).prod hverify)
  exact M.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-- The MAC SUF-CMA experiment is uniformly strict PPT, independently of unused auxiliary input. -/
@[program_certificate]
theorem isPPT_sufCmaGame (M : MACScheme) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsPPT encBool (fun n _ => M.sufCmaGame adversary n) :=
  ((M.isPPTOn_sufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Strong (fresh-pair) existential unforgeability under adaptive chosen-message attack (`SUFCMA`)
for a symmetric MAC against uniform strict oracle-PPT adversaries
([Boneh and Shoup, Attack Game 6.1 / Definition 6.2][BonehShoup2023]). -/
def SUFCMA (M : MACScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.sufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair encBits encBits))

/-- Strong unforgeability gives negligible SUF-CMA forgery probability for every oracle-PPT
forger. -/
theorem SUFCMA.negligible {M : MACScheme} (h : M.SUFCMA)
    (adversary : Forger) (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish SUF-CMA security by bounding every oracle-PPT forger's success probability. -/
theorem SUFCMA.of_negligible {M : MACScheme}
    (h : ∀ adversary, IsOraclePPT (encPair encBits encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n)))) :
    M.SUFCMA := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Running an adaptive program against `signingOracle` produces the exact same distribution as
running it against `signingPairOracle` and projecting the pair transcript to its queried
messages. -/
theorem eval_run_signingOracle_eq_map_fst_signingPairOracle (M : MACScheme)
    (sk : List Bool) (prog : WordOracleComp Unit (List Bool × List Bool)) :
    ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.signingOracle sk)) prog).run []) =
    (ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.signingPairOracle sk)) prog).run [])).map
      (fun (a, s') => (a, s'.map Prod.fst)) := by
  rw [ProbOracleComp.eval_run_interpret, ProbOracleComp.eval_run_interpret]
  exact (ProbOracleComp.run_interpret_map_state
    (oracle := fun q s => ProbComp.eval (M.signingPairOracle sk q s))
    (oracle' := fun q s => ProbComp.eval (M.signingOracle sk q s))
    (represent := List.map Prod.fst)
    (step := by
      intro ⟨⟨⟩, msg⟩ queriedPairs
      simp [signingPairOracle, signingOracle, PMF.map_comp, Function.comp_def])
    prog []).symm

/-- `eufCmaGame` evaluates the same pair-logging execution `signingPairOracle` as `sufCmaGame`,
checking message freshness `!(out.2.map Prod.fst).contains out.1.1` on the projected message log. -/
theorem eval_eufCmaGame_eq_signingPairOracle (M : MACScheme)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (M.eufCmaGame adversary n) =
      ProbComp.eval (do
        let sk ← M.keyGen n
        let out ← (OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.signingPairOracle sk)) (adversary n [])).run []
        return (out.1.1.length == M.msgLen n) && !(out.2.map Prod.fst).contains out.1.1 &&
          M.verify sk out.1.1 out.1.2) := by
  simp only [eufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk _ => ?_
  rw [M.eval_run_signingOracle_eq_map_fst_signingPairOracle sk (adversary n []), PMF.bind_map]
  rfl

private theorem pmf_bind_pure_bool_le {α : Type} (p : PMF α) (f g : α → Bool)
    (hfg : ∀ a ∈ p.support, f a = true → g a = true) :
    (p.bind (fun a => PMF.pure (f a))) true ≤
      (p.bind (fun a => PMF.pure (g a))) true := by
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ p.support
  · refine mul_le_mul_of_nonneg_left ?_ zero_le
    cases hf : f a
    · simp
    · rw [hfg a ha hf]
  · simp [(p.apply_eq_zero_iff a).mpr ha]

/-- **Quantitative EUF-CMA vs. SUF-CMA bound**: for every `MACScheme`, adaptive forger, and
security parameter `n`, the fresh-message EUF-CMA forgery probability is at most the strong
fresh-pair SUF-CMA forgery probability. -/
theorem succProbability_eufCmaGame_le_sufCmaGame (M : MACScheme)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n)) := by
  rw [M.eval_eufCmaGame_eq_signingPairOracle adversary n]
  simp only [Game.succProbability, sufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ true) ?_
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun sk => ?_
  refine mul_le_mul_of_nonneg_left (pmf_bind_pure_bool_le _ _ _ fun out _ hout => ?_) zero_le
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hout ⊢
  refine ⟨⟨hout.1.1, ?_⟩, hout.2⟩
  rw [Bool.eq_false_iff]
  intro hmemPair
  have hmemFst : out.1.1 ∈ out.2.map Prod.fst :=
    List.mem_map_of_mem (List.contains_iff_mem.mp hmemPair)
  have hcontainsFst : (out.2.map Prod.fst).contains out.1.1 = true :=
    List.contains_iff_mem.mpr hmemFst
  rw [hout.1.2] at hcontainsFst
  contradiction

/-- Strong unforgeability (`SUFCMA`) implies ordinary fresh-message unforgeability (`EUFCMA`) for
every `MACScheme`. -/
theorem SUFCMA.eufCma {M : MACScheme} (h : M.SUFCMA) : M.EUFCMA := by
  apply EUFCMA.of_negligible
  intro adversary hadversary
  exact negligible_of_le (h.negligible adversary hadversary)
    (M.succProbability_eufCmaGame_le_sufCmaGame adversary)

/-- Strong unforgeability (`SUFCMA`) implies one-time unforgeability (`OneTimeEUFCMA`) for every
`MACScheme`. -/
theorem SUFCMA.oneTimeEUFCMA {M : MACScheme} (h : M.SUFCMA) : M.OneTimeEUFCMA :=
  h.eufCma.oneTimeEUFCMA

private theorem mem_support_signingPairOracle (M : MACScheme) (sk : List Bool)
    (prog : WordOracleComp Unit (List Bool × List Bool))
    (result : List Bool × List Bool) (queriedPairs : List (List Bool × List Bool))
    (hmem : (result, queriedPairs) ∈ (ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.signingPairOracle sk)) prog).run [])).support) :
    ∀ pair ∈ queriedPairs, pair.2 ∈ (ProbComp.eval (M.sign sk pair.1)).support := by
  rw [ProbOracleComp.eval_run_interpret] at hmem
  refine ProbOracleComp.run_interpret_invariant
    (fun q s => ProbComp.eval (M.signingPairOracle sk q s))
    (fun s => ∀ pair ∈ s, pair.2 ∈ (ProbComp.eval (M.sign sk pair.1)).support)
    ?_ prog [] (by simp) result queriedPairs hmem
  intro ⟨⟨⟩, msg⟩ s hs a s' hstep pair hpair
  simp only [signingPairOracle, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hstep
  obtain ⟨tag, htag, hpairEq⟩ := hstep
  cases hpairEq
  rw [List.mem_cons] at hpair
  rcases hpair with rfl | htail
  · exact htag
  · exact hs pair htail

/-- For any `MACScheme` whose valid tags on `M.msgLen n`-bit messages under supported secret keys
agree with every tag in the support of `M.sign`, the `sufCmaGame` and `eufCmaGame` distributions
are identical. -/
theorem eval_sufCmaGame_eq_eufCmaGame_of_unique_tag (M : MACScheme)
    (huniq : ∀ n sk, sk ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = M.msgLen n → ∀ tag tag',
      M.verify sk msg tag = true →
      tag' ∈ (ProbComp.eval (M.sign sk msg)).support → tag' = tag)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (M.sufCmaGame adversary n) =
      ProbComp.eval (M.eufCmaGame adversary n) := by
  rw [M.eval_eufCmaGame_eq_signingPairOracle adversary n]
  simp only [sufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨msg, tag⟩, queriedPairs⟩ hout => ?_
  have hinv := M.mem_support_signingPairOracle sk (adversary n []) (msg, tag) queriedPairs hout
  congr 1
  by_cases hlen : (msg.length == M.msgLen n) = true
  · by_cases hver : M.verify sk msg tag = true
    · have hmsgLen : msg.length = M.msgLen n := beq_iff_eq.mp hlen
      have hmem_iff : (msg, tag) ∈ queriedPairs ↔ ∃ x, (msg, x) ∈ queriedPairs := by
        refine ⟨fun h => ⟨tag, h⟩, ?_⟩
        rintro ⟨qtag, hmemPair⟩
        have hqtag := hinv (msg, qtag) hmemPair
        have heq := huniq n sk hsk msg hmsgLen tag qtag hver hqtag
        subst heq
        exact hmemPair
      simp [hlen, hver, hmem_iff]
    · have hverF : M.verify sk msg tag = false := Bool.eq_false_iff.mpr hver
      simp [hverF]
  · have hlenF : (msg.length == M.msgLen n) = false := Bool.eq_false_iff.mpr hlen
    simp [hlenF]

/-- For a `MACScheme` with unique valid tags per `(sk, msg)`, the SUF-CMA and EUF-CMA forgery
probabilities are equal for every forger and security parameter `n`. -/
theorem succProbability_sufCmaGame_eq_eufCmaGame_of_unique_tag (M : MACScheme)
    (huniq : ∀ n sk, sk ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = M.msgLen n → ∀ tag tag',
      M.verify sk msg tag = true →
      tag' ∈ (ProbComp.eval (M.sign sk msg)).support → tag' = tag)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n)) =
      Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)) := by
  rw [M.eval_sufCmaGame_eq_eufCmaGame_of_unique_tag huniq adversary n]

/-- For a `MACScheme` with unique valid tags per `(sk, msg)`, strong unforgeability (`SUFCMA`) is
equivalent to ordinary fresh-message unforgeability (`EUFCMA`). -/
theorem sufCma_iff_eufCma_of_unique_tag (M : MACScheme)
    (huniq : ∀ n sk, sk ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = M.msgLen n → ∀ tag tag',
      M.verify sk msg tag = true →
      tag' ∈ (ProbComp.eval (M.sign sk msg)).support → tag' = tag) :
    M.SUFCMA ↔ M.EUFCMA := by
  refine ⟨SUFCMA.eufCma, fun h => ?_⟩
  apply SUFCMA.of_negligible
  intro adversary hadversary
  refine (h.negligible adversary hadversary).congr fun n => ?_
  exact (M.succProbability_sufCmaGame_eq_eufCmaGame_of_unique_tag huniq adversary n).symm

/-! ### Schedule reindexing of a `MACScheme` (`reindex`, `reindexForger`) -/

/-- Reindex a `MACScheme` along a polynomial-time parameter schedule `ℓ : ℕ → ℕ`: at security
parameter `n`, `M.reindex ℓ hℓ` samples keys via `M.keyGen (ℓ n)` and authenticates messages of
length `M.msgLen (ℓ n)`. -/
noncomputable def reindex (M : MACScheme) (ℓ : ℕ → ℕ)
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) : MACScheme where
  msgLen n := M.msgLen (ℓ n)
  msgLen_polyTime := M.computableInPolyTime_msgLen_comp hℓ
  keyGen n := M.keyGen (ℓ n)
  sign := M.sign
  verify := M.verify
  keyGen_ppt := M.isPPTOn_keyGen_comp hℓ
  sign_ppt := M.sign_ppt
  verify_polyTime := M.verify_polyTime
  verify_sign := fun n sk hsk msg hmsg tag htag =>
    M.verify_sign (ℓ n) sk hsk msg hmsg tag htag

/-- Wrap a forger `adversary` against `M.reindex ℓ hℓ` into a forger against `M`: given unary
parameter `m` and auxiliary input `aux`, recover `n := GeneratorReindex.parameter ℓ m`; if
`ℓ n == m`, run `adversary n aux`, and otherwise return `([], [])` without querying the oracle. -/
def reindexForger (ℓ : ℕ → ℕ) (adversary : Forger) : Forger :=
  fun m aux =>
    let n := GeneratorReindex.parameter ℓ m
    if ℓ n == m then
      adversary n aux
    else
      pure ([], [])

/-- At any parameter `m = ℓ n` of a strictly monotone schedule `ℓ`, `reindexForger ℓ adversary`
executes `adversary n`. -/
@[simp]
theorem reindexForger_apply_of_strictMono {ℓ : ℕ → ℕ} (hmono : StrictMono ℓ)
    (adversary : Forger) (n : ℕ) (aux : List Bool) :
    reindexForger ℓ adversary (ℓ n) aux = adversary n aux := by
  simp [reindexForger, GeneratorReindex.parameter_apply_of_strictMono hmono]

/-- `reindexForger ℓ adversary` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_reindexForger {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encBits encBits) (reindexForger ℓ adversary) := by
  have hcond : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool => ℓ (GeneratorReindex.parameter ℓ p.1) == p.1)
      (encPair encUnary encBits) encBool := by
    apply ComputableInPolyTime.tidy
    polytime
  have hprep : ComputableTidilyInPolyTime
      (fun p : ℕ × List Bool => (GeneratorReindex.parameter ℓ p.1, p.2))
      (encPair encUnary encBits) (encPair encUnary encBits) := by
    apply ComputableInPolyTime.tidy
    polytime
  have hyes : IsOraclePPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun p : ℕ × List Bool => adversary (GeneratorReindex.parameter ℓ p.1) p.2) :=
    hadversary.preprocess hprep
  have hno : IsOraclePPTOn (encPair encUnary encBits) (encPair encBits encBits)
      (fun _ : ℕ × List Bool => (pure ([], []) : WordOracleComp Unit (List Bool × List Bool))) :=
    (ComputableTidilyInPolyTime.const (([] : List Bool), ([] : List Bool))).isOraclePPTOn
      (Operation := Unit)
  unfold reindexForger
  exact (IsOraclePPTOn.cond hcond hyes hno).isOraclePPT

/-- For a strictly monotone schedule `ℓ`, `(M.reindex ℓ hℓ).sufCmaGame adversary n` is identical to
`M.sufCmaGame (reindexForger ℓ adversary) (ℓ n)`. -/
@[simp]
theorem sufCmaGame_reindex (M : MACScheme) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ)
    (adversary : Forger) (n : ℕ) :
    (M.reindex ℓ hℓ).sufCmaGame adversary n =
      M.sufCmaGame (reindexForger ℓ adversary) (ℓ n) := by
  unfold sufCmaGame signingPairOracle reindex
  rw [reindexForger_apply_of_strictMono hmono]

/-- For a strictly monotone schedule `ℓ`, `(M.reindex ℓ hℓ).eufCmaGame adversary n` is identical to
`M.eufCmaGame (reindexForger ℓ adversary) (ℓ n)`. -/
@[simp]
theorem eufCmaGame_reindex (M : MACScheme) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ)
    (adversary : Forger) (n : ℕ) :
    (M.reindex ℓ hℓ).eufCmaGame adversary n =
      M.eufCmaGame (reindexForger ℓ adversary) (ℓ n) := by
  unfold eufCmaGame signingOracle reindex
  rw [reindexForger_apply_of_strictMono hmono]

/-- For a strictly monotone schedule `ℓ`, `(M.reindex ℓ hℓ).eufOneTimeGame adversary n` is
identical to `M.eufOneTimeGame (reindexForger ℓ adversary) (ℓ n)`. -/
@[simp]
theorem eufOneTimeGame_reindex (M : MACScheme) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ)
    (adversary : Forger) (n : ℕ) :
    (M.reindex ℓ hℓ).eufOneTimeGame adversary n =
      M.eufOneTimeGame (reindexForger ℓ adversary) (ℓ n) := by
  unfold eufOneTimeGame oneTimeSigningOracle reindex
  rw [reindexForger_apply_of_strictMono hmono]

/-- Strong unforgeability (`SUFCMA`) is preserved under reindexing along any strictly monotone
plain polynomial-time schedule `ℓ`. -/
theorem SUFCMA.reindex {M : MACScheme} (h : M.SUFCMA) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ) :
    (M.reindex ℓ hℓ).SUFCMA := by
  apply SUFCMA.of_negligible
  intro adversary hadversary
  have hneg := h.negligible (reindexForger ℓ adversary)
    (isOraclePPT_reindexForger hℓ hadversary)
  have hcomp : Negligible (fun n =>
      Game.succProbability (ProbComp.eval (M.sufCmaGame (reindexForger ℓ adversary) (ℓ n)))) :=
    hneg.comp_of_polynomial_bound (bound := id) hmono.tendsto_atTop (by fun_prop)
      (Filter.Eventually.of_forall hmono.id_le)
  refine hcomp.congr fun n => ?_
  rw [sufCmaGame_reindex M hℓ hmono adversary n]

/-- Ordinary fresh-message unforgeability (`EUFCMA`) is preserved under reindexing along any
strictly monotone plain polynomial-time schedule `ℓ`. -/
theorem EUFCMA.reindex {M : MACScheme} (h : M.EUFCMA) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ) :
    (M.reindex ℓ hℓ).EUFCMA := by
  apply EUFCMA.of_negligible
  intro adversary hadversary
  have hneg := h.negligible (reindexForger ℓ adversary)
    (isOraclePPT_reindexForger hℓ hadversary)
  have hcomp : Negligible (fun n =>
      Game.succProbability (ProbComp.eval (M.eufCmaGame (reindexForger ℓ adversary) (ℓ n)))) :=
    hneg.comp_of_polynomial_bound (bound := id) hmono.tendsto_atTop (by fun_prop)
      (Filter.Eventually.of_forall hmono.id_le)
  refine hcomp.congr fun n => ?_
  rw [eufCmaGame_reindex M hℓ hmono adversary n]

/-- One-time unforgeability (`OneTimeEUFCMA`) is preserved under reindexing along any strictly
monotone plain polynomial-time schedule `ℓ`. -/
theorem OneTimeEUFCMA.reindex {M : MACScheme} (h : M.OneTimeEUFCMA) {ℓ : ℕ → ℕ}
    (hℓ : ComputableInPolyTime ℓ encUnary encUnary) (hmono : StrictMono ℓ) :
    (M.reindex ℓ hℓ).OneTimeEUFCMA := by
  apply OneTimeEUFCMA.of_negligible
  intro adversary hadversary
  have hneg := h.negligible (reindexForger ℓ adversary)
    (isOraclePPT_reindexForger hℓ hadversary)
  have hcomp : Negligible (fun n =>
      Game.succProbability (ProbComp.eval (M.eufOneTimeGame (reindexForger ℓ adversary) (ℓ n)))) :=
    hneg.comp_of_polynomial_bound (bound := id) hmono.tendsto_atTop (by fun_prop)
      (Filter.Eventually.of_forall hmono.id_le)
  refine hcomp.congr fun n => ?_
  rw [eufOneTimeGame_reindex M hℓ hmono adversary n]

end MACScheme

/-! ### Canonical PRF-based MAC (`prfMAC`, Boneh–Shoup Section 6.3 & Theorem 6.2) -/

/-- Canonical deterministic MAC constructed from a keyed function family `family`
([Boneh and Shoup, Section 6.3][BonehShoup2023]):
* `keyGen n` samples a uniform `n`-bit key via `BitString.sampleList n`.
* `sign sk msg` returns `prfOracle family sk.length sk msg` (which evaluates `family sk msg` on
  `sk.length`-bit messages and rejects malformed queries with `[]`).
* `verify sk msg tag` checks `msg.length == sk.length` and `family sk msg == tag`. -/
noncomputable def prfMAC (family : List Bool → List Bool → List Bool)
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits) : MACScheme where
  keyGen n := BitString.sampleList n
  sign sk msg := pure (prfOracle family sk.length sk msg)
  verify sk msg tag := (msg.length == sk.length) && (family sk msg == tag)
  keyGen_ppt := by ppt
  sign_ppt := by
    have htidy := hpoly.tidy
    have hbody : ComputableTidilyInPolyTime
        (fun p : List Bool × List Bool => prfOracle family p.1.length p.1 p.2)
        (encPair encBits encBits) encBits := by
      have heq : (fun p : List Bool × List Bool => prfOracle family p.1.length p.1 p.2) =
          (fun p : List Bool × List Bool =>
            if p.2.length == p.1.length then family p.1 p.2 else []) := by
        funext p
        simp [prfOracle]
      rw [heq]
      polytime
    exact hbody.isPPTOn
  verify_polyTime := by
    have htidy := hpoly.tidy
    have hcall : ComputableTidilyInPolyTime
        (fun p : List Bool × List Bool × List Bool => family p.1 p.2.1)
        (encPair encBits (encPair encBits encBits)) encBits :=
      htidy.comp ((ComputableTidilyInPolyTime.fst _ _).prod
        ((ComputableTidilyInPolyTime.fst _ _).comp (ComputableTidilyInPolyTime.snd _ _)))
    exact .of_tidy (by polytime)
  verify_sign := by
    intro n sk hsk msg hmsg tag htag
    rw [BitString.eval_sampleList] at hsk
    have hskLen : sk.length = n := BitString.length_of_mem_support_uniformList hsk
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at htag
    subst htag
    simp [prfOracle, hskLen, hmsg]

/-- Open stateful handler that forwards each MAC signing request to the external PRF/random-function
oracle (truncating the reply to `n` bits) and records the queried message in the query log. -/
def macLogHandler (n : ℕ) (request : Unit × List Bool) :
    StateT (List (List Bool)) (WordOracleComp Unit) (List Bool) :=
  fun queried =>
    (fun tag => (tag, request.2 :: queried)) <$>
      (List.take n <$> ProbOracleComp.query ((), request.2))

/-- Oracle reduction turning an adaptive MAC forger `adversary` into an `OracleDistinguisher` for
the PRF security game [Boneh and Shoup, Section 6.3, Theorem 6.2][BonehShoup2023]:
1. Run `adversary n []`, answering each tagging query via `macLogHandler n` and logging all queried
   messages.
2. When `adversary` outputs `((msg, tag), queried)`, if `msg.length == n` and
   `!queried.contains msg`, query the external oracle once on `msg` (reading at most `n` bits) and
   check whether the reply equals `tag`; otherwise return `false`. -/
def macToPrfDistinguisher (adversary : Forger) : OracleDistinguisher :=
  fun n _ => do
    let out ← (OracleComp.interpret
      (ProbOracleComp.handler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (macLogHandler n))
      (adversary n [])).run []
    if (out.1.1.length == n) && !out.2.contains out.1.1 then
      (· == out.1.2) <$> (List.take n <$> ProbOracleComp.query ((), out.1.1))
    else
      pure false

/-- `macToPrfDistinguisher` preserves strict oracle-PPT admissibility (`IsOraclePPT`). -/
theorem isOraclePPT_macToPrfDistinguisher {adversary : Forger}
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT encBool (macToPrfDistinguisher adversary) := by
  have hhandler : IsOraclePPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinEnum Unit) encBits) (encList encBits)))
      (encPair encBits (encList encBits))
      (fun pair : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
        macLogHandler pair.1.1 pair.2.1 pair.2.2) := by
    unfold macLogHandler
    have hq : IsOraclePPTOn
        (encPair (encPair encUnary encBits)
          (encPair (encPair (encFinEnum Unit) encBits) (encList encBits)))
        encBits
        (fun p : (ℕ × List Bool) × ((Unit × List Bool) × List (List Bool)) =>
          List.take p.1.1 <$> ProbOracleComp.query ((), p.2.1.2)) :=
      IsOraclePPTOn.query_take () (by polytime) (by polytime)
    exact hq.map_with (by polytime)
  have hrun : IsOraclePPTOn (encPair encUnary encBits)
      (encPair (encPair encBits encBits) (encList encBits))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler
            (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
            (macLogHandler caller.1))
          (adversary caller.1 [])).run []) := by
    apply hadversary.run_interpret_preprocess_open
      (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
      (initial := fun _ => ([] : List (List Bool)))
      (resources := fun caller query => caller.1 + 2 * query.length + 2)
      (by fun_prop) hhandler (by fun_prop)
      (fun _ _ => True) (fun _ => trivial) (by polytime)
    intro caller request queried _ result hresult
    unfold macLogHandler at hresult
    obtain ⟨tag, htag, rfl⟩ := ProbOracleComp.mem_support_map hresult
    obtain ⟨rawTag, _, rfl⟩ := ProbOracleComp.mem_support_map htag
    refine ⟨trivial, ?_, ?_⟩
    · exact (List.length_take_le _ _).trans (by lia)
    · simp only [encList_cons, List.length_append, length_frame, encBits_apply]
      lia
  have hcond : ComputableTidilyInPolyTime
      (fun p : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool)) =>
        (p.2.1.1.length == p.1.1) && !p.2.2.contains p.2.1.1)
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBits encBits) (encList encBits)))
      encBool := by
    polytime
  have hyes : IsOraclePPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBits encBits) (encList encBits)))
      encBool
      (fun p : (ℕ × List Bool) × ((List Bool × List Bool) × List (List Bool)) =>
        (· == p.2.1.2) <$> (List.take p.1.1 <$> ProbOracleComp.query ((), p.2.1.1))) :=
    (IsOraclePPTOn.query_take () (by polytime) (by polytime)).map_with (by polytime)
  have hno : IsOraclePPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair encBits encBits) (encList encBits)))
      encBool
      (fun _ => pure false) :=
    (ComputableTidilyInPolyTime.const false).isOraclePPTOn (Operation := Unit)
  unfold macToPrfDistinguisher
  exact (hrun.bind_with (IsOraclePPTOn.cond hcond hyes hno)).isOraclePPT

private theorem run_macLogHandler_eq_signingOracle
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (n : ℕ) (sk : List Bool) (hsk : sk.length = n)
    (prog : WordOracleComp Unit (List Bool × List Bool)) :
    ProbComp.eval (OracleComp.interpret
      (ProbOracleComp.handler ProbComp.unifFin (fun request =>
        pure (prfOracle family n sk request.2)))
      ((OracleComp.interpret
        (ProbOracleComp.handler
          (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
          (macLogHandler n))
        prog).run [])) =
    ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        ((prfMAC family hpoly).signingOracle sk)) prog).run []) := by
  have hread := ProbOracleComp.run_interpret_readOnly
    (fun request (_ : Unit) => PMF.pure (prfOracle family n sk request.2))
    ((OracleComp.interpret
      (ProbOracleComp.handler
        (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
        (macLogHandler n))
      prog).run []) ()
  have hfst := congrArg (PMF.map Prod.fst) hread
  simp only [PMF.map_comp, Function.comp_def] at hfst
  rw [show (fun x : (List Bool × List Bool) × List (List Bool) => x) = id from rfl,
    PMF.map_id] at hfst
  simp only [ProbOracleComp.eval_interpret, ProbComp.eval_pure]
  rw [← hfst, ProbOracleComp.run_interpret_run_interpret, ProbOracleComp.eval_run_interpret]
  have hsim := ProbOracleComp.run_interpret_map_state
    (oracle := fun q (state : List (List Bool) × Unit) =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun request (u : Unit) => (PMF.pure (prfOracle family n sk request.2)).map (·, u)))
        ((macLogHandler n q).run state.1)).run state.2).map
          (fun result => (result.1.1, result.1.2, result.2)))
    (oracle' := fun q s => ProbComp.eval ((prfMAC family hpoly).signingOracle sk q s))
    (represent := Prod.fst)
    (step := by
      intro ⟨⟨⟩, msg⟩ ⟨queried, ⟨⟩⟩
      change PMF.map (fun (a, s') => (a, s'.1))
          (((OracleComp.interpret
            (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
              (fun request (u : Unit) => (PMF.pure (prfOracle family n sk request.2)).map (·, u)))
            (macLogHandler n ((), msg) queried)).run ()).map
              (fun result => (result.1.1, result.1.2, result.2))) =
        ProbComp.eval ((prfMAC family hpoly).signingOracle sk ((), msg) queried)
      simp only [macLogHandler, Functor.map_map, OracleComp.interpret_map, StateT.run_map,
        ProbOracleComp.interpret_query, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def,
        PMF.pure_map]
      dsimp only [StateT.run]
      simp only [MACScheme.signingOracle, prfMAC, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.pure_bind, hsk]
      by_cases hmsg : msg.length = n
      · have hlen_eq : (family sk msg).length = n := by
          rw [← hsk]
          exact hlen sk msg (hmsg.trans hsk.symm)
        simp [prfOracle, hmsg, List.take_of_length_le hlen_eq.le]
      · simp [prfOracle, hmsg])
    prog ([], ())
  simpa only [PMF.map_comp, Function.comp_def] using hsim

/-- Running `macToPrfDistinguisher adversary` in `prfRealGame family` produces the exact same
Boolean distribution as the EUF-CMA experiment for `prfMAC family`. -/
theorem eval_prfRealGame_macToPrfDistinguisher
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (prfRealGame family (macToPrfDistinguisher adversary) n) =
      ProbComp.eval ((prfMAC family hpoly).eufCmaGame adversary n) := by
  simp only [prfRealGame, MACScheme.eufCmaGame, macToPrfDistinguisher,
    OracleComp.interpret_bind, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  have hsk' : sk ∈ (ProbComp.eval (BitString.sampleList n)).support := hsk
  rw [BitString.eval_sampleList] at hsk'
  have hskLen : sk.length = n := BitString.length_of_mem_support_uniformList hsk'
  rw [run_macLogHandler_eq_signingOracle hpoly hlen n sk hskLen (adversary n [])]
  refine PMF.bind_congr_on_support _ _ _ fun out _ => ?_
  dsimp only [prfMAC]
  by_cases hcond : ((out.1.1.length == n) && !out.2.contains out.1.1) = true
  · simp only [hcond, ↓reduceIte, Bool.true_and]
    have hmsgLen : out.1.1.length = n := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      exact hcond.1
    have hfamLen : (family sk out.1.1).length = n := by
      rw [← hskLen]
      exact hlen sk out.1.1 (hmsgLen.trans hskLen.symm)
    simp only [Functor.map_map, OracleComp.interpret_map,
      ProbOracleComp.interpret_query, ProbComp.eval_map, ProbComp.eval_pure, PMF.pure_map,
      prfOracle, hmsgLen, ↓reduceIte, List.take_of_length_le hfamLen.le, hskLen, beq_self_eq_true,
      Bool.true_and]
  · have hcondF : ((out.1.1.length == n) && !out.2.contains out.1.1) = false :=
      Bool.eq_false_iff.mpr hcond
    simp only [hcondF, Bool.false_eq_true, ↓reduceIte, Bool.false_and,
      OracleComp.interpret_pure, ProbComp.eval_pure]

private theorem uniformOfFintype_bitString_beq_true_le (n : ℕ) (target : List Bool) :
    ((PMF.uniformOfFintype (BitString n)).map (fun v => List.ofFn v == target)) true ≤
      (1 : ℝ≥0∞) / 2 ^ n := by
  have heq : (PMF.uniformOfFintype (BitString n)).map (fun v => List.ofFn v == target) =
      (BitString.uniformList n).map (· == target) := by
    simp [BitString.uniformList, PMF.map_comp, Function.comp_def]
  rw [heq, BitString.uniformList_map_apply]
  have hcard : (Finset.univ.filter fun r : Fin n → Bool =>
      (List.ofFn r == target) = true).card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr fun {a b} ha hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, beq_iff_eq] at ha hb
    exact List.ofFn_injective (ha.trans hb.symm)
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) (2 ^ n)

/-- In the ideal random-function game, `macToPrfDistinguisher adversary` succeeds with probability
at most `1 / 2 ^ n`: any unqueried `n`-bit forgery message misses the lazy random-oracle cache and
draws a fresh uniform `n`-bit tag, matching the forger's candidate tag with probability at most
`1 / 2 ^ n`. -/
theorem succProbability_prfIdealGame_macToPrfDistinguisher_le (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (prfIdealGame (macToPrfDistinguisher adversary) n)) ≤
      (1 : ℝ≥0) / 2 ^ n := by
  classical
  rw [prfIdealGame_eq_lazy]
  let combinedOracle : Unit × List Bool →
      StateT (List (List Bool) × RandomOracle.Cache (fun _ : BitString n => BitString n))
        PMF (List Bool) :=
    fun q state =>
      ((OracleComp.interpret
        (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun request => lazyRandomFunctionOracle n request.2))
        ((macLogHandler n q).run state.1)).run state.2).map
          (fun result => (result.1.1, result.1.2, result.2))
  let phase1 := ((OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k)) combinedOracle)
    (adversary n [])).run ([], fun _ => none))
  let phase2 : ((List Bool × List Bool) × List (List Bool) ×
      RandomOracle.Cache (fun _ : BitString n => BitString n)) → PMF Bool :=
    fun ⟨out, queried, cache⟩ =>
      if (out.1.length == n) && !queried.contains out.1 then
        ((OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
            (fun request => lazyRandomFunctionOracle n request.2))
          ((· == out.2) <$> (List.take n <$> ProbOracleComp.query ((), out.1)))).run cache).map
            Prod.fst
      else
        PMF.pure false
  have hgame : ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun request => lazyRandomFunctionOracle n request.2))
      (macToPrfDistinguisher adversary n [])).run (fun _ => none)).map Prod.fst =
      phase1.bind phase2 := by
    dsimp only [macToPrfDistinguisher, phase1, phase2, combinedOracle]
    simp only [OracleComp.interpret_bind, StateT.run_bind, PMF.monad_bind_eq_bind, PMF.map_bind,
      ProbOracleComp.run_interpret_run_interpret, PMF.bind_map, Function.comp_def]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨out, queried, cache⟩ _ => ?_
    by_cases hcond : ((out.1.length == n) && !queried.contains out.1) = true
    · simp only [hcond, ↓reduceIte]
    · have hcondF : ((out.1.length == n) && !queried.contains out.1) = false :=
        Bool.eq_false_iff.mpr hcond
      simp only [hcondF, Bool.false_eq_true, ↓reduceIte, OracleComp.interpret_pure,
        StateT.run_pure, PMF.monad_pure_eq_pure, PMF.pure_map]
  have hinv : ∀ result state,
      (result, state) ∈ phase1.support →
      ∀ x : BitString n, state.2 x ≠ none → List.ofFn x ∈ state.1 := by
    intro result state hmem
    refine ProbOracleComp.run_interpret_invariant combinedOracle
      (fun s => ∀ x : BitString n, s.2 x ≠ none → List.ofFn x ∈ s.1)
      ?_ (adversary n []) ([], fun _ => none) (by simp) result state hmem
    intro ⟨⟨⟩, msg⟩ ⟨queried, cache⟩ hstate val ⟨queried', cache'⟩ hstep
    dsimp only [combinedOracle] at hstep
    rw [show (macLogHandler n ((), msg)).run queried = macLogHandler n ((), msg) queried from rfl]
      at hstep
    simp only [macLogHandler, Functor.map_map, OracleComp.interpret_map, StateT.run_map,
      ProbOracleComp.interpret_query, PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hstep
    obtain ⟨⟨rawTag, nextCache'⟩, hlazy, hpair⟩ := hstep
    cases hpair
    obtain ⟨⟨rawAns, nextCache⟩, hlazy, hpair0⟩ := hlazy
    cases hpair0
    intro x hx
    rw [List.mem_cons]
    unfold lazyRandomFunctionOracle randomFunctionQuery at hlazy
    by_cases hmsg : msg.length = n
    · simp only [hmsg, ↓reduceIte, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        StateT.run_map, PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hlazy
      obtain ⟨⟨v, nextCache₂⟩, hans, hpair2⟩ := hlazy
      cases hpair2
      dsimp only [StateT.run] at hans
      cases hcache : cache (BitString.ofList n msg) with
      | some v0 =>
        rw [RandomOracle.answer_of_some _ _ _ _ hcache] at hans
        simp only [PMF.mem_support_pure_iff, Prod.mk.injEq] at hans
        rcases hans with ⟨_, rfl⟩
        exact Or.inr (hstate x hx)
      | none =>
        rw [RandomOracle.answer_of_none _ _ _ hcache] at hans
        simp only [PMF.mem_support_map_iff] at hans
        obtain ⟨v1, _, hupd⟩ := hans
        have hnc : nextCache₂ = Function.update cache (BitString.ofList n msg) (some v1) :=
          (Prod.mk.inj hupd).2.symm
        subst hnc
        by_cases heq : x = BitString.ofList n msg
        · subst heq
          exact Or.inl (BitString.ofFn_ofList hmsg)
        · dsimp only at hx
          rw [Function.update_of_ne heq] at hx
          exact Or.inr (hstate x hx)
    · simp only [hmsg, ↓reduceIte, OracleComp.interpret_pure, StateT.run_pure,
        PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hlazy
      rcases hlazy with ⟨_, rfl⟩
      exact Or.inr (hstate x hx)
  have hstep_bound : ∀ item ∈ phase1.support,
      phase2 item true ≤ (1 : ℝ≥0∞) / 2 ^ n := by
    rintro ⟨⟨msg, tag⟩, queried, cache⟩ hmem
    have hcache_inv := hinv (msg, tag) (queried, cache) hmem
    dsimp only [phase2]
    by_cases hcond : ((msg.length == n) && !queried.contains msg) = true
    · simp only [hcond, ↓reduceIte]
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
      rcases hcond with ⟨hmsgLen, hnotContains⟩
      have hnotMem : msg ∉ queried := by
        intro hmem_q
        have htrue := List.contains_iff_mem.mpr hmem_q
        rw [hnotContains] at htrue
        contradiction
      have hnone : cache (BitString.ofList n msg) = none := by
        by_contra hsome
        exact hnotMem (BitString.ofFn_ofList hmsgLen ▸ hcache_inv _ hsome)
      simp only [Functor.map_map, OracleComp.interpret_map, StateT.run_map,
        ProbOracleComp.interpret_query, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
      unfold lazyRandomFunctionOracle randomFunctionQuery
      simp only [hmsgLen, ↓reduceIte, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        StateT.run_map, PMF.monad_map_eq_map, PMF.map_comp, Function.comp_def]
      dsimp only [StateT.run]
      rw [RandomOracle.answer_of_none _ _ _ hnone]
      simp only [PMF.map_comp, Function.comp_def]
      have htake : (fun x : BitString n => ((List.ofFn x).take n == tag)) =
          (fun x : BitString n => (List.ofFn x == tag)) := by
        funext x
        simp [List.take_of_length_le (List.length_ofFn (f := x)).le]
      rw [htake]
      exact uniformOfFintype_bitString_beq_true_le n tag
    · have hcondF : ((msg.length == n) && !queried.contains msg) = false :=
        Bool.eq_false_iff.mpr hcond
      simp only [hcondF, Bool.false_eq_true, ↓reduceIte, PMF.pure_apply, reduceCtorEq,
        zero_le]
  have htotal : (phase1.bind phase2) true ≤ (1 : ℝ≥0∞) / 2 ^ n := by
    rw [PMF.bind_apply]
    refine (ENNReal.tsum_le_tsum fun a => ?_).trans
      (PMF.tsum_mul_le_of_forall_le phase1 fun _ => le_rfl)
    by_cases ha : a ∈ phase1.support
    · exact mul_le_mul_right (hstep_bound a ha) _
    · simp [(phase1.apply_eq_zero_iff a).mpr ha]
  rw [hgame, Game.succProbability]
  have hne_top : (1 : ℝ≥0∞) / 2 ^ n ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.one_ne_top (by positivity)
  have hmono := ENNReal.toNNReal_mono hne_top htotal
  have hrhs : ((1 : ℝ≥0∞) / 2 ^ n).toNNReal = (1 : ℝ≥0) / 2 ^ n := by
    rw [ENNReal.toNNReal_div, ENNReal.toNNReal_one, ENNReal.toNNReal_pow, ENNReal.toNNReal_ofNat]
  rwa [hrhs] at hmono

private theorem unique_tag_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    ∀ n sk, sk ∈ (ProbComp.eval ((prfMAC family hpoly).keyGen n)).support →
      ∀ msg, msg.length = n → ∀ tag tag',
      (prfMAC family hpoly).verify sk msg tag = true →
      tag' ∈ (ProbComp.eval ((prfMAC family hpoly).sign sk msg)).support →
      tag' = tag := by
  intro n sk hsk msg hmsg tag tag' hver htag'
  dsimp [prfMAC] at hsk hver htag'
  rw [BitString.eval_sampleList] at hsk
  have hskLen : sk.length = n := BitString.length_of_mem_support_uniformList hsk
  simp only [Bool.and_eq_true, beq_iff_eq] at hver
  simp only [PMF.mem_support_pure_iff, prfOracle, hskLen, hmsg, ↓reduceIte] at htag'
  exact htag'.trans hver.2

/-- Because `prfMAC` is deterministic with a unique valid tag per `(sk, msg)`, its strong
fresh-pair `sufCmaGame` distribution is identical to its fresh-message `eufCmaGame`
distribution. -/
theorem eval_sufCmaGame_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval ((prfMAC family hpoly).sufCmaGame adversary n) =
      ProbComp.eval ((prfMAC family hpoly).eufCmaGame adversary n) :=
  (prfMAC family hpoly).eval_sufCmaGame_eq_eufCmaGame_of_unique_tag
    (unique_tag_prfMAC hpoly) adversary n

/-- For `prfMAC`, strong unforgeability (`SUFCMA`) and fresh-message unforgeability (`EUFCMA`)
coincide. -/
theorem sufCma_prfMAC_iff_eufCma
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits) :
    (prfMAC family hpoly).SUFCMA ↔ (prfMAC family hpoly).EUFCMA :=
  (prfMAC family hpoly).sufCma_iff_eufCma_of_unique_tag (unique_tag_prfMAC hpoly)

/-- Running `macToPrfDistinguisher adversary` in `prfRealGame family` produces the exact same
Boolean distribution as the strong SUF-CMA experiment for `prfMAC family`. -/
theorem eval_prfRealGame_macToPrfDistinguisher_eq_sufCmaGame
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (prfRealGame family (macToPrfDistinguisher adversary) n) =
      ProbComp.eval ((prfMAC family hpoly).sufCmaGame adversary n) := by
  rw [eval_sufCmaGame_prfMAC hpoly adversary n]
  exact eval_prfRealGame_macToPrfDistinguisher hpoly hlen adversary n

/-- **Quantitative PRF-to-MAC forgery bound** [Boneh and Shoup, Theorem 6.2][BonehShoup2023]:
for every adaptive MAC forger `adversary` and every security parameter `n`, the EUF-CMA forgery
probability against `prfMAC family` is at most the PRF distinguishing advantage of
`macToPrfDistinguisher adversary` plus `1 / 2 ^ n`. -/
theorem succProbability_eufCmaGame_prfMAC_le
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval ((prfMAC family hpoly).eufCmaGame adversary n)) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame family (macToPrfDistinguisher adversary) n))
        (ProbComp.eval (prfIdealGame (macToPrfDistinguisher adversary) n)) +
      (1 : ℝ≥0) / 2 ^ n := by
  rw [← eval_prfRealGame_macToPrfDistinguisher hpoly hlen adversary n]
  have htri := Game.advantage_triangle
    (ProbComp.eval (prfRealGame family (macToPrfDistinguisher adversary) n))
    (ProbComp.eval (prfIdealGame (macToPrfDistinguisher adversary) n))
    (PMF.pure false)
  simp only [Game.advantage_pure_false] at htri
  exact htri.trans (add_le_add_right
    (succProbability_prfIdealGame_macToPrfDistinguisher_le adversary n) _)

/-- **Quantitative PRF-to-SUF-CMA forgery bound** [Boneh and Shoup, Theorem 6.2][BonehShoup2023]:
for every adaptive MAC forger `adversary` and every security parameter `n`, the strong SUF-CMA
forgery probability against `prfMAC family` is at most the PRF distinguishing advantage of
`macToPrfDistinguisher adversary` plus `1 / 2 ^ n`. -/
theorem succProbability_sufCmaGame_prfMAC_le
    {family : List Bool → List Bool → List Bool}
    (hpoly : ComputableInPolyTime (fun pair : List Bool × List Bool => family pair.1 pair.2)
      (encPair encBits encBits) encBits)
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : Forger) (n : ℕ) :
    Game.succProbability (ProbComp.eval ((prfMAC family hpoly).sufCmaGame adversary n)) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame family (macToPrfDistinguisher adversary) n))
        (ProbComp.eval (prfIdealGame (macToPrfDistinguisher adversary) n)) +
      (1 : ℝ≥0) / 2 ^ n := by
  rw [eval_sufCmaGame_prfMAC hpoly adversary n]
  exact succProbability_eufCmaGame_prfMAC_le hpoly hlen adversary n

/-- **PRF-to-MAC security theorem** [Boneh and Shoup, Theorem 6.2][BonehShoup2023]:
every uniform `PseudorandomFunction` yields an `EUFCMA`-secure `MACScheme`. -/
theorem PseudorandomFunction.eufCma_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) :
    (prfMAC family hprf.polyTime).EUFCMA := by
  apply MACScheme.EUFCMA.of_negligible
  intro adversary hadversary
  have hdist := hprf.secure (macToPrfDistinguisher adversary)
    (isOraclePPT_macToPrfDistinguisher hadversary)
  have hgeom : Negligible (fun n => (1 : ℝ≥0) / 2 ^ n) := by
    simpa only [one_div, inv_pow] using
      negligible_geometric (ratio := (1 / 2 : ℝ≥0)) (by norm_num)
  exact negligible_of_le (hdist.add hgeom)
    (succProbability_eufCmaGame_prfMAC_le hprf.polyTime hprf.length_eq adversary)

/-- **PRF-to-SUF-CMA security theorem** [Boneh and Shoup, Theorem 6.2][BonehShoup2023]:
every uniform `PseudorandomFunction` yields a strongly unforgeable (`SUFCMA`) `MACScheme`. -/
theorem PseudorandomFunction.sufCma_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) :
    (prfMAC family hprf.polyTime).SUFCMA :=
  (sufCma_prfMAC_iff_eufCma hprf.polyTime).mpr hprf.eufCma_prfMAC

/-- Every uniform `PseudorandomFunction` also yields a `OneTimeEUFCMA`-secure `MACScheme`. -/
theorem PseudorandomFunction.oneTimeEUFCMA_prfMAC
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family) :
    (prfMAC family hprf.polyTime).OneTimeEUFCMA :=
  hprf.eufCma_prfMAC.oneTimeEUFCMA

/-! ### Nonce-based message authentication codes (`NonceMACScheme`, Boneh–Shoup Section 7.5) -/

/-- An adaptive nonce-based MAC forger receives a unary security parameter and an auxiliary word,
queries a nonce-respecting tagging oracle on encoded `(message, nonce)` pairs
(`encPair encBits encBits (msg, nonce)`), and outputs a candidate `((message, nonce), tag)` triple
([Boneh and Shoup, Section 7.5, Attack Game 7.4][BonehShoup2023]). -/
abbrev NonceMACForger :=
  ℕ → List Bool → WordOracleComp Unit ((List Bool × List Bool) × List Bool)

/-- A uniform symmetric nonce-based message authentication code (`NonceMACScheme`) on `msgLen n`-bit
messages and `nonceLen n`-bit nonces at security parameter `n` (both defaulting to `n`), with plain
polynomial-time length schedules, strict polynomial-time key generation and tag generation,
deterministic polynomial-time verification, and perfect completeness on supported keys,
`msgLen n`-bit messages, `nonceLen n`-bit nonces, and tags
([Boneh and Shoup, Section 7.5, Attack Game 7.4][BonehShoup2023]). -/
structure NonceMACScheme where
  /-- Message length authenticated at unary security parameter `n` (defaults to `n`). -/
  msgLen : ℕ → ℕ := fun n => n
  /-- The message-length schedule is computable in plain polynomial time in unary. -/
  msgLen_polyTime : ComputableInPolyTime msgLen encUnary encUnary := by
    exact ComputableInPolyTime.id'
  /-- Nonce length required at unary security parameter `n` (defaults to `n`). -/
  nonceLen : ℕ → ℕ := fun n => n
  /-- The nonce-length schedule is computable in plain polynomial time in unary. -/
  nonceLen_polyTime : ComputableInPolyTime nonceLen encUnary encUnary := by
    exact ComputableInPolyTime.id'
  /-- Sample a secret MAC key `sk` at unary security parameter `n`. -/
  keyGen : ℕ → ProbComp (List Bool)
  /-- Compute a MAC tag on message `msg` and nonce `nonce` using the secret key `sk`. -/
  sign : List Bool → List Bool → List Bool → ProbComp (List Bool)
  /-- Deterministically verify a candidate `tag` on `(msg, nonce)` under secret key `sk`. -/
  verify : List Bool → List Bool → List Bool → List Bool → Bool
  /-- Key generation is uniformly strict PPT in the unary security parameter. -/
  keyGen_ppt : IsPPTOn encUnary encBits keyGen
  /-- Tag generation is uniformly strict PPT in the encoded `(sk, msg, nonce)`. -/
  sign_ppt : IsPPTOn (encPair encBits (encPair encBits encBits)) encBits
    (fun p => sign p.1 p.2.1 p.2.2)
  /-- Verification is computable in plain polynomial time on `(sk, msg, nonce, tag)`. -/
  verify_polyTime : ComputableInPolyTime
    (fun p : List Bool × List Bool × List Bool × List Bool => verify p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encBits (encPair encBits (encPair encBits encBits))) encBool
  /-- Every tag produced by `sign` on a `msgLen n`-bit message and `nonceLen n`-bit nonce under a
  supported secret key at security parameter `n` is accepted by `verify`. -/
  verify_sign : ∀ n sk, sk ∈ (ProbComp.eval (keyGen n)).support →
    ∀ msg, msg.length = msgLen n →
    ∀ nonce, nonce.length = nonceLen n →
    ∀ tag, tag ∈ (ProbComp.eval (sign sk msg nonce)).support →
    verify sk msg nonce tag = true

/-- Deciding `List.Nodup` on a framed list of bit strings is computable tidily in polynomial time.
-/
@[local fun_prop]
private theorem computableTidilyInPolyTime_decide_nodup {γ : Type} {encIn : γ ↪ List Bool}
    {list : γ → List (List Bool)}
    (hlist : ComputableTidilyInPolyTime list encIn (encList encBits)) :
    ComputableTidilyInPolyTime (fun a => decide (list a).Nodup) encIn encBool := by
  have heq : (fun a => decide (list a).Nodup) =
      (fun a => (list a).all (fun x => (list a).count x == 1)) := by
    funext a
    rw [Bool.eq_iff_iff, decide_eq_true_eq, List.all_eq_true, List.nodup_iff_count_le_one]
    simp only [beq_iff_eq]
    refine ⟨fun h x hx => ?_, fun h x => ?_⟩
    · have hle := h x
      have hpos := List.count_pos_iff.mpr hx
      omega
    · by_cases hx : x ∈ list a
      · exact (h x hx).le
      · simp [List.count_eq_zero.mpr hx]
  rw [heq]
  exact ComputableTidilyInPolyTime.allWithInput (test := fun a x => (list a).count x == 1)
    hlist (by polytime)

/-- The unframed prefix and remaining suffix of any bit list satisfy
`2 * (unframe v).length + (dropFrame v).length ≤ v.length`. -/
private theorem length_unframe_add_dropFrame_le :
    ∀ v : List Bool, 2 * (unframe v).length + (dropFrame v).length ≤ v.length
  | [] | [true] => by simp [unframe, dropFrame]
  | false :: v => by simp [unframe, dropFrame]
  | true :: b :: v => by
    have ih := length_unframe_add_dropFrame_le v
    simp only [unframe, dropFrame, List.length_cons]
    omega

namespace NonceMACScheme

attribute [program_certificate]
  msgLen_polyTime nonceLen_polyTime keyGen_ppt sign_ppt verify_polyTime

@[local fun_prop]
private theorem computableTidilyInPolyTime_msgLen_comp (M : NonceMACScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ}
    (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    ComputableTidilyInPolyTime (fun a => M.msgLen (n a)) encIn encUnary :=
  M.msgLen_polyTime.tidy.comp hn

/-- Composing `M.msgLen` with a plain polynomial-time unary parameter function is plain
polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_msgLen_comp (M : NonceMACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun a => M.msgLen (n a)) encIn encUnary :=
  M.msgLen_polyTime.comp hn

@[local fun_prop]
private theorem computableTidilyInPolyTime_nonceLen_comp (M : NonceMACScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {n : γ → ℕ}
    (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    ComputableTidilyInPolyTime (fun a => M.nonceLen (n a)) encIn encUnary :=
  M.nonceLen_polyTime.tidy.comp hn

/-- Composing `M.nonceLen` with a plain polynomial-time unary parameter function is plain
polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_nonceLen_comp (M : NonceMACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun a => M.nonceLen (n a)) encIn encUnary :=
  M.nonceLen_polyTime.comp hn

@[local fun_prop]
private theorem isPPTOn_keyGen_comp_tidy (M : NonceMACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableTidilyInPolyTime n encIn encUnary) :
    IsPPTOn encIn encBits (fun a => M.keyGen (n a)) :=
  M.keyGen_ppt.preprocess (ComputableInPolyTime.of_tidy hn)

/-- Composing `M.keyGen` with a plain polynomial-time unary parameter function is strict PPT. -/
@[program_certificate]
theorem isPPTOn_keyGen_comp (M : NonceMACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {n : γ → ℕ} (hn : ComputableInPolyTime n encIn encUnary) :
    IsPPTOn encIn encBits (fun a => M.keyGen (n a)) :=
  M.keyGen_ppt.preprocess hn

@[local fun_prop]
private theorem isPPTOn_sign_comp_tidy (M : NonceMACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {sk msg nonce : γ → List Bool}
    (hsk : ComputableTidilyInPolyTime sk encIn encBits)
    (hmsg : ComputableTidilyInPolyTime msg encIn encBits)
    (hnonce : ComputableTidilyInPolyTime nonce encIn encBits) :
    IsPPTOn encIn encBits (fun a => M.sign (sk a) (msg a) (nonce a)) :=
  M.sign_ppt.preprocess (ComputableInPolyTime.of_tidy (hsk.prod (hmsg.prod hnonce)))

/-- Composing `M.sign` with plain polynomial-time key, message, and nonce selectors is strict
PPT. -/
@[program_certificate]
theorem isPPTOn_sign_comp (M : NonceMACScheme) {γ : Type} {encIn : γ ↪ List Bool}
    {sk msg nonce : γ → List Bool}
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits)
    (hnonce : ComputableInPolyTime nonce encIn encBits) :
    IsPPTOn encIn encBits (fun a => M.sign (sk a) (msg a) (nonce a)) :=
  M.sign_ppt.preprocess (hsk.prod (hmsg.prod hnonce))

@[local fun_prop]
private theorem computableTidilyInPolyTime_verify_comp (M : NonceMACScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {sk msg nonce tag : γ → List Bool}
    (hsk : ComputableTidilyInPolyTime sk encIn encBits)
    (hmsg : ComputableTidilyInPolyTime msg encIn encBits)
    (hnonce : ComputableTidilyInPolyTime nonce encIn encBits)
    (htag : ComputableTidilyInPolyTime tag encIn encBits) :
    ComputableTidilyInPolyTime
      (fun a => M.verify (sk a) (msg a) (nonce a) (tag a)) encIn encBool :=
  M.verify_polyTime.tidy.comp (hsk.prod (hmsg.prod (hnonce.prod htag)))

/-- Composing `M.verify` with plain polynomial-time key, message, nonce, and tag selectors is plain
polynomial-time. -/
@[program_certificate]
theorem computableInPolyTime_verify_comp (M : NonceMACScheme)
    {γ : Type} {encIn : γ ↪ List Bool} {sk msg nonce tag : γ → List Bool}
    (hsk : ComputableInPolyTime sk encIn encBits)
    (hmsg : ComputableInPolyTime msg encIn encBits)
    (hnonce : ComputableInPolyTime nonce encIn encBits)
    (htag : ComputableInPolyTime tag encIn encBits) :
    ComputableInPolyTime
      (fun a => M.verify (sk a) (msg a) (nonce a) (tag a)) encIn encBool :=
  M.verify_polyTime.comp (hsk.prod (hmsg.prod (hnonce.prod htag)))

/-- Stateful nonce-based MAC tagging oracle that decodes `(msg, nonce)` from the framed query word
`request.2`, tags `(msg, nonce)` under `sk`, and prepends the returned `((msg, nonce), tag)` triple
to the transcript ([Boneh and Shoup, Section 7.5, Attack Game 7.4][BonehShoup2023]). -/
noncomputable def signingPairOracle (M : NonceMACScheme) (sk : List Bool)
    (request : Unit × List Bool) :
    StateT (List ((List Bool × List Bool) × List Bool)) ProbComp (List Bool) :=
  fun queriedTriples => do
    let msg := unframe request.2
    let nonce := dropFrame request.2
    let tag ← M.sign sk msg nonce
    return (tag, ((msg, nonce), tag) :: queriedTriples)

/-- The strong nonce-based MAC SUF-CMA experiment
([Boneh and Shoup, Section 7.5, Attack Game 7.4][BonehShoup2023]): sample `sk ← M.keyGen n`, run
the adaptive forger on `(n, [])` with oracle access to `M.signingPairOracle sk`, and accept when:
1. the candidate message has length `M.msgLen n` and the candidate nonce has length `M.nonceLen n`,
2. all nonces queried during the signing phase are pairwise distinct
   (`decide (out.2.map (fun e => e.1.2)).Nodup`),
3. the candidate `((msg, nonce), tag)` triple was never returned by the tagging oracle
   (`!out.2.contains out.1`), and
4. `M.verify sk msg nonce tag = true`. -/
noncomputable def sufCmaGame (M : NonceMACScheme) (adversary : NonceMACForger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.signingPairOracle sk)) (adversary n [])).run []
  return (out.1.1.1.length == M.msgLen n) && (out.1.1.2.length == M.nonceLen n) &&
    decide (out.2.map (fun e => e.1.2)).Nodup && !out.2.contains out.1 &&
    M.verify sk out.1.1.1 out.1.1.2 out.1.2

/-- The fresh-message nonce-based MAC EUF-CMA experiment: identical to `sufCmaGame` except that the
candidate message `out.1.1.1` must never have been queried during the signing phase
(`!(out.2.map (fun e => e.1.1)).contains out.1.1.1`). -/
noncomputable def eufCmaGame (M : NonceMACScheme) (adversary : NonceMACForger) (n : ℕ) :
    ProbComp Bool := do
  let sk ← M.keyGen n
  let out ← (OracleComp.interpret
    (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
      (M.signingPairOracle sk)) (adversary n [])).run []
  return (out.1.1.1.length == M.msgLen n) && (out.1.1.2.length == M.nonceLen n) &&
    decide (out.2.map (fun e => e.1.2)).Nodup &&
    !(out.2.map (fun e => e.1.1)).contains out.1.1.1 &&
    M.verify sk out.1.1.1 out.1.1.2 out.1.2

/-- Running an oracle-PPT nonce-MAC forger against `signingPairOracle` is uniformly strict PPT in
the unary security parameter and secret key. -/
@[program_certificate]
theorem isPPTOn_run_signingPairOracle (M : NonceMACScheme) {adversary : NonceMACForger}
    (hadversary : IsOraclePPT (encPair (encPair encBits encBits) encBits) adversary) :
    IsPPTOn (encPair encUnary encBits)
      (encPair (encPair (encPair encBits encBits) encBits)
        (encList (encPair (encPair encBits encBits) encBits)))
      (fun caller : ℕ × List Bool =>
        (OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.signingPairOracle caller.2)) (adversary caller.1 [])).run []) := by
  obtain ⟨c, d, hlen⟩ := M.sign_ppt.length_le
  have hhandler : IsPPTOn
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encFinite Unit) encBits)
          (encList (encPair (encPair encBits encBits) encBits))))
      (encPair encBits (encList (encPair (encPair encBits encBits) encBits)))
      (fun pair : (ℕ × List Bool) ×
          ((Unit × List Bool) × List ((List Bool × List Bool) × List Bool)) =>
        M.signingPairOracle pair.1.2 pair.2.1 pair.2.2) := by
    unfold signingPairOracle
    ppt
  apply hadversary.run_interpret_preprocess
    (prepare := fun caller : ℕ × List Bool => (caller.1, ([] : List Bool)))
    (initial := fun _ => ([] : List ((List Bool × List Bool) × List Bool)))
    (resources := fun caller query =>
      2 * (c * (2 * caller.2.length + query.length + 3) ^ d) + 4 * query.length + 8)
    (by fun_prop) hhandler (by fun_prop)
    (fun _ _ => True) (fun _ => trivial) (by fun_prop)
  intro caller request queriedTriples _ result hresult
  simp only [signingPairOracle, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hresult
  obtain ⟨tag, htag, rfl⟩ := hresult
  have htagLen := hlen (caller.2, unframe request.2, dropFrame request.2) tag htag
  simp only [encBits_apply, length_encPair] at htagLen
  have hframe := length_unframe_add_dropFrame_le request.2
  have hbase : 2 * caller.2.length + 1 +
      (2 * (unframe request.2).length + 1 + (dropFrame request.2).length) + 1 ≤
      2 * caller.2.length + request.2.length + 3 := by omega
  have hpow : c * (2 * caller.2.length + 1 +
      (2 * (unframe request.2).length + 1 + (dropFrame request.2).length) + 1) ^ d ≤
      c * (2 * caller.2.length + request.2.length + 3) ^ d :=
    Nat.mul_le_mul_left c (Nat.pow_le_pow_left hbase d)
  have htag_le : tag.length ≤ c * (2 * caller.2.length + request.2.length + 3) ^ d :=
    htagLen.trans hpow
  refine ⟨trivial, by dsimp only; omega, ?_⟩
  simp only [encList_cons, List.length_append, length_frame, length_encPair, encBits_apply]
  omega

/-- Run the complete nonce-based MAC SUF-CMA experiment on its unary security parameter for any
oracle-PPT forger. -/
@[program_certificate]
theorem isPPTOn_sufCmaGame (M : NonceMACScheme) {adversary : NonceMACForger}
    (hadversary : IsOraclePPT (encPair (encPair encBits encBits) encBits) adversary) :
    IsPPTOn encUnary encBool (M.sufCmaGame adversary) := by
  have hrun := M.isPPTOn_run_signingPairOracle hadversary
  have hpost : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) ×
          (((List Bool × List Bool) × List Bool) × List ((List Bool × List Bool) × List Bool)) =>
        (pair.2.1.1.1.length == M.msgLen pair.1.1) &&
          (pair.2.1.1.2.length == M.nonceLen pair.1.1) &&
          decide (pair.2.2.map (fun e => e.1.2)).Nodup &&
          !pair.2.2.contains pair.2.1 &&
          M.verify pair.1.2 pair.2.1.1.1 pair.2.1.1.2 pair.2.1.2)
      (encPair (encPair encUnary encBits)
        (encPair (encPair (encPair encBits encBits) encBits)
          (encList (encPair (encPair encBits encBits) encBits)))) encBool := by
    polytime
  exact M.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-- The nonce-based MAC SUF-CMA experiment is uniformly strict PPT, independently of unused
auxiliary input. -/
@[program_certificate]
theorem isPPT_sufCmaGame (M : NonceMACScheme) {adversary : NonceMACForger}
    (hadversary : IsOraclePPT (encPair (encPair encBits encBits) encBits) adversary) :
    IsPPT encBool (fun n _ => M.sufCmaGame adversary n) :=
  ((M.isPPTOn_sufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Run the complete nonce-based MAC EUF-CMA experiment on its unary security parameter for any
oracle-PPT forger. -/
@[program_certificate]
theorem isPPTOn_eufCmaGame (M : NonceMACScheme) {adversary : NonceMACForger}
    (hadversary : IsOraclePPT (encPair (encPair encBits encBits) encBits) adversary) :
    IsPPTOn encUnary encBool (M.eufCmaGame adversary) := by
  have hrun := M.isPPTOn_run_signingPairOracle hadversary
  let EIn := encPair (encPair encUnary encBits)
    (encPair (encPair (encPair encBits encBits) encBits)
      (encList (encPair (encPair encBits encBits) encBits)))
  have hmsgs : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) ×
          (((List Bool × List Bool) × List Bool) × List ((List Bool × List Bool) × List Bool)) =>
        pair.2.2.map (fun e => e.1.1))
      EIn (encList encBits) := by
    dsimp only [EIn]; fun_prop
  have hmsg : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) ×
          (((List Bool × List Bool) × List Bool) × List ((List Bool × List Bool) × List Bool)) =>
        pair.2.1.1.1)
      EIn encBits := by
    dsimp only [EIn]; fun_prop
  have hcontains : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) ×
          (((List Bool × List Bool) × List Bool) × List ((List Bool × List Bool) × List Bool)) =>
        (pair.2.2.map (fun e => e.1.1)).contains pair.2.1.1.1)
      EIn encBool :=
    computableTidilyInPolyTime_contains hmsgs hmsg
  have hprefix : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) ×
          (((List Bool × List Bool) × List Bool) × List ((List Bool × List Bool) × List Bool)) =>
        (pair.2.1.1.1.length == M.msgLen pair.1.1) &&
          (pair.2.1.1.2.length == M.nonceLen pair.1.1) &&
          decide (pair.2.2.map (fun e => e.1.2)).Nodup)
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hver : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) ×
          (((List Bool × List Bool) × List Bool) × List ((List Bool × List Bool) × List Bool)) =>
        M.verify pair.1.2 pair.2.1.1.1 pair.2.1.1.2 pair.2.1.2)
      EIn encBool := by
    dsimp only [EIn]; polytime
  have hpost : ComputableTidilyInPolyTime
      (fun pair : (ℕ × List Bool) ×
          (((List Bool × List Bool) × List Bool) × List ((List Bool × List Bool) × List Bool)) =>
        (pair.2.1.1.1.length == M.msgLen pair.1.1) &&
          (pair.2.1.1.2.length == M.nonceLen pair.1.1) &&
          decide (pair.2.2.map (fun e => e.1.2)).Nodup &&
          !(pair.2.2.map (fun e => e.1.1)).contains pair.2.1.1.1 &&
          M.verify pair.1.2 pair.2.1.1.1 pair.2.1.1.2 pair.2.1.2)
      EIn encBool :=
    ComputableTidilyInPolyTime.bool_and.comp
      ((ComputableTidilyInPolyTime.bool_and.comp
        (hprefix.prod (ComputableTidilyInPolyTime.bool_not.comp hcontains))).prod hver)
  exact M.keyGen_ppt.bind_with (hrun.bind_with hpost.isPPTOn)

/-- The nonce-based MAC EUF-CMA experiment is uniformly strict PPT, independently of unused
auxiliary input. -/
@[program_certificate]
theorem isPPT_eufCmaGame (M : NonceMACScheme) {adversary : NonceMACForger}
    (hadversary : IsOraclePPT (encPair (encPair encBits encBits) encBits) adversary) :
    IsPPT encBool (fun n _ => M.eufCmaGame adversary n) :=
  ((M.isPPTOn_eufCmaGame hadversary).preprocess (ComputableInPolyTime.fst _ _)).isPPT

/-- Strong existential unforgeability under nonce-respecting adaptive chosen-message attack
(`SUFCMA`) for a `NonceMACScheme` against uniform strict oracle-PPT adversaries
([Boneh and Shoup, Section 7.5, Attack Game 7.4][BonehShoup2023]). -/
def SUFCMA (M : NonceMACScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.sufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair (encPair encBits encBits) encBits))

/-- Strong nonce-based unforgeability gives negligible SUF-CMA forgery probability for every
oracle-PPT forger. -/
theorem SUFCMA.negligible {M : NonceMACScheme} (h : M.SUFCMA)
    (adversary : NonceMACForger)
    (hadversary : IsOraclePPT (encPair (encPair encBits encBits) encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish nonce-based SUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem SUFCMA.of_negligible {M : NonceMACScheme}
    (h : ∀ adversary, IsOraclePPT (encPair (encPair encBits encBits) encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n)))) :
    M.SUFCMA := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Fresh-message existential unforgeability under nonce-respecting adaptive chosen-message attack
(`EUFCMA`) for a `NonceMACScheme` against uniform strict oracle-PPT adversaries. -/
def EUFCMA (M : NonceMACScheme) : Prop :=
  Game.Indistinguishable
    (fun adversary n => ProbComp.eval (M.eufCmaGame adversary n))
    (fun _ _ => PMF.pure false)
    (IsOraclePPT (encPair (encPair encBits encBits) encBits))

/-- Nonce-based EUF-CMA security gives negligible forgery probability for every oracle-PPT
forger. -/
theorem EUFCMA.negligible {M : NonceMACScheme} (h : M.EUFCMA)
    (adversary : NonceMACForger)
    (hadversary : IsOraclePPT (encPair (encPair encBits encBits) encBits) adversary) :
    Negligible (fun n => Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n))) := by
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- Establish nonce-based EUF-CMA security by bounding every oracle-PPT forger's success
probability. -/
theorem EUFCMA.of_negligible {M : NonceMACScheme}
    (h : ∀ adversary, IsOraclePPT (encPair (encPair encBits encBits) encBits) adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)))) :
    M.EUFCMA := by
  intro adversary hadversary
  simpa only [Game.advantage_pure_false] using h adversary hadversary

/-- **Quantitative EUF-CMA vs. SUF-CMA bound for `NonceMACScheme`**: for every `NonceMACScheme`,
adaptive forger, and security parameter `n`, the fresh-message `eufCmaGame` forgery probability is
at most the strong fresh-triple `sufCmaGame` forgery probability. -/
theorem succProbability_eufCmaGame_le_sufCmaGame (M : NonceMACScheme)
    (adversary : NonceMACForger) (n : ℕ) :
    Game.succProbability (ProbComp.eval (M.eufCmaGame adversary n)) ≤
      Game.succProbability (ProbComp.eval (M.sufCmaGame adversary n)) := by
  simp only [Game.succProbability, eufCmaGame, sufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ true) ?_
  rw [PMF.bind_apply, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun sk => ?_
  refine mul_le_mul_of_nonneg_left
    (MACScheme.pmf_bind_pure_bool_le _ _ _ fun out _ hout => ?_) zero_le
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hout ⊢
  refine ⟨⟨ hout.1.1, ?_ ⟩, hout.2⟩
  rw [Bool.eq_false_iff]
  intro hmemTriple
  have hmemMsg : out.1.1.1 ∈ out.2.map (fun e => e.1.1) :=
    List.mem_map_of_mem (f := fun e : (List Bool × List Bool) × List Bool => e.1.1)
      (List.contains_iff_mem.mp hmemTriple)
  have hcontainsMsg : (out.2.map (fun e => e.1.1)).contains out.1.1.1 = true :=
    List.contains_iff_mem.mpr hmemMsg
  rw [hout.1.2] at hcontainsMsg
  contradiction

/-- Strong unforgeability (`SUFCMA`) implies fresh-message unforgeability (`EUFCMA`) for every
`NonceMACScheme`. -/
theorem SUFCMA.eufCma {M : NonceMACScheme} (h : M.SUFCMA) : M.EUFCMA := by
  apply EUFCMA.of_negligible
  intro adversary hadversary
  exact negligible_of_le (h.negligible adversary hadversary)
    (M.succProbability_eufCmaGame_le_sufCmaGame adversary)

private theorem mem_support_signingPairOracle (M : NonceMACScheme) (sk : List Bool)
    (prog : WordOracleComp Unit ((List Bool × List Bool) × List Bool))
    (result : (List Bool × List Bool) × List Bool)
    (queriedTriples : List ((List Bool × List Bool) × List Bool))
    (hmem : (result, queriedTriples) ∈ (ProbComp.eval ((OracleComp.interpret
      (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
        (M.signingPairOracle sk)) prog).run [])).support) :
    ∀ triple ∈ queriedTriples,
      triple.2 ∈ (ProbComp.eval (M.sign sk triple.1.1 triple.1.2)).support := by
  rw [ProbOracleComp.eval_run_interpret] at hmem
  refine ProbOracleComp.run_interpret_invariant
    (fun q s => ProbComp.eval (M.signingPairOracle sk q s))
    (fun s => ∀ triple ∈ s,
      triple.2 ∈ (ProbComp.eval (M.sign sk triple.1.1 triple.1.2)).support)
    ?_ prog [] (by simp) result queriedTriples hmem
  intro ⟨⟨⟩, raw⟩ s hs a s' hstep triple htriple
  simp only [signingPairOracle, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hstep
  obtain ⟨tag, htag, htripleEq⟩ := hstep
  cases htripleEq
  rw [List.mem_cons] at htriple
  rcases htriple with rfl | htail
  · exact htag
  · exact hs triple htail

/-- For any `NonceMACScheme` whose valid tags on `M.msgLen n`-bit messages and `M.nonceLen n`-bit
nonces under supported secret keys agree with every tag in the support of `M.sign`, strong
triple-freshness (`!out.2.contains out.1`) in `sufCmaGame` is identical to `(msg, nonce)`-pair
freshness (`!(out.2.map Prod.fst).contains out.1.1`). -/
theorem eval_sufCmaGame_eq_freshPair_of_unique_tag (M : NonceMACScheme)
    (huniq : ∀ n sk, sk ∈ (ProbComp.eval (M.keyGen n)).support →
      ∀ msg, msg.length = M.msgLen n →
      ∀ nonce, nonce.length = M.nonceLen n → ∀ tag tag',
      M.verify sk msg nonce tag = true →
      tag' ∈ (ProbComp.eval (M.sign sk msg nonce)).support → tag' = tag)
    (adversary : NonceMACForger) (n : ℕ) :
    ProbComp.eval (M.sufCmaGame adversary n) =
      ProbComp.eval (do
        let sk ← M.keyGen n
        let out ← (OracleComp.interpret
          (ProbOracleComp.handler (fun k => StateT.lift (ProbComp.unifFin k))
            (M.signingPairOracle sk)) (adversary n [])).run []
        return (out.1.1.1.length == M.msgLen n) && (out.1.1.2.length == M.nonceLen n) &&
          decide (out.2.map (fun e => e.1.2)).Nodup &&
          !(out.2.map Prod.fst).contains out.1.1 &&
          M.verify sk out.1.1.1 out.1.1.2 out.1.2) := by
  simp only [sufCmaGame, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_congr_on_support _ _ _ fun sk hsk => ?_
  refine PMF.bind_congr_on_support _ _ _ fun ⟨⟨⟨msg, nonce⟩, tag⟩, queriedTriples⟩ hout => ?_
  have hinv := M.mem_support_signingPairOracle sk (adversary n [])
    ((msg, nonce), tag) queriedTriples hout
  congr 1
  by_cases hmsg : (msg.length == M.msgLen n) = true
  · by_cases hnonce : (nonce.length == M.nonceLen n) = true
    · by_cases hver : M.verify sk msg nonce tag = true
      · have hmsgLen : msg.length = M.msgLen n := beq_iff_eq.mp hmsg
        have hnonceLen : nonce.length = M.nonceLen n := beq_iff_eq.mp hnonce
        have hmem_iff : ((msg, nonce), tag) ∈ queriedTriples ↔
            (msg, nonce) ∈ queriedTriples.map Prod.fst := by
          rw [List.mem_map]
          refine ⟨fun h => ⟨((msg, nonce), tag), h, rfl⟩, ?_⟩
          rintro ⟨⟨⟨qmsg, qnonce⟩, qtag⟩, hmemTriple, hpair_eq⟩
          cases hpair_eq
          have hqtag := hinv ((msg, nonce), qtag) hmemTriple
          have heq := huniq n sk hsk msg hmsgLen nonce hnonceLen tag qtag hver hqtag
          subst heq
          exact hmemTriple
        simp only [hmsg, hnonce, hver, Bool.true_and, Bool.and_true, List.contains_eq_mem,
          decide_eq_decide.mpr hmem_iff]
      · simp [Bool.eq_false_iff.mpr hver]
    · simp [Bool.eq_false_iff.mpr hnonce]
  · simp [Bool.eq_false_iff.mpr hmsg]

end NonceMACScheme

end Cslib.Crypto
