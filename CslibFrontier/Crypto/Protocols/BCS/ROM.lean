/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.Basic
public import CslibFrontier.Crypto.Computational.Kilian.Micali
public import CslibFrontier.Crypto.Computational.MerkleTree.ROMExtract
public import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformBound
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Soundness and straight-line knowledge soundness of the BCS transform in the random-oracle model

This module lifts the multi-round Ben-Sasson–Chiesa–Spooner (BCS) transformation
(`CslibFrontier/Crypto/Protocols/BCS/Basic.lean`) to an explicit two-channel random-oracle model
([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024], Construction 25.1.1, Remark 25.1.3, and
Theorem 25.2.1, printed pp. 274–278, Theorem 26.1.1 and Construction 26.1.3, printed pp. 288–289,
Chapter 31, Definitions 31.1.1–31.1.2, Definition 31.1.6, Construction 31.1.8, Theorem 31.2.1, and
Theorem 31.3.1, composed with Merkle trace extraction from Chapter 18, Construction 18.5.3 and
Lemma 18.5.7, printed pp. 199 and 207) and proves unconditional adaptive soundness and straight-line
knowledge soundness bounds:

1. **Straight-line multi-round oracle-table reconstruction (`bcsExtractTable`, `bcsExtractOracles`,
   `bcsExtractWitness`).** Given a symbol decoder `decSym : List Bool → Sym` with
   `Function.LeftInverse decSym encSym`, a default symbol `defaultSym : Sym`, and a recorded Merkle
   query-answer trace `tr_MT : List (List Bool × List Bool)`, `bcsExtractTable` reconstructs the
   depth-`d` oracle table committed under any Merkle root `rt` via `extractLeafFromTrace` without
   rewinding, and `bcsExtractOracles` reconstructs all `r` round tables of a `BCSProof`. When
   `tr_MT` is collision-free and records every opened authentication path of an accepted proof,
   `iopVerify` accepts the extracted oracle tables (`iopVerify_bcsExtractOracles_of_bcsVerify`);
   conversely, if `iopVerify` rejects the extracted tables on a trace consistent with `H k`,
   `tr_MT` contains an explicit hash collision
   (`exists_collision_of_bcsVerify_of_iopVerify_eq_false`). Prepending a fresh Merkle query-answer
   pair `(q, ans)` leaves `bcsExtractTable` and `bcsExtractOracles` unchanged unless `ans` hits a
   target root or a child of an existing Merkle query (`bcsExtractTable_cons_of_ne`,
   `bcsExtractOracles_cons_of_ne`).
2. **Two-channel BCS random-oracle model & completeness (`BCSROMSpec`, `chainedFS`, `bcsProveROM`,
   `bcsVerifyROM`, `bcsHonestROMGame_eq_pure_true`).** Over `BCSROMSpec Stmt Chal :=
   MerkleHashSpec ⊕ₒ BCSFSSpec Stmt Chal`, the left channel (`Sum.inl`) answers Merkle hash queries
   lazily with uniform `σ`-bit digests (`BitString.uniformList σ`), while the right channel
   (`Sum.inr`) answers transcript-chained Fiat–Shamir queries `(x, rts, prevChals) ↦ Chal` lazily
   with `PMF.uniformOfFintype Chal`: in round `j`, the prover and verifier query
   `(x, rootPrefix roots j, [c_0, ..., c_{j-1}]) ↦ c_j`. Under any deterministic oracle pair
   `(hTree, f)`, `bcsProveROM` and `bcsVerifyROM` agree via `OracleComp.evalPure` with `bcsProve`
   and `bcsVerify` instantiated with `chainedFS f`, yielding perfect completeness in the lazy
   two-channel ROM (`bcsHonestROMGame_eq_pure_true`).
3. **Adaptive two-channel ROM soundness (`bcsROMSoundness_bound`,
   `bcsROMSoundness_bound_of_prover_verifier`).** Given `IOPRoundByRoundSoundness iop lang doomed
   goodStep` with per-round escape probability `≤ ε_rbr` under `PMF.uniformOfFintype Chal`, the
   combined state invariant `BCSGoodState` requires `TraceCollisionFree tr_MT` together with
   `BCSChainDoomed`: every recorded Fiat–Shamir chain `(rts, chals)` of length `≤ r` for `x ∉ lang`
   maps under `bcsExtractTranscript` to a doomed IOP transcript prefix. Restricting the Merkle
   forbidden-digest guard (`bcsForbiddenDigests`) to the first `r` roots of each Fiat–Shamir query
   keeps the Merkle preimage/root-hit budget bounded by `3 * |tr_MT| + r * |tr_FS|` regardless of
   adversarial Fiat–Shamir input lengths, while `fsOutOfOrderTargets` bounds out-of-order
   Fiat–Shamir chain guessing by `|tr_FS| / |Chal|` per query. Accumulating both growing channel
   budgets via `OracleComp.toOuterMeasure_bad_le_two_budgets` bounds adaptive cheating provers with
   `t_FS` Fiat–Shamir queries and `Q_MT` total Merkle queries by
   `(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / |Chal|)) +`
   `Q_MT * ((3 * Q_MT + r * (t_FS + r)) * (1 / 2 ^ σ))`.
4. **Adaptive straight-line ROM knowledge soundness (`IOPRoundByRoundKnowledgeSoundness`,
   `bcsROMKnowledgeSoundness_bound`, `bcsROMKnowledgeSoundness_bound_of_prover_verifier`).** From
   `IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep` (which also implies
   `IOPRoundByRoundSoundness` for `{x | ∃ w, rel x w}` via
   `IOPRoundByRoundKnowledgeSoundness.toRoundByRoundSoundness`), `bcsKnowledgeSoundnessGame`
   reconstructs `bcsExtractWitness iopExtract decSym defaultSym tr_P x prf.roots` straight-line
   from the prover's own Merkle query trace `tr_P` *before* running `bcsVerifyROM`, with zero
   rewinding, and bounds the probability that `bcsVerifyROM` accepts while `rel x w` fails by the
   same explicit two-channel ROM error bound.

**Source-to-Lean adaptation and scope notes:**
* *Oracle and transcript convention:* [ChiesaYogev2024], Construction 25.1.1 (printed pp. 274–275)
  already uses `2 * r` separate domain-separated per-round Merkle and Fiat–Shamir random oracles
  (with zero-knowledge salt lengths `s_MT`, `s_FS`; see Remark 25.1.3 on root-prefix vs. hash-chain
  Fiat–Shamir queries). Here (`s_MT = s_FS = 0`), `BCSROMSpec Stmt Chal := MerkleHashSpec ⊕ₒ
  BCSFSSpec Stmt Chal` uses two unindexed typed channels: one shared Merkle hash channel on
  `Sum.inl` (`List Bool → List Bool`, via `merkleRootProg` / `merklePathProg` / `merkleVerifyProg`
  with `encPair` node framing) and one transcript-chained Fiat–Shamir channel on `Sum.inr`
  (`BCSFSQuery Stmt Chal := Stmt × List (List Bool) × List Chal ↦ Chal`, querying
  `(x, rootPrefix roots j, [c_0, ..., c_{j-1}]) ↦ c_j` in round `j`).
* *Round-by-round vs. state-restoration hypotheses:* Both [BenSassonChiesaSpooner2016] and
  [ChiesaYogev2024], Theorem 25.2.1 and Theorem 26.1.1 (printed pp. 276–278 and 288–289) formulate
  BCS ROM soundness and straight-line knowledge soundness via IOP state-restoration soundness and
  state-restoration knowledge soundness, while [ChiesaYogev2024], Chapter 31 (Definitions
  31.1.1–31.1.2, Definition 31.1.6, Construction 31.1.8, Theorem 31.2.1, and Theorem 31.3.1)
  reduces state-restoration soundness and knowledge soundness to round-by-round hypotheses. This
  layer proves the ROM bounds directly from `IOPRoundByRoundSoundness` and
  `IOPRoundByRoundKnowledgeSoundness` (whose deterministic `extract_of_doomed` on complete `doomed`
  transcripts is stronger than Definition 31.1.6's two-phase per-round experiment) with per-round
  uniform challenge escape probability `≤ ε_rbr`, bounding adaptive Fiat–Shamir grinding directly
  via `ε_rbr` and out-of-order chain-guessing targets (`fsOutOfOrderTargets`).
* *Explicit additive loss and query budgets:* Accumulating growing budgets across both channels via
  `OracleComp.toOuterMeasure_bad_le_two_budgets` and
  `CslibFrontier/Crypto/Computational/MerkleTree/ROMExtract.lean` yields the explicit additive bound
  `(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) + Q_MT *
  ((3 * Q_MT + r * (t_FS + r)) * (1 / 2 ^ σ))` (rather than the book's state-restoration plus
  multi-instance Merkle extraction error expression). Query budgets count all Merkle and Fiat–Shamir
  oracle calls, including malformed opening paths; the separate-budget corollaries
  (`bcsROMSoundness_bound_of_prover_verifier`, `bcsROMKnowledgeSoundness_bound_of_prover_verifier`)
  bound verifier Merkle cost only on outputs in `P.support`.
* *Straight-line trace extraction and absent runtime certificate:* `bcsKnowledgeSoundnessGame`
  reconstructs `bcsExtractWitness iopExtract decSym defaultSym tr_P x prf.roots` directly from the
  prover's pre-verifier Merkle query trace `tr_P` with zero rewinding (compare [ChiesaYogev2024],
  Construction 26.1.3). These theorems establish exact `OracleComp` probability/query-budget laws;
  machine-level (`IsPPT` / native Turing-machine) runtime certificates for the verifier and
  multi-extractor (compare [ChiesaYogev2024], Remark 18.5.8), digest truncation accounting,
  polynomial-time NP-witness-to-IOP encoding, and zero-knowledge simulation remain outside scope.

## Main definitions

* `Cslib.Crypto.Protocols.BCS.bcsExtractTable`, `Cslib.Crypto.Protocols.BCS.bcsExtractOracles`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractWitness`,
  `Cslib.Crypto.Protocols.BCS.BCSOpeningsQueriedInTrace`: straight-line oracle-table and witness
  extraction from a Merkle trace and path-coverage predicate for BCS openings.
* `Cslib.Crypto.Protocols.BCS.BCSFSQuery`, `Cslib.Crypto.Protocols.BCS.BCSFSSpec`,
  `Cslib.Crypto.Protocols.BCS.BCSROMSpec`, `Cslib.Crypto.Protocols.BCS.bcsOracle`,
  `Cslib.Crypto.Protocols.BCS.chainedFSChallenges`, `Cslib.Crypto.Protocols.BCS.chainedFS`:
  two-channel BCS random-oracle interface and transcript-chained Fiat–Shamir bridge.
* `Cslib.Crypto.Protocols.BCS.bcsChallengesProg`, `Cslib.Crypto.Protocols.BCS.bcsProveROM`,
  `Cslib.Crypto.Protocols.BCS.bcsVerifyOpeningsProg`, `Cslib.Crypto.Protocols.BCS.bcsVerifyROM`,
  `Cslib.Crypto.Protocols.BCS.bcsOracleDist`, `Cslib.Crypto.Protocols.BCS.bcsHonestROMProg`,
  `Cslib.Crypto.Protocols.BCS.bcsHonestROMGame`: oracle-program BCS prover, verifier, and honest
  ROM completeness experiment.
* `Cslib.Crypto.Protocols.BCS.IOPRoundByRoundKnowledgeSoundness`: round-by-round knowledge
  soundness of a `PublicCoinIOP` with a straight-line IOP extractor.
* `Cslib.Crypto.Protocols.BCS.BCSTraceState`, `Cslib.Crypto.Protocols.BCS.bcsMemoize`,
  `Cslib.Crypto.Protocols.BCS.ValidFSChain`, `Cslib.Crypto.Protocols.BCS.bcsExtractTranscript`,
  `Cslib.Crypto.Protocols.BCS.BCSChainDoomed`, `Cslib.Crypto.Protocols.BCS.BCSGoodState`,
  `Cslib.Crypto.Protocols.BCS.bcsForbiddenDigests`,
  `Cslib.Crypto.Protocols.BCS.fsOutOfOrderTargets`: list-trace ROM handler and adaptive soundness
  invariants.
* `Cslib.Crypto.Protocols.BCS.bcsMTCost`, `Cslib.Crypto.Protocols.BCS.bcsFSCost`,
  `Cslib.Crypto.Protocols.BCS.bcsOpeningsMerkleQueries`,
  `Cslib.Crypto.Protocols.BCS.bcsSoundnessProg`, `Cslib.Crypto.Protocols.BCS.bcsSoundnessGame`,
  `Cslib.Crypto.Protocols.BCS.bcsExecROM`,
  `Cslib.Crypto.Protocols.BCS.bcsKnowledgeSoundnessGame`: per-channel query costs and ROM soundness
  and knowledge-soundness experiments.

## Main results

* `Cslib.Crypto.Protocols.BCS.iopVerify_bcsExtractOracles_of_bcsVerify`,
  `Cslib.Crypto.Protocols.BCS.exists_collision_of_bcsVerify_of_iopVerify_eq_false`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractTable_cons_of_ne`,
  `Cslib.Crypto.Protocols.BCS.bcsExtractOracles_cons_of_ne`: fixed-trace consistency, dual
  collision extraction, and non-inverting Merkle extension invariance for `bcsExtractOracles`.
* `Cslib.Crypto.Protocols.BCS.evalPure_bcsChallengesProg`,
  `Cslib.Crypto.Protocols.BCS.evalPure_bcsProveROM`,
  `Cslib.Crypto.Protocols.BCS.evalPure_bcsVerifyROM`,
  `Cslib.Crypto.Protocols.BCS.bcsVerifyROM_bcsProveROM_eq_true`,
  `Cslib.Crypto.Protocols.BCS.bcsHonestROMGame_eq_pure_true`: deterministic simulation and perfect
  completeness of the BCS transform in the two-channel random-oracle model.
* `Cslib.Crypto.Protocols.BCS.IOPRoundByRoundKnowledgeSoundness.toRoundByRoundSoundness`,
  `Cslib.Crypto.Protocols.BCS.IOPRoundByRoundKnowledgeSoundness.rel_iopExtract_of_goodSteps`:
  round-by-round knowledge soundness implies round-by-round soundness for `{x | ∃ w, rel x w}` and
  witness recovery along good challenge steps.
* `Cslib.Crypto.Protocols.BCS.toOuterMeasure_bcsMemoize_not_goodState_step`,
  `Cslib.Crypto.Protocols.BCS.toOuterMeasure_run_bcsMemoize_not_goodState_le`: single-step and
  accumulated bad-state bounds for `bcsMemoize`.
* `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsFSCost_bcsVerifyROM`,
  `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsMTCost_bcsVerifyROM`,
  `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le`: verifier query
  cost bounds on both channels.
* `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound`,
  `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound_of_prover_verifier`: adaptive two-channel ROM
  soundness bounds for the BCS transform.
* `Cslib.Crypto.Protocols.BCS.bcsROMKnowledgeSoundness_trace_bound`,
  `Cslib.Crypto.Protocols.BCS.bcsROMKnowledgeSoundness_bound`,
  `Cslib.Crypto.Protocols.BCS.bcsROMKnowledgeSoundness_bound_of_prover_verifier`: adaptive
  straight-line ROM knowledge soundness bounds without rewinding.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Chapter 18 (Construction 18.5.3 and Lemma 18.5.7, printed pp. 199, 207), Chapter 25
  (Construction 25.1.1, Remark 25.1.3, and Theorem 25.2.1, printed pp. 274–278), Chapter 26
  (Theorem 26.1.1 and Construction 26.1.3, printed pp. 288–289), and Chapter 31 (Definitions
  31.1.1–31.1.2, Definition 31.1.6, Construction 31.1.8, Theorem 31.2.1, and Theorem 31.3.1).
-/

public section

namespace Cslib.Crypto.Protocols.BCS

open Cslib.Crypto Cslib.Probability Cslib.OracleComp Turing.MultiTapeTM
open scoped ENNReal

/-! ### Part 1: Straight-line multi-round oracle-table reconstruction -/

section Extract

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

/-- Straight-line extraction of a depth-`d` IOP oracle table over `Sym` committed under Merkle root
`rt` from a recorded Merkle hash trace `tr_MT`: decodes each leaf returned by
`extractLeafFromTrace` via `decSym`, defaulting to `defaultSym` on unqueried positions
([BenSassonChiesaSpooner2016]; [ChiesaYogev2024], Construction 18.5.3 and Lemma 18.5.7). -/
@[expose] def bcsExtractTable (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool)) (d : ℕ) (rt : List Bool) : OracleTable d Sym :=
  fun idx => match extractLeafFromTrace tr_MT d rt idx.val with
    | some bits => decSym bits
    | none => defaultSym

/-- Straight-line extraction of all `r` committed round oracle tables from a Merkle trace `tr_MT`
and root vector `roots : Fin r → List Bool`. -/
@[expose] def bcsExtractOracles (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool)) (d : ℕ) (roots : Fin r → List Bool) :
    Fin r → OracleTable d Sym :=
  fun j => bcsExtractTable decSym defaultSym tr_MT d (roots j)

/-- Straight-line BCS knowledge extractor: reconstructs the `r` committed IOP oracle tables from
`tr_MT` via `bcsExtractOracles` and applies the underlying straight-line IOP extractor `iopExtract`.
-/
@[expose] def bcsExtractWitness (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool)) (x : Stmt) (roots : Fin r → List Bool) : Wit :=
  iopExtract x (bcsExtractOracles decSym defaultSym tr_MT d roots)

/-- Every Merkle opening `((j, idx), (val, path))` checked by `iop.queries x chals` against
`prf.openings` has all of its hash steps recorded in `tr_MT`. -/
@[expose] def BCSOpeningsQueriedInTrace (H : List Bool → List Bool → List Bool) (k : List Bool)
    (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (encSym : Sym → List Bool)
    (tr_MT : List (List Bool × List Bool)) (x : Stmt) (chals : Fin r → Chal)
    (prf : BCSProof r Sym) : Prop :=
  ∀ j idx val path,
    ((j, idx), (val, path)) ∈ (iop.queries x chals).zip prf.openings →
      PathQueriedInTrace H k tr_MT idx.val (encSym val) path

instance instDecidableBCSOpeningsQueriedInTrace (H : List Bool → List Bool → List Bool)
    (k : List Bool) (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (encSym : Sym → List Bool)
    (tr_MT : List (List Bool × List Bool)) (x : Stmt) (chals : Fin r → Chal)
    (prf : BCSProof r Sym) :
    Decidable (BCSOpeningsQueriedInTrace H k iop encSym tr_MT x chals prf) :=
  decidable_of_iff
    (∀ e ∈ (iop.queries x chals).zip prf.openings,
      match e with
      | ((_, idx), (val, path)) => PathQueriedInTrace H k tr_MT idx.val (encSym val) path)
    ⟨fun h j idx val path hmem => h ((j, idx), (val, path)) hmem,
     fun h ⟨⟨j, idx⟩, ⟨val, path⟩⟩ hmem => h j idx val path hmem⟩

/-- If `tr_MT` is collision-free and records the authentication path of an opening `(val, path)` at
`idx` accepted by `merkleVerify`, then `bcsExtractTable` recovers `val`. -/
theorem bcsExtractTable_eq_of_merkleVerify {H : List Bool → List Bool → List Bool} {k : List Bool}
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym)
    {tr_MT : List (List Bool × List Bool)} {rt : List Bool} {idx : Fin (2 ^ d)} {val : Sym}
    {path : List (List Bool)} (hfree : TraceCollisionFree tr_MT)
    (hpath : PathQueriedInTrace H k tr_MT idx.val (encSym val) path)
    (hver : merkleVerify H k d rt idx.val (encSym val) path = true) :
    bcsExtractTable decSym defaultSym tr_MT d rt idx = val := by
  simp only [bcsExtractTable, extractLeafFromTrace_eq_some_of_merkleVerify hfree hpath hver,
    hdec val]

/-- **Fixed-trace consistency of `bcsExtractOracles`** ([ChiesaYogev2024], Lemma 18.5.7): if
`tr_MT` is collision-free and records all hash steps of the openings in `prf`, then whenever
`bcsVerify` accepts `prf`, `iopVerify` accepts the extracted oracle tables `bcsExtractOracles` at
`bcsChallenge hFS x prf.roots`. -/
theorem iopVerify_bcsExtractOracles_of_bcsVerify {H : List Bool → List Bool → List Bool}
    {k : List Bool} {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym)
    {hFS : Stmt → List (List Bool) → Chal} {tr_MT : List (List Bool × List Bool)}
    {x : Stmt} {prf : BCSProof r Sym}
    (hfree : TraceCollisionFree tr_MT)
    (hpaths : BCSOpeningsQueriedInTrace H k iop encSym tr_MT x (bcsChallenge hFS x prf.roots) prf)
    (hver : bcsVerify iop H k encSym hFS x prf = true) :
    iopVerify iop x (bcsChallenge hFS x prf.roots)
      (bcsExtractOracles decSym defaultSym tr_MT d prf.roots) = true := by
  refine iopVerify_eq_true_of_bcsVerify_of_openings_eq hver fun j idx val path hmem => ?_
  have hmv : merkleVerify H k d (prf.roots j) idx.val (encSym val) path = true := by
    simp only [bcsVerify, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hver
    exact hver.1.2 ((j, idx), (val, path)) hmem
  exact (bcsExtractTable_eq_of_merkleVerify hdec defaultSym hfree
    (hpaths j idx val path hmem) hmv).symm

/-- **Dual collision extraction for `bcsExtractOracles`**: if `tr_MT` is consistent with `H k` and
records all opened paths of a proof accepted by `bcsVerify`, yet `iopVerify` rejects
`bcsExtractOracles`, then `tr_MT` contains two distinct queries with the same hash under `H k`. -/
theorem exists_collision_of_bcsVerify_of_iopVerify_eq_false
    {H : List Bool → List Bool → List Bool} {k : List Bool}
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym)
    {hFS : Stmt → List (List Bool) → Chal} {tr_MT : List (List Bool × List Bool)}
    {x : Stmt} {prf : BCSProof r Sym}
    (hcons : TraceConsistentWith (H k) tr_MT)
    (hpaths : BCSOpeningsQueriedInTrace H k iop encSym tr_MT x (bcsChallenge hFS x prf.roots) prf)
    (hver : bcsVerify iop H k encSym hFS x prf = true)
    (hrej : iopVerify iop x (bcsChallenge hFS x prf.roots)
      (bcsExtractOracles decSym defaultSym tr_MT d prf.roots) = false) :
    ∃ q₁ ∈ tr_MT.map Prod.fst, ∃ q₂ ∈ tr_MT.map Prod.fst, q₁ ≠ q₂ ∧ H k q₁ = H k q₂ := by
  set chals := bcsChallenge hFS x prf.roots
  have hnot_all : ¬ ∀ p ∈ (iop.queries x chals).zip prf.openings,
      extractLeafFromTrace tr_MT d (prf.roots p.1.1) p.1.2.val = some (encSym p.2.1) := by
    intro hall
    have hacc : iopVerify iop x chals
        (bcsExtractOracles decSym defaultSym tr_MT d prf.roots) = true := by
      refine iopVerify_eq_true_of_bcsVerify_of_openings_eq hver fun j idx val path hmem => ?_
      have hleaf := hall ((j, idx), (val, path)) hmem
      simp only [bcsExtractOracles, bcsExtractTable, hleaf, hdec val]
    rw [hacc] at hrej
    cases hrej
  push Not at hnot_all
  obtain ⟨⟨⟨j, idx⟩, ⟨val, path⟩⟩, hmem, hne⟩ := hnot_all
  have hmv : merkleVerify H k d (prf.roots j) idx.val (encSym val) path = true := by
    simp only [bcsVerify, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hver
    exact hver.1.2 ((j, idx), (val, path)) hmem
  exact exists_collision_of_extractLeafFromTrace_ne hcons (hpaths j idx val path hmem) hmv hne

/-- Prepending `(q, ans)` to `tr_MT` leaves `bcsExtractTable` at `rt` unchanged whenever `ans ≠ rt`
and `ans` does not equal `unframe p.1` or `dropFrame p.1` for any `p ∈ tr_MT`. -/
theorem bcsExtractTable_cons_of_ne (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool)) (q : List Bool) {ans rt : List Bool}
    (hrt : ans ≠ rt) (hchildren : ∀ p ∈ tr_MT, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1) :
    bcsExtractTable decSym defaultSym ((q, ans) :: tr_MT) d rt =
      bcsExtractTable decSym defaultSym tr_MT d rt := by
  funext idx
  simp only [bcsExtractTable, extractLeafFromTrace_cons_of_ne tr_MT q d idx.val hrt hchildren]

/-- Prepending `(q, ans)` to `tr_MT` leaves `bcsExtractOracles` on `roots` unchanged whenever `ans`
avoids all `roots j` and all left/right child digests of `tr_MT`. -/
theorem bcsExtractOracles_cons_of_ne (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool)) (q : List Bool) {ans : List Bool}
    {roots : Fin r → List Bool} (hroots : ∀ j : Fin r, ans ≠ roots j)
    (hchildren : ∀ p ∈ tr_MT, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1) :
    bcsExtractOracles decSym defaultSym ((q, ans) :: tr_MT) d roots =
      bcsExtractOracles decSym defaultSym tr_MT d roots := by
  funext j
  exact bcsExtractTable_cons_of_ne decSym defaultSym tr_MT q (hroots j) hchildren

end Extract

/-! ### Part 2: Two-channel BCS random-oracle model & perfect completeness -/

/-- Query input to the transcript-chained BCS Fiat–Shamir oracle: statement `x`, root prefix `rts`
through the current round, and challenges `prevChals` from earlier rounds. -/
abbrev BCSFSQuery (Stmt Chal : Type) : Type :=
  Stmt × List (List Bool) × List Chal

/-- Oracle specification for the transcript-chained BCS Fiat–Shamir challenge oracle. -/
abbrev BCSFSSpec (Stmt Chal : Type) : OracleSpec (BCSFSQuery Stmt Chal) :=
  fun _ => Chal

/-- Combined two-channel random-oracle specification for the BCS transform: a Merkle hash oracle on
the left (`Sum.inl`) and a transcript-chained Fiat–Shamir challenge oracle on the right (`Sum.inr`).
-/
abbrev BCSROMSpec (Stmt Chal : Type) : OracleSpec (List Bool ⊕ BCSFSQuery Stmt Chal) :=
  MerkleHashSpec ⊕ₒ BCSFSSpec Stmt Chal

/-- Combine a deterministic Merkle hash `hTree` and a deterministic transcript-chained Fiat–Shamir
function `f` into a deterministic oracle for `BCSROMSpec Stmt Chal`. -/
abbrev bcsOracle {Stmt Chal : Type} (hTree : List Bool → List Bool)
    (f : BCSFSQuery Stmt Chal → Chal) :
    (q : List Bool ⊕ BCSFSQuery Stmt Chal) → BCSROMSpec Stmt Chal q :=
  OracleComp.sumPure (spec₁ := MerkleHashSpec) (spec₂ := BCSFSSpec Stmt Chal) hTree f

/-- Sequentially compute the transcript-chained Fiat–Shamir challenge list `[c_0, ..., c_{k-1}]`
associated with a Merkle root list `rts = [rt_0, ..., rt_{k-1}]` under `f`. -/
@[expose] def chainedFSChallenges {Stmt Chal : Type} (f : BCSFSQuery Stmt Chal → Chal)
    (x : Stmt) (rts : List (List Bool)) : List Chal :=
  (rts.foldl (fun (accRts, accChals) rt =>
    let rts' := accRts ++ [rt]
    (rts', accChals ++ [f (x, rts', accChals)])) ([], [])).2

/-- Deterministic bridge turning a transcript-chained Fiat–Shamir function
`f : Stmt × List (List Bool) × List Chal → Chal` into the root-prefix Fiat–Shamir interface
`Stmt → List (List Bool) → Chal` of `CslibFrontier/Crypto/Protocols/BCS/Basic.lean`. -/
@[expose] def chainedFS {Stmt Chal : Type} (f : BCSFSQuery Stmt Chal → Chal)
    (x : Stmt) (rts : List (List Bool)) : Chal :=
  f (x, rts, chainedFSChallenges f x rts.dropLast)

private theorem fst_foldl_chainedFSChallenges {Stmt Chal : Type}
    (f : BCSFSQuery Stmt Chal → Chal) (x : Stmt) (rts : List (List Bool))
    (initRts : List (List Bool)) (initChals : List Chal) :
    (rts.foldl (fun (accRts, accChals) rt =>
      let rts' := accRts ++ [rt]
      (rts', accChals ++ [f (x, rts', accChals)])) (initRts, initChals)).1 = initRts ++ rts := by
  induction rts generalizing initRts initChals with
  | nil => simp
  | cons rt rest ih =>
    simp only [List.foldl_cons, ih, List.append_assoc, List.singleton_append]

@[simp]
theorem chainedFSChallenges_nil {Stmt Chal : Type} (f : BCSFSQuery Stmt Chal → Chal) (x : Stmt) :
    chainedFSChallenges f x [] = [] :=
  rfl

theorem chainedFSChallenges_concat {Stmt Chal : Type} (f : BCSFSQuery Stmt Chal → Chal) (x : Stmt)
    (rts : List (List Bool)) (rt : List Bool) :
    chainedFSChallenges f x (rts ++ [rt]) =
      chainedFSChallenges f x rts ++ [chainedFS f x (rts ++ [rt])] := by
  unfold chainedFSChallenges chainedFS
  rw [List.foldl_concat, List.dropLast_concat]
  set p := rts.foldl (fun (accRts, accChals) rt =>
    let rts' := accRts ++ [rt]
    (rts', accChals ++ [f (x, rts', accChals)])) ([], [])
  have hp₁ : p.1 = rts := by
    simpa only [List.nil_append] using fst_foldl_chainedFSChallenges f x rts [] []
  have hp₂ : p.2 = chainedFSChallenges f x rts := rfl
  rcases hp : p with ⟨accRts, accChals⟩
  rw [hp] at hp₁ hp₂
  dsimp only at hp₁ hp₂ ⊢
  subst hp₁
  rw [← hp₂]

/-- Append one element at index `m` to a vector `Fin m → α`. -/
private def snocFin {m : ℕ} {α : Type} (v : Fin m → α) (last : α) (i : Fin (m + 1)) : α :=
  if h : i.val < m then v ⟨i.val, h⟩ else last

private theorem ofFn_snocFin {m : ℕ} {α : Type} (v : Fin m → α) (last : α) :
    List.ofFn (snocFin v last) = List.ofFn v ++ [last] := by
  refine List.ext_getElem (by simp) fun k hk₁ hk₂ => ?_
  simp only [List.length_ofFn] at hk₁
  by_cases hkm : k < m
  · rw [List.getElem_ofFn, List.getElem_append_left (by simpa using hkm), List.getElem_ofFn]
    simp [snocFin, hkm]
  · have hkeq : k = m := by omega
    subst hkeq
    rw [List.getElem_ofFn, List.getElem_append_right (by simp)]
    simp [snocFin]

private theorem rootPrefix_eq_take_append {r : ℕ} (roots : Fin r → List Bool) {m : ℕ}
    (hm : m + 1 ≤ r) :
    rootPrefix roots ⟨m, hm⟩ = (List.ofFn roots).take m ++ [roots ⟨m, hm⟩] := by
  rw [rootPrefix_eq_take_ofFn]
  have hlt : m < (List.ofFn roots).length := by simpa using hm
  simpa only [List.getElem_ofFn] using List.take_succ_eq_append_getElem hlt

/-- Structural round loop for `bcsChallengesProg`. -/
private def bcsChallengesAuxProg {r : ℕ} {Stmt Chal : Type} (x : Stmt)
    (roots : Fin r → List Bool) :
    (m : ℕ) → m ≤ r → OracleComp (BCSFSSpec Stmt Chal) (Fin m → Chal)
  | 0, _ => return Fin.elim0
  | m + 1, hm => do
    let prev ← bcsChallengesAuxProg x roots m (Nat.le_of_succ_le hm)
    let c ← OracleComp.query (spec := BCSFSSpec Stmt Chal)
      (x, rootPrefix roots ⟨m, hm⟩, List.ofFn prev)
    return snocFin prev c

/-- Sequentially query the transcript-chained Fiat–Shamir oracle to derive all `r` round challenges
`(c_0, ..., c_{r-1})` from `(x, roots)`. -/
def bcsChallengesProg {r : ℕ} {Stmt Chal : Type} (x : Stmt)
    (roots : Fin r → List Bool) : OracleComp (BCSFSSpec Stmt Chal) (Fin r → Chal) :=
  bcsChallengesAuxProg x roots r le_rfl

private theorem evalPure_bcsChallengesAuxProg {r : ℕ} {Stmt Chal : Type}
    (f : BCSFSQuery Stmt Chal → Chal) (x : Stmt) (roots : Fin r → List Bool) :
    ∀ (m : ℕ) (hm : m ≤ r),
      List.ofFn (OracleComp.evalPure f (bcsChallengesAuxProg x roots m hm)) =
        chainedFSChallenges f x ((List.ofFn roots).take m) ∧
      ∀ i : Fin m,
        OracleComp.evalPure f (bcsChallengesAuxProg x roots m hm) i =
          bcsChallenge (chainedFS f) x roots ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩
  | 0, _ => ⟨by simp [bcsChallengesAuxProg], fun i => i.elim0⟩
  | m + 1, hm => by
    obtain ⟨hlist, hidx⟩ := evalPure_bcsChallengesAuxProg f x roots m (Nat.le_of_succ_le hm)
    simp only [bcsChallengesAuxProg, OracleComp.evalPure_bind, OracleComp.evalPure_query,
      OracleComp.evalPure_pure]
    have hc : f (x, rootPrefix roots ⟨m, hm⟩,
        List.ofFn (OracleComp.evalPure f (bcsChallengesAuxProg x roots m (Nat.le_of_succ_le hm)))) =
        bcsChallenge (chainedFS f) x roots ⟨m, hm⟩ := by
      rw [hlist, bcsChallenge, chainedFS, rootPrefix_eq_take_append roots hm, List.dropLast_concat]
    refine ⟨?_, fun i => ?_⟩
    · rw [ofFn_snocFin, hc, hlist, bcsChallenge, rootPrefix_eq_take_append roots hm,
        ← chainedFSChallenges_concat, ← rootPrefix_eq_take_append roots hm,
        rootPrefix_eq_take_ofFn]
    · by_cases him : i.val < m
      · simp only [snocFin, him, ↓reduceDIte]
        exact hidx ⟨i.val, him⟩
      · have hieq : i.val = m := by omega
        simp only [snocFin, him, ↓reduceDIte, hc]
        congr 1
        exact Fin.ext hieq.symm

@[simp]
theorem evalPure_bcsChallengesProg {r : ℕ} {Stmt Chal : Type}
    (f : BCSFSQuery Stmt Chal → Chal) (x : Stmt) (roots : Fin r → List Bool) :
    OracleComp.evalPure f (bcsChallengesProg x roots) =
      bcsChallenge (chainedFS f) x roots := by
  funext j
  exact (evalPure_bcsChallengesAuxProg f x roots r le_rfl).2 j

section ROMProtocol

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

/-- Structural round loop for `bcsProveROM`: sequentially computes the first `m` IOP oracle tables,
commits to each with `merkleRootProg`, and derives each round's Fiat–Shamir challenge on the right
channel. -/
private def bcsProveRoundsProg (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (w : Wit) :
    (m : ℕ) → m ≤ r →
      OracleComp (BCSROMSpec Stmt Chal)
        ((Fin m → OracleTable d Sym) × (Fin m → List Bool) × (Fin m → Chal))
  | 0, _ => return (Fin.elim0, Fin.elim0, Fin.elim0)
  | m + 1, hm => do
    let (tables, roots, chals) ← bcsProveRoundsProg iop encSym x w m (Nat.le_of_succ_le hm)
    let π := iop.proveRound ⟨m, hm⟩ x w chals
    let rt ← OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal)
      (merkleRootProg (oracleLeaves encSym d π))
    let roots' := snocFin roots rt
    let c ← OracleComp.liftRight (spec₁ := MerkleHashSpec)
      (OracleComp.query (spec := BCSFSSpec Stmt Chal) (x, List.ofFn roots', List.ofFn chals))
    return (snocFin tables π, roots', snocFin chals c)

/-- **The BCS prover in the two-channel random-oracle model** (`bcsProveROM`): runs all `r`
commit-and-challenge rounds via `bcsProveRoundsProg` and opens every queried entry under
`merklePathProg` ([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024], Construction 25.1.1,
printed pp. 274–275). -/
def bcsProveROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (w : Wit) :
    OracleComp (BCSROMSpec Stmt Chal) (BCSProof r Sym) := do
  let (tables, roots, chals) ← bcsProveRoundsProg iop encSym x w r le_rfl
  let openings ← OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal)
    ((iop.queries x chals).mapM fun (j, idx) => do
      let path ← merklePathProg (oracleLeaves encSym d (tables j)) idx.val
      return (tables j idx, path))
  return { roots := roots, openings := openings }

/-- Verify all Merkle openings and the IOP decision predicate for a `BCSProof` given already
derived challenges `chals`. -/
@[expose] def bcsVerifyOpeningsProg (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (prf : BCSProof r Sym) (chals : Fin r → Chal) :
    OracleComp MerkleHashSpec Bool := do
  let qs := iop.queries x chals
  let checks ← (qs.zip prf.openings).mapM fun ((j, idx), (val, path)) =>
    merkleVerifyProg d (prf.roots j) idx.val (encSym val) path
  return prf.openings.length == qs.length &&
    checks.all id &&
    iop.decide x chals (prf.openings.map Prod.fst)

/-- **The BCS verifier in the two-channel random-oracle model** (`bcsVerifyROM`): re-derives all `r`
round challenges on the Fiat–Shamir channel via `bcsChallengesProg` and checks all Merkle openings
and `iop.decide` on the Merkle channel via `bcsVerifyOpeningsProg` ([BenSassonChiesaSpooner2016];
compare [ChiesaYogev2024], Construction 25.1.1, printed pp. 274–275). -/
@[expose] def bcsVerifyROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (prf : BCSProof r Sym) :
    OracleComp (BCSROMSpec Stmt Chal) Bool := do
  let chals ← OracleComp.liftRight (spec₁ := MerkleHashSpec) (bcsChallengesProg x prf.roots)
  OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal)
    (bcsVerifyOpeningsProg iop encSym x prf chals)

private theorem evalPure_bcsProveRoundsProg (hTree : List Bool → List Bool)
    (f : BCSFSQuery Stmt Chal → Chal) (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (w : Wit) :
    ∀ (m : ℕ) (hm : m ≤ r),
      let out := OracleComp.evalPure (bcsOracle hTree f)
        (bcsProveRoundsProg iop encSym x w m hm)
      let hTables := bcsHonestTables iop (fun _ => hTree) [] encSym (chainedFS f) x w
      let hRoots := bcsHonestRoots iop (fun _ => hTree) [] encSym (chainedFS f) x w
      let hChals := bcsHonestChallenges iop (fun _ => hTree) [] encSym (chainedFS f) x w
      (∀ i : Fin m, out.1 i = hTables ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) ∧
      (∀ i : Fin m, out.2.1 i = hRoots ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) ∧
      (∀ i : Fin m, out.2.2 i = hChals ⟨i.val, Nat.lt_of_lt_of_le i.isLt hm⟩) ∧
      List.ofFn out.2.2 = chainedFSChallenges f x ((List.ofFn hRoots).take m)
  | 0, _ => ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      by simp [bcsProveRoundsProg]⟩
  | m + 1, hm => by
    obtain ⟨htab, hrt, hch, hchList⟩ :=
      evalPure_bcsProveRoundsProg hTree f iop encSym x w m (Nat.le_of_succ_le hm)
    rcases hp : OracleComp.evalPure (bcsOracle hTree f)
      (bcsProveRoundsProg iop encSym x w m (Nat.le_of_succ_le hm)) with ⟨tables, roots, chals⟩
    rw [hp] at htab hrt hch hchList
    dsimp only at htab hrt hch hchList ⊢
    have hch_eq : chals = prefixChallenges
        (bcsHonestChallenges iop (fun _ => hTree) [] encSym (chainedFS f) x w) ⟨m, hm⟩ :=
      funext hch
    have hπ : iop.proveRound ⟨m, hm⟩ x w chals =
        bcsHonestTables iop (fun _ => hTree) [] encSym (chainedFS f) x w ⟨m, hm⟩ := by
      have hon := congrFun (bcsHonestTables_eq_iopProverOracles iop (fun _ => hTree) [] encSym
        (chainedFS f) x w) ⟨m, hm⟩
      dsimp only [iopProverOracles] at hon
      rw [hch_eq, ← hon]
    have hrt_m : merkleRoot (fun _ => hTree) []
        (oracleLeaves encSym d (iop.proveRound ⟨m, hm⟩ x w chals)) =
        bcsHonestRoots iop (fun _ => hTree) [] encSym (chainedFS f) x w ⟨m, hm⟩ := by
      rw [hπ]
      rfl
    have hroots'_list :
        List.ofFn (snocFin roots (merkleRoot (fun _ => hTree) []
          (oracleLeaves encSym d (iop.proveRound ⟨m, hm⟩ x w chals)))) =
        rootPrefix (bcsHonestRoots iop (fun _ => hTree) [] encSym (chainedFS f) x w) ⟨m, hm⟩ := by
      rw [ofFn_snocFin, hrt_m, rootPrefix_eq_take_append _ hm]
      congr 1
      refine List.ext_getElem (by simp [Nat.le_of_succ_le hm]) fun k hk₁ hk₂ => ?_
      simp only [List.length_ofFn] at hk₁
      simp [hrt ⟨k, hk₁⟩]
    have hc_m : f (x, List.ofFn (snocFin roots (merkleRoot (fun _ => hTree) []
          (oracleLeaves encSym d (iop.proveRound ⟨m, hm⟩ x w chals)))),
        List.ofFn chals) =
        bcsHonestChallenges iop (fun _ => hTree) [] encSym (chainedFS f) x w ⟨m, hm⟩ := by
      rw [hroots'_list, hchList, bcsHonestChallenges, bcsChallenge, chainedFS,
        rootPrefix_eq_take_append _ hm, List.dropLast_concat]
    simp only [bcsProveRoundsProg, OracleComp.evalPure_bind, hp, OracleComp.evalPure_liftLeft,
      evalPure_merkleRootProg, OracleComp.evalPure_liftRight, OracleComp.evalPure_query,
      OracleComp.evalPure_pure]
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, ?_⟩
    · by_cases him : i.val < m
      · simp only [snocFin, him, ↓reduceDIte]
        exact htab ⟨i.val, him⟩
      · have hieq : i.val = m := by omega
        simp only [snocFin, him, ↓reduceDIte, hπ]
        congr 1
        exact Fin.ext (by simp [hieq])
    · by_cases him : i.val < m
      · simp only [snocFin, him, ↓reduceDIte]
        exact hrt ⟨i.val, him⟩
      · have hieq : i.val = m := by omega
        simp only [snocFin, him, ↓reduceDIte, hrt_m]
        congr 1
        exact Fin.ext (by simp [hieq])
    · by_cases him : i.val < m
      · simp only [snocFin, him, ↓reduceDIte]
        exact hch ⟨i.val, him⟩
      · have hieq : i.val = m := by omega
        simp only [snocFin, him, ↓reduceDIte, hc_m]
        congr 1
        exact Fin.ext (by simp [hieq])
    · rw [ofFn_snocFin, hc_m, hchList, bcsHonestChallenges, bcsChallenge,
        rootPrefix_eq_take_append _ hm, ← chainedFSChallenges_concat,
        ← rootPrefix_eq_take_append _ hm, rootPrefix_eq_take_ofFn]

@[simp]
theorem evalPure_bcsProveROM (hTree : List Bool → List Bool)
    (f : BCSFSQuery Stmt Chal → Chal) (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (w : Wit) :
    OracleComp.evalPure (bcsOracle hTree f) (bcsProveROM iop encSym x w) =
      bcsProve iop (fun _ => hTree) [] encSym (chainedFS f) x w := by
  obtain ⟨htab, hrt, hch, -⟩ :=
    evalPure_bcsProveRoundsProg hTree f iop encSym x w r le_rfl
  rcases hout : OracleComp.evalPure (bcsOracle hTree f)
    (bcsProveRoundsProg iop encSym x w r le_rfl) with ⟨tables, roots, chals⟩
  rw [hout] at htab hrt hch
  have htab_eq : tables = bcsHonestTables iop (fun _ => hTree) [] encSym (chainedFS f) x w :=
    funext htab
  have hrt_eq : roots = bcsHonestRoots iop (fun _ => hTree) [] encSym (chainedFS f) x w :=
    funext hrt
  have hch_eq : chals = bcsHonestChallenges iop (fun _ => hTree) [] encSym (chainedFS f) x w :=
    funext hch
  simp only [bcsProveROM, OracleComp.evalPure_bind, hout, OracleComp.evalPure_liftLeft,
    OracleComp.evalPure_mapM, evalPure_merklePathProg, OracleComp.evalPure_pure,
    htab_eq, hrt_eq, hch_eq, bcsProve, bcsHonestOpenings]

@[simp]
theorem evalPure_bcsVerifyOpeningsProg (hTree : List Bool → List Bool)
    (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (encSym : Sym → List Bool)
    (x : Stmt) (prf : BCSProof r Sym) (chals : Fin r → Chal) :
    OracleComp.evalPure hTree (bcsVerifyOpeningsProg iop encSym x prf chals) =
      (prf.openings.length == (iop.queries x chals).length &&
        ((iop.queries x chals).zip prf.openings).all (fun ((j, idx), (val, path)) =>
          merkleVerify (fun _ => hTree) [] d (prf.roots j) idx.val (encSym val) path) &&
        iop.decide x chals (prf.openings.map Prod.fst)) := by
  simp only [bcsVerifyOpeningsProg, OracleComp.evalPure_bind, OracleComp.evalPure_mapM,
    OracleComp.evalPure_pure, List.all_map]
  congr 2
  refine List.all_congr rfl ?_
  rintro ⟨⟨j, idx⟩, ⟨val, path⟩⟩
  simp

@[simp]
theorem evalPure_bcsVerifyROM (hTree : List Bool → List Bool)
    (f : BCSFSQuery Stmt Chal → Chal) (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (prf : BCSProof r Sym) :
    OracleComp.evalPure (bcsOracle hTree f) (bcsVerifyROM iop encSym x prf) =
      bcsVerify iop (fun _ => hTree) [] encSym (chainedFS f) x prf := by
  simp [bcsVerifyROM, bcsVerify]

/-- **Perfect completeness of the BCS ROM programs (`OracleComp` simulation form)**: under any
deterministic Merkle hash `hTree` and transcript-chained Fiat–Shamir function `f`, `bcsVerifyROM`
accepts `bcsProveROM` on every `(x, w)` satisfying `rel x w`. -/
theorem bcsVerifyROM_bcsProveROM_eq_true {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {rel : Stmt → Wit → Prop} (hcomp : IOPCompleteness iop rel)
    (hTree : List Bool → List Bool) (f : BCSFSQuery Stmt Chal → Chal)
    (encSym : Sym → List Bool) {x : Stmt} {w : Wit} (hrel : rel x w) :
    OracleComp.evalPure (bcsOracle hTree f) (do
      let prf ← bcsProveROM iop encSym x w
      bcsVerifyROM iop encSym x prf) = true := by
  simp [bcsVerify_bcsProve_eq_true hcomp (fun _ => hTree) [] encSym (chainedFS f) hrel]

/-- Per-query distribution of the two-channel BCS random oracle with `σ`-bit Merkle digests and
uniform challenges over `Chal`: Merkle hash queries (`Sum.inl`) sample `BitString.uniformList σ`,
and Fiat–Shamir queries (`Sum.inr`) sample `PMF.uniformOfFintype Chal`. -/
@[expose] noncomputable def bcsOracleDist (Stmt Chal : Type) [Fintype Chal] [Nonempty Chal]
    (σ : ℕ) : (q : List Bool ⊕ BCSFSQuery Stmt Chal) → PMF (BCSROMSpec Stmt Chal q)
  | .inl _ => BitString.uniformList σ
  | .inr _ => PMF.uniformOfFintype Chal

/-- The honest BCS execution as a two-channel `OracleComp` program: generate a proof via
`bcsProveROM` and verify it via `bcsVerifyROM` against the same oracle. -/
@[expose] def bcsHonestROMProg (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (w : Wit) :
    OracleComp (BCSROMSpec Stmt Chal) Bool := do
  let prf ← bcsProveROM iop encSym x w
  bcsVerifyROM iop encSym x prf

/-- The honest BCS random-oracle experiment with `σ`-bit Merkle digests: runs `bcsHonestROMProg`
against the shared lazy random oracle `RandomOracle.answer (bcsOracleDist Stmt Chal σ)` from an
empty cache. -/
@[expose] noncomputable def bcsHonestROMGame [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal] (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (w : Wit) (σ : ℕ) : PMF Bool :=
  (OracleComp.runWith (RandomOracle.answer (bcsOracleDist Stmt Chal σ))
    (bcsHonestROMProg iop encSym x w) (fun _ => none)).map Prod.fst

/-- **Perfect completeness of the BCS transform in the lazy two-channel random-oracle model**: if
`iop` satisfies `IOPCompleteness iop rel` and `rel x w` holds, then for every digest length `σ`,
`bcsHonestROMGame` outputs `true` with probability `1` ([BenSassonChiesaSpooner2016]; compare
[ChiesaYogev2024], Construction 25.1.1, printed pp. 274–275). -/
theorem bcsHonestROMGame_eq_pure_true [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal] {iop : PublicCoinIOP r d Stmt Wit Sym Chal}
    {rel : Stmt → Wit → Prop} (hcomp : IOPCompleteness iop rel)
    (encSym : Sym → List Bool) {x : Stmt} {w : Wit} (hrel : rel x w) (σ : ℕ) :
    bcsHonestROMGame iop encSym x w σ = PMF.pure true := by
  unfold bcsHonestROMGame
  refine OracleComp.map_fst_runWith_answer_eq_pure (bcsOracleDist Stmt Chal σ)
    (bcsHonestROMProg iop encSym x w) true fun h _ => ?_
  have hsplit : h = bcsOracle (fun msg => h (.inl msg)) (fun fsq => h (.inr fsq)) := by
    funext q
    cases q <;> rfl
  rw [hsplit]
  exact bcsVerifyROM_bcsProveROM_eq_true hcomp _ _ encSym hrel

end ROMProtocol

/-! ### Part 3: Round-by-round knowledge soundness & adaptive ROM state invariant -/

section RBRKnowledge

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

/-- **Round-by-round knowledge soundness** of a `PublicCoinIOP` for relation `rel` with
straight-line IOP extractor `iopExtract`, doomed-prefix predicate `doomed`, and non-escaping round
transitions `goodStep` (compare `IOPRoundByRoundSoundness` and [ChiesaYogev2024], Chapter 31,
Definition 31.1.6 and Theorem 31.3.1, as well as state-restoration knowledge soundness in
[BenSassonChiesaSpooner2016] and [ChiesaYogev2024], Chapter 26, Theorem 26.1.1; note that
`extract_of_doomed` here is deterministic on complete `doomed` transcripts):
1. Every statement `x` starts in `doomed x []` on the empty transcript prefix.
2. Every non-escaping challenge `goodStep x pref π c` preserves `doomed`.
3. On any complete transcript `List.ofFn (fun j => (oracles j, chals j))` that remains `doomed`, if
   `iopVerify` accepts `oracles` at `chals`, then `iopExtract x oracles` satisfies `rel x`. -/
structure IOPRoundByRoundKnowledgeSoundness (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (rel : Stmt → Wit → Prop) (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop) :
    Prop where
  /-- Every statement starts in `doomed` on the empty transcript prefix. -/
  init_doomed : ∀ x, doomed x []
  /-- Every non-escaping challenge preserves `doomed`. -/
  step_doomed : ∀ x pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)])
  /-- On any doomed complete transcript accepted by `iopVerify`, `iopExtract` recovers a valid
  witness for `x`. -/
  extract_of_doomed : ∀ x (oracles : Fin r → OracleTable d Sym) (chals : Fin r → Chal),
    doomed x (List.ofFn fun j : Fin r => (oracles j, chals j)) →
      iopVerify iop x chals oracles = true → rel x (iopExtract x oracles)

/-- `IOPRoundByRoundKnowledgeSoundness` for `rel` implies `IOPRoundByRoundSoundness` for the
associated language `{x | ∃ w, rel x w}` with the same `goodStep` relation. -/
theorem IOPRoundByRoundKnowledgeSoundness.toRoundByRoundSoundness
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {rel : Stmt → Wit → Prop}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hks : IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep) :
    IOPRoundByRoundSoundness iop {x | ∃ w, rel x w}
      (fun x pref => x ∉ {x | ∃ w, rel x w} ∧ doomed x pref) goodStep where
  init_doomed x hx := ⟨hx, hks.init_doomed x⟩
  step_doomed x pref π c hd hgood := ⟨hd.1, hks.step_doomed x pref π c hd.2 hgood⟩
  reject_of_doomed x oracles chals hd :=
    Bool.eq_false_iff.mpr fun hver =>
      hd.1 ⟨iopExtract x oracles, hks.extract_of_doomed x oracles chals hd.2 hver⟩

/-- If every round's challenge satisfies `goodStep` under `IOPRoundByRoundKnowledgeSoundness` and
`iopVerify` accepts, then `iopExtract` recovers a valid witness for `x`. -/
theorem IOPRoundByRoundKnowledgeSoundness.rel_iopExtract_of_goodSteps
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {rel : Stmt → Wit → Prop}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hks : IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep)
    (x : Stmt) (oracles : Fin r → OracleTable d Sym) (chals : Fin r → Chal)
    (hsteps : ∀ j : Fin r,
      goodStep x ((List.ofFn fun i : Fin r => (oracles i, chals i)).take j.val)
        (oracles j) (chals j))
    (hver : iopVerify iop x chals oracles = true) :
    rel x (iopExtract x oracles) :=
  hks.extract_of_doomed x oracles chals
    (doomed_ofFn_of_goodSteps (hks.init_doomed x) (hks.step_doomed x) oracles chals hsteps) hver

end RBRKnowledge

/-! #### Two-channel list-trace ROM handler and adaptive good-state invariant -/

/-- List-cache state for the two-channel BCS random oracle: a Merkle hash trace `st.1` and a
transcript-chained Fiat–Shamir trace `st.2`. -/
abbrev BCSTraceState (Stmt Chal : Type) : Type :=
  List (List Bool × List Bool) × List (BCSFSQuery Stmt Chal × Chal)

/-- Two-channel association-list handler implementing
`RandomOracle.answer (bcsOracleDist Stmt Chal σ)`. -/
@[expose] noncomputable def bcsMemoize {Stmt Chal : Type} [BEq Stmt] [BEq Chal]
    [Fintype Chal] [Nonempty Chal] (σ : ℕ) :
    (q : List Bool ⊕ BCSFSQuery Stmt Chal) →
      StateT (BCSTraceState Stmt Chal) PMF (BCSROMSpec Stmt Chal q)
  | .inl msg => fun (tr_MT, tr_FS) =>
    (memoize (fun _ : List Bool => BitString.uniformList σ) msg tr_MT).map fun (ans, tr_MT') =>
      (ans, (tr_MT', tr_FS))
  | .inr fsq => fun (tr_MT, tr_FS) =>
    (memoize (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal) fsq tr_FS).map
      fun (c, tr_FS') => (c, (tr_MT, tr_FS'))

/-- Represent a `BCSTraceState Stmt Chal` as a `RandomOracle.Cache (BCSROMSpec Stmt Chal)`. -/
@[expose] def bcsOfTraces {Stmt Chal : Type} [BEq Stmt] [BEq Chal]
    (st : BCSTraceState Stmt Chal) : RandomOracle.Cache (BCSROMSpec Stmt Chal)
  | .inl msg => RandomOracle.ofList st.1 msg
  | .inr fsq => RandomOracle.ofList st.2 fsq

@[simp]
theorem bcsOfTraces_nil {Stmt Chal : Type} [BEq Stmt] [BEq Chal] :
    bcsOfTraces (Stmt := Stmt) (Chal := Chal) ([], []) = fun _ => none := by
  funext q
  cases q <;> rfl

/-- `bcsMemoize` implements `RandomOracle.answer (bcsOracleDist Stmt Chal σ)` via `bcsOfTraces`. -/
theorem run_interpret_bcsMemoize {Stmt Chal β : Type} [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal] (σ : ℕ)
    (prog : OracleComp (BCSROMSpec Stmt Chal) β) (st : BCSTraceState Stmt Chal) :
    ((OracleComp.interpret (bcsMemoize σ) prog).run st).map
        (fun (res, st') => (res, bcsOfTraces st')) =
      OracleComp.runWith (RandomOracle.answer (bcsOracleDist Stmt Chal σ)) prog
        (bcsOfTraces st) := by
  apply OracleComp.run_interpret_map_state
  rintro (msg | fsq) ⟨tr_MT, tr_FS⟩
  · dsimp only [bcsMemoize]
    cases h : tr_MT.lookup msg with
    | none =>
      rw [memoize_of_none _ _ _ h,
        RandomOracle.answer_of_none (bcsOracleDist Stmt Chal σ) (bcsOfTraces (tr_MT, tr_FS))
          (.inl msg) h]
      change (((BitString.uniformList σ).map (fun v => (v, (msg, v) :: tr_MT))).map _).map _ = _
      simp only [PMF.map_comp, Function.comp_def, bcsOracleDist]
      congr 2 with v : 1
      simp only [Prod.mk.injEq, true_and]
      funext q
      cases q with
      | inl msg' =>
        simpa [bcsOfTraces] using congrFun (RandomOracle.ofList_cons tr_MT msg v) msg'
      | inr fsq' =>
        simp [bcsOfTraces]
    | some val =>
      rw [memoize_of_some _ _ _ _ h,
        RandomOracle.answer_of_some (bcsOracleDist Stmt Chal σ) (bcsOfTraces (tr_MT, tr_FS))
          (.inl msg) val h]
      simp [PMF.monad_pure_eq_pure]
  · dsimp only [bcsMemoize]
    cases h : tr_FS.lookup fsq with
    | none =>
      rw [memoize_of_none _ _ _ h,
        RandomOracle.answer_of_none (bcsOracleDist Stmt Chal σ) (bcsOfTraces (tr_MT, tr_FS))
          (.inr fsq) h]
      change (((PMF.uniformOfFintype Chal).map (fun v => (v, (fsq, v) :: tr_FS))).map _).map _ = _
      simp only [PMF.map_comp, Function.comp_def, bcsOracleDist]
      congr 2 with v : 1
      simp only [Prod.mk.injEq, true_and]
      funext q
      cases q with
      | inl msg' =>
        simp [bcsOfTraces]
      | inr fsq' =>
        simpa [bcsOfTraces] using congrFun (RandomOracle.ofList_cons tr_FS fsq v) fsq'
    | some val =>
      rw [memoize_of_some _ _ _ _ h,
        RandomOracle.answer_of_some (bcsOracleDist Stmt Chal σ) (bcsOfTraces (tr_MT, tr_FS))
          (.inr fsq) val h]
      simp [PMF.monad_pure_eq_pure]

/-- A pair `(rts, chals)` of Merkle roots and challenges forms a valid recorded Fiat–Shamir chain
for statement `x` in `tr_FS` if `rts` and `chals` have equal length and, at every round index
`i < rts.length`, the transcript-chained query `(x, rts.take (i + 1), chals.take i)` is recorded in
`tr_FS` with answer `chals[i]`. -/
@[expose] def ValidFSChain {Stmt Chal : Type} (tr_FS : List (BCSFSQuery Stmt Chal × Chal))
    (x : Stmt) (rts : List (List Bool)) (chals : List Chal) : Prop :=
  ∃ hlen : rts.length = chals.length,
    ∀ (i : ℕ) (hi : i < rts.length),
      ((x, rts.take (i + 1), chals.take i), chals[i]'(hlen ▸ hi)) ∈ tr_FS

/-- Extract the partial IOP transcript `[(π_0, c_0), ..., (π_{k-1}, c_{k-1})]` associated with a
root prefix `rts` and challenge prefix `chals` from Merkle trace `tr_MT`. -/
@[expose] def bcsExtractTranscript {Sym Chal : Type} (decSym : List Bool → Sym)
    (defaultSym : Sym) (d : ℕ) (tr_MT : List (List Bool × List Bool))
    (rts : List (List Bool)) (chals : List Chal) : List (OracleTable d Sym × Chal) :=
  (rts.zip chals).map fun (rt, c) => (bcsExtractTable decSym defaultSym tr_MT d rt, c)

@[simp]
theorem bcsExtractTranscript_nil_left {Sym Chal : Type} (decSym : List Bool → Sym)
    (defaultSym : Sym) (d : ℕ) (tr_MT : List (List Bool × List Bool)) (chals : List Chal) :
    bcsExtractTranscript decSym defaultSym d tr_MT [] chals = [] :=
  rfl

theorem bcsExtractTranscript_append_singleton {Sym Chal : Type} (decSym : List Bool → Sym)
    (defaultSym : Sym) (d : ℕ) (tr_MT : List (List Bool × List Bool))
    {rts : List (List Bool)} {chals : List Chal} (hlen : rts.length = chals.length)
    (rt : List Bool) (c : Chal) :
    bcsExtractTranscript decSym defaultSym d tr_MT (rts ++ [rt]) (chals ++ [c]) =
      bcsExtractTranscript decSym defaultSym d tr_MT rts chals ++
        [(bcsExtractTable decSym defaultSym tr_MT d rt, c)] := by
  simp only [bcsExtractTranscript, List.zip_append hlen, List.zip_cons_cons, List.zip_nil_left,
    List.map_append, List.map_cons, List.map_nil]

theorem bcsExtractTranscript_ofFn {r d : ℕ} {Sym Chal : Type} (decSym : List Bool → Sym)
    (defaultSym : Sym) (tr_MT : List (List Bool × List Bool))
    (roots : Fin r → List Bool) (chals : Fin r → Chal) :
    bcsExtractTranscript decSym defaultSym d tr_MT (List.ofFn roots) (List.ofFn chals) =
      List.ofFn fun j : Fin r =>
        (bcsExtractOracles decSym defaultSym tr_MT d roots j, chals j) := by
  refine List.ext_getElem (by simp [bcsExtractTranscript]) fun k hk₁ hk₂ => ?_
  simp only [List.length_ofFn] at hk₂
  simp [bcsExtractTranscript, bcsExtractOracles]

theorem bcsExtractTranscript_cons_of_ne {Sym Chal : Type} (decSym : List Bool → Sym)
    (defaultSym : Sym) (d : ℕ) (tr_MT : List (List Bool × List Bool)) (q : List Bool)
    {ans : List Bool} {rts : List (List Bool)} (chals : List Chal)
    (hrts : ∀ rt ∈ rts, ans ≠ rt)
    (hchildren : ∀ p ∈ tr_MT, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1) :
    bcsExtractTranscript decSym defaultSym d ((q, ans) :: tr_MT) rts chals =
      bcsExtractTranscript decSym defaultSym d tr_MT rts chals := by
  unfold bcsExtractTranscript
  refine List.map_congr_left ?_
  rintro ⟨rt, c⟩ hmem
  dsimp only
  have hrt : rt ∈ rts := (List.of_mem_zip hmem).1
  rw [bcsExtractTable_cons_of_ne decSym defaultSym tr_MT q (hrts rt hrt) hchildren]

/-- Every valid recorded Fiat–Shamir chain `(rts, chals)` of length `≤ r` for a statement `x ∈ S`
maps under `bcsExtractTranscript` to a doomed IOP transcript prefix. -/
@[expose] def BCSChainDoomed (r d : ℕ) {Stmt Sym Chal : Type} (S : Set Stmt)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool))
    (tr_FS : List (BCSFSQuery Stmt Chal × Chal)) : Prop :=
  ∀ x ∈ S, ∀ rts chals, rts.length ≤ r →
    ValidFSChain tr_FS x rts chals →
      doomed x (bcsExtractTranscript decSym defaultSym d tr_MT rts chals)

/-- Combined good-state invariant of the two-channel BCS random-oracle state `(tr_MT, tr_FS)`:
the Merkle trace `tr_MT` is collision-free and every valid recorded Fiat–Shamir chain of length
`≤ r` on `S` maps to a doomed IOP transcript prefix. -/
@[expose] def BCSGoodState (r d : ℕ) {Stmt Sym Chal : Type} (S : Set Stmt)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (st : BCSTraceState Stmt Chal) : Prop :=
  TraceCollisionFree st.1 ∧ BCSChainDoomed r d S doomed decSym defaultSym st.1 st.2

theorem bcsGoodState_nil (r d : ℕ) {Stmt Sym Chal : Type} {S : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    (hinit : ∀ x ∈ S, doomed x [])
    (decSym : List Bool → Sym) (defaultSym : Sym) :
    BCSGoodState (Chal := Chal) r d S doomed decSym defaultSym ([], []) := by
  refine ⟨traceCollisionFree_nil, fun x hx rts chals _ ⟨hlen, hsteps⟩ => ?_⟩
  cases rts with
  | nil =>
    simpa only [bcsExtractTranscript_nil_left] using hinit x hx
  | cons rt rest =>
    exact False.elim (List.not_mem_nil (hsteps 0 (Nat.zero_lt_succ _)))

/-- Digests that a fresh Merkle hash output must avoid to preserve `BCSGoodState`: existing Merkle
outputs, left/right child digests of existing Merkle queries, and the first `r` roots of every
existing Fiat–Shamir query. Restricting each Fiat–Shamir entry via `List.take r` makes the list
length independent of adversarial Fiat–Shamir root-list sizes. -/
@[expose] def bcsForbiddenDigests (r : ℕ) {Stmt Chal : Type}
    (st : BCSTraceState Stmt Chal) : List (List Bool) :=
  st.1.map Prod.snd ++ st.1.map (fun (q, _) => unframe q) ++
    st.1.map (fun (q, _) => dropFrame q) ++
    st.2.flatMap (fun ((_, rts, _), _) => rts.take r)

theorem length_bcsForbiddenDigests_le (r : ℕ) {Stmt Chal : Type}
    (st : BCSTraceState Stmt Chal) :
    (bcsForbiddenDigests r st).length ≤ 3 * st.1.length + r * st.2.length := by
  unfold bcsForbiddenDigests
  rw [List.length_append, List.length_append, List.length_append,
    List.length_map, List.length_map, List.length_map]
  have hfs : (st.2.flatMap (fun ((_, rts, _), _) => rts.take r)).length ≤ r * st.2.length := by
    simpa only [Nat.mul_comm] using
      List.length_flatMap_le (l := st.2) (f := fun ((_, rts, _), _) => rts.take r) (k := r)
        fun ⟨⟨_, rts, _⟩, _⟩ _ => List.length_take_le r rts
  omega

/-- If `BCSGoodState` holds on `st` and prepending `(msg, ans)` to `st.1` violates `BCSGoodState`,
then `ans` belongs to `bcsForbiddenDigests r st`. -/
theorem mem_bcsForbiddenDigests_of_not_bcsGoodState_cons {r d : ℕ} {Stmt Sym Chal : Type}
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {decSym : List Bool → Sym} {defaultSym : Sym}
    {st : BCSTraceState Stmt Chal} {msg ans : List Bool}
    (hgood : BCSGoodState r d S doomed decSym defaultSym st)
    (hbad : ¬ BCSGoodState r d S doomed decSym defaultSym ((msg, ans) :: st.1, st.2)) :
    ans ∈ bcsForbiddenDigests r st := by
  rcases st with ⟨tr_MT, tr_FS⟩
  obtain ⟨hfree, hdoomed⟩ := hgood
  by_contra hnot_mem
  simp only [bcsForbiddenDigests, List.mem_append, List.mem_map, List.mem_flatMap, not_or,
    not_exists, not_and] at hnot_mem
  obtain ⟨⟨⟨hnot_snd, hnot_left⟩, hnot_right⟩, hnot_fs⟩ := hnot_mem
  apply hbad
  refine ⟨?_, ?_⟩
  · rw [traceCollisionFree_cons_iff]
    exact ⟨hfree, fun p hp heq => False.elim (hnot_snd p hp heq)⟩
  · intro x hx rts chals hr hchain
    have hchildren : ∀ p ∈ tr_MT, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1 :=
      fun ⟨q, d'⟩ hp =>
        ⟨fun heq => hnot_left (q, d') hp heq.symm, fun heq => hnot_right (q, d') hp heq.symm⟩
    rcases rts with _ | ⟨rt₀, rest⟩
    · rw [bcsExtractTranscript_nil_left]
      exact hdoomed x hx [] chals hr hchain
    · set rts := rt₀ :: rest
      have hpos : 0 < rts.length := Nat.zero_lt_succ _
      obtain ⟨hlen, hsteps⟩ := hchain
      have hi : rts.length - 1 < rts.length := Nat.sub_lt hpos Nat.one_pos
      have htake : rts.take (rts.length - 1 + 1) = rts := by
        rw [Nat.sub_add_cancel hpos, List.take_length]
      have hlast_mem : ((x, rts, chals.take (rts.length - 1)),
          chals[rts.length - 1]'(hlen ▸ hi)) ∈ tr_FS := by
        simpa only [htake] using hsteps (rts.length - 1) hi
      have hrts : ∀ rt ∈ rts, ans ≠ rt := by
        intro rt hrt heq
        subst heq
        exact hnot_fs ((x, rts, chals.take (rts.length - 1)),
          chals[rts.length - 1]'(hlen ▸ hi)) hlast_mem (by rwa [List.take_of_length_le hr])
      rw [bcsExtractTranscript_cons_of_ne decSym defaultSym d tr_MT msg chals hrts hchildren]
      exact hdoomed x hx rts chals hr ⟨hlen, hsteps⟩

/-- Candidate challenges at challenge-list index `idx` already anticipated by existing Fiat–Shamir
trace entries (used to bound out-of-order Fiat–Shamir chain guessing). -/
@[expose] def fsOutOfOrderTargets {Stmt Chal : Type} (idx : ℕ)
    (tr_FS : List (BCSFSQuery Stmt Chal × Chal)) : List Chal :=
  tr_FS.filterMap fun ((_, _, prev), _) => prev[idx]?

theorem length_fsOutOfOrderTargets_le {Stmt Chal : Type} (idx : ℕ)
    (tr_FS : List (BCSFSQuery Stmt Chal × Chal)) :
    (fsOutOfOrderTargets idx tr_FS).length ≤ tr_FS.length :=
  List.length_filterMap_le _ _

/-- Structural analysis of a fresh Fiat–Shamir entry `((x₀, rts₀, prev₀), c)` violating
`BCSChainDoomed`: `x₀ ∈ S`, and either `c` hits `fsOutOfOrderTargets (rts₀.length - 1) tr_FS` (an
out-of-order longer chain was already queried) or the parent prefix is already `doomed` and `c`
violates `goodStep`. -/
private theorem bad_fs_step_cases {r d : ℕ} {Stmt Sym Chal : Type} {S : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hstep : ∀ x ∈ S, ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    {decSym : List Bool → Sym} {defaultSym : Sym}
    {tr_MT : List (List Bool × List Bool)} {tr_FS : List (BCSFSQuery Stmt Chal × Chal)}
    (hdoomed : BCSChainDoomed r d S doomed decSym defaultSym tr_MT tr_FS)
    {x₀ : Stmt} {rts₀ : List (List Bool)} {prev₀ : List Chal} {c : Chal}
    (hbad : ¬ BCSChainDoomed r d S doomed decSym defaultSym tr_MT
      (((x₀, rts₀, prev₀), c) :: tr_FS)) :
    x₀ ∈ S ∧
      ((let pref₀ := bcsExtractTranscript decSym defaultSym d tr_MT
          (rts₀.take (rts₀.length - 1)) prev₀
        let π₀ := bcsExtractTable decSym defaultSym tr_MT d ((rts₀[rts₀.length - 1]?).getD [])
        doomed x₀ pref₀ ∧ ¬ goodStep x₀ pref₀ π₀ c) ∨
        c ∈ fsOutOfOrderTargets (rts₀.length - 1) tr_FS) := by
  unfold BCSChainDoomed at hbad
  push Not at hbad
  obtain ⟨x, hx, rts, chals, hr, ⟨hlen, hsteps⟩, hnot_doomed⟩ := hbad
  have hex_new : ∃ (i₀ : ℕ) (hi₀ : i₀ < rts.length),
      ((x, rts.take (i₀ + 1), chals.take i₀), chals[i₀]'(hlen ▸ hi₀)) =
        ((x₀, rts₀, prev₀), c) := by
    by_contra hall_old
    push Not at hall_old
    have hold_chain : ValidFSChain tr_FS x rts chals := ⟨hlen, fun i hi => by
      rcases List.mem_cons.mp (hsteps i hi) with heq | hmem
      · exact False.elim (hall_old i hi heq)
      · exact hmem⟩
    exact hnot_doomed (hdoomed x hx rts chals hr hold_chain)
  obtain ⟨i₀, hi₀, heq₀⟩ := hex_new
  rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at heq₀
  obtain ⟨⟨hx_eq, ⟨hrts₀_eq, hprev₀_eq⟩⟩, hc_eq⟩ := heq₀
  subst hx_eq
  have hrts₀_len : rts₀.length = i₀ + 1 := by
    rw [← hrts₀_eq, List.length_take_of_le (Nat.succ_le_of_lt hi₀)]
  have hi₀_eq : rts₀.length - 1 = i₀ := by omega
  refine ⟨hx, ?_⟩
  by_cases hmore : i₀ + 1 < rts.length
  · right
    have hstep_next := hsteps (i₀ + 1) hmore
    have hne_next : ((x, rts.take (i₀ + 2), chals.take (i₀ + 1)),
        chals[i₀ + 1]'(hlen ▸ hmore)) ≠ ((x, rts₀, prev₀), c) := by
      intro hsame
      have hlen_eq := congrArg (fun e : BCSFSQuery Stmt Chal × Chal => e.1.2.1.length) hsame
      dsimp only at hlen_eq
      rw [List.length_take_of_le (Nat.succ_le_of_lt hmore), hrts₀_len] at hlen_eq
      omega
    have hmem_next : ((x, rts.take (i₀ + 2), chals.take (i₀ + 1)),
        chals[i₀ + 1]'(hlen ▸ hmore)) ∈ tr_FS :=
      (List.mem_cons.mp hstep_next).resolve_left hne_next
    rw [hi₀_eq, fsOutOfOrderTargets, List.mem_filterMap]
    refine ⟨((x, rts.take (i₀ + 2), chals.take (i₀ + 1)), chals[i₀ + 1]'(hlen ▸ hmore)),
      hmem_next, ?_⟩
    have hi₀_ch : i₀ < (chals.take (i₀ + 1)).length := by
      rw [List.length_take_of_le (by omega)]
      omega
    dsimp only
    rw [List.getElem?_eq_getElem hi₀_ch, List.getElem_take, hc_eq]
  · left
    have hlast : i₀ + 1 = rts.length := by omega
    have hrts_eq : rts = rts₀ := by
      rw [← hrts₀_eq, hlast, List.take_length]
    have hparent : ValidFSChain tr_FS x (rts₀.take i₀) prev₀ := by
      subst hrts_eq hprev₀_eq
      refine ⟨by simp [List.length_take_of_le (Nat.le_of_lt hi₀),
          List.length_take_of_le (hlen ▸ Nat.le_of_lt hi₀)], fun j hj => ?_⟩
      rw [List.length_take_of_le (Nat.le_of_lt hi₀)] at hj
      have hj_rts : j < rts.length := Nat.lt_trans hj hi₀
      have htake_rts : (rts.take i₀).take (j + 1) = rts.take (j + 1) := by
        rw [List.take_take, Nat.min_eq_left (Nat.succ_le_of_lt hj)]
      have htake_ch : (chals.take i₀).take j = chals.take j := by
        rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hj)]
      have hget_ch : (chals.take i₀)[j]'(by
          rw [List.length_take_of_le (hlen ▸ Nat.le_of_lt hi₀)]; exact hj) =
          chals[j]'(hlen ▸ hj_rts) := List.getElem_take
      rw [htake_rts, htake_ch, hget_ch]
      have hstep_j := hsteps j hj_rts
      refine (List.mem_cons.mp hstep_j).resolve_left ?_
      intro hsame
      have hlen_eq := congrArg (fun e : BCSFSQuery Stmt Chal × Chal => e.1.2.1.length) hsame
      dsimp only at hlen_eq
      rw [List.length_take_of_le (Nat.succ_le_of_lt hj_rts), hrts₀_len] at hlen_eq
      omega
    have hparent_doomed : doomed x
        (bcsExtractTranscript decSym defaultSym d tr_MT (rts₀.take (rts₀.length - 1)) prev₀) := by
      rw [hi₀_eq]
      exact hdoomed x hx (rts₀.take i₀) prev₀
        ((List.length_take_le i₀ rts₀).trans (by omega)) hparent
    refine ⟨hparent_doomed, fun hgood_c => hnot_doomed ?_⟩
    have hrts_split : rts =
        rts₀.take (rts₀.length - 1) ++ [(rts₀[rts₀.length - 1]?).getD []] := by
      subst hrts_eq
      rw [hi₀_eq]
      have h1 := List.take_succ_eq_append_getElem hi₀
      rw [hlast, List.take_length] at h1
      have hlastD : (rts[i₀]?).getD [] = rts[i₀] := by
        rw [List.getElem?_eq_getElem hi₀, Option.getD_some]
      rw [hlastD]
      exact h1
    have hchals_split : chals = prev₀ ++ [c] := by
      rw [← hprev₀_eq, ← hc_eq]
      have hi₀_ch : i₀ < chals.length := hlen ▸ hi₀
      have h1 := List.take_succ_eq_append_getElem hi₀_ch
      rw [hlast, hlen, List.take_length] at h1
      exact h1
    have hlen_parent : (rts₀.take (rts₀.length - 1)).length = prev₀.length := by
      rw [hi₀_eq, ← hprev₀_eq, List.length_take_of_le (by omega),
        List.length_take_of_le (by omega)]
    rw [hrts_split, hchals_split,
      bcsExtractTranscript_append_singleton decSym defaultSym d tr_MT hlen_parent]
    exact hstep x hx _ _ c hparent_doomed hgood_c

/-- **Single-step Fiat–Shamir bad-event bound**: from a state `(tr_MT, tr_FS)` satisfying
`BCSChainDoomed`, one call to `memoize (fun _ => PMF.uniformOfFintype Chal)` violates
`BCSChainDoomed` with probability at most `ε_rbr + tr_FS.length * (1 / Fintype.card Chal)`. -/
theorem toOuterMeasure_memoize_not_bcsChainDoomed_step {r d : ℕ} {Stmt Sym Chal : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {ε_rbr : ℝ≥0∞}
    (hstep : ∀ x ∈ S, ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (hescape : ∀ x ∈ S, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool)) (fsq : BCSFSQuery Stmt Chal)
    {tr_FS : List (BCSFSQuery Stmt Chal × Chal)}
    (hdoomed : BCSChainDoomed r d S doomed decSym defaultSym tr_MT tr_FS) :
    (memoize (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal) fsq tr_FS).toOuterMeasure
      {out | ¬ BCSChainDoomed r d S doomed decSym defaultSym tr_MT out.2} ≤
      ε_rbr + (tr_FS.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal) := by
  rcases fsq with ⟨x₀, rts₀, prev₀⟩
  cases hlookup : tr_FS.lookup (x₀, rts₀, prev₀) with
  | some c₀ =>
    rw [memoize_of_some _ _ _ _ hlookup, PMF.monad_pure_eq_pure, PMF.toOuterMeasure_pure_apply]
    simp [hdoomed]
  | none =>
    rw [memoize_of_none _ _ _ hlookup]
    change ((PMF.uniformOfFintype Chal).map
      (fun c => (c, ((x₀, rts₀, prev₀), c) :: tr_FS))).toOuterMeasure
      {out | ¬ BCSChainDoomed r d S doomed decSym defaultSym tr_MT out.2} ≤ _
    rw [PMF.toOuterMeasure_map_apply]
    by_cases hx₀ : x₀ ∈ S
    · set pref₀ := bcsExtractTranscript decSym defaultSym d tr_MT
        (rts₀.take (rts₀.length - 1)) prev₀
      set π₀ := bcsExtractTable decSym defaultSym tr_MT d ((rts₀[rts₀.length - 1]?).getD [])
      set E₁ : Set Chal := {c | doomed x₀ pref₀ ∧ ¬ goodStep x₀ pref₀ π₀ c}
      set E₂ : Set Chal := {c | c ∈ fsOutOfOrderTargets (rts₀.length - 1) tr_FS}
      calc (PMF.uniformOfFintype Chal).toOuterMeasure
            {c | ¬ BCSChainDoomed r d S doomed decSym defaultSym tr_MT
              (((x₀, rts₀, prev₀), c) :: tr_FS)}
          ≤ (PMF.uniformOfFintype Chal).toOuterMeasure (E₁ ∪ E₂) := by
            refine (PMF.uniformOfFintype Chal).toOuterMeasure.mono fun c hc => ?_
            exact (bad_fs_step_cases hstep hdoomed hc).2
        _ ≤ (PMF.uniformOfFintype Chal).toOuterMeasure E₁ +
              (PMF.uniformOfFintype Chal).toOuterMeasure E₂ :=
            MeasureTheory.measure_union_le E₁ E₂
        _ ≤ ε_rbr + (tr_FS.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal) := by
            refine add_le_add ?_ ?_
            · by_cases hd₀ : doomed x₀ pref₀
              · calc (PMF.uniformOfFintype Chal).toOuterMeasure E₁
                    ≤ (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x₀ pref₀ π₀ c} :=
                      (PMF.uniformOfFintype Chal).toOuterMeasure.mono fun _ hc => hc.2
                  _ ≤ ε_rbr := hescape x₀ hx₀ pref₀ π₀ hd₀
              · have hempty : E₁ = ∅ := by
                  ext c
                  simp [E₁, hd₀]
                simp [hempty]
            · calc (PMF.uniformOfFintype Chal).toOuterMeasure E₂
                  ≤ ((fsOutOfOrderTargets (rts₀.length - 1) tr_FS).length : ℝ≥0∞) *
                      ((1 : ℝ≥0∞) / Fintype.card Chal) :=
                    PMF.toOuterMeasure_uniformOfFintype_mem_list_le _
                _ ≤ (tr_FS.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal) := by
                    gcongr
                    exact_mod_cast length_fsOutOfOrderTargets_le _ tr_FS
    · have hempty : {c : Chal | ¬ BCSChainDoomed r d S doomed decSym defaultSym tr_MT
          (((x₀, rts₀, prev₀), c) :: tr_FS)} = ∅ := by
        ext c
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hbad
        exact hx₀ (bad_fs_step_cases hstep hdoomed hbad).1
      simp [hempty]

/-! #### Two-channel query costs and accumulated bad-state bound -/

/-- Cost of a BCS oracle call on the Merkle hash channel (`Sum.inl`). -/
@[expose] def bcsMTCost {Stmt Chal : Type} : List Bool ⊕ BCSFSQuery Stmt Chal → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Cost of a BCS oracle call on the Fiat–Shamir challenge channel (`Sum.inr`). -/
@[expose] def bcsFSCost {Stmt Chal : Type} : List Bool ⊕ BCSFSQuery Stmt Chal → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-! The sticky-bad wrapper `bcsStickyMemoize` runs `bcsMemoize` and records in a flag whether
any step was bad. Forgetting the flag recovers `bcsMemoize`
(`run_interpret_bcsStickyMemoize_map`), so the bad-state bounds of `bcsMemoize` below follow from
those of the wrapper. -/

section StickyBad

variable {r d : ℕ} {Stmt Sym Chal : Type}

/-- Single-step bad transition predicate for the sticky-bad wrapper used in prover-trace knowledge
extraction: either the next state violates `BCSGoodState`, or a fresh Merkle entry hit
`bcsForbiddenDigests r st` (which includes the first `r` roots of every Fiat–Shamir query in `st.2`
and all child digests of `st.1`). -/
private def BCSStepBad (r d : ℕ) {Stmt Sym Chal : Type} (S : Set Stmt)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (st st' : BCSTraceState Stmt Chal) : Prop :=
  ¬ BCSGoodState r d S doomed decSym defaultSym st' ∨
    ∃ msg ans, st'.1 = (msg, ans) :: st.1 ∧ ans ∈ bcsForbiddenDigests r st

open Classical in
private noncomputable def bcsStickyMemoize (r d : ℕ) {Stmt Sym Chal : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    (S : Set Stmt) (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (q : List Bool ⊕ BCSFSQuery Stmt Chal) :
    StateT (BCSTraceState Stmt Chal × Bool) PMF (BCSROMSpec Stmt Chal q) :=
  fun (st, badFlag) =>
    (bcsMemoize σ q st).map fun (ans, st') =>
      (ans, (st', badFlag || decide (BCSStepBad r d S doomed decSym defaultSym st st')))

private def BCSStickyBad (r d : ℕ) {Stmt Sym Chal : Type} (S : Set Stmt)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (p : BCSTraceState Stmt Chal × Bool) : Prop :=
  p.2 = true ∨ ¬ BCSGoodState r d S doomed decSym defaultSym p.1

private theorem run_interpret_bcsStickyMemoize_map {Stmt Sym Chal γ : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    (S : Set Stmt) (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (prog : OracleComp (BCSROMSpec Stmt Chal) γ)
    (st : BCSTraceState Stmt Chal) (badFlag : Bool) :
    ((OracleComp.interpret (bcsStickyMemoize r d S doomed decSym defaultSym σ) prog).run
        (st, badFlag)).map (fun (res, p') => (res, p'.1)) =
      (OracleComp.interpret (bcsMemoize σ) prog).run st := by
  refine OracleComp.run_interpret_map_state
    (bcsStickyMemoize r d S doomed decSym defaultSym σ) (bcsMemoize σ) Prod.fst ?_ prog
    (st, badFlag)
  rintro q ⟨st₀, flag₀⟩
  dsimp only [bcsStickyMemoize]
  simp [Function.comp_def, PMF.map, PMF.bind_pure]

private theorem toOuterMeasure_bcsStickyMemoize_step [BEq Stmt] [BEq Chal]
    [Fintype Chal] [Nonempty Chal]
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {ε_rbr : ℝ≥0∞}
    (hstep : ∀ x ∈ S, ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (hescape : ∀ x ∈ S, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (q : List Bool ⊕ BCSFSQuery Stmt Chal) {p : BCSTraceState Stmt Chal × Bool}
    (hp : ¬ BCSStickyBad r d S doomed decSym defaultSym p) :
    (bcsStickyMemoize r d S doomed decSym defaultSym σ q p).toOuterMeasure
        {out | BCSStickyBad r d S doomed decSym defaultSym out.2} ≤
      (bcsMTCost q : ℝ≥0∞) *
        (((3 * p.1.1.length + r * p.1.2.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) +
      (bcsFSCost q : ℝ≥0∞) *
        (ε_rbr + (p.1.2.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) := by
  classical
  rcases p with ⟨⟨tr_MT, tr_FS⟩, badFlag⟩
  unfold BCSStickyBad at hp
  push Not at hp
  obtain ⟨hflag, hst⟩ := hp
  have hflag_false : badFlag = false := Bool.eq_false_iff.mpr hflag
  subst hflag_false
  cases q with
  | inl msg =>
    simp only [bcsMTCost, bcsFSCost, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, add_zero,
      bcsStickyMemoize, bcsMemoize, PMF.map_comp, Function.comp_def, PMF.toOuterMeasure_map_apply]
    cases hlookup : tr_MT.lookup msg with
    | some ans =>
      rw [memoize_of_some _ _ _ _ hlookup, PMF.monad_pure_eq_pure, PMF.toOuterMeasure_pure_apply]
      simp [BCSStickyBad, BCSStepBad, hst]
    | none =>
      rw [memoize_of_none _ _ _ hlookup]
      change ((BitString.uniformList σ).map (fun ans => (ans, (msg, ans) :: tr_MT))).toOuterMeasure
        _ ≤ _
      rw [PMF.toOuterMeasure_map_apply]
      calc (BitString.uniformList σ).toOuterMeasure _
          ≤ (BitString.uniformList σ).toOuterMeasure
            {ans | ans ∈ bcsForbiddenDigests r (tr_MT, tr_FS)} := by
            refine (BitString.uniformList σ).toOuterMeasure.mono fun ans hbad => ?_
            rcases hbad with hflag_eq | hnot_good
            · dsimp only at hflag_eq
              rw [Bool.false_or] at hflag_eq
              rcases of_decide_eq_true hflag_eq with hnot_good | ⟨msg', ans', hcons, hmem_forb⟩
              · exact mem_bcsForbiddenDigests_of_not_bcsGoodState_cons hst hnot_good
              · rw [List.cons.injEq, Prod.mk.injEq] at hcons
                rcases hcons with ⟨⟨_, rfl⟩, _⟩
                exact hmem_forb
            · exact mem_bcsForbiddenDigests_of_not_bcsGoodState_cons hst hnot_good
        _ ≤ ((bcsForbiddenDigests r (tr_MT, tr_FS)).length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) :=
            toOuterMeasure_uniformList_mem_list_le σ (bcsForbiddenDigests r (tr_MT, tr_FS))
        _ ≤ ((3 * tr_MT.length + r * tr_FS.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) := by
            gcongr
            exact_mod_cast length_bcsForbiddenDigests_le r (tr_MT, tr_FS)
  | inr fsq =>
    simp only [bcsMTCost, bcsFSCost, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, zero_add,
      bcsStickyMemoize, bcsMemoize, PMF.map_comp, Function.comp_def, PMF.toOuterMeasure_map_apply]
    have hno_cons : ¬ ∃ msg' ans', tr_MT = (msg', ans') :: tr_MT ∧
        ans' ∈ bcsForbiddenDigests r (tr_MT, tr_FS) := by
      rintro ⟨msg', ans', heq, -⟩
      have hlen := congrArg List.length heq
      simp at hlen
    calc (memoize (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal)
            fsq tr_FS).toOuterMeasure _
        ≤ (memoize (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal)
            fsq tr_FS).toOuterMeasure
          {x | ¬ BCSChainDoomed r d S doomed decSym defaultSym tr_MT x.2} := by
          refine (memoize (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal)
            fsq tr_FS).toOuterMeasure.mono fun x hbad hfs => ?_
          rcases hbad with hflag_eq | hnot_good
          · dsimp only at hflag_eq
            rw [Bool.false_or] at hflag_eq
            rcases of_decide_eq_true hflag_eq with hnot_good | hcons
            · exact hnot_good ⟨hst.1, hfs⟩
            · exact hno_cons hcons
          · exact hnot_good ⟨hst.1, hfs⟩
      _ ≤ ε_rbr + (tr_FS.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal) :=
          toOuterMeasure_memoize_not_bcsChainDoomed_step hstep hescape decSym defaultSym tr_MT fsq
            hst.2

private theorem toOuterMeasure_run_bcsStickyMemoize_bad_le {γ : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {ε_rbr : ℝ≥0∞}
    (hinit : ∀ x ∈ S, doomed x [])
    (hstep : ∀ x ∈ S, ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (hescape : ∀ x ∈ S, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    {prog : OracleComp (BCSROMSpec Stmt Chal) γ} {Q_MT Q_FS : ℕ}
    (hMT : IsCostBounded bcsMTCost prog Q_MT)
    (hFS : IsCostBounded bcsFSCost prog Q_FS) :
    ((OracleComp.interpret (bcsStickyMemoize r d S doomed decSym defaultSym σ) prog).run
        (([], []), false)).toOuterMeasure
      {out | BCSStickyBad r d S doomed decSym defaultSym out.2} ≤
      (Q_FS : ℝ≥0∞) * (ε_rbr + (Q_FS : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        (Q_MT : ℝ≥0∞) * (((3 * Q_MT + r * Q_FS : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  have h := OracleComp.toOuterMeasure_bad_le_two_budgets
    (handler := bcsStickyMemoize r d S doomed decSym defaultSym σ)
    (bad := BCSStickyBad r d S doomed decSym defaultSym)
    bcsMTCost bcsFSCost
    (fun p => ((3 * p.1.1.length + r * p.1.2.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ))
    (fun p => ε_rbr + (p.1.2.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal))
    (3 * ((1 : ℝ≥0∞) / 2 ^ σ))
    ((r : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ))
    0
    ((1 : ℝ≥0∞) / Fintype.card Chal)
    (fun q p hp => toOuterMeasure_bcsStickyMemoize_step hstep hescape decSym defaultSym σ q hp)
    (fun q p _ x hx _ => by
      rcases p with ⟨⟨tr_MT, tr_FS⟩, badFlag⟩
      cases q with
      | inl msg =>
        simp only [bcsStickyMemoize, bcsMemoize, PMF.map_comp, Function.comp_def,
          PMF.mem_support_map_iff] at hx
        rcases hx with ⟨⟨ans, tr_MT'⟩, hmem, rfl⟩
        have hlen := length_le_of_mem_support_memoize _ msg tr_MT hmem
        simp only [bcsMTCost, bcsFSCost, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, add_zero]
        calc ((3 * tr_MT'.length + r * tr_FS.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)
            ≤ ((3 * (tr_MT.length + 1) + r * tr_FS.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) := by
              gcongr
          _ = ((3 * tr_MT.length + r * tr_FS.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) +
                3 * ((1 : ℝ≥0∞) / 2 ^ σ) := by
              push_cast
              ring
      | inr fsq =>
        simp only [bcsStickyMemoize, bcsMemoize, PMF.map_comp, Function.comp_def,
          PMF.mem_support_map_iff] at hx
        rcases hx with ⟨⟨c, tr_FS'⟩, hmem, rfl⟩
        have hlen := length_le_of_mem_support_memoize _ fsq tr_FS hmem
        simp only [bcsMTCost, bcsFSCost, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, add_zero]
        calc ((3 * tr_MT.length + r * tr_FS'.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)
            ≤ ((3 * tr_MT.length + r * (tr_FS.length + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) := by
              gcongr
          _ = ((3 * tr_MT.length + r * tr_FS.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) +
                (r : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) := by
              push_cast
              ring)
    (fun q p _ x hx _ => by
      rcases p with ⟨⟨tr_MT, tr_FS⟩, badFlag⟩
      cases q with
      | inl msg =>
        simp only [bcsStickyMemoize, bcsMemoize, PMF.map_comp, Function.comp_def,
          PMF.mem_support_map_iff] at hx
        rcases hx with ⟨⟨ans, tr_MT'⟩, _, rfl⟩
        simp [bcsMTCost, bcsFSCost]
      | inr fsq =>
        simp only [bcsStickyMemoize, bcsMemoize, PMF.map_comp, Function.comp_def,
          PMF.mem_support_map_iff] at hx
        rcases hx with ⟨⟨c, tr_FS'⟩, hmem, rfl⟩
        have hlen := length_le_of_mem_support_memoize _ fsq tr_FS hmem
        simp only [bcsMTCost, bcsFSCost, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, add_zero]
        calc ε_rbr + (tr_FS'.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)
            ≤ ε_rbr + ((tr_FS.length + 1 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal) := by
              gcongr
          _ = ε_rbr + (tr_FS.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal) +
                ((1 : ℝ≥0∞) / Fintype.card Chal) := by
              push_cast
              ring)
    hMT hFS (s := (([], []), false))
    (by
      rintro (hflag | hbad)
      · cases hflag
      · exact hbad (bcsGoodState_nil r d hinit decSym defaultSym))
  refine h.trans (le_of_eq ?_)
  simp only [List.length_nil, mul_zero, add_zero]
  push_cast
  ring

end StickyBad

/-- **Single-step bad-state bound for `bcsMemoize`**: from a good state `st`, a call `q` violates
`BCSGoodState` with probability at most
`bcsMTCost q * ((3 * st.1.length + r * st.2.length) * (1 / 2 ^ σ)) +`
`bcsFSCost q * (ε_rbr + st.2.length * (1 / Fintype.card Chal))`. -/
theorem toOuterMeasure_bcsMemoize_not_goodState_step {r d : ℕ} {Stmt Sym Chal : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {ε_rbr : ℝ≥0∞}
    (hstep : ∀ x ∈ S, ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (hescape : ∀ x ∈ S, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (q : List Bool ⊕ BCSFSQuery Stmt Chal) {st : BCSTraceState Stmt Chal}
    (hst : BCSGoodState r d S doomed decSym defaultSym st) :
    (bcsMemoize σ q st).toOuterMeasure
        {out | ¬ BCSGoodState r d S doomed decSym defaultSym out.2} ≤
      (bcsMTCost q : ℝ≥0∞) *
        (((3 * st.1.length + r * st.2.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) +
      (bcsFSCost q : ℝ≥0∞) *
        (ε_rbr + (st.2.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) := by
  rcases st with ⟨tr_MT, tr_FS⟩
  have h := toOuterMeasure_bcsStickyMemoize_step (r := r) hstep hescape decSym defaultSym σ q
    (p := ((tr_MT, tr_FS), false)) fun hbad => Or.elim hbad Bool.false_ne_true (· hst)
  dsimp only [bcsStickyMemoize] at h
  rw [PMF.toOuterMeasure_map_apply] at h
  exact le_trans ((bcsMemoize σ q (tr_MT, tr_FS)).toOuterMeasure.mono
    fun out hout => Or.inr hout) h

/-- **Accumulated bad-state bound for `bcsMemoize`**: any program with Merkle query budget `Q_MT`
and Fiat–Shamir query budget `Q_FS` starting from `([], [])` violates `BCSGoodState` with
probability at most
`Q_FS * (ε_rbr + Q_FS * (1 / Fintype.card Chal)) + Q_MT * ((3 * Q_MT + r * Q_FS) * (1 / 2 ^ σ))`.
-/
theorem toOuterMeasure_run_bcsMemoize_not_goodState_le {r d : ℕ} {Stmt Sym Chal β : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {ε_rbr : ℝ≥0∞}
    (hinit : ∀ x ∈ S, doomed x [])
    (hstep : ∀ x ∈ S, ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (hescape : ∀ x ∈ S, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    {prog : OracleComp (BCSROMSpec Stmt Chal) β} {Q_MT Q_FS : ℕ}
    (hMT : IsCostBounded bcsMTCost prog Q_MT)
    (hFS : IsCostBounded bcsFSCost prog Q_FS) :
    ((OracleComp.interpret (bcsMemoize σ) prog).run ([], [])).toOuterMeasure
        {out | ¬ BCSGoodState r d S doomed decSym defaultSym out.2} ≤
      (Q_FS : ℝ≥0∞) * (ε_rbr + (Q_FS : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        (Q_MT : ℝ≥0∞) * (((3 * Q_MT + r * Q_FS : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [← run_interpret_bcsStickyMemoize_map (r := r) S doomed decSym defaultSym σ prog ([], [])
    false, PMF.toOuterMeasure_map_apply]
  refine le_trans ?_
    (toOuterMeasure_run_bcsStickyMemoize_bad_le hinit hstep hescape decSym defaultSym σ hMT hFS)
  exact (PMF.toOuterMeasure _).mono fun out hout => Or.inr hout

/-! ### Part 4: Query budgets, adaptive ROM soundness, and straight-line knowledge soundness -/

section CostBounds

variable {r d : ℕ} {Stmt Wit Sym Chal β : Type}

/-- Any `MerkleHashSpec` program lifted via `liftLeft` makes `0` Fiat–Shamir calls. -/
theorem isCostBounded_bcsFSCost_liftLeft (prog : OracleComp MerkleHashSpec β) :
    IsCostBounded (bcsFSCost (Stmt := Stmt) (Chal := Chal))
      (OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal) prog) 0 := by
  induction prog with
  | pure a => exact .pure a 0
  | liftBind q cont ih =>
    change IsCostBounded bcsFSCost
      (OracleComp.query (spec := BCSROMSpec Stmt Chal) (.inl q) >>=
        fun a => OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal) (cont a)) 0
    exact IsCostBounded.liftBind (cost := bcsFSCost) (Sum.inl q) _ 0 ih

/-- Any `IsQueryBounded prog k` over `MerkleHashSpec` lifts via `liftLeft` to
`IsCostBounded bcsMTCost (liftLeft prog) k`. -/
theorem isCostBounded_bcsMTCost_liftLeft {prog : OracleComp MerkleHashSpec β} {k : ℕ}
    (h : IsQueryBounded prog k) :
    IsCostBounded (bcsMTCost (Stmt := Stmt) (Chal := Chal))
      (OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal) prog) k := by
  induction h with
  | pure a n => exact .pure a n
  | liftBind q cont n _ ih =>
    change IsCostBounded bcsMTCost
      (OracleComp.query (spec := BCSROMSpec Stmt Chal) (.inl q) >>=
        fun a => OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal) (cont a)) (n + 1)
    exact IsCostBounded.liftBind (cost := bcsMTCost) (Sum.inl q) _ n ih

/-- Any `BCSFSSpec` program lifted via `liftRight` makes `0` Merkle hash calls. -/
theorem isCostBounded_bcsMTCost_liftRight (prog : OracleComp (BCSFSSpec Stmt Chal) β) :
    IsCostBounded (bcsMTCost (Stmt := Stmt) (Chal := Chal))
      (OracleComp.liftRight (spec₁ := MerkleHashSpec) prog) 0 := by
  induction prog with
  | pure a => exact .pure a 0
  | liftBind q cont ih =>
    change IsCostBounded bcsMTCost
      (OracleComp.query (spec := BCSROMSpec Stmt Chal) (.inr q) >>=
        fun a => OracleComp.liftRight (spec₁ := MerkleHashSpec) (cont a)) 0
    exact IsCostBounded.liftBind (cost := bcsMTCost) (Sum.inr q) _ 0 ih

/-- Any `IsQueryBounded prog k` over `BCSFSSpec` lifts via `liftRight` to
`IsCostBounded bcsFSCost (liftRight prog) k`. -/
theorem isCostBounded_bcsFSCost_liftRight {prog : OracleComp (BCSFSSpec Stmt Chal) β} {k : ℕ}
    (h : IsQueryBounded prog k) :
    IsCostBounded (bcsFSCost (Stmt := Stmt) (Chal := Chal))
      (OracleComp.liftRight (spec₁ := MerkleHashSpec) prog) k := by
  induction h with
  | pure a n => exact .pure a n
  | liftBind q cont n _ ih =>
    change IsCostBounded bcsFSCost
      (OracleComp.query (spec := BCSROMSpec Stmt Chal) (.inr q) >>=
        fun a => OracleComp.liftRight (spec₁ := MerkleHashSpec) (cont a)) (n + 1)
    exact IsCostBounded.liftBind (cost := bcsFSCost) (Sum.inr q) _ n ih

private theorem isQueryBounded_bcsChallengesAuxProg (x : Stmt) (roots : Fin r → List Bool) :
    ∀ (m : ℕ) (hm : m ≤ r), IsQueryBounded (bcsChallengesAuxProg (Chal := Chal) x roots m hm) m
  | 0, _ => .pure Fin.elim0 0
  | m + 1, hm => by
    unfold bcsChallengesAuxProg
    have hprev := isQueryBounded_bcsChallengesAuxProg x roots m (Nat.le_of_succ_le hm)
    have hq : IsQueryBounded
        (bcsChallengesAuxProg x roots m (Nat.le_of_succ_le hm) >>= fun prev =>
          OracleComp.query (spec := BCSFSSpec Stmt Chal)
            (x, rootPrefix roots ⟨m, hm⟩, List.ofFn prev)) (m + 1) :=
      hprev.bind fun prev =>
        IsCostBounded.query (cost := fun _ => 1) (x, rootPrefix roots ⟨m, hm⟩, List.ofFn prev)
    simpa only [Nat.add_zero, bind_assoc] using
      hprev.bind fun prev =>
        (IsCostBounded.query (cost := fun _ => 1)
          (x, rootPrefix roots ⟨m, hm⟩, List.ofFn prev)).bind fun c =>
            IsCostBounded.pure (snocFin prev c) 0

/-- `bcsChallengesProg x roots` makes at most `r` Fiat–Shamir queries. -/
theorem isQueryBounded_bcsChallengesProg (x : Stmt) (roots : Fin r → List Bool) :
    IsQueryBounded (bcsChallengesProg (Chal := Chal) x roots) r :=
  isQueryBounded_bcsChallengesAuxProg x roots r le_rfl

/-- `bcsVerifyROM iop encSym x prf` makes at most `r` Fiat–Shamir queries for every statement `x`
and proof `prf`. -/
theorem isCostBounded_bcsFSCost_bcsVerifyROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (prf : BCSProof r Sym) :
    IsCostBounded bcsFSCost (bcsVerifyROM iop encSym x prf) r := by
  unfold bcsVerifyROM
  simpa only [Nat.add_zero] using
    (isCostBounded_bcsFSCost_liftRight (isQueryBounded_bcsChallengesProg x prf.roots)).bind
      fun chals => isCostBounded_bcsFSCost_liftLeft (bcsVerifyOpeningsProg iop encSym x prf chals)

/-- Total number of Merkle hash queries needed to verify every opening in `openings` (one leaf hash
plus `path.length` internal-node hashes per opening). -/
@[expose] def bcsOpeningsMerkleQueries {Sym : Type} (openings : List (BCSOpening Sym)) : ℕ :=
  (openings.map fun (_, path) => path.length + 1).sum

private theorem isQueryBounded_zip_mapM_merkleVerifyProg (encSym : Sym → List Bool)
    (roots : Fin r → List Bool) (qs : List (Fin r × Fin (2 ^ d)))
    (ops : List (BCSOpening Sym)) :
    IsQueryBounded
      ((qs.zip ops).mapM fun ((j, idx), (val, path)) =>
        merkleVerifyProg d (roots j) idx.val (encSym val) path)
      (bcsOpeningsMerkleQueries ops) := by
  induction qs generalizing ops with
  | nil => exact .pure [] _
  | cons q qs' ih =>
    cases ops with
    | nil => exact .pure [] 0
    | cons op ops' =>
      rcases q with ⟨j, idx⟩
      rcases op with ⟨val, path⟩
      have hsum : bcsOpeningsMerkleQueries ((val, path) :: ops') =
          (path.length + 1) + bcsOpeningsMerkleQueries ops' := by
        simp [bcsOpeningsMerkleQueries]
      rw [List.zip_cons_cons, List.mapM_cons, hsum]
      have hhd := isQueryBounded_merkleVerifyProg d (roots j) idx.val (encSym val) path
      have htl := ih ops'
      simpa only [Nat.add_zero] using
        hhd.bind fun c => htl.bind fun cs => IsCostBounded.pure (c :: cs) 0

/-- `bcsVerifyROM iop encSym x prf` makes at most `bcsOpeningsMerkleQueries prf.openings` Merkle
hash queries, independently of the random Fiat–Shamir challenges. -/
theorem isCostBounded_bcsMTCost_bcsVerifyROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (x : Stmt) (prf : BCSProof r Sym) :
    IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf)
      (bcsOpeningsMerkleQueries prf.openings) := by
  unfold bcsVerifyROM
  simpa only [Nat.zero_add] using
    (isCostBounded_bcsMTCost_liftRight (bcsChallengesProg x prf.roots)).bind fun chals =>
      isCostBounded_bcsMTCost_liftLeft (by
        unfold bcsVerifyOpeningsProg
        simpa only [Nat.add_zero] using
          (isQueryBounded_zip_mapM_merkleVerifyProg encSym prf.roots (iop.queries x chals)
            prf.openings).bind fun checks => IsCostBounded.pure _ 0)

private theorem isQueryBounded_zip_mapM_merkleVerifyProg_of_le (encSym : Sym → List Bool)
    (roots : Fin r → List Bool) (qs : List (Fin r × Fin (2 ^ d)))
    (ops : List (BCSOpening Sym)) {q_iop L_path : ℕ}
    (hqs : qs.length ≤ q_iop) (hops : ∀ op ∈ ops, op.2.length ≤ L_path) :
    IsQueryBounded
      ((qs.zip ops).mapM fun ((j, idx), (val, path)) =>
        merkleVerifyProg d (roots j) idx.val (encSym val) path)
      (q_iop * (L_path + 1)) := by
  induction qs generalizing ops q_iop with
  | nil => exact .pure [] _
  | cons q qs' ih =>
    cases q_iop with
    | zero =>
      simp only [List.length_cons] at hqs
      omega
    | succ q_iop' =>
      cases ops with
      | nil => exact .pure [] _
      | cons op ops' =>
        rcases q with ⟨j, idx⟩
        rcases op with ⟨val, path⟩
        simp only [List.zip_cons_cons, List.mapM_cons]
        have hpath_le : path.length + 1 ≤ L_path + 1 :=
          Nat.add_le_add_right (hops (val, path) List.mem_cons_self) 1
        have hhd := (isQueryBounded_merkleVerifyProg d (roots j) idx.val (encSym val) path).mono
          hpath_le
        have htl := ih ops' (Nat.le_of_succ_le_succ hqs)
          (fun op' hop' => hops op' (List.mem_cons_of_mem _ hop'))
        have hsum : (L_path + 1) + q_iop' * (L_path + 1) = (q_iop' + 1) * (L_path + 1) := by ring
        rw [← hsum]
        simpa only [Nat.add_zero] using
          hhd.bind fun c => htl.bind fun cs => IsCostBounded.pure (c :: cs) 0

/-- If `iop.queries x chals` makes at most `q_iop` oracle queries for every `chals` and every
authentication path in `prf.openings` has length at most `L_path`, then
`bcsVerifyROM iop encSym x prf` makes at most `q_iop * (L_path + 1)` Merkle hash queries. -/
theorem isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le
    (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (encSym : Sym → List Bool)
    (x : Stmt) (prf : BCSProof r Sym) {q_iop L_path : ℕ}
    (hqs : ∀ chals, (iop.queries x chals).length ≤ q_iop)
    (hops : ∀ op ∈ prf.openings, op.2.length ≤ L_path) :
    IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf) (q_iop * (L_path + 1)) := by
  unfold bcsVerifyROM
  simpa only [Nat.zero_add] using
    (isCostBounded_bcsMTCost_liftRight (bcsChallengesProg x prf.roots)).bind fun chals =>
      isCostBounded_bcsMTCost_liftLeft (by
        unfold bcsVerifyOpeningsProg
        simpa only [Nat.add_zero] using
          (isQueryBounded_zip_mapM_merkleVerifyProg_of_le encSym prf.roots
            (iop.queries x chals) prf.openings (hqs chals) hops).bind fun checks =>
              IsCostBounded.pure _ 0)

end CostBounds

/-! #### Support invariants of `bcsMemoize`, `bcsChallengesProg`, and `bcsVerifyROM` -/

section SupportInvariants

variable {r d : ℕ} {Stmt Wit Sym Chal β : Type}

private theorem run_bcsMemoize_liftLeft [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    (σ : ℕ) (prog : OracleComp MerkleHashSpec β)
    (tr_MT : List (List Bool × List Bool)) (tr_FS : List (BCSFSQuery Stmt Chal × Chal)) :
    (OracleComp.interpret (bcsMemoize σ)
      (OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal) prog)).run (tr_MT, tr_FS) =
      ((OracleComp.interpret (memoize (fun _ : List Bool => BitString.uniformList σ)) prog).run
        tr_MT).map fun (res, tr_MT') => (res, (tr_MT', tr_FS)) := by
  induction prog using OracleComp.induction generalizing tr_MT with
  | pure a =>
    simp [PMF.monad_pure_eq_pure]
  | query_bind q cont ih =>
    simp only [liftLeft_bind, liftLeft_query, run_interpret_bind, run_interpret_query,
      bcsMemoize, PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind, Function.comp_def]
    refine congrArg (PMF.bind _) (funext fun ⟨ans, tr_MT₁⟩ => ih ans tr_MT₁)

private theorem run_bcsMemoize_liftRight [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    (σ : ℕ) (prog : OracleComp (BCSFSSpec Stmt Chal) β)
    (tr_MT : List (List Bool × List Bool)) (tr_FS : List (BCSFSQuery Stmt Chal × Chal)) :
    (OracleComp.interpret (bcsMemoize σ)
      (OracleComp.liftRight (spec₁ := MerkleHashSpec) prog)).run (tr_MT, tr_FS) =
      ((OracleComp.interpret (memoize (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal))
        prog).run tr_FS).map fun (res, tr_FS') => (res, (tr_MT, tr_FS')) := by
  induction prog using OracleComp.induction generalizing tr_FS with
  | pure a =>
    simp [PMF.monad_pure_eq_pure]
  | query_bind q cont ih =>
    simp only [liftRight_bind, liftRight_query, run_interpret_bind, run_interpret_query,
      bcsMemoize, PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind, Function.comp_def]
    refine congrArg (PMF.bind _) (funext fun ⟨c, tr_FS₁⟩ => ih c tr_FS₁)

private theorem mem_support_run_bcsMemoize_invariant [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal] (σ : ℕ) (prog : OracleComp (BCSROMSpec Stmt Chal) β)
    {st st' : BCSTraceState Stmt Chal} {res : β}
    (hnodup_MT : (st.1.map Prod.fst).Nodup)
    (hsupp_MT : ∀ e ∈ st.1, e.2 ∈ (BitString.uniformList σ).support)
    (hnodup_FS : (st.2.map Prod.fst).Nodup)
    (hsupp_FS : ∀ e ∈ st.2, e.2 ∈ (PMF.uniformOfFintype Chal).support)
    (hmem : (res, st') ∈ ((OracleComp.interpret (bcsMemoize σ) prog).run st).support) :
    (st'.1.map Prod.fst).Nodup ∧
      (∀ e ∈ st'.1, e.2 ∈ (BitString.uniformList σ).support) ∧
      (st'.2.map Prod.fst).Nodup ∧
      (∀ e ∈ st'.2, e.2 ∈ (PMF.uniformOfFintype Chal).support) := by
  induction prog using OracleComp.induction generalizing st with
  | pure a =>
    simp only [run_interpret_pure, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hnodup_MT, hsupp_MT, hnodup_FS, hsupp_FS⟩
  | query_bind q cont ih =>
    simp only [run_interpret_bind, run_interpret_query, PMF.monad_bind_eq_bind,
      PMF.mem_support_bind_iff] at hmem
    rcases hmem with ⟨⟨ans, st₁⟩, hans, hcont⟩
    rcases st with ⟨tr_MT, tr_FS⟩
    cases q with
    | inl msg =>
      simp only [bcsMemoize, PMF.mem_support_map_iff] at hans
      obtain ⟨⟨ans', tr_MT₁⟩, hmt, hpair⟩ := hans
      dsimp only at hpair
      rw [Prod.mk.injEq] at hpair
      rcases hpair with ⟨rfl, rfl⟩
      obtain ⟨-, -, hnodup_MT₁, hsupp_MT₁⟩ :=
        mem_support_memoize_nodup (fun _ : List Bool => BitString.uniformList σ) msg
          hnodup_MT hsupp_MT hmt
      exact @ih ans' (tr_MT₁, tr_FS) hnodup_MT₁ hsupp_MT₁ hnodup_FS hsupp_FS hcont
    | inr fsq =>
      simp only [bcsMemoize, PMF.mem_support_map_iff] at hans
      obtain ⟨⟨c', tr_FS₁⟩, hfs, hpair⟩ := hans
      dsimp only at hpair
      rw [Prod.mk.injEq] at hpair
      rcases hpair with ⟨rfl, rfl⟩
      obtain ⟨-, -, hnodup_FS₁, hsupp_FS₁⟩ :=
        mem_support_memoize_nodup
          (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal) fsq
          hnodup_FS hsupp_FS hfs
      exact @ih c' (tr_MT, tr_FS₁) hnodup_MT hsupp_MT hnodup_FS₁ hsupp_FS₁ hcont

private theorem validFSChain_of_mem_support_bcsChallengesAuxProg
    [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    (x : Stmt) (roots : Fin r → List Bool) :
    ∀ (m : ℕ) (hm : m ≤ r) {tr_FS tr_FS' : List (BCSFSQuery Stmt Chal × Chal)}
      {chals : Fin m → Chal},
      (tr_FS.map Prod.fst).Nodup →
      (∀ e ∈ tr_FS, e.2 ∈ (PMF.uniformOfFintype Chal).support) →
      (chals, tr_FS') ∈
        ((OracleComp.interpret (memoize (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal))
          (bcsChallengesAuxProg x roots m hm)).run tr_FS).support →
      ValidFSChain tr_FS' x ((List.ofFn roots).take m) (List.ofFn chals)
  | 0, _, tr_FS, tr_FS', chals, _, _, hmem => by
    simp only [bcsChallengesAuxProg, run_interpret_pure, PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨by simp, fun _ hi => by simp at hi⟩
  | m + 1, hm, tr_FS, tr_FS', chals, hnodup, hsupp, hmem => by
    simp only [bcsChallengesAuxProg, run_interpret_bind, run_interpret_query, run_interpret_pure,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hmem
    rcases hmem with ⟨⟨prev, tr_FS₁⟩, hprev, ⟨c, tr_FS₂⟩, hc, hpair⟩
    dsimp only at hpair
    rw [Prod.mk.injEq] at hpair
    rcases hpair with ⟨rfl, rfl⟩
    obtain ⟨-, hnodup₁, hsupp₁, -⟩ :=
      mem_support_run_memoize_invariant
        (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal)
        (bcsChallengesAuxProg x roots m (Nat.le_of_succ_le hm)) hnodup hsupp hprev
    have ih := validFSChain_of_mem_support_bcsChallengesAuxProg x roots m (Nat.le_of_succ_le hm)
      hnodup hsupp hprev
    obtain ⟨hc_mem, hsub₂, -, -⟩ :=
      mem_support_memoize_nodup
        (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal)
        (x, rootPrefix roots ⟨m, hm⟩, List.ofFn prev) hnodup₁ hsupp₁ hc
    obtain ⟨_, hsteps_prev⟩ := ih
    refine ⟨by simp [hm], fun i hi => ?_⟩
    have hi_le : i < m + 1 := by
      rw [List.length_take_of_le (by simpa using hm)] at hi
      exact hi
    by_cases him : i < m
    · have htake_rts :
          (((List.ofFn roots).take (m + 1)).take (i + 1)) =
            (((List.ofFn roots).take m).take (i + 1)) := by
        rw [List.take_take, List.take_take, Nat.min_eq_left (by omega),
          Nat.min_eq_left (Nat.succ_le_of_lt him)]
      have htake_ch : (List.ofFn (snocFin prev c)).take i = (List.ofFn prev).take i := by
        rw [ofFn_snocFin, List.take_append_of_le_length (by simp [Nat.le_of_lt him])]
      have hget_ch : (List.ofFn (snocFin prev c))[i]'(by simp [hi_le]) =
          (List.ofFn prev)[i]'(by simp [him]) := by
        rw [List.getElem_ofFn, List.getElem_ofFn]
        simp [snocFin, him]
      rw [htake_rts, htake_ch, hget_ch]
      exact hsub₂ _ (hsteps_prev i (by simpa [Nat.le_of_succ_le hm] using him))
    · have hieq : i = m := by omega
      subst hieq
      have htake_rts :
          ((List.ofFn roots).take (i + 1)).take (i + 1) = rootPrefix roots ⟨i, hm⟩ := by
        rw [List.take_take, Nat.min_self, rootPrefix_eq_take_ofFn]
      have htake_ch : (List.ofFn (snocFin prev c)).take i = List.ofFn prev := by
        rw [ofFn_snocFin, List.take_left' (by simp)]
      have hget_ch : (List.ofFn (snocFin prev c))[i]'(by simp) = c := by
        rw [List.getElem_ofFn]
        simp [snocFin]
      rw [htake_rts, htake_ch, hget_ch]
      exact hc_mem

private theorem validFSChain_of_mem_support_bcsChallengesProg
    [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    (x : Stmt) (roots : Fin r → List Bool)
    {tr_FS tr_FS' : List (BCSFSQuery Stmt Chal × Chal)} {chals : Fin r → Chal}
    (hnodup : (tr_FS.map Prod.fst).Nodup)
    (hsupp : ∀ e ∈ tr_FS, e.2 ∈ (PMF.uniformOfFintype Chal).support)
    (hmem : (chals, tr_FS') ∈
      ((OracleComp.interpret (memoize (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal))
        (bcsChallengesProg x roots)).run tr_FS).support) :
    ValidFSChain tr_FS' x (List.ofFn roots) (List.ofFn chals) := by
  have htake : (List.ofFn roots).take r = List.ofFn roots :=
    List.take_of_length_le (by simp)
  simpa only [htake] using
    validFSChain_of_mem_support_bcsChallengesAuxProg x roots r le_rfl hnodup hsupp hmem

private theorem allOpenings_of_mem_support_mapM_merkleVerifyProg
    (dist : List Bool → PMF (List Bool)) (encSym : Sym → List Bool)
    (roots : Fin r → List Bool)
    (qa : List ((Fin r × Fin (2 ^ d)) × BCSOpening Sym))
    {tr tr' : List (List Bool × List Bool)} {checks : List Bool}
    (hnodup : (tr.map Prod.fst).Nodup)
    (hsupp : ∀ e ∈ tr, e.2 ∈ (dist e.1).support)
    (hmem : (checks, tr') ∈
      ((OracleComp.interpret (memoize dist)
        (qa.mapM fun ((j, idx), (val, path)) =>
          merkleVerifyProg d (roots j) idx.val (encSym val) path)).run tr).support)
    {h : List Bool → List Bool} (hcons : TraceConsistentWith h tr') :
    ∀ j idx val path, ((j, idx), (val, path)) ∈ qa →
      PathQueriedInTrace (fun _ => h) [] tr' idx.val (encSym val) path := by
  induction qa generalizing tr checks with
  | nil =>
    intro _ _ _ _ ho
    cases ho
  | cons hd tl ih =>
    rcases hd with ⟨⟨j₀, idx₀⟩, ⟨val₀, path₀⟩⟩
    simp only [List.mapM_cons, run_interpret_bind, run_interpret_pure, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hmem
    rcases hmem with ⟨⟨c, tr₁⟩, hc, ⟨cs, tr₂⟩, hcs, rfl, rfl⟩
    obtain ⟨hsub₁, hnodup₁, hsupp₁, -⟩ :=
      mem_support_run_memoize_invariant dist
        (merkleVerifyProg d (roots j₀) idx₀.val (encSym val₀) path₀) hnodup hsupp hc
    obtain ⟨hsub₂, -, -, -⟩ :=
      mem_support_run_memoize_invariant dist _ hnodup₁ hsupp₁ hcs
    have hcons₁ : TraceConsistentWith h tr₁ := fun p hp => hcons p (hsub₂ p hp)
    have hhd := pathQueriedInTrace_of_mem_support_merkleVerifyProg dist d (roots j₀)
      idx₀.val (encSym val₀) path₀ hnodup hsupp hc hcons₁
    intro j idx val path ho
    rcases List.mem_cons.mp ho with heq | htl
    · rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at heq
      rcases heq with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
      intro q hq
      exact hsub₂ _ (hhd q hq)
    · exact ih hnodup₁ hsupp₁ hcs j idx val path htl

/-- Core trace soundness/consistency lemma for `bcsVerifyROM`: when `bcsVerifyROM iop encSym x prf`
runs from a valid trace state `(tr_MT₁, tr_FS₁)` and returns `(true, (tr_MT₃, tr_FS₂))`, if
`TraceCollisionFree tr_MT₃` holds, then there exists a challenge vector `chals : Fin r → Chal` such
that `ValidFSChain tr_FS₂ x (List.ofFn prf.roots) (List.ofFn chals)` holds and `iopVerify` accepts
`bcsExtractOracles decSym defaultSym tr_MT₃ d prf.roots` at `chals`. -/
private theorem exists_validFSChain_and_iopVerify_of_mem_support_bcsVerifyROM
    [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    (x : Stmt) (prf : BCSProof r Sym)
    {tr_MT₁ tr_MT₃ : List (List Bool × List Bool)}
    {tr_FS₁ tr_FS₂ : List (BCSFSQuery Stmt Chal × Chal)}
    (hnodup_MT₁ : (tr_MT₁.map Prod.fst).Nodup)
    (hsupp_MT₁ : ∀ e ∈ tr_MT₁, e.2 ∈ (BitString.uniformList σ).support)
    (hnodup_FS₁ : (tr_FS₁.map Prod.fst).Nodup)
    (hsupp_FS₁ : ∀ e ∈ tr_FS₁, e.2 ∈ (PMF.uniformOfFintype Chal).support)
    (hmem : (true, (tr_MT₃, tr_FS₂)) ∈
      ((OracleComp.interpret (bcsMemoize σ) (bcsVerifyROM iop encSym x prf)).run
        (tr_MT₁, tr_FS₁)).support)
    (hfree : TraceCollisionFree tr_MT₃) :
    ∃ chals : Fin r → Chal,
      ValidFSChain tr_FS₂ x (List.ofFn prf.roots) (List.ofFn chals) ∧
      iopVerify iop x chals (bcsExtractOracles decSym defaultSym tr_MT₃ d prf.roots) = true := by
  simp only [bcsVerifyROM, run_interpret_bind, PMF.monad_bind_eq_bind,
    PMF.mem_support_bind_iff] at hmem
  rcases hmem with ⟨⟨chals, st₂⟩, hFS_call, hMT_call⟩
  rw [run_bcsMemoize_liftRight, PMF.mem_support_map_iff] at hFS_call
  obtain ⟨⟨chals', tr_FS₂'⟩, hch_mem, hpair⟩ := hFS_call
  dsimp only at hpair
  rw [Prod.mk.injEq] at hpair
  rcases hpair with ⟨rfl, rfl⟩
  obtain ⟨-, hnodup_FS₂, -, heval_FS⟩ :=
    mem_support_run_memoize_invariant
      (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal)
      (bcsChallengesProg x prf.roots) hnodup_FS₁ hsupp_FS₁ hch_mem
  have hchain : ValidFSChain tr_FS₂' x (List.ofFn prf.roots) (List.ofFn chals') :=
    validFSChain_of_mem_support_bcsChallengesProg x prf.roots hnodup_FS₁ hsupp_FS₁ hch_mem
  rw [run_bcsMemoize_liftLeft, PMF.mem_support_map_iff] at hMT_call
  obtain ⟨⟨ok', tr_MT₃'⟩, hmt_mem, hpair'⟩ := hMT_call
  dsimp only at hpair'
  rw [Prod.mk.injEq, Prod.mk.injEq] at hpair'
  rcases hpair' with ⟨rfl, rfl, rfl⟩
  obtain ⟨-, hnodup_MT₃, -, heval_MT⟩ :=
    mem_support_run_memoize_invariant (fun _ : List Bool => BitString.uniformList σ)
      (bcsVerifyOpeningsProg iop encSym x prf chals') hnodup_MT₁ hsupp_MT₁ hmt_mem
  set hTree : List Bool → List Bool := fun q => (tr_MT₃'.lookup q).getD []
  have hcons_MT : TraceConsistentWith hTree tr_MT₃' :=
    traceConsistentWith_lookup_of_nodup tr_MT₃' [] hnodup_MT₃
  let defaultChal : Chal := Classical.choice ‹Nonempty Chal›
  set f : BCSFSQuery Stmt Chal → Chal := fun fsq => (tr_FS₂'.lookup fsq).getD defaultChal
  have hcons_FS : TraceConsistentWith f tr_FS₂' :=
    traceConsistentWith_lookup_of_nodup tr_FS₂' defaultChal hnodup_FS₂
  have hchals_eq : chals' = bcsChallenge (chainedFS f) x prf.roots := by
    simpa only [evalPure_bcsChallengesProg] using heval_FS f hcons_FS
  have hpaths : BCSOpeningsQueriedInTrace (fun _ => hTree) [] iop encSym tr_MT₃' x chals' prf := by
    simp only [bcsVerifyOpeningsProg, run_interpret_bind, run_interpret_pure,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hmt_mem
    rcases hmt_mem with ⟨⟨checks, tr_MT_mid⟩, hchecks, hpair_mid⟩
    obtain ⟨_, rfl⟩ := Prod.mk.inj hpair_mid
    exact allOpenings_of_mem_support_mapM_merkleVerifyProg _ encSym prf.roots _
      hnodup_MT₁ hsupp_MT₁ hchecks hcons_MT
  have hver : bcsVerify iop (fun _ => hTree) [] encSym (chainedFS f) x prf = true := by
    have heq := (heval_MT hTree hcons_MT).symm
    rw [evalPure_bcsVerifyOpeningsProg, hchals_eq] at heq
    exact heq
  refine ⟨chals', hchain, ?_⟩
  rw [hchals_eq] at hpaths ⊢
  exact iopVerify_bcsExtractOracles_of_bcsVerify hdec defaultSym hfree hpaths hver

/-- An accepting verification that ends in a good state yields a doomed accepted IOP transcript:
if a prover run from `([], [])` reaches `st₁`, `bcsVerifyROM iop encSym x prf` accepts from `st₁`
and ends in `st₃`, `BCSGoodState` on `S` holds at `st₃` and `x ∈ S`, then for some challenges the
transcript extracted from `st₃` is a valid Fiat–Shamir chain, is doomed, and is accepted by
`iopVerify`. -/
private theorem exists_doomed_and_iopVerify_of_mem_support_bcsVerifyROM
    [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {P : OracleComp (BCSROMSpec Stmt Chal) β} {res : β} {x : Stmt} {prf : BCSProof r Sym}
    {st₁ st₃ : BCSTraceState Stmt Chal}
    (hP : (res, st₁) ∈ ((OracleComp.interpret (bcsMemoize σ) P).run ([], [])).support)
    (hV : (true, st₃) ∈
      ((OracleComp.interpret (bcsMemoize σ) (bcsVerifyROM iop encSym x prf)).run st₁).support)
    (hgood : BCSGoodState r d S doomed decSym defaultSym st₃) (hx : x ∈ S) :
    ∃ chals : Fin r → Chal,
      ValidFSChain st₃.2 x (List.ofFn prf.roots) (List.ofFn chals) ∧
      doomed x (List.ofFn fun j : Fin r =>
        (bcsExtractOracles decSym defaultSym st₃.1 d prf.roots j, chals j)) ∧
      iopVerify iop x chals (bcsExtractOracles decSym defaultSym st₃.1 d prf.roots) = true := by
  obtain ⟨hnodup_MT, hsupp_MT, hnodup_FS, hsupp_FS⟩ :=
    mem_support_run_bcsMemoize_invariant σ P (st := ([], []))
      List.nodup_nil (by simp) List.nodup_nil (by simp) hP
  obtain ⟨chals, hchain, hacc⟩ :=
    exists_validFSChain_and_iopVerify_of_mem_support_bcsVerifyROM iop hdec defaultSym σ x prf
      hnodup_MT hsupp_MT hnodup_FS hsupp_FS hV hgood.1
  refine ⟨chals, hchain, ?_, hacc⟩
  rw [← bcsExtractTranscript_ofFn]
  exact hgood.2 x hx (List.ofFn prf.roots) (List.ofFn chals) (by simp) hchain

end SupportInvariants

/-! #### Adaptive two-channel BCS ROM soundness -/

section ROMSoundness

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

open Classical in
/-- The BCS ROM soundness execution as an `OracleComp (BCSROMSpec Stmt Chal)` program: run the
cheating prover `P` to obtain `(x, prf)`, run `bcsVerifyROM iop encSym x prf`, and return `true`
when `x ∉ lang` and the verifier accepts. -/
@[expose] noncomputable def bcsSoundnessProg (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (lang : Set Stmt)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) :
    OracleComp (BCSROMSpec Stmt Chal) Bool := do
  let (x, prf) ← P
  let ok ← bcsVerifyROM iop encSym x prf
  return decide (x ∉ lang) && ok

/-- If the cheating prover `P` makes at most `t_FS` Fiat–Shamir queries, then
`bcsSoundnessProg iop encSym lang P` makes at most `t_FS + r` Fiat–Shamir queries. -/
theorem isCostBounded_bcsFSCost_bcsSoundnessProg (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (lang : Set Stmt)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_FS : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS) :
    IsCostBounded bcsFSCost (bcsSoundnessProg iop encSym lang P) (t_FS + r) := by
  unfold bcsSoundnessProg
  open Classical in
  exact hFS.bind fun (x, prf) =>
    (isCostBounded_bcsFSCost_bcsVerifyROM iop encSym x prf).bind fun ok =>
      IsCostBounded.pure (decide (x ∉ lang) && ok) 0

/-- If `P` makes at most `t_MT` Merkle hash queries and `bcsVerifyROM iop encSym x prf` makes at
most `q_V` Merkle hash queries for every `(x, prf) ∈ P.support`, then `bcsSoundnessProg` makes at
most `t_MT + q_V` Merkle hash queries. -/
theorem isCostBounded_bcsMTCost_bcsSoundnessProg (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (lang : Set Stmt)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_MT q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hV : ∀ x prf, (x, prf) ∈ P.support →
      IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf) q_V) :
    IsCostBounded bcsMTCost (bcsSoundnessProg iop encSym lang P) (t_MT + q_V) := by
  unfold bcsSoundnessProg
  open Classical in
  exact hMT.bind_on_support fun (x, prf) hmem =>
    (hV x prf hmem).bind fun ok =>
      IsCostBounded.pure (decide (x ∉ lang) && ok) 0

/-- The BCS ROM soundness experiment with `σ`-bit Merkle digests: runs `bcsSoundnessProg` against
the shared lazy random oracle `RandomOracle.answer (bcsOracleDist Stmt Chal σ)` from an empty cache.
-/
@[expose] noncomputable def bcsSoundnessGame [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal] (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (lang : Set Stmt)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) (σ : ℕ) : PMF Bool :=
  (OracleComp.runWith (RandomOracle.answer (bcsOracleDist Stmt Chal σ))
    (bcsSoundnessProg iop encSym lang P) (fun _ => none)).map Prod.fst

theorem bcsSoundnessGame_eq_run_bcsMemoize [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal] (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (lang : Set Stmt)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) (σ : ℕ) :
    bcsSoundnessGame iop encSym lang P σ =
      ((OracleComp.interpret (bcsMemoize σ) (bcsSoundnessProg iop encSym lang P)).run ([], [])).map
        Prod.fst := by
  have h := congrArg (PMF.map Prod.fst)
    (run_interpret_bcsMemoize σ (bcsSoundnessProg iop encSym lang P) ([], []))
  simpa only [bcsSoundnessGame, PMF.map_comp, Function.comp_def, bcsOfTraces_nil] using h.symm

/-- Any outcome `(true, st')` in the support of `bcsSoundnessProg` under `bcsMemoize` violates
`BCSGoodState` on `langᶜ`. -/
private theorem not_bcsGoodState_of_mem_support_bcsSoundnessProg
    [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {lang : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hrbr : IOPRoundByRoundSoundness iop lang doomed goodStep)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym))
    {st' : BCSTraceState Stmt Chal}
    (hmem : (true, st') ∈
      ((OracleComp.interpret (bcsMemoize σ) (bcsSoundnessProg iop encSym lang P)).run
        ([], [])).support) :
    ¬ BCSGoodState r d langᶜ doomed decSym defaultSym st' := by
  simp only [bcsSoundnessProg, run_interpret_bind, run_interpret_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hmem
  rcases hmem with ⟨⟨⟨x, prf⟩, ⟨tr_MT₁, tr_FS₁⟩⟩, hP, ⟨ok, ⟨tr_MT₃, tr_FS₂⟩⟩, hV, hwin⟩
  dsimp only at hwin
  rw [Prod.mk.injEq] at hwin
  rcases hwin with ⟨hwin, rfl⟩
  symm at hwin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨hx_not_lang, rfl⟩ := hwin
  intro hgood
  obtain ⟨chals, -, hdoomed, hiop_acc⟩ :=
    exists_doomed_and_iopVerify_of_mem_support_bcsVerifyROM iop hdec defaultSym σ hP hV hgood
      hx_not_lang
  exact Bool.false_ne_true ((hrbr.reject_of_doomed x _ chals hdoomed).symm.trans hiop_acc)

/-- **Adaptive two-channel BCS ROM soundness theorem** (compare state-restoration soundness in
[BenSassonChiesaSpooner2016] and [ChiesaYogev2024], Theorem 25.2.1, printed pp. 276–278, and the
round-by-round reduction in [ChiesaYogev2024], Chapter 31, Definitions 31.1.1–31.1.2 and Theorem
31.2.1): under `IOPRoundByRoundSoundness iop lang doomed goodStep` with per-round challenge escape
probability `≤ ε_rbr`, any adaptive cheating prover `P` making at most `t_FS` Fiat–Shamir queries
such that `bcsSoundnessProg iop encSym lang P` makes at most `Q_MT` Merkle hash queries convinces
`bcsVerifyROM` on a false statement `x ∉ lang` with probability at most
`(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) +`
`Q_MT * ((3 * Q_MT + r * (t_FS + r)) * (1 / 2 ^ σ))`. -/
theorem bcsROMSoundness_bound [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {lang : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hrbr : IOPRoundByRoundSoundness iop lang doomed goodStep)
    {ε_rbr : ℝ≥0∞}
    (hescape : ∀ x ∉ lang, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost (bcsSoundnessProg iop encSym lang P) Q_MT) :
    bcsSoundnessGame iop encSym lang P σ true ≤
      ((t_FS + r : ℕ) : ℝ≥0∞) *
          (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [bcsSoundnessGame_eq_run_bcsMemoize, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  set run := (OracleComp.interpret (bcsMemoize σ) (bcsSoundnessProg iop encSym lang P)).run ([], [])
  rw [← PMF.toOuterMeasure_apply_inter_support]
  calc run.toOuterMeasure ((Prod.fst ⁻¹' {true}) ∩ run.support)
      ≤ run.toOuterMeasure {out | ¬ BCSGoodState r d langᶜ doomed decSym defaultSym out.2} := by
        refine run.toOuterMeasure.mono fun ⟨res, st'⟩ ⟨hres, hmem⟩ => ?_
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hres
        subst hres
        exact not_bcsGoodState_of_mem_support_bcsSoundnessProg hrbr hdec defaultSym σ P hmem
    _ ≤ ((t_FS + r : ℕ) : ℝ≥0∞) *
            (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
          (Q_MT : ℝ≥0∞) *
            (((3 * Q_MT + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
        toOuterMeasure_run_bcsMemoize_not_goodState_le
          hrbr.init_doomed (fun x _ => hrbr.step_doomed x) hescape decSym defaultSym σ hMT
          (isCostBounded_bcsFSCost_bcsSoundnessProg iop encSym lang hFS)

/-- **Adaptive two-channel BCS ROM soundness (separate prover/verifier Merkle budgets on
`P.support`)**: if `P` makes at most `t_MT` Merkle hash queries and `t_FS` Fiat–Shamir queries, and
`bcsVerifyROM iop encSym x prf` makes at most `q_V` Merkle hash queries for outputs `(x, prf) ∈
P.support`, then `bcsSoundnessGame` accepts a false statement with probability at most
`(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) +`
`(t_MT + q_V) * ((3 * (t_MT + q_V) + r * (t_FS + r)) * (1 / 2 ^ σ))`. -/
theorem bcsROMSoundness_bound_of_prover_verifier [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {lang : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hrbr : IOPRoundByRoundSoundness iop lang doomed goodStep)
    {ε_rbr : ℝ≥0∞}
    (hescape : ∀ x ∉ lang, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_MT t_FS q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hV : ∀ x prf, (x, prf) ∈ P.support →
      IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf) q_V) :
    bcsSoundnessGame iop encSym lang P σ true ≤
      ((t_FS + r : ℕ) : ℝ≥0∞) *
          (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        ((t_MT + q_V : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + q_V) + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound hrbr hescape hdec defaultSym σ hFS
    (isCostBounded_bcsMTCost_bcsSoundnessProg iop encSym lang hMT hV)

end ROMSoundness

/-! #### Adaptive straight-line BCS ROM knowledge soundness -/

section ROMKnowledgeSoundness

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

/-- Combined prover-and-verifier execution in the two-channel BCS random-oracle model: runs `P` to
obtain `(x, prf)` and then runs `bcsVerifyROM iop encSym x prf`, returning `((x, prf), ok)`. -/
@[expose] def bcsExecROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (encSym : Sym → List Bool)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) :
    OracleComp (BCSROMSpec Stmt Chal) ((Stmt × BCSProof r Sym) × Bool) := do
  let (x, prf) ← P
  let ok ← bcsVerifyROM iop encSym x prf
  return ((x, prf), ok)

theorem isCostBounded_bcsFSCost_bcsExecROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_FS : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS) :
    IsCostBounded bcsFSCost (bcsExecROM iop encSym P) (t_FS + r) := by
  unfold bcsExecROM
  exact hFS.bind fun (x, prf) =>
    (isCostBounded_bcsFSCost_bcsVerifyROM iop encSym x prf).bind fun ok =>
      IsCostBounded.pure ((x, prf), ok) 0

theorem isCostBounded_bcsMTCost_bcsExecROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_MT q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hV : ∀ x prf, (x, prf) ∈ P.support →
      IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf) q_V) :
    IsCostBounded bcsMTCost (bcsExecROM iop encSym P) (t_MT + q_V) := by
  unfold bcsExecROM
  exact hMT.bind_on_support fun (x, prf) hmem =>
    (hV x prf hmem).bind fun ok =>
      IsCostBounded.pure ((x, prf), ok) 0

open Classical in
/-- **Straight-line BCS ROM knowledge soundness experiment** (`bcsKnowledgeSoundnessGame`):
1. Runs the cheating prover `P` under `bcsMemoize σ` from `([], [])`, recording the prover's own
   Merkle trace `tr_P` and Fiat–Shamir trace `tr_FS`.
2. Reconstructs a candidate witness `w := bcsExtractWitness iopExtract decSym defaultSym tr_P x
   prf.roots` *straight-line from `tr_P` alone* (before running the verifier and with zero
   rewinding).
3. Runs `bcsVerifyROM iop encSym x prf` from `(tr_P, tr_FS)` to obtain `ok`.
4. Outputs `true` iff `ok = true` and `¬ rel x w`. -/
@[expose] noncomputable def bcsKnowledgeSoundnessGame [BEq Stmt] [BEq Chal]
    [Fintype Chal] [Nonempty Chal] (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (rel : Stmt → Wit → Prop) (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit)
    (encSym : Sym → List Bool) (decSym : List Bool → Sym) (defaultSym : Sym)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) (σ : ℕ) : PMF Bool :=
  (((OracleComp.interpret (bcsMemoize σ) P).run ([], [])).bind fun ((x, prf), (tr_P, tr_FS)) =>
    let w := bcsExtractWitness iopExtract decSym defaultSym tr_P x prf.roots
    ((OracleComp.interpret (bcsMemoize σ) (bcsVerifyROM iop encSym x prf)).run (tr_P, tr_FS)).map
      fun (ok, _) => ok && decide (¬ rel x w))

/-- **Trace-level straight-line BCS ROM knowledge soundness bound**: on a combined execution of
`bcsExecROM iop encSym P` under `bcsMemoize σ`, the probability that `bcsVerifyROM` accepts
`(x, prf)` while `iopExtract x (bcsExtractOracles decSym defaultSym tr_MT d prf.roots)` fails
`rel x` is at most
`(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) +`
`Q_MT * ((3 * Q_MT + r * (t_FS + r)) * (1 / 2 ^ σ))`. -/
theorem bcsROMKnowledgeSoundness_trace_bound [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {rel : Stmt → Wit → Prop}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hks : IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep)
    {ε_rbr : ℝ≥0∞}
    (hescape : ∀ x pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost (bcsExecROM iop encSym P) Q_MT) :
    ((OracleComp.interpret (bcsMemoize σ) (bcsExecROM iop encSym P)).run ([], [])).toOuterMeasure
        {out | match out with
          | (((x, prf), ok), (tr_MT, _)) =>
            ok = true ∧
              ¬ rel x (iopExtract x (bcsExtractOracles decSym defaultSym tr_MT d prf.roots))} ≤
      ((t_FS + r : ℕ) : ℝ≥0∞) *
          (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  set run := (OracleComp.interpret (bcsMemoize σ) (bcsExecROM iop encSym P)).run ([], [])
  set badOut : Set (((Stmt × BCSProof r Sym) × Bool) × BCSTraceState Stmt Chal) :=
    {out | match out with
      | (((x, prf), ok), (tr_MT, _)) =>
        ok = true ∧
          ¬ rel x (iopExtract x (bcsExtractOracles decSym defaultSym tr_MT d prf.roots))}
  rw [← PMF.toOuterMeasure_apply_inter_support]
  calc run.toOuterMeasure (badOut ∩ run.support)
      ≤ run.toOuterMeasure {out | ¬ BCSGoodState r d Set.univ doomed decSym defaultSym out.2} := by
        refine run.toOuterMeasure.mono
          fun ⟨⟨⟨x, prf⟩, ok⟩, ⟨tr_MT₃, tr_FS₂⟩⟩ ⟨⟨hok, hnot_rel⟩, hmem⟩ => ?_
        subst hok
        simp only [run, bcsExecROM, run_interpret_bind, run_interpret_pure, PMF.monad_bind_eq_bind,
          PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hmem
        rcases hmem with ⟨⟨⟨x₁, prf₁⟩, ⟨tr_MT₁, tr_FS₁⟩⟩, hP, ⟨ok₁, st₃⟩, hV, hpair⟩
        dsimp only at hpair
        rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hpair
        rcases hpair with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
        intro hgood
        obtain ⟨chals, -, hdoomed, hiop_acc⟩ :=
          exists_doomed_and_iopVerify_of_mem_support_bcsVerifyROM iop hdec defaultSym σ hP hV
            hgood (Set.mem_univ x)
        exact hnot_rel (hks.extract_of_doomed x _ chals hdoomed hiop_acc)
    _ ≤ ((t_FS + r : ℕ) : ℝ≥0∞) *
            (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
          (Q_MT : ℝ≥0∞) *
            (((3 * Q_MT + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
        toOuterMeasure_run_bcsMemoize_not_goodState_le
          (fun x _ => hks.init_doomed x) (fun x _ => hks.step_doomed x)
          (fun x _ => hescape x) decSym defaultSym σ hMT
          (isCostBounded_bcsFSCost_bcsExecROM iop encSym hFS)

/-- Along a `liftRight` program run under `bcsStickyMemoize`, the Merkle trace `tr_MT` is unchanged.
-/
private theorem fst_eq_of_mem_support_bcsStickyMemoize_liftRight {γ : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    (S : Set Stmt) (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (prog : OracleComp (BCSFSSpec Stmt Chal) γ)
    {p p' : BCSTraceState Stmt Chal × Bool} {res : γ}
    (hmem : (res, p') ∈
      ((OracleComp.interpret (bcsStickyMemoize r d S doomed decSym defaultSym σ)
        (OracleComp.liftRight (spec₁ := MerkleHashSpec) prog)).run p).support) :
    p'.1.1 = p.1.1 := by
  induction prog using OracleComp.induction generalizing p with
  | pure a =>
    simp only [liftRight_pure, run_interpret_pure, PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    rfl
  | query_bind q cont ih =>
    simp only [liftRight_bind, liftRight_query, run_interpret_bind, run_interpret_query,
      PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hmem
    rcases hmem with ⟨⟨c, p₁⟩, hc, hcont⟩
    rcases p with ⟨⟨tr_MT, tr_FS⟩, flag⟩
    simp only [bcsStickyMemoize, bcsMemoize, PMF.map_comp, Function.comp_def,
      PMF.mem_support_map_iff] at hc
    rcases hc with ⟨⟨c₂, tr_FS₁⟩, _, hpair⟩
    dsimp only at hpair
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    have h := ih c₂ hcont
    exact h

/-- Along a `liftLeft` program run under `bcsStickyMemoize`, if the final sticky flag `p'.2` is
`false`, then `p'.1.2 = p.1.2` and `bcsExtractTable` is unchanged on every root appearing in the
first `r` roots of any Fiat–Shamir entry in `p.1.2`. -/
private theorem extractTable_eq_of_mem_support_bcsStickyMemoize_liftLeft {γ : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    (S : Set Stmt) (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (prog : OracleComp MerkleHashSpec γ)
    {p p' : BCSTraceState Stmt Chal × Bool} {res : γ}
    (hmem : (res, p') ∈
      ((OracleComp.interpret (bcsStickyMemoize r d S doomed decSym defaultSym σ)
        (OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal) prog)).run p).support)
    (hflag' : p'.2 = false) :
    p.2 = false ∧ p'.1.2 = p.1.2 ∧
      ∀ rt ∈ p.1.2.flatMap (fun ((_, rts, _), _) => rts.take r),
        bcsExtractTable decSym defaultSym p'.1.1 d rt =
          bcsExtractTable decSym defaultSym p.1.1 d rt := by
  induction prog using OracleComp.induction generalizing p with
  | pure a =>
    simp only [liftLeft_pure, run_interpret_pure, PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact ⟨hflag', rfl, fun _ _ => rfl⟩
  | query_bind msg cont ih =>
    simp only [liftLeft_bind, liftLeft_query, run_interpret_bind, run_interpret_query,
      PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hmem
    rcases hmem with ⟨⟨ans, p₁⟩, hans, hcont⟩
    obtain ⟨hflag₁, hfs_eq, hextract_tail⟩ := ih ans hcont
    rcases p with ⟨⟨tr_MT, tr_FS⟩, flag⟩
    simp only [bcsStickyMemoize, bcsMemoize, PMF.map_comp, Function.comp_def,
      PMF.mem_support_map_iff] at hans
    rcases hans with ⟨⟨ans₂, tr_MT₁⟩, hmt, hpair⟩
    dsimp only at hpair
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    dsimp only at hflag₁ hfs_eq hextract_tail
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hflag₁
    obtain ⟨rfl, hnot_step⟩ := hflag₁
    refine ⟨rfl, hfs_eq, fun rt hrt => ?_⟩
    rw [hextract_tail rt hrt]
    rcases (RandomOracle.mem_support_memoize_iff _ msg tr_MT (ans₂, tr_MT₁)).mp hmt with
      ⟨_, htr_eq⟩ | ⟨_, _, htr_eq⟩
    · change tr_MT₁ = tr_MT at htr_eq
      rw [htr_eq]
    · change tr_MT₁ = (msg, ans₂) :: tr_MT at htr_eq
      subst htr_eq
      have hnot_forb : ans₂ ∉ bcsForbiddenDigests r (tr_MT, tr_FS) := by
        intro hforb
        exact hnot_step (Or.inr ⟨msg, ans₂, rfl, hforb⟩)
      simp only [bcsForbiddenDigests, List.mem_append, List.mem_map, not_or, not_exists,
        not_and] at hnot_forb
      obtain ⟨⟨⟨_, hnot_left⟩, hnot_right⟩, hnot_fs⟩ := hnot_forb
      have hne_rt : ans₂ ≠ rt := fun heq => hnot_fs (heq ▸ hrt)
      have hchildren : ∀ e ∈ tr_MT, ans₂ ≠ unframe e.1 ∧ ans₂ ≠ dropFrame e.1 :=
        fun ⟨q, d'⟩ he =>
          ⟨fun heq => hnot_left (q, d') he heq.symm, fun heq => hnot_right (q, d') he heq.symm⟩
      exact bcsExtractTable_cons_of_ne decSym defaultSym tr_MT msg hne_rt hchildren

/-- Rewriting `bcsKnowledgeSoundnessGame` as an event over the sticky-bad execution of
`bcsExecROM iop encSym P`: forgetting the sticky flag in both `P` and `bcsVerifyROM` reproduces
`bcsKnowledgeSoundnessGame`. -/
private theorem bcsKnowledgeSoundnessGame_eq_sticky [BEq Stmt] [BEq Chal]
    [Fintype Chal] [Nonempty Chal] (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (rel : Stmt → Wit → Prop) (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (encSym : Sym → List Bool) (decSym : List Bool → Sym) (defaultSym : Sym)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) (σ : ℕ) :
    open Classical in
    bcsKnowledgeSoundnessGame iop rel iopExtract encSym decSym defaultSym P σ =
      (((OracleComp.interpret (bcsStickyMemoize r d Set.univ doomed decSym defaultSym σ) P).run
          (([], []), false)).bind fun ((x, prf), p₁) =>
        let w := bcsExtractWitness iopExtract decSym defaultSym p₁.1.1 x prf.roots
        ((OracleComp.interpret (bcsStickyMemoize r d Set.univ doomed decSym defaultSym σ)
          (bcsVerifyROM iop encSym x prf)).run p₁).map
            fun (ok, _) => ok && decide (¬ rel x w)) := by
  classical
  unfold bcsKnowledgeSoundnessGame
  rw [← run_interpret_bcsStickyMemoize_map Set.univ doomed decSym defaultSym σ P ([], []) false,
    PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun ⟨⟨x, prf⟩, ⟨⟨tr_P, tr_FS⟩, flag₁⟩⟩ => ?_)
  dsimp only [Function.comp_def]
  rw [← run_interpret_bcsStickyMemoize_map Set.univ doomed decSym defaultSym σ
    (bcsVerifyROM iop encSym x prf) (tr_P, tr_FS) flag₁, PMF.map_comp]
  rfl

/-- **Adaptive straight-line BCS ROM knowledge soundness theorem** (compare state-restoration
knowledge soundness and direct extraction in [BenSassonChiesaSpooner2016] and [ChiesaYogev2024],
Theorem 26.1.1 and Construction 26.1.3, printed pp. 288–289, and the round-by-round reduction in
[ChiesaYogev2024], Chapter 31, Definition 31.1.6 and Theorem 31.3.1): under
`IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep` with per-round challenge
escape probability `≤ ε_rbr`, for any adaptive cheating prover `P` making at most `t_FS`
Fiat–Shamir queries such that `bcsExecROM iop encSym P` makes at most `Q_MT` Merkle hash queries,
the probability that `bcsVerifyROM` accepts `(x, prf)` while the straight-line witness
`bcsExtractWitness iopExtract decSym defaultSym tr_P x prf.roots` (extracted from the prover's own
Merkle trace `tr_P` with zero rewinding, before running the verifier) fails `rel x` is at most
`(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) +`
`Q_MT * ((3 * Q_MT + r * (t_FS + r)) * (1 / 2 ^ σ))`. -/
theorem bcsROMKnowledgeSoundness_bound [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {rel : Stmt → Wit → Prop}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hks : IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep)
    {ε_rbr : ℝ≥0∞}
    (hescape : ∀ x pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost (bcsExecROM iop encSym P) Q_MT) :
    bcsKnowledgeSoundnessGame iop rel iopExtract encSym decSym defaultSym P σ true ≤
      ((t_FS + r : ℕ) : ℝ≥0∞) *
          (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  classical
  set handler := bcsStickyMemoize r d (Set.univ : Set Stmt) doomed decSym defaultSym σ
  have hgame_eq : bcsKnowledgeSoundnessGame iop rel iopExtract encSym decSym defaultSym P σ =
      (((OracleComp.interpret handler P).run (([], []), false)).bind fun ((x, prf), p₁) =>
        ((OracleComp.interpret handler (bcsVerifyROM iop encSym x prf)).run p₁).map
          fun (ok, p₃) =>
            (ok && decide (¬ rel x
              (bcsExtractWitness iopExtract decSym defaultSym p₁.1.1 x prf.roots)), p₃)).map
        Prod.fst := by
    rw [bcsKnowledgeSoundnessGame_eq_sticky iop rel iopExtract doomed encSym decSym defaultSym P σ,
      PMF.map_bind]
    refine congrArg (PMF.bind _) (funext fun ⟨⟨x, prf⟩, p₁⟩ => ?_)
    simp only [handler, PMF.map_comp, Function.comp_def]
  set combined : PMF (Bool × (BCSTraceState Stmt Chal × Bool)) :=
    ((OracleComp.interpret handler P).run (([], []), false)).bind fun ((x, prf), p₁) =>
      ((OracleComp.interpret handler (bcsVerifyROM iop encSym x prf)).run p₁).map
        fun (ok, p₃) =>
          (ok && decide (¬ rel x
            (bcsExtractWitness iopExtract decSym defaultSym p₁.1.1 x prf.roots)), p₃)
  have hrun_snd : combined.map Prod.snd =
      ((OracleComp.interpret handler (bcsExecROM iop encSym P)).run (([], []), false)).map
        Prod.snd := by
    simp only [combined, bcsExecROM, run_interpret_bind, run_interpret_pure,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind]
    refine congrArg (PMF.bind _) (funext fun ⟨⟨x, prf⟩, p₁⟩ => ?_)
    simp only [Function.comp_def, PMF.map, PMF.bind_bind, PMF.pure_bind]
  rw [hgame_eq, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    ← PMF.toOuterMeasure_apply_inter_support]
  calc combined.toOuterMeasure ((Prod.fst ⁻¹' {true}) ∩ combined.support)
      ≤ combined.toOuterMeasure
          {out | BCSStickyBad r d Set.univ doomed decSym defaultSym out.2} := by
        refine combined.toOuterMeasure.mono fun ⟨win, p₃⟩ ⟨hwin, hmem⟩ => ?_
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hwin
        subst hwin
        simp only [combined, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hmem
        rcases hmem with ⟨⟨⟨x, prf⟩, p₁⟩, hP_sticky, ⟨ok, p₃'⟩, hV_sticky, hpair⟩
        rw [Prod.mk.injEq] at hpair
        rcases hpair with ⟨hwin_eq, rfl⟩
        dsimp only at hwin_eq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin_eq
        obtain ⟨rfl, hnot_rel_P⟩ := hwin_eq
        by_contra hnot_bad
        change ¬ BCSStickyBad r d Set.univ doomed decSym defaultSym p₃' at hnot_bad
        unfold BCSStickyBad at hnot_bad
        push Not at hnot_bad
        obtain ⟨hflag₃_ne, hgood₃⟩ := hnot_bad
        have hflag₃ : p₃'.2 = false := Bool.eq_false_iff.mpr hflag₃_ne
        -- Extract intermediate state between `bcsChallengesProg` and `bcsVerifyOpeningsProg`.
        have hV_split := hV_sticky
        simp only [bcsVerifyROM, run_interpret_bind, PMF.monad_bind_eq_bind,
          PMF.mem_support_bind_iff] at hV_split
        rcases hV_split with ⟨⟨chals_mid, p₂⟩, hchal_sticky, hopen_sticky⟩
        have htr_P_eq : p₂.1.1 = p₁.1.1 :=
          fst_eq_of_mem_support_bcsStickyMemoize_liftRight Set.univ doomed decSym defaultSym σ
            (bcsChallengesProg x prf.roots) hchal_sticky
        obtain ⟨_, hfs₂_eq, hextract_eq⟩ :=
          extractTable_eq_of_mem_support_bcsStickyMemoize_liftLeft Set.univ doomed decSym
            defaultSym σ (bcsVerifyOpeningsProg iop encSym x prf chals_mid) hopen_sticky hflag₃
        -- Project sticky support memberships to `bcsMemoize` for `ValidFSChain` & `iopVerify`.
        have hP_mem : ((x, prf), p₁.1) ∈
            ((OracleComp.interpret (bcsMemoize σ) P).run ([], [])).support := by
          rw [← run_interpret_bcsStickyMemoize_map Set.univ doomed decSym defaultSym σ P
            ([], []) false, PMF.mem_support_map_iff]
          exact ⟨((x, prf), p₁), hP_sticky, rfl⟩
        have hV_mem : (true, p₃'.1) ∈
            ((OracleComp.interpret (bcsMemoize σ) (bcsVerifyROM iop encSym x prf)).run
              p₁.1).support := by
          rcases hp₁ : p₁ with ⟨st₁, flag₁⟩
          rw [← run_interpret_bcsStickyMemoize_map Set.univ doomed decSym defaultSym σ
            (bcsVerifyROM iop encSym x prf) st₁ flag₁, PMF.mem_support_map_iff]
          exact ⟨(true, p₃'), hp₁ ▸ hV_sticky, rfl⟩
        obtain ⟨chals, hchain, hdoomed, hiop_acc⟩ :=
          exists_doomed_and_iopVerify_of_mem_support_bcsVerifyROM iop hdec defaultSym σ hP_mem
            hV_mem hgood₃ (Set.mem_univ x)
        have horacles_eq :
            bcsExtractOracles decSym defaultSym p₁.1.1 d prf.roots =
              bcsExtractOracles decSym defaultSym p₃'.1.1 d prf.roots := by
          funext j
          obtain ⟨hlen_ch, hsteps_ch⟩ := hchain
          have hj_lt : j.val < (List.ofFn prf.roots).length := by simp [j.isLt]
          have hstep_j := hsteps_ch j.val hj_lt
          have hmem_forb_j : prf.roots j ∈
              p₂.1.2.flatMap (fun ((_, rts, _), _) => rts.take r) := by
            rw [← hfs₂_eq, List.mem_flatMap]
            refine ⟨((x, (List.ofFn prf.roots).take (j.val + 1), (List.ofFn chals).take j.val),
              (List.ofFn chals)[j.val]'(hlen_ch ▸ hj_lt)), hstep_j, ?_⟩
            have htake_le : ((List.ofFn prf.roots).take (j.val + 1)).length ≤ r := by
              simp [Nat.succ_le_of_lt j.isLt]
            dsimp only
            rw [List.take_of_length_le htake_le, ← rootPrefix_eq_take_ofFn]
            exact List.mem_ofFn.mpr ⟨Fin.last j.val, by simp⟩
          have htab := hextract_eq (prf.roots j) hmem_forb_j
          rw [htr_P_eq] at htab
          exact htab.symm
        have hrel_final := hks.extract_of_doomed x _ chals hdoomed hiop_acc
        exact hnot_rel_P (by simpa only [bcsExtractWitness, horacles_eq] using hrel_final)
    _ = ((OracleComp.interpret handler (bcsExecROM iop encSym P)).run
          (([], []), false)).toOuterMeasure
          {out | BCSStickyBad r d Set.univ doomed decSym defaultSym out.2} := by
        have h1 : combined.toOuterMeasure
            {out | BCSStickyBad r d Set.univ doomed decSym defaultSym out.2} =
            (combined.map Prod.snd).toOuterMeasure
              {p | BCSStickyBad r d Set.univ doomed decSym defaultSym p} :=
          (PMF.toOuterMeasure_map_apply Prod.snd combined
            {p | BCSStickyBad r d Set.univ doomed decSym defaultSym p}).symm
        rw [h1, hrun_snd, PMF.toOuterMeasure_map_apply]
        rfl
    _ ≤ ((t_FS + r : ℕ) : ℝ≥0∞) *
            (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
          (Q_MT : ℝ≥0∞) *
            (((3 * Q_MT + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
        toOuterMeasure_run_bcsStickyMemoize_bad_le
          (fun x _ => hks.init_doomed x) (fun x _ => hks.step_doomed x)
          (fun x _ => hescape x) decSym defaultSym σ hMT
          (isCostBounded_bcsFSCost_bcsExecROM iop encSym hFS)

/-- **Adaptive straight-line BCS ROM knowledge soundness (separate prover/verifier Merkle budgets on
`P.support`)**: if `P` makes at most `t_MT` Merkle hash queries and `t_FS` Fiat–Shamir queries, and
`bcsVerifyROM iop encSym x prf` makes at most `q_V` Merkle hash queries for outputs `(x, prf) ∈
P.support`, then `bcsKnowledgeSoundnessGame` fails straight-line witness extraction on an accepted
proof with probability at most
`(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) +`
`(t_MT + q_V) * ((3 * (t_MT + q_V) + r * (t_FS + r)) * (1 / 2 ^ σ))`. -/
theorem bcsROMKnowledgeSoundness_bound_of_prover_verifier
    [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {rel : Stmt → Wit → Prop}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hks : IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep)
    {ε_rbr : ℝ≥0∞}
    (hescape : ∀ x pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_MT t_FS q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hV : ∀ x prf, (x, prf) ∈ P.support →
      IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf) q_V) :
    bcsKnowledgeSoundnessGame iop rel iopExtract encSym decSym defaultSym P σ true ≤
      ((t_FS + r : ℕ) : ℝ≥0∞) *
          (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        ((t_MT + q_V : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + q_V) + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMKnowledgeSoundness_bound hks hescape hdec defaultSym σ hFS
    (isCostBounded_bcsMTCost_bcsExecROM iop encSym hMT hV)

end ROMKnowledgeSoundness

end Cslib.Crypto.Protocols.BCS
