/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Kilian.Micali
public import CslibFrontier.Crypto.Computational.Kilian.Soundness
public import CslibFrontier.Crypto.Computational.Kilian.Succinct
public import CslibFrontier.Crypto.Computational.MerkleTree.ROMExtract
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
import CslibFrontier.Computability.Complexity.Classes.SharpP.Probability
import CslibFrontier.Computability.PCP.Completeness
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EventBind
import Mathlib.Data.List.GetD

/-!
# Soundness of Micali's Computationally Sound Proofs in the Random Oracle Model

This module proves an explicit soundness bound for an unsalted, two-channel adaptation of
Micali's non-interactive random-oracle compilation of Kilian's protocol ([Micali2000];
[ChiesaYogev2024], Construction 21.1.1 and Theorem 21.2.1, printed pp. 239–242) by
combining the straight-line Merkle trace extractor of
`CslibFrontier/Crypto/Computational/MerkleTree/ROMExtract.lean` with a union bound over the
Fiat–Shamir challenge queries:

1. **Pure / fixed-trace soundness bridge (`micaliVerifyPure_sound_of_traceCollisionFree`).**
   Given a deterministic Merkle hash `H k` (or unkeyed `hTree`), a Fiat–Shamir oracle `hFS`, and a
   recorded Merkle query-answer trace `tr : List (List Bool × List Bool)`: if `tr` is
   collision-free (`TraceCollisionFree tr`) and records every hash evaluation along the openings of
   `proof : MicaliProof` (`AllOpeningsQueriedInTrace`), then whenever `micaliVerifyPure` accepts
   `(x, proof)`, the PCP verifier `V` accepts the single extracted proof
   `micaliExtractProof V tr x proof.root` on every challenge string `ρ ∈ hFS (x, proof.root)` of
   length `V.coins x`. Equivalently, an accepting Micali proof whose opened paths lie in `tr`
   either exhibits a collision in `tr` (`¬ TraceCollisionFree tr`, from which
   `extractTraceCollision` extracts a concrete hash collision when `TraceConsistentWith (H k) tr`)
   or convinces `V` on the extracted PCP proof
   (`not_traceCollisionFree_or_accepts_of_micaliVerifyPure`,
   `exists_collision_of_micaliVerifyPure_of_rejects`).
2. **Fiat–Shamir challenge union bound & two-stage ROM soundness
   (`toOuterMeasure_run_memoize_not_fsTraceSound_le`, `toOuterMeasure_twoStageMicali_le`).**
   For any false statement `x ∉ L` and any fixed Merkle root `rt` (which determines the extracted
   PCP proof `micaliExtractProof V tr x rt` from `tr`), a fresh challenge draw
   `ρs ← kilianChallenges V m x` makes `V` accept on all `m` repetitions with probability at most
   `(1 / 2) ^ m` (`toOuterMeasure_kilianChallenges_accepts_le`). Across at most `Q_FS` queries to
   the lazy Fiat–Shamir oracle, the probability that any queried `(x, rt)` with `x ∉ L` passes all
   `m` PCP repetitions against `micaliExtractProof V tr x rt` is at most `Q_FS * (1 / 2) ^ m`.
   Combining this bound with `toOuterMeasure_run_memoize_not_traceCollisionFree_le` bounds a
   two-stage execution (a `Q_MT`-query Merkle phase followed by a `(t_FS + 1)`-query Fiat–Shamir
   phase) by `(t_FS + 1) * (1 / 2) ^ m + Q_MT * (Q_MT * (1 / 2 ^ σ))`.
3. **Full adaptive two-channel ROM soundness (`micaliSoundness_bound`).**
   When a single-stage cheating prover `P : OracleComp (MicaliSpec α) (α × MicaliProof)`
   interleaves Merkle hash queries (`Sum.inl`) and Fiat–Shamir queries (`Sum.inr`) arbitrarily, a
   fresh `σ`-bit Merkle digest preserves the extracted proof `micaliExtractProof V tr x rt` of
   every earlier Fiat–Shamir query `(x, rt)` unless it collides with an existing Merkle digest,
   inverts the left or right child of an existing Merkle query, or hits an earlier Fiat–Shamir root
   `rt` (`micaliExtractProof_cons_of_ne`). Bounding this joint bad event across `Q_MT` Merkle
   queries and `t_FS + 1` Fiat–Shamir queries (the prover's `t_FS` queries plus the verifier's
   evaluation query) yields Micali's unconditional ROM soundness bound:
   `micaliSoundnessGame V L P σ m true ≤`
   `(t_FS + 1) * (1 / 2) ^ m + Q_MT * ((3 * Q_MT + (t_FS + 1)) * (1 / 2 ^ σ))`.
4. **CS proofs for `NP` (`exists_micaliCSProof_of_mem_NP`).**
   Combining Micali's construction with the PCP theorem (`NP_subset_PCP_log`) gives unconditional
   non-interactive random-oracle CS proofs with polylogarithmic proof size for every language
   `L ∈ NP`, with compact PCP tables (`V.tableVerifier`) as the honest prover's witness relation.

The cited construction includes privacy parameters and a salt in the Fiat–Shamir query; here
that query is `(x, root)`. Our explicit error expression counts all Merkle queries in the prover
and verifier execution, including queries on malformed paths, and is not the source's literal
multi-extraction bound. The separate-budget corollary requires a verifier bound only for outputs
in `P.support`. Native verifier runtime, truncation, and polynomial-time conversion of arbitrary
NP witnesses to compact PCP tables are not established here.

## Main definitions

* `Cslib.Crypto.AllOpeningsQueriedInTrace`: all Merkle opening paths in a `KilianResponse` are
  recorded in a hash trace `tr`.
* `Cslib.Crypto.micaliExtractCompactTable`, `Cslib.Crypto.micaliExtractProof`: straight-line
  extraction of the compact bit table and full PCP proof from a Merkle trace `tr`.
* `Cslib.Crypto.FSTraceSound`, `Cslib.Crypto.MicaliGoodState`: soundness invariants on the
  Fiat–Shamir trace and combined `(tr_MT, tr_FS)` ROM state.
* `Cslib.Crypto.micaliMTCost`, `Cslib.Crypto.micaliFSCost`: per-channel query cost functions on
  `MicaliSpec α`.
* `Cslib.Crypto.micaliSoundnessProg`, `Cslib.Crypto.micaliSoundnessGame`,
  `Cslib.Crypto.micaliMemoize`: the Micali ROM soundness experiment and its list-cache handler.
* `Cslib.Crypto.micaliProofBits`: payload bit length of a `MicaliProof`.

## Main results

* `Cslib.Crypto.kilianVerify_sound_of_traceCollisionFree`,
  `Cslib.Crypto.micaliVerifyPure_sound_of_traceCollisionFree`,
  `Cslib.Crypto.not_traceCollisionFree_or_accepts_of_micaliVerifyPure`,
  `Cslib.Crypto.exists_collision_of_micaliVerifyPure_of_rejects`: pure fixed-trace soundness and
  dual collision extraction for Micali verification.
* `Cslib.Crypto.toOuterMeasure_kilianChallenges_accepts_le`,
  `Cslib.Crypto.toOuterMeasure_run_memoize_not_fsTraceSound_le`,
  `Cslib.Crypto.toOuterMeasure_twoStageMicali_le`: Fiat–Shamir challenge union bound and two-stage
  ROM soundness bound.
* `Cslib.Crypto.micaliExtractProof_cons_of_ne`: invariance of extracted PCP proofs under
  non-inverting Merkle trace extensions.
* `Cslib.Crypto.micaliSoundness_bound`, `Cslib.Crypto.micaliSoundness_bound_of_prover_verifier`:
  Micali's explicit ROM soundness theorem for adaptive two-channel cheating provers.
* `Cslib.Crypto.micaliProofBits_micaliProvePure_le`,
  `Cslib.Crypto.micaliProofBits_micaliProvePure_le_log`: succinctness of honest Micali proofs.
* `Cslib.Crypto.exists_micaliCSProof_of_mem_NP`: every language in `NP` has a Micali CS proof
  system in the random oracle model.

## References

* [S. Micali, *Computationally Sound Proofs*][Micali2000]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Construction 21.1.1 and Theorem 21.2.1, printed pp. 239–242, March 25, 2026 version.
* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [J. Kilian, *A note on efficient zero-knowledge proofs and arguments*][Kilian1992]
-/

@[expose] public section

namespace Cslib.Crypto

open Complexity Probability OracleComp Turing.MultiTapeTM
open scoped ENNReal

variable {α : Type}

/-! ### Part 1: Pure / Fixed-Trace Soundness Bridge -/

/-- Every Merkle authentication path in `response` for challenge strings `ρs` on statement `x` has
all of its hash steps recorded in `tr`. -/
def AllOpeningsQueriedInTrace (H : List Bool → List Bool → List Bool) (k : List Bool)
    (V : PCPVerifier α) (tr : List (List Bool × List Bool)) (x : α)
    (ρs : List (List Bool)) (response : KilianResponse) : Prop :=
  ∀ o ∈ kilianOpenings V x ρs response,
    PathQueriedInTrace H k tr (kilianPosition V x o.1) [o.2.1] o.2.2

instance (H : List Bool → List Bool → List Bool) (k : List Bool) (V : PCPVerifier α)
    (tr : List (List Bool × List Bool)) (x : α) (ρs : List (List Bool))
    (response : KilianResponse) :
    Decidable (AllOpeningsQueriedInTrace H k V tr x ρs response) :=
  inferInstanceAs (Decidable (∀ o ∈ kilianOpenings V x ρs response,
    PathQueriedInTrace H k tr (kilianPosition V x o.1) [o.2.1] o.2.2))

/-- Extract the compact bit table (of length `2 ^ kilianDepth V x`) committed under Merkle root
`rt` from a recorded hash query-answer trace `tr`, taking the first bit (`headD false`) of each
extracted leaf. -/
def micaliExtractCompactTable (V : PCPVerifier α) (tr : List (List Bool × List Bool))
    (x : α) (rt : List Bool) : List Bool :=
  (extractTableFromTrace tr (kilianDepth V x) rt []).map fun leaf => leaf.headD false

/-- Extract the full PCP proof (indexed by PCP addresses `a`) committed under Merkle root `rt`
from a recorded hash query-answer trace `tr`. -/
def micaliExtractProof (V : PCPVerifier α) (tr : List (List Bool × List Bool))
    (x : α) (rt : List Bool) : List Bool :=
  kilianProof V x fun j => (micaliExtractCompactTable V tr x rt).getD j false

@[simp]
theorem length_micaliExtractCompactTable (V : PCPVerifier α) (tr : List (List Bool × List Bool))
    (x : α) (rt : List Bool) :
    (micaliExtractCompactTable V tr x rt).length = 2 ^ kilianDepth V x := by
  simp [micaliExtractCompactTable]

theorem getD_micaliExtractCompactTable (V : PCPVerifier α) (tr : List (List Bool × List Bool))
    (x : α) (rt : List Bool) (i : ℕ) :
    (micaliExtractCompactTable V tr x rt).getD i false =
      ((extractTableFromTrace tr (kilianDepth V x) rt []).getD i []).headD false := by
  unfold micaliExtractCompactTable
  by_cases hi : i < (extractTableFromTrace tr (kilianDepth V x) rt []).length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi,
      List.getElem_map]
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt (by simpa using hi)),
      List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    rfl

/-- If `tr` is collision-free and records the authentication path of an accepted one-bit leaf
`[b]` at position `i`, then entry `i` of `micaliExtractCompactTable V tr x rt` is `b`. -/
theorem getD_micaliExtractCompactTable_eq_of_merkleVerify
    {H : List Bool → List Bool → List Bool} {k : List Bool} {V : PCPVerifier α}
    {tr : List (List Bool × List Bool)} {x : α} {rt : List Bool} {i : ℕ} {b : Bool}
    {path : List (List Bool)} (hfree : TraceCollisionFree tr)
    (hpath : PathQueriedInTrace H k tr i [b] path)
    (hver : merkleVerify H k (kilianDepth V x) rt i [b] path = true) :
    (micaliExtractCompactTable V tr x rt).getD i false = b := by
  rw [getD_micaliExtractCompactTable,
    getD_extractTableFromTrace_eq_of_merkleVerify hfree hpath hver, List.headD_cons]

/-- **Fixed-trace soundness of `kilianVerify`**: if `tr` is collision-free and records all hash
steps of every opening in `response`, then `kilianVerify H V k x rt ρs response = true` implies
that the PCP verifier `V` accepts the single extracted proof `micaliExtractProof V tr x rt` on
every challenge string `ρ ∈ ρs` of length `V.coins x`. -/
theorem kilianVerify_sound_of_traceCollisionFree
    {H : List Bool → List Bool → List Bool} {k : List Bool} {V : PCPVerifier α}
    {tr : List (List Bool × List Bool)} {x : α} {rt : List Bool}
    {ρs : List (List Bool)} {response : KilianResponse}
    (hfree : TraceCollisionFree tr)
    (hpaths : AllOpeningsQueriedInTrace H k V tr x ρs response)
    (hver : kilianVerify H V k x rt ρs response = true)
    {ρ : List Bool} (hρ : ρ ∈ ρs) (hlen : ρ.length = V.coins x) :
    V.accepts x (micaliExtractProof V tr x rt) ρ = true := by
  refine accepts_kilianProof hver (fun o ho => ?_) hρ hlen
  exact (getD_micaliExtractCompactTable_eq_of_merkleVerify hfree (hpaths o ho)
    (merkleVerify_of_mem_kilianOpenings hver ho)).symm

/-- **Pure / fixed-trace soundness bridge for Micali verification**
([ChiesaYogev2024], Lemma 18.5.7 and Theorem 21.2.1): if `tr` is collision-free and records all
hash steps of the openings in `proof : MicaliProof`, then
`micaliVerifyPure hTree hFS V x proof = true` implies that the PCP verifier `V` accepts the
extracted proof `micaliExtractProof V tr x proof.root` on every challenge string
`ρ ∈ hFS (x, proof.root)` of length `V.coins x`. -/
theorem micaliVerifyPure_sound_of_traceCollisionFree
    {hTree : List Bool → List Bool} {hFS : α × List Bool → List (List Bool)}
    {V : PCPVerifier α} {tr : List (List Bool × List Bool)} {x : α} {proof : MicaliProof}
    (hfree : TraceCollisionFree tr)
    (hpaths : AllOpeningsQueriedInTrace (fun _ => hTree) [] V tr x
      (hFS (x, proof.root)) proof.response)
    (hver : micaliVerifyPure hTree hFS V x proof = true)
    {ρ : List Bool} (hρ : ρ ∈ hFS (x, proof.root)) (hlen : ρ.length = V.coins x) :
    V.accepts x (micaliExtractProof V tr x proof.root) ρ = true :=
  kilianVerify_sound_of_traceCollisionFree hfree hpaths hver hρ hlen

/-- **Disjunctive fixed-trace soundness of `micaliVerifyPure`**: if `micaliVerifyPure` accepts
`proof` and all opened paths are in `tr`, then either `tr` contains a hash collision
(`¬ TraceCollisionFree tr`) or `V` accepts the extracted proof
`micaliExtractProof V tr x proof.root` on every challenge string of length `V.coins x` in
`hFS (x, proof.root)`. -/
theorem not_traceCollisionFree_or_accepts_of_micaliVerifyPure
    {hTree : List Bool → List Bool} {hFS : α × List Bool → List (List Bool)}
    {V : PCPVerifier α} {tr : List (List Bool × List Bool)} {x : α} {proof : MicaliProof}
    (hpaths : AllOpeningsQueriedInTrace (fun _ => hTree) [] V tr x
      (hFS (x, proof.root)) proof.response)
    (hver : micaliVerifyPure hTree hFS V x proof = true) :
    ¬ TraceCollisionFree tr ∨
      ∀ ρ ∈ hFS (x, proof.root), ρ.length = V.coins x →
        V.accepts x (micaliExtractProof V tr x proof.root) ρ = true := by
  by_cases hfree : TraceCollisionFree tr
  · exact Or.inr fun ρ hρ hlen =>
      micaliVerifyPure_sound_of_traceCollisionFree hfree hpaths hver hρ hlen
  · exact Or.inl hfree

/-- **Dual collision extraction for `micaliVerifyPure`**: if `tr` is consistent with `H k` and
records all opened paths of a proof accepted by `micaliVerifyPure (H k) hFS V x proof`, yet `V`
rejects the extracted proof `micaliExtractProof V tr x proof.root` on some challenge
`ρ ∈ hFS (x, proof.root)` of length `V.coins x`, then `tr` contains two distinct queries with the
same hash under `H k`. -/
theorem exists_collision_of_micaliVerifyPure_of_rejects
    {H : List Bool → List Bool → List Bool} {k : List Bool}
    {hFS : α × List Bool → List (List Bool)} {V : PCPVerifier α}
    {tr : List (List Bool × List Bool)} {x : α} {proof : MicaliProof}
    (hcons : TraceConsistentWith (H k) tr)
    (hpaths : AllOpeningsQueriedInTrace H k V tr x (hFS (x, proof.root)) proof.response)
    (hver : micaliVerifyPure (H k) hFS V x proof = true)
    {ρ : List Bool} (hρ : ρ ∈ hFS (x, proof.root)) (hlen : ρ.length = V.coins x)
    (hrej : V.accepts x (micaliExtractProof V tr x proof.root) ρ = false) :
    ∃ q₁ ∈ tr.map Prod.fst, ∃ q₂ ∈ tr.map Prod.fst, q₁ ≠ q₂ ∧ H k q₁ = H k q₂ := by
  have hnot_all : ¬ ∀ o ∈ kilianOpenings V x (hFS (x, proof.root)) proof.response,
      extractLeafFromTrace tr (kilianDepth V x) proof.root (kilianPosition V x o.1) =
        some [o.2.1] := by
    intro hall
    have hacc : V.accepts x (micaliExtractProof V tr x proof.root) ρ = true := by
      refine accepts_kilianProof hver (fun o ho => ?_) hρ hlen
      have hleaf := hall o ho
      have hi : kilianPosition V x o.1 < 2 ^ kilianDepth V x := by
        have hm := merkleVerify_of_mem_kilianOpenings hver ho
        simp only [merkleVerify, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hm
        exact hm.1.2
      rw [getD_micaliExtractCompactTable, getD_extractTableFromTrace hi, hleaf,
        Option.getD_some, List.headD_cons]
    rw [hacc] at hrej
    cases hrej
  push Not at hnot_all
  obtain ⟨o, ho, hne⟩ := hnot_all
  have hpath_o : PathQueriedInTrace H k tr (kilianPosition V x o.1) [o.2.1] o.2.2 := hpaths o ho
  have hver_o : merkleVerify H k (kilianDepth V x) proof.root
      (kilianPosition V x o.1) [o.2.1] o.2.2 = true :=
    merkleVerify_of_mem_kilianOpenings (H := H) (k := k) hver ho
  exact exists_collision_of_extractLeafFromTrace_ne hcons hpath_o hver_o hne

/-! ### Part 2: Fiat–Shamir Challenge Union Bound & Two-Stage ROM Soundness -/

/-- One PCP repetition accepts a fixed candidate proof `π` of a statement `x` with soundness
bound `2 * acceptCount ... ≤ 2 ^ V.coins x` with probability at most `1 / 2` in `ℝ≥0∞`. -/
theorem toOuterMeasure_sampleList_accepts_le (V : PCPVerifier α) {x : α} {π : List Bool}
    (hsound : 2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x) :
    (ProbComp.eval (BitString.sampleList (V.coins x))).toOuterMeasure
      {ρ | V.accepts x π ρ = true} ≤ 1 / 2 := by
  have hmap : (ProbComp.eval (BitString.sampleList (V.coins x))).toOuterMeasure
      {ρ | V.accepts x π ρ = true} =
      ((BitString.uniformList (V.coins x)).map fun ρ => V.accepts x π ρ) true := by
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      BitString.eval_sampleList]
    rfl
  rw [hmap, uniformList_acceptCount (V := fun y => V.accepts y.1 π y.2),
    ENNReal.div_le_iff_le_mul (Or.inl (by positivity)) (Or.inl (by finiteness))]
  calc (acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) : ℝ≥0∞)
      = 1 / 2 * (2 * (acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) : ℝ≥0∞)) := by
        rw [← mul_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ 1 / 2 * (2 : ℝ≥0∞) ^ V.coins x := by
        gcongr
        exact_mod_cast hsound

/-- Across `m` independent PCP challenge strings `kilianChallenges V m x`, a fixed candidate proof
`π` for `x` with per-repetition soundness error `≤ 1 / 2` is accepted on all `m` repetitions with
probability at most `(1 / 2) ^ m`. -/
theorem toOuterMeasure_kilianChallenges_accepts_le (V : PCPVerifier α) (m : ℕ) {x : α}
    {π : List Bool}
    (hsound : 2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x) :
    (ProbComp.eval (kilianChallenges V m x)).toOuterMeasure
      {ρs | ∀ ρ ∈ ρs, V.accepts x π ρ = true} ≤ (1 / 2) ^ m := by
  rw [kilianChallenges, ProbComp.toOuterMeasure_replicate_forall]
  exact pow_le_pow_left' (toOuterMeasure_sampleList_accepts_le V hsound) m

/-- A Fiat–Shamir query-answer trace `tr_FS` has no accepting false-statement entry relative to the
Merkle trace `tr` if for every recorded `((x, rt), ρs) ∈ tr_FS` with `x ∉ L`, the PCP verifier `V`
rejects `micaliExtractProof V tr x rt` on at least one challenge `ρ ∈ ρs`. -/
def FSTraceSound (V : PCPVerifier α) (L : Set α) (tr : List (List Bool × List Bool))
    (tr_FS : List ((α × List Bool) × List (List Bool))) : Prop :=
  ∀ e ∈ tr_FS, e.1.1 ∉ L →
    ¬ ∀ ρ ∈ e.2, V.accepts e.1.1 (micaliExtractProof V tr e.1.1 e.1.2) ρ = true

@[simp]
theorem fsTraceSound_nil (V : PCPVerifier α) (L : Set α) (tr : List (List Bool × List Bool)) :
    FSTraceSound V L tr [] := by
  intro _ he
  cases he

theorem fsTraceSound_cons_iff {V : PCPVerifier α} {L : Set α}
    {tr : List (List Bool × List Bool)} {x : α} {rt : List Bool} {ρs : List (List Bool)}
    {tr_FS : List ((α × List Bool) × List (List Bool))} :
    FSTraceSound V L tr (((x, rt), ρs) :: tr_FS) ↔
      (x ∉ L → ¬ ∀ ρ ∈ ρs, V.accepts x (micaliExtractProof V tr x rt) ρ = true) ∧
        FSTraceSound V L tr tr_FS :=
  List.forall_mem_cons

/-- **Single-step Fiat–Shamir bad-event bound**: from a Fiat–Shamir trace `tr_FS` satisfying
`FSTraceSound V L tr tr_FS`, one call to the lazy Fiat–Shamir oracle violates `FSTraceSound` with
probability at most `(1 / 2) ^ m`. -/
theorem toOuterMeasure_memoize_not_fsTraceSound_step [BEq α] (V : PCPVerifier α) (L : Set α)
    (m : ℕ) (tr : List (List Bool × List Bool))
    (hsound : ∀ x ∉ L, ∀ π : List Bool,
      2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x)
    (q : α × List Bool) {tr_FS : List ((α × List Bool) × List (List Bool))}
    (htr : FSTraceSound V L tr tr_FS) :
    (memoize (fun q : α × List Bool => ProbComp.eval (kilianChallenges V m q.1))
      q tr_FS).toOuterMeasure {out | ¬ FSTraceSound V L tr out.2} ≤ (1 / 2) ^ m := by
  rcases q with ⟨x, rt⟩
  cases hlookup : tr_FS.lookup (x, rt) with
  | some ρs =>
    rw [memoize_of_some _ _ _ _ hlookup, PMF.monad_pure_eq_pure, PMF.toOuterMeasure_pure_apply]
    simp [htr]
  | none =>
    rw [memoize_of_none _ _ _ hlookup]
    change ((ProbComp.eval (kilianChallenges V m x)).map
      (fun ρs => (ρs, ((x, rt), ρs) :: tr_FS))).toOuterMeasure
      {out | ¬ FSTraceSound V L tr out.2} ≤ _
    rw [PMF.toOuterMeasure_map_apply]
    by_cases hx : x ∈ L
    · have hempty : {ρs : List (List Bool) |
          ¬ FSTraceSound V L tr (((x, rt), ρs) :: tr_FS)} = ∅ := by
        ext ρs
        simp [fsTraceSound_cons_iff, hx, htr]
      simp [hempty]
    · calc (ProbComp.eval (kilianChallenges V m x)).toOuterMeasure
            {ρs | ¬ FSTraceSound V L tr (((x, rt), ρs) :: tr_FS)}
          ≤ (ProbComp.eval (kilianChallenges V m x)).toOuterMeasure
            {ρs | ∀ ρ ∈ ρs, V.accepts x (micaliExtractProof V tr x rt) ρ = true} := by
            refine (ProbComp.eval (kilianChallenges V m x)).toOuterMeasure.mono fun ρs hbad => ?_
            change ¬ FSTraceSound V L tr (((x, rt), ρs) :: tr_FS) at hbad
            rw [fsTraceSound_cons_iff] at hbad
            by_contra hnot
            exact hbad ⟨fun _ => hnot, htr⟩
        _ ≤ (1 / 2) ^ m :=
            toOuterMeasure_kilianChallenges_accepts_le V m (hsound x hx _)

/-- **Fiat–Shamir challenge union bound**: any program making at most `Q_FS` queries to the lazy
Fiat–Shamir oracle starting from the empty trace violates `FSTraceSound V L tr` with probability at
most `Q_FS * (1 / 2) ^ m`. -/
theorem toOuterMeasure_run_memoize_not_fsTraceSound_le [BEq α] {β : Type}
    (V : PCPVerifier α) (L : Set α) (m : ℕ) (tr : List (List Bool × List Bool))
    (hsound : ∀ x ∉ L, ∀ π : List Bool,
      2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x)
    {prog : OracleComp (MicaliFSSpec α) β} {Q_FS : ℕ} (hQ : IsQueryBounded prog Q_FS) :
    ((OracleComp.interpret
      (memoize (fun q : α × List Bool => ProbComp.eval (kilianChallenges V m q.1)))
      prog).run []).toOuterMeasure {out | ¬ FSTraceSound V L tr out.2} ≤
      (Q_FS : ℝ≥0∞) * (1 / 2) ^ m := by
  have hbound := OracleComp.toOuterMeasure_bad_le
    (handler := memoize (fun q : α × List Bool => ProbComp.eval (kilianChallenges V m q.1)))
    (bad := fun tr_FS => ¬ FSTraceSound V L tr tr_FS)
    (fun _ => 1)
    (fun _ => (1 / 2) ^ m)
    0
    (fun q tr_FS htr => by
      rw [Nat.cast_one, one_mul]
      exact toOuterMeasure_memoize_not_fsTraceSound_step V L m tr hsound q (not_not.mp htr))
    (fun _ _ _ _ _ _ => le_self_add)
    hQ hQ (s := []) (not_not.mpr (fsTraceSound_nil V L tr))
  refine hbound.trans (le_of_eq ?_)
  rw [mul_zero, add_zero]

/-- **Two-stage ROM soundness bound** (combining
`toOuterMeasure_run_memoize_not_traceCollisionFree_le` with
`toOuterMeasure_run_memoize_not_fsTraceSound_le`): if a first stage `mtProg` makes at most `Q_MT`
queries to a uniform `σ`-bit Merkle random oracle (producing a state `st` and Merkle trace `tr`) and
a second stage `fsProg st` makes at most `t_FS + 1` queries to the Fiat–Shamir random oracle
(producing a Fiat–Shamir trace `tr_FS`), then the probability that either `tr` has a collision or
`tr_FS` violates `FSTraceSound V L tr` is at most
`(t_FS + 1) * (1 / 2) ^ m + Q_MT * (Q_MT * (1 / 2 ^ σ))`. -/
theorem toOuterMeasure_twoStageMicali_le [BEq α] {γ β : Type}
    (V : PCPVerifier α) (L : Set α) (σ m : ℕ)
    (hsound : ∀ x ∉ L, ∀ π : List Bool,
      2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x)
    {mtProg : OracleComp MerkleHashSpec γ} {fsProg : γ → OracleComp (MicaliFSSpec α) β}
    {Q_MT t_FS : ℕ} (hMT : IsQueryBounded mtProg Q_MT)
    (hFS : ∀ st, IsQueryBounded (fsProg st) (t_FS + 1)) :
    (((OracleComp.interpret (memoize (fun _ : List Bool => BitString.uniformList σ))
      mtProg).run []).bind fun (st, tr) =>
        ((OracleComp.interpret
          (memoize (fun q : α × List Bool => ProbComp.eval (kilianChallenges V m q.1)))
          (fsProg st)).run []).map fun (res, tr_FS) =>
            (res, tr, tr_FS)).toOuterMeasure
      {out | ¬ TraceCollisionFree out.2.1 ∨ ¬ FSTraceSound V L out.2.1 out.2.2} ≤
      ((t_FS + 1 : ℕ) : ℝ≥0∞) * (1 / 2) ^ m +
        (Q_MT : ℝ≥0∞) * ((Q_MT : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  refine (Probability.PMF.toOuterMeasure_bind_failure_le _ _
    {y | TraceCollisionFree y.2} _ (((t_FS + 1 : ℕ) : ℝ≥0∞) * (1 / 2) ^ m) ?_).trans ?_
  · rintro ⟨st, tr⟩ _ hcol
    change TraceCollisionFree tr at hcol
    rw [PMF.toOuterMeasure_map_apply]
    refine (?_ : _ ≤ ((OracleComp.interpret
      (memoize (fun q : α × List Bool => ProbComp.eval (kilianChallenges V m q.1)))
      (fsProg st)).run []).toOuterMeasure {y | ¬ FSTraceSound V L tr y.2}).trans
      (toOuterMeasure_run_memoize_not_fsTraceSound_le V L m tr hsound (hFS st))
    refine ((OracleComp.interpret
      (memoize (fun q : α × List Bool => ProbComp.eval (kilianChallenges V m q.1)))
      (fsProg st)).run []).toOuterMeasure.mono fun y hy => ?_
    exact Or.resolve_left hy (not_not.mpr hcol)
  · exact (add_le_add (toOuterMeasure_run_memoize_not_traceCollisionFree_le σ hMT) le_rfl).trans
      (add_comm _ _).le

/-! ### Part 3: Full Adaptive Two-Channel ROM Soundness -/

/-! #### Invariance of trace extraction under non-inverting Merkle additions -/

/-- Prepending `(q, ans)` to `tr` leaves `micaliExtractProof` at `rt` unchanged whenever `ans ≠ rt`
and `ans` does not equal `unframe p.1` or `dropFrame p.1` for any `p ∈ tr`. -/
theorem micaliExtractProof_cons_of_ne (V : PCPVerifier α) (tr : List (List Bool × List Bool))
    (q : List Bool) {ans rt : List Bool} (x : α) (hrt : ans ≠ rt)
    (hchildren : ∀ p ∈ tr, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1) :
    micaliExtractProof V ((q, ans) :: tr) x rt = micaliExtractProof V tr x rt := by
  simp only [micaliExtractProof, micaliExtractCompactTable,
    extractTableFromTrace_cons_of_ne tr q (kilianDepth V x) [] hrt hchildren]

/-! #### Two-channel query costs, good-state invariant, and accumulated bad-state lemma -/

/-- Cost of a Micali oracle call on the Merkle hash channel (`Sum.inl`). -/
def micaliMTCost : List Bool ⊕ (α × List Bool) → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Cost of a Micali oracle call on the Fiat–Shamir channel (`Sum.inr`). -/
def micaliFSCost : List Bool ⊕ (α × List Bool) → ℕ
  | .inl _ => 0
  | .inr _ => 1

/-- Any `MerkleHashSpec` program lifted to `MicaliSpec α` via `liftLeft` makes `0` Fiat–Shamir
calls. -/
theorem isCostBounded_micaliFSCost_liftLeft {β : Type} (prog : OracleComp MerkleHashSpec β) :
    IsCostBounded (micaliFSCost (α := α))
      (OracleComp.liftLeft (spec₂ := MicaliFSSpec α) prog) 0 := by
  induction prog with
  | pure a => exact .pure a 0
  | liftBind q cont ih =>
    change IsCostBounded micaliFSCost
      (OracleComp.query (spec := MicaliSpec α) (.inl q) >>=
        fun a => OracleComp.liftLeft (spec₂ := MicaliFSSpec α) (cont a)) 0
    exact IsCostBounded.liftBind (cost := micaliFSCost) (Sum.inl q) _ 0 ih

/-- Any `IsQueryBounded prog k` over `MerkleHashSpec` lifts via `liftLeft` to
`IsCostBounded micaliMTCost (liftLeft prog) k`. -/
theorem isCostBounded_micaliMTCost_liftLeft {β : Type} {prog : OracleComp MerkleHashSpec β}
    {k : ℕ} (h : IsQueryBounded prog k) :
    IsCostBounded (micaliMTCost (α := α))
      (OracleComp.liftLeft (spec₂ := MicaliFSSpec α) prog) k := by
  induction h with
  | pure a n => exact .pure a n
  | liftBind q cont n _ ih =>
    change IsCostBounded micaliMTCost
      (OracleComp.query (spec := MicaliSpec α) (.inl q) >>=
        fun a => OracleComp.liftLeft (spec₂ := MicaliFSSpec α) (cont a)) (n + 1)
    exact IsCostBounded.liftBind (cost := micaliMTCost) (Sum.inl q) _ n ih

/-- `micaliVerify V x proof` always makes at most `1` Fiat–Shamir query (`(x, proof.root)`). -/
theorem isCostBounded_micaliFSCost_micaliVerify (V : PCPVerifier α) (x : α) (proof : MicaliProof) :
    IsCostBounded micaliFSCost (micaliVerify V x proof) 1 := by
  unfold micaliVerify
  have hq : IsCostBounded micaliFSCost
      (OracleComp.liftRight (spec₁ := MerkleHashSpec)
        (OracleComp.query (spec := MicaliFSSpec α) (x, proof.root))) 1 :=
    IsCostBounded.query (spec := MicaliSpec α) (cost := micaliFSCost) (Sum.inr (x, proof.root))
  exact hq.bind fun ρs =>
    isCostBounded_micaliFSCost_liftLeft (kilianVerifyProg V x proof.root ρs proof.response)

open Classical in
/-- The Micali soundness execution as an `OracleComp (MicaliSpec α)` program: run the cheating
prover `P` to obtain `(x, proof)`, run `micaliVerify V x proof`, and return `true` when `x ∉ L` and
the verifier accepts. -/
noncomputable def micaliSoundnessProg (V : PCPVerifier α) (L : Set α)
    (P : OracleComp (MicaliSpec α) (α × MicaliProof)) : OracleComp (MicaliSpec α) Bool := do
  let (x, proof) ← P
  let ok ← micaliVerify V x proof
  return decide (x ∉ L) && ok

/-- If the cheating prover `P` makes at most `t_FS` Fiat–Shamir queries, then
`micaliSoundnessProg V L P` makes at most `t_FS + 1` Fiat–Shamir queries. -/
theorem isCostBounded_micaliFSCost_micaliSoundnessProg (V : PCPVerifier α) (L : Set α)
    {P : OracleComp (MicaliSpec α) (α × MicaliProof)} {t_FS : ℕ}
    (hFS : IsCostBounded micaliFSCost P t_FS) :
    IsCostBounded micaliFSCost (micaliSoundnessProg V L P) (t_FS + 1) := by
  unfold micaliSoundnessProg
  open Classical in
  exact hFS.bind fun (x, proof) =>
    (isCostBounded_micaliFSCost_micaliVerify V x proof).bind fun ok =>
      IsCostBounded.pure (decide (x ∉ L) && ok) 0

/-- If `P` makes at most `t_MT` Merkle hash queries and `micaliVerify V x proof` makes at most
`q_V` Merkle hash queries for every `(x, proof)` that `P` can output, then
`micaliSoundnessProg V L P` makes at most `t_MT + q_V` Merkle hash queries. -/
theorem isCostBounded_micaliMTCost_micaliSoundnessProg (V : PCPVerifier α) (L : Set α)
    {P : OracleComp (MicaliSpec α) (α × MicaliProof)} {t_MT q_V : ℕ}
    (hMT : IsCostBounded micaliMTCost P t_MT)
    (hV : ∀ x proof, (x, proof) ∈ P.support →
      IsCostBounded micaliMTCost (micaliVerify V x proof) q_V) :
    IsCostBounded micaliMTCost (micaliSoundnessProg V L P) (t_MT + q_V) := by
  unfold micaliSoundnessProg
  open Classical in
  exact hMT.bind_on_support fun (x, proof) hmem =>
    (hV x proof hmem).bind fun ok =>
      IsCostBounded.pure (decide (x ∉ L) && ok) 0

/-- The Micali ROM soundness experiment with `σ`-bit Merkle digests and `m` PCP repetitions: runs
`micaliSoundnessProg V L P` against the shared lazy random oracle
`RandomOracle.answer (micaliOracleDist V σ m)` starting from an empty cache. -/
noncomputable def micaliSoundnessGame [DecidableEq α] (V : PCPVerifier α) (L : Set α)
    (P : OracleComp (MicaliSpec α) (α × MicaliProof)) (σ m : ℕ) : PMF Bool :=
  (OracleComp.runWith (RandomOracle.answer (micaliOracleDist V σ m))
    (micaliSoundnessProg V L P) (fun _ => none)).map Prod.fst

/-- List-cache state for the two-channel Micali random oracle: a Merkle hash trace and a
Fiat–Shamir challenge trace. -/
abbrev MicaliTraceState (α : Type) :=
  List (List Bool × List Bool) × List ((α × List Bool) × List (List Bool))

/-- Two-channel association-list handler implementing
`RandomOracle.answer (micaliOracleDist V σ m)`. -/
noncomputable def micaliMemoize [BEq α] (V : PCPVerifier α) (σ m : ℕ) :
    (q : List Bool ⊕ (α × List Bool)) → StateT (MicaliTraceState α) PMF (MicaliSpec α q)
  | .inl msg => fun (tr_MT, tr_FS) =>
    (memoize (fun _ : List Bool => BitString.uniformList σ) msg tr_MT).map fun (ans, tr_MT') =>
      (ans, (tr_MT', tr_FS))
  | .inr xrt => fun (tr_MT, tr_FS) =>
    (memoize (fun q : α × List Bool => ProbComp.eval (kilianChallenges V m q.1)) xrt tr_FS).map
      fun (ρs, tr_FS') => (ρs, (tr_MT, tr_FS'))

/-- Represent a `MicaliTraceState α` as a `RandomOracle.Cache (MicaliSpec α)`. -/
def micaliOfTraces [BEq α] (st : MicaliTraceState α) : RandomOracle.Cache (MicaliSpec α)
  | .inl msg => RandomOracle.ofList st.1 msg
  | .inr xrt => RandomOracle.ofList st.2 xrt

@[simp]
theorem micaliOfTraces_nil [BEq α] :
    micaliOfTraces (α := α) ([], []) = fun _ => none := by
  funext q
  cases q <;> rfl

/-- `micaliMemoize` implements `RandomOracle.answer (micaliOracleDist V σ m)` via
`micaliOfTraces`. -/
theorem run_interpret_micaliMemoize [DecidableEq α] (V : PCPVerifier α) (σ m : ℕ) {β : Type}
    (prog : OracleComp (MicaliSpec α) β) (st : MicaliTraceState α) :
    ((OracleComp.interpret (micaliMemoize V σ m) prog).run st).map
        (fun (res, st') => (res, micaliOfTraces st')) =
      OracleComp.runWith (RandomOracle.answer (micaliOracleDist V σ m)) prog
        (micaliOfTraces st) := by
  apply OracleComp.run_interpret_map_state
  rintro (msg | ⟨x, rt⟩) ⟨tr_MT, tr_FS⟩
  · dsimp only [micaliMemoize]
    cases h : tr_MT.lookup msg with
    | none =>
      rw [memoize_of_none _ _ _ h,
        RandomOracle.answer_of_none (micaliOracleDist V σ m) (micaliOfTraces (tr_MT, tr_FS))
          (.inl msg) h]
      change (((BitString.uniformList σ).map (fun v => (v, (msg, v) :: tr_MT))).map _).map _ = _
      simp only [PMF.map_comp, Function.comp_def, micaliOracleDist]
      congr 2
      funext v
      simp only [Prod.mk.injEq, true_and]
      funext q
      cases q with
      | inl msg' =>
        simpa [micaliOfTraces] using congrFun (RandomOracle.ofList_cons tr_MT msg v) msg'
      | inr xrt' =>
        simp [micaliOfTraces]
    | some val =>
      rw [memoize_of_some _ _ _ _ h,
        RandomOracle.answer_of_some (micaliOracleDist V σ m) (micaliOfTraces (tr_MT, tr_FS))
          (.inl msg) val h]
      simp [PMF.monad_pure_eq_pure]
  · dsimp only [micaliMemoize]
    cases h : tr_FS.lookup (x, rt) with
    | none =>
      rw [memoize_of_none _ _ _ h,
        RandomOracle.answer_of_none (micaliOracleDist V σ m) (micaliOfTraces (tr_MT, tr_FS))
          (.inr (x, rt)) h]
      change (((ProbComp.eval (kilianChallenges V m x)).map
        (fun v => (v, ((x, rt), v) :: tr_FS))).map _).map _ = _
      simp only [PMF.map_comp, Function.comp_def, micaliOracleDist]
      congr 2
      funext v
      simp only [Prod.mk.injEq, true_and]
      funext q
      cases q with
      | inl msg' =>
        simp [micaliOfTraces]
      | inr xrt' =>
        simpa [micaliOfTraces] using congrFun (RandomOracle.ofList_cons tr_FS (x, rt) v) xrt'
    | some val =>
      rw [memoize_of_some _ _ _ _ h,
        RandomOracle.answer_of_some (micaliOracleDist V σ m) (micaliOfTraces (tr_MT, tr_FS))
          (.inr (x, rt)) val h]
      simp [PMF.monad_pure_eq_pure]

/-- `micaliSoundnessGame` has the same output distribution as running `micaliSoundnessProg` under
`micaliMemoize` from the empty trace pair `([], [])`. -/
theorem micaliSoundnessGame_eq_run_micaliMemoize [DecidableEq α] (V : PCPVerifier α) (L : Set α)
    (P : OracleComp (MicaliSpec α) (α × MicaliProof)) (σ m : ℕ) :
    micaliSoundnessGame V L P σ m =
      ((OracleComp.interpret (micaliMemoize V σ m) (micaliSoundnessProg V L P)).run ([], [])).map
        Prod.fst := by
  have h := congrArg (PMF.map Prod.fst)
    (run_interpret_micaliMemoize V σ m (micaliSoundnessProg V L P) ([], []))
  simpa only [micaliSoundnessGame, PMF.map_comp, Function.comp_def, micaliOfTraces_nil] using h.symm

/-- Good-state invariant of the two-channel Micali ROM state `(tr_MT, tr_FS)`: the Merkle trace
`tr_MT` is collision-free and the Fiat–Shamir trace `tr_FS` has no accepting false-statement entry
relative to `tr_MT`. -/
def MicaliGoodState (V : PCPVerifier α) (L : Set α) (st : MicaliTraceState α) : Prop :=
  TraceCollisionFree st.1 ∧ FSTraceSound V L st.1 st.2

@[simp]
theorem micaliGoodState_nil (V : PCPVerifier α) (L : Set α) :
    MicaliGoodState V L ([], []) :=
  ⟨traceCollisionFree_nil, fsTraceSound_nil V L []⟩

/-- The list of digests in `st = (tr_MT, tr_FS)` that a fresh Merkle hash answer must avoid in
order to preserve `MicaliGoodState`: existing Merkle outputs, left/right child digests of existing
Merkle queries, and roots of existing Fiat–Shamir queries. -/
def micaliForbiddenDigests (st : MicaliTraceState α) : List (List Bool) :=
  st.1.map Prod.snd ++ st.1.map (fun p => unframe p.1) ++
    st.1.map (fun p => dropFrame p.1) ++ st.2.map (fun e => e.1.2)

@[simp]
theorem length_micaliForbiddenDigests (st : MicaliTraceState α) :
    (micaliForbiddenDigests st).length = 3 * st.1.length + st.2.length := by
  simp only [micaliForbiddenDigests, List.length_append, List.length_map]
  omega

/-- If `MicaliGoodState V L st` holds and prepending `(msg, ans)` to `st.1` violates
`MicaliGoodState`, then `ans` belongs to `micaliForbiddenDigests st`. -/
theorem mem_micaliForbiddenDigests_of_not_micaliGoodState_cons
    {V : PCPVerifier α} {L : Set α} {st : MicaliTraceState α} {msg ans : List Bool}
    (hgood : MicaliGoodState V L st)
    (hbad : ¬ MicaliGoodState V L ((msg, ans) :: st.1, st.2)) :
    ans ∈ micaliForbiddenDigests st := by
  rcases st with ⟨tr_MT, tr_FS⟩
  obtain ⟨hfree, hfs⟩ := hgood
  by_contra hnot_mem
  simp only [micaliForbiddenDigests, List.mem_append, List.mem_map, not_or, not_exists,
    not_and] at hnot_mem
  obtain ⟨⟨⟨hnot_snd, hnot_left⟩, hnot_right⟩, hnot_rt⟩ := hnot_mem
  apply hbad
  refine ⟨?_, ?_⟩
  · rw [traceCollisionFree_cons_iff]
    refine ⟨hfree, fun p hp heq => ?_⟩
    exact False.elim (hnot_snd p hp heq)
  · intro e he hx
    have hrt : ans ≠ e.1.2 := fun heq => hnot_rt e he heq.symm
    have hchildren : ∀ p ∈ tr_MT, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1 :=
      fun p hp => ⟨fun heq => hnot_left p hp heq.symm, fun heq => hnot_right p hp heq.symm⟩
    rw [micaliExtractProof_cons_of_ne V tr_MT msg e.1.1 hrt hchildren]
    exact hfs e he hx

/-- **Single-step bad-state bound for `micaliMemoize`**: from a good state `st`, a call `q`
violates `MicaliGoodState V L` with probability at most
`micaliMTCost q * ((3 * st.1.length + st.2.length) * (1 / 2 ^ σ)) +`
`micaliFSCost q * (1 / 2) ^ m`. -/
theorem toOuterMeasure_micaliMemoize_not_goodState_step [BEq α]
    (V : PCPVerifier α) (L : Set α) (σ m : ℕ)
    (hsound : ∀ x ∉ L, ∀ π : List Bool,
      2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x)
    (q : List Bool ⊕ (α × List Bool)) {st : MicaliTraceState α}
    (hst : MicaliGoodState V L st) :
    (micaliMemoize V σ m q st).toOuterMeasure {out | ¬ MicaliGoodState V L out.2} ≤
      (micaliMTCost q : ℝ≥0∞) *
        (((3 * st.1.length + st.2.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) +
      (micaliFSCost q : ℝ≥0∞) * (1 / 2) ^ m := by
  rcases st with ⟨tr_MT, tr_FS⟩
  cases q with
  | inl msg =>
    simp only [micaliMTCost, micaliFSCost, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul,
      add_zero, micaliMemoize, PMF.toOuterMeasure_map_apply]
    cases hlookup : tr_MT.lookup msg with
    | some ans =>
      rw [memoize_of_some _ _ _ _ hlookup, PMF.monad_pure_eq_pure, PMF.toOuterMeasure_pure_apply]
      simp [hst]
    | none =>
      rw [memoize_of_none _ _ _ hlookup]
      change ((BitString.uniformList σ).map (fun ans => (ans, (msg, ans) :: tr_MT))).toOuterMeasure
        {x | ¬ MicaliGoodState V L (x.2, tr_FS)} ≤ _
      rw [PMF.toOuterMeasure_map_apply]
      calc (BitString.uniformList σ).toOuterMeasure
            {ans | ¬ MicaliGoodState V L ((msg, ans) :: tr_MT, tr_FS)}
          ≤ (BitString.uniformList σ).toOuterMeasure
            {ans | ans ∈ micaliForbiddenDigests (tr_MT, tr_FS)} := by
            refine (BitString.uniformList σ).toOuterMeasure.mono fun ans hans => ?_
            exact mem_micaliForbiddenDigests_of_not_micaliGoodState_cons hst hans
        _ ≤ ((micaliForbiddenDigests (tr_MT, tr_FS)).length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) :=
            toOuterMeasure_uniformList_mem_list_le σ (micaliForbiddenDigests (tr_MT, tr_FS))
        _ = ((3 * tr_MT.length + tr_FS.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) := by
            rw [length_micaliForbiddenDigests]
  | inr xrt =>
    simp only [micaliMTCost, micaliFSCost, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
      zero_add, micaliMemoize, PMF.toOuterMeasure_map_apply]
    calc (memoize (fun q : α × List Bool => ProbComp.eval (kilianChallenges V m q.1))
            xrt tr_FS).toOuterMeasure {x | ¬ MicaliGoodState V L (tr_MT, x.2)}
        ≤ (memoize (fun q : α × List Bool => ProbComp.eval (kilianChallenges V m q.1))
            xrt tr_FS).toOuterMeasure {x | ¬ FSTraceSound V L tr_MT x.2} := by
          refine (memoize (fun q : α × List Bool => ProbComp.eval (kilianChallenges V m q.1))
            xrt tr_FS).toOuterMeasure.mono fun x hbad hfs => ?_
          exact hbad ⟨hst.1, hfs⟩
      _ ≤ (1 / 2) ^ m :=
          toOuterMeasure_memoize_not_fsTraceSound_step V L m tr_MT hsound xrt hst.2

/-- **Accumulated bad-state bound for `micaliMemoize`**: any program with Merkle query budget
`Q_MT` and Fiat–Shamir query budget `Q_FS` starting from `([], [])` violates `MicaliGoodState V L`
with probability at most
`Q_FS * (1 / 2) ^ m + Q_MT * ((3 * Q_MT + Q_FS) * (1 / 2 ^ σ))`. -/
theorem toOuterMeasure_run_micaliMemoize_not_goodState_le [BEq α] {β : Type}
    (V : PCPVerifier α) (L : Set α) (σ m : ℕ)
    (hsound : ∀ x ∉ L, ∀ π : List Bool,
      2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x)
    {prog : OracleComp (MicaliSpec α) β} {Q_MT Q_FS : ℕ}
    (hMT : IsCostBounded micaliMTCost prog Q_MT)
    (hFS : IsCostBounded micaliFSCost prog Q_FS) :
    ((OracleComp.interpret (micaliMemoize V σ m) prog).run ([], [])).toOuterMeasure
      {out | ¬ MicaliGoodState V L out.2} ≤
      (Q_FS : ℝ≥0∞) * (1 / 2) ^ m +
        (Q_MT : ℝ≥0∞) * (((3 * Q_MT + Q_FS : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  have h := toOuterMeasure_bad_le_two
    (handler := micaliMemoize V σ m)
    (bad := fun st => ¬ MicaliGoodState V L st)
    micaliMTCost micaliFSCost
    (fun st => ((3 * st.1.length + st.2.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ))
    (3 * ((1 : ℝ≥0∞) / 2 ^ σ))
    ((1 : ℝ≥0∞) / 2 ^ σ)
    ((1 / 2) ^ m)
    (fun q st hst => toOuterMeasure_micaliMemoize_not_goodState_step V L σ m hsound q
      (not_not.mp hst))
    (fun q st _ x hx _ => by
      rcases st with ⟨tr_MT, tr_FS⟩
      cases q with
      | inl msg =>
        simp only [micaliMemoize, PMF.mem_support_map_iff] at hx
        obtain ⟨⟨ans, tr_MT'⟩, hmem, rfl⟩ := hx
        have hlen := length_le_of_mem_support_memoize _ msg tr_MT hmem
        simp only [micaliMTCost, micaliFSCost, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul,
          add_zero]
        calc ((3 * tr_MT'.length + tr_FS.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)
            ≤ ((3 * (tr_MT.length + 1) + tr_FS.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) := by
              gcongr
        _ = ((3 * tr_MT.length + tr_FS.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) +
              3 * ((1 : ℝ≥0∞) / 2 ^ σ) := by
              push_cast
              ring
      | inr xrt =>
        simp only [micaliMemoize, PMF.mem_support_map_iff] at hx
        obtain ⟨⟨ρs, tr_FS'⟩, hmem, rfl⟩ := hx
        have hlen := length_le_of_mem_support_memoize _ xrt tr_FS hmem
        simp only [micaliMTCost, micaliFSCost, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul,
          add_zero]
        calc ((3 * tr_MT.length + tr_FS'.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)
            ≤ ((3 * tr_MT.length + (tr_FS.length + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) := by
              gcongr
        _ = ((3 * tr_MT.length + tr_FS.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ) +
              (1 : ℝ≥0∞) / 2 ^ σ := by
              push_cast
              ring)
    hMT hFS (s := ([], [])) (not_not.mpr (micaliGoodState_nil V L))
  refine h.trans (le_of_eq ?_)
  simp only [List.length_nil, mul_zero, add_zero]
  push_cast
  ring

/-! #### Support invariants of `memoize`, `kilianVerifyProg` and `micaliVerify` -/

private theorem allOpenings_of_mem_support_mapM_merkleVerifyProg
    (dist : List Bool → PMF (List Bool)) (d : ℕ) (root : List Bool) (V : PCPVerifier α) (x : α)
    (qa : List (ℕ × KilianOpening)) {tr tr' : List (List Bool × List Bool)} {checks : List Bool}
    (hnodup : (tr.map Prod.fst).Nodup)
    (hsupp : ∀ e ∈ tr, e.2 ∈ (dist e.1).support)
    (hmem : (checks, tr') ∈
      ((OracleComp.interpret (memoize dist)
        (qa.mapM fun (a, b, path) =>
          merkleVerifyProg d root (kilianPosition V x a) [b] path)).run tr).support)
    {h : List Bool → List Bool} (hcons : TraceConsistentWith h tr') :
    ∀ o ∈ qa, PathQueriedInTrace (fun _ => h) [] tr' (kilianPosition V x o.1) [o.2.1] o.2.2 := by
  induction qa generalizing tr checks with
  | nil =>
    intro _ ho
    cases ho
  | cons hd tl ih =>
    rcases hd with ⟨a, b, path⟩
    simp only [List.mapM_cons, run_interpret_bind, run_interpret_pure, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hmem
    rcases hmem with ⟨⟨c, tr₁⟩, hc, ⟨cs, tr₂⟩, hcs, rfl, rfl⟩
    obtain ⟨hsub₁, hnodup₁, hsupp₁, -⟩ :=
      mem_support_run_memoize_invariant dist
        (merkleVerifyProg d root (kilianPosition V x a) [b] path) hnodup hsupp hc
    obtain ⟨hsub₂, -, -, -⟩ :=
      mem_support_run_memoize_invariant dist _ hnodup₁ hsupp₁ hcs
    have hcons₁ : TraceConsistentWith h tr₁ := fun p hp => hcons p (hsub₂ p hp)
    have hhd := pathQueriedInTrace_of_mem_support_merkleVerifyProg dist d root
      (kilianPosition V x a) [b] path hnodup hsupp hc hcons₁
    intro o ho
    rcases List.mem_cons.mp ho with rfl | htl
    · intro q hq
      exact hsub₂ _ (hhd q hq)
    · exact ih hnodup₁ hsupp₁ hcs o htl

private theorem allOpenings_of_mem_support_mapM_kilianCheckProg
    (dist : List Bool → PMF (List Bool)) (V : PCPVerifier α) (x : α) (root : List Bool)
    (ra : List (List Bool × List KilianOpening))
    {tr tr' : List (List Bool × List Bool)} {checks : List Bool}
    (hnodup : (tr.map Prod.fst).Nodup)
    (hsupp : ∀ e ∈ tr, e.2 ∈ (dist e.1).support)
    (hmem : (checks, tr') ∈
      ((OracleComp.interpret (memoize dist)
        (ra.mapM fun (ρ, answers) => kilianCheckProg V x root ρ answers)).run tr).support)
    {h : List Bool → List Bool} (hcons : TraceConsistentWith h tr') :
    ∀ p ∈ ra, ∀ o ∈ (V.queries (x, p.1)).zip p.2,
      PathQueriedInTrace (fun _ => h) [] tr' (kilianPosition V x o.1) [o.2.1] o.2.2 := by
  induction ra generalizing tr checks with
  | nil =>
    intro _ hp
    cases hp
  | cons hd tl ih =>
    rcases hd with ⟨ρ, answers⟩
    simp only [List.mapM_cons, kilianCheckProg, run_interpret_bind, run_interpret_pure,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hmem
    rcases hmem with ⟨_, ⟨⟨subchecks, tr₁⟩, hsub, rfl⟩, ⟨cs, tr₂⟩, hcs, rfl, rfl⟩
    obtain ⟨hsub₁, hnodup₁, hsupp₁, -⟩ :=
      mem_support_run_memoize_invariant dist _ hnodup hsupp hsub
    obtain ⟨hsub₂, -, -, -⟩ :=
      mem_support_run_memoize_invariant dist _ hnodup₁ hsupp₁ hcs
    have hcons₁ : TraceConsistentWith h tr₁ := fun p hp => hcons p (hsub₂ p hp)
    have hhd := allOpenings_of_mem_support_mapM_merkleVerifyProg dist (kilianDepth V x) root V x
      ((V.queries (x, ρ)).zip answers) hnodup hsupp hsub hcons₁
    intro p hp o ho
    rcases List.mem_cons.mp hp with rfl | htl
    · intro q hq
      exact hsub₂ _ (hhd o ho q hq)
    · exact ih hnodup₁ hsupp₁ hcs p htl o ho

/-- Running `kilianVerifyProg V x root ρs response` under `memoize dist` records every opening path
in `tr'`, so `AllOpeningsQueriedInTrace (fun _ => h) [] V tr' x ρs response` holds. -/
theorem allOpeningsQueriedInTrace_of_mem_support_kilianVerifyProg
    (dist : List Bool → PMF (List Bool)) (V : PCPVerifier α) (x : α) (root : List Bool)
    (ρs : List (List Bool)) (response : KilianResponse)
    {tr tr' : List (List Bool × List Bool)} {ok : Bool}
    (hnodup : (tr.map Prod.fst).Nodup)
    (hsupp : ∀ e ∈ tr, e.2 ∈ (dist e.1).support)
    (hmem : (ok, tr') ∈
      ((OracleComp.interpret (memoize dist)
        (kilianVerifyProg V x root ρs response)).run tr).support)
    {h : List Bool → List Bool} (hcons : TraceConsistentWith h tr') :
    AllOpeningsQueriedInTrace (fun _ => h) [] V tr' x ρs response := by
  simp only [kilianVerifyProg, run_interpret_bind, run_interpret_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hmem
  rcases hmem with ⟨⟨checks, tr₁⟩, hchecks, rfl, rfl⟩
  have hall := allOpenings_of_mem_support_mapM_kilianCheckProg dist V x root
    (ρs.zip response) hnodup hsupp hchecks hcons
  intro o ho
  simp only [kilianOpenings, List.mem_flatMap] at ho
  obtain ⟨p, hp, ho⟩ := ho
  exact hall p hp o ho

/-- Running a `liftLeft` program under `micaliMemoize` runs it on the Merkle trace and leaves the
Fiat–Shamir trace unchanged. -/
private theorem run_micaliMemoize_liftLeft [BEq α] (V : PCPVerifier α) (σ m : ℕ) {β : Type}
    (prog : OracleComp MerkleHashSpec β) (tr_MT : List (List Bool × List Bool))
    (tr_FS : List ((α × List Bool) × List (List Bool))) :
    (OracleComp.interpret (micaliMemoize V σ m)
      (OracleComp.liftLeft (spec₂ := MicaliFSSpec α) prog)).run (tr_MT, tr_FS) =
      ((OracleComp.interpret (memoize (fun _ : List Bool => BitString.uniformList σ)) prog).run
        tr_MT).map fun (res, tr_MT') => (res, (tr_MT', tr_FS)) := by
  induction prog using OracleComp.induction generalizing tr_MT with
  | pure a =>
    simp [PMF.monad_pure_eq_pure]
  | query_bind q cont ih =>
    simp only [liftLeft_bind, liftLeft_query, run_interpret_bind, run_interpret_query,
      micaliMemoize, PMF.monad_bind_eq_bind, PMF.bind_map, PMF.map_bind, Function.comp_def]
    refine congrArg (PMF.bind _) (funext fun ⟨ans, tr_MT₁⟩ => ih ans tr_MT₁)

/-- Multi-step structural invariant of `micaliMemoize`: starting from traces with `Nodup` keys and
supported values, any run preserves `Nodup` keys and supported values on both channels. -/
private theorem mem_support_run_micaliMemoize_invariant [DecidableEq α]
    (V : PCPVerifier α) (σ m : ℕ) {β : Type} (prog : OracleComp (MicaliSpec α) β)
    {st st' : MicaliTraceState α} {res : β}
    (hnodup_MT : (st.1.map Prod.fst).Nodup)
    (hsupp_MT : ∀ e ∈ st.1, e.2 ∈ (BitString.uniformList σ).support)
    (hnodup_FS : (st.2.map Prod.fst).Nodup)
    (hsupp_FS : ∀ e ∈ st.2, e.2 ∈ (ProbComp.eval (kilianChallenges V m e.1.1)).support)
    (hmem : (res, st') ∈ ((OracleComp.interpret (micaliMemoize V σ m) prog).run st).support) :
    (st'.1.map Prod.fst).Nodup ∧
      (∀ e ∈ st'.1, e.2 ∈ (BitString.uniformList σ).support) ∧
      (st'.2.map Prod.fst).Nodup ∧
      (∀ e ∈ st'.2, e.2 ∈ (ProbComp.eval (kilianChallenges V m e.1.1)).support) := by
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
      simp only [micaliMemoize, PMF.mem_support_map_iff] at hans
      obtain ⟨⟨ans', tr_MT₁⟩, hmt, hpair⟩ := hans
      dsimp only at hpair
      rw [Prod.mk.injEq] at hpair
      rcases hpair with ⟨rfl, rfl⟩
      obtain ⟨-, -, hnodup_MT₁, hsupp_MT₁⟩ :=
        mem_support_memoize_nodup (fun _ : List Bool => BitString.uniformList σ) msg
          hnodup_MT hsupp_MT hmt
      exact @ih ans' (tr_MT₁, tr_FS) hnodup_MT₁ hsupp_MT₁ hnodup_FS hsupp_FS hcont
    | inr xrt =>
      simp only [micaliMemoize, PMF.mem_support_map_iff] at hans
      obtain ⟨⟨ρs', tr_FS₁⟩, hfs, hpair⟩ := hans
      dsimp only at hpair
      rw [Prod.mk.injEq] at hpair
      rcases hpair with ⟨rfl, rfl⟩
      obtain ⟨-, -, hnodup_FS₁, hsupp_FS₁⟩ :=
        mem_support_memoize_nodup
          (fun q : α × List Bool => ProbComp.eval (kilianChallenges V m q.1)) xrt
          hnodup_FS hsupp_FS hfs
      exact @ih ρs' (tr_MT, tr_FS₁) hnodup_MT hsupp_MT hnodup_FS₁ hsupp_FS₁ hcont

/-- Any outcome `(true, st')` in the support of `micaliSoundnessProg V L P` under `micaliMemoize`
must violate `MicaliGoodState V L st'`. -/
theorem not_micaliGoodState_of_mem_support_micaliSoundnessProg [DecidableEq α]
    (V : PCPVerifier α) (L : Set α) (σ m : ℕ)
    (P : OracleComp (MicaliSpec α) (α × MicaliProof)) {st' : MicaliTraceState α}
    (hmem : (true, st') ∈
      ((OracleComp.interpret (micaliMemoize V σ m) (micaliSoundnessProg V L P)).run
        ([], [])).support) :
    ¬ MicaliGoodState V L st' := by
  simp only [micaliSoundnessProg, run_interpret_bind, run_interpret_pure,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff] at hmem
  rcases hmem with ⟨⟨⟨x, proof⟩, st₁⟩, hP, ⟨ok, st₃⟩, hMV, hwin⟩
  dsimp only at hwin
  rw [Prod.mk.injEq] at hwin
  rcases hwin with ⟨hwin, rfl⟩
  symm at hwin
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨hx_not_L, rfl⟩ := hwin
  simp only [micaliVerify, run_interpret_bind, PMF.monad_bind_eq_bind,
    PMF.mem_support_bind_iff] at hMV
  rcases hMV with ⟨⟨ρs, st₂⟩, hFS_call, hKV⟩
  obtain ⟨hnodup_MT₁, hsupp_MT₁, hnodup_FS₁, hsupp_FS₁⟩ :=
    mem_support_run_micaliMemoize_invariant V σ m P (st := ([], [])) List.nodup_nil (by simp)
      List.nodup_nil (by simp) hP
  rcases st₁ with ⟨tr_MT₁, tr_FS₁⟩
  simp only [liftRight_query, run_interpret_query, micaliMemoize, PMF.mem_support_map_iff]
    at hFS_call
  obtain ⟨⟨ρs', tr_FS₂⟩, hfs_mem, hpair⟩ := hFS_call
  dsimp only at hpair
  rw [Prod.mk.injEq] at hpair
  rcases hpair with ⟨rfl, rfl⟩
  obtain ⟨hρs_in_FS₂, -, hnodup_FS₂, hsupp_FS₂⟩ :=
    mem_support_memoize_nodup
      (fun q : α × List Bool => ProbComp.eval (kilianChallenges V m q.1)) (x, proof.root)
      hnodup_FS₁ hsupp_FS₁ hfs_mem
  rw [run_micaliMemoize_liftLeft, PMF.mem_support_map_iff] at hKV
  obtain ⟨⟨ok', tr_MT₃⟩, hkv_mem, hpair'⟩ := hKV
  dsimp only at hpair'
  rw [Prod.mk.injEq] at hpair'
  rcases hpair' with ⟨rfl, rfl⟩
  obtain ⟨-, hnodup_MT₃, -, heval⟩ :=
    mem_support_run_memoize_invariant (fun _ : List Bool => BitString.uniformList σ)
      (kilianVerifyProg V x proof.root ρs' proof.response) hnodup_MT₁ hsupp_MT₁ hkv_mem
  set hTree : List Bool → List Bool := fun q => (tr_MT₃.lookup q).getD []
  have hcons : TraceConsistentWith hTree tr_MT₃ :=
    traceConsistentWith_lookup_of_nodup tr_MT₃ [] hnodup_MT₃
  have hpaths : AllOpeningsQueriedInTrace (fun _ => hTree) [] V tr_MT₃ x ρs' proof.response :=
    allOpeningsQueriedInTrace_of_mem_support_kilianVerifyProg _ V x proof.root ρs' proof.response
      hnodup_MT₁ hsupp_MT₁ hkv_mem hcons
  have hver : kilianVerify (fun _ => hTree) V [] x proof.root ρs' proof.response = true := by
    have heq := heval hTree hcons
    simpa [evalPure_kilianVerifyProg] using heq.symm
  have hρs_len : ∀ ρ ∈ ρs', ρ.length = V.coins x := by
    have hsupp_ρs := hsupp_FS₂ ((x, proof.root), ρs') hρs_in_FS₂
    simp only [kilianChallenges, ProbComp.mem_support_replicate_iff] at hsupp_ρs
    intro ρ hρ
    exact BitString.length_of_mem_support_uniformList (by simpa using hsupp_ρs.2 ρ hρ)
  rintro ⟨hfree, hfs_sound⟩
  exact hfs_sound ((x, proof.root), ρs') hρs_in_FS₂ hx_not_L fun ρ hρ =>
    kilianVerify_sound_of_traceCollisionFree hfree hpaths hver hρ (hρs_len ρ hρ)

/-- **Adaptive ROM soundness for the unsalted two-channel variant** (compare [Micali2000];
[ChiesaYogev2024], Theorem 21.2.1, printed pp. 241–242):
for any PCP verifier `V` whose soundness error on statements outside `L` is at most `1 / 2` per
repetition, and any cheating prover `P` making at most `t_FS` Fiat–Shamir queries such that the
combined execution `micaliSoundnessProg V L P` makes at most `Q_MT` Merkle hash queries, the
probability that `P` outputs `(x, proof)` with `x ∉ L` accepted by `micaliVerify` is at most
`(t_FS + 1) * (1 / 2) ^ m + Q_MT * ((3 * Q_MT + (t_FS + 1)) * (1 / 2 ^ σ))`. -/
theorem micaliSoundness_bound [DecidableEq α] (V : PCPVerifier α) (L : Set α) (σ m : ℕ)
    (hsound : ∀ x ∉ L, ∀ π : List Bool,
      2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x)
    {P : OracleComp (MicaliSpec α) (α × MicaliProof)} {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded micaliFSCost P t_FS)
    (hMT : IsCostBounded micaliMTCost (micaliSoundnessProg V L P) Q_MT) :
    micaliSoundnessGame V L P σ m true ≤
      ((t_FS + 1 : ℕ) : ℝ≥0∞) * (1 / 2) ^ m +
        (Q_MT : ℝ≥0∞) * (((3 * Q_MT + (t_FS + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [micaliSoundnessGame_eq_run_micaliMemoize, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  set run := (OracleComp.interpret (micaliMemoize V σ m) (micaliSoundnessProg V L P)).run ([], [])
  rw [← PMF.toOuterMeasure_apply_inter_support]
  calc run.toOuterMeasure ((Prod.fst ⁻¹' {true}) ∩ run.support)
      ≤ run.toOuterMeasure {out | ¬ MicaliGoodState V L out.2} := by
        refine run.toOuterMeasure.mono fun ⟨res, st'⟩ ⟨hres, hmem⟩ => ?_
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hres
        subst hres
        exact not_micaliGoodState_of_mem_support_micaliSoundnessProg V L σ m P hmem
    _ ≤ ((t_FS + 1 : ℕ) : ℝ≥0∞) * (1 / 2) ^ m +
          (Q_MT : ℝ≥0∞) * (((3 * Q_MT + (t_FS + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
        toOuterMeasure_run_micaliMemoize_not_goodState_le V L σ m hsound hMT
          (isCostBounded_micaliFSCost_micaliSoundnessProg V L hFS)

/-- **Micali's ROM Soundness Theorem (separate prover/verifier Merkle budgets)**: if the cheating
prover `P` makes at most `t_MT` Merkle hash queries and at most `t_FS` Fiat–Shamir queries, and
`micaliVerify V x proof` makes at most `q_V` Merkle hash queries for outputs in `P.support`,
then `micaliSoundnessGame`
accepts a false statement with probability at most
`(t_FS + 1) * (1 / 2) ^ m + (t_MT + q_V) * ((3 * (t_MT + q_V) + (t_FS + 1)) * (1 / 2 ^ σ))`. -/
theorem micaliSoundness_bound_of_prover_verifier [DecidableEq α] (V : PCPVerifier α) (L : Set α)
    (σ m : ℕ)
    (hsound : ∀ x ∉ L, ∀ π : List Bool,
      2 * acceptCount (fun y => V.accepts y.1 π y.2) x (V.coins x) ≤ 2 ^ V.coins x)
    {P : OracleComp (MicaliSpec α) (α × MicaliProof)} {t_MT t_FS q_V : ℕ}
    (hMT : IsCostBounded micaliMTCost P t_MT)
    (hFS : IsCostBounded micaliFSCost P t_FS)
    (hV : ∀ x proof, (x, proof) ∈ P.support →
      IsCostBounded micaliMTCost (micaliVerify V x proof) q_V) :
    micaliSoundnessGame V L P σ m true ≤
      ((t_FS + 1 : ℕ) : ℝ≥0∞) * (1 / 2) ^ m +
        ((t_MT + q_V : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + q_V) + (t_FS + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  micaliSoundness_bound V L σ m hsound hFS
    (isCostBounded_micaliMTCost_micaliSoundnessProg V L hMT hV)

/-! ### Part 4: Succinctness of Micali Proofs and CS-Proofs for `NP` -/

/-- The payload bits of a non-interactive Micali proof: the Merkle root and the opening
responses. -/
def micaliProofBits (proof : MicaliProof) : ℕ :=
  proof.root.length + kilianResponseBits proof.response

/-- **Honest Micali proof size** in the PCP parameters: with `σ`-bit Merkle digests and `m`
Fiat–Shamir challenge strings of `r = V.coins x` bits, the honest proof `micaliProvePure` has at
most `σ + m * (q * (1 + (r + ⌈log₂ q⌉) * σ))` payload bits. -/
theorem micaliProofBits_micaliProvePure_le {hTree : List Bool → List Bool}
    {hFS : α × List Bool → List (List Bool)} {V : PCPVerifier α} {σ m : ℕ}
    (hlen : ∀ y, (hTree y).length = σ) {x : α} {table : List Bool}
    (hm : (hFS (x, kilianCommit (fun _ => hTree) V [] x table)).length = m)
    (hρs : ∀ ρ ∈ hFS (x, kilianCommit (fun _ => hTree) V [] x table), ρ.length = V.coins x)
    {q : ℕ} (hq : ∀ ρ : List Bool, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ q) :
    micaliProofBits (micaliProvePure hTree hFS V x table) ≤
      σ + m * (q * (1 + (V.coins x + Nat.clog 2 q) * σ)) := by
  set H : List Bool → List Bool → List Bool := fun k y =>
    if k.length = σ then hTree y else List.replicate k.length false
  set k₀ : List Bool := List.replicate σ false
  have hk₀ : k₀.length = σ := List.length_replicate
  have hH_eq : H k₀ = hTree := by
    funext y
    simp [H, hk₀]
  have hlenH : ∀ k y, (H k y).length = k.length := by
    intro k y
    by_cases hk : k.length = σ
    · simp [H, hk, hlen y]
    · simp [H, hk]
  have hparents : merkleParents (fun _ => hTree) [] = merkleParents H k₀ := by
    funext level
    simp [merkleParents, hH_eq]
  have hstep_eq : merklePathStep (fun _ => hTree) [] = merklePathStep H k₀ := by
    funext st
    simp [merklePathStep, hparents]
  have hcommit : kilianCommit (fun _ => hTree) V [] x table = kilianCommit H V k₀ x table := by
    simp [kilianCommit, merkleRoot, merkleLevel, merkleLeafLevel, hparents, hH_eq]
  have hrespond (ρs : List (List Bool)) :
      kilianRespond (fun _ => hTree) V [] x table ρs = kilianRespond H V k₀ x table ρs := by
    simp [kilianRespond, kilianOpen, merklePath, merkleLeafLevel, hstep_eq, hH_eq]
  have hroot : (kilianCommit (fun _ => hTree) V [] x table).length ≤ σ := by
    rw [hcommit, kilianCommit, merkleRoot]
    cases h : merkleLevel H k₀ (kilianLeaves (kilianTable V x table))
        (Nat.clog 2 (kilianLeaves (kilianTable V x table)).length) with
    | nil => simp
    | cons y ys =>
      rw [List.headD_cons, length_of_mem_merkleLevel hlenH (h ▸ List.mem_cons_self), hk₀]
  have hresp := kilianResponseBits_kilianRespond_le hlenH (k := k₀) (table := table) hq hρs
  have hdepth : (hFS (x, kilianCommit (fun _ => hTree) V [] x table)).length *
      (q * (1 + kilianDepth V x * k₀.length)) ≤
      m * (q * (1 + (V.coins x + Nat.clog 2 q) * σ)) := by
    rw [hm, hk₀]
    gcongr
    exact kilianDepth_le hq
  unfold micaliProofBits micaliProvePure
  dsimp only
  rw [hrespond]
  omega

/-- **Polylogarithmic Micali proof size**: for a verifier with at most `c * (log₂ |enc x| + 1)`
random bits and at most `q` queries per random string, the honest proof `micaliProvePure` with
`σ`-bit Merkle digests and `m` repetitions has at most
`(1 + q + q * c + q * ⌈log₂ q⌉) * (σ + m + 1) ^ 2 * (log₂ |enc x| + 1)` payload bits. -/
theorem micaliProofBits_micaliProvePure_le_log {enc : α ↪ List Bool} {c : ℕ}
    {hTree : List Bool → List Bool} {hFS : α × List Bool → List (List Bool)}
    {V : PCPVerifier α} {σ m : ℕ} (hlen : ∀ y, (hTree y).length = σ)
    {x : α} {table : List Bool}
    (hm : (hFS (x, kilianCommit (fun _ => hTree) V [] x table)).length = m)
    (hρs : ∀ ρ ∈ hFS (x, kilianCommit (fun _ => hTree) V [] x table), ρ.length = V.coins x)
    {q : ℕ} (hq : ∀ ρ : List Bool, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ q)
    (hcoins : V.coins x ≤ c * (Nat.log 2 (enc x).length + 1)) :
    micaliProofBits (micaliProvePure hTree hFS V x table) ≤
      (1 + q + q * c + q * Nat.clog 2 q) * (σ + m + 1) ^ 2 * (Nat.log 2 (enc x).length + 1) := by
  set ℓ := Nat.log 2 (enc x).length + 1
  set L := Nat.clog 2 q
  have hℓ : 1 ≤ ℓ := Nat.le_add_left 1 _
  refine (micaliProofBits_micaliProvePure_le hlen hm hρs hq).trans ?_
  have hstep : σ + m * (q * (1 + (V.coins x + L) * σ)) ≤
      σ + m * (q * (1 + (c * ℓ + L) * σ)) := by
    gcongr
  refine hstep.trans ?_
  have hms : m * σ ≤ (σ + m + 1) ^ 2 := by nlinarith
  have h₁ : σ ≤ (σ + m + 1) ^ 2 * ℓ := by nlinarith
  have h₂ : m ≤ (σ + m + 1) ^ 2 * ℓ := by nlinarith
  have h₃ : m * σ * ℓ ≤ (σ + m + 1) ^ 2 * ℓ := Nat.mul_le_mul_right ℓ hms
  have h₄ : m * σ ≤ (σ + m + 1) ^ 2 * ℓ := by nlinarith [hms, hℓ]
  have e₁ := Nat.mul_le_mul_left q h₂
  have e₂ := Nat.mul_le_mul_left (q * c) h₃
  have e₃ := Nat.mul_le_mul_left (q * L) h₄
  nlinarith

/-- **Micali's CS Proofs for `NP` in the Random Oracle Model**
([Micali2000]; compare [ChiesaYogev2024], Construction 21.1.1 and Theorem 21.2.1): every language
`L ∈ NP` has a polynomial-time
PCP verifier `V` with `O(log n)` random bits and a constant number of queries whose accepted
compact tables (`V.tableVerifier`) characterize `L`, such that Micali's non-interactive ROM
protocol over `V`:
* accepts the honest prover with probability `1` on every accepted compact table
  (`micaliHonestGame_eq_pure_true`),
* satisfies the unconditional ROM soundness bound `micaliSoundness_bound` against any cheating
  prover `P` with Fiat–Shamir budget `t_FS` and total Merkle budget `Q_MT`, and
* produces honest proofs of `O((σ + m + 1)² · (log₂ |enc x| + 1))` payload bits. -/
theorem exists_micaliCSProof_of_mem_NP [DecidableEq α] {enc : α ↪ List Bool} {L : Set α}
    (hL : L ∈ NP enc) :
    ∃ (V : PCPVerifier α) (c d : ℕ), V.PolyTime enc ∧
      (∀ x, V.coins x ≤ c * (Nat.log 2 (enc x).length + 1)) ∧
      (∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d) ∧
      (∀ x, x ∈ L ↔ ∃ table, V.tableVerifier (x, table) = true) ∧
      (∀ x table, V.tableVerifier (x, table) = true →
        ∀ σ m, micaliHonestGame V x table σ m = PMF.pure true) ∧
      (∀ (P : OracleComp (MicaliSpec α) (α × MicaliProof)) (t_FS Q_MT σ m : ℕ),
        IsCostBounded micaliFSCost P t_FS →
        IsCostBounded micaliMTCost (micaliSoundnessProg V L P) Q_MT →
        micaliSoundnessGame V L P σ m true ≤
          ((t_FS + 1 : ℕ) : ℝ≥0∞) * (1 / 2) ^ m +
            (Q_MT : ℝ≥0∞) * (((3 * Q_MT + (t_FS + 1) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ))) ∧
      ∃ C : ℕ, ∀ (σ m : ℕ) (hTree : List Bool → List Bool)
        (hFS : α × List Bool → List (List Bool)) (x : α) (table : List Bool),
        (∀ y, (hTree y).length = σ) →
        (hFS (x, kilianCommit (fun _ => hTree) V [] x table)).length = m →
        (∀ ρ ∈ hFS (x, kilianCommit (fun _ => hTree) V [] x table), ρ.length = V.coins x) →
          micaliProofBits (micaliProvePure hTree hFS V x table) ≤
            C * (σ + m + 1) ^ 2 * (Nat.log 2 (enc x).length + 1) := by
  obtain ⟨V, c, d, hV, hpcp⟩ := NP_subset_PCP_log enc hL
  have hq : ∀ x ρ, ρ.length = V.coins x → (V.queries (x, ρ)).length ≤ d := by
    intro x ρ hρ
    simpa using hpcp.2.1 x ρ hρ
  refine ⟨V, c, d, hV, hpcp.1, hq,
    fun x => ⟨fun hx => ?_, fun ⟨table, htable⟩ => ?_⟩,
    fun x table htable σ m => micaliHonestGame_eq_pure_true V htable σ m,
    fun P t_FS Q_MT σ m hFS hMT => micaliSoundness_bound V L σ m hpcp.2.2.2 hFS hMT,
    _, fun σ m hTree hFS x table hlen hm hρs =>
      micaliProofBits_micaliProvePure_le_log hlen hm hρs (fun ρ hρ => hq x ρ hρ)
        (hpcp.1 x)⟩
  · obtain ⟨proof, hproof⟩ := hpcp.2.2.1 x hx
    exact ⟨_, by simpa using PCPVerifier.tableVerifier_complete x proof [] hproof⟩
  · by_contra hx
    obtain ⟨proof, hproof⟩ := PCPVerifier.tableVerifier_sound x table htable
    have hs := hpcp.2.2.2 x hx proof
    have hc : acceptCount (fun y => V.accepts y.1 proof y.2) x (V.coins x) = 2 ^ V.coins x := by
      simp [acceptCount, hproof]
    rw [hc] at hs
    have hp : 0 < 2 ^ V.coins x := Nat.two_pow_pos _
    lia

end Cslib.Crypto
