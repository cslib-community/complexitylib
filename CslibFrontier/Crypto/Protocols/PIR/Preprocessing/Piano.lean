/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Basic
public import Mathlib.Algebra.Ring.BooleanRing
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.Fin.Tuple.Basic

/-!
# The Piano client-preprocessing single-server PIR scheme

This module formalizes the core of the Piano client-preprocessing single-server PIR scheme of
[Zhou, Park, Zheng and Shi][ZhouParkZhengShi2024] (Sections 2–3, Figure 1, and Appendix C).

A database `db : Chunk × Offset → Bool` of size `n` is partitioned into `|Chunk| = √n` chunks of
`|Offset| = √n` elements each. A *chunked set* `S : Chunk → Offset` selects one offset in each
chunk.

* **Offline streaming phase** (`HintTable`, `streamChunk`, `streamPreprocess`): the client samples
  a primary table of `M₁` random chunked sets `primarySets : Fin M₁ → Chunk → Offset` together with
  `M₂` replacement offsets `replOffsets : Chunk → Fin M₂ → Offset` and `M₂` backup sets
  `backupSets : Chunk → Fin M₂ → Chunk → Offset` per chunk. Streaming the database one chunk
  `j : Chunk` at a time via `streamChunk j (fun δ => db (j, δ))`, the client accumulates the full
  parity `setParity db (primarySets i)` of each primary set, the database bit
  `db (j, replOffsets j k)` at each replacement offset, and the punctured parity
  `backupParity db j (backupSets j k)` (excluding chunk `j`) of each backup set.
* **Online query and reconstruction** (`findHint`, `replaceInChunk`, `reconstructBit`,
  `HintTable.onlineStep`): to query `x = (j*, δ*) : Chunk × Offset`, the client finds the first
  primary hint `i : Fin M₁` such that `primarySets i j* = δ*`, replaces its `j*`-th coordinate with
  a random offset `r : Offset` in chunk `j*` (`S' = replaceInChunk (primarySets i) j* r`), and sends
  `S'` (or its compacted punctured form `compactedOffsets S' j*` of `√n - 1` offsets) to the server.
  The server returns `q = setParity db S'`, and the client reconstructs
  `β = q + primaryParities i + db (j*, r) = db x`.
* **Online hint refresh** (`refreshParity`, `pianoStepSets`, `HintTable.onlineStep`): to restore the
  primary hint table after consuming entry `i`, the client promotes a backup entry `(B, p_bak)` for
  chunk `j*` by setting the new primary set at `i` to `replaceInChunk B j* δ*` (forcing it to
  contain `x`) and the new parity to `p_bak + β = setParity db (replaceInChunk B j* δ*)`.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.replaceInChunk`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.setParity`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.backupParity`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.reconstructBit`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.refreshParity`: chunked sets and parity
  operations.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.findHint`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.pianoStepSets`: primary hint matching and the
  joint set-refresh / server-query transformation.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.compactedOffsets`: punctured query representation
  dropping the queried chunk `j*` (`√n - 1` offsets).
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.HintTable`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.streamChunk`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.streamPreprocess`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.HintTable.onlineStep`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.HintTable.runOnlineSteps`: Figure 1 state,
  single-pass chunk streaming, and online execution.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.pianoHybridScheme`: the ideal-random-set hybrid
  of Piano (server view only; not a correct PIR scheme) packaged as a `Preprocessing.Scheme`.

## Main results

* `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.reconstructBit_setParity_eq`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.refreshParity_eq_setParity`: algebraic
  correctness of online reconstruction and hint refresh.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.pianoStepSets_involutive`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.eval_pianoStepSets_uniform`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.eval_pianoRefreshedTable_uniform`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.eval_pianoServerQuery_uniform`:
  `pianoStepSets`
  is an involution, so in the ideal-random-set model the server query is uniformly distributed on
  `Chunk → Offset` independent of `x` and the refreshed primary table remains uniformly distributed
  on `Fin M₁ → Chunk → Offset` (Theorem 3.2 core / Lemma C.2).
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.eval_compactedQuery_uniform`: the compacted
  punctured query of `√n - 1` offsets is uniformly distributed on `Fin m → Offset` independent of
  `x`.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.foldr_streamChunk_univ`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.HintTable.onlineStep_correct`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.HintTable.runOnlineSteps_correct`: offline
  single-pass chunk streaming and deterministic multi-query correctness whenever a matching hint
  exists and the chunk's backup group is not exhausted (Theorem 3.3 deterministic core).
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.HintTable.onlineStep_sets_eq_pianoStepSets`: the
  full client's server query and refreshed primary table are given by `pianoStepSets`.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.isPerfectlyPrivateWith_pianoHybridScheme`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.eval_queryTranscript_pianoHybridScheme`:
  multi-query adaptive perfect privacy (Definition 3.1) and non-adaptive transcript privacy of the
  ideal-random-set hybrid (the `Real*` step of the proof of Theorem C.1). The hybrid models only
  the server's view and is not a correct PIR scheme.
* `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.onlineCommunication_fullQuery`,
  `Cslib.Crypto.Protocols.PIR.Preprocessing.Piano.onlineCommunication_compacted`: per-query online
  communication of the main scheme and of the Appendix A variant (Theorem 3.4 online part).

## What is not proved

* Pseudorandom sets are replaced by truly random sets: the PRF step of the proof of Theorem C.1 is
  not formalized, and the privacy results are perfect privacy in that idealized model.
* Privacy is proved for `pianoHybridScheme`, which samples the replacement offset and backup set
  online. Privacy of the full `HintTable` client, which stores `M₂` entries per chunk in advance and
  can exhaust them, is not proved; `HintTable.onlineStep_sets_eq_pianoStepSets` only identifies the
  set map the two share.
* Correctness is the deterministic part of Theorem 3.3: the exact precondition `CanAnswerSeq`
  (a matching hint exists and the backup group is not exhausted at every step). The
  failure-probability bound for `M₁` and `M₂` is not formalized. Replacement and backup entries of a
  chunk share one consumption counter `used`.
* The restriction to distinct random queries, the pipelining that removes the query bound, the
  Appendix A server algorithm (Figure 3), and the storage and server-time bounds of Theorem 3.4 are
  not formalized.

## References

* [M. Zhou, A. Park, W. Zheng, E. Shi, *Piano: Extremely Simple, Single-Server PIR with Sublinear
  Server Computation*][ZhouParkZhengShi2024], Sections 2–3, Figure 1, Appendix A, and Appendix C
  (source locators follow the full ePrint version, where the author order is Zhou, Park, Shi, Zheng)
-/

public section

namespace Cslib.Crypto.Protocols.PIR.Preprocessing.Piano

open Probability
open scoped ENNReal NNReal

variable {M₁ M₂ : ℕ} {Chunk Offset : Type}

/-! ### Chunked sets and parity identities -/

/-- Replaces the offset selected by `S : Chunk → Offset` in chunk `j` with `δ`, denoted
`S⟨j → δ⟩` in [Zhou, Park, Zheng and Shi, Figure 1][ZhouParkZhengShi2024]. -/
@[expose] def replaceInChunk [DecidableEq Chunk] (S : Chunk → Offset) (j : Chunk) (δ : Offset) :
    Chunk → Offset :=
  Function.update S j δ

@[simp]
theorem replaceInChunk_self [DecidableEq Chunk] (S : Chunk → Offset) (j : Chunk) (δ : Offset) :
    replaceInChunk S j δ j = δ := by
  simp [replaceInChunk]

theorem replaceInChunk_of_ne [DecidableEq Chunk] (S : Chunk → Offset) {j j' : Chunk} (δ : Offset)
    (h : j' ≠ j) : replaceInChunk S j δ j' = S j' := by
  simp [replaceInChunk, h]

@[simp]
theorem replaceInChunk_idem [DecidableEq Chunk] (S : Chunk → Offset) (j : Chunk)
    (δ₁ δ₂ : Offset) :
    replaceInChunk (replaceInChunk S j δ₁) j δ₂ = replaceInChunk S j δ₂ := by
  simp [replaceInChunk]

@[simp]
theorem replaceInChunk_eq_self [DecidableEq Chunk] (S : Chunk → Offset) (j : Chunk) :
    replaceInChunk S j (S j) = S := by
  simp [replaceInChunk]

/-- The full parity `⊕_{j ∈ Chunk} db (j, S j)` of a chunked set `S : Chunk → Offset` against
database `db : Chunk × Offset → Bool`, using the `BooleanRing Bool` addition (XOR). -/
@[expose] def setParity [Fintype Chunk] (db : Chunk × Offset → Bool) (S : Chunk → Offset) : Bool :=
  ∑ j : Chunk, db (j, S j)

/-- The punctured backup parity `⊕_{j ∈ Chunk \ {jStar}} db (j, B j)` of a backup set
`B : Chunk → Offset` belonging to chunk `jStar`
[Zhou, Park, Zheng and Shi, Figure 1][ZhouParkZhengShi2024]. -/
@[expose] def backupParity [Fintype Chunk] [DecidableEq Chunk] (db : Chunk × Offset → Bool)
    (jStar : Chunk)
    (B : Chunk → Offset) : Bool :=
  ∑ j ∈ Finset.univ.erase jStar, db (j, B j)

/-- Decomposes the full parity `setParity db S` into the bit in chunk `jStar` plus the punctured
backup parity outside `jStar`. -/
theorem setParity_eq_add_backupParity [Fintype Chunk] [DecidableEq Chunk]
    (db : Chunk × Offset → Bool) (jStar : Chunk) (S : Chunk → Offset) :
    setParity db S = db (jStar, S jStar) + backupParity db jStar S := by
  rw [setParity, backupParity, ← Finset.add_sum_erase _ _ (Finset.mem_univ jStar)]

/-- Replacing the offset in chunk `jStar` leaves the punctured backup parity for `jStar` unchanged.
-/
@[simp]
theorem backupParity_replaceInChunk_self [Fintype Chunk] [DecidableEq Chunk]
    (db : Chunk × Offset → Bool) (jStar : Chunk) (S : Chunk → Offset) (δ : Offset) :
    backupParity db jStar (replaceInChunk S jStar δ) = backupParity db jStar S := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [replaceInChunk_of_ne _ _ (Finset.ne_of_mem_erase hj)]

/-- The full parity of `replaceInChunk S jStar δ` equals `db (jStar, δ)` plus the punctured backup
parity of `S` outside `jStar`. -/
theorem setParity_replaceInChunk [Fintype Chunk] [DecidableEq Chunk]
    (db : Chunk × Offset → Bool) (jStar : Chunk) (S : Chunk → Offset) (δ : Offset) :
    setParity db (replaceInChunk S jStar δ) = db (jStar, δ) + backupParity db jStar S := by
  rw [setParity_eq_add_backupParity db jStar (replaceInChunk S jStar δ),
    replaceInChunk_self, backupParity_replaceInChunk_self]

/-- Client online answer reconstruction `β = q ⊕ p ⊕ v`
([Zhou, Park, Zheng and Shi, Figure 1, Step 1(e)][ZhouParkZhengShi2024]). -/
@[expose] def reconstructBit (q p v : Bool) : Bool :=
  q + p + v

/-- Client online parity refresh `p_new = p_bak ⊕ β`
([Zhou, Park, Zheng and Shi, Figure 1, Step 2][ZhouParkZhengShi2024]). -/
@[expose] def refreshParity (pBak β : Bool) : Bool :=
  pBak + β

private theorem bool_xor_cancel (a b c : Bool) : a + b + (c + b) + a = c := by
  revert a b c
  decide

/-- **Online reconstruction identity**: if primary set `S` contains `x` (`S x.1 = x.2`), then
combining the server answer `setParity db (replaceInChunk S x.1 r)`, the stored primary parity
`setParity db S`, and the replacement bit `db (x.1, r)` recovers `db x`. -/
theorem reconstructBit_setParity_eq [Fintype Chunk] [DecidableEq Chunk]
    (db : Chunk × Offset → Bool) (S : Chunk → Offset) (x : Chunk × Offset) (r : Offset)
    (hS : S x.1 = x.2) :
    reconstructBit (setParity db (replaceInChunk S x.1 r)) (setParity db S) (db (x.1, r)) =
      db x := by
  rw [reconstructBit, setParity_replaceInChunk, setParity_eq_add_backupParity db x.1 S, hS,
    Prod.mk.eta]
  exact bool_xor_cancel _ _ _

/-- **Online refresh parity identity**: XORing the punctured backup parity `backupParity db x.1 B`
with `db x` yields the exact full parity `setParity db (replaceInChunk B x.1 x.2)` of the promoted
primary set `replaceInChunk B x.1 x.2`. -/
theorem refreshParity_eq_setParity [Fintype Chunk] [DecidableEq Chunk]
    (db : Chunk × Offset → Bool) (B : Chunk → Offset) (x : Chunk × Offset) :
    refreshParity (backupParity db x.1 B) (db x) = setParity db (replaceInChunk B x.1 x.2) := by
  rw [refreshParity, setParity_replaceInChunk, Prod.mk.eta, add_comm]

/-! ### Primary hint lookup and the set-refresh involution -/

/-- Finds the first primary table index `i : Fin M₁` whose set `T i` contains `x` (`T i x.1 = x.2`),
or returns `none` if no primary hint contains `x`. -/
@[expose] def findHint [DecidableEq Offset] (T : Fin M₁ → Chunk → Offset) (x : Chunk × Offset) :
    Option (Fin M₁) :=
  (List.finRange M₁).find? (fun i => decide (T i x.1 = x.2))

theorem findHint_eq_some [DecidableEq Offset] {T : Fin M₁ → Chunk → Offset}
    {x : Chunk × Offset} {i : Fin M₁} (h : findHint T x = some i) : T i x.1 = x.2 := by
  simpa [findHint] using List.find?_some h

theorem findHint_eq_none_iff [DecidableEq Offset] (T : Fin M₁ → Chunk → Offset)
    (x : Chunk × Offset) :
    findHint T x = none ↔ ∀ i : Fin M₁, T i x.1 ≠ x.2 := by
  simp [findHint, List.find?_eq_none]

theorem findHint_isSome_iff [DecidableEq Offset] (T : Fin M₁ → Chunk → Offset)
    (x : Chunk × Offset) :
    (findHint T x).isSome ↔ ∃ i : Fin M₁, T i x.1 = x.2 := by
  simp [findHint, List.find?_isSome]

/-- Updating the matched primary slot `i` to another set `S'` that still contains `x` preserves
`findHint T x = some i`. -/
theorem findHint_update_self [DecidableEq Offset] (T : Fin M₁ → Chunk → Offset)
    (x : Chunk × Offset) (i : Fin M₁) (S' : Chunk → Offset) (hfind : findHint T x = some i)
    (hS' : S' x.1 = x.2) :
    findHint (Function.update T i S') x = some i := by
  have hTi : T i x.1 = x.2 := findHint_eq_some hfind
  have hpred : (fun k : Fin M₁ => decide (Function.update T i S' k x.1 = x.2)) =
      (fun k : Fin M₁ => decide (T k x.1 = x.2)) := by
    funext k
    by_cases hk : k = i <;> simp [hk, hTi, hS']
  simpa [findHint, hpred] using hfind

/-- The joint transformation of the primary set table `T : Fin M₁ → Chunk → Offset` and the active
backup/replacement set `B : Chunk → Offset` during an online query for `x : Chunk × Offset`
([Zhou, Park, Zheng and Shi, Figure 1 & Lemma C.2][ZhouParkZhengShi2024]):

* If `findHint T x = some i`, primary slot `i` is refreshed to `replaceInChunk B x.1 x.2` and the
  server receives `replaceInChunk (T i) x.1 (B x.1)`.
* If `findHint T x = none`, the primary table is unchanged (`T`) and the server receives the random
  fallback set `B`. -/
@[expose] def pianoStepSets [DecidableEq Chunk] [DecidableEq Offset] (x : Chunk × Offset)
    (tb : (Fin M₁ → Chunk → Offset) × (Chunk → Offset)) :
    (Fin M₁ → Chunk → Offset) × (Chunk → Offset) :=
  match findHint tb.1 x with
  | some i =>
    (Function.update tb.1 i (replaceInChunk tb.2 x.1 x.2),
     replaceInChunk (tb.1 i) x.1 (tb.2 x.1))
  | none => (tb.1, tb.2)

/-- **Key involution property of Piano** (heart of Theorem 3.2 and Lemma C.2 of
[Zhou, Park, Zheng and Shi][ZhouParkZhengShi2024]): `pianoStepSets x` is an involution on
`(Fin M₁ → Chunk → Offset) × (Chunk → Offset)`. -/
theorem pianoStepSets_involutive [DecidableEq Chunk] [DecidableEq Offset] (x : Chunk × Offset) :
    Function.Involutive (pianoStepSets (M₁ := M₁) (Chunk := Chunk) (Offset := Offset) x) := by
  rintro ⟨T, B⟩
  dsimp only [pianoStepSets]
  cases h : findHint T x with
  | none =>
    simp [h]
  | some i =>
    have hTi : T i x.1 = x.2 := findHint_eq_some h
    have hfind' : findHint (Function.update T i (replaceInChunk B x.1 x.2)) x = some i :=
      findHint_update_self T x i (replaceInChunk B x.1 x.2) h (replaceInChunk_self B x.1 x.2)
    simp only [hfind']
    ext1
    · rw [replaceInChunk_idem, ← hTi, replaceInChunk_eq_self, Function.update_idem,
        Function.update_eq_self]
    · simp only [Function.update_self, replaceInChunk_self, replaceInChunk_idem,
        replaceInChunk_eq_self]

/-- `pianoStepSets x` packaged as a permutation (`Equiv.Perm`) of
`(Fin M₁ → Chunk → Offset) × (Chunk → Offset)`. -/
@[expose] def pianoStepSetsEquiv [DecidableEq Chunk] [DecidableEq Offset] (x : Chunk × Offset) :
    Equiv.Perm ((Fin M₁ → Chunk → Offset) × (Chunk → Offset)) :=
  (pianoStepSets_involutive x).toPerm

@[simp]
theorem pianoStepSetsEquiv_apply [DecidableEq Chunk] [DecidableEq Offset] (x : Chunk × Offset)
    (tb : (Fin M₁ → Chunk → Offset) × (Chunk → Offset)) :
    pianoStepSetsEquiv x tb = pianoStepSets x tb :=
  rfl

/-- Reparametrizing two independent uniform draws `(a, b)` by an equivalence `e : α × β ≃ γ × δ`
yields two independent uniform draws `(c, d)`. -/
private theorem uniformOfFintype_bind_bind_equiv {α β γ δ ε : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] [Fintype γ] [Nonempty γ] [Fintype δ] [Nonempty δ]
    (e : α × β ≃ γ × δ) (f : γ × δ → PMF ε) :
    ((PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).bind fun b =>
      f (e (a, b))) =
      (PMF.uniformOfFintype γ).bind fun c => (PMF.uniformOfFintype δ).bind fun d => f (c, d) := by
  calc _ = (PMF.uniformOfFintype (α × β)).bind (fun ab => f (e ab)) := by
        rw [← PMF.uniformOfFintype_prod, PMF.bind_bind]
        simp only [PMF.bind_map, Function.comp_def]
    _ = ((PMF.uniformOfFintype (α × β)).map e).bind f := by
        rw [PMF.bind_map]
        rfl
    _ = (PMF.uniformOfFintype (γ × δ)).bind f := by
        rw [PMF.uniformOfFintype_map_equiv]
    _ = _ := by
        rw [← PMF.uniformOfFintype_prod, PMF.bind_bind]
        simp only [PMF.bind_map, Function.comp_def]

section IdealUniform

variable [Fintype Chunk] [DecidableEq Chunk] [Fintype Offset] [DecidableEq Offset] [Nonempty Offset]

/-- **Joint resampling invariance of Piano** (Lemma C.2 of
[Zhou, Park, Zheng and Shi][ZhouParkZhengShi2024]): when the primary table `T` and backup set `B`
are drawn independently and uniformly, the pair `pianoStepSets x (T, B)` of the refreshed primary
table and the server query has the same distribution as two independent uniform draws `(T', Q)`. -/
theorem uniformOfFintype_bind_bind_pianoStepSets {ε : Type*} (x : Chunk × Offset)
    (f : (Fin M₁ → Chunk → Offset) × (Chunk → Offset) → PMF ε) :
    ((PMF.uniformOfFintype (Fin M₁ → Chunk → Offset)).bind fun T =>
      (PMF.uniformOfFintype (Chunk → Offset)).bind fun B =>
        f (pianoStepSets x (T, B))) =
      (PMF.uniformOfFintype (Fin M₁ → Chunk → Offset)).bind fun T' =>
        (PMF.uniformOfFintype (Chunk → Offset)).bind fun Q => f (T', Q) :=
  uniformOfFintype_bind_bind_equiv (pianoStepSetsEquiv x) f

/-- The joint distribution of `(refreshedPrimarySets, serverQuery)` in one Piano step is the
uniform product distribution on `(Fin M₁ → Chunk → Offset) × (Chunk → Offset)`,
independent of `x`. -/
theorem eval_pianoStepSets_uniform (x : Chunk × Offset) :
    ProbComp.eval (do
      let T ← ProbComp.uniform (Fin M₁ → Chunk → Offset)
      let B ← ProbComp.uniform (Chunk → Offset)
      pure (pianoStepSets x (T, B))) =
      PMF.uniformOfFintype ((Fin M₁ → Chunk → Offset) × (Chunk → Offset)) := by
  simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [uniformOfFintype_bind_bind_pianoStepSets x PMF.pure, ← PMF.uniformOfFintype_prod]
  rfl

/-- **Primary table distribution invariant** (Theorem 3.2 of
[Zhou, Park, Zheng and Shi][ZhouParkZhengShi2024]): after refreshing the consumed hint with a
uniform backup set, the primary table distribution remains uniform on `Fin M₁ → Chunk → Offset`. -/
theorem eval_pianoRefreshedTable_uniform (x : Chunk × Offset) :
    ProbComp.eval (do
      let T ← ProbComp.uniform (Fin M₁ → Chunk → Offset)
      let B ← ProbComp.uniform (Chunk → Offset)
      pure (pianoStepSets x (T, B)).1) =
      PMF.uniformOfFintype (Fin M₁ → Chunk → Offset) := by
  simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [uniformOfFintype_bind_bind_pianoStepSets x (fun p => PMF.pure p.1)]
  simp [PMF.bind_const]

/-- **Single-query server view privacy** (Theorem 3.2 of
[Zhou, Park, Zheng and Shi][ZhouParkZhengShi2024]): for any queried index `x`, the set sent to the
server is uniformly distributed on `Chunk → Offset`, independent of `x`. -/
theorem eval_pianoServerQuery_uniform (x : Chunk × Offset) :
    ProbComp.eval (do
      let T ← ProbComp.uniform (Fin M₁ → Chunk → Offset)
      let B ← ProbComp.uniform (Chunk → Offset)
      pure (pianoStepSets x (T, B)).2) =
      PMF.uniformOfFintype (Chunk → Offset) := by
  simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  rw [uniformOfFintype_bind_bind_pianoStepSets x (fun p => PMF.pure p.2)]
  simp [PMF.bind_const]

omit [DecidableEq Offset] in
/-- Overwriting chunk `j` of a uniform set `B : Chunk → Offset` with an independent uniform offset
`r : Offset` produces a uniform set on `Chunk → Offset` (connecting Figure 1's separate replacement
offset `r` to `pianoStepSets`). -/
theorem eval_replaceInChunk_uniform (j : Chunk) :
    ProbComp.eval (do
      let B ← ProbComp.uniform (Chunk → Offset)
      let r ← ProbComp.uniform Offset
      pure (replaceInChunk B j r)) =
      PMF.uniformOfFintype (Chunk → Offset) := by
  simp only [ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, replaceInChunk]
  exact Cslib.Probability.PMF.uniformOfFintype_bind_bind_adaptiveUpdate
    (fun _ => j) (fun _ _ => rfl) PMF.pure |>.trans (PMF.bind_pure _)

end IdealUniform

/-! ### Compacted punctured queries (`√n - 1` offsets) -/

/-- For a database partitioned into `m + 1` chunks (`Chunk = Fin (m + 1)`), `compactedOffsets` drops
the queried chunk `jStar` from `S : Fin (m + 1) → Offset` via `Fin.succAbove`, leaving the
`m = √n - 1` offsets in chunks `j ≠ jStar`
([Zhou, Park, Zheng and Shi, Appendix A][ZhouParkZhengShi2024]). -/
@[expose] def compactedOffsets {m : ℕ} (S : Fin (m + 1) → Offset) (jStar : Fin (m + 1)) :
    Fin m → Offset :=
  fun k => S (jStar.succAbove k)

/-- Removing chunk `jStar` erases any replacement offset inserted at `jStar`. -/
@[simp]
theorem compactedOffsets_replaceInChunk_self {m : ℕ} (S : Fin (m + 1) → Offset)
    (jStar : Fin (m + 1)) (δ : Offset) :
    compactedOffsets (replaceInChunk S jStar δ) jStar = compactedOffsets S jStar := by
  ext k
  exact replaceInChunk_of_ne S δ (Fin.succAbove_ne jStar k)

/-- Whenever `findHint T x = some i`, the compacted punctured server query is the matched hint set
`T i` with the queried chunk's element removed. -/
theorem compactedOffsets_pianoServerQuery_eq {m : ℕ} [DecidableEq Offset]
    (T : Fin M₁ → Fin (m + 1) → Offset) (B : Fin (m + 1) → Offset) (x : Fin (m + 1) × Offset)
    {i : Fin M₁} (h : findHint T x = some i) :
    compactedOffsets (pianoStepSets x (T, B)).2 x.1 = compactedOffsets (T i) x.1 := by
  simp [pianoStepSets, h]

/-- Puncturing a uniform set `S : Fin (m + 1) → Offset` at chunk `jStar` yields a uniform vector
of `m` offsets `Fin m → Offset`. -/
theorem uniformOfFintype_map_compactedOffsets {m : ℕ} [Fintype Offset] [Nonempty Offset]
    (jStar : Fin (m + 1)) :
    (PMF.uniformOfFintype (Fin (m + 1) → Offset)).map (fun S => compactedOffsets S jStar) =
      PMF.uniformOfFintype (Fin m → Offset) := by
  let e : (Fin (m + 1) → Offset) ≃ (Fin m → Offset) × Offset :=
    (Fin.insertNthEquiv (fun _ : Fin (m + 1) => Offset) jStar).symm.trans (Equiv.prodComm _ _)
  calc (PMF.uniformOfFintype (Fin (m + 1) → Offset)).map (fun S => compactedOffsets S jStar)
      = ((PMF.uniformOfFintype (Fin (m + 1) → Offset)).map e).map Prod.fst := by
          rw [PMF.map_comp]
          rfl
    _ = (PMF.uniformOfFintype ((Fin m → Offset) × Offset)).map Prod.fst := by
          rw [PMF.uniformOfFintype_map_equiv e]
    _ = PMF.uniformOfFintype (Fin m → Offset) :=
          Cslib.Probability.PMF.uniformOfFintype_prod_map_fst

/-- **Compacted punctured query privacy** (the observation in
[Zhou, Park, Zheng and Shi, Appendix A][ZhouParkZhengShi2024] that the compacted offset vector
hides `x`): for any queried index `x`, removing the queried chunk from the hybrid's server query
leaves `m = √n - 1` offsets that are uniformly distributed on `Fin m → Offset`, independent of `x`.
This is a single-query statement about the offset vector only; the Appendix A variant's client and
server algorithms are not formalized. -/
theorem eval_compactedQuery_uniform {m : ℕ} [Fintype Offset] [DecidableEq Offset] [Nonempty Offset]
    (x : Fin (m + 1) × Offset) :
    ProbComp.eval (do
      let T ← ProbComp.uniform (Fin M₁ → Fin (m + 1) → Offset)
      let B ← ProbComp.uniform (Fin (m + 1) → Offset)
      pure (compactedOffsets (pianoStepSets x (T, B)).2 x.1)) =
      PMF.uniformOfFintype (Fin m → Offset) := by
  have hmap : ProbComp.eval (do
      let T ← ProbComp.uniform (Fin M₁ → Fin (m + 1) → Offset)
      let B ← ProbComp.uniform (Fin (m + 1) → Offset)
      pure (compactedOffsets (pianoStepSets x (T, B)).2 x.1)) =
      (ProbComp.eval (do
        let T ← ProbComp.uniform (Fin M₁ → Fin (m + 1) → Offset)
        let B ← ProbComp.uniform (Fin (m + 1) → Offset)
        pure (pianoStepSets x (T, B)).2)).map (fun S => compactedOffsets S x.1) := by
    simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
  rw [hmap, eval_pianoServerQuery_uniform, uniformOfFintype_map_compactedOffsets]

/-! ### Figure 1 `HintTable`, single-pass chunk streaming, and deterministic correctness -/

/-- The client's local hint table in [Zhou, Park, Zheng and Shi, Figure 1][ZhouParkZhengShi2024],
consisting of:

* `M₁` primary hints `(primarySets i, primaryParities i)`,
* `M₂` replacement entries `(replOffsets j k, replValues j k)` per chunk `j`,
* `M₂` backup entries `(backupSets j k, backupParities j k)` per chunk `j`, and
* the number `used j` of backup/replacement entries consumed so far in each chunk `j`. -/
@[ext]
structure HintTable (M₁ M₂ : ℕ) (Chunk Offset : Type) where
  /-- The `M₁` chunked sets in the primary hint table. -/
  primarySets : Fin M₁ → Chunk → Offset
  /-- The parity bit stored for each primary hint set. -/
  primaryParities : Fin M₁ → Bool
  /-- The `M₂` replacement offsets pre-sampled in each chunk. -/
  replOffsets : Chunk → Fin M₂ → Offset
  /-- The database bit stored for each replacement offset. -/
  replValues : Chunk → Fin M₂ → Bool
  /-- The `M₂` backup sets pre-sampled for each chunk. -/
  backupSets : Chunk → Fin M₂ → Chunk → Offset
  /-- The punctured parity bit stored for each backup set. -/
  backupParities : Chunk → Fin M₂ → Bool
  /-- Per-chunk count of consumed replacement/backup entries. -/
  used : Chunk → ℕ

/-- Initializes a `HintTable` prior to streaming the database, with all parities and replacement
values set to `false` (`0`) and all consumption counters set to `0`
([Zhou, Park, Zheng and Shi, Figure 1, offline preprocessing][ZhouParkZhengShi2024]). -/
@[expose] def initHintTable (primarySets : Fin M₁ → Chunk → Offset)
    (replOffsets : Chunk → Fin M₂ → Offset)
    (backupSets : Chunk → Fin M₂ → Chunk → Offset) : HintTable M₁ M₂ Chunk Offset where
  primarySets := primarySets
  primaryParities := fun _ => false
  replOffsets := replOffsets
  replValues := fun _ _ => false
  backupSets := backupSets
  backupParities := fun _ _ => false
  used := fun _ => 0

/-- Processes a single streamed chunk `j : Chunk` using only the chunk slice
`chunkDB : Offset → Bool` (`fun δ => db (j, δ)`), updating primary parities, chunk `j`'s
replacement values, and the backup parities for all other chunks `j' ≠ j`
([Zhou, Park, Zheng and Shi, Figure 1, offline preprocessing][ZhouParkZhengShi2024]). -/
@[expose] def streamChunk [DecidableEq Chunk] (j : Chunk) (chunkDB : Offset → Bool)
    (t : HintTable M₁ M₂ Chunk Offset) : HintTable M₁ M₂ Chunk Offset where
  primarySets := t.primarySets
  primaryParities := fun i => chunkDB (t.primarySets i j) + t.primaryParities i
  replOffsets := t.replOffsets
  replValues := Function.update t.replValues j (fun k => chunkDB (t.replOffsets j k))
  backupSets := t.backupSets
  backupParities := fun j' k =>
    if j' = j then t.backupParities j' k
    else chunkDB (t.backupSets j' k j) + t.backupParities j' k
  used := t.used

/-- The `HintTable` obtained after streaming the subset of chunks `s : Finset Chunk` of `db`. -/
@[expose] def streamUpTo [DecidableEq Chunk] (db : Chunk × Offset → Bool) (s : Finset Chunk)
    (primarySets : Fin M₁ → Chunk → Offset) (replOffsets : Chunk → Fin M₂ → Offset)
    (backupSets : Chunk → Fin M₂ → Chunk → Offset) : HintTable M₁ M₂ Chunk Offset where
  primarySets := primarySets
  primaryParities := fun i => ∑ j ∈ s, db (j, primarySets i j)
  replOffsets := replOffsets
  replValues := fun j k => if j ∈ s then db (j, replOffsets j k) else false
  backupSets := backupSets
  backupParities := fun j' k => ∑ j ∈ s.erase j', db (j, backupSets j' k j)
  used := fun _ => 0

/-- Offline preprocessing result after streaming all chunks `Finset.univ` of `db`. -/
@[expose] def streamPreprocess [Fintype Chunk] [DecidableEq Chunk] (db : Chunk × Offset → Bool)
    (primarySets : Fin M₁ → Chunk → Offset) (replOffsets : Chunk → Fin M₂ → Offset)
    (backupSets : Chunk → Fin M₂ → Chunk → Offset) : HintTable M₁ M₂ Chunk Offset :=
  streamUpTo db Finset.univ primarySets replOffsets backupSets

@[simp]
theorem streamUpTo_empty [DecidableEq Chunk] (db : Chunk × Offset → Bool)
    (primarySets : Fin M₁ → Chunk → Offset) (replOffsets : Chunk → Fin M₂ → Offset)
    (backupSets : Chunk → Fin M₂ → Chunk → Offset) :
    streamUpTo db ∅ primarySets replOffsets backupSets =
      initHintTable primarySets replOffsets backupSets := by
  ext <;> simp only [streamUpTo, initHintTable, Finset.sum_empty, Finset.notMem_empty, ↓reduceIte,
    Finset.erase_empty] <;> rfl

/-- Streaming a fresh chunk `j ∉ s` via `streamChunk` transitions `streamUpTo db s` to
`streamUpTo db (insert j s)`. -/
theorem streamChunk_streamUpTo [DecidableEq Chunk] (db : Chunk × Offset → Bool)
    {s : Finset Chunk} {j : Chunk} (hj : j ∉ s) (primarySets : Fin M₁ → Chunk → Offset)
    (replOffsets : Chunk → Fin M₂ → Offset) (backupSets : Chunk → Fin M₂ → Chunk → Offset) :
    streamChunk j (fun δ => db (j, δ)) (streamUpTo db s primarySets replOffsets backupSets) =
      streamUpTo db (insert j s) primarySets replOffsets backupSets := by
  ext i j' k
  · rfl
  · simp [streamChunk, streamUpTo, Finset.sum_insert hj]
  · rfl
  · by_cases hjeq : i = j
    · subst hjeq
      simp [streamChunk, streamUpTo]
    · simp [streamChunk, streamUpTo, hjeq]
  · rfl
  · by_cases hjeq : i = j
    · subst hjeq
      simp [streamChunk, streamUpTo, Finset.erase_insert hj, Finset.erase_eq_of_notMem hj]
    · have hmem : j ∉ s.erase i := fun h => hj (Finset.mem_of_mem_erase h)
      simp [streamChunk, streamUpTo, hjeq, Finset.erase_insert_of_ne (Ne.symm hjeq),
        Finset.sum_insert hmem]
  · rfl

/-- Folding `streamChunk` over any duplicate-free list of chunks `js` starting from
`initHintTable` produces `streamUpTo db js.toFinset`. -/
theorem foldr_streamChunk_eq_streamUpTo [DecidableEq Chunk] (db : Chunk × Offset → Bool)
    (primarySets : Fin M₁ → Chunk → Offset) (replOffsets : Chunk → Fin M₂ → Offset)
    (backupSets : Chunk → Fin M₂ → Chunk → Offset) {js : List Chunk} (hnd : js.Nodup) :
    js.foldr (fun j t => streamChunk j (fun δ => db (j, δ)) t)
      (initHintTable primarySets replOffsets backupSets) =
      streamUpTo db js.toFinset primarySets replOffsets backupSets := by
  induction js with
  | nil =>
    simp only [List.foldr_nil, List.toFinset_nil, streamUpTo_empty]
  | cons j js ih =>
    rw [List.nodup_cons] at hnd
    have hj : j ∉ js.toFinset := by simpa using hnd.1
    simp only [List.foldr_cons, ih hnd.2, List.toFinset_cons, streamChunk_streamUpTo db hj]

/-- **Offline single-pass streaming correctness**: folding `streamChunk` once over all chunks
`Finset.univ.toList` starting from `initHintTable` produces `streamPreprocess`. -/
theorem foldr_streamChunk_univ [Fintype Chunk] [DecidableEq Chunk] (db : Chunk × Offset → Bool)
    (primarySets : Fin M₁ → Chunk → Offset) (replOffsets : Chunk → Fin M₂ → Offset)
    (backupSets : Chunk → Fin M₂ → Chunk → Offset) :
    (Finset.univ : Finset Chunk).toList.foldr
      (fun j t => streamChunk j (fun δ => db (j, δ)) t)
      (initHintTable primarySets replOffsets backupSets) =
      streamPreprocess db primarySets replOffsets backupSets := by
  rw [foldr_streamChunk_eq_streamUpTo db primarySets replOffsets backupSets
    (Finset.nodup_toList _), Finset.toList_toFinset, streamPreprocess]

namespace HintTable

/-- Parity validity invariant for a `HintTable` against database `db`:

1. Every primary parity equals the full parity `setParity db (t.primarySets i)`.
2. Every replacement value equals `db (j, t.replOffsets j k)`.
3. Every backup parity equals the punctured parity `backupParity db j (t.backupSets j k)`. -/
structure Valid [Fintype Chunk] [DecidableEq Chunk] (db : Chunk × Offset → Bool)
    (t : HintTable M₁ M₂ Chunk Offset) : Prop where
  /-- Each primary parity is the full parity of its primary set. -/
  valid_primary : ∀ i : Fin M₁, t.primaryParities i = setParity db (t.primarySets i)
  /-- Each replacement value is the database bit at its replacement offset. -/
  valid_repl : ∀ (j : Chunk) (k : Fin M₂), t.replValues j k = db (j, t.replOffsets j k)
  /-- Each backup parity is the punctured parity of its backup set. -/
  valid_backup : ∀ (j : Chunk) (k : Fin M₂),
    t.backupParities j k = backupParity db j (t.backupSets j k)

/-- `streamPreprocess` produces a valid `HintTable`. -/
theorem valid_streamPreprocess [Fintype Chunk] [DecidableEq Chunk] (db : Chunk × Offset → Bool)
    (primarySets : Fin M₁ → Chunk → Offset) (replOffsets : Chunk → Fin M₂ → Offset)
    (backupSets : Chunk → Fin M₂ → Chunk → Offset) :
    Valid db (streamPreprocess db primarySets replOffsets backupSets) where
  valid_primary _ := rfl
  valid_repl j _ := by simp [streamPreprocess, streamUpTo]
  valid_backup _ _ := rfl

/-- Deterministic precondition of [Zhou, Park, Zheng and Shi, Theorem 3.3][ZhouParkZhengShi2024]
for answering query `x`: some primary hint contains `x`, and chunk `x.1` has an unconsumed
backup/replacement entry (`t.used x.1 < M₂`). -/
@[expose] def CanAnswer (t : HintTable M₁ M₂ Chunk Offset) (x : Chunk × Offset) : Prop :=
  (∃ i : Fin M₁, t.primarySets i x.1 = x.2) ∧ t.used x.1 < M₂

/-- Deterministic online query-answer-reconstruct-refresh step on `t : HintTable M₁ M₂ Chunk Offset`
([Zhou, Park, Zheng and Shi, Figure 1][ZhouParkZhengShi2024]), returning the refreshed `HintTable`
and the reconstructed database bit `β`. -/
@[expose] def onlineStep [Fintype Chunk] [DecidableEq Chunk] [DecidableEq Offset]
    (db : Chunk × Offset → Bool) (t : HintTable M₁ M₂ Chunk Offset) (x : Chunk × Offset) :
    HintTable M₁ M₂ Chunk Offset × Bool :=
  match findHint t.primarySets x with
  | some i =>
    if hk : t.used x.1 < M₂ then
      let k : Fin M₂ := ⟨t.used x.1, hk⟩
      let qSet := replaceInChunk (t.primarySets i) x.1 (t.replOffsets x.1 k)
      let q := setParity db qSet
      let β := reconstructBit q (t.primaryParities i) (t.replValues x.1 k)
      let newSet := replaceInChunk (t.backupSets x.1 k) x.1 x.2
      let newParity := refreshParity (t.backupParities x.1 k) β
      ({ t with
          primarySets := Function.update t.primarySets i newSet
          primaryParities := Function.update t.primaryParities i newParity
          used := Function.update t.used x.1 (t.used x.1 + 1) }, β)
    else
      (t, false)
  | none => (t, false)

/-- **Single-query deterministic correctness of Piano**
([Zhou, Park, Zheng and Shi, Theorem 3.3][ZhouParkZhengShi2024]): if `t.Valid db` and
`t.CanAnswer x` (a primary hint contains `x` and chunk `x.1`'s backup group is not exhausted), then
`t.onlineStep db x` reconstructs `db x` and preserves `Valid db`. -/
theorem onlineStep_correct [Fintype Chunk] [DecidableEq Chunk] [DecidableEq Offset]
    {db : Chunk × Offset → Bool} {t : HintTable M₁ M₂ Chunk Offset} {x : Chunk × Offset}
    (hvalid : t.Valid db) (hcan : t.CanAnswer x) :
    (t.onlineStep db x).2 = db x ∧ (t.onlineStep db x).1.Valid db := by
  obtain ⟨hex, hk⟩ := hcan
  have hisome : (findHint t.primarySets x).isSome := (findHint_isSome_iff t.primarySets x).mpr hex
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hisome
  have hTi : t.primarySets i x.1 = x.2 := findHint_eq_some hi
  simp only [onlineStep, hi, ↓reduceDIte, hk]
  have hβ : reconstructBit
      (setParity db (replaceInChunk (t.primarySets i) x.1 (t.replOffsets x.1 ⟨t.used x.1, hk⟩)))
      (t.primaryParities i) (t.replValues x.1 ⟨t.used x.1, hk⟩) = db x := by
    rw [hvalid.valid_primary i, hvalid.valid_repl x.1 ⟨t.used x.1, hk⟩,
      reconstructBit_setParity_eq db (t.primarySets i) x (t.replOffsets x.1 ⟨t.used x.1, hk⟩) hTi]
  refine ⟨hβ, ?_⟩
  refine ⟨fun i' => ?_, hvalid.valid_repl, hvalid.valid_backup⟩
  by_cases hieq : i' = i
  · subst hieq
    simp only [Function.update_self, hβ, hvalid.valid_backup x.1 ⟨t.used x.1, hk⟩,
      refreshParity_eq_setParity]
  · simp only [Function.update_of_ne hieq, hvalid.valid_primary i']

/-- **The full client moves its sets by `pianoStepSets`.** Suppose primary hint `i` is the first
to contain `x` and chunk `x.1` still has an unconsumed entry `k = t.used x.1`. Let `B` be the
backup set `t.backupSets x.1 k` with its `x.1`-th offset set to the replacement offset
`r = t.replOffsets x.1 k`. Then the set `S⟨j* → r⟩` that `onlineStep` sends to the server
([Zhou, Park, Zheng and Shi, Figure 1, Step 1(c)][ZhouParkZhengShi2024]) and its refreshed
primary table (Step 2) are the two components of `pianoStepSets x (t.primarySets, B)`. So the
privacy results for `pianoHybridScheme` describe the same set map; they do not cover the
replacement and backup entries that `onlineStep` stores in advance. -/
theorem onlineStep_sets_eq_pianoStepSets [Fintype Chunk] [DecidableEq Chunk] [DecidableEq Offset]
    (db : Chunk × Offset → Bool) (t : HintTable M₁ M₂ Chunk Offset) (x : Chunk × Offset)
    {i : Fin M₁} (hi : findHint t.primarySets x = some i) (hk : t.used x.1 < M₂) :
    (t.onlineStep db x).1.primarySets =
        (pianoStepSets x (t.primarySets, replaceInChunk (t.backupSets x.1 ⟨t.used x.1, hk⟩) x.1
          (t.replOffsets x.1 ⟨t.used x.1, hk⟩))).1 ∧
      replaceInChunk (t.primarySets i) x.1 (t.replOffsets x.1 ⟨t.used x.1, hk⟩) =
        (pianoStepSets x (t.primarySets, replaceInChunk (t.backupSets x.1 ⟨t.used x.1, hk⟩) x.1
          (t.replOffsets x.1 ⟨t.used x.1, hk⟩))).2 := by
  simp [onlineStep, pianoStepSets, hi, hk]

/-- Runs a sequence of deterministic online steps on `xs : List (Chunk × Offset)` starting from
`t`, returning the final `HintTable` and the list of reconstructed bits. -/
@[expose] def runOnlineSteps [Fintype Chunk] [DecidableEq Chunk] [DecidableEq Offset]
    (db : Chunk × Offset → Bool) : HintTable M₁ M₂ Chunk Offset → List (Chunk × Offset) →
      HintTable M₁ M₂ Chunk Offset × List Bool
  | t, [] => (t, [])
  | t, x :: xs =>
    let stepOut := t.onlineStep db x
    let tailOut := runOnlineSteps db stepOut.1 xs
    (tailOut.1, stepOut.2 :: tailOut.2)

/-- Sequential availability predicate over a query list `xs : List (Chunk × Offset)`: at each step,
the current `HintTable` satisfies `CanAnswer` for the next query. -/
@[expose] def CanAnswerSeq [Fintype Chunk] [DecidableEq Chunk] [DecidableEq Offset]
    (db : Chunk × Offset → Bool) : HintTable M₁ M₂ Chunk Offset → List (Chunk × Offset) → Prop
  | _, [] => True
  | t, x :: xs => t.CanAnswer x ∧ CanAnswerSeq db (t.onlineStep db x).1 xs

/-- **Multi-query deterministic correctness of Piano**
([Zhou, Park, Zheng and Shi, Theorem 3.3][ZhouParkZhengShi2024]): over any sequence of queries
`xs : List (Chunk × Offset)` for which `CanAnswerSeq db t xs` holds, `t.runOnlineSteps db xs`
outputs the exact database bits `xs.map db` and preserves `Valid db`. -/
theorem runOnlineSteps_correct [Fintype Chunk] [DecidableEq Chunk] [DecidableEq Offset]
    {db : Chunk × Offset → Bool} {t : HintTable M₁ M₂ Chunk Offset} {xs : List (Chunk × Offset)}
    (hvalid : t.Valid db) (hcan : t.CanAnswerSeq db xs) :
    (t.runOnlineSteps db xs).2 = xs.map db ∧ (t.runOnlineSteps db xs).1.Valid db := by
  induction xs generalizing t with
  | nil =>
    exact ⟨rfl, hvalid⟩
  | cons x xs ih =>
    obtain ⟨hx, hxs⟩ := hcan
    obtain ⟨hβ, hvalid'⟩ := onlineStep_correct hvalid hx
    obtain ⟨hβs, hvalid''⟩ := ih hvalid' hxs
    exact ⟨by simp [runOnlineSteps, hβ, hβs], hvalid''⟩

end HintTable

/-! ### The ideal-random-set hybrid as a `Preprocessing.Scheme` and adaptive privacy

`pianoHybridScheme` keeps exactly the parts of the Figure 1 client that the server can observe: the
primary sets, the matching rule `findHint`, the edited set sent to the server, and the replacement
of the consumed hint. It samples the replacement offset and the backup set online instead of
storing them during preprocessing, so it holds no replacement bits or backup parities and its
`reconstruct` output is not `db x` in general. Correctness of the full client is
`HintTable.runOnlineSteps_correct`, and `HintTable.onlineStep_sets_eq_pianoStepSets` shows that the
full client moves its sets by the same map `pianoStepSets`. -/

/-- Persistent client hint state for `pianoHybridScheme`, storing the primary table of `M₁` chunked
sets and their parity bits. -/
@[ext]
structure PianoHint (M₁ : ℕ) (Chunk Offset : Type) where
  /-- The `M₁` chunked sets in the primary hint table. -/
  primarySets : Fin M₁ → Chunk → Offset
  /-- The parity bit for each primary hint set. -/
  primaryParities : Fin M₁ → Bool

/-- Retained per-query client state for `pianoHybridScheme` between `query`, `reconstruct`, and
`refresh`. -/
structure PianoQueryRecord (M₁ : ℕ) (Chunk Offset : Type) where
  /-- Index of the matched primary hint, or `none` if no primary hint contained the query. -/
  matchedHint : Option (Fin M₁)
  /-- Stored parity of the matched primary hint. -/
  matchedParity : Bool
  /-- Placeholder for the replacement bit `db (j*, r)`: always `false` in `pianoHybridScheme`, which
  stores no replacement entries. -/
  replacementBit : Bool
  /-- Promoted primary set `replaceInChunk B j* δ*` used to refresh the matched slot. -/
  promotedSet : Chunk → Offset
  /-- Placeholder for the punctured backup parity of the backup set `B`: always `false` in
  `pianoHybridScheme`, which stores no backup parities. -/
  backupParityBit : Bool

/-- The ideal-random-set hybrid of Piano, packaged as a
`Preprocessing.Scheme (Chunk × Offset) (PianoHint M₁ Chunk Offset)
(PianoQueryRecord M₁ Chunk Offset) (Chunk → Offset) Bool`. It follows the `Real*` experiment in the
proof of [Zhou, Park, Zheng and Shi, Theorem C.1][ZhouParkZhengShi2024], with truly random sets in
place of PRF sets: the primary sets are uniform, and each query draws a fresh uniform set `B` whose
`j*`-th offset plays the replacement offset `r` and whose other offsets form the backup set
(`eval_replaceInChunk_uniform` shows this matches drawing `r` and the backup set independently).
If a primary set contains `x`, the server receives that set with chunk `j*` edited to `r`, and the
set is replaced by `B` with `x` forced in; otherwise the server receives `B` and the table is
unchanged.

This is a model of the server's view only. Backups are never exhausted, and `replacementBit` and
`backupParityBit` are placeholders (`false`), so `reconstruct` returns `q ⊕ p` rather than `db x`
and this is **not** a correct PIR scheme: no correctness result is stated for it. Correctness is
proved for the full Figure 1 client `HintTable.onlineStep`. -/
@[expose] noncomputable def pianoHybridScheme (M₁ : ℕ) (Chunk Offset : Type) [Fintype Chunk]
    [DecidableEq Chunk] [Fintype Offset] [DecidableEq Offset] [Nonempty Offset] :
    Scheme (Chunk × Offset) (PianoHint M₁ Chunk Offset)
      (PianoQueryRecord M₁ Chunk Offset) (Chunk → Offset) Bool where
  preprocess db := do
    let T ← ProbComp.uniform (Fin M₁ → Chunk → Offset)
    pure ⟨T, fun i => setParity db (T i)⟩
  query h x := do
    let B ← ProbComp.uniform (Chunk → Offset)
    pure (match findHint h.primarySets x with
      | some i => ⟨some i, h.primaryParities i, false, replaceInChunk B x.1 x.2, false⟩
      | none => ⟨none, false, false, B, false⟩,
      (pianoStepSets x (h.primarySets, B)).2)
  answer db qSet := setParity db qSet
  reconstruct rec q := reconstructBit q rec.matchedParity rec.replacementBit
  refresh h _ rec β :=
    pure (match rec.matchedHint with
      | some i => ⟨Function.update h.primarySets i rec.promotedSet,
                   Function.update h.primaryParities i (refreshParity rec.backupParityBit β)⟩
      | none => h)

/-- After refreshing in `pianoHybridScheme`, the new `primarySets` equals
`(pianoStepSets x (h.primarySets, B)).1`. -/
theorem pianoHybridScheme_refresh_primarySets [DecidableEq Chunk] [DecidableEq Offset]
    (h : PianoHint M₁ Chunk Offset) (x : Chunk × Offset) (B : Chunk → Offset) :
    (match findHint h.primarySets x with
      | some i => Function.update h.primarySets i (replaceInChunk B x.1 x.2)
      | none => h.primarySets) = (pianoStepSets x (h.primarySets, B)).1 := by
  cases hfind : findHint h.primarySets x <;> simp [pianoStepSets, hfind]

section PianoSchemePrivacy

variable [Fintype Chunk] [DecidableEq Chunk] [Fintype Offset] [DecidableEq Offset] [Nonempty Offset]

/-- Projected one-step transition of `(primarySets, serverState)` in the adaptive privacy
experiment for `pianoHybridScheme`. -/
private noncomputable def pianoAdaptiveStepSets {St : Type}
    (adv : AdaptiveServer (Chunk × Offset) (Chunk → Offset) Bool St)
    (T : Fin M₁ → Chunk → Offset) (st : St) :
    PMF ((Fin M₁ → Chunk → Offset) × St) :=
  (ProbComp.eval (adv.chooseQuery st)).bind fun p =>
    (PMF.uniformOfFintype (Chunk → Offset)).bind fun B =>
      (ProbComp.eval (adv.onQuery p.1 (pianoStepSets p.2 (T, B)).2)).map fun sa =>
        ((pianoStepSets p.2 (T, B)).1, sa.1)

/-- **Multi-query adaptive perfect privacy of the Piano hybrid** (Definition 3.1, and the
ideal-random-set part of the proof of Theorem C.1 in
[Zhou, Park, Zheng and Shi][ZhouParkZhengShi2024]): `pianoHybridScheme` is perfectly private with
simulator `ProbComp.uniform (Chunk → Offset)` against any adaptive malicious server `adv` over any
number of queries `k`. `pianoHybridScheme` is not a correct PIR scheme, so this is privacy of the
server's view in the hybrid only. The PRF step and the correct `HintTable` client are not covered.
-/
theorem isPerfectlyPrivateWith_pianoHybridScheme :
    (pianoHybridScheme M₁ Chunk Offset).IsPerfectlyPrivateWith
      (ProbComp.uniform (Chunk → Offset)) := by
  apply Scheme.isPerfectlyPrivateWith_of_invariant
    (proj := PianoHint.primarySets)
    (inv := PMF.uniformOfFintype (Fin M₁ → Chunk → Offset))
    (sim := ProbComp.uniform (Chunk → Offset))
    (stepS := fun adv => pianoAdaptiveStepSets adv)
  · intro db
    simp only [pianoHybridScheme, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map]
    exact PMF.bind_pure _
  · intro St adv h st
    dsimp only [pianoAdaptiveStepSets]
    simp only [Scheme.realAdaptiveStep, pianoHybridScheme, ProbComp.eval_bind,
      ProbComp.eval_uniform, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map]
    congr 1
    funext p
    congr 1
    funext B
    congr 1
    funext sa
    cases hfind : findHint h.primarySets p.2 <;>
      simp [pianoStepSets, hfind]
  · intro St adv st kCont
    dsimp only [pianoAdaptiveStepSets]
    simp only [idealAdaptiveStep, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.bind_map, Function.comp_def]
    rw [PMF.bind_comm (PMF.uniformOfFintype (Fin M₁ → Chunk → Offset))
      (ProbComp.eval (adv.chooseQuery st))]
    congr 1
    funext p
    rw [uniformOfFintype_bind_bind_pianoStepSets p.2
      (fun tq => (ProbComp.eval (adv.onQuery p.1 tq.2)).bind fun sa => kCont tq.1 sa.1)]
    rw [PMF.bind_comm (PMF.uniformOfFintype (Fin M₁ → Chunk → Offset))
      (PMF.uniformOfFintype (Chunk → Offset))]
    congr 1
    funext Q
    rw [PMF.bind_comm (PMF.uniformOfFintype (Fin M₁ → Chunk → Offset))
      (ProbComp.eval (adv.onQuery p.1 Q))]

/-- `pianoHybridScheme` satisfies `Scheme.IsPerfectlyPrivate`. The hybrid is not a correct PIR
scheme (see `pianoHybridScheme`); privacy of the correct `HintTable` client is not proved. -/
theorem isPerfectlyPrivate_pianoHybridScheme :
    (pianoHybridScheme M₁ Chunk Offset).IsPerfectlyPrivate :=
  isPerfectlyPrivateWith_pianoHybridScheme.isPerfectlyPrivate

/-- Every adaptive malicious server with Boolean finalizer `finalize : St → Bool` has zero
distinguishing advantage against `pianoHybridScheme` in the ideal-random-set model. The hybrid is
not a correct PIR scheme. -/
theorem privacyAdvantage_pianoHybridScheme_eq_zero {St : Type}
    (adv : AdaptiveServer (Chunk × Offset) (Chunk → Offset) Bool St) (finalize : St → Bool)
    (db : Chunk × Offset → Bool) (k : ℕ) (st₀ : St) :
    (pianoHybridScheme M₁ Chunk Offset).privacyAdvantage (ProbComp.uniform (Chunk → Offset))
      adv finalize db k st₀ = 0 :=
  isPerfectlyPrivateWith_pianoHybridScheme.privacyAdvantage_eq_zero adv finalize db k st₀

/-- **Multi-query non-adaptive transcript privacy of the Piano hybrid** (the uniform-set view in the
proof sketch of [Zhou, Park, Zheng and Shi, Theorem 3.2][ZhouParkZhengShi2024]): for every database
`db` and fixed query sequence `xs : List (Chunk × Offset)`, the `xs.length` sets that
`pianoHybridScheme` sends to the server are distributed as `xs.length` independent uniform draws
from `Chunk → Offset`, independent of `db` and `xs`. -/
theorem eval_queryTranscript_pianoHybridScheme (db : Chunk × Offset → Bool)
    (xs : List (Chunk × Offset)) :
    ProbComp.eval ((pianoHybridScheme M₁ Chunk Offset).queryTranscript db xs) =
      ProbComp.eval (simTranscript (ProbComp.uniform (Chunk → Offset)) xs.length) := by
  apply Scheme.eval_queryTranscript_eq_of_invariant
    (proj := PianoHint.primarySets)
    (inv := PMF.uniformOfFintype (Fin M₁ → Chunk → Offset))
    (sim := ProbComp.uniform (Chunk → Offset))
    (stepQ := fun T x =>
      (PMF.uniformOfFintype (Chunk → Offset)).map fun B => pianoStepSets x (T, B))
  · simp only [pianoHybridScheme, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map]
    exact PMF.bind_pure _
  · intro h x
    simp only [Scheme.queryStep, pianoHybridScheme, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, PMF.map]
    congr 1
    funext B
    cases hfind : findHint h.primarySets x <;> simp [pianoStepSets, hfind]
  · intro x kCont
    simp only [PMF.bind_map, Function.comp_def, ProbComp.eval_uniform]
    rw [uniformOfFintype_bind_bind_pianoStepSets x (fun tq => kCont tq.1 tq.2)]
    exact PMF.bind_comm _ _ _

end PianoSchemePrivacy

/-! ### Online communication cost (Theorem 3.4 online part) -/

/-- For `Chunk = Fin c` and `Offset = Fin b`, a query that sends one offset per chunk
(`Fin c → Fin b`, the edited set `S⟨j* → r⟩` of
[Zhou, Park, Zheng and Shi, Figure 1, Step 1(c)][ZhouParkZhengShi2024]) and receives one parity bit
costs `⌈log₂ (b ^ c)⌉ + 1` bits. -/
theorem onlineCommunication_fullQuery (c b : ℕ) :
    onlineCommunication (Fin c → Fin b) Bool = Nat.clog 2 (b ^ c) + 1 := by
  rw [onlineCommunication_bool, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- With `√n = c` chunks of size `b = 2 ^ ℓ`, each online query of the main scheme communicates
`c * ℓ + 1` bits, the `O(√n)` online communication of
[Zhou, Park, Zheng and Shi, Theorem 3.4][ZhouParkZhengShi2024] (up to the `log` factor of the offset
encoding). -/
theorem onlineCommunication_fullQuery_pow (c ℓ : ℕ) :
    onlineCommunication (Fin c → Fin (2 ^ ℓ)) Bool = c * ℓ + 1 := by
  rw [onlineCommunication_fullQuery, ← pow_mul, mul_comm, Nat.clog_pow _ _ (by decide)]

/-- In the variant of [Zhou, Park, Zheng and Shi, Appendix A][ZhouParkZhengShi2024], the client
sends the compacted offset vector of `m = √n - 1` offsets (`Fin m → Fin b`) and the server returns
one parity for each of the `m + 1 = √n` possible positions of the removed chunk
(`Fin (m + 1) → Bool`, Figure 3). This costs `⌈log₂ (b ^ m)⌉ + (m + 1)` bits. -/
theorem onlineCommunication_compacted (m b : ℕ) :
    onlineCommunication (Fin m → Fin b) (Fin (m + 1) → Bool) =
      Nat.clog 2 (b ^ m) + (m + 1) := by
  rw [onlineCommunication_eq, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_bool, Nat.clog_pow _ _ (by decide)]

/-- With offsets in `Fin (2 ^ ℓ)`, the Appendix A variant communicates `m * ℓ + (m + 1)` bits per
online query, for `m = √n - 1`. -/
theorem onlineCommunication_compacted_pow (m ℓ : ℕ) :
    onlineCommunication (Fin m → Fin (2 ^ ℓ)) (Fin (m + 1) → Bool) = m * ℓ + (m + 1) := by
  rw [onlineCommunication_compacted, ← pow_mul, mul_comm, Nat.clog_pow _ _ (by decide)]

end Cslib.Crypto.Protocols.PIR.Preprocessing.Piano
