/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.RehashExec

/-!
# Multi-Level Randomized `OracleComp` Dictionary Execution and Unconditional `Lemma 5.3`

This file couples the external dynamic dictionary interface (`Dynamic.Op`, `Dynamic.spec`) on
`TreeSchedule.TreeState` to the multi-level `OracleComp` seed-resampling process (`RehashExec.lean`)
and proves the unconditional `Lemma 5.3` expected rehashing work bound across initialization and any
admissible sequence of `M` external dictionary operations (`query`, `insert` with overwrite, and
`delete`) for the subconstant-redundancy dictionary tree of Tianxiao Li, Jingxun Liang, Huacheng Yu,
and Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per Key*
([LiLiangYuZhou2024, Section 5.5, Lemma 5.3];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 34–35 / printed pp. 33–34).

## Modeling design

* **Normal updates vs. localized subtree seed resampling**: On each single-key sentinel-padded
  update (`execRawInsertFresh`, `execRawDeleteMem`), if `st.seeds` remains good on the post-update
  padded set `S'`, the execution takes the deterministic normal path (`normalInsertFresh` or
  `normalDeleteMem`, `0` oracle queries). When `st.seeds` fails on `S'`, `stepTrunc` resamples only
  node seeds inside the failing subtree `InSubtree ℓ₀ u₀` (`stepTrunc_seed_eq_outside_inSubtree`)
  under `rehashWorkCost` (`2 * nFloor ℓ` work per resampled node) and `materializeFromTrunc`
  constructs the canonical `TreeState` for `d'` with those resampled seeds (localized storage
  reconstruction on `TreeState` is formalized separately by `TreeState.rehashSubtree` in
  `TreeRehash.lean`).
* **Sentinel-padded step expansion**: Each external `insert` or `delete` maintains
  `#(paddedDom d) ∈ {cap - 1, cap}` by performing at most `2` internal single-key padded updates
  (one sentinel update plus one real-key update), so `M` external operations emit at most `2 * M`
  `PaddedStep`s.

## Main definitions

* `TreeSchedule.execInit`, `TreeSchedule.TreeState.execInsert`, `TreeSchedule.TreeState.execDelete`,
  `TreeSchedule.TreeState.execOp`, `TreeSchedule.execHistory`: randomized `OracleComp` dictionary
  initialization, operations, and multi-step execution over `Dynamic.Op P.univ`.

## Main results

* `TreeSchedule.mem_support_execHistory`: every supported outcome `(st', trace)` of `execHistory` on
  an admissible history `ops` satisfies `st'.WellFormed` for the final abstract dictionary state and
  returns the exact `Dynamic.spec` observation trace.
* `TreeSchedule.expectedCost_execHistory_le`: unconditional `14 * (depth + 1) * (cap + 2 * M)`
  expected rehashing work bound for any `ConcentrationReady` schedule `P`.
* `canonicalSchedule_expectedCost_execHistory_le`: unconditional `84 * (n + M) * Nat.logStar n`
  expected rehashing work bound across `ValidRegime` (`Lemma 5.3`).

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

open scoped ENNReal

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.Probability
open Finset

namespace TreeSchedule

@[ext]
theorem PaddedStep.ext {P : TreeSchedule} {s₁ s₂ : P.PaddedStep}
    (hpre : s₁.preSet = s₂.preSet) (hpost : s₁.postSet = s₂.postSet) (hkey : s₁.key = s₂.key) :
    s₁ = s₂ := by
  cases s₁; cases s₂; subst hpre hpost hkey; rfl

/-- Construct a `PaddedStep` inserting `x` into `S`. -/
def mkInsertStep (P : TreeSchedule) (S : Finset (Fin P.paddedUniv)) (x : Fin P.paddedUniv)
    (hpre : P.validRootBounds S) (hpost : P.validRootBounds (Insert.insert x S)) :
    P.PaddedStep where
  preSet := S
  postSet := Insert.insert x S
  key := x
  pre_bounds := hpre
  post_bounds := hpost
  diff_key y :=
    if hyx : y = x then Or.inr hyx
    else Or.inl ⟨fun hm => (mem_insert.mp hm).resolve_left hyx, mem_insert_of_mem⟩

/-- Construct a `PaddedStep` erasing `z` from `S`. -/
def mkDeleteStep (P : TreeSchedule) (S : Finset (Fin P.paddedUniv)) (z : Fin P.paddedUniv)
    (hpre : P.validRootBounds S) (hpost : P.validRootBounds (S.erase z)) :
    P.PaddedStep where
  preSet := S
  postSet := S.erase z
  key := z
  pre_bounds := hpre
  post_bounds := hpost
  diff_key y :=
    if hyz : y = z then Or.inr hyz
    else Or.inl ⟨mem_of_mem_erase, fun hm => mem_erase.mpr ⟨hyz, hm⟩⟩

namespace TreeState

variable {P : TreeSchedule}

theorem seeds_withSentCount (st : P.TreeState) (sc : ℕ) :
    ({ st with sentCount := sc } : P.TreeState).seeds = st.seeds := by
  let st' : P.TreeState := { st with sentCount := sc }
  ext ℓ hℓ u
  by_cases h0 : ℓ = 0
  · subst h0; rw [seeds_zero, seeds_zero]
  · by_cases h1 : ℓ = 1
    · subst h1; rw [seeds_one, seeds_one]
    · by_cases hlt : ℓ < P.depth
      · rw [seeds_inner st' (by omega) hlt hℓ, seeds_inner st (by omega) hlt hℓ]
      · have hd : ℓ = P.depth := by omega
        subst hd; rw [seeds_depth, seeds_depth]

end TreeState

/-! ## Section 1: Randomized `OracleComp` Dictionary Operations on `TreeState` -/

open Classical in
/-- Materialize a `TreeState` for `(d, sc)` from full-depth `ts : P.TruncSeeds P.depth` whenever
`ts.toSeeds` is good on `P.paddedDom d` (which holds on every supported `OracleComp` branch). -/
noncomputable def materializeFromTrunc (P : TreeSchedule) (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (d : P.PaddedDict) (sc : ℕ) (ts : P.TruncSeeds P.depth) : P.TreeState :=
  if hg : ts.toSeeds.AllGoodSeeds (P.paddedDom d) then
    P.buildTreeFromSeeds scheme d sc ts.toSeeds hg
  else
    P.initTree hcr scheme

/-- Randomized `OracleComp` initialization of an empty external dictionary (`Dictionary.empty`)
padded with `P.cap` sentinels. -/
@[expose]
noncomputable def execInit (P : TreeSchedule) (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)) :
    OracleComp P.goodSeedSpec P.TreeState :=
  P.initTrunc P.depth le_rfl (P.paddedDom P.initPaddedDict) >>= fun ts =>
    pure (P.materializeFromTrunc hcr scheme P.initPaddedDict P.cap ts)

namespace TreeState

variable {P : TreeSchedule}

open Classical in
/-- Randomized internal fresh-key insertion (`x ∉ paddedDom d`): runs `normalInsertFresh` (`0`
queries) if `st.seeds` remains good on `Insert.insert x S`, and otherwise resamples failing subtree
seeds via `stepTrunc` before rebuilding. -/
noncomputable def execRawInsertFresh (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (x : Fin P.paddedUniv) (v : Fin P.valBound) :
    OracleComp P.goodSeedSpec P.TreeState :=
  let d_cur : P.PaddedDict := st.rawQuery scheme
  let S_cur := P.paddedDom d_cur
  let S' := Insert.insert x S_cur
  if h_wf : ∃ storeLvl, st.WellFormedPadded scheme d_cur storeLvl ∧
      x ∉ S_cur ∧ P.validRootBounds S' then
    have ⟨hwf, hx_fresh, hcard'⟩ := Classical.choose_spec h_wf
    if hgood' : st.seeds.AllGoodSeeds S' then
      pure (st.normalInsertFresh hwf x v hx_fresh hgood')
    else
      let pstep := P.mkInsertStep S_cur x hwf.goodSeeds.1 hcard'
      P.stepTrunc P.depth le_rfl pstep (P.truncOfSeeds P.depth st.seeds) >>= fun am =>
        pure (P.materializeFromTrunc hcr scheme (Function.update d_cur x (some v))
          st.sentCount am.1)
  else
    pure st

open Classical in
/-- Randomized internal member-key deletion (`z ∈ paddedDom d`): runs `normalDeleteMem`
(`Algorithm 3`, `0` queries) if `st.seeds` remains good on `S.erase z`, and otherwise resamples
failing subtree seeds via `stepTrunc` before rebuilding. -/
noncomputable def execRawDeleteMem (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (z : Fin P.paddedUniv) :
    OracleComp P.goodSeedSpec P.TreeState :=
  let d_cur : P.PaddedDict := st.rawQuery scheme
  let S_cur := P.paddedDom d_cur
  let S' := S_cur.erase z
  if h_wf : ∃ storeLvl, st.WellFormedPadded scheme d_cur storeLvl ∧
      z ∈ S_cur ∧ P.validRootBounds S' then
    have ⟨hwf, _, hcard'⟩ := Classical.choose_spec h_wf
    if st.seeds.AllGoodSeeds S' then
      pure (st.normalDeleteMem scheme z)
    else
      let pstep := P.mkDeleteStep S_cur z hwf.goodSeeds.1 hcard'
      P.stepTrunc P.depth le_rfl pstep (P.truncOfSeeds P.depth st.seeds) >>= fun am =>
        pure (P.materializeFromTrunc hcr scheme (Function.update d_cur z none)
          st.sentCount am.1)
  else
    pure st

/-- Randomized external `insert` (with in-place overwrite and sentinel padding in `{cap - 1, cap}`).
-/
noncomputable def execInsert (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (u : Fin P.univ) (v : Fin P.valBound) :
    OracleComp P.goodSeedSpec P.TreeState :=
  let x := P.embedReal u
  if (st.rawQuery scheme x).isSome then
    pure (st.rawOverwrite scheme x v)
  else if #(P.paddedDom (st.rawQuery scheme)) < P.cap then
    st.execRawInsertFresh hcr scheme x v
  else if hsc : 0 < st.sentCount ∧ st.sentCount ≤ P.cap then
    let s_last := P.sentinelKey ⟨st.sentCount - 1, by omega⟩
    st.execRawDeleteMem hcr scheme s_last >>= fun st_del =>
      let st₁ : P.TreeState := { st_del with sentCount := st.sentCount - 1 }
      st₁.execRawInsertFresh hcr scheme x v
  else
    pure st

/-- Randomized external `delete` (no-op if absent, maintaining sentinel padding in
`{cap - 1, cap}`). -/
noncomputable def execDelete (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (u : Fin P.univ) :
    OracleComp P.goodSeedSpec P.TreeState :=
  let x := P.embedReal u
  if !(st.rawQuery scheme x).isSome then
    pure st
  else if P.cap ≤ #(P.paddedDom (st.rawQuery scheme)) then
    st.execRawDeleteMem hcr scheme x
  else if hsc : st.sentCount < P.cap then
    let s_new := P.sentinelKey ⟨st.sentCount, hsc⟩
    st.execRawInsertFresh hcr scheme s_new ⟨0, P.val_pos⟩ >>= fun st_ins =>
      let st₁ : P.TreeState := { st_ins with sentCount := st.sentCount + 1 }
      st₁.execRawDeleteMem hcr scheme x
  else
    pure st

/-- Execute a single `Dynamic.Op P.univ` operation on `st : P.TreeState`. -/
@[expose]
noncomputable def execOp (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) : (o : Dynamic.Op P.univ) →
      OracleComp P.goodSeedSpec (P.TreeState × o.Result)
  | .query u => pure (st, st.query scheme u)
  | .insert u v =>
    if hv : v < P.valBound then
      st.execInsert hcr scheme u ⟨v, hv⟩ >>= fun st' => pure (st', ())
    else
      pure (st, ())
  | .delete u =>
    st.execDelete hcr scheme u >>= fun st' => pure (st', ())

end TreeState

/-- Fold `TreeState.execOp` across a sequence of external dictionary operations, recording the
final `TreeState` and typed observation trace `List (Sigma Dynamic.Op.Result)`. -/
@[expose]
noncomputable def execSteps (P : TreeSchedule) (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)) :
    List (Dynamic.Op P.univ) → P.TreeState →
      OracleComp P.goodSeedSpec
        (P.TreeState × List (Sigma (Dynamic.Op.Result (U := P.univ))))
  | [], st => pure (st, [])
  | o :: ops, st =>
    st.execOp hcr scheme o >>= fun p =>
      P.execSteps hcr scheme ops p.1 >>= fun rest =>
        pure (rest.1, ⟨o, p.2⟩ :: rest.2)

/-- Full randomized `OracleComp` execution from `execInit` across `ops : List (Dynamic.Op P.univ)`.
-/
@[expose]
noncomputable def execHistory (P : TreeSchedule) (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (ops : List (Dynamic.Op P.univ)) :
    OracleComp P.goodSeedSpec
      (P.TreeState × List (Sigma (Dynamic.Op.Result (U := P.univ)))) :=
  P.execInit hcr scheme >>= P.execSteps hcr scheme ops

/-! ## Section 2: Relational `OracleComp` Coupling to `execTruncHistory` -/

private theorem evalWith_ne_zero_mem_support {ι : Type} {spec : OracleSpec ι} {α : Type}
    {h : (q : ι) → PMF (spec q)} {prog : OracleComp spec α} {a : α}
    (hne : OracleComp.evalWith h prog a ≠ 0) : a ∈ prog.support :=
  OracleComp.supportWith_mono (fun _ _ _ => trivial) prog
    ((OracleComp.support_evalWith h prog) ▸ (PMF.mem_support_iff _ a).mpr hne)

/-- Relational invariant coupling a concrete `st : P.TreeState` with its truncated seed assignment
`ts : P.TruncSeeds P.depth` on deterministic padded state `(d, sc)`. -/
private def StateSeedRel {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (d : P.PaddedDict) (sc : ℕ) (st : P.TreeState) (ts : P.TruncSeeds P.depth) : Prop :=
  st.sentCount = sc ∧
    P.truncOfSeeds P.depth st.seeds = ts ∧
    ∃ storeLvl : Fin P.paddedUniv → ℕ, st.WellFormedPadded scheme d storeLvl

private theorem stateSeedRel_withSentCount {P : TreeSchedule}
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {d : P.PaddedDict} {sc : ℕ} {st : P.TreeState} {ts : P.TruncSeeds P.depth}
    (hrel : StateSeedRel scheme d sc st ts) (sc' : ℕ) :
    StateSeedRel scheme d sc' ({ st with sentCount := sc' } : P.TreeState) ts := by
  obtain ⟨_, hts, sl, hwf⟩ := hrel
  exact ⟨rfl, by rw [TreeState.seeds_withSentCount, hts], sl, hwf.withSentCount sc'⟩

private theorem materializeFromTrunc_stateSeedRel {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (d : P.PaddedDict) (sc : ℕ) (ts : P.TruncSeeds P.depth)
    (hg : ts.toSeeds.AllGoodSeeds (P.paddedDom d)) :
    StateSeedRel scheme d sc (P.materializeFromTrunc hcr scheme d sc ts) ts := by
  dsimp only [materializeFromTrunc]
  rw [dite_eq_left hg]
  refine ⟨P.sentCount_buildTreeFromSeeds scheme d sc ts.toSeeds hg, ?_,
    _, P.wellFormedPadded_buildTreeFromSeeds scheme d sc ts.toSeeds hg⟩
  rw [P.seeds_buildTreeFromSeeds, truncOfSeeds_toSeeds]

/-- Monadic cost-and-support coupling between a `TreeState` computation and a `TruncSeeds`
computation. -/
private structure CoupledState {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (d : P.PaddedDict) (sc : ℕ)
    (pt : OracleComp P.goodSeedSpec P.TreeState)
    (ps : OracleComp P.goodSeedSpec (P.TruncSeeds P.depth)) : Prop where
  support_rel : ∀ st ∈ pt.support,
    StateSeedRel scheme d sc st (P.truncOfSeeds P.depth st.seeds)
  bind_cost : ∀ (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q))
    (cost : P.GoodSeedQuery → ℝ≥0∞) {β γ : Type}
    (kt : P.TreeState → OracleComp P.goodSeedSpec β)
    (ks : P.TruncSeeds P.depth → OracleComp P.goodSeedSpec γ),
    (∀ st ts, StateSeedRel scheme d sc st ts →
      OracleComp.expectedCost h cost (kt st) = OracleComp.expectedCost h cost (ks ts)) →
    OracleComp.expectedCost h cost (pt >>= kt) =
      OracleComp.expectedCost h cost (ps >>= ks)

private theorem CoupledState.pure_step {P : TreeSchedule}
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {d : P.PaddedDict} {sc : ℕ} {st' : P.TreeState} {ts : P.TruncSeeds P.depth}
    (hrel : StateSeedRel scheme d sc st' ts) :
    CoupledState scheme d sc (pure st') (pure ts) where
  support_rel st hst := by
    have heq : st = st' := hst
    subst heq
    exact ⟨hrel.1, rfl, hrel.2.2⟩
  bind_cost h cost {_ _} kt ks hagree := by
    rw [pure_bind, pure_bind]
    exact hagree st' ts hrel

private theorem CoupledState.bind {P : TreeSchedule}
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {d₁ d₂ : P.PaddedDict} {sc₁ sc₂ : ℕ}
    {pt₁ : OracleComp P.goodSeedSpec P.TreeState}
    {ps₁ : OracleComp P.goodSeedSpec (P.TruncSeeds P.depth)}
    {ft : P.TreeState → OracleComp P.goodSeedSpec P.TreeState}
    {fs : P.TruncSeeds P.depth → OracleComp P.goodSeedSpec (P.TruncSeeds P.depth)}
    (hc₁ : CoupledState scheme d₁ sc₁ pt₁ ps₁)
    (hc₂ : ∀ st ts, StateSeedRel scheme d₁ sc₁ st ts →
      CoupledState scheme d₂ sc₂ (ft st) (fs ts)) :
    CoupledState scheme d₂ sc₂ (pt₁ >>= ft) (ps₁ >>= fs) where
  support_rel st₂ hst₂ := by
    rw [OracleComp.mem_supportWith_bind_iff] at hst₂
    obtain ⟨st₁, hst₁, hst₂⟩ := hst₂
    exact (hc₂ st₁ _ (hc₁.support_rel st₁ hst₁)).support_rel st₂ hst₂
  bind_cost h cost {_ _} kt ks hagree := by
    rw [bind_assoc, bind_assoc]
    exact hc₁.bind_cost h cost _ _ fun st ts hrel =>
      (hc₂ st ts hrel).bind_cost h cost kt ks hagree

private theorem coupledState_execInit {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)) :
    CoupledState scheme P.initPaddedDict P.cap (P.execInit hcr scheme)
      (P.initTrunc P.depth le_rfl (P.paddedDom P.initPaddedDict)) := by
  have hm := P.matchesExternal_initPaddedDict
  have hS₀ : P.validRootBounds (P.paddedDom P.initPaddedDict) := by
    rw [validRootBounds, P.nLow_zero_eq, P.nHigh_zero_eq]
    exact ⟨hm.card_lo, hm.card_hi⟩
  refine ⟨fun st hst => ?_, fun h cost _ _ kt ks hagree => ?_⟩
  · dsimp only [execInit] at hst
    rw [OracleComp.mem_supportWith_bind_iff] at hst
    obtain ⟨ts, hts, hst_eq⟩ := hst
    have heq : st = P.materializeFromTrunc hcr scheme P.initPaddedDict P.cap ts := hst_eq
    subst heq
    have hg : ts.toSeeds.AllGoodSeeds (P.paddedDom P.initPaddedDict) :=
      (goodTrunc_depth_iff _ ts).mp (mem_support_initTrunc P.depth le_rfl hS₀ hts)
    have hrel := P.materializeFromTrunc_stateSeedRel hcr scheme P.initPaddedDict P.cap ts hg
    exact ⟨hrel.1, rfl, hrel.2.2⟩
  · dsimp only [execInit]
    rw [bind_assoc, OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
    congr 1
    refine tsum_congr fun ts => ?_
    by_cases h0 : OracleComp.evalWith h
        (P.initTrunc P.depth le_rfl (P.paddedDom P.initPaddedDict)) ts = 0
    · rw [h0, zero_mul, zero_mul]
    · rw [pure_bind]
      have hg : ts.toSeeds.AllGoodSeeds (P.paddedDom P.initPaddedDict) :=
        (goodTrunc_depth_iff _ ts).mp
          (mem_support_initTrunc P.depth le_rfl hS₀ (evalWith_ne_zero_mem_support h0))
      rw [hagree _ ts (P.materializeFromTrunc_stateSeedRel hcr scheme P.initPaddedDict P.cap ts hg)]

private theorem coupledState_execRawInsertFresh {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    {d : P.PaddedDict} {sc : ℕ} {st : P.TreeState} {ts : P.TruncSeeds P.depth}
    (hrel : StateSeedRel scheme d sc st ts)
    {x : Fin P.paddedUniv} (hx_fresh : x ∉ P.paddedDom d) (v : Fin P.valBound)
    (pstep : P.PaddedStep)
    (hp_pre : pstep.preSet = P.paddedDom d)
    (hp_post : pstep.postSet = Insert.insert x (P.paddedDom d))
    (hp_key : pstep.key = x) :
    CoupledState scheme (Function.update d x (some v)) sc
      (st.execRawInsertFresh hcr scheme x v)
      (P.runTruncSteps P.depth le_rfl [pstep] ts) := by
  classical
  obtain ⟨hsc, hts, sl, hwf⟩ := hrel
  have hd_eq : st.rawQuery scheme = d := funext (st.rawQuery_eq hwf)
  let S' := Insert.insert x (P.paddedDom d)
  have hcard' : P.validRootBounds S' := by dsimp only [S']; rw [← hp_post]; exact pstep.post_bounds
  have h_wf : ∃ s, st.WellFormedPadded scheme d s ∧ x ∉ P.paddedDom d ∧ P.validRootBounds S' :=
    ⟨sl, hwf, hx_fresh, hcard'⟩
  have ⟨hwf₀, hx₀, hcard₀⟩ := Classical.choose_spec h_wf
  have hdom_upd : P.paddedDom (Function.update d x (some v)) = S' := P.paddedDom_update_some d x v
  dsimp only [TreeState.execRawInsertFresh, runTruncSteps]
  simp only [hd_eq]
  rw [dite_eq_left h_wf]
  by_cases hgood' : st.seeds.AllGoodSeeds S'
  · rw [dite_eq_left hgood']
    have hg_ts : GoodTrunc P.depth le_rfl pstep.postSet ts := by
      rw [hp_post, goodTrunc_depth_iff, ← hts, toSeeds_truncOfSeeds]
      exact hgood'
    rw [stepTrunc_of_goodTrunc_post P.depth le_rfl pstep ts hg_ts, pure_bind]
    exact CoupledState.pure_step
      ⟨(st.sentCount_normalInsertFresh hwf₀ x v hx₀ hgood').trans hsc,
        (congrArg (P.truncOfSeeds P.depth)
          (st.seeds_normalInsertFresh hwf₀ x v hx₀ hgood')).trans hts,
        _, st.wellFormedPadded_normalInsertFresh hwf₀ x v hx₀ hgood'⟩
  · rw [dite_eq_right hgood']
    have hp_eq : P.mkInsertStep (P.paddedDom d) x hwf₀.goodSeeds.1 hcard₀ = pstep :=
      PaddedStep.ext hp_pre.symm hp_post.symm hp_key.symm
    rw [hp_eq, hts]
    refine ⟨fun st' hst' => ?_, fun h cost _ _ kt ks hagree => ?_⟩
    · rw [OracleComp.mem_supportWith_bind_iff] at hst'
      obtain ⟨am, ham, hst'_eq⟩ := hst'
      have heq : st' = P.materializeFromTrunc hcr scheme (Function.update d x (some v))
          st.sentCount am.1 := hst'_eq
      subst heq
      have hg_am : am.1.toSeeds.AllGoodSeeds (P.paddedDom (Function.update d x (some v))) := by
        rw [hdom_upd]; dsimp only [S']; rw [← hp_post]
        exact (goodTrunc_depth_iff _ am.1).mp (mem_support_stepTrunc P.depth le_rfl pstep ts ham).1
      have hrel' := P.materializeFromTrunc_stateSeedRel hcr scheme
        (Function.update d x (some v)) st.sentCount am.1 hg_am
      exact ⟨hrel'.1.trans hsc, rfl, hrel'.2.2⟩
    · rw [bind_assoc, bind_assoc, OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
      congr 1
      refine tsum_congr fun am => ?_
      by_cases h0 : OracleComp.evalWith h (P.stepTrunc P.depth le_rfl pstep ts) am = 0
      · rw [h0, zero_mul, zero_mul]
      · rw [pure_bind, pure_bind]
        have hg_am : am.1.toSeeds.AllGoodSeeds (P.paddedDom (Function.update d x (some v))) := by
          rw [hdom_upd]; dsimp only [S']; rw [← hp_post]
          exact (goodTrunc_depth_iff _ am.1).mp
            (mem_support_stepTrunc P.depth le_rfl pstep ts (evalWith_ne_zero_mem_support h0)).1
        have hrel' := P.materializeFromTrunc_stateSeedRel hcr scheme
          (Function.update d x (some v)) st.sentCount am.1 hg_am
        rw [hsc] at hrel' ⊢
        rw [hagree _ am.1 hrel']

private theorem coupledState_execRawDeleteMem {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    {d : P.PaddedDict} {sc : ℕ} {st : P.TreeState} {ts : P.TruncSeeds P.depth}
    (hrel : StateSeedRel scheme d sc st ts)
    {z : Fin P.paddedUniv} (hz : z ∈ P.paddedDom d)
    (pstep : P.PaddedStep)
    (hp_pre : pstep.preSet = P.paddedDom d)
    (hp_post : pstep.postSet = (P.paddedDom d).erase z)
    (hp_key : pstep.key = z) :
    CoupledState scheme (Function.update d z none) sc
      (st.execRawDeleteMem hcr scheme z)
      (P.runTruncSteps P.depth le_rfl [pstep] ts) := by
  classical
  obtain ⟨hsc, hts, sl, hwf⟩ := hrel
  have hd_eq : st.rawQuery scheme = d := funext (st.rawQuery_eq hwf)
  let S' := (P.paddedDom d).erase z
  have hcard' : P.validRootBounds S' := by dsimp only [S']; rw [← hp_post]; exact pstep.post_bounds
  have h_wf : ∃ s, st.WellFormedPadded scheme d s ∧ z ∈ P.paddedDom d ∧ P.validRootBounds S' :=
    ⟨sl, hwf, hz, hcard'⟩
  have ⟨hwf₀, hz₀, hcard₀⟩ := Classical.choose_spec h_wf
  have hdom_upd : P.paddedDom (Function.update d z none) = S' := P.paddedDom_update_none d z
  dsimp only [TreeState.execRawDeleteMem, runTruncSteps]
  simp only [hd_eq]
  rw [dite_eq_left h_wf]
  by_cases hgood' : st.seeds.AllGoodSeeds S'
  · rw [ite_eq_left hgood']
    have hg_ts : GoodTrunc P.depth le_rfl pstep.postSet ts := by
      rw [hp_post, goodTrunc_depth_iff, ← hts, toSeeds_truncOfSeeds]
      exact hgood'
    rw [stepTrunc_of_goodTrunc_post P.depth le_rfl pstep ts hg_ts, pure_bind]
    obtain ⟨hsc', hsd', sl', hwf'⟩ := TreeState.wellFormedPadded_normalDeleteMem hwf₀ hz₀ hgood'
    exact CoupledState.pure_step
      ⟨hsc'.trans hsc, (congrArg (P.truncOfSeeds P.depth) hsd').trans hts, sl', hwf'⟩
  · rw [ite_eq_right hgood']
    have hp_eq : P.mkDeleteStep (P.paddedDom d) z hwf₀.goodSeeds.1 hcard₀ = pstep :=
      PaddedStep.ext hp_pre.symm hp_post.symm hp_key.symm
    rw [hp_eq, hts]
    refine ⟨fun st' hst' => ?_, fun h cost _ _ kt ks hagree => ?_⟩
    · rw [OracleComp.mem_supportWith_bind_iff] at hst'
      obtain ⟨am, ham, hst'_eq⟩ := hst'
      have heq : st' = P.materializeFromTrunc hcr scheme (Function.update d z none)
          st.sentCount am.1 := hst'_eq
      subst heq
      have hg_am : am.1.toSeeds.AllGoodSeeds (P.paddedDom (Function.update d z none)) := by
        rw [hdom_upd]; dsimp only [S']; rw [← hp_post]
        exact (goodTrunc_depth_iff _ am.1).mp (mem_support_stepTrunc P.depth le_rfl pstep ts ham).1
      have hrel' := P.materializeFromTrunc_stateSeedRel hcr scheme
        (Function.update d z none) st.sentCount am.1 hg_am
      exact ⟨hrel'.1.trans hsc, rfl, hrel'.2.2⟩
    · rw [bind_assoc, bind_assoc, OracleComp.expectedCost_bind, OracleComp.expectedCost_bind]
      congr 1
      refine tsum_congr fun am => ?_
      by_cases h0 : OracleComp.evalWith h (P.stepTrunc P.depth le_rfl pstep ts) am = 0
      · rw [h0, zero_mul, zero_mul]
      · rw [pure_bind, pure_bind]
        have hg_am : am.1.toSeeds.AllGoodSeeds (P.paddedDom (Function.update d z none)) := by
          rw [hdom_upd]; dsimp only [S']; rw [← hp_post]
          exact (goodTrunc_depth_iff _ am.1).mp
            (mem_support_stepTrunc P.depth le_rfl pstep ts (evalWith_ne_zero_mem_support h0)).1
        have hrel' := P.materializeFromTrunc_stateSeedRel hcr scheme
          (Function.update d z none) st.sentCount am.1 hg_am
        rw [hsc] at hrel' ⊢
        rw [hagree _ am.1 hrel']


/-! ## Section 3: External Operation Coupling and Unconditional `Lemma 5.3` -/

private def ChainStepsTo {P : TreeSchedule} :
    Finset (Fin P.paddedUniv) → List P.PaddedStep → Finset (Fin P.paddedUniv) → Prop
  | S, [], S' => S = S'
  | S, st :: sts, S' => st.preSet = S ∧ ChainStepsTo st.postSet sts S'

private theorem ChainStepsTo.toChainSteps {P : TreeSchedule} :
    ∀ {S S' : Finset (Fin P.paddedUniv)} {sts : List P.PaddedStep},
      ChainStepsTo S sts S' → ChainSteps S sts
  | _, _, [], _ => trivial
  | _, _, _ :: _, ⟨hp, hc⟩ => ⟨hp, hc.toChainSteps⟩

private theorem ChainStepsTo.append {P : TreeSchedule} :
    ∀ {S₁ S₂ S₃ : Finset (Fin P.paddedUniv)} {xs ys : List P.PaddedStep},
      ChainStepsTo S₁ xs S₂ → ChainStepsTo S₂ ys S₃ → ChainStepsTo S₁ (xs ++ ys) S₃
  | _, _, _, [], _, rfl, h₂ => h₂
  | _, _, _, _ :: _, _, ⟨hp, h₁⟩, h₂ => ⟨hp, h₁.append h₂⟩

private structure CoupledOut {P : TreeSchedule} {α : Type}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (d : P.PaddedDict) (sc : ℕ) (ret : α)
    (pt : OracleComp P.goodSeedSpec (P.TreeState × α))
    (ps : OracleComp P.goodSeedSpec (P.TruncSeeds P.depth)) : Prop where
  support_rel : ∀ p ∈ pt.support,
    p.2 = ret ∧ StateSeedRel scheme d sc p.1 (P.truncOfSeeds P.depth p.1.seeds)
  bind_cost : ∀ (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q))
    (cost : P.GoodSeedQuery → ℝ≥0∞) {β γ : Type}
    (kt : P.TreeState × α → OracleComp P.goodSeedSpec β)
    (ks : P.TruncSeeds P.depth → OracleComp P.goodSeedSpec γ),
    (∀ st ts, StateSeedRel scheme d sc st ts →
      OracleComp.expectedCost h cost (kt (st, ret)) = OracleComp.expectedCost h cost (ks ts)) →
    OracleComp.expectedCost h cost (pt >>= kt) =
      OracleComp.expectedCost h cost (ps >>= ks)

private theorem CoupledState.attach_ret {P : TreeSchedule} {α : Type}
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {d : P.PaddedDict} {sc : ℕ} (ret : α)
    {pt : OracleComp P.goodSeedSpec P.TreeState}
    {ps : OracleComp P.goodSeedSpec (P.TruncSeeds P.depth)}
    (hc : CoupledState scheme d sc pt ps) :
    CoupledOut scheme d sc ret (pt >>= fun st' => pure (st', ret)) ps where
  support_rel p hp := by
    rw [OracleComp.mem_supportWith_bind_iff] at hp
    obtain ⟨st', hst', hp_eq⟩ := hp
    have heq : p = (st', ret) := hp_eq
    subst heq
    exact ⟨rfl, hc.support_rel st' hst'⟩
  bind_cost h cost {_ _} kt ks hagree := by
    rw [bind_assoc]
    exact hc.bind_cost h cost _ _ fun st ts hrel => by
      rw [pure_bind]
      exact hagree st ts hrel

private theorem exists_coupled_execInsert {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    {d : P.PaddedDict} {sc : ℕ} {dict : Dictionary.State P.univ}
    (hm : P.MatchesExternal d sc dict) (u : Fin P.univ) (v : Fin P.valBound)
    (hcap : u ∈ Dictionary.dom dict ∨ (Dictionary.dom dict).card < P.cap) :
    ∃ (d' : P.PaddedDict) (sc' : ℕ) (sts : List P.PaddedStep),
      sts.length ≤ 2 ∧
      ChainStepsTo (P.paddedDom d) sts (P.paddedDom d') ∧
      P.MatchesExternal d' sc' (Function.update dict u (some v.val)) ∧
      ∀ st ts, StateSeedRel scheme d sc st ts →
        CoupledState scheme d' sc' (st.execInsert hcr scheme u v)
          (P.runTruncSteps P.depth le_rfl sts ts) := by
  let x := P.embedReal u
  have hroot_d : P.validRootBounds (P.paddedDom d) := by
    rw [validRootBounds, P.nLow_zero_eq, P.nHigh_zero_eq]
    exact ⟨hm.card_lo, hm.card_hi⟩
  have hreal_iff : (d x).isSome ↔ u ∈ Dictionary.dom dict := by
    simp only [Dictionary.dom, mem_filter, Finset.mem_univ, true_and, ← hm.real_eq u,
      Option.isSome_map, x]
  by_cases hmem : (d x).isSome
  · have hx_dom : x ∈ P.paddedDom d := (P.mem_paddedDom_iff d x).mpr hmem
    have hdom_eq : P.paddedDom (Function.update d x (some v)) = P.paddedDom d := by
      rw [P.paddedDom_update_some, insert_eq_of_mem hx_dom]
    refine ⟨Function.update d x (some v), sc, [], by simp, hdom_eq.symm, hm.overwrite hmem v,
      fun st ts ⟨hsc, hts, sl, hwfp⟩ => ?_⟩
    have hd_eq : st.rawQuery scheme = d := funext (st.rawQuery_eq hwfp)
    dsimp only [TreeState.execInsert, runTruncSteps]
    rw [hd_eq, ite_eq_left hmem]
    exact CoupledState.pure_step
      ⟨(st.sentCount_rawOverwrite scheme x v).trans hsc,
        (congrArg (P.truncOfSeeds P.depth) (st.seeds_rawOverwrite scheme x v)).trans hts,
        sl, st.wellFormedPadded_rawOverwrite hwfp hx_dom v⟩
  · have hu_not_dom : u ∉ Dictionary.dom dict := mt hreal_iff.mpr hmem
    have hlt_cap : (Dictionary.dom dict).card < P.cap := hcap.resolve_left hu_not_dom
    have hx_fresh : x ∉ P.paddedDom d := mt (P.mem_paddedDom_iff d x).mp hmem
    by_cases hlt_pad : #(P.paddedDom d) < P.cap
    · have hcard' : P.validRootBounds (Insert.insert x (P.paddedDom d)) := by
        rw [validRootBounds, card_insert_of_notMem hx_fresh, P.nLow_zero_eq, P.nHigh_zero_eq]
        have := hm.card_lo; have := P.two_le_cap; omega
      let pstep := P.mkInsertStep (P.paddedDom d) x hroot_d hcard'
      refine ⟨Function.update d x (some v), sc, [pstep], by simp,
        ⟨rfl, (P.paddedDom_update_some d x v).symm⟩,
        hm.insert_fresh_lt hx_fresh hlt_pad v, fun st ts hrel => ?_⟩
      have hd_eq : st.rawQuery scheme = d := funext (st.rawQuery_eq hrel.2.2.choose_spec)
      dsimp only [TreeState.execInsert]
      rw [hd_eq, ite_eq_right hmem, ite_eq_left hlt_pad]
      exact coupledState_execRawInsertFresh hcr scheme hrel hx_fresh v pstep rfl rfl rfl
    · have hcard_d : #(P.paddedDom d) = P.cap := by have := hm.card_hi; omega
      have hsum_d := P.card_paddedDom_eq hm
      have hsc_ok : 0 < sc ∧ sc ≤ P.cap := ⟨by omega, hm.sentCount_le⟩
      let s_last := P.sentinelKey ⟨sc - 1, by omega⟩
      have hs_ge : P.univ ≤ s_last.val := by dsimp only [s_last, sentinelKey]; omega
      have hs_lt : s_last.val < P.univ + sc := by dsimp only [s_last, sentinelKey]; omega
      have hs_mem : s_last ∈ P.paddedDom d := by
        rw [P.mem_paddedDom_iff, hm.sentinel_eq s_last hs_ge, ite_eq_left hs_lt]; rfl
      have hcard_er : P.validRootBounds ((P.paddedDom d).erase s_last) := by
        rw [validRootBounds, card_erase_of_mem hs_mem, hcard_d, P.nLow_zero_eq, P.nHigh_zero_eq]
        exact ⟨le_rfl, by omega⟩
      let d₁ := Function.update d s_last none
      have hdom₁ : P.paddedDom d₁ = (P.paddedDom d).erase s_last := P.paddedDom_update_none d s_last
      have hx_fresh₁ : x ∉ P.paddedDom d₁ := by
        rw [hdom₁, mem_erase]; exact fun h => hx_fresh h.2
      have hcard_ins : P.validRootBounds (Insert.insert x (P.paddedDom d₁)) := by
        rw [validRootBounds, card_insert_of_notMem hx_fresh₁, hdom₁,
          card_erase_of_mem hs_mem, hcard_d, P.nLow_zero_eq, P.nHigh_zero_eq]
        have := P.two_le_cap; omega
      let pstep₁ := P.mkDeleteStep (P.paddedDom d) s_last hroot_d hcard_er
      let pstep₂ := P.mkInsertStep (P.paddedDom d₁) x (hdom₁ ▸ hcard_er) hcard_ins
      refine ⟨Function.update d₁ x (some v), sc - 1, [pstep₁, pstep₂], by simp,
        ⟨rfl, hdom₁, (P.paddedDom_update_some d₁ x v).symm⟩,
        hm.insert_fresh_full hx_fresh hlt_pad hsc_ok v, fun st ts hrel => ?_⟩
      have hsc_st : 0 < st.sentCount ∧ st.sentCount ≤ P.cap := hrel.1.symm ▸ hsc_ok
      have hd_eq : st.rawQuery scheme = d := funext (st.rawQuery_eq hrel.2.2.choose_spec)
      dsimp only [TreeState.execInsert]
      rw [hd_eq, ite_eq_right hmem, ite_eq_right hlt_pad, dite_eq_left hsc_st]
      simp only [hrel.1]
      rw [show ([pstep₁, pstep₂] : List P.PaddedStep) = [pstep₁] ++ [pstep₂] from rfl,
        P.runTruncSteps_append]
      exact (coupledState_execRawDeleteMem hcr scheme hrel hs_mem pstep₁ rfl rfl rfl).bind
        fun st_del ts₁ hrel₁ =>
          coupledState_execRawInsertFresh hcr scheme (stateSeedRel_withSentCount hrel₁ (sc - 1))
            hx_fresh₁ v pstep₂ rfl rfl rfl

private theorem exists_coupled_execDelete {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    {d : P.PaddedDict} {sc : ℕ} {dict : Dictionary.State P.univ}
    (hm : P.MatchesExternal d sc dict) (u : Fin P.univ) :
    ∃ (d' : P.PaddedDict) (sc' : ℕ) (sts : List P.PaddedStep),
      sts.length ≤ 2 ∧
      ChainStepsTo (P.paddedDom d) sts (P.paddedDom d') ∧
      P.MatchesExternal d' sc' (Function.update dict u none) ∧
      ∀ st ts, StateSeedRel scheme d sc st ts →
        CoupledState scheme d' sc' (st.execDelete hcr scheme u)
          (P.runTruncSteps P.depth le_rfl sts ts) := by
  let x := P.embedReal u
  have hroot_d : P.validRootBounds (P.paddedDom d) := by
    rw [validRootBounds, P.nLow_zero_eq, P.nHigh_zero_eq]
    exact ⟨hm.card_lo, hm.card_hi⟩
  by_cases hmem : (d x).isSome
  · have hx_dom : x ∈ P.paddedDom d := (P.mem_paddedDom_iff d x).mpr hmem
    have hu_dom : u ∈ Dictionary.dom dict := by
      simp only [Dictionary.dom, mem_filter, Finset.mem_univ, true_and, ← hm.real_eq u,
        Option.isSome_map]
      exact hmem
    have hdom_pos : 1 ≤ (Dictionary.dom dict).card := Finset.card_pos.mpr ⟨u, hu_dom⟩
    by_cases hge_cap : P.cap ≤ #(P.paddedDom d)
    · have hcard_d : #(P.paddedDom d) = P.cap := by have := hm.card_hi; omega
      have hcard_er : P.validRootBounds ((P.paddedDom d).erase x) := by
        rw [validRootBounds, card_erase_of_mem hx_dom, hcard_d, P.nLow_zero_eq, P.nHigh_zero_eq]
        exact ⟨le_rfl, by omega⟩
      let pstep := P.mkDeleteStep (P.paddedDom d) x hroot_d hcard_er
      refine ⟨Function.update d x none, sc, [pstep], by simp,
        ⟨rfl, (P.paddedDom_update_none d x).symm⟩,
        hm.delete_ge hx_dom hge_cap, fun st ts hrel => ?_⟩
      have hd_eq : st.rawQuery scheme = d := funext (st.rawQuery_eq hrel.2.2.choose_spec)
      dsimp only [TreeState.execDelete]
      rw [hd_eq, ite_eq_right (by simp [x, hmem]), ite_eq_left hge_cap]
      exact coupledState_execRawDeleteMem hcr scheme hrel hx_dom pstep rfl rfl rfl
    · have hcard_d : #(P.paddedDom d) = P.cap - 1 := by have := hm.card_lo; omega
      have hsum_d := P.card_paddedDom_eq hm
      have hsc_lt : sc < P.cap := by omega
      let s_new := P.sentinelKey ⟨sc, hsc_lt⟩
      have hs_ge : P.univ ≤ s_new.val := by dsimp only [s_new, sentinelKey]; omega
      have hs_not_lt : ¬ s_new.val < P.univ + sc := by dsimp only [s_new, sentinelKey]; omega
      have hs_fresh : s_new ∉ P.paddedDom d := by
        rw [P.mem_paddedDom_iff, hm.sentinel_eq s_new hs_ge, ite_eq_right hs_not_lt]; simp
      have hcard_ins : P.validRootBounds (Insert.insert s_new (P.paddedDom d)) := by
        rw [validRootBounds, card_insert_of_notMem hs_fresh, hcard_d,
          P.nLow_zero_eq, P.nHigh_zero_eq]
        have := P.two_le_cap; omega
      let d₁ := Function.update d s_new (some ⟨0, P.val_pos⟩)
      have hdom₁ : P.paddedDom d₁ = Insert.insert s_new (P.paddedDom d) :=
        P.paddedDom_update_some d s_new ⟨0, P.val_pos⟩
      have hx_dom₁ : x ∈ P.paddedDom d₁ := by rw [hdom₁, mem_insert]; exact Or.inr hx_dom
      have hcard_er : P.validRootBounds ((P.paddedDom d₁).erase x) := by
        rw [validRootBounds, card_erase_of_mem hx_dom₁, hdom₁,
          card_insert_of_notMem hs_fresh, hcard_d, P.nLow_zero_eq, P.nHigh_zero_eq]
        have := P.two_le_cap; omega
      let pstep₁ := P.mkInsertStep (P.paddedDom d) s_new hroot_d hcard_ins
      let pstep₂ := P.mkDeleteStep (P.paddedDom d₁) x (hdom₁ ▸ hcard_ins) hcard_er
      refine ⟨Function.update d₁ x none, sc + 1, [pstep₁, pstep₂], by simp,
        ⟨rfl, hdom₁, (P.paddedDom_update_none d₁ x).symm⟩,
        hm.delete_lt hx_dom hge_cap hsc_lt, fun st ts hrel => ?_⟩
      have hsc_st : st.sentCount < P.cap := hrel.1.symm ▸ hsc_lt
      have hd_eq : st.rawQuery scheme = d := funext (st.rawQuery_eq hrel.2.2.choose_spec)
      dsimp only [TreeState.execDelete]
      rw [hd_eq, ite_eq_right (by simp [x, hmem]), ite_eq_right hge_cap, dite_eq_left hsc_st]
      simp only [hrel.1]
      rw [show ([pstep₁, pstep₂] : List P.PaddedStep) = [pstep₁] ++ [pstep₂] from rfl,
        P.runTruncSteps_append]
      exact (coupledState_execRawInsertFresh hcr scheme hrel hs_fresh ⟨0, P.val_pos⟩
          pstep₁ rfl rfl rfl).bind fun st_ins ts₁ hrel₁ =>
        coupledState_execRawDeleteMem hcr scheme (stateSeedRel_withSentCount hrel₁ (sc + 1))
          hx_dom₁ pstep₂ rfl rfl rfl
  · have hdu_none : dict u = none := by
      rw [← hm.real_eq u]
      rcases hd_u : d x with _ | w
      · rfl
      · simp [x, hd_u] at hmem
    have hupd_eq : Function.update dict u none = dict := by
      ext u'; by_cases hu : u' = u
      · subst hu; rw [Function.update_self, hdu_none]
      · rw [Function.update_of_ne hu]
    refine ⟨d, sc, [], by simp, rfl, hupd_eq.symm ▸ hm, fun st ts hrel => ?_⟩
    have hd_eq : st.rawQuery scheme = d := funext (st.rawQuery_eq hrel.2.2.choose_spec)
    dsimp only [TreeState.execDelete, runTruncSteps]
    rw [hd_eq, ite_eq_left (by simp [x, hmem])]
    exact CoupledState.pure_step hrel

private theorem exists_coupled_execOp {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    {d : P.PaddedDict} {sc : ℕ} {dict : Dictionary.State P.univ}
    (hm : P.MatchesExternal d sc dict) (o : Dynamic.Op P.univ)
    (hval : (Dynamic.spec P.univ P.valBound P.cap).valid dict o) :
    ∃ (d' : P.PaddedDict) (sc' : ℕ) (sts : List P.PaddedStep),
      sts.length ≤ 2 ∧
      ChainStepsTo (P.paddedDom d) sts (P.paddedDom d') ∧
      P.MatchesExternal d' sc' ((Dynamic.spec P.univ P.valBound P.cap).stepFn dict o).1 ∧
      ∀ st ts, StateSeedRel scheme d sc st ts →
        CoupledOut scheme d' sc' ((Dynamic.spec P.univ P.valBound P.cap).stepFn dict o).2
          (st.execOp hcr scheme o) (P.runTruncSteps P.depth le_rfl sts ts) := by
  cases o with
  | query u =>
    refine ⟨d, sc, [], by simp, rfl, hm, fun st ts hrel => ?_⟩
    obtain ⟨hsc, hts, sl, hwfp⟩ := hrel
    have hwf : st.WellFormed scheme dict := ⟨d, sl, hsc.symm ▸ hm, hwfp⟩
    have hq : st.query scheme u = dict u := TreeState.query_eq_apply hwf u
    dsimp only [TreeState.execOp, runTruncSteps, Dynamic.spec, StateTransitionSpec.stepFn,
      StateTransitionSpec.ofFn, Dynamic.step]
    rw [hq, ← pure_bind st fun st' => pure (st', dict u)]
    exact (CoupledState.pure_step ⟨hsc, hts, sl, hwfp⟩).attach_ret (dict u)
  | insert u v =>
    dsimp only [Dynamic.spec, StateTransitionSpec.ofFn, Dynamic.valid] at hval
    obtain ⟨hcap_raw, hv⟩ := hval
    have hcap : u ∈ Dictionary.dom dict ∨ (Dictionary.dom dict).card < P.cap :=
      hcap_raw.elim Or.inr fun hs => Or.inl (Dictionary.mem_dom_iff_isSome.mpr hs)
    obtain ⟨d', sc', sts, hlen, hch, hm', hc⟩ :=
      exists_coupled_execInsert hcr scheme hm u ⟨v, hv⟩ hcap
    refine ⟨d', sc', sts, hlen, hch, hm', fun st ts hrel => ?_⟩
    dsimp only [TreeState.execOp, Dynamic.spec, StateTransitionSpec.stepFn,
      StateTransitionSpec.ofFn, Dynamic.step]
    rw [dite_eq_left hv]
    exact (hc st ts hrel).attach_ret ()
  | delete u =>
    obtain ⟨d', sc', sts, hlen, hch, hm', hc⟩ := exists_coupled_execDelete hcr scheme hm u
    refine ⟨d', sc', sts, hlen, hch, hm', fun st ts hrel => ?_⟩
    dsimp only [TreeState.execOp, Dynamic.spec, StateTransitionSpec.stepFn,
      StateTransitionSpec.ofFn, Dynamic.step]
    exact (hc st ts hrel).attach_ret ()

private theorem exists_coupled_execSteps {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)) :
    ∀ (ops : List (Dynamic.Op P.univ)) {d : P.PaddedDict} {sc : ℕ}
      {dict : Dictionary.State P.univ},
      P.MatchesExternal d sc dict →
      (Dynamic.spec P.univ P.valBound P.cap).ValidHistory dict ops →
      ∃ (d' : P.PaddedDict) (sc' : ℕ) (sts : List P.PaddedStep),
        sts.length ≤ 2 * ops.length ∧
        ChainStepsTo (P.paddedDom d) sts (P.paddedDom d') ∧
        P.MatchesExternal d' sc' ((Dynamic.spec P.univ P.valBound P.cap).run dict ops).1 ∧
        ∀ st ts, StateSeedRel scheme d sc st ts →
          CoupledOut scheme d' sc' ((Dynamic.spec P.univ P.valBound P.cap).run dict ops).2
            (P.execSteps hcr scheme ops st) (P.runTruncSteps P.depth le_rfl sts ts)
  | [], d, sc, dict, hm, _ =>
    ⟨d, sc, [], by simp, rfl, hm, fun st ts hrel => by
      dsimp only [execSteps, StateTransitionSpec.run, runTruncSteps]
      rw [← pure_bind st fun st' =>
        pure (st', ([] : List (Sigma (Dynamic.Op.Result (U := P.univ)))))]
      exact (CoupledState.pure_step hrel).attach_ret []⟩
  | o :: ops, d, sc, dict, hm, ⟨hval, hvh⟩ => by
    obtain ⟨d₁, sc₁, sts₁, hlen₁, hch₁, hm₁, hc₁⟩ :=
      exists_coupled_execOp hcr scheme hm o hval
    obtain ⟨d₂, sc₂, sts₂, hlen₂, hch₂, hm₂, hc₂⟩ :=
      exists_coupled_execSteps hcr scheme ops hm₁ hvh
    refine ⟨d₂, sc₂, sts₁ ++ sts₂, by rw [List.length_append, List.length_cons]; omega,
      hch₁.append hch₂, hm₂, fun st ts hrel => ?_⟩
    dsimp only [execSteps, StateTransitionSpec.run]
    rw [P.runTruncSteps_append]
    refine ⟨fun q hq => ?_, fun h cost {_ _} kt ks hagree => ?_⟩
    · rw [OracleComp.mem_supportWith_bind_iff] at hq
      obtain ⟨p, hp, hq⟩ := hq
      rw [OracleComp.mem_supportWith_bind_iff] at hq
      obtain ⟨rest, hrest, hq_eq⟩ := hq
      obtain ⟨hp_ret, hp_rel⟩ := (hc₁ st ts hrel).support_rel p hp
      obtain ⟨hr_ret, hr_rel⟩ := (hc₂ p.1 _ hp_rel).support_rel rest hrest
      have heq : q = (rest.1, ⟨o, p.2⟩ :: rest.2) := hq_eq
      subst heq
      rw [hp_ret, hr_ret]
      exact ⟨rfl, hr_rel⟩
    · rw [bind_assoc, bind_assoc]
      refine (hc₁ st ts hrel).bind_cost h cost _ _ fun st₁ ts₁ hrel₁ => ?_
      rw [bind_assoc]
      refine (hc₂ st₁ ts₁ hrel₁).bind_cost h cost _ _ fun st₂ ts₂ hrel₂ => ?_
      rw [pure_bind]
      exact hagree st₂ ts₂ hrel₂

/-- **End-to-end functional correctness of `execHistory` on `.support`**:
for any admissible external history `ops`, every supported outcome `(st', trace)` of `execHistory`
satisfies `st'.WellFormed` for the final `Dynamic.spec` state and produces the exact `Dynamic.spec`
observation trace. -/
theorem mem_support_execHistory {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    {ops : List (Dynamic.Op P.univ)}
    (hvh : (Dynamic.spec P.univ P.valBound P.cap).ValidHistory (Dictionary.empty P.univ) ops)
    {out : P.TreeState × List (Sigma (Dynamic.Op.Result (U := P.univ)))}
    (hout : out ∈ (P.execHistory hcr scheme ops).support) :
    out.1.WellFormed scheme
        ((Dynamic.spec P.univ P.valBound P.cap).run (Dictionary.empty P.univ) ops).1 ∧
      out.2 = ((Dynamic.spec P.univ P.valBound P.cap).run (Dictionary.empty P.univ) ops).2 := by
  dsimp only [execHistory] at hout
  rw [OracleComp.mem_supportWith_bind_iff] at hout
  obtain ⟨st₀, hst₀, hout⟩ := hout
  have hrel₀ := (coupledState_execInit hcr scheme).support_rel st₀ hst₀
  obtain ⟨d', sc', _, _, _, hm', hc⟩ :=
    exists_coupled_execSteps hcr scheme ops P.matchesExternal_initPaddedDict hvh
  obtain ⟨hret, hsc', _, sl', hwfp'⟩ := (hc st₀ _ hrel₀).support_rel out hout
  exact ⟨⟨d', sl', hsc'.symm ▸ hm', hwfp'⟩, hret⟩

/-- **Exact `expectedCost` coupling between `execHistory` and `execSeedSteps`**:
any admissible external history `ops` of length `M` induces a deterministic chain `sts` of at most
`2 * M` single-key `PaddedStep`s such that `execHistory` and `execSeedSteps` have identical
`expectedCost` under **every** oracle interpretation `h` and query cost function `cost`. -/
theorem expectedCost_execHistory_eq_execSeedSteps {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    {ops : List (Dynamic.Op P.univ)}
    (hvh : (Dynamic.spec P.univ P.valBound P.cap).ValidHistory (Dictionary.empty P.univ) ops) :
    ∃ sts : List P.PaddedStep,
      sts.length ≤ 2 * ops.length ∧
      ChainSteps (P.paddedDom P.initPaddedDict) sts ∧
      ∀ (h : (q : P.GoodSeedQuery) → PMF (P.goodSeedSpec q))
        (cost : P.GoodSeedQuery → ℝ≥0∞),
        OracleComp.expectedCost h cost (P.execHistory hcr scheme ops) =
          OracleComp.expectedCost h cost
            (P.execSeedSteps (P.paddedDom P.initPaddedDict) sts) := by
  obtain ⟨d', sc', sts, hlen, hch, _, hc⟩ :=
    exists_coupled_execSteps hcr scheme ops P.matchesExternal_initPaddedDict hvh
  refine ⟨sts, hlen, hch.toChainSteps, fun h cost => ?_⟩
  dsimp only [execHistory, execSeedSteps, execTruncHistory]
  have hlhs : P.execInit hcr scheme >>= P.execSteps hcr scheme ops =
      P.execInit hcr scheme >>= fun st => P.execSteps hcr scheme ops st >>= pure := by
    simp only [bind_pure]
  rw [hlhs, bind_assoc (P.initTrunc P.depth le_rfl _)]
  refine (coupledState_execInit hcr scheme).bind_cost h cost _ _ fun st₀ ts₀ hrel₀ => ?_
  exact (hc st₀ ts₀ hrel₀).bind_cost h cost pure (fun ts => pure ts.toSeeds) fun _ _ _ => by
    simp only [OracleComp.expectedCost_pure]

/-- **Unconditional `Lemma 5.3` over external `Dynamic.Op` histories**
(`[LiLiangYuZhou2024, Section 5.5]`):
across initialization and any admissible sequence `ops` of `M = ops.length` external dictionary
operations (`query`, `insert` with overwrite, and `delete`), the total expected rehashing work of
`execHistory` under `goodSeedLaw hcr` is at most `14 * (depth + 1) * (cap + 2 * M)`. -/
theorem expectedCost_execHistory_le {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    {ops : List (Dynamic.Op P.univ)}
    (hvh : (Dynamic.spec P.univ P.valBound P.cap).ValidHistory (Dictionary.empty P.univ) ops) :
    OracleComp.expectedCost (P.goodSeedLaw hcr) P.rehashWorkCost
        (P.execHistory hcr scheme ops) ≤
      ENNReal.ofReal (14 * ((P.depth + 1 : ℕ) : ℝ) * ((P.cap + 2 * ops.length : ℕ) : ℝ)) := by
  obtain ⟨sts, hlen, hchain, hcost_eq⟩ := expectedCost_execHistory_eq_execSeedSteps hcr scheme hvh
  have hm := P.matchesExternal_initPaddedDict
  have hS₀ : P.validRootBounds (P.paddedDom P.initPaddedDict) := by
    rw [validRootBounds, P.nLow_zero_eq, P.nHigh_zero_eq]
    exact ⟨hm.card_lo, hm.card_hi⟩
  rw [hcost_eq]
  refine (P.expectedCost_execSeedSteps_le hcr hS₀ hchain).trans (ENNReal.ofReal_le_ofReal ?_)
  have hcap_le : ((P.cap + sts.length : ℕ) : ℝ) ≤ ((P.cap + 2 * ops.length : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_le_add_left hlen P.cap
  gcongr

end TreeSchedule

/-- **Unconditional `Lemma 5.3` across `ValidRegime` (`[LiLiangYuZhou2024, Section 5.5]`)**:
for any admissible sequence `ops` of `M = ops.length` external dynamic dictionary operations
starting from `Dictionary.empty U`, the total expected rehashing work of `canonicalSchedule h`
across initialization and all `M` operations is `O((n + M) * Nat.logStar n)`, bounded explicitly by
`84 * (n + ops.length) * Nat.logStar n`. -/
theorem canonicalSchedule_expectedCost_execHistory_le
    {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max)
    (scheme : DynamicMatching.Scheme
      (2 ^ (canonicalSchedule h).idBits (canonicalSchedule h).depth)
      ((canonicalSchedule h).nLow (canonicalSchedule h).depth))
    {ops : List (Dynamic.Op U)}
    (hvh : (Dynamic.spec U V n).ValidHistory (Dictionary.empty U) ops) :
    OracleComp.expectedCost
        ((canonicalSchedule h).goodSeedLaw (canonicalSchedule_concentrationReady h))
        (canonicalSchedule h).rehashWorkCost
        ((canonicalSchedule h).execHistory (canonicalSchedule_concentrationReady h) scheme ops) ≤
      ENNReal.ofReal (84 * ((n + ops.length : ℕ) : ℝ) * (Nat.logStar n : ℝ)) := by
  have hgen := (canonicalSchedule h).expectedCost_execHistory_le
    (canonicalSchedule_concentrationReady h) scheme hvh
  refine hgen.trans (ENNReal.ofReal_le_ofReal ?_)
  have hdepth : (((canonicalSchedule h).depth + 1 : ℕ) : ℝ) ≤ 3 * (Nat.logStar n : ℝ) := by
    exact_mod_cast h.treeDepth_add_one_le_three_mul_logStar
  have hcap : (canonicalSchedule h).cap = n := rfl
  rw [hcap]
  have hlen : ((n + 2 * ops.length : ℕ) : ℝ) ≤ 2 * ((n + ops.length : ℕ) : ℝ) := by
    have hnat : n + 2 * ops.length ≤ 2 * (n + ops.length) := by omega
    exact_mod_cast hnat
  have hpos1 : (0 : ℝ) ≤ ((n + 2 * ops.length : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpos2 : (0 : ℝ) ≤ 3 * (Nat.logStar n : ℝ) := by positivity
  have hmul := mul_le_mul hdepth hlen hpos1 hpos2
  calc 14 * (((canonicalSchedule h).depth + 1 : ℕ) : ℝ) * ((n + 2 * ops.length : ℕ) : ℝ)
      = 14 * ((((canonicalSchedule h).depth + 1 : ℕ) : ℝ) * ((n + 2 * ops.length : ℕ) : ℝ)) := by
        ring
    _ ≤ 14 * ((3 * (Nat.logStar n : ℝ)) * (2 * ((n + ops.length : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = 84 * ((n + ops.length : ℕ) : ℝ) * (Nat.logStar n : ℝ) := by ring

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
