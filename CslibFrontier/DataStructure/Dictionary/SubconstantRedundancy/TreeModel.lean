/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.Params
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.StorageNode
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.RehashBounds
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeRehash
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Pure Multi-Level Subconstant-Redundancy Dictionary Tree Model

This module serves as the top-level entry point for the pure multi-level dictionary tree of
Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou, *Dynamic Dictionary with Subconstant
Wasted Bits per Key* ([LiLiangYuZhou2024, Section 5, Sections 5.1–5.6];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 25–36 / printed pp. 24–35).

It publicly re-exports the parameter schedule and `infoBits + O(R)` bit budget (`Params.lean`),
pure node-level storage structures and Section 5.6 metadata separation (`StorageNode.lean`),
single-node survival (`Claim 5.4`, PDF p. 35 / printed p. 34) and multi-level expected rehashing
work (`Lemma 5.3`, PDF pp. 34–35 / printed pp. 33–34) (`RehashBounds.lean`), sentinel-padded
routing (`TreeRouting.lean`), tree invariants and Section 5.6 DFS subtree metadata
(`TreeCore.lean`), root-to-leaf `query` and `rawOverwrite` (`TreeQuery.lean`), normal-path
insertion (`TreeInsert.lean`), `Algorithm 3` (`deleteAndGetQuotient`, PDF p. 31 / printed p. 30,
`TreeDelete.lean`), and `Algorithm 4` (`rehashSubtree`, PDF p. 34 / printed p. 33,
`TreeRehash.lean`).

In addition, this file provides:
1. Internal single-key padded updates `rawInsertFresh` and `rawDeleteMem` combining the normal
   `O(depth)` path with localized subtree seed repair (`exists_allGoodSeeds_localized`).
2. The external dictionary interface `TreeSchedule.initTree`, `TreeState.insert`, and
   `TreeState.delete` maintaining sentinel padding (`|S_padded| ∈ {cap - 1, cap}`, `Section 4,
   Footnote 5`, PDF p. 12 / printed p. 11; `Section 5`, PDF p. 26 / printed p. 25) and satisfying
   the exact `Dictionary.State` `Function.update` laws (`query_initTree`, `query_insert`,
   `query_delete`).
3. The trajectory bridge `primSetAt_validPrimIdSeq` connecting multi-step update trajectories
   without strict-ancestor rehashes directly to `RehashBounds.ValidPrimIdSeq`, `Claim 5.4`, and
   `Lemma 5.3`.

## Formalization adaptations and explicit scope boundaries

* **Clamped redundancy (`effRedundancy`)**: clamps `R` internally to
  `min R (max 1 (n / max 256 (2 ^ log* n)))` (`Section 5`, PDF p. 26 / printed p. 25) so inverse
  redundancy `r ≥ max 256 (2 ^ log* n)` holds across all `n / log₂ ^ 0.1 n ≤ R ≤ n` without
  inflating `thresholdN`.
* **Small-node child-router regime switch (`NodeSeeds.lean`)**: nodes with
  `nFloor ℓ ≥ FeistelPerm.childRouterThreshold 100 2` use `FeistelPerm.ChildRouterSeed`
  (`DoubleTabulation`), while deeper nodes below `childRouterThreshold 100 2` switch to exact
  `(2 * m)`-wise `FeistelPerm.trinomialPolyHash` (`m = childRouterHalfInd (nFloor ℓ) = O(1)`,
  adapting `[LiLiangYuZhou2024, Sections 5.1 & 5.4, Claim B.2]`, PDF pp. 27, 32–33, 46 /
  printed pp. 26, 31–32, 45).
* **Out of scope**: Word-RAM `Memory.Prog` compilation and lookup-table realization, Section 4
  small-parameter variable-length adapter trees (`R < n / log₂ ^ 0.1 n`), strong history
  independence, dynamic capacity resizing in `|S|`, and super-polynomial key universes
  (`U > n ^ (1 + α_max)`).

## Main definitions

* `TreeSchedule.TreeState.rawInsertFresh`, `TreeSchedule.TreeState.rawDeleteMem`: internal padded
  fresh insertion and member deletion with localized seed repair.
* `TreeSchedule.initTree`, `TreeSchedule.TreeState.insert`, `TreeSchedule.TreeState.delete`:
  external dictionary initialization, insertion, and deletion.

## Main results

* `TreeSchedule.wellFormed_initTree`, `TreeSchedule.query_initTree`: initialization correctness.
* `TreeSchedule.TreeState.wellFormed_insert`, `TreeSchedule.TreeState.query_insert`,
  `TreeSchedule.TreeState.wellFormed_delete`, `TreeSchedule.TreeState.query_delete`: invariant
  preservation and `Function.update` lookup specifications.
* `TreeSchedule.SeedAssignment.primSetAt_validPrimIdSeq`,
  `TreeSchedule.SeedAssignment.prob_survives_window_of_ancestorFree`: trajectory bridge to
  `Claim 5.4` and `Lemma 5.3`.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.Probability
open Finset

namespace TreeSchedule

/-! ## Section 1: Internal padded updates with localized subtree seed repair -/

namespace TreeState

variable {P : TreeSchedule}

private def hasBadSeedOn (seeds : P.SeedAssignment) (S' : Finset (Fin P.paddedUniv))
    (ℓ : ℕ) : Prop :=
  ∃ hℓ : ℓ ≤ P.depth, ∃ w : Fin (P.numNodes ℓ),
    ¬ P.IsGoodNodeSeed ℓ (seeds.seed ℓ hℓ w) (seeds.primSetAt S' ℓ hℓ w)

open scoped Classical in
private noncomputable def repairBadSeedsTree (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (seeds : P.SeedAssignment) (S_cur : Finset (Fin P.paddedUniv))
    (d' : P.PaddedDict) (sentCount : ℕ) (z : Fin P.paddedUniv)
    (hgood : seeds.AllGoodSeeds S_cur)
    (hcard' : P.nLow 0 ≤ #(P.paddedDom d') ∧ #(P.paddedDom d') ≤ P.nHigh 0)
    (hdiff_z : ∀ y, (y ∈ P.paddedDom d' ↔ y ∈ S_cur) ∨ y = z)
    (h_bad : ∃ ℓ, hasBadSeedOn seeds (P.paddedDom d') ℓ) : P.TreeState :=
  let ℓ₀ := Nat.find h_bad
  have hℓ₀ : ℓ₀ ≤ P.depth := (Nat.find_spec h_bad).1
  let u₀ := seeds.nodeAt ℓ₀ hℓ₀ z
  have hdiff : ∀ y, (y ∈ P.paddedDom d' ↔ y ∈ S_cur) ∨ seeds.nodeAt ℓ₀ hℓ₀ y = u₀ := fun y =>
    (hdiff_z y).elim Or.inl fun hy => Or.inr (congrArg (seeds.nodeAt ℓ₀ hℓ₀) hy)
  have hbelow : ∀ (j : ℕ) (hj : j < ℓ₀) (w : Fin (P.numNodes j)),
      P.IsGoodNodeSeed j (seeds.seed j (hj.le.trans hℓ₀) w)
        (seeds.primSetAt (P.paddedDom d') j (hj.le.trans hℓ₀) w) := fun j hj w => by
    by_contra hnot; exact Nat.find_min h_bad hj ⟨hj.le.trans hℓ₀, w, hnot⟩
  let hex := exists_allGoodSeeds_localized hcr seeds hgood hcard' hℓ₀ u₀ hdiff hbelow
  P.buildTreeFromSeeds scheme d' sentCount (Classical.choose hex) (Classical.choose_spec hex).2

open scoped Classical in
private theorem repairBadSeedsTree_spec (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (seeds : P.SeedAssignment) (S_cur : Finset (Fin P.paddedUniv))
    (d' : P.PaddedDict) (sentCount : ℕ) (z : Fin P.paddedUniv)
    (hgood : seeds.AllGoodSeeds S_cur)
    (hcard' : P.nLow 0 ≤ #(P.paddedDom d') ∧ #(P.paddedDom d') ≤ P.nHigh 0)
    (hdiff_z : ∀ y, (y ∈ P.paddedDom d' ↔ y ∈ S_cur) ∨ y = z)
    (h_bad : ∃ ℓ, hasBadSeedOn seeds (P.paddedDom d') ℓ) :
    let st' := repairBadSeedsTree hcr scheme seeds S_cur d' sentCount z hgood hcard' hdiff_z h_bad
    st'.sentCount = sentCount ∧
    (∃ (ℓ₀ : ℕ) (hℓ₀ : ℓ₀ ≤ P.depth),
      ¬ P.IsGoodNodeSeed ℓ₀ (seeds.seed ℓ₀ hℓ₀ (seeds.nodeAt ℓ₀ hℓ₀ z))
        (seeds.primSetAt (P.paddedDom d') ℓ₀ hℓ₀ (seeds.nodeAt ℓ₀ hℓ₀ z)) ∧
      ∀ (j : ℕ) (hj : j ≤ P.depth) (w : Fin (P.numNodes j)),
        ¬ P.InSubtree ℓ₀ (seeds.nodeAt ℓ₀ hℓ₀ z) j w →
          st'.seeds.seed j hj w = seeds.seed j hj w) ∧
    ∃ storeLvl' : Fin P.paddedUniv → ℕ, st'.WellFormedPadded scheme d' storeLvl' := by
  dsimp only [repairBadSeedsTree]
  let ℓ₀ := Nat.find h_bad
  obtain ⟨hℓ₀, w_bad, hw_bad⟩ := Nat.find_spec h_bad
  let u₀ := seeds.nodeAt ℓ₀ hℓ₀ z
  have hdiff : ∀ y, (y ∈ P.paddedDom d' ↔ y ∈ S_cur) ∨ seeds.nodeAt ℓ₀ hℓ₀ y = u₀ := fun y =>
    (hdiff_z y).elim Or.inl fun hy => Or.inr (congrArg (seeds.nodeAt ℓ₀ hℓ₀) hy)
  have hbelow : ∀ (j : ℕ) (hj : j < ℓ₀) (w : Fin (P.numNodes j)),
      P.IsGoodNodeSeed j (seeds.seed j (hj.le.trans hℓ₀) w)
        (seeds.primSetAt (P.paddedDom d') j (hj.le.trans hℓ₀) w) := fun j hj w => by
    by_contra hnot; exact Nat.find_min h_bad hj ⟨hj.le.trans hℓ₀, w, hnot⟩
  have h_not_good : ¬ P.IsGoodNodeSeed ℓ₀ (seeds.seed ℓ₀ hℓ₀ u₀)
      (seeds.primSetAt (P.paddedDom d') ℓ₀ hℓ₀ u₀) := by
    by_cases hwz : w_bad = u₀
    · exact hwz ▸ hw_bad
    · have hact_eq : seeds.activeAt (P.paddedDom d') ℓ₀ hℓ₀ w_bad =
          seeds.activeAt S_cur ℓ₀ hℓ₀ w_bad := by
        ext y
        simp only [SeedAssignment.mem_activeAt_iff]
        rcases hdiff_z y with hiff | rfl
        · exact and_congr_left' hiff
        · exact ⟨fun ⟨_, hn⟩ => False.elim (hwz hn.symm),
            fun ⟨_, hn⟩ => False.elim (hwz hn.symm)⟩
      have hp_eq : seeds.primSetAt (P.paddedDom d') ℓ₀ hℓ₀ w_bad =
          seeds.primSetAt S_cur ℓ₀ hℓ₀ w_bad := by
        dsimp only [SeedAssignment.primSetAt]; rw [hact_eq]
      exact False.elim (hw_bad (hp_eq ▸ hgood.2 ℓ₀ hℓ₀ w_bad))
  refine ⟨by simp, ⟨ℓ₀, hℓ₀, h_not_good, fun j hj w hnot => ?_⟩, _,
    P.wellFormedPadded_buildTreeFromSeeds scheme d' sentCount _ _⟩
  rw [P.seeds_buildTreeFromSeeds]
  exact (Classical.choose_spec
    (exists_allGoodSeeds_localized hcr seeds hgood hcard' hℓ₀ u₀ hdiff hbelow)).1 j hj w hnot

open scoped Classical in
/-- Internal fresh-key insertion on `st` (`x ∉ paddedDom d`, `#S' ∈ [nLow 0, nHigh 0]`): runs
`normalInsertFresh` when `st.seeds` stays good on `Insert.insert x S`, and otherwise resamples only
the subtree rooted at the highest failing node `(ℓ₀, nodeAt ℓ₀ x)`. -/
noncomputable def rawInsertFresh (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (x : Fin P.paddedUniv) (v : Fin P.valBound) : P.TreeState :=
  let d_cur : P.PaddedDict := st.rawQuery scheme
  let S_cur := P.paddedDom d_cur
  let d' := Function.update d_cur x (some v)
  let S' := P.paddedDom d'
  if h_norm : ∃ storeLvl, st.WellFormedPadded scheme d_cur storeLvl ∧
      x ∉ S_cur ∧ st.seeds.AllGoodSeeds (Insert.insert x S_cur) then
    let spec := Classical.choose_spec h_norm
    st.normalInsertFresh spec.1 x v spec.2.1 spec.2.2
  else if h_pre : st.seeds.AllGoodSeeds S_cur ∧ (P.nLow 0 ≤ #S' ∧ #S' ≤ P.nHigh 0) then
    if h_bad : ∃ ℓ, hasBadSeedOn st.seeds S' ℓ then
      repairBadSeedsTree hcr scheme st.seeds S_cur d' st.sentCount x h_pre.1 h_pre.2
        (fun y => if hyx : y = x then Or.inr hyx else Or.inl (by simp [d', S_cur, hyx])) h_bad
    else
      have hgood' : st.seeds.AllGoodSeeds S' :=
        ⟨h_pre.2, fun ℓ hℓ w => by
          by_contra hnot; exact h_bad ⟨ℓ, hℓ, w, hnot⟩⟩
      P.buildTreeFromSeeds scheme d' st.sentCount st.seeds hgood'
  else st

open scoped Classical in
theorem wellFormedPadded_rawInsertFresh (hcr : P.ConcentrationReady)
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {x : Fin P.paddedUniv} (hx_fresh : x ∉ P.paddedDom d) (v : Fin P.valBound)
    (hcard' : P.nLow 0 ≤ #(Insert.insert x (P.paddedDom d)) ∧
      #(Insert.insert x (P.paddedDom d)) ≤ P.nHigh 0) :
    let st' := st.rawInsertFresh hcr scheme x v
    st'.sentCount = st.sentCount ∧
    (st'.seeds = st.seeds ∨
      ∃ (ℓ₀ : ℕ) (hℓ₀ : ℓ₀ ≤ P.depth),
        ¬ P.IsGoodNodeSeed ℓ₀ (st.seeds.seed ℓ₀ hℓ₀ (st.seeds.nodeAt ℓ₀ hℓ₀ x))
          (st.seeds.primSetAt (Insert.insert x (P.paddedDom d)) ℓ₀ hℓ₀
            (st.seeds.nodeAt ℓ₀ hℓ₀ x)) ∧
        ∀ (j : ℕ) (hj : j ≤ P.depth) (w : Fin (P.numNodes j)),
          ¬ P.InSubtree ℓ₀ (st.seeds.nodeAt ℓ₀ hℓ₀ x) j w →
            st'.seeds.seed j hj w = st.seeds.seed j hj w) ∧
    ∃ storeLvl' : Fin P.paddedUniv → ℕ,
      st'.WellFormedPadded scheme (Function.update d x (some v)) storeLvl' := by
  have hd_eq : st.rawQuery scheme = d := funext (st.rawQuery_eq hwf)
  let d' := Function.update d x (some v)
  have hS'_eq : P.paddedDom d' = Insert.insert x (P.paddedDom d) := P.paddedDom_update_some d x v
  dsimp only [rawInsertFresh]
  simp only [hd_eq]
  by_cases h_norm : ∃ sl, st.WellFormedPadded scheme d sl ∧
      x ∉ P.paddedDom d ∧ st.seeds.AllGoodSeeds (Insert.insert x (P.paddedDom d))
  · rw [dite_eq_left h_norm]
    let spec := Classical.choose_spec h_norm
    exact ⟨st.sentCount_normalInsertFresh spec.1 x v spec.2.1 spec.2.2,
      Or.inl (st.seeds_normalInsertFresh spec.1 x v spec.2.1 spec.2.2),
      _, st.wellFormedPadded_normalInsertFresh spec.1 x v spec.2.1 spec.2.2⟩
  · rw [dite_eq_right h_norm]
    have h_pre : st.seeds.AllGoodSeeds (P.paddedDom d) ∧
        (P.nLow 0 ≤ #(P.paddedDom d') ∧ #(P.paddedDom d') ≤ P.nHigh 0) :=
      ⟨hwf.goodSeeds, hS'_eq ▸ hcard'⟩
    rw [dite_eq_left h_pre]
    by_cases h_bad : ∃ ℓ, hasBadSeedOn st.seeds (P.paddedDom d') ℓ
    · rw [dite_eq_left h_bad]
      obtain ⟨hsc, ⟨ℓ₀, hℓ₀, hng, hout⟩, sl', hwfp'⟩ :=
        repairBadSeedsTree_spec hcr scheme st.seeds (P.paddedDom d) d' st.sentCount x
          h_pre.1 h_pre.2
          (fun y => if hyx : y = x then Or.inr hyx else Or.inl (by simp [d', hyx])) h_bad
      exact ⟨hsc, Or.inr ⟨ℓ₀, hℓ₀, hS'_eq ▸ hng, hout⟩, sl', hwfp'⟩
    · rw [dite_eq_right h_bad]
      have hgood' : st.seeds.AllGoodSeeds (P.paddedDom d') :=
        ⟨h_pre.2, fun ℓ hℓ w => by by_contra hnot; exact h_bad ⟨ℓ, hℓ, w, hnot⟩⟩
      exact False.elim (h_norm ⟨storeLvl, hwf, hx_fresh, hS'_eq ▸ hgood'⟩)

open scoped Classical in
/-- Internal member-key deletion on `st` (`z ∈ paddedDom d`, `#S' ∈ [nLow 0, nHigh 0]`): runs
`normalDeleteMem` (`Algorithm 3`) when `st.seeds` stays good on `S.erase z`, and otherwise
resamples only `InSubtree ℓ₀ (nodeAt ℓ₀ z)` at the highest failing level `ℓ₀`. -/
noncomputable def rawDeleteMem (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (z : Fin P.paddedUniv) : P.TreeState :=
  let d_cur : P.PaddedDict := st.rawQuery scheme
  let S_cur := P.paddedDom d_cur
  let d' := Function.update d_cur z none
  let S' := P.paddedDom d'
  if st.seeds.AllGoodSeeds S' then
    st.normalDeleteMem scheme z
  else if h_pre : st.seeds.AllGoodSeeds S_cur ∧ (P.nLow 0 ≤ #S' ∧ #S' ≤ P.nHigh 0) then
    if h_bad : ∃ ℓ, hasBadSeedOn st.seeds S' ℓ then
      repairBadSeedsTree hcr scheme st.seeds S_cur d' st.sentCount z h_pre.1 h_pre.2
        (fun y => if hyz : y = z then Or.inr hyz else Or.inl (by simp [d', S_cur, hyz])) h_bad
    else st.normalDeleteMem scheme z
  else st

open scoped Classical in
theorem wellFormedPadded_rawDeleteMem (hcr : P.ConcentrationReady)
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {z : Fin P.paddedUniv} (hz : z ∈ P.paddedDom d)
    (hcard' : P.nLow 0 ≤ #((P.paddedDom d).erase z) ∧
      #((P.paddedDom d).erase z) ≤ P.nHigh 0) :
    let st' := st.rawDeleteMem hcr scheme z
    st'.sentCount = st.sentCount ∧
    (st'.seeds = st.seeds ∨
      ∃ (ℓ₀ : ℕ) (hℓ₀ : ℓ₀ ≤ P.depth),
        ¬ P.IsGoodNodeSeed ℓ₀ (st.seeds.seed ℓ₀ hℓ₀ (st.seeds.nodeAt ℓ₀ hℓ₀ z))
          (st.seeds.primSetAt ((P.paddedDom d).erase z) ℓ₀ hℓ₀
            (st.seeds.nodeAt ℓ₀ hℓ₀ z)) ∧
        ∀ (j : ℕ) (hj : j ≤ P.depth) (w : Fin (P.numNodes j)),
          ¬ P.InSubtree ℓ₀ (st.seeds.nodeAt ℓ₀ hℓ₀ z) j w →
            st'.seeds.seed j hj w = st.seeds.seed j hj w) ∧
    ∃ storeLvl' : Fin P.paddedUniv → ℕ,
      st'.WellFormedPadded scheme (Function.update d z none) storeLvl' := by
  have hd_eq : st.rawQuery scheme = d := funext (st.rawQuery_eq hwf)
  let d' := Function.update d z none
  have hS'_eq : P.paddedDom d' = (P.paddedDom d).erase z := P.paddedDom_update_none d z
  dsimp only [rawDeleteMem]
  simp only [hd_eq]
  by_cases hgood' : st.seeds.AllGoodSeeds (P.paddedDom d')
  · rw [ite_eq_left hgood']
    obtain ⟨hsc, hsd, sl', hwf'⟩ := wellFormedPadded_normalDeleteMem hwf hz (hS'_eq ▸ hgood')
    exact ⟨hsc, Or.inl hsd, sl', hwf'⟩
  · rw [ite_eq_right hgood']
    have h_pre : st.seeds.AllGoodSeeds (P.paddedDom d) ∧
        (P.nLow 0 ≤ #(P.paddedDom d') ∧ #(P.paddedDom d') ≤ P.nHigh 0) :=
      ⟨hwf.goodSeeds, hS'_eq ▸ hcard'⟩
    rw [dite_eq_left h_pre]
    have h_bad : ∃ ℓ, hasBadSeedOn st.seeds (P.paddedDom d') ℓ := by
      by_contra hno
      exact hgood' ⟨h_pre.2, fun ℓ hℓ w => by by_contra hn; exact hno ⟨ℓ, hℓ, w, hn⟩⟩
    rw [dite_eq_left h_bad]
    obtain ⟨hsc, ⟨ℓ₀, hℓ₀, hng, hout⟩, sl', hwfp'⟩ :=
      repairBadSeedsTree_spec hcr scheme st.seeds (P.paddedDom d) d' st.sentCount z
        h_pre.1 h_pre.2
        (fun y => if hyz : y = z then Or.inr hyz else Or.inl (by simp [d', hyz])) h_bad
    exact ⟨hsc, Or.inr ⟨ℓ₀, hℓ₀, hS'_eq ▸ hng, hout⟩, sl', hwfp'⟩

private theorem WellFormedPadded.withSentCount
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl) (sc : ℕ) :
    ({ st with sentCount := sc } : P.TreeState).WellFormedPadded scheme d storeLvl := by
  let st' : P.TreeState := { st with sentCount := sc }
  have hsd : st'.seeds = st.seeds := by
    ext ℓ hℓ u
    by_cases h0 : ℓ = 0
    · subst h0; rw [seeds_zero, seeds_zero]
    · by_cases h1 : ℓ = 1
      · subst h1; rw [seeds_one, seeds_one]
      · by_cases hlt : ℓ < P.depth
        · rw [seeds_inner st' (by omega) hlt hℓ, seeds_inner st (by omega) hlt hℓ]
        · have hd : ℓ = P.depth := by omega
          subst hd; rw [seeds_depth, seeds_depth]
  have hdom : ∀ (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)),
      st'.nodeDom ℓ h1 hℓ u = st.nodeDom ℓ h1 hℓ u := fun ℓ h1 hℓ u => by
    by_cases ho : ℓ = 1
    · subst ho; rw [nodeDom_one, nodeDom_one]
    · by_cases hlt : ℓ < P.depth
      · rw [nodeDom_inner st' h1 (by omega) hlt hℓ, nodeDom_inner st h1 (by omega) hlt hℓ]
      · have hd : ℓ = P.depth := by omega
        subst hd; rw [nodeDom_depth, nodeDom_depth]
  have hq : ∀ (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) k,
      st'.nodeQuery scheme ℓ h1 hℓ u k = st.nodeQuery scheme ℓ h1 hℓ u k := fun ℓ h1 hℓ u k => by
    by_cases ho : ℓ = 1
    · subst ho; rw [nodeQuery_one, nodeQuery_one]
    · by_cases hlt : ℓ < P.depth
      · rw [nodeQuery_inner _ st' h1 (by omega) hlt hℓ, nodeQuery_inner _ st h1 (by omega) hlt hℓ]
      · have hd : ℓ = P.depth := by omega
        subst hd; rw [nodeQuery_depth, nodeQuery_depth]
  have hw : ∀ (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)),
      st'.nodeWait ℓ h2 hℓ u = st.nodeWait ℓ h2 hℓ u := fun ℓ h2 hℓ u => by
    by_cases hlt : ℓ < P.depth
    · rw [nodeWait_inner st' h2 hlt hℓ, nodeWait_inner st h2 hlt hℓ]
    · have hd : ℓ = P.depth := by omega
      subst hd; rw [nodeWait_depth, nodeWait_depth]
  refine
    { goodSeeds := hsd ▸ hwf.goodSeeds
      storeLvl_bounds := hwf.storeLvl_bounds
      storeLvl_outside := hwf.storeLvl_outside
      dom_eq := fun ℓ h1 hℓ u => by rw [hdom, hsd, hwf.dom_eq]
      query_eq_of_storeLvl := fun ℓ h1 hℓ u x vx hdx hnx hsl => by
        rw [hsd] at hnx ⊢; rw [hq]; exact hwf.query_eq_of_storeLvl ℓ h1 hℓ u x vx hdx hnx hsl
      inner_full := hwf.inner_full
      wait_dom_eq := fun ℓ h2 hℓ u => by rw [hw, hsd, hwf.wait_dom_eq]
      wait_lookup_eq := fun ℓ h2 hℓ u x hx hsl => by
        rw [hsd] at hx ⊢; rw [hw]; exact hwf.wait_lookup_eq ℓ h2 hℓ u x hx hsl }

end TreeState

/-! ## Section 2: External Dictionary Interface (`initTree`, `insert`, `delete`) -/

private theorem nLow_zero_eq (P : TreeSchedule) : P.nLow 0 = P.cap - 1 := by rfl

private theorem nHigh_zero_eq (P : TreeSchedule) : P.nHigh 0 = P.cap := by rfl

/-- Initialize an empty external dictionary (`Dictionary.empty P.univ`) padded with `P.cap`
sentinel keys (`Section 4, Footnote 5` & `Section 5`). -/
noncomputable def initTree (P : TreeSchedule) (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)) : P.TreeState :=
  have hm := P.matchesExternal_initPaddedDict
  have hcard0 : P.nLow 0 ≤ #(P.paddedDom P.initPaddedDict) ∧
      #(P.paddedDom P.initPaddedDict) ≤ P.nHigh 0 := by
    rw [P.nLow_zero_eq, P.nHigh_zero_eq]
    exact ⟨hm.card_lo, hm.card_hi⟩
  let hex := exists_allGoodSeeds hcr hcard0
  P.buildTreeFromSeeds scheme P.initPaddedDict P.cap (Classical.choose hex)
    (Classical.choose_spec hex)

/-- **`initTree` satisfies `WellFormed` for `Dictionary.empty P.univ`**. -/
theorem wellFormed_initTree (P : TreeSchedule) (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)) :
    (P.initTree hcr scheme).WellFormed scheme (Dictionary.empty P.univ) := by
  dsimp only [initTree]
  refine ⟨P.initPaddedDict, _, ?_,
    P.wellFormedPadded_buildTreeFromSeeds scheme P.initPaddedDict P.cap _ _⟩
  rw [P.sentCount_buildTreeFromSeeds]
  exact P.matchesExternal_initPaddedDict

@[simp]
theorem query_initTree (P : TreeSchedule) (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (u : Fin P.univ) :
    (P.initTree hcr scheme).query scheme u = none :=
  TreeState.query_eq_apply (P.wellFormed_initTree hcr scheme) u

namespace TreeState

variable {P : TreeSchedule}

/-- Insert or overwrite external key `u : Fin P.univ` with bounded value `v : Fin P.valBound`,
maintaining sentinel padding in `{cap - 1, cap}` (`Section 5.3`). -/
noncomputable def insert (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (u : Fin P.univ) (v : Fin P.valBound) : P.TreeState :=
  let x := P.embedReal u
  if (st.rawQuery scheme x).isSome then
    st.rawOverwrite scheme x v
  else if #(P.paddedDom (st.rawQuery scheme)) < P.cap then
    st.rawInsertFresh hcr scheme x v
  else if hsc : 0 < st.sentCount ∧ st.sentCount ≤ P.cap then
    let s_last := P.sentinelKey ⟨st.sentCount - 1, by omega⟩
    let st₁ := { (st.rawDeleteMem hcr scheme s_last) with sentCount := st.sentCount - 1 }
    st₁.rawInsertFresh hcr scheme x v
  else st

/-- **External `insert` preserves `WellFormed`** (either overwriting an existing key `u ∈ dom dict`
or inserting a fresh key when `(dom dict).card < P.cap`). -/
theorem wellFormed_insert (hcr : P.ConcentrationReady)
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {dict : Dictionary.State P.univ} (hwf : st.WellFormed scheme dict)
    (u : Fin P.univ) (v : Fin P.valBound)
    (hcap : u ∈ Dictionary.dom dict ∨ (Dictionary.dom dict).card < P.cap) :
    (st.insert hcr scheme u v).WellFormed scheme (Function.update dict u (some v.val)) := by
  obtain ⟨d, storeLvl, hm, hwfp⟩ := hwf
  have hd_eq : st.rawQuery scheme = d := funext (st.rawQuery_eq hwfp)
  let x := P.embedReal u
  have hreal_iff : (d x).isSome ↔ u ∈ Dictionary.dom dict := by
    simp only [Dictionary.dom, mem_filter, Finset.mem_univ, true_and, ← hm.real_eq u,
      Option.isSome_map, x]
  dsimp only [insert]
  rw [hd_eq]
  by_cases hmem : (d x).isSome
  · rw [ite_eq_left hmem]
    have hx_dom : x ∈ P.paddedDom d := (P.mem_paddedDom_iff d x).mpr hmem
    refine ⟨Function.update d x (some v), storeLvl, ?_, st.wellFormedPadded_rawOverwrite hwfp
      hx_dom v⟩
    rw [st.sentCount_rawOverwrite]
    have hdom_eq : P.paddedDom (Function.update d x (some v)) = P.paddedDom d := by
      rw [P.paddedDom_update_some, insert_eq_of_mem hx_dom]
    refine
      { sentCount_le := hm.sentCount_le
        card_lo := hdom_eq ▸ hm.card_lo
        card_hi := hdom_eq ▸ hm.card_hi
        real_eq := fun u' => by
          by_cases hu : u' = u
          · subst hu; simp [x]
          · have hne : P.embedReal u' ≠ x := fun h => hu (P.embedReal_injective h)
            rw [Function.update_of_ne hne, Function.update_of_ne hu, hm.real_eq u']
        sentinel_eq := fun y hy => by
          have hne : y ≠ x := fun h => by subst h; exact absurd u.isLt (not_lt.mpr hy)
          rw [Function.update_of_ne hne, hm.sentinel_eq y hy] }
  · rw [ite_eq_right hmem]
    have hu_not_dom : u ∉ Dictionary.dom dict := mt hreal_iff.mpr hmem
    have hlt_cap : (Dictionary.dom dict).card < P.cap := hcap.resolve_left hu_not_dom
    have hx_fresh : x ∉ P.paddedDom d := mt (P.mem_paddedDom_iff d x).mp hmem
    by_cases hlt_pad : #(P.paddedDom d) < P.cap
    · rw [ite_eq_left hlt_pad]
      have hcard_d : #(P.paddedDom d) = P.cap - 1 := by
        have := hm.card_lo; omega
      have hcard' : P.nLow 0 ≤ #(Insert.insert x (P.paddedDom d)) ∧
          #(Insert.insert x (P.paddedDom d)) ≤ P.nHigh 0 := by
        rw [card_insert_of_notMem hx_fresh, P.nLow_zero_eq, P.nHigh_zero_eq]
        have := P.two_le_cap; omega
      obtain ⟨hsc, _, sl', hwfp'⟩ :=
        st.wellFormedPadded_rawInsertFresh hcr hwfp hx_fresh v hcard'
      refine ⟨Function.update d x (some v), sl', ?_, hwfp'⟩
      rw [hsc]
      have hdom' : #(P.paddedDom (Function.update d x (some v))) = P.cap := by
        rw [P.paddedDom_update_some, card_insert_of_notMem hx_fresh]
        have := P.two_le_cap; omega
      refine
        { sentCount_le := hm.sentCount_le
          card_lo := by rw [hdom']; omega
          card_hi := by rw [hdom']
          real_eq := fun u' => by
            by_cases hu : u' = u
            · subst hu; simp [x]
            · have hne : P.embedReal u' ≠ x := fun h => hu (P.embedReal_injective h)
              rw [Function.update_of_ne hne, Function.update_of_ne hu, hm.real_eq u']
          sentinel_eq := fun y hy => by
            have hne : y ≠ x := fun h => by subst h; exact absurd u.isLt (not_lt.mpr hy)
            rw [Function.update_of_ne hne, hm.sentinel_eq y hy] }
    · rw [ite_eq_right hlt_pad]
      have hcard_d : #(P.paddedDom d) = P.cap := by have := hm.card_hi; omega
      have hsum_d := P.card_paddedDom_eq hm
      have hsc_ok : 0 < st.sentCount ∧ st.sentCount ≤ P.cap := ⟨by omega, hm.sentCount_le⟩
      rw [dite_eq_left hsc_ok]
      let s_last := P.sentinelKey ⟨st.sentCount - 1, by omega⟩
      have hs_ge : P.univ ≤ s_last.val := by dsimp only [s_last, sentinelKey]; omega
      have hs_lt : s_last.val < P.univ + st.sentCount := by dsimp only [s_last, sentinelKey]; omega
      have hs_mem : s_last ∈ P.paddedDom d := by
        rw [P.mem_paddedDom_iff, hm.sentinel_eq s_last hs_ge, ite_eq_left hs_lt]; rfl
      have hcard_er : P.nLow 0 ≤ #((P.paddedDom d).erase s_last) ∧
          #((P.paddedDom d).erase s_last) ≤ P.nHigh 0 := by
        rw [card_erase_of_mem hs_mem, hcard_d, P.nLow_zero_eq, P.nHigh_zero_eq]
        exact ⟨le_rfl, by omega⟩
      obtain ⟨_, _, sl₁, hwfp₁_raw⟩ :=
        st.wellFormedPadded_rawDeleteMem hcr hwfp hs_mem hcard_er
      let d₁ := Function.update d s_last none
      let st₁ : P.TreeState :=
        { (st.rawDeleteMem hcr scheme s_last) with sentCount := st.sentCount - 1 }
      have hwfp₁ : st₁.WellFormedPadded scheme d₁ sl₁ := hwfp₁_raw.withSentCount (st.sentCount - 1)
      have hx_ne_s : x ≠ s_last := P.embedReal_ne_sentinelKey u _
      have hx_fresh₁ : x ∉ P.paddedDom d₁ := by
        rw [P.paddedDom_update_none, mem_erase]
        exact fun h => hx_fresh h.2
      have hcard_ins : P.nLow 0 ≤ #(Insert.insert x (P.paddedDom d₁)) ∧
          #(Insert.insert x (P.paddedDom d₁)) ≤ P.nHigh 0 := by
        rw [card_insert_of_notMem hx_fresh₁, P.paddedDom_update_none,
          card_erase_of_mem hs_mem, hcard_d, P.nLow_zero_eq, P.nHigh_zero_eq]
        have := P.two_le_cap; omega
      obtain ⟨hsc₂, _, sl₂, hwfp₂⟩ :=
        st₁.wellFormedPadded_rawInsertFresh hcr hwfp₁ hx_fresh₁ v hcard_ins
      refine ⟨Function.update d₁ x (some v), sl₂, ?_, hwfp₂⟩
      rw [hsc₂]
      have hdom₂ : #(P.paddedDom (Function.update d₁ x (some v))) = P.cap := by
        rw [P.paddedDom_update_some, card_insert_of_notMem hx_fresh₁, P.paddedDom_update_none,
          card_erase_of_mem hs_mem, hcard_d]
        have := P.two_le_cap; omega
      refine
        { sentCount_le := by change st.sentCount - 1 ≤ P.cap; omega
          card_lo := by rw [hdom₂]; omega
          card_hi := by rw [hdom₂]
          real_eq := fun u' => by
            by_cases hu : u' = u
            · subst hu; simp [x]
            · have hne_x : P.embedReal u' ≠ x := fun h => hu (P.embedReal_injective h)
              have hne_s : P.embedReal u' ≠ s_last := P.embedReal_ne_sentinelKey u' _
              rw [Function.update_of_ne hne_x, Function.update_of_ne hu]
              dsimp only [d₁]
              rw [Function.update_of_ne hne_s, hm.real_eq u']
          sentinel_eq := fun y hy => by
            have hne_x : y ≠ x := fun h => by subst h; exact absurd u.isLt (not_lt.mpr hy)
            rw [Function.update_of_ne hne_x]
            dsimp only [d₁]
            by_cases hys : y = s_last
            · subst hys
              rw [Function.update_self]
              change none = if s_last.val < P.univ + (st.sentCount - 1) then _ else none
              have hnot_lt : ¬ s_last.val < P.univ + (st.sentCount - 1) := by
                dsimp only [s_last, sentinelKey]; omega
              rw [ite_eq_right hnot_lt]
            · rw [Function.update_of_ne hys, hm.sentinel_eq y hy]
              have hs_val_ne : y.val ≠ P.univ + (st.sentCount - 1) := fun hv =>
                hys (Fin.ext (by dsimp only [s_last, sentinelKey]; omega))
              change (if y.val < P.univ + st.sentCount then _ else none) =
                if y.val < P.univ + (st.sentCount - 1) then _ else none
              by_cases hlt1 : y.val < P.univ + (st.sentCount - 1)
              · rw [ite_eq_left (by omega), ite_eq_left hlt1]
              · rw [ite_eq_right (by omega), ite_eq_right hlt1] }

/-- **Lookup after `insert` satisfies `Function.update`**. -/
theorem query_insert (hcr : P.ConcentrationReady)
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {dict : Dictionary.State P.univ} (hwf : st.WellFormed scheme dict)
    (u : Fin P.univ) (v : Fin P.valBound)
    (hcap : u ∈ Dictionary.dom dict ∨ (Dictionary.dom dict).card < P.cap)
    (u' : Fin P.univ) :
    (st.insert hcr scheme u v).query scheme u' =
      Function.update (st.query scheme) u (some v.val) u' := by
  rw [query_eq_apply (st.wellFormed_insert hcr hwf u v hcap) u']
  have hq : st.query scheme = dict := funext (query_eq_apply hwf)
  rw [hq]

/-- Delete external key `u : Fin P.univ` (no-op if absent), maintaining sentinel padding in
`{cap - 1, cap}` (`Section 5.3` & `Algorithm 3`). -/
noncomputable def delete (hcr : P.ConcentrationReady)
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (st : P.TreeState) (u : Fin P.univ) : P.TreeState :=
  let x := P.embedReal u
  if !(st.rawQuery scheme x).isSome then
    st
  else if P.cap ≤ #(P.paddedDom (st.rawQuery scheme)) then
    st.rawDeleteMem hcr scheme x
  else if hsc : st.sentCount < P.cap then
    let s_new := P.sentinelKey ⟨st.sentCount, hsc⟩
    let st₁ := { (st.rawInsertFresh hcr scheme s_new ⟨0, P.val_pos⟩) with
      sentCount := st.sentCount + 1 }
    st₁.rawDeleteMem hcr scheme x
  else st

/-- **External `delete` preserves `WellFormed`**. -/
theorem wellFormed_delete (hcr : P.ConcentrationReady)
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {dict : Dictionary.State P.univ} (hwf : st.WellFormed scheme dict)
    (u : Fin P.univ) :
    (st.delete hcr scheme u).WellFormed scheme (Function.update dict u none) := by
  obtain ⟨d, storeLvl, hm, hwfp⟩ := hwf
  have hd_eq : st.rawQuery scheme = d := funext (st.rawQuery_eq hwfp)
  let x := P.embedReal u
  dsimp only [delete]
  rw [hd_eq]
  by_cases hmem : (d x).isSome
  · rw [ite_eq_right (by simp [x, hmem])]
    have hx_dom : x ∈ P.paddedDom d := (P.mem_paddedDom_iff d x).mpr hmem
    have hu_dom : u ∈ Dictionary.dom dict := by
      simp only [Dictionary.dom, mem_filter, Finset.mem_univ, true_and, ← hm.real_eq u,
        Option.isSome_map]
      exact hmem
    have hdom_pos : 1 ≤ (Dictionary.dom dict).card := Finset.card_pos.mpr ⟨u, hu_dom⟩
    by_cases hge_cap : P.cap ≤ #(P.paddedDom d)
    · rw [ite_eq_left hge_cap]
      have hcard_d : #(P.paddedDom d) = P.cap := by have := hm.card_hi; omega
      have hcard_er : P.nLow 0 ≤ #((P.paddedDom d).erase x) ∧
          #((P.paddedDom d).erase x) ≤ P.nHigh 0 := by
        rw [card_erase_of_mem hx_dom, hcard_d, P.nLow_zero_eq, P.nHigh_zero_eq]
        exact ⟨le_rfl, by omega⟩
      obtain ⟨hsc, _, sl', hwfp'⟩ :=
        st.wellFormedPadded_rawDeleteMem hcr hwfp hx_dom hcard_er
      refine ⟨Function.update d x none, sl', ?_, hwfp'⟩
      rw [hsc]
      have hdom' : #(P.paddedDom (Function.update d x none)) = P.cap - 1 := by
        rw [P.paddedDom_update_none, card_erase_of_mem hx_dom, hcard_d]
      refine
        { sentCount_le := hm.sentCount_le
          card_lo := by rw [hdom']
          card_hi := by rw [hdom']; omega
          real_eq := fun u' => by
            by_cases hu : u' = u
            · subst hu; simp [x]
            · have hne : P.embedReal u' ≠ x := fun h => hu (P.embedReal_injective h)
              rw [Function.update_of_ne hne, Function.update_of_ne hu, hm.real_eq u']
          sentinel_eq := fun y hy => by
            have hne : y ≠ x := fun h => by subst h; exact absurd u.isLt (not_lt.mpr hy)
            rw [Function.update_of_ne hne, hm.sentinel_eq y hy] }
    · rw [ite_eq_right hge_cap]
      have hcard_d : #(P.paddedDom d) = P.cap - 1 := by have := hm.card_lo; omega
      have hsum_d := P.card_paddedDom_eq hm
      have hsc_lt : st.sentCount < P.cap := by omega
      rw [dite_eq_left hsc_lt]
      let s_new := P.sentinelKey ⟨st.sentCount, hsc_lt⟩
      have hs_ge : P.univ ≤ s_new.val := by dsimp only [s_new, sentinelKey]; omega
      have hs_not_lt : ¬ s_new.val < P.univ + st.sentCount := by
        dsimp only [s_new, sentinelKey]; omega
      have hs_fresh : s_new ∉ P.paddedDom d := by
        rw [P.mem_paddedDom_iff, hm.sentinel_eq s_new hs_ge, ite_eq_right hs_not_lt]; simp
      have hcard_ins : P.nLow 0 ≤ #(Insert.insert s_new (P.paddedDom d)) ∧
          #(Insert.insert s_new (P.paddedDom d)) ≤ P.nHigh 0 := by
        rw [card_insert_of_notMem hs_fresh, hcard_d, P.nLow_zero_eq, P.nHigh_zero_eq]
        have := P.two_le_cap; omega
      obtain ⟨_, _, sl₁, hwfp₁_raw⟩ :=
        st.wellFormedPadded_rawInsertFresh hcr hwfp hs_fresh ⟨0, P.val_pos⟩ hcard_ins
      let d₁ := Function.update d s_new (some ⟨0, P.val_pos⟩)
      let st₁ : P.TreeState :=
        { (st.rawInsertFresh hcr scheme s_new ⟨0, P.val_pos⟩) with
          sentCount := st.sentCount + 1 }
      have hwfp₁ : st₁.WellFormedPadded scheme d₁ sl₁ := hwfp₁_raw.withSentCount (st.sentCount + 1)
      have hx_ne_s : x ≠ s_new := P.embedReal_ne_sentinelKey u _
      have hx_dom₁ : x ∈ P.paddedDom d₁ := by
        rw [P.paddedDom_update_some, mem_insert]
        exact Or.inr hx_dom
      have hcard_er : P.nLow 0 ≤ #((P.paddedDom d₁).erase x) ∧
          #((P.paddedDom d₁).erase x) ≤ P.nHigh 0 := by
        rw [card_erase_of_mem hx_dom₁, P.paddedDom_update_some,
          card_insert_of_notMem hs_fresh, hcard_d, P.nLow_zero_eq, P.nHigh_zero_eq]
        have := P.two_le_cap; omega
      obtain ⟨hsc₂, _, sl₂, hwfp₂⟩ :=
        st₁.wellFormedPadded_rawDeleteMem hcr hwfp₁ hx_dom₁ hcard_er
      refine ⟨Function.update d₁ x none, sl₂, ?_, hwfp₂⟩
      rw [hsc₂]
      have hdom₂ : #(P.paddedDom (Function.update d₁ x none)) = P.cap - 1 := by
        rw [P.paddedDom_update_none, card_erase_of_mem hx_dom₁, P.paddedDom_update_some,
          card_insert_of_notMem hs_fresh, hcard_d]
        have := P.two_le_cap; omega
      refine
        { sentCount_le := by change st.sentCount + 1 ≤ P.cap; omega
          card_lo := by rw [hdom₂]
          card_hi := by rw [hdom₂]; omega
          real_eq := fun u' => by
            by_cases hu : u' = u
            · subst hu; simp [x]
            · have hne_x : P.embedReal u' ≠ x := fun h => hu (P.embedReal_injective h)
              have hne_s : P.embedReal u' ≠ s_new := P.embedReal_ne_sentinelKey u' _
              rw [Function.update_of_ne hne_x, Function.update_of_ne hu]
              dsimp only [d₁]
              rw [Function.update_of_ne hne_s, hm.real_eq u']
          sentinel_eq := fun y hy => by
            have hne_x : y ≠ x := fun h => by subst h; exact absurd u.isLt (not_lt.mpr hy)
            rw [Function.update_of_ne hne_x]
            dsimp only [d₁]
            by_cases hys : y = s_new
            · subst hys
              rw [Function.update_self]
              change some (⟨0, P.val_pos⟩ : Fin P.valBound) =
                if s_new.val < P.univ + (st.sentCount + 1) then some ⟨0, P.val_pos⟩ else none
              have hlt_new : s_new.val < P.univ + (st.sentCount + 1) := by
                dsimp only [s_new, sentinelKey]; omega
              rw [ite_eq_left hlt_new]
            · rw [Function.update_of_ne hys, hm.sentinel_eq y hy]
              have hs_val_ne : y.val ≠ P.univ + st.sentCount := fun hv =>
                hys (Fin.ext (by dsimp only [s_new, sentinelKey]; omega))
              change (if y.val < P.univ + st.sentCount then _ else none) =
                if y.val < P.univ + (st.sentCount + 1) then _ else none
              by_cases hlt1 : y.val < P.univ + st.sentCount
              · rw [ite_eq_left hlt1, ite_eq_left (by omega)]
              · rw [ite_eq_right hlt1, ite_eq_right (by omega)] }
  · rw [ite_eq_left (by simp [x, hmem])]
    have hdu_none : dict u = none := by
      rw [← hm.real_eq u]
      rcases hd_u : d x with _ | w
      · rfl
      · simp [x, hd_u] at hmem
    have hupd_eq : Function.update dict u none = dict := by
      ext u'; by_cases hu : u' = u
      · subst hu; rw [Function.update_self, hdu_none]
      · rw [Function.update_of_ne hu]
    rw [hupd_eq]
    exact ⟨d, storeLvl, hm, hwfp⟩

/-- **Lookup after `delete` satisfies `Function.update`**. -/
theorem query_delete (hcr : P.ConcentrationReady)
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {dict : Dictionary.State P.univ} (hwf : st.WellFormed scheme dict)
    (u u' : Fin P.univ) :
    (st.delete hcr scheme u).query scheme u' =
      Function.update (st.query scheme) u none u' := by
  rw [query_eq_apply (st.wellFormed_delete hcr hwf u) u']
  have hq : st.query scheme = dict := funext (query_eq_apply hwf)
  rw [hq]

end TreeState

/-! ## Section 3: Trajectory Bridge to `Claim 5.4` and `Lemma 5.3` (`RehashBounds`) -/

namespace SeedAssignment

variable {P : TreeSchedule}

/-- **Maximal ancestor-rehash-free trajectory theorem (`Section 5.5` bridge to `RehashBounds`)**:
along any `T`-step padded update sequence `(S_seq 0, …, S_seq T)` and seed sequence
`(seeds_seq 0, …, seeds_seq T)` where each `seeds_seq i` is good on `S_seq i` and no strict
ancestor `j < ℓ` of `(ℓ, u)` changes its seed, the primitive-ID sets arriving at `(ℓ, u)` depend
solely on `seeds_seq 0` and `S_seq i` and form a `ValidPrimIdSeq ℓ T`. -/
theorem primSetAt_validPrimIdSeq {T ℓ : ℕ} (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    (S_seq : Fin (T + 1) → Finset (Fin P.paddedUniv))
    (seeds_seq : Fin (T + 1) → P.SeedAssignment)
    (hgood : ∀ i : Fin (T + 1), (seeds_seq i).AllGoodSeeds (S_seq i))
    (hanc_fixed : ∀ (i : Fin (T + 1)) (j : ℕ) (hj : j < ℓ),
      (seeds_seq i).seed j (hj.le.trans hℓ) (P.ancestorAt hj.le u) =
        (seeds_seq 0).seed j (hj.le.trans hℓ) (P.ancestorAt hj.le u)) :
    (∀ i : Fin (T + 1),
      (seeds_seq i).primSetAt (S_seq i) ℓ hℓ u =
        (seeds_seq 0).primSetAt (S_seq i) ℓ hℓ u) ∧
    P.ValidPrimIdSeq ℓ T (fun i => (seeds_seq 0).primSetAt (S_seq i) ℓ hℓ u) := by
  have heq : ∀ i : Fin (T + 1),
      (seeds_seq i).primSetAt (S_seq i) ℓ hℓ u =
        (seeds_seq 0).primSetAt (S_seq i) ℓ hℓ u := fun i =>
    primSetAt_congr_ancestors (S_seq i) hℓ u (hanc_fixed i)
  refine ⟨heq, fun i => ?_⟩
  dsimp only
  rw [← heq i, (seeds_seq i).card_primSetAt_eq (hgood i) hℓ u]
  exact (seeds_seq i).load_bounds_of_allGoodSeeds (hgood i) hℓ u

/-- **`Claim 5.4` over an ancestor-rehash-free tree trajectory**: for `k ≤ P.rehashWindow ℓ`, a
uniformly resampled seed `g : P.NodeSeed ℓ` at `(ℓ, u)` survives all `k + 1` steps with probability
at least `1 / 2`. -/
theorem prob_survives_window_of_ancestorFree (hcr : P.ConcentrationReady) {k ℓ : ℕ}
    (hℓ : ℓ ≤ P.depth) (hk : k ≤ P.rehashWindow ℓ) (u : Fin (P.numNodes ℓ))
    (S_seq : Fin (k + 1) → Finset (Fin P.paddedUniv))
    (seeds_seq : Fin (k + 1) → P.SeedAssignment)
    (hgood : ∀ i : Fin (k + 1), (seeds_seq i).AllGoodSeeds (S_seq i))
    (hanc_fixed : ∀ (i : Fin (k + 1)) (j : ℕ) (hj : j < ℓ),
      (seeds_seq i).seed j (hj.le.trans hℓ) (P.ancestorAt hj.le u) =
        (seeds_seq 0).seed j (hj.le.trans hℓ) (P.ancestorAt hj.le u)) :
    (1 : ℝ) / 2 ≤ ((PMF.uniformOfFintype (P.NodeSeed ℓ)).toOuterMeasure
      {g : P.NodeSeed ℓ |
        ∀ i : Fin (k + 1),
          P.IsGoodNodeSeed ℓ g ((seeds_seq 0).primSetAt (S_seq i) ℓ hℓ u)}).toReal :=
  P.prob_goodNodeSeed_survives_window_ge_half hcr hℓ hk
    (primSetAt_validPrimIdSeq hℓ u S_seq seeds_seq hgood hanc_fixed).2

end SeedAssignment

end TreeSchedule

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
