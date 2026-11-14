/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeDelete

/-!
# Subtree Seed Resampling and Canonical Multi-Level Tree Construction

This file formalizes good-seed existence (`exists_goodSubtreeSeeds`, `exists_allGoodSeeds`,
`exists_allGoodSeeds_localized_pair`) and canonical bottom-up tree
construction (`buildTreeFromSeeds`)
for the subconstant-redundancy dictionary tree of Tianxiao Li, Jingxun Liang, Huacheng Yu, and
Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per Key*
([LiLiangYuZhou2024, Sections 5.2 and 5.5];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 27–30 and 34 /
printed pp. 26–29 and 33).

## Main definitions

* `TreeSchedule.InSubtree`: subtree membership predicate `∃ h : ℓ₀ ≤ ℓ, ancestorAt h u = u₀`.
* `TreeSchedule.ValidStoreLvl`, `TreeSchedule.canonicalStoreLvl`: valid per-key storage-level
  partitions and canonical bottom-up storage-level selection.
* `TreeSchedule.buildTreeFromSeeds`: full-tree construction from a good `SeedAssignment`.

## Main results

* `TreeSchedule.exists_goodSubtreeSeeds`, `TreeSchedule.exists_allGoodSeeds`,
  `TreeSchedule.exists_allGoodSeeds_localized_pair`: existence of good subtree/forest seed
  assignments under `ConcentrationReady` across both `DoubleTabulation` and small-node
  `trinomialPolyHash`.
* `TreeSchedule.wellFormedPadded_buildTreeFromSeeds`: `WellFormedPadded` for `buildTreeFromSeeds`.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Finset

namespace TreeSchedule

variable (P : TreeSchedule)

/-! ## Section 1: Subtree predicate and good-seed resampling (`exists_goodSubtreeSeeds`) -/

/-- Node `(ℓ, u)` lies in the subtree rooted at `(ℓ₀, u₀)` iff `ℓ₀ ≤ ℓ` and `ancestorAt u = u₀`. -/
@[expose]
def InSubtree (ℓ₀ : ℕ) (u₀ : Fin (P.numNodes ℓ₀)) (ℓ : ℕ) (u : Fin (P.numNodes ℓ)) : Prop :=
  ∃ h : ℓ₀ ≤ ℓ, P.ancestorAt h u = u₀

instance instDecidableInSubtree (ℓ₀ : ℕ) (u₀ : Fin (P.numNodes ℓ₀)) (ℓ : ℕ)
    (u : Fin (P.numNodes ℓ)) : Decidable (P.InSubtree ℓ₀ u₀ ℓ u) :=
  if h : ℓ₀ ≤ ℓ then
    decidable_of_iff (P.ancestorAt h u = u₀) ⟨fun he => ⟨h, he⟩, fun ⟨_, he⟩ => he⟩
  else
    isFalse fun ⟨h', _⟩ => h h'

theorem inSubtree_refl {ℓ₀ : ℕ} (u₀ : Fin (P.numNodes ℓ₀)) :
    P.InSubtree ℓ₀ u₀ ℓ₀ u₀ :=
  ⟨le_rfl, P.ancestorAt_refl u₀⟩

theorem not_inSubtree_ancestor_of_not_inSubtree {ℓ₀ : ℕ} {u₀ : Fin (P.numNodes ℓ₀)} {j ℓ : ℕ}
    (hj : j ≤ ℓ) {u : Fin (P.numNodes ℓ)} (hnot : ¬ P.InSubtree ℓ₀ u₀ ℓ u) :
    ¬ P.InSubtree ℓ₀ u₀ j (P.ancestorAt hj u) := by
  rintro ⟨h0j, hanc⟩
  exact hnot ⟨h0j.trans hj, by rw [← P.ancestorAt_trans h0j hj u, hanc]⟩

/-- Update `base : P.SeedAssignment` only at level `L` on nodes satisfying `InSubtree ℓ₀ u₀ L v`. -/
private def updateSeedsAtLevel {P : TreeSchedule} (base : P.SeedAssignment) (ℓ₀ : ℕ)
    (u₀ : Fin (P.numNodes ℓ₀)) (L : ℕ) (hL : L ≤ P.depth)
    (f : ∀ v : Fin (P.numNodes L), P.InSubtree ℓ₀ u₀ L v → P.NodeSeed L) : P.SeedAssignment where
  seed j hj v :=
    if h_eq : j = L then
      Eq.ndrec
        (motive := fun m => Fin (P.numNodes m) → P.NodeSeed m)
        (fun v' => if hsub : P.InSubtree ℓ₀ u₀ L v' then f v' hsub else base.seed L hL v')
        h_eq.symm v
    else base.seed j hj v

private theorem updateSeedsAtLevel_ne {P : TreeSchedule} (base : P.SeedAssignment) (ℓ₀ : ℕ)
    (u₀ : Fin (P.numNodes ℓ₀)) {L : ℕ} (hL : L ≤ P.depth)
    (f : ∀ v : Fin (P.numNodes L), P.InSubtree ℓ₀ u₀ L v → P.NodeSeed L)
    {j : ℕ} (hj : j ≤ P.depth) (v : Fin (P.numNodes j)) (hne : j ≠ L) :
    (updateSeedsAtLevel base ℓ₀ u₀ L hL f).seed j hj v = base.seed j hj v := by
  dsimp only [updateSeedsAtLevel]; rw [dite_eq_right hne]

private theorem updateSeedsAtLevel_outside {P : TreeSchedule} (base : P.SeedAssignment) (ℓ₀ : ℕ)
    (u₀ : Fin (P.numNodes ℓ₀)) {L : ℕ} (hL : L ≤ P.depth)
    (f : ∀ v : Fin (P.numNodes L), P.InSubtree ℓ₀ u₀ L v → P.NodeSeed L)
    {j : ℕ} (hj : j ≤ P.depth) (v : Fin (P.numNodes j)) (hnot : ¬ P.InSubtree ℓ₀ u₀ j v) :
    (updateSeedsAtLevel base ℓ₀ u₀ L hL f).seed j hj v = base.seed j hj v := by
  by_cases h_eq : j = L
  · subst h_eq; dsimp only [updateSeedsAtLevel]; rw [dite_eq_left rfl, dite_eq_right hnot]
  · exact updateSeedsAtLevel_ne base ℓ₀ u₀ hL f hj v h_eq

private theorem updateSeedsAtLevel_self {P : TreeSchedule} (base : P.SeedAssignment) (ℓ₀ : ℕ)
    (u₀ : Fin (P.numNodes ℓ₀)) {L : ℕ} (hL : L ≤ P.depth)
    (f : ∀ v : Fin (P.numNodes L), P.InSubtree ℓ₀ u₀ L v → P.NodeSeed L)
    (v : Fin (P.numNodes L)) (hsub : P.InSubtree ℓ₀ u₀ L v) :
    (updateSeedsAtLevel base ℓ₀ u₀ L hL f).seed L hL v = f v hsub := by
  dsimp only [updateSeedsAtLevel]; rw [dite_eq_left rfl, dite_eq_left hsub]

/-- **Paired subtree good-seed existence (`Algorithm 4` resampling)**: whenever `#S₁, #S₂ ∈
[nLow 0, nHigh 0]` and all strict ancestors `j < ℓ₀` of `u₀` have good seeds in `base` on both `S₁`
and `S₂`, there exists `seeds'` agreeing with `base` outside `InSubtree ℓ₀ u₀` whose every node in
`InSubtree ℓ₀ u₀` satisfies `IsGoodNodeSeed` on both `S₁` and `S₂`. -/
theorem exists_goodSubtreeSeeds_pair {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (base : P.SeedAssignment) {S₁ S₂ : Finset (Fin P.paddedUniv)}
    (hcard₁ : P.nLow 0 ≤ #S₁ ∧ #S₁ ≤ P.nHigh 0)
    (hcard₂ : P.nLow 0 ≤ #S₂ ∧ #S₂ ≤ P.nHigh 0)
    {ℓ₀ : ℕ} (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (hanc₁ : ∀ (j : ℕ) (hj : j < ℓ₀),
      P.IsGoodNodeSeed j (base.seed j (hj.le.trans hℓ₀) (P.ancestorAt hj.le u₀))
        (base.primSetAt S₁ j (hj.le.trans hℓ₀) (P.ancestorAt hj.le u₀)))
    (hanc₂ : ∀ (j : ℕ) (hj : j < ℓ₀),
      P.IsGoodNodeSeed j (base.seed j (hj.le.trans hℓ₀) (P.ancestorAt hj.le u₀))
        (base.primSetAt S₂ j (hj.le.trans hℓ₀) (P.ancestorAt hj.le u₀))) :
    ∃ seeds' : P.SeedAssignment,
      (∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
        ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = base.seed j hj v) ∧
      (∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
        P.InSubtree ℓ₀ u₀ j v →
          P.IsGoodNodeSeed j (seeds'.seed j hj v) (seeds'.primSetAt S₁ j hj v) ∧
          P.IsGoodNodeSeed j (seeds'.seed j hj v) (seeds'.primSetAt S₂ j hj v)) := by
  have hstep : ∀ (t : ℕ) (ht : ℓ₀ + t ≤ P.depth),
      ∃ s : P.SeedAssignment,
        (∀ j hj v, ¬ P.InSubtree ℓ₀ u₀ j v → s.seed j hj v = base.seed j hj v) ∧
        (∀ j hj v, P.InSubtree ℓ₀ u₀ j v → j ≤ ℓ₀ + t →
          P.IsGoodNodeSeed j (s.seed j hj v) (s.primSetAt S₁ j hj v) ∧
          P.IsGoodNodeSeed j (s.seed j hj v) (s.primSetAt S₂ j hj v)) := by
    intro t
    induction t with
    | zero =>
      intro ht
      obtain ⟨hinj₁, hb₁, _⟩ := base.ancestorsGood_invariants hcard₁ ℓ₀ hℓ₀ u₀ hanc₁
      obtain ⟨hinj₂, hb₂, _⟩ := base.ancestorsGood_invariants hcard₂ ℓ₀ hℓ₀ u₀ hanc₂
      have hcp₁ : #(base.primSetAt S₁ ℓ₀ hℓ₀ u₀) = #(base.activeAt S₁ ℓ₀ hℓ₀ u₀) :=
        card_image_of_injOn hinj₁
      have hcp₂ : #(base.primSetAt S₂ ℓ₀ hℓ₀ u₀) = #(base.activeAt S₂ ℓ₀ hℓ₀ u₀) :=
        card_image_of_injOn hinj₂
      have hex₀ := P.exists_isGoodNodeSeed_pair hcr hℓ₀
        (base.primSetAt S₁ ℓ₀ hℓ₀ u₀) (base.primSetAt S₂ ℓ₀ hℓ₀ u₀)
        (hcp₁ ▸ hb₁.1) (hcp₁ ▸ hb₁.2) (hcp₂ ▸ hb₂.1) (hcp₂ ▸ hb₂.2)
      let g₀ := Classical.choose hex₀
      have hg₀ := Classical.choose_spec hex₀
      let s₀ := updateSeedsAtLevel base ℓ₀ u₀ ℓ₀ hℓ₀ fun _ _ => g₀
      refine ⟨s₀, fun j hj v hnot => updateSeedsAtLevel_outside base ℓ₀ u₀ hℓ₀ _ hj v hnot, ?_⟩
      intro j hj v ⟨h0j, hanc_v⟩ hjle
      have hj_eq : ℓ₀ = j := by omega
      subst hj_eq
      have hv : u₀ = v := by simpa only [P.ancestorAt_refl] using hanc_v.symm
      subst hv
      have hp₁ : s₀.primSetAt S₁ ℓ₀ hj u₀ = base.primSetAt S₁ ℓ₀ hℓ₀ u₀ :=
        SeedAssignment.primSetAt_congr_ancestors S₁ hj u₀ fun i hi =>
          updateSeedsAtLevel_ne base ℓ₀ u₀ hℓ₀ _ (hi.le.trans hj) _ (by omega)
      have hp₂ : s₀.primSetAt S₂ ℓ₀ hj u₀ = base.primSetAt S₂ ℓ₀ hℓ₀ u₀ :=
        SeedAssignment.primSetAt_congr_ancestors S₂ hj u₀ fun i hi =>
          updateSeedsAtLevel_ne base ℓ₀ u₀ hℓ₀ _ (hi.le.trans hj) _ (by omega)
      rw [hp₁, hp₂, updateSeedsAtLevel_self base ℓ₀ u₀ hℓ₀ _ u₀ (P.inSubtree_refl u₀)]
      exact hg₀
    | succ t ih =>
      intro ht1
      obtain ⟨s_t, hout_t, hgood_t⟩ := ih (by omega)
      let L := ℓ₀ + (t + 1)
      have hanc_of : ∀ {A : Finset (Fin P.paddedUniv)}
          (hancA : ∀ (j : ℕ) (hj : j < ℓ₀),
            P.IsGoodNodeSeed j (base.seed j (hj.le.trans hℓ₀) (P.ancestorAt hj.le u₀))
              (base.primSetAt A j (hj.le.trans hℓ₀) (P.ancestorAt hj.le u₀)))
          (hgA : ∀ j hj v, P.InSubtree ℓ₀ u₀ j v → j ≤ ℓ₀ + t →
            P.IsGoodNodeSeed j (s_t.seed j hj v) (s_t.primSetAt A j hj v))
          (v : Fin (P.numNodes L)), P.InSubtree ℓ₀ u₀ L v → ∀ (j : ℕ) (hj : j < L),
            P.IsGoodNodeSeed j (s_t.seed j (hj.le.trans ht1) (P.ancestorAt hj.le v))
              (s_t.primSetAt A j (hj.le.trans ht1) (P.ancestorAt hj.le v)) := by
        intro A hancA hgA v ⟨h0L, hanc_v⟩ j hj
        by_cases h0j : ℓ₀ ≤ j
        · exact hgA j (hj.le.trans ht1) (P.ancestorAt hj.le v)
            ⟨h0j, by rw [P.ancestorAt_trans h0j hj.le v, hanc_v]⟩ (by omega)
        · have hjlt0 : j < ℓ₀ := by omega
          have htr : P.ancestorAt hj.le v = P.ancestorAt hjlt0.le u₀ := by
            rw [← hanc_v, P.ancestorAt_trans hjlt0.le h0L v]
          rw [htr, hout_t j _ _ (fun ⟨hge, _⟩ => h0j hge),
            SeedAssignment.primSetAt_congr_ancestors A _ _ fun i _ =>
              hout_t i _ _ fun ⟨hge, _⟩ => by omega]
          exact hancA j hjlt0
      have hex_L : ∀ (v : Fin (P.numNodes L)), P.InSubtree ℓ₀ u₀ L v →
          ∃ g : P.NodeSeed L,
            P.IsGoodNodeSeed L g (s_t.primSetAt S₁ L ht1 v) ∧
            P.IsGoodNodeSeed L g (s_t.primSetAt S₂ L ht1 v) := by
        intro v hv
        obtain ⟨hinj₁, hb₁, _⟩ := s_t.ancestorsGood_invariants hcard₁ L ht1 v
          (hanc_of hanc₁ (fun j hj w hw hle => (hgood_t j hj w hw hle).1) v hv)
        obtain ⟨hinj₂, hb₂, _⟩ := s_t.ancestorsGood_invariants hcard₂ L ht1 v
          (hanc_of hanc₂ (fun j hj w hw hle => (hgood_t j hj w hw hle).2) v hv)
        have hcp₁ : #(s_t.primSetAt S₁ L ht1 v) = #(s_t.activeAt S₁ L ht1 v) :=
          card_image_of_injOn hinj₁
        have hcp₂ : #(s_t.primSetAt S₂ L ht1 v) = #(s_t.activeAt S₂ L ht1 v) :=
          card_image_of_injOn hinj₂
        exact P.exists_isGoodNodeSeed_pair hcr ht1
          (s_t.primSetAt S₁ L ht1 v) (s_t.primSetAt S₂ L ht1 v)
          (hcp₁ ▸ hb₁.1) (hcp₁ ▸ hb₁.2) (hcp₂ ▸ hb₂.1) (hcp₂ ▸ hb₂.2)
      let f_L : ∀ v : Fin (P.numNodes L), P.InSubtree ℓ₀ u₀ L v → P.NodeSeed L :=
        fun v hv => Classical.choose (hex_L v hv)
      let s_next := updateSeedsAtLevel s_t ℓ₀ u₀ L ht1 f_L
      refine ⟨s_next,
        fun j hj v hnot =>
          (updateSeedsAtLevel_outside s_t ℓ₀ u₀ ht1 f_L hj v hnot).trans (hout_t j hj v hnot),
        ?_⟩
      intro j hj v hsub hjle
      have hp₁ : s_next.primSetAt S₁ j hj v = s_t.primSetAt S₁ j hj v :=
        SeedAssignment.primSetAt_congr_ancestors S₁ hj v fun i hi =>
          updateSeedsAtLevel_ne s_t ℓ₀ u₀ ht1 f_L (hi.le.trans hj) _ (by omega)
      have hp₂ : s_next.primSetAt S₂ j hj v = s_t.primSetAt S₂ j hj v :=
        SeedAssignment.primSetAt_congr_ancestors S₂ hj v fun i hi =>
          updateSeedsAtLevel_ne s_t ℓ₀ u₀ ht1 f_L (hi.le.trans hj) _ (by omega)
      rw [hp₁, hp₂]
      by_cases hjL : j = L
      · subst hjL
        rw [updateSeedsAtLevel_self s_t ℓ₀ u₀ ht1 f_L v hsub]
        exact Classical.choose_spec (hex_L v hsub)
      · rw [updateSeedsAtLevel_ne s_t ℓ₀ u₀ ht1 f_L hj v hjL]
        exact hgood_t j hj v hsub (by omega)
  obtain ⟨s, hout, hgood⟩ := hstep (P.depth - ℓ₀) (by omega)
  exact ⟨s, hout, fun j hj v hsub => hgood j hj v hsub (by omega)⟩

/-- **Subtree good-seed existence (`Algorithm 4` resampling)** on a single set `S`. -/
theorem exists_goodSubtreeSeeds {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (base : P.SeedAssignment) {S : Finset (Fin P.paddedUniv)}
    (hcard0 : P.nLow 0 ≤ #S ∧ #S ≤ P.nHigh 0) {ℓ₀ : ℕ} (hℓ₀ : ℓ₀ ≤ P.depth)
    (u₀ : Fin (P.numNodes ℓ₀))
    (hanc₀ : ∀ (j : ℕ) (hj : j < ℓ₀),
      P.IsGoodNodeSeed j (base.seed j (hj.le.trans hℓ₀) (P.ancestorAt hj.le u₀))
        (base.primSetAt S j (hj.le.trans hℓ₀) (P.ancestorAt hj.le u₀))) :
    ∃ seeds' : P.SeedAssignment,
      (∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
        ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = base.seed j hj v) ∧
      (∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
        P.InSubtree ℓ₀ u₀ j v →
          P.IsGoodNodeSeed j (seeds'.seed j hj v) (seeds'.primSetAt S j hj v)) := by
  obtain ⟨s, hout, hgood⟩ := exists_goodSubtreeSeeds_pair hcr base hcard0 hcard0 hℓ₀ u₀ hanc₀ hanc₀
  exact ⟨s, hout, fun j hj v hsub => (hgood j hj v hsub).1⟩

/-- **Global good-seed existence** for any `S` with `#S ∈ [nLow 0, nHigh 0]`. -/
theorem exists_allGoodSeeds {P : TreeSchedule} (hcr : P.ConcentrationReady)
    {S : Finset (Fin P.paddedUniv)} (hcard0 : P.nLow 0 ≤ #S ∧ #S ≤ P.nHigh 0) :
    ∃ seeds : P.SeedAssignment, seeds.AllGoodSeeds S := by
  let base : P.SeedAssignment :=
    ⟨fun ℓ _ _ => Classical.choice (Fintype.card_pos_iff.mp Fintype.card_pos)⟩
  let u₀ : Fin (P.numNodes 0) := ⟨0, P.numNodes_pos 0⟩
  obtain ⟨seeds, _, hgood⟩ := exists_goodSubtreeSeeds hcr base hcard0 (Nat.zero_le _) u₀
    (fun _ hj => False.elim (by omega))
  exact ⟨seeds, hcard0, fun ℓ hℓ v => hgood ℓ hℓ v ⟨Nat.zero_le ℓ, Subsingleton.elim _ u₀⟩⟩

/-- **Simultaneous pre/post-update localized subtree seed repair**: if `base.AllGoodSeeds S`, `S'`
agrees with `S` off `u₀`, `#S' ∈ [nLow 0, nHigh 0]`, and all levels `< ℓ₀` remain good on `S'`,
resampling only `InSubtree ℓ₀ u₀` yields `seeds'` simultaneously good on both `S` and `S'` so
`rehashSubtree` can run on `S` followed by the normal-path update to `S'`. -/
theorem exists_allGoodSeeds_localized_pair {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (base : P.SeedAssignment) {S S' : Finset (Fin P.paddedUniv)}
    (hbase : base.AllGoodSeeds S) (hcard0' : P.nLow 0 ≤ #S' ∧ #S' ≤ P.nHigh 0)
    {ℓ₀ : ℕ} (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (hdiff : ∀ x : Fin P.paddedUniv, (x ∈ S' ↔ x ∈ S) ∨ base.nodeAt ℓ₀ hℓ₀ x = u₀)
    (hbelow : ∀ (j : ℕ) (hj : j < ℓ₀) (w : Fin (P.numNodes j)),
      P.IsGoodNodeSeed j (base.seed j (hj.le.trans hℓ₀) w)
        (base.primSetAt S' j (hj.le.trans hℓ₀) w)) :
    ∃ seeds' : P.SeedAssignment,
      (∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
        ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = base.seed j hj v) ∧
      seeds'.AllGoodSeeds S ∧ seeds'.AllGoodSeeds S' := by
  obtain ⟨seeds', hout, hsub_good⟩ := exists_goodSubtreeSeeds_pair hcr base hbase.1 hcard0' hℓ₀ u₀
    (fun j hj => hbase.2 j (hj.le.trans hℓ₀) (P.ancestorAt hj.le u₀))
    (fun j hj => hbelow j hj (P.ancestorAt hj.le u₀))
  refine ⟨seeds', hout, ⟨hbase.1, fun j hj w => ?_⟩, ⟨hcard0', fun j hj w => ?_⟩⟩
  · by_cases hsub : P.InSubtree ℓ₀ u₀ j w
    · exact (hsub_good j hj w hsub).1
    · rw [hout j hj w hsub,
        SeedAssignment.primSetAt_congr_ancestors S hj w fun i hi =>
          hout i (hi.le.trans hj) _ (P.not_inSubtree_ancestor_of_not_inSubtree hi.le hsub)]
      exact hbase.2 j hj w
  · by_cases hsub : P.InSubtree ℓ₀ u₀ j w
    · exact (hsub_good j hj w hsub).2
    · rw [hout j hj w hsub,
        SeedAssignment.primSetAt_congr_ancestors S' hj w fun i hi =>
          hout i (hi.le.trans hj) _ (P.not_inSubtree_ancestor_of_not_inSubtree hi.le hsub)]
      by_cases hjlt : j < ℓ₀
      · exact hbelow j hjlt w
      · have h0j : ℓ₀ ≤ j := by omega
        have hanc_ne : P.ancestorAt h0j w ≠ u₀ := fun he => hsub ⟨h0j, he⟩
        have hact_eq : base.activeAt S' j hj w = base.activeAt S j hj w := by
          ext x
          simp only [SeedAssignment.mem_activeAt_iff]
          rcases hdiff x with hiff | hnx0
          · rw [hiff]
          · have hnw : base.nodeAt j hj x ≠ w := fun h =>
              hanc_ne (by rw [← h, base.ancestorAt_nodeAt h0j hj x, hnx0])
            simp [hnw]
        have hp_eq : base.primSetAt S' j hj w = base.primSetAt S j hj w := by
          dsimp only [SeedAssignment.primSetAt]; rw [hact_eq]
        rw [hp_eq]
        exact hbase.2 j hj w

/-! ## Section 2: Canonical bottom-up storage levels and `buildTreeFromSeeds` -/

/-- Bottom-up canonical storage-level construction for `(seeds, S, hgood)`. -/
private noncomputable def canonicalStoreLvlAux {P : TreeSchedule} (seeds : P.SeedAssignment)
    (S : Finset (Fin P.paddedUniv)) (hgood : seeds.AllGoodSeeds S) :
    ∀ (k m : ℕ), m + k = P.depth → 1 ≤ m → m ≤ P.depth →
      { lvl : Fin P.paddedUniv → ℕ //
        (∀ x, x ∉ S → lvl x = 0) ∧
        (∀ x ∈ S, lvl x = 0 ∨ (m ≤ lvl x ∧ lvl x ≤ P.depth)) ∧
        (m = 1 → ∀ x ∈ S, 1 ≤ lvl x ∧ lvl x ≤ P.depth) ∧
        (∀ j, m ≤ j → 2 ≤ j → (hlt : j < P.depth) → ∀ u : Fin (P.numNodes j),
          ((seeds.activeAt S j hlt.le u).filter fun x => lvl x = j).card = P.tableCap j) ∧
        (∀ u : Fin (P.numNodes P.depth),
          ((seeds.activeAt S P.depth le_rfl u).filter fun x => lvl x = P.depth).card =
            P.nLow P.depth) ∧
        (2 ≤ m → ∀ (hm : m ≤ P.depth) (u : Fin (P.numNodes m)),
          ((seeds.activeAt S m hm u).filter fun x => m ≤ lvl x).card = P.nLow m) }
  | 0, m, hsum, _, _ => by
    obtain rfl : m = P.depth := by omega
    have h2d := P.two_le_depth
    let chosen : Fin (P.numNodes P.depth) → Finset (Fin P.paddedUniv) := fun u =>
      takeFinset (seeds.activeAt S P.depth le_rfl u) (P.nLow P.depth)
        (seeds.load_bounds_of_allGoodSeeds hgood le_rfl u).1
    let lvl : Fin P.paddedUniv → ℕ := fun x =>
      if x ∈ S ∧ x ∈ chosen (seeds.nodeAt P.depth le_rfl x) then P.depth else 0
    have hleaf : ∀ u : Fin (P.numNodes P.depth),
        ((seeds.activeAt S P.depth le_rfl u).filter fun x => lvl x = P.depth) = chosen u := by
      intro u; ext x
      simp only [mem_filter, SeedAssignment.mem_activeAt_iff, lvl]
      by_cases hx : x ∈ S ∧ seeds.nodeAt P.depth le_rfl x = u
      · rcases hx with ⟨hxS, hnu⟩
        rw [hnu]
        by_cases hch : x ∈ chosen u
        · simp [hxS, hch]
        · simp [hxS, hch, show 0 ≠ P.depth by omega]
      · constructor
        · rintro ⟨hfalse, _⟩; exact False.elim (hx hfalse)
        · intro hch
          have hact := takeFinset_subset _ _ _ hch
          exact False.elim (hx (SeedAssignment.mem_activeAt_iff.mp hact))
    refine ⟨lvl, fun x hx => ite_eq_right (fun h => hx h.1), fun x _ => ?_, fun _ => by omega,
      fun j _ _ _ => by omega, fun u => by rw [hleaf u, card_takeFinset],
      fun _ hm u => ?_⟩
    · dsimp only [lvl]; split_ifs <;> omega
    · have hfeq : ((seeds.activeAt S P.depth hm u).filter fun x => P.depth ≤ lvl x) =
          (seeds.activeAt S P.depth le_rfl u).filter fun x => lvl x = P.depth :=
        filter_congr fun x _ => by dsimp only [lvl]; split_ifs <;> omega
      rw [hfeq, hleaf u, card_takeFinset]
  | k + 1, m, hsum, h1m, hml => by
    have hmlt : m < P.depth := by omega
    obtain ⟨lvl_next, hout_n, hb_n, _, hinner_n, hleaf_n, hsub_n⟩ :=
      canonicalStoreLvlAux seeds S hgood k (m + 1) (by omega) (by omega) hmlt
    have hm1_2 : 2 ≤ m + 1 := by omega
    let rem : Fin (P.numNodes m) → Finset (Fin P.paddedUniv) := fun u =>
      (seeds.activeAt S m hml u).filter fun x => lvl_next x = 0
    have hrem_card : ∀ u : Fin (P.numNodes m),
        (rem u).card + P.branchFactor m * P.nLow (m + 1) = (seeds.activeAt S m hml u).card := by
      intro u
      have hpart := card_filter_add_card_filter_not (s := seeds.activeAt S m hml u)
        (p := fun x => lvl_next x = 0)
      have hnot : ((seeds.activeAt S m hml u).filter fun x => ¬ lvl_next x = 0) =
          (seeds.activeAt S m hml u).filter fun x => m + 1 ≤ lvl_next x :=
        filter_congr fun x hx => by
          rcases hb_n x (SeedAssignment.mem_activeAt_iff.mp hx).1 with h0 | ⟨hge, _⟩ <;> omega
      rw [hnot, TreeState.activeAt_filter_card_eq_sum_children seeds S hmlt u
        (fun x => m + 1 ≤ lvl_next x)] at hpart
      have hc : ∀ b : Fin (2 ^ P.branchBits m),
          ((seeds.activeAt S (m + 1) hmlt (P.childNodeEquiv m (u, b))).filter
            fun x => m + 1 ≤ lvl_next x).card = P.nLow (m + 1) :=
        fun b => hsub_n hm1_2 hmlt _
      rw [Finset.sum_congr rfl fun b _ => hc b, sum_const, card_univ, Fintype.card_fin,
        smul_eq_mul] at hpart
      exact hpart
    by_cases hm_eq1 : m = 1
    · subst hm_eq1
      let lvl : Fin P.paddedUniv → ℕ := fun x =>
        if lvl_next x ≠ 0 then lvl_next x else if x ∈ S then 1 else 0
      have hgt1 : ∀ x (j : ℕ), 2 ≤ j → (lvl x = j ↔ lvl_next x = j) := fun x j hj2 => by
        dsimp only [lvl]
        by_cases hn0 : lvl_next x ≠ 0
        · rw [ite_eq_left hn0]
        · push Not at hn0; rw [ite_eq_right (by simp [hn0])]; split_ifs <;> omega
      refine ⟨lvl, fun x hx => ?_, fun x hx => ?_, fun _ x hx => ?_, fun j _ hj2 hlt u => ?_,
        fun u => ?_, fun h2 => by omega⟩
      · dsimp only [lvl]; rw [hout_n x hx]; simp [hx]
      · right
        dsimp only [lvl]
        rcases hb_n x hx with h0 | ⟨hge, hle⟩
        · simp [h0, hx, hml]
        · rw [ite_eq_left (by omega)]; exact ⟨by omega, hle⟩
      · dsimp only [lvl]
        rcases hb_n x hx with h0 | ⟨hge, hle⟩
        · simp [h0, hx, hml]
        · rw [ite_eq_left (by omega)]; exact ⟨by omega, hle⟩
      · rw [filter_congr fun x _ => hgt1 x j hj2]
        exact hinner_n j hj2 hj2 hlt u
      · rw [filter_congr fun x _ => hgt1 x P.depth P.two_le_depth]
        exact hleaf_n u
    · have hm2 : 2 ≤ m := by omega
      have hrem_ge : ∀ u : Fin (P.numNodes m), P.tableCap m ≤ (rem u).card := by
        intro u
        have hlo := (seeds.load_bounds_of_allGoodSeeds hgood hml u).1
        have hrc := hrem_card u
        have hcap_eq := P.tableCap_add_branchFactor_mul_nLow_succ hm2 hmlt
        omega
      let chosen : Fin (P.numNodes m) → Finset (Fin P.paddedUniv) := fun u =>
        takeFinset (rem u) (P.tableCap m) (hrem_ge u)
      let lvl : Fin P.paddedUniv → ℕ := fun x =>
        if lvl_next x ≠ 0 then lvl_next x
        else if x ∈ S ∧ x ∈ chosen (seeds.nodeAt m hml x) then m else 0
      have hgt_m : ∀ x (j : ℕ), m < j → (lvl x = j ↔ lvl_next x = j) := fun x j hgt => by
        dsimp only [lvl]
        by_cases hn0 : lvl_next x ≠ 0
        · rw [ite_eq_left hn0]
        · push Not at hn0; rw [ite_eq_right (by simp [hn0])]; split_ifs <;> omega
      have heq_m : ∀ u : Fin (P.numNodes m),
          ((seeds.activeAt S m hml u).filter fun x => lvl x = m) = chosen u := by
        intro u; ext x
        simp only [mem_filter, SeedAssignment.mem_activeAt_iff, lvl]
        by_cases hx : x ∈ S ∧ seeds.nodeAt m hml x = u
        · rcases hx with ⟨hxS, hnu⟩
          rw [hnu]
          by_cases hn0 : lvl_next x ≠ 0
          · rw [ite_eq_left hn0]
            have hge : m + 1 ≤ lvl_next x := by
              rcases hb_n x hxS with h0 | ⟨hg, _⟩
              · exact absurd h0 hn0
              · exact hg
            have hnot_ch : x ∉ chosen u := fun hch =>
              hn0 (mem_filter.mp (takeFinset_subset _ _ _ hch)).2
            simp [show lvl_next x ≠ m by omega, hnot_ch]
          · push Not at hn0
            rw [ite_eq_right (by simp [hn0])]
            by_cases hch : x ∈ chosen u <;> simp [hxS, hch, show 0 ≠ m by omega]
        · constructor
          · rintro ⟨hf, _⟩; exact False.elim (hx hf)
          · intro hch
            have hact := (mem_filter.mp (takeFinset_subset _ _ _ hch)).1
            exact False.elim (hx (SeedAssignment.mem_activeAt_iff.mp hact))
      refine ⟨lvl, fun x hx => ?_, fun x hx => ?_, fun _ => by omega,
        fun j hmj hj2 hlt u => ?_, fun u => ?_, fun _ hm' u => ?_⟩
      · dsimp only [lvl]; rw [hout_n x hx]; simp [hx]
      · dsimp only [lvl]
        rcases hb_n x hx with h0 | ⟨hge, hle⟩
        · rw [ite_eq_right (by simp [h0])]; split_ifs <;> omega
        · rw [ite_eq_left (by omega)]; exact Or.inr ⟨by omega, hle⟩
      · by_cases hjm : j = m
        · subst hjm; rw [heq_m u, card_takeFinset]
        · rw [filter_congr fun x _ => hgt_m x j (by omega)]
          exact hinner_n j (by omega) hj2 hlt u
      · rw [filter_congr fun x _ => hgt_m x P.depth (by omega)]
        exact hleaf_n u
      · have hsplit : ((seeds.activeAt S m hm' u).filter fun x => m ≤ lvl x) =
            chosen u ∪ ((seeds.activeAt S m hml u).filter fun x => m + 1 ≤ lvl_next x) := by
          ext x
          rw [← heq_m u]
          simp only [mem_filter, mem_union]
          constructor
          · rintro ⟨hx, hle⟩
            by_cases he : lvl x = m
            · exact Or.inl ⟨hx, he⟩
            · have hgt : m < lvl x := by omega
              dsimp only [lvl] at hgt
              by_cases hn0 : lvl_next x ≠ 0
              · rw [ite_eq_left hn0] at hgt
                rcases hb_n x (SeedAssignment.mem_activeAt_iff.mp hx).1 with h0 | ⟨hg, _⟩
                · exact absurd h0 hn0
                · exact Or.inr ⟨hx, hg⟩
              · push Not at hn0
                rw [ite_eq_right (by simp [hn0])] at hgt
                split_ifs at hgt <;> omega
          · rintro (⟨hx, he⟩ | ⟨hx, hg⟩)
            · exact ⟨hx, by omega⟩
            · refine ⟨hx, ?_⟩
              dsimp only [lvl]; rw [ite_eq_left (by omega)]; omega
        have hdisj : Disjoint (chosen u)
            ((seeds.activeAt S m hml u).filter fun x => m + 1 ≤ lvl_next x) := by
          rw [Finset.disjoint_left]; intro x hch hflt
          have h0 := (mem_filter.mp (takeFinset_subset _ _ _ hch)).2
          have := (mem_filter.mp hflt).2; omega
        have hchildren : ((seeds.activeAt S m hml u).filter
            fun x => m + 1 ≤ lvl_next x).card = P.branchFactor m * P.nLow (m + 1) := by
          rw [TreeState.activeAt_filter_card_eq_sum_children seeds S hmlt u]
          have hc : ∀ b : Fin (2 ^ P.branchBits m),
              ((seeds.activeAt S (m + 1) hmlt (P.childNodeEquiv m (u, b))).filter
                fun x => m + 1 ≤ lvl_next x).card = P.nLow (m + 1) :=
            fun b => hsub_n hm1_2 hmlt _
          simp only [hc, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, branchFactor]
        rw [hsplit, card_union_of_disjoint hdisj, card_takeFinset, hchildren,
          P.tableCap_add_branchFactor_mul_nLow_succ hm2 hmlt]

/-- Canonical bottom-up storage-level function `Fin P.paddedUniv → ℕ` for `(seeds, S, hgood)`. -/
noncomputable def canonicalStoreLvl {P : TreeSchedule} (seeds : P.SeedAssignment)
    (S : Finset (Fin P.paddedUniv)) (hgood : seeds.AllGoodSeeds S) : Fin P.paddedUniv → ℕ :=
  (canonicalStoreLvlAux seeds S hgood (P.depth - 1) 1 (by have := P.two_le_depth; omega)
    le_rfl (Nat.one_le_of_lt P.two_le_depth)).1

theorem validStoreLvl_canonicalStoreLvl {P : TreeSchedule} (seeds : P.SeedAssignment)
    (S : Finset (Fin P.paddedUniv)) (hgood : seeds.AllGoodSeeds S) :
    ValidStoreLvl seeds S (canonicalStoreLvl seeds S hgood) := by
  let res := canonicalStoreLvlAux seeds S hgood (P.depth - 1) 1
    (by have := P.two_le_depth; omega) le_rfl (Nat.one_le_of_lt P.two_le_depth)
  exact
    { bounds := res.2.2.2.1 rfl
      outside := res.2.1
      inner_card := fun ℓ h2 hlt u => res.2.2.2.2.1 ℓ (by omega) h2 hlt u
      leaf_card := res.2.2.2.2.2.1 }

private noncomputable def nodePayloadOf {P : TreeSchedule} (d : P.PaddedDict)
    (seeds : P.SeedAssignment) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ)) (k : Fin (2 ^ P.idBits ℓ)) :
    Fin (P.quotUniv ℓ) × Fin P.valBound :=
  if h : ∃ x ∈ seeds.activeAt (P.paddedDom d) ℓ hℓ u, seeds.idAt ℓ h1 hℓ x = k then
    let x := Classical.choose h
    (seeds.quotAt ℓ h1 hℓ x, (d x).getD ⟨0, P.val_pos⟩)
  else
    (⟨0, P.quotUniv_pos ℓ⟩, ⟨0, P.val_pos⟩)

private theorem nodePayloadOf_eq {P : TreeSchedule} {d : P.PaddedDict}
    {seeds : P.SeedAssignment} (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    {x : Fin P.paddedUniv} {v : Fin P.valBound} (hdx : d x = some v)
    (hnx : seeds.nodeAt ℓ hℓ x = u) :
    nodePayloadOf d seeds ℓ h1 hℓ u (seeds.idAt ℓ h1 hℓ x) =
      (seeds.quotAt ℓ h1 hℓ x, v) := by
  have hx_act : x ∈ seeds.activeAt (P.paddedDom d) ℓ hℓ u :=
    SeedAssignment.mem_activeAt_iff.mpr ⟨(P.mem_paddedDom_iff d x).mpr (by simp [hdx]), hnx⟩
  have hex : ∃ y ∈ seeds.activeAt (P.paddedDom d) ℓ hℓ u,
      seeds.idAt ℓ h1 hℓ y = seeds.idAt ℓ h1 hℓ x := ⟨x, hx_act, rfl⟩
  dsimp only [nodePayloadOf]
  rw [dite_eq_left hex]
  obtain ⟨hy_act, hid_eq⟩ := Classical.choose_spec hex
  have hyx : Classical.choose hex = x :=
    seeds.injOn_idAt_activeAt hgood h1 hℓ u hy_act hx_act hid_eq
  rw [hyx, hdx]
  rfl

private noncomputable def waitPrevIdOf {P : TreeSchedule} (S : Finset (Fin P.paddedUniv))
    (seeds : P.SeedAssignment) (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth)
    (u : Fin (P.numNodes ℓ)) (k : Fin (2 ^ P.idBits ℓ)) : Fin (2 ^ P.idBits (ℓ - 1)) :=
  if h : ∃ x ∈ seeds.activeAt S ℓ hℓ u, seeds.idAt ℓ (by omega) hℓ x = k then
    seeds.idAt (ℓ - 1) (by omega) (by omega) (Classical.choose h)
  else
    ⟨0, Nat.two_pow_pos _⟩

private theorem waitPrevIdOf_eq {P : TreeSchedule} {S : Finset (Fin P.paddedUniv)}
    {seeds : P.SeedAssignment} (hgood : seeds.AllGoodSeeds S)
    {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ))
    {x : Fin P.paddedUniv} (hx : x ∈ seeds.activeAt S ℓ hℓ u) :
    waitPrevIdOf S seeds ℓ h2 hℓ u (seeds.idAt ℓ (by omega) hℓ x) =
      seeds.idAt (ℓ - 1) (by omega) (by omega) x := by
  have hex : ∃ y ∈ seeds.activeAt S ℓ hℓ u,
      seeds.idAt ℓ (by omega) hℓ y = seeds.idAt ℓ (by omega) hℓ x := ⟨x, hx, rfl⟩
  dsimp only [waitPrevIdOf]
  rw [dite_eq_left hex]
  obtain ⟨hy_act, hid_eq⟩ := Classical.choose_spec hex
  rw [seeds.injOn_idAt_activeAt hgood (by omega) hℓ u hy_act hx hid_eq]

/-- Construct a single `RootNode` from `(d, seeds, hgood, storeLvl)`. -/
noncomputable def buildRootOfStoreLvl {P : TreeSchedule} (d : P.PaddedDict)
    (seeds : P.SeedAssignment) (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds (P.paddedDom d) storeLvl)
    (u₁ : Fin (P.numNodes 1)) : P.RootNode :=
  let h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
  { seed := seeds.seed 1 h1d u₁
    table := StorageTable.ofFinset
      (((seeds.activeAt (P.paddedDom d) 1 h1d u₁).filter fun x => storeLvl x = 1).image
        (seeds.idAt 1 le_rfl h1d))
      (hvsl.root_card_le hgood u₁) (P.quotUniv_pos 1) P.val_pos
      (nodePayloadOf d seeds 1 le_rfl h1d u₁) }

@[simp]
theorem seed_buildRootOfStoreLvl {P : TreeSchedule} (d : P.PaddedDict)
    (seeds : P.SeedAssignment) (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds (P.paddedDom d) storeLvl)
    (u₁ : Fin (P.numNodes 1)) :
    (buildRootOfStoreLvl d seeds hgood hvsl u₁).seed =
      seeds.seed 1 (Nat.one_le_of_lt P.two_le_depth) u₁ := by
  rfl

@[simp]
theorem dom_buildRootOfStoreLvl {P : TreeSchedule} (d : P.PaddedDict)
    (seeds : P.SeedAssignment) (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds (P.paddedDom d) storeLvl)
    (u₁ : Fin (P.numNodes 1)) :
    (buildRootOfStoreLvl d seeds hgood hvsl u₁).table.tableMeta.dom =
      ((seeds.activeAt (P.paddedDom d) 1 (Nat.one_le_of_lt P.two_le_depth) u₁).filter
        fun x => storeLvl x = 1).image
        (seeds.idAt 1 le_rfl (Nat.one_le_of_lt P.two_le_depth)) := by
  dsimp only [buildRootOfStoreLvl]; rw [StorageTable.dom_ofFinset]

theorem query_buildRootOfStoreLvl {P : TreeSchedule} {d : P.PaddedDict}
    {seeds : P.SeedAssignment} (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds (P.paddedDom d) storeLvl)
    (u₁ : Fin (P.numNodes 1)) {x : Fin P.paddedUniv} {v : Fin P.valBound}
    (hdx : d x = some v)
    (hnx : seeds.nodeAt 1 (Nat.one_le_of_lt P.two_le_depth) x = u₁) (hsl : storeLvl x = 1) :
    (buildRootOfStoreLvl d seeds hgood hvsl u₁).table.query
      (seeds.idAt 1 le_rfl (Nat.one_le_of_lt P.two_le_depth) x) =
      some (seeds.quotAt 1 le_rfl (Nat.one_le_of_lt P.two_le_depth) x, v) := by
  let h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
  have hmem : seeds.idAt 1 le_rfl h1d x ∈
      ((seeds.activeAt (P.paddedDom d) 1 h1d u₁).filter fun y => storeLvl y = 1).image
        (seeds.idAt 1 le_rfl h1d) :=
    mem_image_of_mem _ (mem_filter.mpr
      ⟨SeedAssignment.mem_activeAt_iff.mpr
        ⟨(P.mem_paddedDom_iff d x).mpr (by simp [hdx]), hnx⟩, hsl⟩)
  dsimp only [buildRootOfStoreLvl]
  rw [StorageTable.query_ofFinset, ite_eq_left hmem, nodePayloadOf_eq hgood le_rfl h1d u₁ hdx hnx]

private noncomputable def buildWaitOfStoreLvl {P : TreeSchedule} (S : Finset (Fin P.paddedUniv))
    (seeds : P.SeedAssignment) (hgood : seeds.AllGoodSeeds S)
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds S storeLvl)
    (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hℓ : ℓ ≤ P.depth) (u : Fin (P.numNodes ℓ)) :
    WaitingList (P.idBits ℓ) (P.idBits (ℓ - 1)) (P.waitCap ℓ) :=
  WaitingList.ofFinset
    (((seeds.activeAt S ℓ hℓ u).filter fun x => storeLvl x < ℓ).image
      (seeds.idAt ℓ (by omega) hℓ))
    (hvsl.wait_card_le hgood h2 hℓ u)
    (waitPrevIdOf S seeds ℓ h2 hℓ u)

/-- Construct a single `InnerNode ℓ` from `(d, seeds, hgood, storeLvl)`. -/
noncomputable def buildInnerOfStoreLvl {P : TreeSchedule} (d : P.PaddedDict)
    (seeds : P.SeedAssignment) (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds (P.paddedDom d) storeLvl)
    (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth) (u : Fin (P.numNodes ℓ)) : P.InnerNode ℓ :=
  let S_id := ((seeds.activeAt (P.paddedDom d) ℓ hlt.le u).filter fun x => storeLvl x = ℓ).image
    (seeds.idAt ℓ (by omega) hlt.le)
  have hcard : S_id.card = P.tableCap ℓ := by
    rw [card_image_of_injOn ((seeds.injOn_idAt_activeAt hgood (by omega) hlt.le u).mono
      (filter_subset _ _)), hvsl.inner_card ℓ h2 hlt u]
  { seed := seeds.seed ℓ hlt.le u
    wait := buildWaitOfStoreLvl (P.paddedDom d) seeds hgood hvsl ℓ h2 hlt.le u
    table := StorageTable.ofFinset S_id hcard.le (P.quotUniv_pos ℓ) P.val_pos
      (nodePayloadOf d seeds ℓ (by omega) hlt.le u) }

@[simp]
theorem seed_buildInnerOfStoreLvl {P : TreeSchedule} (d : P.PaddedDict)
    (seeds : P.SeedAssignment) (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds (P.paddedDom d) storeLvl)
    (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth) (u : Fin (P.numNodes ℓ)) :
    (buildInnerOfStoreLvl d seeds hgood hvsl ℓ h2 hlt u).seed = seeds.seed ℓ hlt.le u := by
  rfl

@[simp]
theorem dom_buildInnerOfStoreLvl {P : TreeSchedule} (d : P.PaddedDict)
    (seeds : P.SeedAssignment) (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds (P.paddedDom d) storeLvl)
    (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth) (u : Fin (P.numNodes ℓ)) :
    (buildInnerOfStoreLvl d seeds hgood hvsl ℓ h2 hlt u).table.tableMeta.dom =
      ((seeds.activeAt (P.paddedDom d) ℓ hlt.le u).filter fun x => storeLvl x = ℓ).image
        (seeds.idAt ℓ (by omega) hlt.le) := by
  dsimp only [buildInnerOfStoreLvl]; rw [StorageTable.dom_ofFinset]

theorem card_dom_buildInnerOfStoreLvl {P : TreeSchedule} (d : P.PaddedDict)
    (seeds : P.SeedAssignment) (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds (P.paddedDom d) storeLvl)
    (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth) (u : Fin (P.numNodes ℓ)) :
    (buildInnerOfStoreLvl d seeds hgood hvsl ℓ h2 hlt u).table.tableMeta.dom.card =
      P.tableCap ℓ := by
  rw [dom_buildInnerOfStoreLvl, card_image_of_injOn
    ((seeds.injOn_idAt_activeAt hgood (by omega) hlt.le u).mono (filter_subset _ _)),
    hvsl.inner_card ℓ h2 hlt u]

theorem query_buildInnerOfStoreLvl {P : TreeSchedule} {d : P.PaddedDict}
    {seeds : P.SeedAssignment} (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds (P.paddedDom d) storeLvl)
    {ℓ : ℕ} (h1 : 1 ≤ ℓ) (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth) (u : Fin (P.numNodes ℓ))
    {x : Fin P.paddedUniv} {v : Fin P.valBound} (hdx : d x = some v)
    (hnx : seeds.nodeAt ℓ hlt.le x = u) (hsl : storeLvl x = ℓ) :
    (buildInnerOfStoreLvl d seeds hgood hvsl ℓ h2 hlt u).table.query
      (seeds.idAt ℓ h1 hlt.le x) =
      some (seeds.quotAt ℓ h1 hlt.le x, v) := by
  have hmem : seeds.idAt ℓ h1 hlt.le x ∈
      ((seeds.activeAt (P.paddedDom d) ℓ hlt.le u).filter fun y => storeLvl y = ℓ).image
        (seeds.idAt ℓ h1 hlt.le) :=
    mem_image_of_mem _ (mem_filter.mpr
      ⟨SeedAssignment.mem_activeAt_iff.mpr
        ⟨(P.mem_paddedDom_iff d x).mpr (by simp [hdx]), hnx⟩, hsl⟩)
  dsimp only [buildInnerOfStoreLvl]
  rw [StorageTable.query_ofFinset, ite_eq_left hmem, nodePayloadOf_eq hgood h1 hlt.le u hdx hnx]

@[simp]
theorem wait_dom_buildInnerOfStoreLvl {P : TreeSchedule} (d : P.PaddedDict)
    (seeds : P.SeedAssignment) (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds (P.paddedDom d) storeLvl)
    (ℓ : ℕ) (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth) (u : Fin (P.numNodes ℓ)) :
    (buildInnerOfStoreLvl d seeds hgood hvsl ℓ h2 hlt u).wait.dom =
      ((seeds.activeAt (P.paddedDom d) ℓ hlt.le u).filter fun x => storeLvl x < ℓ).image
        (seeds.idAt ℓ (by omega) hlt.le) := by
  dsimp only [buildInnerOfStoreLvl, buildWaitOfStoreLvl]; rw [WaitingList.dom_ofFinset]

theorem wait_lookup_buildInnerOfStoreLvl {P : TreeSchedule} {d : P.PaddedDict}
    {seeds : P.SeedAssignment} (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds (P.paddedDom d) storeLvl)
    {ℓ : ℕ} (h2 : 2 ≤ ℓ) (hlt : ℓ < P.depth) (u : Fin (P.numNodes ℓ))
    {x : Fin P.paddedUniv} (hx : x ∈ seeds.activeAt (P.paddedDom d) ℓ hlt.le u)
    (hsl : storeLvl x < ℓ) :
    (buildInnerOfStoreLvl d seeds hgood hvsl ℓ h2 hlt u).wait.lookup
      (seeds.idAt ℓ (by omega) hlt.le x) =
      some (seeds.idAt (ℓ - 1) (by omega) (by omega) x) := by
  have hmem : seeds.idAt ℓ (by omega) hlt.le x ∈
      ((seeds.activeAt (P.paddedDom d) ℓ hlt.le u).filter fun y => storeLvl y < ℓ).image
        (seeds.idAt ℓ (by omega) hlt.le) :=
    mem_image_of_mem _ (mem_filter.mpr ⟨hx, hsl⟩)
  dsimp only [buildInnerOfStoreLvl, buildWaitOfStoreLvl]
  rw [WaitingList.lookup_ofFinset, ite_eq_left hmem, waitPrevIdOf_eq hgood h2 hlt.le u hx]

private noncomputable def buildLeafOfStoreLvl {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (d : P.PaddedDict) (seeds : P.SeedAssignment) (hgood : seeds.AllGoodSeeds (P.paddedDom d))
    {storeLvl : Fin P.paddedUniv → ℕ} (hvsl : ValidStoreLvl seeds (P.paddedDom d) storeLvl)
    (u : Fin (P.numNodes P.depth)) : P.LeafNode :=
  let h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
  let S_id := ((seeds.activeAt (P.paddedDom d) P.depth le_rfl u).filter
    fun x => storeLvl x = P.depth).image (seeds.idAt P.depth h1d le_rfl)
  have hcard : S_id.card = P.nLow P.depth := by
    rw [card_image_of_injOn ((seeds.injOn_idAt_activeAt hgood h1d le_rfl u).mono
      (filter_subset _ _)), hvsl.leaf_card u]
  LeafNode.ofFinset scheme (seeds.seed P.depth le_rfl u)
    (buildWaitOfStoreLvl (P.paddedDom d) seeds hgood hvsl P.depth P.two_le_depth le_rfl u)
    S_id hcard (nodePayloadOf d seeds P.depth h1d le_rfl u)

/-- Build a full `TreeState` from any `d : P.PaddedDict`, `sentCount : ℕ`, and `seeds` satisfying
`seeds.AllGoodSeeds (P.paddedDom d)`. -/
noncomputable def buildTreeFromSeeds
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (d : P.PaddedDict) (sentCount : ℕ) (seeds : P.SeedAssignment)
    (hgood : seeds.AllGoodSeeds (P.paddedDom d)) : P.TreeState :=
  let hvsl := validStoreLvl_canonicalStoreLvl seeds (P.paddedDom d) hgood
  { topSeed := seeds.seed 0 (Nat.zero_le _) ⟨0, P.numNodes_pos 0⟩
    roots := buildRootOfStoreLvl d seeds hgood hvsl
    inner := fun ℓ h2 hlt u => buildInnerOfStoreLvl d seeds hgood hvsl ℓ h2 hlt u
    leaves := buildLeafOfStoreLvl scheme d seeds hgood hvsl
    sentCount := sentCount }

@[simp]
theorem seeds_buildTreeFromSeeds {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (d : P.PaddedDict) (sentCount : ℕ) (seeds : P.SeedAssignment)
    (hgood : seeds.AllGoodSeeds (P.paddedDom d)) :
    (P.buildTreeFromSeeds scheme d sentCount seeds hgood).seeds = seeds := by
  ext ℓ hℓ u
  by_cases h0 : ℓ = 0
  · subst h0
    rw [TreeState.seeds_zero]
    dsimp only [buildTreeFromSeeds]
    rw [Subsingleton.elim u ⟨0, P.numNodes_pos 0⟩]
  · by_cases h1 : ℓ = 1
    · subst h1; simp [buildTreeFromSeeds]
    · by_cases hlt : ℓ < P.depth
      · simp [TreeState.seeds_inner _ (by omega) hlt hℓ, buildTreeFromSeeds]
      · have hd : ℓ = P.depth := by omega
        subst hd; simp [buildTreeFromSeeds, buildLeafOfStoreLvl]

@[simp]
theorem sentCount_buildTreeFromSeeds {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (d : P.PaddedDict) (sentCount : ℕ) (seeds : P.SeedAssignment)
    (hgood : seeds.AllGoodSeeds (P.paddedDom d)) :
    (P.buildTreeFromSeeds scheme d sentCount seeds hgood).sentCount = sentCount := by
  rfl

/-- **`buildTreeFromSeeds` establishes `WellFormedPadded`**. -/
theorem wellFormedPadded_buildTreeFromSeeds {P : TreeSchedule}
    (scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth))
    (d : P.PaddedDict) (sentCount : ℕ) (seeds : P.SeedAssignment)
    (hgood : seeds.AllGoodSeeds (P.paddedDom d)) :
    (P.buildTreeFromSeeds scheme d sentCount seeds hgood).WellFormedPadded scheme d
      (canonicalStoreLvl seeds (P.paddedDom d) hgood) := by
  set st := P.buildTreeFromSeeds scheme d sentCount seeds hgood
  have hvsl := validStoreLvl_canonicalStoreLvl seeds (P.paddedDom d) hgood
  have hseeds : st.seeds = seeds := P.seeds_buildTreeFromSeeds scheme d sentCount seeds hgood
  refine
    { goodSeeds := by rw [hseeds]; exact hgood
      storeLvl_bounds := hvsl.bounds
      storeLvl_outside := hvsl.outside
      dom_eq := fun ℓ h1 hℓ u => by
        rw [hseeds]
        by_cases h_one : ℓ = 1
        · subst h_one; simp [st, buildTreeFromSeeds]
        · by_cases hlt : ℓ < P.depth
          · rw [TreeState.nodeDom_inner st h1 (by omega) hlt hℓ]
            simp [st, buildTreeFromSeeds]
          · have hd : ℓ = P.depth := by omega
            subst hd; simp [st, buildTreeFromSeeds, buildLeafOfStoreLvl]
      query_eq_of_storeLvl := fun ℓ h1 hℓ u x v hdx hnx hslx => by
        rw [hseeds] at hnx ⊢
        by_cases h_one : ℓ = 1
        · subst h_one
          rw [TreeState.nodeQuery_one]
          exact query_buildRootOfStoreLvl hgood hvsl u hdx hnx hslx
        · by_cases hlt : ℓ < P.depth
          · rw [TreeState.nodeQuery_inner scheme st h1 (by omega) hlt hℓ]
            exact query_buildInnerOfStoreLvl hgood hvsl h1 (by omega) hlt u hdx hnx hslx
          · have hd : ℓ = P.depth := by omega
            subst hd
            rw [TreeState.nodeQuery_depth]
            have hx_mem : seeds.idAt P.depth h1 le_rfl x ∈
                ((seeds.activeAt (P.paddedDom d) P.depth le_rfl u).filter
                  fun y => canonicalStoreLvl seeds (P.paddedDom d) hgood y = P.depth).image
                  (seeds.idAt P.depth h1 le_rfl) :=
              mem_image_of_mem _ (mem_filter.mpr
                ⟨SeedAssignment.mem_activeAt_iff.mpr
                  ⟨(P.mem_paddedDom_iff d x).mpr (by simp [hdx]), hnx⟩, hslx⟩)
            dsimp only [st, buildTreeFromSeeds, buildLeafOfStoreLvl]
            rw [LeafNode.query_ofFinset, ite_eq_left hx_mem,
              nodePayloadOf_eq hgood h1 le_rfl u hdx hnx]
      inner_full := fun ℓ h2 hlt u => card_dom_buildInnerOfStoreLvl d seeds hgood hvsl ℓ h2 hlt u
      wait_dom_eq := fun ℓ h2 hℓ u => by
        rw [hseeds]
        by_cases hlt : ℓ < P.depth
        · rw [TreeState.nodeWait_inner st h2 hlt hℓ]
          simp [st, buildTreeFromSeeds]
        · have hd : ℓ = P.depth := by omega
          subst hd
          simp [st, buildTreeFromSeeds, buildLeafOfStoreLvl, buildWaitOfStoreLvl]
      wait_lookup_eq := fun ℓ h2 hℓ u x hx hslx => by
        rw [hseeds] at hx ⊢
        by_cases hlt : ℓ < P.depth
        · rw [TreeState.nodeWait_inner st h2 hlt hℓ]
          exact wait_lookup_buildInnerOfStoreLvl hgood hvsl h2 hlt u hx hslx
        · have hd : ℓ = P.depth := by omega
          subst hd
          rw [TreeState.nodeWait_depth]
          have hx_mem : seeds.idAt P.depth (by omega) le_rfl x ∈
              ((seeds.activeAt (P.paddedDom d) P.depth le_rfl u).filter
                fun y => canonicalStoreLvl seeds (P.paddedDom d) hgood y < P.depth).image
                (seeds.idAt P.depth (by omega) le_rfl) :=
            mem_image_of_mem _ (mem_filter.mpr ⟨hx, hslx⟩)
          dsimp only [st, buildTreeFromSeeds, buildLeafOfStoreLvl]
          rw [LeafNode.wait_ofFinset]
          dsimp only [buildWaitOfStoreLvl]
          rw [WaitingList.lookup_ofFinset, ite_eq_left hx_mem,
            waitPrevIdOf_eq hgood P.two_le_depth le_rfl u hx] }

end TreeSchedule

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
