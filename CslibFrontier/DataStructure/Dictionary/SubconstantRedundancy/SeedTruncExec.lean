/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeModel
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.SingleNodeExec

/-!
# Level-Truncated Multi-Level `OracleComp` Seed Resampling (`Algorithm 4`)

This file defines single-key sentinel-padded update chains (`PaddedStep`, `ChainSteps`),
level-truncated seed assignments (`TruncSeeds`, `GoodTrunc`), and the top-down `OracleComp`
seed-resampling programs (`initTrunc`, `stepTrunc`, `runTruncSteps`, `execTruncHistory`,
`execSeedSteps`), together with their support goodness, `InSubtree` locality, and worst-case query
budgets, for the subconstant-redundancy dictionary tree of Tianxiao Li, Jingxun Liang, Huacheng Yu,
and Renfei Zhou, *Dynamic Dictionary with Subconstant Wasted Bits per Key*
([LiLiangYuZhou2024, Section 5.5, Algorithm 4];
[arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF p. 34 / printed p. 33).

## Main definitions

* `TreeSchedule.PaddedStep`, `TreeSchedule.ChainSteps`: single-key sentinel-padded dictionary update
  steps and chained step histories.
* `TreeSchedule.TruncSeeds`, `TreeSchedule.GoodTrunc`: level-truncated seed assignments up to level
  `ℓ ≤ depth` and their goodness invariant.
* `TreeSchedule.initTrunc`, `TreeSchedule.stepTrunc`, `TreeSchedule.runTruncSteps`,
  `TreeSchedule.execTruncHistory`, `TreeSchedule.execSeedSteps`: top-down `OracleComp` seed
  initialization and localized subtree seed resampling (`Algorithm 4`).

## Main results

* `TreeSchedule.stepTrunc_of_goodTrunc_post`: when existing seeds remain good after a step,
  `stepTrunc` reduces to `pure (ts, fun _ => false)` (`0` oracle calls).
* `TreeSchedule.mem_support_initTrunc`, `TreeSchedule.mem_support_stepTrunc`,
  `TreeSchedule.stepTrunc_seed_eq_outside_inSubtree`: seed goodness and `InSubtree ℓ₀ u₀` locality
  on every supported outcome.
* `TreeSchedule.isQueryBounded_execTruncHistory`,
  `TreeSchedule.expectedCost_levelRehashCost_ne_top`: pathwise query budgets and finiteness of
  levelwise expected rehash counts.

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

/-! ## Section 1: Padded Update Chains and Level-Truncated Seed Assignments -/

/-- Root-level occupancy window `P.nLow 0 ≤ #S ≤ P.nHigh 0` on `S : Finset (Fin P.paddedUniv)`. -/
abbrev validRootBounds (P : TreeSchedule) (S : Finset (Fin P.paddedUniv)) : Prop :=
  P.nLow 0 ≤ #S ∧ #S ≤ P.nHigh 0

/-- Single-key sentinel-padded dictionary update step (`Insert.insert key preSet` or
`preSet.erase key`) preserving `validRootBounds`. -/
structure PaddedStep (P : TreeSchedule) where
  /-- Active padded key set before the step. -/
  preSet : Finset (Fin P.paddedUniv)
  /-- Active padded key set after the step. -/
  postSet : Finset (Fin P.paddedUniv)
  /-- Single padded key inserted or erased at this step. -/
  key : Fin P.paddedUniv
  /-- Root occupancy window before the step. -/
  pre_bounds : P.validRootBounds preSet
  /-- Root occupancy window after the step. -/
  post_bounds : P.validRootBounds postSet
  /-- Symmetric-difference witness: `postSet` and `preSet` agree away from `key`. -/
  diff_key : ∀ y : Fin P.paddedUniv, (y ∈ postSet ↔ y ∈ preSet) ∨ y = key

/-- Chained sequence of `PaddedStep`s starting from initial padded key set `S₀`. -/
@[expose]
def ChainSteps {P : TreeSchedule} : Finset (Fin P.paddedUniv) → List P.PaddedStep → Prop
  | _, [] => True
  | S, st :: sts => st.preSet = S ∧ ChainSteps st.postSet sts

/-- Canonical fallback `SeedAssignment` used to witness seed-independent level-`0` routing. -/
noncomputable def defaultSeeds (P : TreeSchedule) : P.SeedAssignment where
  seed _ _ _ := Classical.choice (Fintype.card_pos_iff.mp Fintype.card_pos)

/-- Top-level primitive-ID image of `S : Finset (Fin P.paddedUniv)` (independent of seeds). -/
noncomputable def primSetZero (P : TreeSchedule) (S : Finset (Fin P.paddedUniv)) :
    Finset (P.PrimId 0) :=
  P.defaultSeeds.primSetAt S 0 (Nat.zero_le _) ⟨0, P.numNodes_pos 0⟩

theorem SeedAssignment.primSetAt_zero {P : TreeSchedule} (seeds : P.SeedAssignment)
    (S : Finset (Fin P.paddedUniv)) (h0 : 0 ≤ P.depth) (u : Fin (P.numNodes 0)) :
    seeds.primSetAt S 0 h0 u = P.primSetZero S := by
  dsimp only [primSetZero]
  rw [Subsingleton.elim u ⟨0, P.numNodes_pos 0⟩]
  exact SeedAssignment.primSetAt_congr_ancestors S h0 _ fun _ hj =>
    False.elim (Nat.not_lt_zero _ hj)

theorem validPrimBounds_primSetZero_of_root {P : TreeSchedule} {S : Finset (Fin P.paddedUniv)}
    (hS : P.validRootBounds S) :
    P.validPrimBounds 0 (P.primSetZero S) := by
  obtain ⟨hinj, hb, _⟩ := P.defaultSeeds.ancestorsGood_invariants hS 0 (Nat.zero_le _)
    ⟨0, P.numNodes_pos 0⟩ fun _ hj => False.elim (Nat.not_lt_zero _ hj)
  have hcard : #(P.primSetZero S) = #(P.defaultSeeds.activeAt S 0 (Nat.zero_le _)
      ⟨0, P.numNodes_pos 0⟩) := card_image_of_injOn hinj
  exact ⟨hcard ▸ hb.1, hcard ▸ hb.2⟩

/-- Truncated forest seed assignment storing node seeds at levels `0 ≤ j ≤ ℓ`. -/
@[ext]
structure TruncSeeds (P : TreeSchedule) (ℓ : ℕ) where
  /-- Per-node hash seed at `(j, u)` for `j ≤ ℓ` (`j ≤ P.depth`). -/
  seed : ∀ (j : ℕ), j ≤ ℓ → j ≤ P.depth → Fin (P.numNodes j) → P.NodeSeed j

/-- Extend `ts : P.TruncSeeds ℓ` to a full `SeedAssignment` via an arbitrary fallback above `ℓ`. -/
noncomputable def TruncSeeds.toFull {P : TreeSchedule} {ℓ : ℕ} (ts : P.TruncSeeds ℓ) :
    P.SeedAssignment where
  seed j hj u :=
    if h : j ≤ ℓ then ts.seed j h hj u
    else Classical.choice (Fintype.card_pos_iff.mp Fintype.card_pos)

@[simp]
theorem TruncSeeds.toFull_seed {P : TreeSchedule} {ℓ j : ℕ} (ts : P.TruncSeeds ℓ)
    (hjℓ : j ≤ ℓ) (hj : j ≤ P.depth) (u : Fin (P.numNodes j)) :
    ts.toFull.seed j hj u = ts.seed j hjℓ hj u := by
  dsimp only [toFull]; rw [dite_eq_left hjℓ]

/-- Restrict `ts : P.TruncSeeds (ℓ + 1)` to levels `0 ≤ j ≤ ℓ`. -/
def TruncSeeds.restrict {P : TreeSchedule} {ℓ : ℕ} (ts : P.TruncSeeds (ℓ + 1)) :
    P.TruncSeeds ℓ where
  seed j hjℓ hj u := ts.seed j (Nat.le_succ_of_le hjℓ) hj u

/-- Extract the level-`(ℓ + 1)` seed row from `ts : P.TruncSeeds (ℓ + 1)`. -/
def TruncSeeds.lastRow {P : TreeSchedule} {ℓ : ℕ} (hℓ1 : ℓ + 1 ≤ P.depth)
    (ts : P.TruncSeeds (ℓ + 1)) : Fin (P.numNodes (ℓ + 1)) → P.NodeSeed (ℓ + 1) :=
  fun v => ts.seed (ℓ + 1) le_rfl hℓ1 v

/-- Extend `anc : P.TruncSeeds ℓ` with a level-`(ℓ + 1)` seed row. -/
def TruncSeeds.extend {P : TreeSchedule} {ℓ : ℕ} (anc : P.TruncSeeds ℓ)
    (row : Fin (P.numNodes (ℓ + 1)) → P.NodeSeed (ℓ + 1)) : P.TruncSeeds (ℓ + 1) where
  seed j hjℓ1 hj u :=
    if h : j ≤ ℓ then anc.seed j h hj u
    else
      have heq : j = ℓ + 1 := by omega
      Eq.ndrec (motive := fun m => Fin (P.numNodes m) → P.NodeSeed m) row heq.symm u

@[simp]
theorem TruncSeeds.extend_seed_le {P : TreeSchedule} {ℓ j : ℕ} (anc : P.TruncSeeds ℓ)
    (row : Fin (P.numNodes (ℓ + 1)) → P.NodeSeed (ℓ + 1)) (hj : j ≤ ℓ) (hjd : j ≤ P.depth)
    (u : Fin (P.numNodes j)) :
    (anc.extend row).seed j (Nat.le_succ_of_le hj) hjd u = anc.seed j hj hjd u := by
  dsimp only [extend]; rw [dite_eq_left hj]

@[simp]
theorem TruncSeeds.extend_seed_succ {P : TreeSchedule} {ℓ : ℕ} (anc : P.TruncSeeds ℓ)
    (row : Fin (P.numNodes (ℓ + 1)) → P.NodeSeed (ℓ + 1)) (hℓ1 : ℓ + 1 ≤ P.depth)
    (v : Fin (P.numNodes (ℓ + 1))) :
    (anc.extend row).seed (ℓ + 1) le_rfl hℓ1 v = row v := by
  dsimp only [extend]; rw [dite_eq_right (by omega)]

@[simp]
theorem TruncSeeds.restrict_extend {P : TreeSchedule} {ℓ : ℕ} (anc : P.TruncSeeds ℓ)
    (row : Fin (P.numNodes (ℓ + 1)) → P.NodeSeed (ℓ + 1)) :
    (anc.extend row).restrict = anc := by
  ext j hjℓ hjd u
  exact anc.extend_seed_le row hjℓ hjd u

@[simp]
theorem TruncSeeds.lastRow_extend {P : TreeSchedule} {ℓ : ℕ} (hℓ1 : ℓ + 1 ≤ P.depth)
    (anc : P.TruncSeeds ℓ) (row : Fin (P.numNodes (ℓ + 1)) → P.NodeSeed (ℓ + 1)) :
    (anc.extend row).lastRow hℓ1 = row := by
  funext v
  exact anc.extend_seed_succ row hℓ1 v

@[simp]
theorem TruncSeeds.extend_restrict_lastRow {P : TreeSchedule} {ℓ : ℕ} (hℓ1 : ℓ + 1 ≤ P.depth)
    (ts : P.TruncSeeds (ℓ + 1)) :
    ts.restrict.extend (ts.lastRow hℓ1) = ts := by
  ext j hjℓ1 hjd u
  by_cases h : j ≤ ℓ
  · dsimp only [extend, restrict]; rw [dite_eq_left h]
  · have heq : j = ℓ + 1 := by omega
    subst heq
    dsimp only [extend, lastRow]; rw [dite_eq_right (by omega)]

theorem TruncSeeds.primSetAt_restrict_eq {P : TreeSchedule} {ℓ j : ℕ}
    (ts : P.TruncSeeds (ℓ + 1)) (S : Finset (Fin P.paddedUniv)) (hjℓ1 : j ≤ ℓ + 1)
    (hjd : j ≤ P.depth) (u : Fin (P.numNodes j)) :
    ts.toFull.primSetAt S j hjd u = ts.restrict.toFull.primSetAt S j hjd u := by
  refine SeedAssignment.primSetAt_congr_ancestors S hjd u fun i hi => ?_
  have hiℓ : i ≤ ℓ := by omega
  rw [ts.toFull_seed (Nat.le_succ_of_le hiℓ), ts.restrict.toFull_seed hiℓ]
  rfl

theorem TruncSeeds.primSetAt_extend_eq {P : TreeSchedule} {ℓ j : ℕ} (anc : P.TruncSeeds ℓ)
    (row : Fin (P.numNodes (ℓ + 1)) → P.NodeSeed (ℓ + 1)) (S : Finset (Fin P.paddedUniv))
    (hjℓ1 : j ≤ ℓ + 1) (hjd : j ≤ P.depth) (u : Fin (P.numNodes j)) :
    (anc.extend row).toFull.primSetAt S j hjd u = anc.toFull.primSetAt S j hjd u := by
  rw [(anc.extend row).primSetAt_restrict_eq S hjℓ1 hjd u, anc.restrict_extend]

/-- Project a full `SeedAssignment` onto `TruncSeeds P ℓ`. -/
@[expose]
def truncOfSeeds (P : TreeSchedule) (ℓ : ℕ) (s : P.SeedAssignment) : P.TruncSeeds ℓ where
  seed j _ hj u := s.seed j hj u

/-- Convert full-depth `TruncSeeds P P.depth` into a `SeedAssignment`. -/
@[expose]
def TruncSeeds.toSeeds {P : TreeSchedule} (ts : P.TruncSeeds P.depth) : P.SeedAssignment where
  seed j hj u := ts.seed j hj hj u

@[simp]
theorem truncOfSeeds_toSeeds {P : TreeSchedule} (ts : P.TruncSeeds P.depth) :
    P.truncOfSeeds P.depth ts.toSeeds = ts := rfl

@[simp]
theorem toSeeds_truncOfSeeds {P : TreeSchedule} (s : P.SeedAssignment) :
    (P.truncOfSeeds P.depth s).toSeeds = s := rfl

theorem TruncSeeds.toFull_eq_toSeeds {P : TreeSchedule} (ts : P.TruncSeeds P.depth) :
    ts.toFull = ts.toSeeds := by
  ext j hj u
  exact ts.toFull_seed hj hj u

/-- Truncated seed-goodness invariant on `S` up to level `ℓ ≤ P.depth`. -/
def GoodTrunc {P : TreeSchedule} (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) (S : Finset (Fin P.paddedUniv))
    (ts : P.TruncSeeds ℓ) : Prop :=
  P.validRootBounds S ∧
    ∀ (j : ℕ) (hj : j ≤ ℓ) (u : Fin (P.numNodes j)),
      P.IsGoodNodeSeed j (ts.seed j hj (hj.trans hℓ) u)
        (ts.toFull.primSetAt S j (hj.trans hℓ) u)

theorem GoodTrunc.restrict {P : TreeSchedule} {ℓ : ℕ} {hℓ1 : ℓ + 1 ≤ P.depth}
    {S : Finset (Fin P.paddedUniv)} {ts : P.TruncSeeds (ℓ + 1)}
    (hg : GoodTrunc (ℓ + 1) hℓ1 S ts) :
    GoodTrunc ℓ (Nat.le_of_succ_le hℓ1) S ts.restrict := by
  refine ⟨hg.1, fun j hj u => ?_⟩
  rw [← ts.primSetAt_restrict_eq S (Nat.le_succ_of_le hj) (hj.trans (Nat.le_of_succ_le hℓ1)) u]
  exact hg.2 j (Nat.le_succ_of_le hj) u

theorem GoodTrunc.validPrimBounds_succ {P : TreeSchedule} {ℓ : ℕ} {hℓ : ℓ ≤ P.depth}
    (hℓ1 : ℓ + 1 ≤ P.depth) {S : Finset (Fin P.paddedUniv)} {anc : P.TruncSeeds ℓ}
    (hg : GoodTrunc ℓ hℓ S anc) (v : Fin (P.numNodes (ℓ + 1))) :
    P.validPrimBounds (ℓ + 1) (anc.toFull.primSetAt S (ℓ + 1) hℓ1 v) := by
  obtain ⟨hinj, hb, _⟩ := anc.toFull.ancestorsGood_invariants hg.1 (ℓ + 1) hℓ1 v fun j hj => by
    have hjℓ : j ≤ ℓ := Nat.le_of_lt_succ hj
    rw [anc.toFull_seed hjℓ (hj.le.trans hℓ1)]
    exact hg.2 j hjℓ (P.ancestorAt hj.le v)
  have hcard : #(anc.toFull.primSetAt S (ℓ + 1) hℓ1 v) =
      #(anc.toFull.activeAt S (ℓ + 1) hℓ1 v) := card_image_of_injOn hinj
  exact ⟨hcard ▸ hb.1, hcard ▸ hb.2⟩

theorem goodTrunc_depth_iff {P : TreeSchedule} (S : Finset (Fin P.paddedUniv))
    (ts : P.TruncSeeds P.depth) :
    GoodTrunc P.depth le_rfl S ts ↔ ts.toSeeds.AllGoodSeeds S := by
  simp only [GoodTrunc, validRootBounds, SeedAssignment.AllGoodSeeds, ts.toFull_eq_toSeeds]
  rfl

/-! ## Section 2: Top-Down `OracleComp` Samplers (`initTrunc`, `stepTrunc`, `execSeedSteps`) -/

/-- Top-down initial seed sampler up to level `ℓ ≤ P.depth` on initial padded set `S₀`. -/
@[expose]
noncomputable def initTrunc (P : TreeSchedule) :
    ∀ (ℓ : ℕ), ℓ ≤ P.depth → Finset (Fin P.paddedUniv) → OracleComp P.goodSeedSpec (P.TruncSeeds ℓ)
  | 0, h0, S₀ =>
    OracleComp.pi (fun _ : Fin (P.numNodes 0) => P.queryGoodOrArb 0 h0 (P.primSetZero S₀)) >>=
      fun row₀ => pure ⟨fun j hj0 _ u => by obtain rfl := Nat.eq_zero_of_le_zero hj0; exact row₀ u⟩
  | ℓ + 1, hℓ1, S₀ =>
    P.initTrunc ℓ (Nat.le_of_succ_le hℓ1) S₀ >>= fun anc =>
      OracleComp.pi (fun v : Fin (P.numNodes (ℓ + 1)) =>
        P.queryGoodOrArb (ℓ + 1) hℓ1 (anc.toFull.primSetAt S₀ (ℓ + 1) hℓ1 v)) >>=
        fun row => pure (anc.extend row)

open Classical in
/-- Single-step top-down seed update up to level `ℓ ≤ P.depth` on `st : P.PaddedStep`, returning
the updated `TruncSeeds ℓ` together with the boolean mask of level-`ℓ` nodes rehashed at this step.
-/
@[expose]
noncomputable def stepTrunc (P : TreeSchedule) :
    ∀ (ℓ : ℕ), ℓ ≤ P.depth → P.PaddedStep → P.TruncSeeds ℓ →
      OracleComp P.goodSeedSpec (P.TruncSeeds ℓ × (Fin (P.numNodes ℓ) → Bool))
  | 0, h0, st, ts =>
    let row_old : Fin (P.numNodes 0) → P.NodeSeed 0 := fun u => ts.seed 0 le_rfl h0 u
    let s' := P.primSetZero st.postSet
    let need : Fin (P.numNodes 0) → Bool := fun u =>
      !decide (P.IsGoodNodeSeed 0 (row_old u) s')
    OracleComp.pi (fun u : Fin (P.numNodes 0) =>
      P.singleNodeStep 0 h0 (s', false) (row_old u)) >>= fun row_new =>
        pure (⟨fun j hj0 _ u => by obtain rfl := Nat.eq_zero_of_le_zero hj0; exact row_new u⟩, need)
  | ℓ + 1, hℓ1, st, ts =>
    P.stepTrunc ℓ (Nat.le_of_succ_le hℓ1) st ts.restrict >>= fun am =>
      let anc' := am.1
      let reh := am.2
      let row_old := ts.lastRow hℓ1
      let s' : Fin (P.numNodes (ℓ + 1)) → Finset (P.PrimId (ℓ + 1)) := fun v =>
        anc'.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 v
      let need : Fin (P.numNodes (ℓ + 1)) → Bool := fun v =>
        reh (P.parentNode ℓ v) || !decide (P.IsGoodNodeSeed (ℓ + 1) (row_old v) (s' v))
      OracleComp.pi (fun v : Fin (P.numNodes (ℓ + 1)) =>
        P.singleNodeStep (ℓ + 1) hℓ1 (s' v, reh (P.parentNode ℓ v)) (row_old v)) >>=
          fun row_new => pure (anc'.extend row_new, need)

/-- Sequential fold of `stepTrunc` across `sts : List P.PaddedStep`. -/
@[expose]
noncomputable def runTruncSteps (P : TreeSchedule) (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) :
    List P.PaddedStep → P.TruncSeeds ℓ → OracleComp P.goodSeedSpec (P.TruncSeeds ℓ)
  | [], ts => pure ts
  | st :: sts, ts => P.stepTrunc ℓ hℓ st ts >>= fun am => P.runTruncSteps ℓ hℓ sts am.1

theorem runTruncSteps_append (P : TreeSchedule) (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) :
    ∀ (xs ys : List P.PaddedStep) (ts : P.TruncSeeds ℓ),
      P.runTruncSteps ℓ hℓ (xs ++ ys) ts =
        (P.runTruncSteps ℓ hℓ xs ts >>= P.runTruncSteps ℓ hℓ ys)
  | [], _, _ => by simp [runTruncSteps]
  | st :: xs, ys, ts => by
    dsimp only [List.cons_append, runTruncSteps]
    rw [bind_assoc]
    exact congrArg _ (funext fun am => P.runTruncSteps_append ℓ hℓ xs ys am.1)

/-- Full initialization + multi-step execution up to level `ℓ ≤ P.depth`. -/
@[expose]
noncomputable def execTruncHistory (P : TreeSchedule) (ℓ : ℕ) (hℓ : ℓ ≤ P.depth)
    (S₀ : Finset (Fin P.paddedUniv)) (sts : List P.PaddedStep) :
    OracleComp P.goodSeedSpec (P.TruncSeeds ℓ) :=
  P.initTrunc ℓ hℓ S₀ >>= P.runTruncSteps ℓ hℓ sts

/-- Full-depth (`0 ≤ ℓ ≤ depth`) seed initialization and localized subtree resampling across `sts`.
-/
@[expose]
noncomputable def execSeedSteps (P : TreeSchedule) (S₀ : Finset (Fin P.paddedUniv))
    (sts : List P.PaddedStep) : OracleComp P.goodSeedSpec P.SeedAssignment :=
  P.execTruncHistory P.depth le_rfl S₀ sts >>= fun ts => pure ts.toSeeds

private theorem pi_pure {ι : Type} {spec : OracleSpec ι} {m : ℕ} {β : Fin m → Type}
    (row : (i : Fin m) → β i) :
    OracleComp.pi (spec := spec) (fun i => pure (row i)) = pure row := by
  induction m with
  | zero =>
    rw [OracleComp.pi_zero]
    exact congrArg pure (Subsingleton.elim _ _)
  | succ m ih =>
    rw [OracleComp.pi_succ, pure_bind, ih, ← bind_pure_comp, pure_bind]
    exact congrArg pure (Fin.cons_self_tail row)

private theorem mem_support_pi {ι : Type} {spec : OracleSpec ι} {m : ℕ} {β : Fin m → Type}
    {programs : (i : Fin m) → OracleComp spec (β i)} {r : (i : Fin m) → β i}
    (hr : r ∈ (OracleComp.pi programs).support) (i : Fin m) :
    r i ∈ (programs i).support :=
  (OracleComp.mem_supportWith_pi_iff (fun _ => Set.univ) programs r).mp hr i

private theorem isGoodNodeSeed_of_mem_support_queryGoodOrArb {P : TreeSchedule} {L : ℕ}
    (hL : L ≤ P.depth) {s : Finset (P.PrimId L)} (hb : P.validPrimBounds L s)
    {g : P.NodeSeed L} (hg : g ∈ (P.queryGoodOrArb L hL s).support) :
    P.IsGoodNodeSeed L g s := by
  dsimp only [queryGoodOrArb] at hg
  rw [dite_eq_left hb, OracleComp.mem_supportWith_bind_iff] at hg
  obtain ⟨r, _, hgr⟩ := hg
  exact (show g = r.1 from hgr) ▸ r.2

/-- When `ts` already satisfies `GoodTrunc ℓ hℓ st.postSet ts`, `stepTrunc` makes zero oracle calls
and evaluates identically to `pure (ts, fun _ => false)`. -/
theorem stepTrunc_of_goodTrunc_post {P : TreeSchedule} :
    ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) (st : P.PaddedStep) (ts : P.TruncSeeds ℓ),
      GoodTrunc ℓ hℓ st.postSet ts →
      P.stepTrunc ℓ hℓ st ts = pure (ts, fun _ => false)
  | 0, h0, st, ts, hgood => by
    classical
    dsimp only [stepTrunc]
    have hg0 : ∀ u : Fin (P.numNodes 0),
        P.IsGoodNodeSeed 0 (ts.seed 0 le_rfl h0 u) (P.primSetZero st.postSet) := fun u => by
      simpa only [SeedAssignment.primSetAt_zero] using hgood.2 0 le_rfl u
    have hstep0 : (fun u : Fin (P.numNodes 0) =>
        P.singleNodeStep 0 h0 (P.primSetZero st.postSet, false) (ts.seed 0 le_rfl h0 u)) =
        fun u => pure (ts.seed 0 le_rfl h0 u) := by
      funext u
      dsimp only [singleNodeStep]
      simp [hg0 u]
    have hneed : (fun u : Fin (P.numNodes 0) =>
        !decide (P.IsGoodNodeSeed 0 (ts.seed 0 le_rfl h0 u) (P.primSetZero st.postSet))) =
        fun _ => false := by
      funext u; simp [hg0 u]
    rw [hstep0, pi_pure, pure_bind, hneed]
    congr 2
    ext j hj0 _ u
    obtain rfl := Nat.eq_zero_of_le_zero hj0
    rfl
  | ℓ + 1, hℓ1, st, ts, hgood => by
    classical
    dsimp only [stepTrunc]
    rw [stepTrunc_of_goodTrunc_post ℓ (Nat.le_of_succ_le hℓ1) st ts.restrict hgood.restrict,
      pure_bind]
    have hg_succ : ∀ v : Fin (P.numNodes (ℓ + 1)),
        P.IsGoodNodeSeed (ℓ + 1) (ts.lastRow hℓ1 v)
          (ts.restrict.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 v) := fun v => by
      rw [← ts.primSetAt_restrict_eq st.postSet le_rfl hℓ1 v]
      exact hgood.2 (ℓ + 1) le_rfl v
    have hstep1 : (fun v : Fin (P.numNodes (ℓ + 1)) =>
        P.singleNodeStep (ℓ + 1) hℓ1
          (ts.restrict.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 v, false) (ts.lastRow hℓ1 v)) =
        fun v => pure (ts.lastRow hℓ1 v) := by
      funext v; dsimp only [singleNodeStep]; simp [hg_succ v]
    have hneed : (fun v : Fin (P.numNodes (ℓ + 1)) =>
        false || !decide (P.IsGoodNodeSeed (ℓ + 1) (ts.lastRow hℓ1 v)
          (ts.restrict.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 v))) = fun _ => false := by
      funext v; simp [hg_succ v]
    rw [hstep1, pi_pure, pure_bind, hneed, ts.extend_restrict_lastRow hℓ1]

/-- Every outcome in `(P.initTrunc ℓ hℓ S₀).support` satisfies `GoodTrunc ℓ hℓ S₀`. -/
theorem mem_support_initTrunc {P : TreeSchedule} :
    ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) {S₀ : Finset (Fin P.paddedUniv)},
      P.validRootBounds S₀ →
      ∀ {ts : P.TruncSeeds ℓ}, ts ∈ (P.initTrunc ℓ hℓ S₀).support → GoodTrunc ℓ hℓ S₀ ts
  | 0, h0, S₀, hS₀, ts, hts => by
    dsimp only [initTrunc] at hts
    rw [OracleComp.mem_supportWith_bind_iff] at hts
    obtain ⟨row₀, hrow₀, hts_eq⟩ := hts
    have hts' : ts = ⟨fun j hj0 _ u => by
        obtain rfl := Nat.eq_zero_of_le_zero hj0; exact row₀ u⟩ := hts_eq
    subst hts'
    refine ⟨hS₀, fun j hj0 u => ?_⟩
    obtain rfl := Nat.eq_zero_of_le_zero hj0
    rw [SeedAssignment.primSetAt_zero]
    exact isGoodNodeSeed_of_mem_support_queryGoodOrArb h0
      (P.validPrimBounds_primSetZero_of_root hS₀) (mem_support_pi hrow₀ u)
  | ℓ + 1, hℓ1, S₀, hS₀, ts, hts => by
    dsimp only [initTrunc] at hts
    rw [OracleComp.mem_supportWith_bind_iff] at hts
    obtain ⟨anc, hanc, hrest⟩ := hts
    rw [OracleComp.mem_supportWith_bind_iff] at hrest
    obtain ⟨row, hrow, hts_eq⟩ := hrest
    have hts' : ts = anc.extend row := hts_eq
    subst hts'
    have hg_anc := mem_support_initTrunc ℓ (Nat.le_of_succ_le hℓ1) hS₀ hanc
    refine ⟨hS₀, fun j hj u => ?_⟩
    rw [anc.primSetAt_extend_eq row S₀ hj (hj.trans hℓ1) u]
    by_cases hjℓ : j ≤ ℓ
    · rw [anc.extend_seed_le row hjℓ (hj.trans hℓ1) u]
      exact hg_anc.2 j hjℓ u
    · have heq : j = ℓ + 1 := by omega
      subst heq
      rw [anc.extend_seed_succ row hℓ1 u]
      exact isGoodNodeSeed_of_mem_support_queryGoodOrArb hℓ1
        (hg_anc.validPrimBounds_succ hℓ1 u) (mem_support_pi hrow u)

/-- Every outcome `(ts', mask) ∈ (P.stepTrunc ℓ hℓ st ts).support` satisfies `GoodTrunc` on
`st.postSet`, and every node `u` with `mask u = false` preserves all ancestor seeds `j ≤ ℓ`. -/
theorem mem_support_stepTrunc {P : TreeSchedule} :
    ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) (st : P.PaddedStep) (ts : P.TruncSeeds ℓ)
      {am : P.TruncSeeds ℓ × (Fin (P.numNodes ℓ) → Bool)},
      am ∈ (P.stepTrunc ℓ hℓ st ts).support →
      GoodTrunc ℓ hℓ st.postSet am.1 ∧
        ∀ (u : Fin (P.numNodes ℓ)), am.2 u = false →
          ∀ (j : ℕ) (hj : j ≤ ℓ),
            am.1.seed j hj (hj.trans hℓ) (P.ancestorAt hj u) =
              ts.seed j hj (hj.trans hℓ) (P.ancestorAt hj u)
  | 0, h0, st, ts, am, ham => by
    classical
    dsimp only [stepTrunc] at ham
    rw [OracleComp.mem_supportWith_bind_iff] at ham
    obtain ⟨row_new, hrow, ham_eq⟩ := ham
    obtain ⟨hts', hmask⟩ := Prod.mk.inj (show am = _ from ham_eq)
    have hb0 : P.validPrimBounds 0 (P.primSetZero st.postSet) :=
      P.validPrimBounds_primSetZero_of_root st.post_bounds
    refine ⟨⟨st.post_bounds, fun j hj0 u => ?_⟩, fun u hmu j hj0 => ?_⟩
    · obtain rfl := Nat.eq_zero_of_le_zero hj0
      have hru := mem_support_pi hrow u
      dsimp only [singleNodeStep] at hru
      rw [hts', SeedAssignment.primSetAt_zero]
      change P.IsGoodNodeSeed 0 (row_new u) (P.primSetZero st.postSet)
      by_cases hg : P.IsGoodNodeSeed 0 (ts.seed 0 le_rfl h0 u) (P.primSetZero st.postSet)
      · simp only [hg, decide_true, Bool.not_true, Bool.or_false, Bool.false_eq_true,
          ↓reduceIte, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hru
        exact hru ▸ hg
      · simp only [hg, decide_false, Bool.not_false, Bool.or_true, ↓reduceIte] at hru
        exact isGoodNodeSeed_of_mem_support_queryGoodOrArb h0 hb0 hru
    · obtain rfl := Nat.eq_zero_of_le_zero hj0
      rw [P.ancestorAt_refl, hts']
      have hru := mem_support_pi hrow u
      have hg : P.IsGoodNodeSeed 0 (ts.seed 0 le_rfl h0 u) (P.primSetZero st.postSet) := by
        have hm := congrFun hmask u
        rw [hmu] at hm
        by_contra hng
        simp [hng] at hm
      dsimp only [singleNodeStep] at hru
      simp only [hg, decide_true, Bool.not_true, Bool.or_false, Bool.false_eq_true,
        ↓reduceIte, OracleComp.supportWith_pure, Set.mem_singleton_iff] at hru
      exact hru
  | ℓ + 1, hℓ1, st, ts, am, ham => by
    classical
    dsimp only [stepTrunc] at ham
    rw [OracleComp.mem_supportWith_bind_iff] at ham
    obtain ⟨am_anc, ham_anc, hrest⟩ := ham
    rw [OracleComp.mem_supportWith_bind_iff] at hrest
    obtain ⟨row_new, hrow, ham_eq⟩ := hrest
    obtain ⟨hts', hmask⟩ := Prod.mk.inj (show am = _ from ham_eq)
    obtain ⟨hg_anc, hfix_anc⟩ :=
      mem_support_stepTrunc ℓ (Nat.le_of_succ_le hℓ1) st ts.restrict ham_anc
    refine ⟨⟨st.post_bounds, fun j hj u => ?_⟩, fun v hmv j hj => ?_⟩
    · rw [hts', am_anc.1.primSetAt_extend_eq row_new st.postSet hj (hj.trans hℓ1) u]
      by_cases hjℓ : j ≤ ℓ
      · rw [am_anc.1.extend_seed_le row_new hjℓ (hj.trans hℓ1) u]
        exact hg_anc.2 j hjℓ u
      · have heq : j = ℓ + 1 := by omega
        subst heq
        rw [am_anc.1.extend_seed_succ row_new hℓ1 u]
        have hrv := mem_support_pi hrow u
        dsimp only [singleNodeStep] at hrv
        by_cases hcond : am_anc.2 (P.parentNode ℓ u) ||
            !decide (P.IsGoodNodeSeed (ℓ + 1) (ts.lastRow hℓ1 u)
              (am_anc.1.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 u))
        · rw [ite_eq_left hcond] at hrv
          exact isGoodNodeSeed_of_mem_support_queryGoodOrArb hℓ1
            (hg_anc.validPrimBounds_succ hℓ1 u) hrv
        · rw [ite_eq_right hcond] at hrv
          have hg_old : P.IsGoodNodeSeed (ℓ + 1) (ts.lastRow hℓ1 u)
              (am_anc.1.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 u) := by
            simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_or,
              not_not] at hcond
            exact hcond.2
          exact (show row_new u = ts.lastRow hℓ1 u from hrv) ▸ hg_old
    · have hmv' : (am_anc.2 (P.parentNode ℓ v) ||
          !decide (P.IsGoodNodeSeed (ℓ + 1) (ts.lastRow hℓ1 v)
            (am_anc.1.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 v))) = false := by
        rw [hmask] at hmv; exact hmv
      have hp_false : am_anc.2 (P.parentNode ℓ v) = false :=
        (Bool.or_eq_false_iff.mp hmv').1
      by_cases hjℓ : j ≤ ℓ
      · rw [P.ancestorAt_succ hjℓ v, hts',
          am_anc.1.extend_seed_le row_new hjℓ (hj.trans hℓ1) _,
          hfix_anc (P.parentNode ℓ v) hp_false j hjℓ]
        rfl
      · have heq : j = ℓ + 1 := by omega
        subst heq
        rw [P.ancestorAt_refl, hts', am_anc.1.extend_seed_succ row_new hℓ1 v]
        have hrv := mem_support_pi hrow v
        dsimp only [singleNodeStep] at hrv
        rw [hmv'] at hrv
        exact hrv

/-- Subtree locality of `stepTrunc`: when `ts` is good on `st.preSet` and fails on `st.postSet`,
there is a failing node `(ℓ₀, nodeAt ℓ₀ st.key)` outside whose subtree every supported outcome
preserves `ts`'s seeds verbatim. -/
theorem stepTrunc_seed_eq_outside_inSubtree {P : TreeSchedule} (st : P.PaddedStep)
    (ts : P.TruncSeeds P.depth) (hpre : ts.toSeeds.AllGoodSeeds st.preSet)
    (hbad : ¬ ts.toSeeds.AllGoodSeeds st.postSet)
    {am : P.TruncSeeds P.depth × (Fin (P.numNodes P.depth) → Bool)}
    (ham : am ∈ (P.stepTrunc P.depth le_rfl st ts).support) :
    ∃ (ℓ₀ : ℕ) (hℓ₀ : ℓ₀ ≤ P.depth),
      ¬ P.IsGoodNodeSeed ℓ₀ (ts.toSeeds.seed ℓ₀ hℓ₀ (ts.toSeeds.nodeAt ℓ₀ hℓ₀ st.key))
        (ts.toSeeds.primSetAt st.postSet ℓ₀ hℓ₀ (ts.toSeeds.nodeAt ℓ₀ hℓ₀ st.key)) ∧
      ∀ (j : ℕ) (hj : j ≤ P.depth) (w : Fin (P.numNodes j)),
        ¬ P.InSubtree ℓ₀ (ts.toSeeds.nodeAt ℓ₀ hℓ₀ st.key) j w →
          am.1.toSeeds.seed j hj w = ts.toSeeds.seed j hj w := by
  classical
  have hex_bad : ∃ ℓ, TreeState.hasBadSeedOn ts.toSeeds st.postSet ℓ := by
    by_contra hno
    exact hbad ⟨st.post_bounds, fun ℓ hℓ w => by by_contra hn; exact hno ⟨ℓ, hℓ, w, hn⟩⟩
  let ℓ₀ := Nat.find hex_bad
  obtain ⟨hℓ₀, w_bad, hw_bad⟩ := Nat.find_spec hex_bad
  let u₀ := ts.toSeeds.nodeAt ℓ₀ hℓ₀ st.key
  have hu₀_bad := TreeState.not_isGoodNodeSeed_at_changed hpre st.diff_key hℓ₀ hw_bad
  refine ⟨ℓ₀, hℓ₀, hu₀_bad, ?_⟩
  have hbelow : ∀ (j : ℕ) (hj : j < ℓ₀) (w : Fin (P.numNodes j)),
      P.IsGoodNodeSeed j (ts.toSeeds.seed j (hj.le.trans hℓ₀) w)
        (ts.toSeeds.primSetAt st.postSet j (hj.le.trans hℓ₀) w) := fun j hj w => by
    by_contra hnot; exact Nat.find_min hex_bad hj ⟨hj.le.trans hℓ₀, w, hnot⟩
  have hkeep : ∀ (L : ℕ) (hL : L ≤ P.depth) (t_cur : P.TruncSeeds L)
      (ht_eq : ∀ j (hj : j ≤ L) w, t_cur.seed j hj (hj.trans hL) w =
        ts.toSeeds.seed j (hj.trans hL) w)
      {amL : P.TruncSeeds L × (Fin (P.numNodes L) → Bool)},
      amL ∈ (P.stepTrunc L hL st t_cur).support →
      ∀ (w : Fin (P.numNodes L)), ¬ P.InSubtree ℓ₀ u₀ L w →
        amL.2 w = false ∧ amL.1.seed L le_rfl hL w = ts.toSeeds.seed L hL w := by
    intro L
    induction L with
    | zero =>
      intro hL t_cur ht_eq am0 ham0 w hnot
      have h0lt : 0 < ℓ₀ := by
        by_contra hle
        have hle0 : ℓ₀ ≤ 0 := by omega
        have hn1 : P.numNodes ℓ₀ = 1 := (congrArg P.numNodes (show ℓ₀ = 0 by omega)).trans
          P.numNodes_zero
        have hanc_lt := (P.ancestorAt hle0 w).isLt
        have hu_lt := u₀.isLt
        exact hnot ⟨hle0, Fin.ext (by omega)⟩
      have hg0 : GoodTrunc 0 hL st.postSet t_cur := by
        refine ⟨st.post_bounds, fun j hj0 u => ?_⟩
        obtain rfl := Nat.eq_zero_of_le_zero hj0
        rw [ht_eq 0 le_rfl u, SeedAssignment.primSetAt_zero,
          ← ts.toSeeds.primSetAt_zero st.postSet hL u]
        exact hbelow 0 h0lt u
      rw [stepTrunc_of_goodTrunc_post 0 hL st t_cur hg0] at ham0
      obtain ⟨ha1, ha2⟩ := Prod.mk.inj (show am0 = _ from ham0)
      exact ⟨congrFun ha2 w, ha1 ▸ ht_eq 0 le_rfl w⟩
    | succ m ih =>
      intro hL t_cur ht_eq am1 ham1 w hnot
      dsimp only [stepTrunc] at ham1
      rw [OracleComp.mem_supportWith_bind_iff] at ham1
      obtain ⟨am_m, ham_m, hrest⟩ := ham1
      rw [OracleComp.mem_supportWith_bind_iff] at hrest
      obtain ⟨row_new, hrow, ham1_eq⟩ := hrest
      obtain ⟨hts1, hmask1⟩ := Prod.mk.inj (show am1 = _ from ham1_eq)
      have hp_not : ¬ P.InSubtree ℓ₀ u₀ m (P.parentNode m w) := by
        have h := P.not_inSubtree_ancestor_of_not_inSubtree (Nat.le_succ m) hnot
        rwa [P.ancestorAt_succ le_rfl, P.ancestorAt_refl] at h
      have ht_res : ∀ j (hj : j ≤ m) u,
          t_cur.restrict.seed j hj (hj.trans (Nat.le_of_succ_le hL)) u =
            ts.toSeeds.seed j (hj.trans (Nat.le_of_succ_le hL)) u := fun j hj u =>
        ht_eq j (Nat.le_succ_of_le hj) u
      have ⟨hp_false, _⟩ := ih (Nat.le_of_succ_le hL) t_cur.restrict ht_res ham_m _ hp_not
      have hfix_m := (mem_support_stepTrunc m (Nat.le_of_succ_le hL) st t_cur.restrict ham_m).2
        (P.parentNode m w) hp_false
      have hprim_eq : am_m.1.toFull.primSetAt st.postSet (m + 1) hL w =
          ts.toSeeds.primSetAt st.postSet (m + 1) hL w := by
        refine SeedAssignment.primSetAt_congr_ancestors st.postSet hL w fun j hj => ?_
        have hjm : j ≤ m := Nat.le_of_lt_succ hj
        rw [am_m.1.toFull_seed hjm, P.ancestorAt_succ hjm w,
          hfix_m j hjm, ht_res j hjm]
      have hgw : P.IsGoodNodeSeed (m + 1) (t_cur.lastRow hL w)
          (am_m.1.toFull.primSetAt st.postSet (m + 1) hL w) := by
        rw [hprim_eq, show t_cur.lastRow hL w = ts.toSeeds.seed (m + 1) hL w from
          ht_eq (m + 1) le_rfl w]
        by_cases hlt : m + 1 < ℓ₀
        · exact hbelow (m + 1) hlt w
        · have h0m1 : ℓ₀ ≤ m + 1 := by omega
          have hanc_ne : P.ancestorAt h0m1 w ≠ u₀ := fun he => hnot ⟨h0m1, he⟩
          have hact_eq : ts.toSeeds.activeAt st.postSet (m + 1) hL w =
              ts.toSeeds.activeAt st.preSet (m + 1) hL w := by
            ext y
            simp only [SeedAssignment.mem_activeAt_iff]
            rcases st.diff_key y with hiff | rfl
            · rw [hiff]
            · have hnw : ts.toSeeds.nodeAt (m + 1) hL st.key ≠ w := fun h =>
                hanc_ne (by rw [← h, ts.toSeeds.ancestorAt_nodeAt h0m1 hL])
              simp [hnw]
          have hp_pre : ts.toSeeds.primSetAt st.postSet (m + 1) hL w =
              ts.toSeeds.primSetAt st.preSet (m + 1) hL w := by
            dsimp only [SeedAssignment.primSetAt]; rw [hact_eq]
          rw [hp_pre]
          exact hpre.2 (m + 1) hL w
      have hneed_w : (am_m.2 (P.parentNode m w) ||
          !decide (P.IsGoodNodeSeed (m + 1) (t_cur.lastRow hL w)
            (am_m.1.toFull.primSetAt st.postSet (m + 1) hL w))) = false := by
        simp [hp_false, hgw]
      have hrw := mem_support_pi hrow w
      dsimp only [singleNodeStep] at hrw
      rw [hneed_w] at hrw
      refine ⟨by rw [hmask1]; exact hneed_w, ?_⟩
      rw [hts1, am_m.1.extend_seed_succ row_new hL w, show row_new w = t_cur.lastRow hL w from hrw]
      exact ht_eq (m + 1) le_rfl w
  have hall : ∀ (L : ℕ) (hL : L ≤ P.depth) (t_cur : P.TruncSeeds L)
      (ht_eq : ∀ j (hj : j ≤ L) w, t_cur.seed j hj (hj.trans hL) w =
        ts.toSeeds.seed j (hj.trans hL) w)
      {amL : P.TruncSeeds L × (Fin (P.numNodes L) → Bool)},
      amL ∈ (P.stepTrunc L hL st t_cur).support →
      ∀ (j : ℕ) (hj : j ≤ L) (w : Fin (P.numNodes j)), ¬ P.InSubtree ℓ₀ u₀ j w →
        amL.1.seed j hj (hj.trans hL) w = ts.toSeeds.seed j (hj.trans hL) w := by
    intro L
    induction L with
    | zero =>
      intro hL t_cur ht_eq _ ham0 j hj0 w hnot
      obtain rfl := Nat.eq_zero_of_le_zero hj0
      exact (hkeep 0 hL t_cur ht_eq ham0 w hnot).2
    | succ m ih =>
      intro hL t_cur ht_eq am1 ham1 j hj w hnot
      by_cases hjm : j ≤ m
      · dsimp only [stepTrunc] at ham1
        rw [OracleComp.mem_supportWith_bind_iff] at ham1
        obtain ⟨am_m, ham_m, hrest⟩ := ham1
        rw [OracleComp.mem_supportWith_bind_iff] at hrest
        obtain ⟨row_new, _, ham1_eq⟩ := hrest
        obtain ⟨hts1, _⟩ := Prod.mk.inj (show am1 = _ from ham1_eq)
        rw [hts1, am_m.1.extend_seed_le row_new hjm (hj.trans hL) w]
        exact ih (Nat.le_of_succ_le hL) t_cur.restrict
          (fun i hi u => ht_eq i (Nat.le_succ_of_le hi) u) ham_m j hjm w hnot
      · have heq : j = m + 1 := by omega
        subst heq
        exact (hkeep (m + 1) hL t_cur ht_eq ham1 w hnot).2
  exact hall P.depth le_rfl ts (fun _ _ _ => rfl) ham

/-! ## Section 3: Worst-Case Query Budgets and Levelwise Finiteness -/

/-- Sum of node counts across levels `0 .. ℓ`. -/
def sumNumNodes (P : TreeSchedule) (ℓ : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (ℓ + 1), P.numNodes j

theorem isQueryBounded_initTrunc (P : TreeSchedule) :
    ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) (S₀ : Finset (Fin P.paddedUniv)),
      OracleComp.IsQueryBounded (P.initTrunc ℓ hℓ S₀) (P.sumNumNodes ℓ)
  | 0, h0, S₀ => by
    dsimp only [initTrunc, sumNumNodes]
    rw [Nat.zero_add, Finset.range_one, Finset.sum_singleton]
    have hpi := isCostBounded_pi_unit fun _ : Fin (P.numNodes 0) =>
      P.isQueryBounded_queryGoodOrArb 0 h0 (P.primSetZero S₀)
    exact (hpi.bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  | ℓ + 1, hℓ1, S₀ => by
    dsimp only [initTrunc, sumNumNodes]
    rw [Finset.sum_range_succ]
    refine (P.isQueryBounded_initTrunc ℓ (Nat.le_of_succ_le hℓ1) S₀).bind fun anc => ?_
    have hpi := isCostBounded_pi_unit fun v : Fin (P.numNodes (ℓ + 1)) =>
      P.isQueryBounded_queryGoodOrArb (ℓ + 1) hℓ1 (anc.toFull.primSetAt S₀ (ℓ + 1) hℓ1 v)
    exact (hpi.bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono (by omega)

theorem isQueryBounded_stepTrunc (P : TreeSchedule) :
    ∀ (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) (st : P.PaddedStep) (ts : P.TruncSeeds ℓ),
      OracleComp.IsQueryBounded (P.stepTrunc ℓ hℓ st ts) (P.sumNumNodes ℓ)
  | 0, h0, st, ts => by
    dsimp only [stepTrunc, sumNumNodes]
    rw [Nat.zero_add, Finset.range_one, Finset.sum_singleton]
    have hpi := isCostBounded_pi_unit fun u : Fin (P.numNodes 0) =>
      P.isQueryBounded_singleNodeStep 0 h0 (P.primSetZero st.postSet, false)
        (ts.seed 0 le_rfl h0 u)
    exact (hpi.bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  | ℓ + 1, hℓ1, st, ts => by
    dsimp only [stepTrunc, sumNumNodes]
    rw [Finset.sum_range_succ]
    refine (P.isQueryBounded_stepTrunc ℓ (Nat.le_of_succ_le hℓ1) st ts.restrict).bind fun am => ?_
    have hpi := isCostBounded_pi_unit fun v : Fin (P.numNodes (ℓ + 1)) =>
      P.isQueryBounded_singleNodeStep (ℓ + 1) hℓ1
        (am.1.toFull.primSetAt st.postSet (ℓ + 1) hℓ1 v, am.2 (P.parentNode ℓ v))
        (ts.lastRow hℓ1 v)
    exact (hpi.bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono (by omega)

theorem isQueryBounded_runTruncSteps (P : TreeSchedule) (ℓ : ℕ) (hℓ : ℓ ≤ P.depth) :
    ∀ (sts : List P.PaddedStep) (ts : P.TruncSeeds ℓ),
      OracleComp.IsQueryBounded (P.runTruncSteps ℓ hℓ sts ts) (sts.length * P.sumNumNodes ℓ)
  | [], ts => .pure ts _
  | st :: sts, ts => by
    dsimp only [runTruncSteps, List.length_cons]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    exact (P.isQueryBounded_stepTrunc ℓ hℓ st ts).bind fun am =>
      P.isQueryBounded_runTruncSteps ℓ hℓ sts am.1

theorem isQueryBounded_execTruncHistory (P : TreeSchedule) (ℓ : ℕ) (hℓ : ℓ ≤ P.depth)
    (S₀ : Finset (Fin P.paddedUniv)) (sts : List P.PaddedStep) :
    OracleComp.IsQueryBounded (P.execTruncHistory ℓ hℓ S₀ sts)
      ((1 + sts.length) * P.sumNumNodes ℓ) := by
  rw [Nat.add_mul, Nat.one_mul]
  exact (P.isQueryBounded_initTrunc ℓ hℓ S₀).bind (P.isQueryBounded_runTruncSteps ℓ hℓ sts)

theorem expectedCost_levelRehashCost_ne_top {P : TreeSchedule} (hcr : P.ConcentrationReady)
    (L ℓ : ℕ) (hℓ : ℓ ≤ P.depth) (S₀ : Finset (Fin P.paddedUniv)) (sts : List P.PaddedStep) :
    OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost L)
      (P.execTruncHistory ℓ hℓ S₀ sts) ≠ ⊤ := by
  have hle1 : levelRehashCost (P := P) L ≤ fun _ => ((1 : ℕ) : ℝ≥0∞) := fun q => by
    dsimp only [levelRehashCost]; split_ifs <;> norm_num
  have hlt : OracleComp.expectedCost (P.goodSeedLaw hcr) (levelRehashCost L)
      (P.execTruncHistory ℓ hℓ S₀ sts) < ⊤ :=
    ((OracleComp.expectedCost_mono (P.goodSeedLaw hcr) hle1 _).trans
      (OracleComp.expectedCost_le_of_isCostBounded (P.goodSeedLaw hcr)
        (P.isQueryBounded_execTruncHistory ℓ hℓ S₀ sts))).trans_lt
      (ENNReal.natCast_ne_top _).lt_top
  exact hlt.ne

end TreeSchedule

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
