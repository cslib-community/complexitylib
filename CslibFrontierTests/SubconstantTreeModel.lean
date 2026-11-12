/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.TreeModel
public meta import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.StorageNode
public meta import CslibFrontier.DataStructure.Dictionary.Minimap
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multi-Level Subconstant-Redundancy Dictionary Tree Tests (`Params`, `StorageNode`, `TreeModel`)

Exercises:
1. `SubconstantRedundancy.Params` (`Schedule`, `Canonical`, `BitBudget`):
   - concrete checks of clamped `effRedundancy`, `redundancyRatio`, `treeDepth`, and `infoBits`;
   - non-vacuous smaller-than-`n` `ValidRegime` instance (`R = n / 4 < n`, `U = n ^ 2`,
     `V = 2 ^ 64`), `canonicalSchedule`, `ConcentrationReady`, and the `infoBits + O(R)` space
     bound `totalTreeBits_le_infoBits_add`;
2. `SubconstantRedundancy.NodeSeeds`:
   - both child-router regimes (`RouterSeed.trinomial` below `childRouterThreshold` on a depth-`3`
     schedule and `RouterSeed.doubleTab` above `childRouterThreshold`), plus zero-padded degree
     compatibility (`routerRound_trinomial_eq_padded`) for static-degree polynomial evaluation;
3. `SubconstantRedundancy.StorageNode`:
   - executable `#eval` traces of `WaitingList`, `StorageTable` (`Section 5.6` metadata separation
     `locateSlot`), and `RootValPool`;
4. `SubconstantRedundancy.TreeModel`:
   - `SeedAssignment` routing bijections and Section 5.6 `dfsSubtreeMeta` on depth `3`;
   - end-to-end dictionary trace (`initTree`, `insert`, overwrite, `query`, `delete`, absent
     `delete`) preserving `WellFormed`;
   - `Algorithm 3` (`deleteAndGetQuotient_spec`) and `Algorithm 4` (`rehashSubtree` strict
     locality and `wellFormedPadded_rehashSubtree`);
5. `SubconstantRedundancy.RehashBounds`:
   - `Claim 5.4` (`prob_survives_window_of_ancestorFree`,
     `condProb_goodNodeSeed_survives_window_ge_half`) and `Lemma 5.3`
     (`canonicalSchedule_rehashWork_le_mul_logStar`).
-/

public section

namespace CslibFrontierTests.SubconstantTreeModel

open Cslib.DataStructure
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.SubconstantRedundancy
open Cslib.Probability
open scoped BigOperators Finset

/-! ## 1. Parameter Schedule, Clamped Redundancy & `infoBits + O(R)` Space Bound -/

-- Clamped `effRedundancy` ensures `redundancyRatio ≥ minRedundancyRatio = 256` even when
-- `R = n / 2`, while leaving genuinely small `R` untouched.
example : effRedundancy 1024 512 = 4 := by decide
example : redundancyRatio 1024 512 = 256 := by decide
example : effRedundancy 1024 2 = 2 := by decide
example : redundancyRatio 1024 2 = 512 := by decide
example : infoBits 16 4 4 = 19 := by decide

-- Stopping-depth bounds (`2 ≤ treeDepth U r ≤ floorLogStar U + 2`, `iterLog k U ≤ 4 * r`).
example : 2 ≤ treeDepth (2 ^ 64) 256 ∧
    Nat.iterLog (treeDepth (2 ^ 64) 256) (2 ^ 64) ≤ 1024 :=
  ⟨two_le_treeDepth _ _, iterLog_treeDepth_le (by decide)⟩

/-- Base-`2` log capacity for the non-vacuous sublinear-redundancy `ValidRegime` witness. -/
def testLogN : ℕ := thresholdLogN 1 1

/-- Dictionary capacity `n = thresholdN 1 1 = 2 ^ testLogN`. -/
def testN : ℕ := thresholdN 1 1

/-- Quadratic universe `U = n ^ 2` (`p_min = q_min = p_max = q_max = 1`). -/
def testU : ℕ := testN ^ 2

/-- 64-bit value universe `V = 2 ^ 64`. -/
def testV : ℕ := 2 ^ 64

/-- Redundancy parameter `R = n / 4 < n`. -/
def testR : ℕ := 2 ^ (testLogN - 2)

theorem four_pow_ten_le_testLogN : 4 ^ 10 ≤ testLogN := by
  have hpoly : 2560000 * (max 1 1 + 1 + 4) ^ 4 ≤ testLogN := poly_le_thresholdLogN 1 1
  have h1 : 4 ^ 10 ≤ 2560000 := by decide
  have h2 : 1 ≤ (max 1 1 + 1 + 4) ^ 4 := by decide
  exact h1.trans ((Nat.le_mul_of_pos_right _ h2).trans hpoly)

theorem testR_lt_testN : testR * 4 = testN ∧ testR < testN := by
  have h4 := ValidRegime.four_le_thresholdLogN 1 1
  have htn : testN = 2 ^ testLogN := thresholdN_eq 1 1
  rw [htn]
  dsimp only [testR, testLogN]
  refine ⟨by rw [show (4 : ℕ) = 2 ^ 2 by decide, ← Nat.pow_add, Nat.sub_add_cancel (by omega)],
    Nat.pow_lt_pow_right Nat.one_lt_two (by omega)⟩

/-- Non-vacuous `ValidRegime` witness with `R = n / 4 < n`, `U = n ^ 2`, and `V = 2 ^ 64`. -/
theorem sublinearRegime : ValidRegime testU testV testN testR 1 1 1 1 where
  p_min_pos := le_rfl
  q_min_pos := le_rfl
  q_max_pos := le_rfl
  val_pos := Nat.two_pow_pos 64
  n_ge_threshold := le_rfl
  univ_lower := by
    have hu : testU = testN ^ 2 := rfl
    rw [hu, pow_one]
  univ_upper := by
    have hu : testU = testN ^ 2 := rfl
    rw [hu, pow_one]
  redundancy_pos := Nat.two_pow_pos _
  redundancy_le := testR_lt_testN.2.le
  redundancy_lower := by
    have htn : testN = 2 ^ testLogN := thresholdN_eq 1 1
    have htn_ne : testN ≠ 0 := by rw [htn]; exact (Nat.two_pow_pos _).ne'
    have hlog : testLogN ≤ Nat.log 2 testN :=
      (Nat.le_log_iff_pow_le Nat.one_lt_two htn_ne).mpr htn.symm.le
    calc testN ^ 10 = (testR * 4) ^ 10 := by rw [testR_lt_testN.1]
      _ = testR ^ 10 * 4 ^ 10 := Nat.mul_pow _ _ _
      _ ≤ testR ^ 10 * Nat.log 2 testN :=
          Nat.mul_le_mul_left _ (four_pow_ten_le_testLogN.trans hlog)

/-- Non-vacuous `ConcentrationReady` witness via `canonicalSchedule`. -/
theorem sublinearConcentrationReady : (canonicalSchedule sublinearRegime).ConcentrationReady :=
  canonicalSchedule_concentrationReady sublinearRegime

/-- Concrete instantiation of the headline `infoBits + O(R)` bit-budget bound. -/
theorem sublinear_space_bound :
    (canonicalSchedule sublinearRegime).totalTreeBits ≤
      infoBits testU testV testN + spaceConst * testR :=
  totalTreeBits_le_infoBits_add sublinearRegime

/-! ## 2. Both Child-Router Regimes (`trinomial` and `doubleTab`) & Zero-Padding -/

/-- Concrete `depth = 3` schedule (`cap = 16`, `paddedUniv = 32`) exercising top, root, inner, and
leaf levels simultaneously in the small-node `trinomialPolyHash` router regime. -/
@[expose]
def smallDepth3Sched : TreeSchedule where
  univ := 16
  valBound := 4
  cap := 16
  depth := 3
  branchBits := fun _ => 1
  nFloor := fun | 0 => 16 | 1 => 8 | 2 => 4 | _ => 2
  delta := fun _ => 1
  idBits := fun | 1 => 4 | 2 => 3 | _ => 2
  quotOne := 1
  epsInv := 12
  alphaInv := 2
  val_pos := by decide
  two_le_cap := by decide
  two_le_depth := by decide
  quotOne_pos := by decide
  nFloor_zero := rfl
  nFloor_pos ℓ _ := by
    match ℓ with
    | 0 | 1 | 2 => decide
    | _ + 3 => exact Nat.le_succ 1
  branchBits_pos _ _ := le_rfl
  delta_lt_nFloor ℓ h1 hℓ := by
    match ℓ with
    | 0 => omega
    | 1 | 2 | 3 => decide
    | _ + 4 => omega
  nFloor_step_le ℓ hlt := by
    match ℓ with
    | 0 | 1 | 2 => decide
    | _ + 3 => omega
  inner_cap_le ℓ h2 hlt := by
    have : ℓ = 2 := by omega
    subst this; decide
  root_cap_le := by decide
  idBits_step_le ℓ h1 hlt := by
    match ℓ with
    | 0 => omega
    | 1 | 2 => decide
    | _ + 3 => omega
  nHigh_le_two_pow_idBits ℓ h1 hℓ := by
    match ℓ with
    | 0 => omega
    | 1 | 2 | 3 => decide
    | _ + 4 => omega
  univ_le_padded := by decide

theorem smallDepth3Sched_uses_trinomial {ℓ : ℕ} (hℓ : ℓ < smallDepth3Sched.depth) :
    ¬ smallDepth3Sched.usesDoubleTabRouter ℓ := by
  dsimp only [TreeSchedule.usesDoubleTabRouter, smallDepth3Sched]
  rw [FeistelPerm.childRouterThreshold_eq 12 2]
  have hnlow : smallDepth3Sched.nLow ℓ ≤ 15 := by
    have hlt3 : ℓ < 3 := hℓ
    match ℓ with
    | 0 | 1 | 2 => decide
  have hpow : 16 ≤ 2 ^ ((FeistelPerm.childRouterChars 12 * max 2 1) *
      max (4 * FeistelPerm.childRouterChars 12 *
        (2 * FeistelPerm.childRouterRep 12 2 * FeistelPerm.childRouterChars 12) ^
          FeistelPerm.childRouterRep 12 2 *
        (FeistelPerm.childRouterChars 12 *
          (6 * (FeistelPerm.childRouterChars 12 * max 2 1) + 8)) ^
          (2 * FeistelPerm.childRouterChars 12 * FeistelPerm.childRouterRep 12 2))
        (4 * (2 * FeistelPerm.childRouterChars 12 * FeistelPerm.childRouterRep 12 2 + 1) ^ 2)) := by
    have hexp : 4 ≤ (FeistelPerm.childRouterChars 12 * max 2 1) *
        (4 * (2 * FeistelPerm.childRouterChars 12 *
          FeistelPerm.childRouterRep 12 2 + 1) ^ 2) := by
      have hc : FeistelPerm.childRouterChars 12 = 24 := by
        rw [FeistelPerm.childRouterChars_eq]
        decide
      rw [hc]
      exact le_trans (by decide : 4 ≤ 48 * 4)
        (Nat.mul_le_mul_left 48 (Nat.le_mul_of_pos_right 4 (by positivity)))
    exact (by decide : 16 ≤ 2 ^ 4).trans
      (Nat.pow_le_pow_right Nat.two_pos
        (hexp.trans (Nat.mul_le_mul_left _ (le_max_right _ _))))
  change ¬ _ ≤ smallDepth3Sched.nLow ℓ
  omega

/-- Schedule above `childRouterThreshold 12 2`, exercising `RouterSeed.doubleTab`. -/
def largeRouterBase : ℕ := FeistelPerm.childRouterThreshold 12 2 + 8

theorem eight_le_largeRouterBase : 8 ≤ largeRouterBase :=
  Nat.le_add_left 8 _

@[expose]
def largeRouterSched : TreeSchedule where
  univ := 4 * largeRouterBase
  valBound := 4
  cap := 4 * largeRouterBase
  depth := 2
  branchBits := fun _ => 1
  nFloor := fun | 0 => 4 * largeRouterBase | 1 => 2 * largeRouterBase | _ => largeRouterBase
  delta := fun _ => 1
  idBits := fun
    | 1 => Nat.clog 2 (4 * largeRouterBase + 2) + 2
    | _ => Nat.clog 2 (4 * largeRouterBase + 2) + 1
  quotOne := 1
  epsInv := 12
  alphaInv := 2
  val_pos := by decide
  two_le_cap := by have := eight_le_largeRouterBase; omega
  two_le_depth := le_rfl
  quotOne_pos := le_rfl
  nFloor_zero := rfl
  nFloor_pos ℓ _ := by
    have := eight_le_largeRouterBase
    match ℓ with
    | 0 => change 1 ≤ 4 * largeRouterBase; omega
    | 1 => change 1 ≤ 2 * largeRouterBase; omega
    | _ + 2 => change 1 ≤ largeRouterBase; omega
  branchBits_pos _ _ := le_rfl
  delta_lt_nFloor ℓ h1 _ := by
    have := eight_le_largeRouterBase
    match ℓ with
    | 0 => omega
    | 1 => change 1 < 2 * largeRouterBase; omega
    | _ + 2 => change 1 < largeRouterBase; omega
  nFloor_step_le ℓ hlt := by
    match ℓ with
    | 0 => change 2 * (2 * largeRouterBase) ≤ 4 * largeRouterBase; omega
    | 1 => change 2 * largeRouterBase ≤ 2 * largeRouterBase; omega
    | _ + 2 => omega
  inner_cap_le _ h2 hlt := by omega
  root_cap_le := by
    have := eight_le_largeRouterBase
    change 2 * (largeRouterBase - 1) ≤ 2 * largeRouterBase + 1
    omega
  idBits_step_le ℓ h1 hlt := by
    have : ℓ = 1 := by omega
    subst this
    change 1 + (Nat.clog 2 (4 * largeRouterBase + 2) + 1) ≤
      Nat.clog 2 (4 * largeRouterBase + 2) + 2
    omega
  nHigh_le_two_pow_idBits ℓ h1 hℓ := by
    have hcl : 4 * largeRouterBase + 2 ≤ 2 ^ Nat.clog 2 (4 * largeRouterBase + 2) :=
      Nat.le_pow_clog Nat.one_lt_two _
    match ℓ with
    | 0 => omega
    | 1 =>
      change 2 * largeRouterBase + 1 ≤ 2 ^ (Nat.clog 2 (4 * largeRouterBase + 2) + 2)
      exact (by omega : 2 * largeRouterBase + 1 ≤ 4 * largeRouterBase + 2).trans
        (hcl.trans (Nat.pow_le_pow_right Nat.two_pos (by omega)))
    | 2 =>
      change largeRouterBase + 1 ≤ 2 ^ (Nat.clog 2 (4 * largeRouterBase + 2) + 1)
      exact (by omega : largeRouterBase + 1 ≤ 4 * largeRouterBase + 2).trans
        (hcl.trans (Nat.pow_le_pow_right Nat.two_pos (by omega)))
    | _ + 3 => omega
  univ_le_padded := by
    have hcl : 4 * largeRouterBase + 2 ≤ 2 ^ Nat.clog 2 (4 * largeRouterBase + 2) :=
      Nat.le_pow_clog Nat.one_lt_two _
    change 4 * largeRouterBase + 4 * largeRouterBase ≤
      2 * 2 ^ (Nat.clog 2 (4 * largeRouterBase + 2) + 2) * 1
    rw [Nat.mul_one]
    calc 4 * largeRouterBase + 4 * largeRouterBase
        ≤ 2 * (4 * largeRouterBase + 2) := by omega
      _ ≤ 2 * 2 ^ Nat.clog 2 (4 * largeRouterBase + 2) := Nat.mul_le_mul_left 2 hcl
      _ ≤ 2 * 2 ^ (Nat.clog 2 (4 * largeRouterBase + 2) + 2) :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right Nat.two_pos (by omega))

theorem largeRouterSched_uses_doubleTab :
    largeRouterSched.usesDoubleTabRouter 0 ∧ largeRouterSched.usesDoubleTabRouter 1 := by
  dsimp only [TreeSchedule.usesDoubleTabRouter, largeRouterSched, TreeSchedule.nLow,
    largeRouterBase]
  exact ⟨by simp; omega, by simp; omega⟩

theorem both_router_regimes_exercised
    (sSmall : smallDepth3Sched.SmallRouterSeed 0)
    (sLarge : largeRouterSched.LargeRouterSeed 0) :
    Function.Involutive (smallDepth3Sched.routerPerm 0
      (.trinomial (smallDepth3Sched_uses_trinomial (by decide)) sSmall)) ∧
    Function.Involutive (largeRouterSched.routerPerm 0
      (.doubleTab largeRouterSched_uses_doubleTab.1 sLarge)) :=
  ⟨smallDepth3Sched.routerPerm_involutive 0 _, largeRouterSched.routerPerm_involutive 0 _⟩

theorem small_router_zero_pad_compat {ℓ : ℕ}
    (hℓ : ℓ < (canonicalSchedule sublinearRegime).depth)
    (hsmall : ¬ (canonicalSchedule sublinearRegime).usesDoubleTabRouter ℓ)
    (seed : (canonicalSchedule sublinearRegime).SmallRouterSeed ℓ)
    (x : Fin ((canonicalSchedule sublinearRegime).routerRightUniv ℓ)) :
    (canonicalSchedule sublinearRegime).routerRound ℓ (.trinomial hsmall seed) x =
      trinomialPolyHash
        (trinomialStep ((canonicalSchedule sublinearRegime).routerRightUniv ℓ)
          ((canonicalSchedule sublinearRegime).branchBits ℓ))
        (smallRouterMaxDegree (canonicalSchedule sublinearRegime).epsInv
          (canonicalSchedule sublinearRegime).alphaInv)
        ((canonicalSchedule sublinearRegime).routerRightUniv ℓ)
        ((canonicalSchedule sublinearRegime).branchBits ℓ)
        ((canonicalSchedule sublinearRegime).padSmallRouterSeed ℓ seed) x :=
  (canonicalSchedule sublinearRegime).routerRound_trinomial_eq_padded
    sublinearConcentrationReady hℓ hsmall seed x

/-! ## 3. Executable Node Storage & Section 5.6 Metadata Separation (`StorageNode`) -/

-- Concrete `#eval` trace of `WaitingList` (`empty`, `push`, `lookup`, `pop`, `remove`).
/-- info: (some 5, some 2, none, (3, 5), none, some 2) -/
#guard_msgs in
#eval
  let w0 := WaitingList.empty 3 4 2
  let w1 := w0.push ⟨2, by decide⟩ ⟨2, by decide⟩
    (by rw [← w0.card_dom]; simp [w0]) (by simp [w0])
  let w2 := w1.push ⟨3, by decide⟩ ⟨5, by decide⟩
    (by rw [← w1.card_dom]; simp [w1, w0]) (by simp [w1, w0])
  let lk3 := (w2.lookup ⟨3, by decide⟩).map Fin.val
  let lk2 := (w2.lookup ⟨2, by decide⟩).map Fin.val
  let lk0 := (w2.lookup ⟨0, by decide⟩).map Fin.val
  let popped := w2.pop (⟨⟨3, by decide⟩, by simp [w2, w1]⟩)
  let headPair := (popped.1.1.val, popped.1.2.val)
  let afterPop3 := (popped.2.lookup ⟨3, by decide⟩).map Fin.val
  let afterPop2 := (popped.2.lookup ⟨2, by decide⟩).map Fin.val
  (lk3, lk2, lk0, headPair, afterPop3, afterPop2)

-- Concrete `#eval` trace of `StorageTable` separating `StorageTableMeta.locateSlot`
-- (`Section 5.6`) from `(quot, val)` payload slots across `insert`, `overwrite`, and `delete`.
/-- info: (some 0, some (3, 1), some 0, some (3, 2), none, some (1, 0)) -/
#guard_msgs in
#eval
  let t0 := StorageTable.empty 3 2 (Q := 4) (V := 4) (by decide) (by decide)
  let t1 := t0.insert ⟨5, by decide⟩ (⟨3, by decide⟩, ⟨1, by decide⟩)
    (by simp [t0]) (by simp [t0])
  let t2 := t1.insert ⟨2, by decide⟩ (⟨1, by decide⟩, ⟨0, by decide⟩)
    (by simp [t1, t0]) (by simp [t1, t0])
  let slotBefore := (t2.tableMeta.locateSlot ⟨5, by decide⟩).map Fin.val
  let qBefore := (t2.query ⟨5, by decide⟩).map fun p => (p.1.val, p.2.val)
  let t3 := t2.overwrite ⟨5, by decide⟩ (⟨3, by decide⟩, ⟨2, by decide⟩)
    (by simp [t2, t1])
  let slotAfter := (t3.tableMeta.locateSlot ⟨5, by decide⟩).map Fin.val
  let qAfter := (t3.query ⟨5, by decide⟩).map fun p => (p.1.val, p.2.val)
  let t4 := t3.delete ⟨5, by decide⟩
  let qDel := (t4.query ⟨5, by decide⟩).map fun p => (p.1.val, p.2.val)
  let qRem := (t4.query ⟨2, by decide⟩).map fun p => (p.1.val, p.2.val)
  (slotBefore, qBefore, slotAfter, qAfter, qDel, qRem)

-- Concrete `RootValPool` capacity conservation check on `smallDepth3Sched`:
-- `8` leaves (`1` key each) + `4` inner nodes (`1` key each) = `12` non-root keys, leaving
-- `rootValPoolCap = 16 - 4 * 3 = 4` root value slots for up to `16` active keys.
example : smallDepth3Sched.rootValPoolCap = 4 := by decide

example {rootKeys totalActive : ℕ}
    (hpart : smallDepth3Sched.numNodes 3 * smallDepth3Sched.nLow 3 +
      (∑ ℓ ∈ Finset.Ico 2 3, smallDepth3Sched.numNodes ℓ * smallDepth3Sched.tableCap ℓ) +
        rootKeys = totalActive)
    (hcap : totalActive ≤ 16) :
    rootKeys ≤ smallDepth3Sched.rootValPoolCap :=
  smallDepth3Sched.rootKeys_le_rootValPoolCap hpart hcap

/-! ## 4. Multi-Level Tree Operations, `Algorithm 3`, `Algorithm 4` & DFS Metadata -/

-- Level-coordinate bijection and Section 5.6 DFS pre-order metadata on `smallDepth3Sched`.
theorem smallDepth3_routing_and_dfs_meta (st : smallDepth3Sched.TreeState)
    (u₂ : Fin (smallDepth3Sched.numNodes 2)) :
    Function.Bijective (st.seeds.levelCoordEquiv 2 (by decide) (by decide)) ∧
    st.dfsSubtreeMeta 2 (by decide) (by decide) u₂ ≠ [] :=
  ⟨(st.seeds.levelCoordEquiv 2 (by decide) (by decide)).bijective,
    st.dfsSubtreeMeta_nonempty (by decide) (by decide) u₂⟩

/-- End-to-end dictionary trace on `canonicalSchedule sublinearRegime` exercising `initTree`,
fresh `insert`s, in-place key overwrite, present-key `delete`, and absent-key `delete`, verifying
both `WellFormed` preservation and exact `query` outputs at every step. -/
theorem endToEnd_dictionary_trace
    (scheme : DynamicMatching.Scheme
      (2 ^ (canonicalSchedule sublinearRegime).idBits (canonicalSchedule sublinearRegime).depth)
      ((canonicalSchedule sublinearRegime).nLow (canonicalSchedule sublinearRegime).depth)) :
    let P := canonicalSchedule sublinearRegime
    let hcr := sublinearConcentrationReady
    let hU : 4 ≤ P.univ := by
      have h2n : 2 * testN ≤ testU := sublinearRegime.two_mul_n_le_univ
      have hn2 : 2 ≤ testN := sublinearRegime.two_le_n
      change 4 ≤ testU
      omega
    let k₁ : Fin P.univ := ⟨0, by omega⟩
    let k₂ : Fin P.univ := ⟨1, by omega⟩
    let k₃ : Fin P.univ := ⟨2, by omega⟩
    let v₁ : Fin P.valBound := ⟨1, by change 1 < 2 ^ 64; decide⟩
    let v₂ : Fin P.valBound := ⟨2, by change 2 < 2 ^ 64; decide⟩
    let v₁' : Fin P.valBound := ⟨3, by change 3 < 2 ^ 64; decide⟩
    let st0 := P.initTree hcr scheme
    let st1 := st0.insert hcr scheme k₁ v₁
    let st2 := st1.insert hcr scheme k₂ v₂
    let st3 := st2.insert hcr scheme k₁ v₁'
    let st4 := st3.delete hcr scheme k₂
    let st5 := st4.delete hcr scheme k₃
    st0.query scheme k₁ = none ∧
    st2.query scheme k₁ = some 1 ∧
    st2.query scheme k₂ = some 2 ∧
    st3.query scheme k₁ = some 3 ∧
    st3.query scheme k₂ = some 2 ∧
    st4.query scheme k₁ = some 3 ∧
    st4.query scheme k₂ = none ∧
    st5.query scheme k₁ = some 3 ∧
    st5.query scheme k₃ = none ∧
    ∃ dict5, st5.WellFormed scheme dict5 := by
  intro P hcr hU k₁ k₂ k₃ v₁ v₂ v₁' st0 st1 st2 st3 st4 st5
  have hk12 : k₁ ≠ k₂ := by decide
  have hk13 : k₁ ≠ k₃ := by decide
  have hcap2 : 2 < P.cap := by
    have h4 : 4 ≤ thresholdLogN 1 1 := ValidRegime.four_le_thresholdLogN 1 1
    have h16 : 16 ≤ testN :=
      (by decide : 16 ≤ 2 ^ 4).trans (Nat.pow_le_pow_right Nat.two_pos h4)
    change 2 < testN
    omega
  have hwf0 := P.wellFormed_initTree hcr scheme
  have hc0 : (Dictionary.dom (Dictionary.empty P.univ)).card < P.cap := by
    have hempty : Dictionary.dom (Dictionary.empty P.univ) = ∅ := by
      ext u; simp [Dictionary.dom, Dictionary.empty]
    rw [hempty]; exact Nat.zero_lt_of_lt hcap2
  have hwf1 := st0.wellFormed_insert hcr hwf0 k₁ v₁ (Or.inr hc0)
  have hdom1 : Dictionary.dom (Function.update (Dictionary.empty P.univ) k₁ (some v₁.val)) ⊆
      {k₁} := by
    intro u hu
    simp only [Dictionary.dom, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hu ⊢
    by_contra hne
    rw [Function.update_of_ne hne] at hu
    simp [Dictionary.empty] at hu
  have hc1 :
      (Dictionary.dom (Function.update (Dictionary.empty P.univ) k₁ (some v₁.val))).card <
        P.cap :=
    (Finset.card_le_card hdom1).trans_lt (by simpa using Nat.lt_trans Nat.one_lt_two hcap2)
  have hwf2 := st1.wellFormed_insert hcr hwf1 k₂ v₂ (Or.inr hc1)
  have hk1_mem2 : k₁ ∈ Dictionary.dom
      (Function.update (Function.update (Dictionary.empty P.univ) k₁ (some v₁.val))
        k₂ (some v₂.val)) := by
    simp [Dictionary.dom, Function.update_of_ne hk12]
  have hwf3 := st2.wellFormed_insert hcr hwf2 k₁ v₁' (Or.inl hk1_mem2)
  have hwf4 := st3.wellFormed_delete hcr hwf3 k₂
  have hwf5 := st4.wellFormed_delete hcr hwf4 k₃
  have hq0 : ∀ u, st0.query scheme u = none := P.query_initTree hcr scheme
  have hq1 : ∀ u, st1.query scheme u = Function.update (st0.query scheme) k₁ (some 1) u :=
    st0.query_insert hcr hwf0 k₁ v₁ (Or.inr hc0)
  have hq2 : ∀ u, st2.query scheme u = Function.update (st1.query scheme) k₂ (some 2) u :=
    st1.query_insert hcr hwf1 k₂ v₂ (Or.inr hc1)
  have hq3 : ∀ u, st3.query scheme u = Function.update (st2.query scheme) k₁ (some 3) u :=
    st2.query_insert hcr hwf2 k₁ v₁' (Or.inl hk1_mem2)
  have hq4 : ∀ u, st4.query scheme u = Function.update (st3.query scheme) k₂ none u :=
    st3.query_delete hcr hwf3 k₂
  have hq5 : ∀ u, st5.query scheme u = Function.update (st4.query scheme) k₃ none u :=
    st4.query_delete hcr hwf4 k₃
  refine ⟨hq0 k₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, _, hwf5⟩
  · rw [hq2 k₁, Function.update_of_ne hk12, hq1 k₁, Function.update_self]
  · rw [hq2 k₂, Function.update_self]
  · rw [hq3 k₁, Function.update_self]
  · rw [hq3 k₂, Function.update_of_ne hk12.symm, hq2 k₂, Function.update_self]
  · rw [hq4 k₁, Function.update_of_ne hk12, hq3 k₁, Function.update_self]
  · rw [hq4 k₂, Function.update_self]
  · rw [hq5 k₁, Function.update_of_ne hk13, hq4 k₁, Function.update_of_ne hk12, hq3 k₁,
      Function.update_self]
  · rw [hq5 k₃, Function.update_self]

/-- Direct instantiation of `Algorithm 3` (`deleteAndGetQuotient_spec`) and `Algorithm 4`
(`rehashSubtree` locality and `wellFormedPadded_rehashSubtree`) on any `TreeSchedule`. -/
theorem deleteAndGetQuotient_and_rehashSubtree_specs
    {P : TreeSchedule}
    {scheme : DynamicMatching.Scheme (2 ^ P.idBits P.depth) (P.nLow P.depth)}
    {st : P.TreeState} {d : P.PaddedDict} {storeLvl : Fin P.paddedUniv → ℕ}
    (hwf : st.WellFormedPadded scheme d storeLvl)
    {z : Fin P.paddedUniv} {vz : Fin P.valBound} (hdz : d z = some vz)
    (hloads : ∀ (j : ℕ) (_hj2 : 2 ≤ j) (hj : j ≤ P.depth),
      P.nLow j <
        (st.seeds.activeAt (P.paddedDom d) j hj
          (P.ancestorAt hj (st.seeds.nodeAt P.depth le_rfl z))).card)
    {ℓ₀ : ℕ} (h1₀ : 1 ≤ ℓ₀) (hℓ₀ : ℓ₀ ≤ P.depth) (u₀ : Fin (P.numNodes ℓ₀))
    (seeds' : P.SeedAssignment)
    (houtside : ∀ (j : ℕ) (hj : j ≤ P.depth) (v : Fin (P.numNodes j)),
      ¬ P.InSubtree ℓ₀ u₀ j v → seeds'.seed j hj v = st.seeds.seed j hj v)
    (hgood' : seeds'.AllGoodSeeds (P.paddedDom d))
    (v_leaf : Fin (P.numNodes P.depth)) (hnot_sub : ¬ P.InSubtree ℓ₀ u₀ P.depth v_leaf) :
    let h1d : 1 ≤ P.depth := Nat.one_le_of_lt P.two_le_depth
    let delRes := st.deleteAndGetQuotient scheme P.depth h1d le_rfl
      (st.seeds.nodeAt P.depth le_rfl z) (st.seeds.idAt P.depth h1d le_rfl z)
    let st_reh := st.rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood'
    delRes.2 = (st.seeds.quotAt P.depth h1d le_rfl z, vz) ∧
    st_reh.leaves v_leaf = st.leaves v_leaf ∧
    (∃ storeLvl', st_reh.WellFormedPadded scheme d storeLvl') := by
  intro h1d delRes st_reh
  have hz : z ∈ P.paddedDom d := (P.mem_paddedDom_iff d z).mpr (by simp [hdz])
  obtain ⟨hq, hv, _, _⟩ := TreeSchedule.TreeState.deleteAndGetQuotient_spec hwf P.depth h1d le_rfl
    _ z vz hdz rfl (hwf.storeLvl_bounds z hz).2 hloads
  exact ⟨Prod.ext hq hv,
    st.rehashSubtree_untouched_leaves hwf h1₀ hℓ₀ u₀ seeds' houtside hgood' v_leaf hnot_sub,
    st.wellFormedPadded_rehashSubtree hwf ℓ₀ hℓ₀ u₀ seeds' houtside hgood'⟩

/-! ## 5. Single-Node Survival (`Claim 5.4`) and Expected Rehashing Work (`Lemma 5.3`) -/

theorem window_survival_on_sublinearRegime {k ℓ : ℕ}
    (hℓ : ℓ ≤ (canonicalSchedule sublinearRegime).depth)
    (hk : k ≤ (canonicalSchedule sublinearRegime).rehashWindow ℓ)
    (u : Fin ((canonicalSchedule sublinearRegime).numNodes ℓ))
    (S_seq : Fin (k + 1) → Finset (Fin (canonicalSchedule sublinearRegime).paddedUniv))
    (seeds_seq : Fin (k + 1) → (canonicalSchedule sublinearRegime).SeedAssignment)
    (hgood : ∀ i : Fin (k + 1), (seeds_seq i).AllGoodSeeds (S_seq i))
    (hanc_fixed : ∀ (i : Fin (k + 1)) (j : ℕ) (hj : j < ℓ),
      (seeds_seq i).seed j (hj.le.trans hℓ)
        ((canonicalSchedule sublinearRegime).ancestorAt hj.le u) =
        (seeds_seq 0).seed j (hj.le.trans hℓ)
          ((canonicalSchedule sublinearRegime).ancestorAt hj.le u)) :
    let P := canonicalSchedule sublinearRegime
    (1 : ℝ) / 2 ≤ ((PMF.uniformOfFintype (P.NodeSeed ℓ)).toOuterMeasure
      {g : P.NodeSeed ℓ |
        ∀ i : Fin (k + 1),
          P.IsGoodNodeSeed ℓ g ((seeds_seq 0).primSetAt (S_seq i) ℓ hℓ u)}).toReal :=
  TreeSchedule.SeedAssignment.prob_survives_window_of_ancestorFree
    sublinearConcentrationReady hℓ hk u S_seq seeds_seq hgood hanc_fixed

theorem expected_rehashWork_on_sublinearRegime (M : ℕ) {succRehashes : ℕ → ℝ}
    (hnonneg : ∀ ℓ ≤ (canonicalSchedule sublinearRegime).depth, 0 ≤ succRehashes ℓ)
    (hbase : succRehashes 0 ≤
      1 + 20 * (M : ℝ) / ((canonicalSchedule sublinearRegime).nFloor 0 : ℝ) ^ 2)
    (hstep : ∀ ℓ < (canonicalSchedule sublinearRegime).depth,
      succRehashes (ℓ + 1) ≤
        succRehashes ℓ * ((canonicalSchedule sublinearRegime).branchFactor ℓ : ℝ) +
          20 * (M : ℝ) / ((canonicalSchedule sublinearRegime).nFloor (ℓ + 1) : ℝ) ^ 2) :
    ∑ ℓ ∈ Finset.range ((canonicalSchedule sublinearRegime).depth + 1),
        2 * succRehashes ℓ * ((canonicalSchedule sublinearRegime).nFloor ℓ : ℝ) ≤
      42 * ((testN + M : ℕ) : ℝ) * (Nat.logStar testN : ℝ) :=
  canonicalSchedule_rehashWork_le_mul_logStar sublinearRegime hnonneg hbase hstep

end CslibFrontierTests.SubconstantTreeModel
