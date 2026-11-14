/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.Params
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.NodeSeeds
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.SeedBounds
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.NodeSlackBounds
import Mathlib.Tactic.Positivity

/-!
# Multi-Level Subconstant-Redundancy Schedule and Bit Budget Tests

Exercises:
1. `SubconstantRedundancy.Params` (`Schedule`, `Canonical`, `BitBudget`):
   - concrete checks of clamped `effRedundancy`, `redundancyRatio`, `treeDepth`, and `infoBits`;
   - non-vacuous smaller-than-`n` `ValidRegime` instance (`R = n / 4 < n`, `U = n ^ 2`,
     `V = 2 ^ 64`), `canonicalSchedule`, `ConcentrationReady`, the operational metadata bound
     `treeMeta_slack_le`, and the `infoBits + O(R)` space bound `totalTreeBits_le_infoBits_add`;
2. `SubconstantRedundancy.BitBudget`:
   - `treeMetaBits`, `totalTreeBits`, and `redundancySlack` accounting on a depth-`3` schedule;
3. `SubconstantRedundancy.NodeSeeds`:
   - both child-router regimes (`RouterSeed.trinomial` below `childRouterThreshold` on a depth-`3`
     schedule and `RouterSeed.doubleTab` above `childRouterThreshold`), zero-padded degree
     compatibility (`routerRound_trinomial_eq_padded`), and good-seed existence
     (`exists_isGoodNodeSeed`);
4. `SubconstantRedundancy.NodeSlackBounds`:
   - `spaceConst` and `redundancySlack_le_mul_effRedundancy`.
-/

public section

namespace CslibFrontierTests.SubconstantParams

open Cslib
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

/-- Concrete instantiation of the operational metadata bit budget bound. -/
theorem sublinear_treeMeta_slack_bound :
    (canonicalSchedule sublinearRegime).treeMetaBits * redundancyRatio testN testR ≤ testN :=
  treeMeta_slack_le sublinearRegime

/-- Concrete instantiation of the redundancy slack bound. -/
theorem sublinear_redundancy_slack_bound :
    (canonicalSchedule sublinearRegime).redundancySlack ≤ 150000 * effRedundancy testN testR :=
  redundancySlack_le_mul_effRedundancy sublinearRegime

/-- Concrete instantiation of the headline `infoBits + O(R)` bit-budget bound. -/
theorem sublinear_space_bound :
    (canonicalSchedule sublinearRegime).totalTreeBits ≤
      infoBits testU testV testN + spaceConst * testR :=
  totalTreeBits_le_infoBits_add sublinearRegime

/-! ## 2. Concrete Bit Budget Accounting -/

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

-- Tree operational metadata bits on small schedule: clog 2 (16 + 1) + 1 = 5 + 1 = 6.
example : smallDepth3Sched.treeMetaBits = 6 := by decide

-- Positive capacity on small schedule.
example : 0 < smallDepth3Sched.cap := by decide

/-! ## 3. Both Child-Router Regimes (`trinomial` and `doubleTab`) & Seed Concentration -/

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

/-- Good-seed existence on the canonical schedule. -/
theorem sublinear_exists_good_seed {ℓ : ℕ}
    (hℓ : ℓ ≤ (canonicalSchedule sublinearRegime).depth)
    (S : Finset ((canonicalSchedule sublinearRegime).PrimId ℓ))
    (hlo : (canonicalSchedule sublinearRegime).nLow ℓ ≤ #S)
    (hhi : #S ≤ (canonicalSchedule sublinearRegime).nHigh ℓ) :
    ∃ s : (canonicalSchedule sublinearRegime).NodeSeed ℓ,
      (canonicalSchedule sublinearRegime).IsGoodNodeSeed ℓ s S :=
  (canonicalSchedule sublinearRegime).exists_isGoodNodeSeed sublinearConcentrationReady hℓ S hlo hhi

end CslibFrontierTests.SubconstantParams

end
