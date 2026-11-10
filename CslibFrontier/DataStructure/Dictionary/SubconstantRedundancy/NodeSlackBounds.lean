/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.SeedBounds
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Node, Pool, Waiting-List, and Hash-Seed Redundancy Slack Bounds

This module bounds the per-level node-metadata, root-value-pool directory, waiting-list, and
hash-seed components of `(canonicalSchedule h).redundancySlack` by `O(n / redundancyRatio n R)`
across `ValidRegime` ([LiLiangYuZhou2024], `arXiv:2310.20536v1`, Sections 5.2 and 5.4–5.6,
PDF pp. 27–36 / printed pp. 26–35).

## Main results

* `leaf_and_deficit_slack_le`, `nonLeaf_tables_slack_le`, `rootExtra_and_poolDir_slack_le`,
  `waitingLists_and_hashSeeds_slack_le`: inverse-redundancy bounds on the non-shared-table
  components of `redundancySlack`.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Finset

theorem canonical_target_bounds {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (∀ j ≤ treeDepth U (redundancyRatio n R),
        1 ≤ targetSize n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) j) ∧
      (∀ j ≤ treeDepth U (redundancyRatio n R),
        targetSize n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) j ≤ n) := by
  have hr256 : minRedundancyRatio ≤ redundancyRatio n R := h.redundancyRatio_bounds.1
  have h4r : 4 * redundancyRatio n R ≤ Nat.log 2 U := h.four_mul_redundancyRatio_le_log_univ
  have hn18 : 2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ n := h.two_pow_eighteen_mul_log_univ_pow_le
  have hstep : ∀ i < treeDepth U (redundancyRatio n R),
      2 ^ 18 * targetSize n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) (i + 1) ≤
        targetSize n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) i :=
    fun i hi => two_pow_eighteen_mul_targetSize_succ_le hr256 h4r hn18 hi
  refine ⟨fun j hj => targetSize_pos (by have := h.two_le_n; omega)
    (by dsimp [minRedundancyRatio] at hr256; omega) h4r hj rfl,
    targetSize_le_of_step hstep⟩

theorem canonicalSchedule_branchFactor_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) (ℓ : ℕ) :
    (canonicalSchedule h).branchFactor ℓ =
      branchFactor n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := rfl

theorem canonicalSchedule_nFloor_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) (ℓ : ℕ) :
    (canonicalSchedule h).nFloor ℓ =
      nFloor n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := rfl

theorem canonicalSchedule_delta_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) (ℓ : ℕ) :
    (canonicalSchedule h).delta ℓ =
      delta n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := rfl

theorem canonicalSchedule_idBits_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) (ℓ : ℕ) :
    (canonicalSchedule h).idBits ℓ =
      idBits n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := rfl

theorem canonicalSchedule_nFloor_div_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hℓ : ℓ ≤ (canonicalSchedule h).depth) :
    (canonicalSchedule h).nFloor ℓ = n / (canonicalSchedule h).numNodes ℓ := by
  rw [canonicalSchedule_nFloor_eq h ℓ, canonicalSchedule_numNodes_eq h hℓ]
  rfl

theorem delta_pos_of_le_depth {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {j : ℕ}
    (hj : j ≤ (canonicalSchedule h).depth) :
    1 ≤ (canonicalSchedule h).delta j := by
  have hnF : 256 ^ 9 ≤ (canonicalSchedule h).nFloor j := nFloor_ge_pow_256 h hj
  have hy1 : 1 ≤ (canonicalSchedule h).nFloor j :=
    (Nat.one_le_pow 9 256 (by decide)).trans hnF
  rw [canonicalSchedule_delta_eq h j]
  dsimp only [delta]
  rw [← canonicalSchedule_nFloor_eq h j]
  exact (Nat.le_nthRoot_iff (by decide)).mpr (by nlinarith)

private theorem numNodes_mul_tableCap_of_schedule (P : TreeSchedule) {ℓ : ℕ}
    (h1 : 1 ≤ ℓ) (hlt : ℓ < P.depth)
    (hnf_div : P.nFloor (ℓ + 1) = P.nFloor ℓ / P.branchFactor ℓ)
    (hd_next_pos : 1 ≤ P.delta (ℓ + 1))
    (h10d : ℓ = 1 → 10 * P.delta 1 ≤ P.branchFactor 1 * P.delta 2) :
    P.numNodes ℓ * P.tableCap ℓ ≤ 3 * P.numNodes (ℓ + 1) * P.delta (ℓ + 1) := by
  have hB_pos : 0 < P.branchFactor ℓ := P.branchFactor_pos ℓ
  have hnf_le : P.nFloor ℓ ≤ P.branchFactor ℓ * P.nFloor (ℓ + 1) + P.branchFactor ℓ := by
    have hdiv := Nat.div_add_mod (P.nFloor ℓ) (P.branchFactor ℓ)
    have hmod := Nat.mod_lt (P.nFloor ℓ) hB_pos
    rw [← hnf_div] at hdiv
    omega
  have hd_next_lt : P.delta (ℓ + 1) < P.nFloor (ℓ + 1) :=
    P.delta_lt_nFloor (ℓ + 1) (by omega) hlt
  have hB_le_Bd : P.branchFactor ℓ ≤ P.branchFactor ℓ * P.delta (ℓ + 1) :=
    Nat.le_mul_of_pos_right _ hd_next_pos
  have hcap_le : P.tableCap ℓ ≤ 3 * P.branchFactor ℓ * P.delta (ℓ + 1) := by
    have hnl_next : P.nLow (ℓ + 1) = P.nFloor (ℓ + 1) - P.delta (ℓ + 1) := by
      dsimp only [TreeSchedule.nLow]; rw [ite_eq_right (by omega)]
    have hB_sub : P.branchFactor ℓ * P.nLow (ℓ + 1) =
        P.branchFactor ℓ * P.nFloor (ℓ + 1) - P.branchFactor ℓ * P.delta (ℓ + 1) := by
      rw [hnl_next, Nat.mul_sub_left_distrib]
    have hBd_le : P.branchFactor ℓ * P.delta (ℓ + 1) ≤ P.branchFactor ℓ * P.nFloor (ℓ + 1) :=
      Nat.mul_le_mul_left _ hd_next_lt.le
    rcases eq_or_lt_of_le h1 with rfl | hgt1
    · have htc1 : P.tableCap 1 = (P.nFloor 1 + P.delta 1) - P.branchFactor 1 * P.nLow 2 := by
        dsimp only [TreeSchedule.tableCap, TreeSchedule.nHigh]; simp
      have h10 := h10d rfl
      change P.nFloor 1 ≤ P.branchFactor 1 * P.nFloor 2 + P.branchFactor 1 at hnf_le
      change P.branchFactor 1 ≤ P.branchFactor 1 * P.delta 2 at hB_le_Bd
      change P.branchFactor 1 * P.nLow 2 =
        P.branchFactor 1 * P.nFloor 2 - P.branchFactor 1 * P.delta 2 at hB_sub
      change P.branchFactor 1 * P.delta 2 ≤ P.branchFactor 1 * P.nFloor 2 at hBd_le
      change P.tableCap 1 ≤ 3 * P.branchFactor 1 * P.delta 2
      rw [htc1, hB_sub, Nat.mul_assoc 3]
      omega
    · have htc : P.tableCap ℓ = (P.nFloor ℓ - P.delta ℓ) -
          P.branchFactor ℓ * P.nLow (ℓ + 1) := by
        dsimp only [TreeSchedule.tableCap, TreeSchedule.nLow]
        rw [ite_eq_right (by omega), ite_eq_left hlt, ite_eq_right (by omega)]
      rw [htc, hB_sub, Nat.mul_assoc 3]
      omega
  calc P.numNodes ℓ * P.tableCap ℓ
      ≤ P.numNodes ℓ * (3 * P.branchFactor ℓ * P.delta (ℓ + 1)) :=
        Nat.mul_le_mul_left _ hcap_le
    _ = 3 * (P.numNodes ℓ * P.branchFactor ℓ) * P.delta (ℓ + 1) := by ring
    _ = 3 * P.numNodes (ℓ + 1) * P.delta (ℓ + 1) := by rw [← P.numNodes_succ ℓ]

theorem numNodes_mul_tableCap_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (h1 : 1 ≤ ℓ) (hlt : ℓ < (canonicalSchedule h).depth) :
    (canonicalSchedule h).numNodes ℓ * (canonicalSchedule h).tableCap ℓ ≤
      3 * (canonicalSchedule h).numNodes (ℓ + 1) * (canonicalSchedule h).delta (ℓ + 1) := by
  have hlt_k : ℓ < treeDepth U (redundancyRatio n R) := hlt
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  have hstep_t := two_pow_eighteen_mul_targetSize_succ_le h.redundancyRatio_bounds.1
    h.four_mul_redundancyRatio_le_log_univ h.two_pow_eighteen_mul_log_univ_pow_le hlt_k
  have hS17 := cumBranchBits_add_seventeen_le (hT_pos ℓ hlt_k.le) (hT_pos (ℓ + 1) hlt_k)
    (hT_le ℓ hlt_k.le) hstep_t
  refine numNodes_mul_tableCap_of_schedule (canonicalSchedule h) h1 hlt ?_
    (delta_pos_of_le_depth h hlt) ?_
  · rw [canonicalSchedule_nFloor_eq h (ℓ + 1), canonicalSchedule_nFloor_eq h ℓ,
      canonicalSchedule_branchFactor_eq h ℓ]
    exact nFloor_succ_eq_div (by omega)
  · intro hℓ1
    subst hℓ1
    have hx8 : 8 ≤ nFloor n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) 2 := by
      rw [← canonicalSchedule_nFloor_eq h 2]
      exact (by decide : 8 ≤ 256 ^ 9).trans (nFloor_ge_pow_256 h hlt)
    rw [canonicalSchedule_delta_eq h 1, canonicalSchedule_branchFactor_eq h 1,
      canonicalSchedule_delta_eq h 2]
    exact ten_mul_delta_le_branchFactor_mul_delta_succ hS17 hx8

private theorem leaf_and_deficit_of_schedule (P : TreeSchedule) {n r : ℕ}
    (hcap : P.cap = n)
    (hNk_r : P.numNodes P.depth * r ≤ n)
    (hnf_div : P.nFloor P.depth = n / P.numNodes P.depth)
    (hd_pos : 1 ≤ P.delta P.depth)
    (hNd_r : P.numNodes P.depth * P.delta P.depth * r ≤ n) :
    (3 * P.numNodes P.depth + 3 * (P.cap - P.numNodes P.depth * P.nLow P.depth)) * r ≤ 9 * n := by
  have hk2 := P.two_le_depth
  have hn_lt : n ≤ P.numNodes P.depth * P.nFloor P.depth + P.numNodes P.depth := by
    have hdiv := Nat.div_add_mod n (P.numNodes P.depth)
    have hmod := Nat.mod_lt n (P.numNodes_pos P.depth)
    rw [← hnf_div] at hdiv
    omega
  have hd_lt : P.delta P.depth < P.nFloor P.depth :=
    P.delta_lt_nFloor P.depth (by omega) le_rfl
  have hdef_le : P.cap - P.numNodes P.depth * P.nLow P.depth ≤
      2 * P.numNodes P.depth * P.delta P.depth := by
    have hnl : P.nLow P.depth = P.nFloor P.depth - P.delta P.depth := by
      dsimp only [TreeSchedule.nLow]; rw [ite_eq_right (by omega)]
    have hsub : P.numNodes P.depth * P.nLow P.depth =
        P.numNodes P.depth * P.nFloor P.depth - P.numNodes P.depth * P.delta P.depth := by
      rw [hnl, Nat.mul_sub_left_distrib]
    have hNd_le : P.numNodes P.depth * P.delta P.depth ≤
        P.numNodes P.depth * P.nFloor P.depth := Nat.mul_le_mul_left _ hd_lt.le
    have hN_le_Nd : P.numNodes P.depth ≤ P.numNodes P.depth * P.delta P.depth :=
      Nat.le_mul_of_pos_right _ hd_pos
    rw [hcap, hsub, Nat.mul_assoc 2]
    omega
  have hdef_r : (P.cap - P.numNodes P.depth * P.nLow P.depth) * r ≤ 2 * n := by
    calc (P.cap - P.numNodes P.depth * P.nLow P.depth) * r
        ≤ (2 * P.numNodes P.depth * P.delta P.depth) * r := Nat.mul_le_mul_right r hdef_le
      _ = 2 * (P.numNodes P.depth * P.delta P.depth * r) := by ring
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 hNd_r
  nlinarith

theorem leaf_and_deficit_slack_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (3 * (canonicalSchedule h).numNodes (canonicalSchedule h).depth +
      3 * ((canonicalSchedule h).cap -
        (canonicalSchedule h).numNodes (canonicalSchedule h).depth *
          (canonicalSchedule h).nLow (canonicalSchedule h).depth)) *
      redundancyRatio n R ≤ 9 * n := by
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  obtain ⟨hNTk, _⟩ := numNodes_mul_targetSize_bounds (hT_pos _ le_rfl) (hT_le _ le_rfl)
  have hk2 := two_le_treeDepth U (redundancyRatio n R)
  have hTk_eq : targetSize n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R))
      (treeDepth U (redundancyRatio n R)) = (redundancyRatio n R) ^ 9 := by
    rw [targetSize_eq_levelScale_pow (by omega)]
    simp [levelScale]
  refine leaf_and_deficit_of_schedule (canonicalSchedule h) rfl ?_
    (canonicalSchedule_nFloor_div_eq h le_rfl) (delta_pos_of_le_depth h le_rfl) ?_
  · rw [canonicalSchedule_numNodes_eq h le_rfl, canonicalSchedule_depth]
    exact (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) _)).trans (hTk_eq ▸ hNTk)
  · rw [canonicalSchedule_numNodes_eq h le_rfl, canonicalSchedule_delta_eq h _,
      canonicalSchedule_depth]
    have hcub := numNodes_mul_delta_mul_levelScale_cubed_le (by omega)
      (hT_pos _ le_rfl) (hT_le _ le_rfl)
    have hls_k : levelScale U (redundancyRatio n R) (treeDepth U (redundancyRatio n R))
        (treeDepth U (redundancyRatio n R)) = redundancyRatio n R := by simp [levelScale]
    rw [hls_k] at hcub
    exact (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide) _)).trans hcub

private theorem single_nonLeaf_tableMeta_of_schedule (P : TreeSchedule) {n r s ℓ : ℕ}
    (h1 : 1 ≤ ℓ) (hlt : ℓ < P.depth)
    (hs_ge_r : r ≤ s)
    (hy_ge : 256 ^ 9 ≤ P.nFloor ℓ)
    (hid_def : P.idBits ℓ = 4 * Nat.clog 2 (2 * max (P.nFloor ℓ) 1))
    (hid_le : P.idBits ℓ + 2 ≤ 150 * s)
    (hNtc : P.numNodes ℓ * P.tableCap ℓ ≤ 3 * P.numNodes (ℓ + 1) * P.delta (ℓ + 1))
    (hd_pos : 1 ≤ P.delta (ℓ + 1))
    (hcub : P.numNodes (ℓ + 1) * P.delta (ℓ + 1) * s ^ 3 ≤ n) :
    P.numNodes ℓ *
        (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
          P.tableCap ℓ *
            (Nat.clog 2 (2 * (P.nFloor ℓ + 1)) + Nat.clog 2 (P.tableCap ℓ + 1))) *
      r ^ 2 ≤ 36000 * n := by
  have htc_nh : P.tableCap ℓ ≤ P.nFloor ℓ + P.delta ℓ := by
    rcases eq_or_lt_of_le h1 with rfl | hgt1
    · dsimp only [TreeSchedule.tableCap, TreeSchedule.nHigh]
      rw [ite_eq_left rfl, ite_eq_right one_ne_zero]
      exact Nat.sub_le _ _
    · dsimp only [TreeSchedule.tableCap, TreeSchedule.nLow]
      rw [ite_eq_right (by omega), ite_eq_left hlt, ite_eq_right (by omega)]
      exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (Nat.le_add_right _ _))
  have hnh_id : P.nFloor ℓ + P.delta ℓ ≤ 2 ^ P.idBits ℓ :=
    P.nHigh_le_two_pow_idBits ℓ h1 hlt.le
  have htc_id : P.tableCap ℓ ≤ 2 ^ P.idBits ℓ := htc_nh.trans hnh_id
  have hmeta := succinctTableMetaBits_le htc_id
  have hcl_nf : Nat.clog 2 (2 * (P.nFloor ℓ + 1)) ≤ P.idBits ℓ := by
    set y := P.nFloor ℓ
    have hy2 : 2 ≤ y := (by decide : 2 ≤ 256 ^ 9).trans hy_ge
    set c := Nat.clog 2 (2 * max y 1)
    have h2y_c : 2 * y ≤ 2 ^ c := by
      have hc_le : 2 * max y 1 ≤ 2 ^ c := Nat.le_pow_clog Nat.one_lt_two (2 * max y 1)
      rwa [max_eq_left (by omega : 1 ≤ y)] at hc_le
    refine Nat.clog_le_of_le_pow ?_
    rw [hid_def]
    calc 2 * (y + 1) ≤ (2 * y) ^ 2 := by nlinarith
      _ ≤ (2 ^ c) ^ 2 := Nat.pow_le_pow_left h2y_c 2
      _ = 2 ^ (2 * c) := by rw [← Nat.pow_mul, Nat.mul_comm]
      _ ≤ 2 ^ (4 * c) := Nat.pow_le_pow_right Nat.two_pos (by omega)
  have hcl_tc : Nat.clog 2 (P.tableCap ℓ + 1) ≤ P.idBits ℓ + 1 := by
    refine Nat.clog_le_of_le_pow ?_
    calc P.tableCap ℓ + 1 ≤ 2 ^ P.idBits ℓ + 2 ^ P.idBits ℓ :=
          Nat.add_le_add htc_id (Nat.two_pow_pos _)
      _ = 2 ^ (P.idBits ℓ + 1) := by rw [← two_mul, pow_succ']
  have hinner_sum : succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
      P.tableCap ℓ * (Nat.clog 2 (2 * (P.nFloor ℓ + 1)) + Nat.clog 2 (P.tableCap ℓ + 1)) ≤
      (77 * P.tableCap ℓ + 9) * (P.idBits ℓ + 2) := by
    have hsum_cl : Nat.clog 2 (2 * (P.nFloor ℓ + 1)) + Nat.clog 2 (P.tableCap ℓ + 1) ≤
        2 * P.idBits ℓ + 1 := by omega
    have hprod := Nat.mul_le_mul_left (P.tableCap ℓ) hsum_cl
    nlinarith
  have hN_le_Nd : P.numNodes ℓ ≤ P.numNodes (ℓ + 1) * P.delta (ℓ + 1) := by
    calc P.numNodes ℓ ≤ P.numNodes ℓ * P.branchFactor ℓ :=
          Nat.le_mul_of_pos_right _ (P.branchFactor_pos ℓ)
      _ = P.numNodes (ℓ + 1) := (P.numNodes_succ ℓ).symm
      _ ≤ P.numNodes (ℓ + 1) * P.delta (ℓ + 1) := Nat.le_mul_of_pos_right _ hd_pos
  have hN77 : P.numNodes ℓ * (77 * P.tableCap ℓ + 9) ≤
      240 * (P.numNodes (ℓ + 1) * P.delta (ℓ + 1)) := by nlinarith
  have hsr2 : s * r ^ 2 ≤ s ^ 3 := by
    calc s * r ^ 2 ≤ s * s ^ 2 := Nat.mul_le_mul_left s (Nat.pow_le_pow_left hs_ge_r 2)
      _ = s ^ 3 := (pow_succ' s 2).symm
  calc P.numNodes ℓ *
        (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
          P.tableCap ℓ *
            (Nat.clog 2 (2 * (P.nFloor ℓ + 1)) + Nat.clog 2 (P.tableCap ℓ + 1))) * r ^ 2
      ≤ P.numNodes ℓ * ((77 * P.tableCap ℓ + 9) * (P.idBits ℓ + 2)) * r ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hinner_sum)
    _ = (P.numNodes ℓ * (77 * P.tableCap ℓ + 9)) * (P.idBits ℓ + 2) * r ^ 2 := by ring
    _ ≤ (240 * (P.numNodes (ℓ + 1) * P.delta (ℓ + 1))) * (150 * s) * r ^ 2 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hN77 hid_le)
    _ = 36000 * ((P.numNodes (ℓ + 1) * P.delta (ℓ + 1)) * (s * r ^ 2)) := by ring
    _ ≤ 36000 * ((P.numNodes (ℓ + 1) * P.delta (ℓ + 1)) * s ^ 3) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hsr2)
    _ ≤ 36000 * n := Nat.mul_le_mul_left 36000 hcub

private theorem nonLeaf_tables_of_schedule (P : TreeSchedule) {n r : ℕ}
    (hr1 : 1 ≤ r) (hk_le_r : P.depth ≤ r)
    (hsingle : ∀ ℓ, 1 ≤ ℓ → ℓ < P.depth →
      P.numNodes ℓ *
        (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
          P.tableCap ℓ *
            (Nat.clog 2 (2 * (P.nFloor ℓ + 1)) + Nat.clog 2 (P.tableCap ℓ + 1))) *
        r ^ 2 ≤ 36000 * n) :
    ((∑ ℓ ∈ Finset.Ico 2 P.depth,
        P.numNodes ℓ *
          (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
            P.tableCap ℓ * Nat.clog 2 (2 * (P.nFloor ℓ + 1)))) +
      P.numNodes 1 *
        (succinctTableMetaBits (P.idBits 1) (P.tableCap 1) +
          P.tableCap 1 *
            (Nat.clog 2 (2 * (P.nFloor 1 + 1)) + Nat.clog 2 (P.tableCap 1 + 1)))) *
      r ≤ 72000 * n := by
  have hsum_r2 : (∑ ℓ ∈ Finset.Ico 2 P.depth,
      P.numNodes ℓ *
        (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
          P.tableCap ℓ * Nat.clog 2 (2 * (P.nFloor ℓ + 1)))) * r ^ 2 ≤ r * (36000 * n) := by
    rw [Finset.sum_mul]
    calc ∑ ℓ ∈ Finset.Ico 2 P.depth,
          P.numNodes ℓ *
            (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
              P.tableCap ℓ * Nat.clog 2 (2 * (P.nFloor ℓ + 1))) * r ^ 2
        ≤ ∑ _ℓ ∈ Finset.Ico 2 P.depth, 36000 * n := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          obtain ⟨h2, hlt⟩ := Finset.mem_Ico.mp hℓ
          refine (Nat.mul_le_mul_right (r ^ 2) (Nat.mul_le_mul_left (P.numNodes ℓ) ?_)).trans
            (hsingle ℓ (by omega) hlt)
          exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)) _
      _ = (Finset.Ico 2 P.depth).card * (36000 * n) := by simp
      _ ≤ r * (36000 * n) := by
          refine Nat.mul_le_mul_right _ ?_
          rw [Nat.card_Ico]
          omega
  have hsum_r : (∑ ℓ ∈ Finset.Ico 2 P.depth,
      P.numNodes ℓ *
        (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
          P.tableCap ℓ * Nat.clog 2 (2 * (P.nFloor ℓ + 1)))) * r ≤ 36000 * n := by
    refine Nat.le_of_mul_le_mul_right ?_ hr1
    calc _ * r * r = _ * r ^ 2 := by ring
      _ ≤ 36000 * n * r := by linarith
  have hroot_r : P.numNodes 1 *
      (succinctTableMetaBits (P.idBits 1) (P.tableCap 1) +
        P.tableCap 1 *
          (Nat.clog 2 (2 * (P.nFloor 1 + 1)) + Nat.clog 2 (P.tableCap 1 + 1))) * r ≤
      36000 * n := by
    have h1 := hsingle 1 le_rfl (by have := P.two_le_depth; omega)
    have hr_r2 : r ≤ r ^ 2 := Nat.le_self_pow (by decide) r
    exact (Nat.mul_le_mul_left _ hr_r2).trans h1
  nlinarith

theorem nonLeaf_tables_slack_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    ((∑ ℓ ∈ Finset.Ico 2 (canonicalSchedule h).depth,
        (canonicalSchedule h).numNodes ℓ *
          (succinctTableMetaBits ((canonicalSchedule h).idBits ℓ)
              ((canonicalSchedule h).tableCap ℓ) +
            (canonicalSchedule h).tableCap ℓ *
              Nat.clog 2 (2 * ((canonicalSchedule h).nFloor ℓ + 1)))) +
      (canonicalSchedule h).numNodes 1 *
        (succinctTableMetaBits ((canonicalSchedule h).idBits 1)
            ((canonicalSchedule h).tableCap 1) +
          (canonicalSchedule h).tableCap 1 *
            (Nat.clog 2 (2 * ((canonicalSchedule h).nFloor 1 + 1)) +
              Nat.clog 2 ((canonicalSchedule h).tableCap 1 + 1)))) *
      redundancyRatio n R ≤ 72000 * n := by
  have hr256 := h.redundancyRatio_bounds.1
  have hr1 : 1 ≤ redundancyRatio n R := by dsimp [minRedundancyRatio] at hr256; omega
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  refine nonLeaf_tables_of_schedule (canonicalSchedule h) hr1 h.treeDepth_le_redundancyRatio
    fun ℓ h1 hlt => ?_
  have hlt_k : ℓ < treeDepth U (redundancyRatio n R) := hlt
  have hs_ge_r := r_le_levelScale (ℓ := ℓ + 1) (by omega) h.four_mul_redundancyRatio_le_log_univ
  refine single_nonLeaf_tableMeta_of_schedule (canonicalSchedule h) h1 hlt hs_ge_r
    (nFloor_ge_pow_256 h hlt.le) (by rw [canonicalSchedule_idBits_eq h ℓ,
      canonicalSchedule_nFloor_eq h ℓ]; rfl) ?_
    (numNodes_mul_tableCap_le h h1 hlt) (delta_pos_of_le_depth h hlt) ?_
  · have hpred := idBits_pred_le_mul_levelScale hr256 (by omega : 2 ≤ ℓ + 1) hlt_k
      (hT_pos ℓ hlt_k.le) (hT_le ℓ hlt_k.le)
    rw [canonicalSchedule_idBits_eq h ℓ]
    change idBits n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ((ℓ + 1) - 1) ≤ _
      at hpred
    rw [Nat.add_sub_cancel] at hpred
    have hs256 : 256 ≤ levelScale U (redundancyRatio n R) (treeDepth U (redundancyRatio n R))
        (ℓ + 1) := by dsimp [minRedundancyRatio] at hr256; omega
    omega
  · rw [canonicalSchedule_numNodes_eq h hlt, canonicalSchedule_delta_eq h (ℓ + 1)]
    exact numNodes_mul_delta_mul_levelScale_cubed_le (by omega) (hT_pos (ℓ + 1) hlt_k)
      (hT_le (ℓ + 1) hlt_k)

private theorem rootExtra_and_poolDir_of_schedule (P : TreeSchedule) {n r L s1 p_max : ℕ}
    (hn2 : 2 ≤ n) (hL_eq : L = Nat.log 2 n)
    (h10_L : 10 ≤ L) (hpL : 2 * (p_max + 2) + 1 ≤ L) (hL_s1 : L ≤ s1) (hr_le_L : r ≤ L)
    (hcap : P.cap = n)
    (hpad_pow : P.paddedUniv ≤ 2 ^ (2 * (p_max + 2) * L))
    (hN1_nf : P.numNodes 1 * P.nFloor 1 ≤ n)
    (hcub1 : P.numNodes 1 * P.delta 1 * s1 ^ 3 ≤ n)
    (hNtc1 : P.numNodes 1 * P.tableCap 1 ≤ 3 * P.numNodes 2 * P.delta 2)
    (hN2d2 : P.numNodes 2 * P.delta 2 ≤ n)
    (hN1_L9 : P.numNodes 1 * L ^ 9 ≤ n) :
    ((P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap) *
        Nat.clog 2 ((P.paddedUniv + P.cap - 1) / P.cap) +
      P.rootPoolDirBits) * r ≤ 8 * n := by
  have hr_le_s1 : r ≤ s1 := hr_le_L.trans hL_s1
  have hextra_le : P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap ≤
      P.numNodes 1 * P.delta 1 := by
    have hN2_nl : P.numNodes 2 * P.nLow 2 ≤ n := hcap ▸ P.numNodes_two_mul_nLow_two_le_cap
    have hrc : P.branchFactor 1 * P.nLow 2 ≤ P.nFloor 1 + P.delta 1 := P.root_cap_le
    have hN_rc : P.numNodes 2 * P.nLow 2 ≤ P.numNodes 1 * (P.nFloor 1 + P.delta 1) := by
      calc P.numNodes 2 * P.nLow 2
          = P.numNodes 1 * (P.branchFactor 1 * P.nLow 2) := by
            rw [show (2 : ℕ) = 1 + 1 from rfl, P.numNodes_succ 1, Nat.mul_assoc]
        _ ≤ P.numNodes 1 * (P.nFloor 1 + P.delta 1) := Nat.mul_le_mul_left _ hrc
    have htc1 : P.numNodes 1 * P.tableCap 1 =
        P.numNodes 1 * (P.nFloor 1 + P.delta 1) - P.numNodes 2 * P.nLow 2 := by
      dsimp only [TreeSchedule.tableCap, TreeSchedule.nHigh]
      rw [ite_eq_left rfl, ite_eq_right one_ne_zero, Nat.mul_sub_left_distrib, ← Nat.mul_assoc,
        ← P.numNodes_succ 1]
    dsimp only [TreeSchedule.rootValPoolCap]
    rw [hcap, htc1, Nat.mul_add]
    rw [Nat.mul_add] at hN_rc
    omega
  have hq_le : Nat.clog 2 ((P.paddedUniv + P.cap - 1) / P.cap) ≤ s1 ^ 2 := by
    have hdiv_le : (P.paddedUniv + P.cap - 1) / P.cap ≤ 2 * P.paddedUniv := by
      rw [hcap]
      have hpad_n : n ≤ P.paddedUniv := by
        have hp := P.univ_le_padded
        dsimp only [TreeSchedule.paddedUniv, TreeSchedule.branchFactor]
        omega
      calc (P.paddedUniv + n - 1) / n ≤ P.paddedUniv + n - 1 := Nat.div_le_self _ _
        _ ≤ 2 * P.paddedUniv := by omega
    have h2p : 2 * (p_max + 2) * L + 1 ≤ s1 ^ 2 := by
      calc 2 * (p_max + 2) * L + 1 ≤ (2 * (p_max + 2) + 1) * L := by nlinarith
        _ ≤ L * L := Nat.mul_le_mul_right L hpL
        _ = L ^ 2 := (sq L).symm
        _ ≤ s1 ^ 2 := Nat.pow_le_pow_left hL_s1 2
    refine Nat.clog_le_of_le_pow (hdiv_le.trans ?_)
    calc 2 * P.paddedUniv ≤ 2 * 2 ^ (2 * (p_max + 2) * L) :=
          Nat.mul_le_mul_left 2 hpad_pow
      _ = 2 ^ (2 * (p_max + 2) * L + 1) := (pow_succ' 2 _).symm
      _ ≤ 2 ^ (s1 ^ 2) := Nat.pow_le_pow_right Nat.two_pos h2p
  have hextra_r : (P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap) *
      Nat.clog 2 ((P.paddedUniv + P.cap - 1) / P.cap) * r ≤ n := by
    calc (P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap) *
          Nat.clog 2 ((P.paddedUniv + P.cap - 1) / P.cap) * r
        ≤ (P.numNodes 1 * P.delta 1) * (s1 ^ 2) * s1 :=
          Nat.mul_le_mul (Nat.mul_le_mul hextra_le hq_le) hr_le_s1
      _ = P.numNodes 1 * P.delta 1 * s1 ^ 3 := by ring
      _ ≤ n := hcub1
  set ptrBits := Nat.clog 2 (P.cap + 2)
  have hptr_bounds : L ≤ ptrBits ∧ ptrBits ≤ 2 * L := by
    refine ⟨?_, ?_⟩
    · by_contra hlt
      have hpow_le : 2 ^ ptrBits ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right Nat.two_pos (by omega)
      have hlt_L : 2 ^ (L - 1) < 2 ^ L := Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
      have hn_ge : 2 ^ L ≤ n := hL_eq ▸ Nat.pow_log_le_self 2 (by omega)
      have hcl : P.cap + 2 ≤ 2 ^ ptrBits := Nat.le_pow_clog Nat.one_lt_two (P.cap + 2)
      omega
    · refine Nat.clog_le_of_le_pow ?_
      have hn_lt : n < 2 ^ (L + 1) := hL_eq ▸ Nat.lt_pow_succ_log_self Nat.one_lt_two n
      calc P.cap + 2 ≤ 2 * 2 ^ (L + 1) := by omega
        _ = 2 ^ (L + 2) := (pow_succ' 2 _).symm
        _ ≤ 2 ^ (2 * L) := Nat.pow_le_pow_right Nat.two_pos (by omega)
  set K := max P.rootSlabSize 1
  have hK_eq : K = ptrBits ^ 2 := by
    dsimp only [K, TreeSchedule.rootSlabSize]
    exact max_eq_left (Nat.one_le_pow 2 ptrBits (by omega))
  have hpr_le_K : ptrBits * r ≤ K := by
    rw [hK_eq, sq]
    exact Nat.mul_le_mul_left ptrBits (hr_le_L.trans hptr_bounds.1)
  have hdiv_tc : P.numNodes 1 * (P.tableCap 1 / K) * (ptrBits * r) ≤ 3 * n := by
    have h1 : (P.tableCap 1 / K) * (ptrBits * r) ≤ P.tableCap 1 :=
      (Nat.mul_le_mul_left _ hpr_le_K).trans (Nat.div_mul_le_self _ K)
    calc P.numNodes 1 * (P.tableCap 1 / K) * (ptrBits * r)
        = P.numNodes 1 * ((P.tableCap 1 / K) * (ptrBits * r)) := by ring
      _ ≤ P.numNodes 1 * P.tableCap 1 := Nat.mul_le_mul_left _ h1
      _ ≤ 3 * P.numNodes 2 * P.delta 2 := hNtc1
      _ = 3 * (P.numNodes 2 * P.delta 2) := by ring
      _ ≤ 3 * n := Nat.mul_le_mul_left 3 hN2d2
  have hdiv_pool : (P.rootValPoolCap / K) * (ptrBits * r) ≤ n :=
    ((Nat.mul_le_mul_left _ hpr_le_K).trans (Nat.div_mul_le_self _ K)).trans
      (by dsimp only [TreeSchedule.rootValPoolCap]; omega)
  have hrem_dir : (P.numNodes 1 * (1 + K) + 4) * (ptrBits * r) ≤ 3 * n := by
    have h1K : 1 + K ≤ 5 * L ^ 2 := by
      rw [hK_eq]
      have hsq : ptrBits ^ 2 ≤ 4 * L ^ 2 := by
        calc ptrBits ^ 2 ≤ (2 * L) ^ 2 := Nat.pow_le_pow_left hptr_bounds.2 2
          _ = 4 * L ^ 2 := by ring
      have hL2 : 1 ≤ L ^ 2 := Nat.one_le_pow 2 L (by omega)
      omega
    have hpr_L2 : ptrBits * r ≤ 2 * L ^ 2 := by
      calc ptrBits * r ≤ (2 * L) * L := Nat.mul_le_mul hptr_bounds.2 hr_le_L
        _ = 2 * L ^ 2 := by ring
    have h10L4 : 10 * L ^ 4 ≤ L ^ 9 := by
      have h10 : 10 ≤ L ^ 5 := h10_L.trans (Nat.le_self_pow (by decide) L)
      calc 10 * L ^ 4 ≤ L ^ 5 * L ^ 4 := Nat.mul_le_mul_right _ h10
        _ = L ^ 9 := (Nat.pow_add L 5 4).symm
    have h8L2 : 8 * L ^ 2 ≤ n := by
      calc 8 * L ^ 2 ≤ 10 * L ^ 4 := by
            have : 1 ≤ L ^ 2 := Nat.one_le_pow 2 L (by omega)
            nlinarith
        _ ≤ L ^ 9 := h10L4
        _ ≤ P.numNodes 1 * L ^ 9 := Nat.le_mul_of_pos_left _ (P.numNodes_pos 1)
        _ ≤ n := hN1_L9
    calc (P.numNodes 1 * (1 + K) + 4) * (ptrBits * r)
        ≤ (P.numNodes 1 * (5 * L ^ 2) + 4) * (2 * L ^ 2) :=
          Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left _ h1K) 4) hpr_L2
      _ = P.numNodes 1 * (10 * L ^ 4) + 8 * L ^ 2 := by ring
      _ ≤ P.numNodes 1 * L ^ 9 + n := Nat.add_le_add (Nat.mul_le_mul_left _ h10L4) h8L2
      _ ≤ 3 * n := by linarith
  have hdir_r : P.rootPoolDirBits * r ≤ 7 * n := by
    have heq : P.rootPoolDirBits * r =
        P.numNodes 1 * (P.tableCap 1 / K) * (ptrBits * r) +
          (P.rootValPoolCap / K) * (ptrBits * r) +
          (P.numNodes 1 * (1 + K) + 4) * (ptrBits * r) := by
      dsimp only [TreeSchedule.rootPoolDirBits]
      change ((P.numNodes 1 * (P.tableCap 1 / K + 1 + K) + P.rootValPoolCap / K + 4) * ptrBits) *
        r = _
      ring
    rw [heq]
    linarith
  nlinarith

theorem rootExtra_and_poolDir_slack_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (((canonicalSchedule h).numNodes 1 * (canonicalSchedule h).tableCap 1 -
        (canonicalSchedule h).rootValPoolCap) *
      Nat.clog 2 (((canonicalSchedule h).paddedUniv + (canonicalSchedule h).cap - 1) /
        (canonicalSchedule h).cap) +
      (canonicalSchedule h).rootPoolDirBits) * redundancyRatio n R ≤ 8 * n := by
  obtain ⟨hr256, _, hr10⟩ := h.redundancyRatio_bounds
  obtain ⟨hL_s1, _⟩ := h.log_univ_bounds
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  have h1_lt : 1 < treeDepth U (redundancyRatio n R) := by
    have := two_le_treeDepth U (redundancyRatio n R); omega
  have hr_le_L : redundancyRatio n R ≤ Nat.log 2 n :=
    (Nat.le_self_pow (by decide : 10 ≠ 0) _).trans hr10
  have hpoly : 2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ Nat.log 2 n :=
    (poly_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
  have hbase_p : max q_min 1 + p_max + 4 ≤ (max q_min 1 + p_max + 4) ^ 4 :=
    Nat.le_self_pow (by decide) _
  refine rootExtra_and_poolDir_of_schedule (canonicalSchedule h) h.two_le_n rfl (by omega)
    (by omega) hL_s1 hr_le_L rfl (paddedUniv_le_two_pow_mul_log h) ?_ ?_
    (numNodes_mul_tableCap_le h le_rfl h1_lt) ?_ ?_
  · rw [canonicalSchedule_nFloor_div_eq h h1_lt.le]
    exact Nat.mul_div_le n _
  · rw [canonicalSchedule_numNodes_eq h h1_lt.le, canonicalSchedule_delta_eq h 1]
    have hc := numNodes_mul_delta_mul_levelScale_cubed_le le_rfl (hT_pos 1 h1_lt.le)
      (hT_le 1 h1_lt.le)
    have hls1 : levelScale U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) 1 =
        Nat.log 2 U := by
      dsimp only [levelScale]; rw [ite_eq_left h1_lt]; rfl
    rwa [hls1] at hc
  · rw [canonicalSchedule_numNodes_eq h h1_lt, canonicalSchedule_delta_eq h 2]
    have hc := numNodes_mul_delta_mul_levelScale_cubed_le (by decide : 1 ≤ 2)
      (hT_pos 2 h1_lt) (hT_le 2 h1_lt)
    have hs2_pos : 1 ≤ (levelScale U (redundancyRatio n R)
        (treeDepth U (redundancyRatio n R)) 2) ^ 3 := by
      refine Nat.one_le_pow 3 _ ?_
      have := r_le_levelScale (ℓ := 2) (by decide) h.four_mul_redundancyRatio_le_log_univ
      dsimp [minRedundancyRatio] at hr256
      omega
    exact (Nat.le_mul_of_pos_right _ hs2_pos).trans hc
  · rw [canonicalSchedule_numNodes_eq h h1_lt.le]
    obtain ⟨hNT1, _⟩ := numNodes_mul_targetSize_bounds (hT_pos 1 h1_lt.le) (hT_le 1 h1_lt.le)
    have hT1_eq : targetSize n U (redundancyRatio n R)
        (treeDepth U (redundancyRatio n R)) 1 = (Nat.log 2 U) ^ 9 := by
      rw [targetSize_eq_levelScale_pow le_rfl]
      dsimp only [levelScale]; rw [ite_eq_left h1_lt]; rfl
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL_s1 9)).trans (hT1_eq ▸ hNT1)

private theorem waitingLists_and_hashSeeds_of_schedule (P : TreeSchedule) {n U r s1 : ℕ}
    (hr256 : 256 ≤ r) (hr2_n : r ^ 2 ≤ n) (hr_s1 : r ≤ s1) (hs1_eq : s1 = Nat.log 2 U)
    (h4r : 4 * r ≤ Nat.log 2 U)
    (hdepth_eq : P.depth = treeDepth U r) (hcap_eq : P.cap = n) (hk_le_r : P.depth ≤ r)
    (hpad_s1 : P.paddedUniv ≤ 2 ^ (s1 ^ 2))
    (hsq_all : ∀ ℓ < P.depth, (P.routerSeedBits ℓ) ^ 2 ≤ P.nFloor ℓ)
    (hd_pos_all : ∀ j ≤ P.depth, 1 ≤ P.delta j)
    (hhd_all : ∀ j ≤ P.depth, 2 * P.delta j ≤ P.nFloor j)
    (hid_pred_all : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ P.depth → P.idBits (ℓ - 1) ≤ 148 * levelScale U r P.depth ℓ)
    (hcub_all : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.depth →
      P.numNodes ℓ * P.delta ℓ * (levelScale U r P.depth ℓ) ^ 3 ≤ n)
    (hNT_all : ∀ ℓ, 1 ≤ ℓ → ℓ ≤ P.depth →
      P.numNodes ℓ * (levelScale U r P.depth ℓ) ^ 9 ≤ n ∧
        (levelScale U r P.depth ℓ) ^ 9 ≤ P.nFloor ℓ ∧
        P.numNodes ℓ * P.nFloor ℓ ≤ n) :
    (P.allWaitingListsBits + P.allHashSeedsBits) * r ≤ 1700 * n := by
  have hr1 : 1 ≤ r := by omega
  have hwait_r2 : (∑ ℓ ∈ Finset.Icc 2 P.depth,
      P.numNodes ℓ * waitingListBits (P.waitCap ℓ) (P.idBits ℓ) (P.idBits (ℓ - 1))) * r ^ 2 ≤
      r * (740 * n) := by
    rw [Finset.sum_mul]
    calc ∑ ℓ ∈ Finset.Icc 2 P.depth,
          P.numNodes ℓ * waitingListBits (P.waitCap ℓ) (P.idBits ℓ) (P.idBits (ℓ - 1)) * r ^ 2
        ≤ ∑ _ℓ ∈ Finset.Icc 2 P.depth, 740 * n := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          obtain ⟨h2, hle⟩ := Finset.mem_Icc.mp hℓ
          have hd_pos : 1 ≤ P.delta ℓ := hd_pos_all ℓ hle
          have hhd := hhd_all ℓ hle
          have hnh_id := P.nHigh_le_two_pow_idBits ℓ (by omega) hle
          have hcl_w : Nat.clog 2 (P.waitCap ℓ + 1) ≤ P.idBits ℓ := by
            refine Nat.clog_le_of_le_pow ?_
            dsimp only [TreeSchedule.waitCap]
            omega
          have hid_mono : P.idBits ℓ ≤ P.idBits (ℓ - 1) := by
            have hstep := P.idBits_step_le (ℓ - 1) (by omega) (by omega)
            rw [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] at hstep
            omega
          set s := levelScale U r P.depth ℓ
          have hid_pred : P.idBits (ℓ - 1) ≤ 148 * s := hid_pred_all ℓ h2 hle
          have hw_le : waitingListBits (P.waitCap ℓ) (P.idBits ℓ) (P.idBits (ℓ - 1)) ≤
              740 * P.delta ℓ * s := by
            dsimp only [waitingListBits, TreeSchedule.waitCap]
            have h1 : Nat.clog 2 (2 * P.delta ℓ + 1) +
                2 * P.delta ℓ * (P.idBits ℓ + P.idBits (ℓ - 1)) ≤
                5 * P.delta ℓ * P.idBits (ℓ - 1) := by
              have hcl2 : Nat.clog 2 (2 * P.delta ℓ + 1) ≤ P.delta ℓ * P.idBits (ℓ - 1) :=
                (hcl_w.trans hid_mono).trans (Nat.le_mul_of_pos_left _ hd_pos)
              nlinarith
            calc _ ≤ 5 * P.delta ℓ * P.idBits (ℓ - 1) := h1
              _ ≤ 5 * P.delta ℓ * (148 * s) := Nat.mul_le_mul_left _ hid_pred
              _ = 740 * P.delta ℓ * s := by ring
          have hs_r : r ≤ s := by
            dsimp only [s]; rw [hdepth_eq]; exact r_le_levelScale (by omega) h4r
          have hsr2 : s * r ^ 2 ≤ s ^ 3 := by
            calc s * r ^ 2 ≤ s * s ^ 2 := Nat.mul_le_mul_left s (Nat.pow_le_pow_left hs_r 2)
              _ = s ^ 3 := (pow_succ' s 2).symm
          have hcub := hcub_all ℓ (by omega) hle
          calc P.numNodes ℓ * waitingListBits (P.waitCap ℓ) (P.idBits ℓ) (P.idBits (ℓ - 1)) *
                r ^ 2
              ≤ P.numNodes ℓ * (740 * P.delta ℓ * s) * r ^ 2 :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hw_le)
            _ = 740 * (P.numNodes ℓ * P.delta ℓ * (s * r ^ 2)) := by ring
            _ ≤ 740 * (P.numNodes ℓ * P.delta ℓ * s ^ 3) :=
                Nat.mul_le_mul_left 740 (Nat.mul_le_mul_left _ hsr2)
            _ ≤ 740 * n := Nat.mul_le_mul_left 740 hcub
      _ = (Finset.Icc 2 P.depth).card * (740 * n) := by simp
      _ ≤ r * (740 * n) := by
          refine Nat.mul_le_mul_right _ ?_
          rw [Nat.card_Icc]
          omega
  have hwait_r : P.allWaitingListsBits * r ≤ 740 * n := by
    refine Nat.le_of_mul_le_mul_right ?_ hr1
    calc P.allWaitingListsBits * r * r = P.allWaitingListsBits * r ^ 2 := by ring
      _ ≤ 740 * n * r := by dsimp only [TreeSchedule.allWaitingListsBits]; linarith
  have hseed0_r : P.routerSeedBits 0 * r ≤ n := by
    have hsq0 : (P.routerSeedBits 0) ^ 2 ≤ n := by
      have h0 := hsq_all 0 (by have := P.two_le_depth; omega)
      rwa [P.nFloor_zero, hcap_eq] at h0
    rcases le_total (P.routerSeedBits 0) r with hle | hge
    · exact (Nat.mul_le_mul_right r hle).trans ((sq r).symm ▸ hr2_n)
    · exact (Nat.mul_le_mul_left _ hge).trans ((sq (P.routerSeedBits 0)).symm ▸ hsq0)
  have hseed_sum_r2 : (∑ ℓ ∈ Finset.Icc 1 P.depth, P.numNodes ℓ * P.nodeHashSeedBits ℓ) * r ^ 2 ≤
      r * (900 * n) := by
    rw [Finset.sum_mul]
    calc ∑ ℓ ∈ Finset.Icc 1 P.depth, P.numNodes ℓ * P.nodeHashSeedBits ℓ * r ^ 2
        ≤ ∑ _ℓ ∈ Finset.Icc 1 P.depth, 900 * n := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          obtain ⟨h1, hle⟩ := Finset.mem_Icc.mp hℓ
          set s := levelScale U r P.depth ℓ
          have hs_r : r ≤ s := by
            dsimp only [s]; rw [hdepth_eq]; exact r_le_levelScale h1 h4r
          obtain ⟨hNTℓ, hs9_nf, hN_nf⟩ := hNT_all ℓ h1 hle
          have hrouter_part : P.numNodes ℓ *
              (if ℓ < P.depth then P.routerSeedBits ℓ else 0) * r ^ 2 ≤ n := by
            split_ifs with hlt
            · have hsq := hsq_all ℓ hlt
              have hr4_nf : (r ^ 2) ^ 2 ≤ P.nFloor ℓ := by
                calc (r ^ 2) ^ 2 = r ^ 4 := (Nat.pow_mul r 2 2).symm
                  _ ≤ r ^ 9 := Nat.pow_le_pow_right hr1 (by decide)
                  _ ≤ s ^ 9 := Nat.pow_le_pow_left hs_r 9
                  _ ≤ P.nFloor ℓ := hs9_nf
              have hprod : P.routerSeedBits ℓ * r ^ 2 ≤ P.nFloor ℓ := by
                rcases le_total (P.routerSeedBits ℓ) (r ^ 2) with ha | hb
                · exact (Nat.mul_le_mul_right _ ha).trans ((sq (r ^ 2)).symm ▸ hr4_nf)
                · exact (Nat.mul_le_mul_left _ hb).trans ((sq (P.routerSeedBits ℓ)).symm ▸ hsq)
              calc P.numNodes ℓ * P.routerSeedBits ℓ * r ^ 2
                  = P.numNodes ℓ * (P.routerSeedBits ℓ * r ^ 2) := by ring
                _ ≤ P.numNodes ℓ * P.nFloor ℓ := Nat.mul_le_mul_left _ hprod
                _ ≤ n := hN_nf
            · simp
          have hidcomp_part : P.numNodes ℓ *
              FeistelPerm.idCompressorSeedBits (P.idBits ℓ) (P.idCompRightUniv ℓ) * r ^ 2 ≤
              894 * n := by
            have hic := FeistelPerm.idCompressorSeedBits_le (P.idBits ℓ) (P.idCompRightUniv ℓ)
            rcases eq_or_lt_of_le h1 with rfl | hgt1
            · have hs_eq : s = s1 := by
                dsimp only [s, levelScale]
                rw [ite_eq_left (by have := P.two_le_depth; omega)]
                simpa only [Nat.iterLog_succ, Nat.iterLog_zero] using hs1_eq.symm
              have hs1_256 : 256 ≤ s1 := by omega
              have hcl1 : Nat.clog 2 (max (P.idCompRightUniv 1) 2) ≤ s1 ^ 2 := by
                dsimp only [TreeSchedule.idCompRightUniv]
                rw [ite_eq_left le_rfl]
                have hq_pad : P.quotOne ≤ P.paddedUniv := by
                  dsimp only [TreeSchedule.paddedUniv]
                  exact Nat.le_mul_of_pos_left _
                    (Nat.mul_pos (P.branchFactor_pos 0) (Nat.two_pow_pos _))
                refine Nat.clog_le_of_le_pow (max_le (hq_pad.trans hpad_s1) ?_)
                exact (show 2 = 2 ^ 1 by decide) ▸
                  Nat.pow_le_pow_right Nat.two_pos (Nat.one_le_pow 2 s1 (by omega))
              have hid1_s1 : max (P.idBits 1) 1 ≤ s1 ^ 2 := by
                have hid1 := hid_pred_all 2 le_rfl P.two_le_depth
                have hls2_s1 : levelScale U r P.depth 2 ≤ s1 := by
                  dsimp only [levelScale]
                  split_ifs
                  · simpa only [Nat.iterLog_succ, Nat.iterLog_zero, ← hs1_eq] using
                      Nat.log_le_self 2 s1
                  · exact hr_s1
                refine max_le ?_ (Nat.one_le_pow 2 s1 (by omega))
                calc P.idBits 1 ≤ 148 * levelScale U r P.depth 2 := hid1
                  _ ≤ 148 * s1 := Nat.mul_le_mul_left 148 hls2_s1
                  _ ≤ s1 * s1 := Nat.mul_le_mul_right s1 (by omega)
                  _ = s1 ^ 2 := (sq s1).symm
              have hic1 : FeistelPerm.idCompressorSeedBits (P.idBits 1) (P.idCompRightUniv 1) ≤
                  6 * s1 ^ 2 :=
                hic.trans (Nat.mul_le_mul_left 6 (max_le hcl1 hid1_s1))
              have hs1_4 : s1 ^ 2 * r ^ 2 ≤ s1 ^ 9 := by
                calc s1 ^ 2 * r ^ 2 ≤ s1 ^ 2 * s1 ^ 2 :=
                      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr_s1 2)
                  _ = s1 ^ 4 := (Nat.pow_add s1 2 2).symm
                  _ ≤ s1 ^ 9 := Nat.pow_le_pow_right (by omega) (by decide)
              have hNT1 : P.numNodes 1 * s1 ^ 9 ≤ n := hs_eq ▸ hNTℓ
              calc P.numNodes 1 *
                    FeistelPerm.idCompressorSeedBits (P.idBits 1) (P.idCompRightUniv 1) * r ^ 2
                  ≤ P.numNodes 1 * (6 * s1 ^ 2) * r ^ 2 :=
                    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hic1)
                _ = 6 * (P.numNodes 1 * (s1 ^ 2 * r ^ 2)) := by ring
                _ ≤ 6 * (P.numNodes 1 * s1 ^ 9) :=
                    Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left _ hs1_4)
                _ ≤ 6 * n := Nat.mul_le_mul_left 6 hNT1
                _ ≤ 894 * n := by omega
            · have hid_pred : P.idBits (ℓ - 1) ≤ 148 * s := hid_pred_all ℓ hgt1 hle
              have hs_ge256 : 256 ≤ s := by omega
              have hcl_rem : Nat.clog 2 (max (P.idCompRightUniv ℓ) 2) ≤ 149 * s := by
                dsimp only [TreeSchedule.idCompRightUniv]
                rw [ite_eq_right (by omega)]
                refine Nat.clog_le_of_le_pow (max_le ?_ ?_)
                · refine Nat.pow_le_pow_right Nat.two_pos ?_
                  dsimp only [TreeSchedule.remBits]
                  omega
                · exact (show 2 = 2 ^ 1 by decide) ▸ Nat.pow_le_pow_right Nat.two_pos (by omega)
              have hid_s : max (P.idBits ℓ) 1 ≤ 149 * s := by
                have hstep := P.idBits_step_le (ℓ - 1) (by omega) (by omega)
                rw [Nat.sub_add_cancel (by omega : 1 ≤ ℓ)] at hstep
                omega
              have hic_ℓ : FeistelPerm.idCompressorSeedBits (P.idBits ℓ) (P.idCompRightUniv ℓ) ≤
                  894 * s := by
                have := max_le hcl_rem hid_s
                omega
              have hsr9 : s * r ^ 2 ≤ s ^ 9 := by
                calc s * r ^ 2 ≤ s * s ^ 2 := Nat.mul_le_mul_left s (Nat.pow_le_pow_left hs_r 2)
                  _ = s ^ 3 := (pow_succ' s 2).symm
                  _ ≤ s ^ 9 := Nat.pow_le_pow_right (by omega) (by decide)
              calc P.numNodes ℓ *
                    FeistelPerm.idCompressorSeedBits (P.idBits ℓ) (P.idCompRightUniv ℓ) * r ^ 2
                  ≤ P.numNodes ℓ * (894 * s) * r ^ 2 :=
                    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hic_ℓ)
                _ = 894 * (P.numNodes ℓ * (s * r ^ 2)) := by ring
                _ ≤ 894 * (P.numNodes ℓ * s ^ 9) :=
                    Nat.mul_le_mul_left 894 (Nat.mul_le_mul_left _ hsr9)
                _ ≤ 894 * n := Nat.mul_le_mul_left 894 hNTℓ
          have hnhs : P.nodeHashSeedBits ℓ =
              (if ℓ < P.depth then P.routerSeedBits ℓ else 0) +
                FeistelPerm.idCompressorSeedBits (P.idBits ℓ) (P.idCompRightUniv ℓ) := by
            dsimp only [TreeSchedule.nodeHashSeedBits]; rw [ite_eq_right (by omega)]
          rw [hnhs]
          nlinarith
      _ = (Finset.Icc 1 P.depth).card * (900 * n) := by simp
      _ ≤ r * (900 * n) := by
          refine Nat.mul_le_mul_right _ ?_
          rw [Nat.card_Icc]
          omega
  have hseed_sum_r :
      (∑ ℓ ∈ Finset.Icc 1 P.depth, P.numNodes ℓ * P.nodeHashSeedBits ℓ) * r ≤ 900 * n := by
    refine Nat.le_of_mul_le_mul_right ?_ hr1
    calc _ * r * r = _ * r ^ 2 := by ring
      _ ≤ 900 * n * r := by linarith
  dsimp only [TreeSchedule.allHashSeedsBits]
  nlinarith

theorem waitingLists_and_hashSeeds_slack_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    ((canonicalSchedule h).allWaitingListsBits + (canonicalSchedule h).allHashSeedsBits) *
      redundancyRatio n R ≤ 1700 * n := by
  obtain ⟨hr256, _, hr10⟩ := h.redundancyRatio_bounds
  obtain ⟨hL_s1, _⟩ := h.log_univ_bounds
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  have hr1 : 1 ≤ redundancyRatio n R := by dsimp [minRedundancyRatio] at hr256; omega
  have hr_le_L : redundancyRatio n R ≤ Nat.log 2 n :=
    (Nat.le_self_pow (by decide : 10 ≠ 0) _).trans hr10
  have hr2_n : (redundancyRatio n R) ^ 2 ≤ n :=
    ((Nat.pow_le_pow_right hr1 (by decide : 2 ≤ 10)).trans hr10).trans (Nat.log_le_self 2 n)
  have hpoly : 2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ Nat.log 2 n :=
    (poly_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
  have hbase_p : max q_min 1 + p_max + 4 ≤ (max q_min 1 + p_max + 4) ^ 4 :=
    Nat.le_self_pow (by decide) _
  have h2p_s1 : 2 * (p_max + 2) * Nat.log 2 n ≤ (Nat.log 2 U) ^ 2 := by
    have hpL : 2 * (p_max + 2) ≤ Nat.log 2 n := by omega
    exact ((Nat.mul_le_mul_right _ hpL).trans (sq _).symm.le).trans
      (Nat.pow_le_pow_left hL_s1 2)
  refine waitingLists_and_hashSeeds_of_schedule (canonicalSchedule h)
    (by dsimp [minRedundancyRatio] at hr256; exact hr256) hr2_n (hr_le_L.trans hL_s1) rfl
    h.four_mul_redundancyRatio_le_log_univ rfl rfl h.treeDepth_le_redundancyRatio
    ((paddedUniv_le_two_pow_mul_log h).trans (Nat.pow_le_pow_right Nat.two_pos h2p_s1))
    (fun ℓ hlt => routerSeedBits_sq_le_nFloor h hlt)
    (fun j hj => delta_pos_of_le_depth h hj) ?_ ?_ ?_ ?_
  · intro j hj
    have hg := nFloor_ge_pow_256 h hj
    rw [canonicalSchedule_nFloor_eq h j] at hg
    rw [canonicalSchedule_delta_eq h j, canonicalSchedule_nFloor_eq h j]
    exact two_mul_delta_le_nFloor_of_eight_le ((by decide : 8 ≤ 256 ^ 9).trans hg)
  · intro ℓ h2 hle
    have hle_k : ℓ ≤ treeDepth U (redundancyRatio n R) := hle
    rw [canonicalSchedule_idBits_eq h (ℓ - 1), canonicalSchedule_depth]
    exact idBits_pred_le_mul_levelScale hr256 h2 hle_k
      (hT_pos (ℓ - 1) (by omega)) (hT_le (ℓ - 1) (by omega))
  · intro ℓ h1 hle
    have hle_k : ℓ ≤ treeDepth U (redundancyRatio n R) := hle
    rw [canonicalSchedule_numNodes_eq h hle, canonicalSchedule_delta_eq h ℓ,
      canonicalSchedule_depth]
    exact numNodes_mul_delta_mul_levelScale_cubed_le h1 (hT_pos ℓ hle_k) (hT_le ℓ hle_k)
  · intro ℓ h1 hle
    have hle_k : ℓ ≤ treeDepth U (redundancyRatio n R) := hle
    obtain ⟨hNT, _⟩ := numNodes_mul_targetSize_bounds (hT_pos ℓ hle_k) (hT_le ℓ hle_k)
    obtain ⟨hlo, _⟩ := targetSize_le_nFloor_and_lt (hT_pos ℓ hle_k) (hT_le ℓ hle_k)
    rw [targetSize_eq_levelScale_pow h1] at hNT hlo
    rw [canonicalSchedule_numNodes_eq h hle, canonicalSchedule_nFloor_eq h ℓ,
      canonicalSchedule_depth]
    exact ⟨hNT, hlo, Nat.mul_div_le n _⟩

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
