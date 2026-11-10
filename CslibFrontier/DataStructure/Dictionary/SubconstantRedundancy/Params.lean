/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.NodeSlackBounds
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# End-to-End Pure Subconstant-Redundancy Bit-Budget Bound (`infoBits + O(R)`)

This module is the top-level parameter and space-accounting entry point for the Section 5
multi-level dictionary tree of [LiLiangYuZhou2024] (`arXiv:2310.20536v1`, Sections 5.1–5.2 and
5.4–5.6, PDF pp. 25–36 / printed pp. 24–35), publicly re-exporting `Schedule`, `BitBudget`,
`Canonical`, `SeedBounds`, and `NodeSlackBounds` and proving the headline pure space theorem
`totalTreeBits_le_infoBits_add`:

```text
(canonicalSchedule h).totalTreeBits ≤ infoBits U V n + spaceConst * R
```

for an explicit universal constant `spaceConst` across all
`ValidRegime U V n R p_min q_min p_max q_max` (with zero upper bound on the value universe `V`).

## Main definitions

* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.spaceConst`: explicit universal constant
  `O(1)` in `infoBits U V n + spaceConst * R`.

## Main results

* `redundancySlack_le_mul_effRedundancy`: all `V`-independent redundancy slack terms sum to at most
  `150000 * effRedundancy n R`.
* `totalTreeBits_le_infoBits_add`: total pure tree representation bits are at most
  `infoBits U V n + spaceConst * R`.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Finset

private theorem descFactorial_le_pow_self (m : ℕ) : ∀ j : ℕ, m.descFactorial j ≤ m ^ j
  | 0 => le_rfl
  | j + 1 => by
    rw [Nat.descFactorial_succ, pow_succ']
    exact Nat.mul_le_mul (Nat.sub_le m j) (descFactorial_le_pow_self m j)

private theorem choose_le_pow_self (m j : ℕ) : m.choose j ≤ m ^ j := by
  have h := descFactorial_le_pow_self m j
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  exact (Nat.le_mul_of_pos_left _ (Nat.factorial_pos j)).trans h

private theorem add_one_le_two_pow : ∀ d : ℕ, d + 1 ≤ 2 ^ d
  | 0 => le_rfl
  | d + 1 => by
    have ih := add_one_le_two_pow d
    rw [pow_succ']
    omega

private theorem leafAndClmul_of_schedule (P : TreeSchedule) {n r L t : ℕ}
    (hn2 : 2 ≤ n) (hL_eq : L = Nat.log 2 n) (h2M : 2560000 ≤ L)
    (ht_eq : t = Nat.log 2 L) (ht_ge : 300 ≤ t) (hr10 : r ^ 10 ≤ L)
    (hcap : P.cap = n)
    (hnf_k_le : P.nFloor P.depth ≤ 2 * r ^ 9)
    (hid_k_def : P.idBits P.depth = 4 * Nat.clog 2 (2 * max (P.nFloor P.depth) 1))
    (hpad_L2 : P.paddedUniv ≤ 2 ^ (L ^ 2)) :
    let U_leaf := 2 ^ P.idBits P.depth
    let n_leaf := P.nLow P.depth
    let matchBits := U_leaf * (U_leaf + n_leaf) * Nat.clog 2 (U_leaf + n_leaf + 1)
    let minimapTabBits := U_leaf *
        Minimap.headerUniv U_leaf n_leaf (P.quotUniv P.depth * P.valBound) n_leaf *
        Nat.clog 2 (2 * n_leaf ^ 2 + 2)
    let clmulBits := 2 ^ (2 * (Nat.log 2 (max P.cap 2) / 3)) *
        (6 * Nat.clog 2 (max P.paddedUniv 2) + 6)
    (matchBits + minimapTabBits + clmulBits) * r ≤ 3 * n := by
  intro U_leaf n_leaf matchBits minimapTabBits clmulBits
  have ht_pow : 2 ^ t ≤ L := ht_eq ▸ Nat.pow_log_le_self 2 (by omega)
  have hr_le_L : r ≤ L := (Nat.le_self_pow (by decide : 10 ≠ 0) r).trans hr10
  have hn_2L : 2 ^ L ≤ n := hL_eq ▸ Nat.pow_log_le_self 2 (by omega)
  set s := t / 10
  have hs_ge : 30 ≤ s := by omega
  have hr_2s : r ≤ 2 ^ (s + 1) := by
    have hL_lt : L < 2 ^ (t + 1) := ht_eq ▸ Nat.lt_pow_succ_log_self Nat.one_lt_two L
    have ht_10 : t + 1 ≤ 10 * (s + 1) := by omega
    have hpow10 : r ^ 10 ≤ (2 ^ (s + 1)) ^ 10 := by
      calc r ^ 10 ≤ L := hr10
        _ ≤ 2 ^ (t + 1) := hL_lt.le
        _ ≤ 2 ^ (10 * (s + 1)) := Nat.pow_le_pow_right Nat.two_pos ht_10
        _ = (2 ^ (s + 1)) ^ 10 := by rw [Nat.mul_comm 10, Nat.pow_mul]
    exact (Nat.pow_le_pow_iff_left (by decide : 10 ≠ 0)).mp hpow10
  have hnf_s : P.nFloor P.depth ≤ 2 ^ (9 * s + 10) := by
    calc P.nFloor P.depth ≤ 2 * r ^ 9 := hnf_k_le
      _ ≤ 2 * (2 ^ (s + 1)) ^ 9 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hr_2s 9)
      _ = 2 ^ (9 * s + 10) := by rw [← Nat.pow_mul, ← pow_succ']; congr 1; ring
  have hid_k_le : P.idBits P.depth ≤ 36 * s + 44 := by
    have hcl : Nat.clog 2 (2 * max (P.nFloor P.depth) 1) ≤ 9 * s + 11 := by
      refine Nat.clog_le_of_le_pow ?_
      rw [max_eq_left (P.nFloor_pos P.depth le_rfl)]
      calc 2 * P.nFloor P.depth ≤ 2 * 2 ^ (9 * s + 10) := Nat.mul_le_mul_left 2 hnf_s
        _ = 2 ^ (9 * s + 11) := (pow_succ' 2 _).symm
    rw [hid_k_def]; omega
  have hn_leaf_le : n_leaf ≤ 2 ^ (9 * s + 10) := by
    dsimp only [n_leaf, TreeSchedule.nLow]
    rw [ite_eq_right (by have := P.two_le_depth; omega)]
    exact (Nat.sub_le _ _).trans hnf_s
  have hn_leaf_U : n_leaf ≤ U_leaf := by
    dsimp only [n_leaf, U_leaf, TreeSchedule.nLow]
    rw [ite_eq_right (by have := P.two_le_depth; omega)]
    exact (Nat.sub_le _ _).trans ((Nat.le_add_right _ _).trans
      (P.nHigh_le_two_pow_idBits P.depth (by have := P.two_le_depth; omega) le_rfl))
  have hexp_half : (48 * (s + 1)) * 2 ^ (9 * s + 10) ≤ L / 2 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hs_ge
    have h48 : 48 * (s + 1) ≤ 2 ^ (11 + d) := by
      have hd1 := add_one_le_two_pow d
      have h11 : (2 : ℕ) ^ 11 = 2048 := by norm_num
      calc 48 * (s + 1) = 1488 + 48 * d := by omega
        _ ≤ 2048 * (d + 1) := by omega
        _ ≤ 2 ^ 11 * 2 ^ d := by rw [h11]; exact Nat.mul_le_mul_left _ hd1
        _ = 2 ^ (11 + d) := (Nat.pow_add 2 11 d).symm
    have hpow_sum : 2 ^ (11 + d) * 2 ^ (9 * s + 10) ≤ 2 ^ (t - 1) := by
      rw [← Nat.pow_add]
      exact Nat.pow_le_pow_right Nat.two_pos (by omega)
    have ht_half : 2 ^ (t - 1) ≤ L / 2 := by
      refine (Nat.le_div_iff_mul_le (by decide)).mpr ?_
      calc 2 ^ (t - 1) * 2 = 2 ^ t := by rw [← pow_succ]; congr 1; omega
        _ ≤ L := ht_pow
    exact (Nat.mul_le_mul_right _ h48).trans (hpow_sum.trans ht_half)
  have hL_pow_half : 2 ^ (L / 2) * r ≤ n := by
    have hr_pow : r ≤ 2 ^ (L / 2) := by
      have hsq : (L / 2) ^ 2 ≤ 2 ^ (L / 2) := Nat.sq_le_two_pow (by omega)
      have hL_sq : L ≤ (L / 2) ^ 2 := by
        calc L ≤ 3 * (L / 2) := by omega
          _ ≤ (L / 2) * (L / 2) := Nat.mul_le_mul_right _ (by omega)
          _ = (L / 2) ^ 2 := (sq _).symm
      exact hr_le_L.trans (hL_sq.trans hsq)
    calc 2 ^ (L / 2) * r ≤ 2 ^ (L / 2) * 2 ^ (L / 2) := Nat.mul_le_mul_left _ hr_pow
      _ = 2 ^ (L / 2 + L / 2) := (Nat.pow_add 2 _ _).symm
      _ ≤ 2 ^ L := Nat.pow_le_pow_right Nat.two_pos (by omega)
      _ ≤ n := hn_2L
  have hmatch_le : matchBits ≤ 2 ^ (L / 2) := by
    have hcl : Nat.clog 2 (U_leaf + n_leaf + 1) ≤ P.idBits P.depth + 2 := by
      refine Nat.clog_le_of_le_pow ?_
      have : 1 ≤ U_leaf := Nat.two_pow_pos _
      calc U_leaf + n_leaf + 1 ≤ 4 * U_leaf := by omega
        _ = 2 ^ 2 * 2 ^ P.idBits P.depth := rfl
        _ = 2 ^ (P.idBits P.depth + 2) := by rw [← Nat.pow_add, Nat.add_comm]
    calc matchBits ≤ U_leaf * (2 * U_leaf) * 2 ^ (P.idBits P.depth + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
            (hcl.trans Nat.lt_two_pow_self.le)
      _ = 2 ^ (3 * P.idBits P.depth + 3) := by
          dsimp only [U_leaf]
          calc 2 ^ P.idBits P.depth * (2 * 2 ^ P.idBits P.depth) * 2 ^ (P.idBits P.depth + 2)
              = 2 ^ 1 * 2 ^ P.idBits P.depth * 2 ^ P.idBits P.depth *
                  2 ^ (P.idBits P.depth + 2) := by ring
            _ = 2 ^ (3 * P.idBits P.depth + 3) := by
                rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]; congr 1; ring
      _ ≤ 2 ^ ((48 * (s + 1)) * 2 ^ (9 * s + 10)) := by
          refine Nat.pow_le_pow_right Nat.two_pos ?_
          have h1 : 1 ≤ 2 ^ (9 * s + 10) := Nat.two_pow_pos _
          have h3id : 3 * P.idBits P.depth + 3 ≤ 150 * (s + 1) := by omega
          calc 3 * P.idBits P.depth + 3 ≤ 150 * (s + 1) := h3id
            _ = (s + 1) * 150 := by ring
            _ ≤ (48 * (s + 1)) * 2 ^ (9 * s + 10) := by
                refine Nat.mul_le_mul (by omega) ?_
                exact (by norm_num : 150 ≤ 2 ^ 10).trans
                  (Nat.pow_le_pow_right Nat.two_pos (by omega))
      _ ≤ 2 ^ (L / 2) := Nat.pow_le_pow_right Nat.two_pos hexp_half
  have hminimap_le : minimapTabBits ≤ 2 ^ (L / 2) := by
    have hn1 : 1 ≤ n_leaf := P.nLow_pos le_rfl
    have hqt := Minimap.queryTableSize_le (U' := U_leaf) (n' := n_leaf)
      (X := P.quotUniv P.depth * P.valBound) hn1
    have hch : U_leaf.choose n_leaf ≤ U_leaf ^ n_leaf := choose_le_pow_self U_leaf n_leaf
    have h2n : 2 * n_leaf ≤ 2 ^ (9 * s + 11) := by
      calc 2 * n_leaf ≤ 2 * 2 ^ (9 * s + 10) := Nat.mul_le_mul_left 2 hn_leaf_le
        _ = 2 ^ (9 * s + 11) := (pow_succ' 2 _).symm
    have hcl2 : Nat.clog 2 (2 * n_leaf ^ 2 + 2) ≤ 18 * s + 24 := by
      refine Nat.clog_le_of_le_pow ?_
      have hsq : 2 * n_leaf ^ 2 + 2 ≤ 4 * (2 ^ (9 * s + 10)) ^ 2 := by
        have h1 : 1 ≤ (2 ^ (9 * s + 10)) ^ 2 := Nat.one_le_pow 2 _ (Nat.two_pow_pos _)
        have h2 := Nat.pow_le_pow_left hn_leaf_le 2
        omega
      calc 2 * n_leaf ^ 2 + 2 ≤ 2 ^ 2 * (2 ^ (9 * s + 10)) ^ 2 := hsq
        _ = 2 ^ (18 * s + 22) := by rw [← Nat.pow_mul, ← Nat.pow_add]; congr 1; ring
        _ ≤ 2 ^ (18 * s + 24) := Nat.pow_le_pow_right Nat.two_pos (by omega)
    have hcl_pow : Nat.clog 2 (2 * n_leaf ^ 2 + 2) ≤ 2 ^ (18 * s + 24) :=
      hcl2.trans Nat.lt_two_pow_self.le
    have hU_pow : U_leaf ≤ 2 ^ (36 * s + 44) := Nat.pow_le_pow_right Nat.two_pos hid_k_le
    have htot_pow : U_leaf * U_leaf ^ n_leaf * (2 * n_leaf) ^ n_leaf * 2 ^ (18 * s + 24) ≤
        2 ^ ((48 * (s + 1)) * 2 ^ (9 * s + 10)) := by
      have hm1 := Nat.mul_le_mul hU_pow (Nat.pow_le_pow_left hU_pow n_leaf)
      have hm2 := Nat.mul_le_mul hm1 (Nat.pow_le_pow_left h2n n_leaf)
      calc U_leaf * U_leaf ^ n_leaf * (2 * n_leaf) ^ n_leaf * 2 ^ (18 * s + 24)
          ≤ 2 ^ (36 * s + 44) * (2 ^ (36 * s + 44)) ^ n_leaf *
              (2 ^ (9 * s + 11)) ^ n_leaf * 2 ^ (18 * s + 24) :=
            Nat.mul_le_mul_right _ hm2
        _ = 2 ^ ((45 * s + 55) * n_leaf + (54 * s + 68)) := by
            rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
            congr 1; ring
        _ ≤ 2 ^ ((48 * (s + 1)) * 2 ^ (9 * s + 10)) := by
            refine Nat.pow_le_pow_right Nat.two_pos ?_
            have h2_ge : 54 * s + 68 ≤ (3 * s - 7) * 2 ^ (9 * s + 10) := by
              have hpow10 : 1024 ≤ 2 ^ (9 * s + 10) :=
                (by norm_num : 1024 = 2 ^ 10) ▸ Nat.pow_le_pow_right Nat.two_pos (by omega)
              calc 54 * s + 68 ≤ (3 * s - 7) * 1024 := by omega
                _ ≤ (3 * s - 7) * 2 ^ (9 * s + 10) := Nat.mul_le_mul_left _ hpow10
            calc (45 * s + 55) * n_leaf + (54 * s + 68)
                ≤ (45 * s + 55) * 2 ^ (9 * s + 10) + (3 * s - 7) * 2 ^ (9 * s + 10) :=
                  Nat.add_le_add (Nat.mul_le_mul_left _ hn_leaf_le) h2_ge
              _ = (48 * (s + 1)) * 2 ^ (9 * s + 10) := by
                  rw [← Nat.add_mul]; congr 1; omega
    calc minimapTabBits
        ≤ (U_leaf * U_leaf.choose n_leaf * (2 * n_leaf) ^ n_leaf) * 2 ^ (18 * s + 24) :=
          Nat.mul_le_mul hqt hcl_pow
      _ ≤ (U_leaf * U_leaf ^ n_leaf * (2 * n_leaf) ^ n_leaf) * 2 ^ (18 * s + 24) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hch))
      _ ≤ 2 ^ ((48 * (s + 1)) * 2 ^ (9 * s + 10)) := htot_pow
      _ ≤ 2 ^ (L / 2) := Nat.pow_le_pow_right Nat.two_pos hexp_half
  have hclmul_r : clmulBits * r ≤ n := by
    have hcap_max : max P.cap 2 = n := by rw [hcap]; exact max_eq_left hn2
    have hcl_pad : Nat.clog 2 (max P.paddedUniv 2) ≤ L ^ 2 := by
      refine Nat.clog_le_of_le_pow (max_le hpad_L2 ?_)
      exact (by norm_num : 2 = 2 ^ 1) ▸
        Nat.pow_le_pow_right Nat.two_pos (Nat.one_le_pow 2 L (by omega))
    set q := L / 3
    have hq_ge : 800000 ≤ q := by omega
    have hpoly_q : (6 * L ^ 2 + 6) * L ≤ 2 ^ q := by
      have hL_4q : L ≤ 4 * q := by omega
      have hq4 : q ^ 4 ≤ 2 ^ q := Nat.pow_le_two_pow (by decide) (by omega)
      calc (6 * L ^ 2 + 6) * L ≤ (7 * L ^ 2) * L := by
            have hL2 : 6 ≤ L ^ 2 :=
              (by norm_num : 6 ≤ 4 ^ 2).trans (Nat.pow_le_pow_left (by omega : 4 ≤ L) 2)
            exact Nat.mul_le_mul_right L (by omega)
        _ = 7 * L ^ 3 := by ring
        _ ≤ 7 * (4 * q) ^ 3 := Nat.mul_le_mul_left 7 (Nat.pow_le_pow_left hL_4q 3)
        _ = 448 * q ^ 3 := by ring
        _ ≤ q * q ^ 3 := Nat.mul_le_mul_right _ (by omega)
        _ = q ^ 4 := (pow_succ' q 3).symm
        _ ≤ 2 ^ q := hq4
    calc clmulBits * r
        = 2 ^ (2 * q) * (6 * Nat.clog 2 (max P.paddedUniv 2) + 6) * r := by
          dsimp only [clmulBits, q]; rw [hcap_max, ← hL_eq]
      _ ≤ 2 ^ (2 * q) * ((6 * L ^ 2 + 6) * L) := by
          rw [Nat.mul_assoc]
          exact Nat.mul_le_mul_left _
            (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 6 hcl_pad) 6) hr_le_L)
      _ ≤ 2 ^ (2 * q) * 2 ^ q := Nat.mul_le_mul_left _ hpoly_q
      _ = 2 ^ (3 * q) := by rw [← Nat.pow_add]; congr 1; ring
      _ ≤ 2 ^ L := Nat.pow_le_pow_right Nat.two_pos (by omega)
      _ ≤ n := hn_2L
  have hm_r : matchBits * r ≤ n := (Nat.mul_le_mul_right r hmatch_le).trans hL_pow_half
  have hmm_r : minimapTabBits * r ≤ n := (Nat.mul_le_mul_right r hminimap_le).trans hL_pow_half
  rw [Nat.add_mul, Nat.add_mul]
  omega

private theorem dfs_of_schedule (P : TreeSchedule) {n r L t : ℕ}
    (hn2 : 2 ≤ n) (hL_eq : L = Nat.log 2 n) (h2M : 2560000 ≤ L)
    (ht_eq : t = Nat.log 2 L) (ht_ge : 300 ≤ t) (hr_le_L : r ≤ L)
    (hcap : P.cap = n) (hk_le_r : P.depth ≤ r)
    (hk_3t : 3 ≤ P.depth → P.depth ≤ 3 * t)
    (hid_j : 3 ≤ P.depth → ∀ j, 3 ≤ j → j ≤ P.depth →
      P.idBits (j - 1) ≤ 444 * t ∧ P.idBits j ≤ 444 * t)
    (hnf_j : 3 ≤ P.depth → ∀ j, 3 ≤ j → j ≤ P.depth → P.nFloor j ≤ t ^ 11)
    (hrat_j : 3 ≤ P.depth → ∀ j, 3 ≤ j → j ≤ P.depth → P.numNodes j / P.numNodes 3 ≤ t ^ 11)
    (hsq_j : ∀ j < P.depth, (P.routerSeedBits j) ^ 2 ≤ P.nFloor j)
    (hhd_j : ∀ j ≤ P.depth, 2 * P.delta j ≤ P.nFloor j) :
    (if 3 ≤ P.depth then
      2 ^ (P.subtreeMetaBits 3 + P.idBits 3) * (Nat.clog 2 (P.cap + P.depth + 2) + P.idBits 3)
    else 0) * r ≤ n := by
  split_ifs with h3
  · have ht_pow : 2 ^ t ≤ L := ht_eq ▸ Nat.pow_log_le_self 2 (by omega)
    have hn_2L : 2 ^ L ≤ n := hL_eq ▸ Nat.pow_log_le_self 2 (by omega)
    have ht31_L : 512 * t ^ 31 ≤ L := by
      set m := t / 32
      have hm_ge : 9 ≤ m := by omega
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hm_ge
      have ht_2m : t ≤ 2 ^ m := by
        have hd1 := add_one_le_two_pow d
        have h9 : (2 : ℕ) ^ 9 = 512 := by norm_num
        calc t ≤ 32 * m + 31 := by omega
          _ = 319 + 32 * d := by omega
          _ ≤ 512 * (d + 1) := by omega
          _ ≤ 2 ^ 9 * 2 ^ d := by rw [h9]; exact Nat.mul_le_mul_left _ hd1
          _ = 2 ^ m := by rw [← Nat.pow_add]; congr 1; omega
      calc 512 * t ^ 31 ≤ 2 ^ 9 * (2 ^ m) ^ 31 := by
            have h9 : (512 : ℕ) = 2 ^ 9 := by norm_num
            rw [h9]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht_2m 31)
        _ = 2 ^ (9 + 31 * m) := by rw [← Nat.pow_mul, ← Nat.pow_add, Nat.mul_comm m 31]
        _ ≤ 2 ^ t := Nat.pow_le_pow_right Nat.two_pos (by omega)
        _ ≤ L := ht_pow
    have hmeta_j_le : ∀ j, 3 ≤ j → j ≤ P.depth → P.nodeMetaBits j ≤ t ^ 15 := by
      intro j hj3 hjk
      obtain ⟨hid_prev, hid_cur⟩ := hid_j h3 j hj3 hjk
      have hnf := hnf_j h3 j hj3 hjk
      have hd_j_le : P.delta j ≤ t ^ 11 := (P.delta_lt_nFloor j (by omega) hjk).le.trans hnf
      have hseed_j : P.nodeHashSeedBits j ≤ t ^ 12 := by
        dsimp only [TreeSchedule.nodeHashSeedBits]
        rw [ite_eq_right (by omega)]
        have hr_part : (if j < P.depth then P.routerSeedBits j else 0) ≤ t ^ 11 := by
          split_ifs with hlt
          · have hsq := hsq_j j hlt
            rcases le_or_gt (P.routerSeedBits j) 1 with h1 | hgt1
            · exact h1.trans (Nat.one_le_pow 11 t (by omega))
            · exact ((Nat.le_mul_of_pos_right _ (by omega : 1 ≤ P.routerSeedBits j)).trans
                ((sq (P.routerSeedBits j)).symm ▸ hsq)).trans hnf
          · simp
        have hic_part : FeistelPerm.idCompressorSeedBits (P.idBits j) (P.idCompRightUniv j) ≤
            3000 * t := by
          have hic := FeistelPerm.idCompressorSeedBits_le (P.idBits j) (P.idCompRightUniv j)
          have hcl_rem : Nat.clog 2 (max (P.idCompRightUniv j) 2) ≤ 445 * t := by
            dsimp only [TreeSchedule.idCompRightUniv]
            rw [ite_eq_right (by omega)]
            refine Nat.clog_le_of_le_pow (max_le ?_ ?_)
            · refine Nat.pow_le_pow_right Nat.two_pos ?_
              dsimp only [TreeSchedule.remBits]; omega
            · exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_le_pow_right Nat.two_pos (by omega)
          have hid_m : max (P.idBits j) 1 ≤ 445 * t := max_le (by omega) (by omega)
          have := max_le hcl_rem hid_m
          omega
        have h3000_t11 : 3000 * t ≤ t ^ 11 := by
          calc 3000 * t ≤ (10 * t) * t := Nat.mul_le_mul_right t (by omega)
            _ = 10 * t ^ 2 := by ring
            _ ≤ t * t ^ 2 := Nat.mul_le_mul_right _ (by omega)
            _ = t ^ 3 := (pow_succ' t 2).symm
            _ ≤ t ^ 11 := Nat.pow_le_pow_right (by omega) (by decide)
        calc (if j < P.depth then P.routerSeedBits j else 0) +
              FeistelPerm.idCompressorSeedBits (P.idBits j) (P.idCompRightUniv j)
            ≤ t ^ 11 + t ^ 11 := Nat.add_le_add hr_part (hic_part.trans h3000_t11)
          _ = 2 * t ^ 11 := (two_mul _).symm
          _ ≤ t * t ^ 11 := Nat.mul_le_mul_right _ (by omega)
          _ = t ^ 12 := (pow_succ' t 11).symm
      have hwait_j : waitingListBits (P.waitCap j) (P.idBits j) (P.idBits (j - 1)) ≤
          2500 * t ^ 12 := by
        dsimp only [waitingListBits, TreeSchedule.waitCap]
        have hnh_id := P.nHigh_le_two_pow_idBits j (by omega) hjk
        have hhd := hhd_j j hjk
        have hnf_pos := P.nFloor_pos j hjk
        have hcl_w : Nat.clog 2 (2 * P.delta j + 1) ≤ P.idBits j :=
          Nat.clog_le_of_le_pow (by omega)
        have h1 : Nat.clog 2 (2 * P.delta j + 1) +
            2 * P.delta j * (P.idBits j + P.idBits (j - 1)) ≤
            1776 * P.delta j * t + 444 * t := by
          have hcl_t : Nat.clog 2 (2 * P.delta j + 1) ≤ 444 * t := hcl_w.trans hid_cur
          have hmul_t : 2 * P.delta j * (P.idBits j + P.idBits (j - 1)) ≤
              2 * P.delta j * (444 * t + 444 * t) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add hid_cur hid_prev)
          linarith
        have ht_t12 : t ≤ t ^ 12 := Nat.le_self_pow (by decide) t
        have hd_t12 : P.delta j * t ≤ t ^ 12 := by
          calc P.delta j * t ≤ t ^ 11 * t := Nat.mul_le_mul_right t hd_j_le
            _ = t ^ 12 := (pow_succ t 11).symm
        calc Nat.clog 2 (2 * P.delta j + 1) +
              2 * P.delta j * (P.idBits j + P.idBits (j - 1))
            ≤ 1776 * (P.delta j * t) + 444 * t := by linarith
          _ ≤ 1776 * t ^ 12 + 444 * t ^ 12 :=
              Nat.add_le_add (Nat.mul_le_mul_left _ hd_t12) (Nat.mul_le_mul_left _ ht_t12)
          _ ≤ 2500 * t ^ 12 := by omega
      dsimp only [TreeSchedule.nodeMetaBits]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      have h45000 : 45000 ≤ t ^ 2 :=
        (by norm_num : 45000 ≤ 300 ^ 2).trans (Nat.pow_le_pow_left ht_ge 2)
      have ht14_15 : t ^ 14 ≤ t ^ 15 := Nat.pow_le_pow_right (by omega) (by decide)
      split_ifs with hlt
      · have htc_le : P.tableCap j ≤ t ^ 11 := by
          dsimp only [TreeSchedule.tableCap, TreeSchedule.nLow]
          rw [ite_eq_right (by omega), ite_eq_left hlt, ite_eq_right (by omega)]
          exact ((Nat.sub_le _ _).trans (Nat.sub_le _ _)).trans hnf
        have htc_id : P.tableCap j ≤ 2 ^ P.idBits j := by
          dsimp only [TreeSchedule.tableCap, TreeSchedule.nLow]
          rw [ite_eq_right (by omega), ite_eq_left hlt, ite_eq_right (by omega)]
          exact ((Nat.sub_le _ _).trans (Nat.sub_le _ _)).trans
            ((Nat.le_add_right _ _).trans (P.nHigh_le_two_pow_idBits j (by omega) hjk))
        have hstb : succinctTableMetaBits (P.idBits j) (P.tableCap j) ≤ 40000 * t ^ 12 := by
          have hm := succinctTableMetaBits_le htc_id
          have hid2 : P.idBits j + 2 ≤ 446 * t := by omega
          have ht11 : 1 ≤ t ^ 11 := Nat.one_le_pow 11 t (by omega)
          calc succinctTableMetaBits (P.idBits j) (P.tableCap j)
              ≤ (75 * P.tableCap j + 9) * (P.idBits j + 2) := by linarith
            _ ≤ (75 * t ^ 11 + 9 * t ^ 11) * (446 * t) :=
                Nat.mul_le_mul (by linarith) hid2
            _ = 37464 * (t ^ 11 * t) := by ring
            _ = 37464 * t ^ 12 := by rw [← pow_succ]
            _ ≤ 40000 * t ^ 12 := by omega
        calc P.nodeHashSeedBits j +
              waitingListBits (P.waitCap j) (P.idBits j) (P.idBits (j - 1)) +
              succinctTableMetaBits (P.idBits j) (P.tableCap j)
            ≤ 45000 * t ^ 12 := by linarith
          _ ≤ t ^ 2 * t ^ 12 := Nat.mul_le_mul_right _ h45000
          _ = t ^ 14 := (Nat.pow_add t 2 12).symm
          _ ≤ t ^ 15 := ht14_15
      · have hj_eq : j = P.depth := by omega
        subst hj_eq
        set n' := P.nLow P.depth
        have hn'_le : n' ≤ t ^ 11 := by
          dsimp only [n', TreeSchedule.nLow]
          rw [ite_eq_right (by omega)]
          exact (Nat.sub_le _ _).trans hnf
        have h2n'_id : 2 * n' ≤ 2 ^ (P.idBits P.depth + 1) := by
          have hn'_id : n' ≤ 2 ^ P.idBits P.depth := by
            dsimp only [n', TreeSchedule.nLow]
            rw [ite_eq_right (by omega)]
            exact (Nat.sub_le _ _).trans
              ((Nat.le_add_right _ _).trans (P.nHigh_le_two_pow_idBits P.depth (by omega) le_rfl))
          calc 2 * n' ≤ 2 * 2 ^ P.idBits P.depth := Nat.mul_le_mul_left 2 hn'_id
            _ = 2 ^ (P.idBits P.depth + 1) := (pow_succ' 2 _).symm
        have hcl_leaf : Nat.clog 2 ((2 ^ P.idBits P.depth).choose n' * (2 * n') ^ n') ≤
            889 * t ^ 12 := by
          have hch := choose_le_pow_self (2 ^ P.idBits P.depth) n'
          refine Nat.clog_le_of_le_pow ?_
          calc (2 ^ P.idBits P.depth).choose n' * (2 * n') ^ n'
              ≤ (2 ^ P.idBits P.depth) ^ n' * (2 ^ (P.idBits P.depth + 1)) ^ n' :=
                Nat.mul_le_mul hch (Nat.pow_le_pow_left h2n'_id n')
            _ = 2 ^ ((2 * P.idBits P.depth + 1) * n') := by
                rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]; congr 1; ring
            _ ≤ 2 ^ (889 * t ^ 12) := by
                refine Nat.pow_le_pow_right Nat.two_pos ?_
                have hid2 : 2 * P.idBits P.depth + 1 ≤ 889 * t := by omega
                calc (2 * P.idBits P.depth + 1) * n' ≤ (889 * t) * t ^ 11 :=
                      Nat.mul_le_mul hid2 hn'_le
                  _ = 889 * (t * t ^ 11) := by ring
                  _ = 889 * t ^ 12 := by rw [← pow_succ']
        calc P.nodeHashSeedBits P.depth +
              waitingListBits (P.waitCap P.depth) (P.idBits P.depth) (P.idBits (P.depth - 1)) +
              Nat.clog 2 ((2 ^ P.idBits P.depth).choose n' * (2 * n') ^ n')
            ≤ 45000 * t ^ 12 := by linarith
          _ ≤ t ^ 2 * t ^ 12 := Nat.mul_le_mul_right _ h45000
          _ = t ^ 14 := (Nat.pow_add t 2 12).symm
          _ ≤ t ^ 15 := ht14_15
    have hsub_half : P.subtreeMetaBits 3 + P.idBits 3 ≤ L / 2 := by
      have hk3 := hk_3t h3
      have hsum_le : P.subtreeMetaBits 3 ≤ 3 * t ^ 27 := by
        dsimp only [TreeSchedule.subtreeMetaBits]
        calc ∑ j ∈ Finset.Icc 3 P.depth, (P.numNodes j / P.numNodes 3) * P.nodeMetaBits j
            ≤ ∑ _j ∈ Finset.Icc 3 P.depth, t ^ 26 := by
              refine Finset.sum_le_sum fun j hj => ?_
              obtain ⟨hj3, hjk⟩ := Finset.mem_Icc.mp hj
              calc (P.numNodes j / P.numNodes 3) * P.nodeMetaBits j
                  ≤ t ^ 11 * t ^ 15 :=
                    Nat.mul_le_mul (hrat_j h3 j hj3 hjk) (hmeta_j_le j hj3 hjk)
                _ = t ^ 26 := (Nat.pow_add t 11 15).symm
          _ = (Finset.Icc 3 P.depth).card * t ^ 26 := by simp
          _ ≤ (3 * t) * t ^ 26 := by
              refine Nat.mul_le_mul_right _ ?_
              rw [Nat.card_Icc]; omega
          _ = 3 * (t * t ^ 26) := by ring
          _ = 3 * t ^ 27 := by rw [← pow_succ']
      have hid3 := (hid_j h3 3 le_rfl h3).2
      have ht31_sum : P.subtreeMetaBits 3 + P.idBits 3 ≤ t ^ 31 := by
        have ht27 : t ≤ t ^ 27 := Nat.le_self_pow (by decide) t
        have h447 : 447 ≤ t ^ 4 := by
          calc 447 ≤ t ^ 2 := (by norm_num : 447 ≤ 300 ^ 2).trans (Nat.pow_le_pow_left ht_ge 2)
            _ ≤ t ^ 4 := Nat.pow_le_pow_right (by omega) (by decide)
        calc P.subtreeMetaBits 3 + P.idBits 3
            ≤ 3 * t ^ 27 + 444 * t ^ 27 :=
              Nat.add_le_add hsum_le (hid3.trans (Nat.mul_le_mul_left 444 ht27))
          _ = 447 * t ^ 27 := by ring
          _ ≤ t ^ 4 * t ^ 27 := Nat.mul_le_mul_right _ h447
          _ = t ^ 31 := (Nat.pow_add t 4 27).symm
      omega
    have hmul_L : (Nat.clog 2 (P.cap + P.depth + 2) + P.idBits 3) * r ≤ 2 ^ (L / 2) := by
      have hcl_cap : Nat.clog 2 (P.cap + P.depth + 2) ≤ L + 2 := by
        have hk_n : P.depth + 2 ≤ n := by
          have hk_L : P.depth ≤ L := hk_le_r.trans hr_le_L
          have hL_sq : L ^ 2 ≤ 2 ^ L := Nat.sq_le_two_pow (by omega)
          have h2L : L + 2 ≤ L ^ 2 := by nlinarith
          exact (Nat.add_le_add_right hk_L 2).trans (h2L.trans (hL_sq.trans hn_2L))
        refine Nat.clog_le_of_le_pow ?_
        have hn_lt : n < 2 ^ (L + 1) := hL_eq ▸ Nat.lt_pow_succ_log_self Nat.one_lt_two n
        calc P.cap + P.depth + 2 ≤ 2 * 2 ^ (L + 1) := by omega
          _ = 2 ^ (L + 2) := (pow_succ' 2 _).symm
      have hid3_L : P.idBits 3 ≤ L := by
        have hid3 := (hid_j h3 3 le_rfl h3).2
        have ht_L : 444 * t ≤ 512 * t ^ 31 := by
          have ht31 : t ≤ t ^ 31 := Nat.le_self_pow (by decide) t
          exact (Nat.mul_le_mul_left 444 ht31).trans (Nat.mul_le_mul_right _ (by omega))
        exact hid3.trans (ht_L.trans ht31_L)
      have hprod_L2 : (Nat.clog 2 (P.cap + P.depth + 2) + P.idBits 3) * r ≤ 3 * L ^ 2 := by
        have hsum_3L : Nat.clog 2 (P.cap + P.depth + 2) + P.idBits 3 ≤ 3 * L := by omega
        calc (Nat.clog 2 (P.cap + P.depth + 2) + P.idBits 3) * r
            ≤ (3 * L) * L := Nat.mul_le_mul hsum_3L hr_le_L
          _ = 3 * L ^ 2 := by ring
      have h3L2_pow : 3 * L ^ 2 ≤ 2 ^ (L / 2) := by
        set hL := L / 2
        have hhL_ge : 1000000 ≤ hL := by omega
        have hL_3hL : L ≤ 3 * hL := by omega
        have hhL3 : hL ^ 3 ≤ 2 ^ hL := Nat.pow_le_two_pow (by decide) (by omega)
        calc 3 * L ^ 2 ≤ 3 * (3 * hL) ^ 2 :=
              Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hL_3hL 2)
          _ = 27 * hL ^ 2 := by ring
          _ ≤ hL * hL ^ 2 := Nat.mul_le_mul_right _ (by omega)
          _ = hL ^ 3 := (pow_succ' hL 2).symm
          _ ≤ 2 ^ hL := hhL3
      exact hprod_L2.trans h3L2_pow
    calc 2 ^ (P.subtreeMetaBits 3 + P.idBits 3) *
          (Nat.clog 2 (P.cap + P.depth + 2) + P.idBits 3) * r
        = 2 ^ (P.subtreeMetaBits 3 + P.idBits 3) *
            ((Nat.clog 2 (P.cap + P.depth + 2) + P.idBits 3) * r) := by ring
      _ ≤ 2 ^ (L / 2) * 2 ^ (L / 2) :=
          Nat.mul_le_mul (Nat.pow_le_pow_right Nat.two_pos hsub_half) hmul_L
      _ = 2 ^ (L / 2 + L / 2) := (Nat.pow_add 2 _ _).symm
      _ ≤ 2 ^ L := Nat.pow_le_pow_right Nat.two_pos (by omega)
      _ ≤ n := hn_2L
  · simp

theorem sharedTables_slack_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).sharedTablesBits * redundancyRatio n R ≤ 4 * n := by
  obtain ⟨hr256, _, hr10⟩ := h.redundancyRatio_bounds
  obtain ⟨_, hs1_le⟩ := h.log_univ_bounds
  obtain ⟨hT_pos, hT_le⟩ := canonical_target_bounds h
  have hpoly : 2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ Nat.log 2 n :=
    (poly_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
  have hbase_p : max q_min 1 + p_max + 4 ≤ (max q_min 1 + p_max + 4) ^ 4 :=
    Nat.le_self_pow (by decide) _
  have ht_ge : 300 ≤ Nat.log 2 (Nat.log 2 n) := by
    refine (Nat.le_log_iff_pow_le Nat.one_lt_two (by omega)).mpr ?_
    rw [show (300 : ℕ) = 250 + 50 by decide, Nat.pow_add 2 250 50]
    exact (two_pow_300_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
  have hr_le_L : redundancyRatio n R ≤ Nat.log 2 n :=
    (Nat.le_self_pow (by decide : 10 ≠ 0) _).trans hr10
  have hpad_L2 : (canonicalSchedule h).paddedUniv ≤ 2 ^ ((Nat.log 2 n) ^ 2) := by
    have h2p : 2 * (p_max + 2) * Nat.log 2 n ≤ (Nat.log 2 n) ^ 2 := by
      have hpL : 2 * (p_max + 2) ≤ Nat.log 2 n := by omega
      exact (Nat.mul_le_mul_right _ hpL).trans (sq _).symm.le
    exact (paddedUniv_le_two_pow_mul_log h).trans (Nat.pow_le_pow_right Nat.two_pos h2p)
  have hnf_k_le : (canonicalSchedule h).nFloor (canonicalSchedule h).depth ≤
      2 * (redundancyRatio n R) ^ 9 := by
    have hhi := (targetSize_le_nFloor_and_lt (hT_pos _ le_rfl) (hT_le _ le_rfl)).2
    have hTk : targetSize n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R))
        (treeDepth U (redundancyRatio n R)) = (redundancyRatio n R) ^ 9 := by
      rw [targetSize_eq_levelScale_pow (by have := two_le_treeDepth U (redundancyRatio n R); omega)]
      simp [levelScale]
    rw [canonicalSchedule_nFloor_eq h _, canonicalSchedule_depth]
    omega
  have h1 := leafAndClmul_of_schedule (canonicalSchedule h) h.two_le_n rfl (by omega) rfl ht_ge
    hr10 rfl hnf_k_le
    (by rw [canonicalSchedule_idBits_eq h _, canonicalSchedule_nFloor_eq h _]; rfl) hpad_L2
  have hiter2_le : Nat.iterLog 2 U ≤ 3 * Nat.log 2 (Nat.log 2 n) := by
    set L := Nat.log 2 n
    set t := Nat.log 2 L
    have hs1_L2 : Nat.log 2 U ≤ L ^ 2 := by
      have hp2 : 2 * (p_max + 1) ≤ L := by omega
      exact (hs1_le.trans (Nat.mul_le_mul_right L hp2)).trans (sq L).symm.le
    have hL_lt : L < 2 ^ (t + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two L
    have hlogU_lt : Nat.log 2 U < 2 ^ (3 * t + 1) := by
      calc Nat.log 2 U ≤ (2 ^ (t + 1)) ^ 2 := hs1_L2.trans (Nat.pow_le_pow_left hL_lt.le 2)
        _ = 2 ^ (2 * t + 2) := by rw [← Nat.pow_mul]; congr 1; ring
        _ < 2 ^ (3 * t + 1) := Nat.pow_lt_pow_right Nat.one_lt_two (by omega)
    have h4r := h.four_mul_redundancyRatio_le_log_univ
    have hlogU_pos : Nat.log 2 U ≠ 0 := by dsimp [minRedundancyRatio] at hr256; omega
    simpa only [Nat.iterLog_succ, Nat.iterLog_zero] using
      Nat.lt_succ_iff.mp ((Nat.log_lt_iff_lt_pow Nat.one_lt_two hlogU_pos).mpr hlogU_lt)
  have hls_3t : 3 ≤ (canonicalSchedule h).depth →
      ∀ j, 3 ≤ j → j ≤ treeDepth U (redundancyRatio n R) →
        levelScale U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) j ≤
          3 * Nat.log 2 (Nat.log 2 n) := by
    intro h3 j hj3 hjk
    have h2lt : 2 < treeDepth U (redundancyRatio n R) := h3
    have hr_3t : redundancyRatio n R ≤ 3 * Nat.log 2 (Nat.log 2 n) := by
      have := lt_iterLog_of_lt_treeDepth le_rfl h2lt
      omega
    dsimp only [levelScale]
    split_ifs
    · exact (Nat.iterLog_anti_left U (by omega : 2 ≤ j)).trans hiter2_le
    · exact hr_3t
  have h2 := dfs_of_schedule (canonicalSchedule h) h.two_le_n rfl (by omega) rfl ht_ge hr_le_L
    rfl h.treeDepth_le_redundancyRatio
    (fun h3 => by
      have h2lt : 2 < treeDepth U (redundancyRatio n R) := h3
      have := lt_iterLog_of_lt_treeDepth le_rfl h2lt
      have hk := h.treeDepth_le_redundancyRatio
      rw [canonicalSchedule_depth]; omega)
    (fun h3 j hj3 hjk => by
      have hjk' : j ≤ treeDepth U (redundancyRatio n R) := hjk
      have hpred : (canonicalSchedule h).idBits (j - 1) ≤ 444 * Nat.log 2 (Nat.log 2 n) := by
        rw [canonicalSchedule_idBits_eq h (j - 1)]
        calc idBits n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) (j - 1)
            ≤ 148 * levelScale U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) j :=
              idBits_pred_le_mul_levelScale hr256 (by omega) hjk'
                (hT_pos (j - 1) (by omega)) (hT_le (j - 1) (by omega))
          _ ≤ 148 * (3 * Nat.log 2 (Nat.log 2 n)) :=
              Nat.mul_le_mul_left 148 (hls_3t h3 j hj3 hjk')
          _ = 444 * Nat.log 2 (Nat.log 2 n) := by ring
      have hstep := (canonicalSchedule h).idBits_step_le (j - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ j)] at hstep
      exact ⟨hpred, (Nat.le_add_left _ _).trans (hstep.trans hpred)⟩)
    (fun h3 j hj3 hjk => by
      have hjk' : j ≤ treeDepth U (redundancyRatio n R) := hjk
      have hhi := (targetSize_le_nFloor_and_lt (hT_pos j hjk') (hT_le j hjk')).2
      rw [targetSize_eq_levelScale_pow (by omega)] at hhi
      have hls := hls_3t h3 j hj3 hjk'
      set t := Nat.log 2 (Nat.log 2 n)
      have h2_3 : 2 * 3 ^ 9 ≤ t ^ 2 :=
        (by norm_num : 2 * 3 ^ 9 ≤ 300 ^ 2).trans (Nat.pow_le_pow_left ht_ge 2)
      rw [canonicalSchedule_nFloor_eq h j]
      calc nFloor n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) j
          ≤ 2 * (levelScale U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) j) ^ 9 := by
            omega
        _ ≤ 2 * (3 * t) ^ 9 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hls 9)
        _ = (2 * 3 ^ 9) * t ^ 9 := by ring
        _ ≤ t ^ 2 * t ^ 9 := Nat.mul_le_mul_right _ h2_3
        _ = t ^ 11 := (Nat.pow_add t 2 9).symm)
    (fun h3 j hj3 hjk => by
      have hjk' : j ≤ treeDepth U (redundancyRatio n R) := hjk
      have h3' : 3 ≤ treeDepth U (redundancyRatio n R) := h3
      have hdiv_eq : ((canonicalSchedule h).numNodes j / (canonicalSchedule h).numNodes 3) *
          (canonicalSchedule h).numNodes 3 = (canonicalSchedule h).numNodes j := by
        have hcbb : (canonicalSchedule h).cumBranchBits 3 ≤
            (canonicalSchedule h).cumBranchBits j := by
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj3
          clear hj3 hjk hjk'
          induction d with
          | zero => exact le_rfl
          | succ d ih =>
            dsimp only [TreeSchedule.cumBranchBits]
            exact ih.trans (Nat.le_add_right _ _)
        dsimp only [TreeSchedule.numNodes]
        exact Nat.div_mul_cancel (Nat.pow_dvd_pow 2 hcbb)
      obtain ⟨_, hhi3⟩ := numNodes_mul_targetSize_bounds (hT_pos 3 h3') (hT_le 3 h3')
      obtain ⟨hNTj, _⟩ := numNodes_mul_targetSize_bounds (hT_pos j hjk') (hT_le j hjk')
      have hNj_le : (canonicalSchedule h).numNodes j ≤ n := by
        rw [canonicalSchedule_numNodes_eq h hjk]
        exact (Nat.le_mul_of_pos_right _ (hT_pos j hjk')).trans hNTj
      have hmul_3 : ((canonicalSchedule h).numNodes j / (canonicalSchedule h).numNodes 3) *
          (canonicalSchedule h).numNodes 3 ≤
          (2 * targetSize n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) 3) *
            (canonicalSchedule h).numNodes 3 := by
        rw [hdiv_eq, canonicalSchedule_numNodes_eq h h3]
        linarith
      have hrat2 := Nat.le_of_mul_le_mul_right hmul_3 ((canonicalSchedule h).numNodes_pos 3)
      rw [targetSize_eq_levelScale_pow (by decide : 1 ≤ 3)] at hrat2
      have hls3 := hls_3t h3 3 le_rfl h3'
      set t := Nat.log 2 (Nat.log 2 n)
      have h2_3 : 2 * 3 ^ 9 ≤ t ^ 2 :=
        (by norm_num : 2 * 3 ^ 9 ≤ 300 ^ 2).trans (Nat.pow_le_pow_left ht_ge 2)
      calc (canonicalSchedule h).numNodes j / (canonicalSchedule h).numNodes 3
          ≤ 2 * (3 * t) ^ 9 :=
            hrat2.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hls3 9))
        _ = (2 * 3 ^ 9) * t ^ 9 := by ring
        _ ≤ t ^ 2 * t ^ 9 := Nat.mul_le_mul_right _ h2_3
        _ = t ^ 11 := (Nat.pow_add t 2 9).symm)
    (fun j hlt => routerSeedBits_sq_le_nFloor h hlt)
    (fun j hj => by
      have hg := nFloor_ge_pow_256 h hj
      rw [canonicalSchedule_nFloor_eq h j] at hg
      rw [canonicalSchedule_delta_eq h j, canonicalSchedule_nFloor_eq h j]
      exact two_mul_delta_le_nFloor_of_eight_le ((by decide : 8 ≤ 256 ^ 9).trans hg))
  have hadd : ((canonicalSchedule h).sharedTablesBits) * redundancyRatio n R ≤ 3 * n + n := by
    have hsum := Nat.add_le_add h1 h2
    rwa [← Nat.add_mul] at hsum
  omega

private theorem redundancySlack_sub_one_of_schedule (P : TreeSchedule) {n r : ℕ}
    (hb1 : (3 * P.numNodes P.depth + 3 * (P.cap - P.numNodes P.depth * P.nLow P.depth)) * r ≤
      9 * n)
    (hb2 : ((∑ ℓ ∈ Finset.Ico 2 P.depth,
        P.numNodes ℓ *
          (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
            P.tableCap ℓ * Nat.clog 2 (2 * (P.nFloor ℓ + 1)))) +
      P.numNodes 1 *
        (succinctTableMetaBits (P.idBits 1) (P.tableCap 1) +
          P.tableCap 1 *
            (Nat.clog 2 (2 * (P.nFloor 1 + 1)) + Nat.clog 2 (P.tableCap 1 + 1)))) * r ≤
      72000 * n)
    (hb3 : ((P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap) *
        Nat.clog 2 ((P.paddedUniv + P.cap - 1) / P.cap) + P.rootPoolDirBits) * r ≤ 8 * n)
    (hb4 : (P.allWaitingListsBits + P.allHashSeedsBits) * r ≤ 1700 * n)
    (hb5 : P.sharedTablesBits * r ≤ 4 * n) :
    (P.redundancySlack - 1) * r ≤ 74000 * n := by
  have heq : P.redundancySlack - 1 =
      (3 * P.numNodes P.depth + 3 * (P.cap - P.numNodes P.depth * P.nLow P.depth)) +
      ((∑ ℓ ∈ Finset.Ico 2 P.depth,
          P.numNodes ℓ *
            (succinctTableMetaBits (P.idBits ℓ) (P.tableCap ℓ) +
              P.tableCap ℓ * Nat.clog 2 (2 * (P.nFloor ℓ + 1)))) +
        P.numNodes 1 *
          (succinctTableMetaBits (P.idBits 1) (P.tableCap 1) +
            P.tableCap 1 *
              (Nat.clog 2 (2 * (P.nFloor 1 + 1)) + Nat.clog 2 (P.tableCap 1 + 1)))) +
      ((P.numNodes 1 * P.tableCap 1 - P.rootValPoolCap) *
          Nat.clog 2 ((P.paddedUniv + P.cap - 1) / P.cap) + P.rootPoolDirBits) +
      (P.allWaitingListsBits + P.allHashSeedsBits) +
      P.sharedTablesBits := by
    dsimp only [TreeSchedule.redundancySlack]
    omega
  rw [heq]
  nlinarith

/-- Total `V`-independent redundancy slack `(canonicalSchedule h).redundancySlack` is at most
`150000 * effRedundancy n R` across `ValidRegime`. -/
theorem redundancySlack_le_mul_effRedundancy {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).redundancySlack ≤ 150000 * effRedundancy n R := by
  have hr256 := h.redundancyRatio_bounds.1
  have hr1 : 1 ≤ redundancyRatio n R := by dsimp [minRedundancyRatio] at hr256; omega
  have hRe1 : 1 ≤ effRedundancy n R := effRedundancy_pos h.redundancy_pos n
  have hsub_r := redundancySlack_sub_one_of_schedule (canonicalSchedule h)
    (leaf_and_deficit_slack_le h) (nonLeaf_tables_slack_le h)
    (rootExtra_and_poolDir_slack_le h) (waitingLists_and_hashSeeds_slack_le h)
    (sharedTables_slack_le h)
  have hsub_Re := le_two_mul_effRedundancy_of_mul_ratio_le h.redundancy_pos hr1 hsub_r
  omega

/-- Explicit universal constant `O(1)` in the pure tree bit-budget bound
`totalTreeBits ≤ infoBits U V n + spaceConst * R`. -/
@[expose]
def spaceConst : ℕ := 160000

/-- **Headline Section 5 Pure Tree Bit-Budget Bound** (`[LiLiangYuZhou2024, Sections 5.2 & 5.6]`):
across all `ValidRegime U V n R p_min q_min p_max q_max` (with zero upper bound on the value bound
`V`), the total representation bits of `(canonicalSchedule h)` satisfy
`(canonicalSchedule h).totalTreeBits ≤ infoBits U V n + spaceConst * R`. -/
theorem totalTreeBits_le_infoBits_add {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).totalTreeBits ≤ infoBits U V n + spaceConst * R := by
  have hdiv : ∀ ℓ, 1 ≤ ℓ → ℓ < (canonicalSchedule h).depth →
      (canonicalSchedule h).cap ≤
        (canonicalSchedule h).numNodes ℓ * ((canonicalSchedule h).nFloor ℓ + 1) := by
    intro ℓ _ hlt
    rw [canonicalSchedule_cap, canonicalSchedule_nFloor_div_eq h hlt.le, Nat.mul_add, Nat.mul_one]
    have hdm := Nat.div_add_mod n ((canonicalSchedule h).numNodes ℓ)
    have hlt_m := Nat.mod_lt n ((canonicalSchedule h).numNodes_pos ℓ)
    omega
  have hU3 : 3 * (canonicalSchedule h).cap ≤ (canonicalSchedule h).paddedUniv := by
    have h2n := h.two_mul_n_le_univ
    have hpad := (canonicalSchedule h).univ_le_padded
    rw [canonicalSchedule_univ, canonicalSchedule_cap] at hpad
    rw [canonicalSchedule_cap]
    dsimp only [TreeSchedule.paddedUniv, TreeSchedule.branchFactor]
    omega
  have htot := (canonicalSchedule h).totalTreeBits_le_padded_infoBits_add hdiv hU3
  have hpad_info : infoBits (canonicalSchedule h).paddedUniv
      (canonicalSchedule h).valBound (canonicalSchedule h).cap ≤
      infoBits U V n + 2 * effRedundancy n R + 1 := infoBits_paddedUniv_le h
  have hslack := redundancySlack_le_mul_effRedundancy h
  have hRe_pos : 1 ≤ effRedundancy n R := effRedundancy_pos h.redundancy_pos n
  have hRe_le : effRedundancy n R ≤ R := effRedundancy_le n R
  dsimp only [spaceConst]
  linarith [Nat.mul_le_mul_left 150003 hRe_le]

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
