/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.BitBudget
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Canonical Large-Parameter Schedule and End-to-End `infoBits + O(R)` Space Bound

This module builds on `CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.Schedule` and
`CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.BitBudget` to formalize the
polynomial-universe large-parameter regime (`ValidRegime`), the canonical Section 5 parameter
instantiation (`canonicalSchedule`), its probabilistic concentration readiness
(`canonicalSchedule_concentrationReady`), and the end-to-end pure bit-budget bound
`totalTreeBits ≤ infoBits U V n + spaceConst * R` ([LiLiangYuZhou2024, Sections 5.1–5.2 and
5.4–5.6]; [arXiv:2310.20536v1](https://arxiv.org/abs/2310.20536v1), PDF pp. 25–36 / printed
pp. 24–35).

## Scope and adaptations

* **Clamped redundancy (`effRedundancy`) and small-node child-router regime switch**:
  `effRedundancy n R` clamps `R` below `n / max 256 (2 ^ log* n)` so `r ≥ 256` and
  `2 ^ log* n ≤ r` hold across all `R ≤ n` without inflating `thresholdN`. Nodes with
  `nLow ℓ < childRouterThreshold epsInv alphaInv` switch from Thorup's `DoubleTabulation` to exact
  `(2 * childRouterHalfInd (nHigh ℓ))`-wise `trinomialPolyHash`, avoiding `childRouterThreshold` in
  `thresholdN`.
* **Out-of-scope gaps**: Word-RAM `Memory.Prog` compilation, Section 4 small-`R` adapter trees
  (`R < n / log₂ ^ 0.1 n`), strong history independence, dynamic resizing in `|S|`, and
  super-polynomial key universes (`U > n ^ (1 + α_max)`) are out of scope here.

## Main definitions

* `Cslib.DataStructure.Dictionary.SubconstantRedundancy.routerEpsInv`, `routerAlphaInv`,
  `thresholdLogN`, `thresholdN`, `ValidRegime`, `canonicalSchedule`, `spaceConst`.

## Main results

* `canonicalSchedule_concentrationReady`: `canonicalSchedule` satisfies `ConcentrationReady`.
* `totalTreeBits_le_infoBits_add`: end-to-end pure space bound
  `(canonicalSchedule h).totalTreeBits ≤ infoBits U V n + spaceConst * R`.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Finset

/-! ## Section 2: Large-parameter polynomial-`U` regime and `canonicalSchedule` -/

/-- Inverse space exponent `ε_inv = max 12 (2 * (p_max + 3))` for `DoubleTabulation` child
routers across polynomial universes `U ≤ n ^ (1 + p_max / q_max)`. -/
@[expose]
def routerEpsInv (p_max : ℕ) : ℕ :=
  max 12 (2 * (p_max + 3))

/-- Gap exponent `α_inv = max q_min 1 + 1` (`≥ 2`) for `DoubleTabulation` child routers across
polynomial universes `n ^ (1 + p_min / q_min) ≤ U`. -/
@[expose]
def routerAlphaInv (q_min : ℕ) : ℕ :=
  max q_min 1 + 1

/-- Base-2 logarithm threshold `L₀(q_min, p_max)` above which `2 ^ L₀ ≤ n` ensures all
poly-logarithmic and polynomial-gap inequalities in Section 5. -/
def thresholdLogN (q_min p_max : ℕ) : ℕ :=
  max (2 ^ 250 * 2 ^ 50) (2560000 * (max q_min 1 + p_max + 4) ^ 4)

/-- Minimum dictionary capacity `n₀(q_min, p_max) = 2 ^ thresholdLogN q_min p_max` for the
Section 5 large-parameter polynomial-`U` regime. -/
@[expose]
def thresholdN (q_min p_max : ℕ) : ℕ :=
  2 ^ thresholdLogN q_min p_max

theorem thresholdN_eq (q_min p_max : ℕ) :
    thresholdN q_min p_max = 2 ^ thresholdLogN q_min p_max := rfl

theorem two_pow_300_le_thresholdLogN (q_min p_max : ℕ) :
    2 ^ 250 * 2 ^ 50 ≤ thresholdLogN q_min p_max :=
  le_max_left _ _

theorem poly_le_thresholdLogN (q_min p_max : ℕ) :
    2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ thresholdLogN q_min p_max :=
  le_max_right _ _

/-- Large-parameter polynomial-universe regime of `[LiLiangYuZhou2024, Section 5]`
(`n / (log₂ n) ^ 0.1 ≤ R ≤ n`, `n ^ (1 + p_min / q_min) ≤ U ≤ n ^ (1 + p_max / q_max)`,
`1 ≤ V`, `thresholdN q_min p_max ≤ n`). -/
structure ValidRegime (U V n R p_min q_min p_max q_max : ℕ) : Prop where
  p_min_pos : 1 ≤ p_min
  q_min_pos : 1 ≤ q_min
  q_max_pos : 1 ≤ q_max
  val_pos : 1 ≤ V
  n_ge_threshold : thresholdN q_min p_max ≤ n
  univ_lower : n ^ (q_min + p_min) ≤ U ^ q_min
  univ_upper : U ^ q_max ≤ n ^ (q_max + p_max)
  redundancy_pos : 1 ≤ R
  redundancy_le : R ≤ n
  redundancy_lower : n ^ 10 ≤ R ^ 10 * Nat.log 2 n

namespace ValidRegime

variable {U V n R p_min q_min p_max q_max : ℕ}

theorem thresholdLogN_le_log (h : ValidRegime U V n R p_min q_min p_max q_max) :
    thresholdLogN q_min p_max ≤ Nat.log 2 n := by
  have hn_pos : n ≠ 0 := by
    have hpos : 0 < thresholdN q_min p_max := Nat.two_pow_pos _
    have := h.n_ge_threshold
    omega
  exact (Nat.le_log_iff_pow_le Nat.one_lt_two hn_pos).mpr h.n_ge_threshold

theorem four_le_thresholdLogN (q_min p_max : ℕ) :
    4 ≤ thresholdLogN q_min p_max := by
  have hp := poly_le_thresholdLogN q_min p_max
  have h1 : 1 ≤ (max q_min 1 + p_max + 4) ^ 4 := Nat.one_le_pow 4 _ (by omega)
  omega

theorem two_le_n (h : ValidRegime U V n R p_min q_min p_max q_max) : 2 ≤ n := by
  have hle1 : 1 ≤ thresholdLogN q_min p_max := by
    have := four_le_thresholdLogN q_min p_max
    omega
  exact (Nat.pow_le_pow_right Nat.two_pos hle1).trans h.n_ge_threshold

theorem univ_le_pow (h : ValidRegime U V n R p_min q_min p_max q_max) :
    U ≤ n ^ (p_max + 1) := by
  have hexp : q_max + p_max ≤ q_max * (p_max + 1) := by
    have := h.q_max_pos
    nlinarith
  have hpow : U ^ q_max ≤ (n ^ (p_max + 1)) ^ q_max := by
    calc U ^ q_max ≤ n ^ (q_max + p_max) := h.univ_upper
      _ ≤ n ^ (q_max * (p_max + 1)) := Nat.pow_le_pow_right (by have := h.two_le_n; omega) hexp
      _ = (n ^ (p_max + 1)) ^ q_max := by rw [← Nat.pow_mul, Nat.mul_comm]
  exact (Nat.pow_le_pow_iff_left (by have := h.q_max_pos; omega)).mp hpow

theorem n_pow_succ_le_univ_pow (h : ValidRegime U V n R p_min q_min p_max q_max) :
    n ^ (q_min + 1) ≤ U ^ q_min :=
  (Nat.pow_le_pow_right (by have := h.two_le_n; omega)
    (by have := h.p_min_pos; omega)).trans h.univ_lower

theorem two_mul_n_le_univ (h : ValidRegime U V n R p_min q_min p_max q_max) :
    2 * n ≤ U := by
  have hn2 := h.two_le_n
  have hpow : (2 * n) ^ q_min ≤ U ^ q_min := by
    calc (2 * n) ^ q_min = 2 ^ q_min * n ^ q_min := Nat.mul_pow 2 n q_min
      _ ≤ n * n ^ q_min := by
          have h2n : 2 ^ q_min ≤ n := by
            have hL : q_min ≤ thresholdLogN q_min p_max := by
              have hp := poly_le_thresholdLogN q_min p_max
              have hbase : max q_min 1 + p_max + 4 ≤ (max q_min 1 + p_max + 4) ^ 4 :=
                Nat.le_self_pow (by decide) _
              omega
            exact (Nat.pow_le_pow_right Nat.two_pos hL).trans h.n_ge_threshold
          exact Nat.mul_le_mul_right _ h2n
      _ = n ^ (q_min + 1) := (pow_succ' n q_min).symm
      _ ≤ U ^ q_min := h.n_pow_succ_le_univ_pow
  exact (Nat.pow_le_pow_iff_left (by have := h.q_min_pos; omega)).mp hpow

theorem log_univ_bounds (h : ValidRegime U V n R p_min q_min p_max q_max) :
    Nat.log 2 n ≤ Nat.log 2 U ∧ Nat.log 2 U ≤ 2 * (p_max + 1) * Nat.log 2 n := by
  have hn2 := h.two_le_n
  have hUn : n ≤ U := by have := h.two_mul_n_le_univ; omega
  refine ⟨Nat.log_mono_right hUn, ?_⟩
  set L := Nat.log 2 n
  have hL1 : 1 ≤ L := by
    have := (two_pow_300_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
    omega
  have hn_lt : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
  have hU_lt : U < 2 ^ (2 * (p_max + 1) * L + 1) := by
    calc U ≤ n ^ (p_max + 1) := h.univ_le_pow
      _ ≤ (2 ^ (L + 1)) ^ (p_max + 1) := Nat.pow_le_pow_left hn_lt.le _
      _ = 2 ^ ((L + 1) * (p_max + 1)) := (Nat.pow_mul 2 (L + 1) (p_max + 1)).symm
      _ < 2 ^ (2 * (p_max + 1) * L + 1) :=
          Nat.pow_lt_pow_right Nat.one_lt_two (by nlinarith)
  exact Nat.lt_succ_iff.mp ((Nat.log_lt_iff_lt_pow Nat.one_lt_two (by omega)).mpr hU_lt)

private theorem logStar_le_triple_clog_add_three (x : ℕ) :
    Nat.logStar x ≤ Nat.clog 2 (Nat.clog 2 (Nat.clog 2 x)) + 3 := by
  set m := Nat.clog 2 (Nat.clog 2 (Nat.clog 2 x))
  rw [Nat.logStar_le_iff]
  have h1 : x ≤ 2 ^ Nat.clog 2 x := Nat.le_pow_clog Nat.one_lt_two x
  have h2 : Nat.clog 2 x ≤ 2 ^ Nat.clog 2 (Nat.clog 2 x) := Nat.le_pow_clog Nat.one_lt_two _
  have h3 : Nat.clog 2 (Nat.clog 2 x) ≤ 2 ^ m := Nat.le_pow_clog Nat.one_lt_two _
  have hm : m ≤ Nat.twoTower m := (Nat.lt_twoTower m).le
  calc x ≤ 2 ^ (2 ^ (2 ^ m)) :=
        h1.trans (Nat.pow_le_pow_right Nat.two_pos (h2.trans (Nat.pow_le_pow_right Nat.two_pos h3)))
    _ ≤ 2 ^ (2 ^ (2 ^ Nat.twoTower m)) :=
        Nat.pow_le_pow_right Nat.two_pos
          (Nat.pow_le_pow_right Nat.two_pos (Nat.pow_le_pow_right Nat.two_pos hm))
    _ = Nat.twoTower (m + 3) := rfl

theorem two_pow_logStar_le_log_log (h : ValidRegime U V n R p_min q_min p_max q_max) :
    2 ^ Nat.logStar n ≤ 32 * (Nat.log 2 (Nat.log 2 n) + 1) := by
  set L := Nat.log 2 n
  set t := Nat.log 2 L
  have hL_ge4 : 4 ≤ L := (four_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
  have hn_le : n ≤ 2 ^ (L + 1) := (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
  have hcl1 : Nat.clog 2 n ≤ L + 1 := Nat.clog_le_of_le_pow hn_le
  have hL_lt : L < 2 ^ (t + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two L
  have hcl2 : Nat.clog 2 (Nat.clog 2 n) ≤ t + 2 := by
    refine (Nat.clog_mono_right 2 hcl1).trans (Nat.clog_le_of_le_pow ?_)
    have : L + 1 ≤ 2 ^ (t + 1) := by omega
    exact this.trans (Nat.pow_le_pow_right Nat.two_pos (by omega))
  have hls := logStar_le_triple_clog_add_three n
  set m := Nat.clog 2 (Nat.clog 2 (Nat.clog 2 n))
  have h2m : 2 ^ m ≤ 2 * (t + 2) := by
    calc 2 ^ m ≤ 2 * max (Nat.clog 2 (Nat.clog 2 n)) 1 := by
          rcases Nat.eq_zero_or_pos (Nat.clog 2 (Nat.clog 2 n)) with h0 | hpos
          · simp [m, h0]
          · exact (Nat.pow_clog_le_mul Nat.one_lt_two hpos.ne').trans
              (Nat.mul_le_mul_left 2 (le_max_left _ 1))
      _ ≤ 2 * (t + 2) := Nat.mul_le_mul_left 2 (max_le hcl2 (by omega))
  calc 2 ^ Nat.logStar n ≤ 2 ^ (m + 3) := Nat.pow_le_pow_right Nat.two_pos hls
    _ = 8 * 2 ^ m := by rw [Nat.pow_add]; ring
    _ ≤ 8 * (2 * (t + 2)) := Nat.mul_le_mul_left 8 h2m
    _ ≤ 32 * (t + 1) := by omega

theorem redundancyRatio_bounds (h : ValidRegime U V n R p_min q_min p_max q_max) :
    minRedundancyRatio ≤ redundancyRatio n R ∧
      2 ^ Nat.logStar n ≤ redundancyRatio n R ∧
      (redundancyRatio n R) ^ 10 ≤ Nat.log 2 n := by
  set L := Nat.log 2 n
  set t := Nat.log 2 L
  have hL_ge4 : 4 ≤ L := (four_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
  have hL_pos : L ≠ 0 := by omega
  have ht_ge : 250 + 50 ≤ t := by
    refine (Nat.le_log_iff_pow_le Nat.one_lt_two hL_pos).mpr ?_
    rw [Nat.pow_add 2 250 50]
    exact (two_pow_300_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
  have hls_le : 2 ^ Nat.logStar n ≤ 32 * (t + 1) := h.two_pow_logStar_le_log_log
  have ht_pow : 2 ^ t ≤ L := Nat.pow_log_le_self 2 hL_pos
  set s := t / 10
  have hs_ge : 30 ≤ s := by omega
  have h704s : 704 * s ≤ 2 ^ s := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hs_ge
    have hsq : (15 + d) ^ 2 ≤ 2 ^ (15 + d) := Nat.sq_le_two_pow (by omega)
    have hmul : 2 ^ 15 * (15 + d) ^ 2 ≤ 2 ^ s := by
      calc 2 ^ 15 * (15 + d) ^ 2 ≤ 2 ^ 15 * 2 ^ (15 + d) := Nat.mul_le_mul_left _ hsq
        _ = 2 ^ s := by rw [← Nat.pow_add]; congr 1; omega
    have h15 : (2 : ℕ) ^ 15 = 32768 := by decide
    rw [h15] at hmul
    nlinarith
  have hn_large : 2 * 704 * s ≤ n := by
    have h1 : 2 * 704 * s ≤ 2 * L := by
      calc 2 * 704 * s ≤ 2 * 2 ^ s := by omega
        _ ≤ 2 * 2 ^ t := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right Nat.two_pos (by omega))
        _ ≤ 2 * L := Nat.mul_le_mul_left 2 ht_pow
    have h2L : 2 * L ≤ 2 ^ L := by
      calc 2 * L ≤ L * L := Nat.mul_le_mul_right L (by omega)
        _ = L ^ 2 := (sq L).symm
        _ ≤ 2 ^ L := Nat.sq_le_two_pow hL_ge4
    exact (h1.trans h2L).trans (Nat.pow_log_le_self 2 (by have := h.two_le_n; omega))
  set M := max minRedundancyRatio (2 ^ Nat.logStar n)
  have hM_le : M ≤ 352 * s := by
    dsimp only [M, minRedundancyRatio]
    exact max_le (by omega) (by omega)
  have hM_le_n : M ≤ n := by omega
  refine ⟨minRedundancyRatio_le_redundancyRatio (le_trans (le_max_left _ _) hM_le_n),
    two_pow_logStar_le_redundancyRatio (le_trans (le_max_right _ _) hM_le_n), ?_⟩
  have heff_pos : 1 ≤ effRedundancy n R := effRedundancy_pos h.redundancy_pos n
  have hr_eq : redundancyRatio n R = n / effRedundancy n R := by
    dsimp only [redundancyRatio]
    rw [max_eq_left heff_pos]
  dsimp only [effRedundancy] at hr_eq
  by_cases hR_le : R ≤ max 1 (n / M)
  · rw [min_eq_left hR_le] at hr_eq
    have hprod : (redundancyRatio n R * R) ^ 10 ≤ L * R ^ 10 := by
      rw [hr_eq, Nat.mul_comm L]
      exact (Nat.pow_le_pow_left (Nat.div_mul_le_self n R) 10).trans h.redundancy_lower
    rw [Nat.mul_pow] at hprod
    exact Nat.le_of_mul_le_mul_right hprod (Nat.pow_pos h.redundancy_pos)
  · rw [min_eq_right (not_le.mp hR_le).le] at hr_eq
    have hM_pos : 0 < M := by dsimp only [M, minRedundancyRatio]; omega
    have hdiv_ge1 : 1 ≤ n / M := (Nat.le_div_iff_mul_le hM_pos).mpr (by omega)
    rw [max_eq_right hdiv_ge1] at hr_eq
    have hr_le_2M : redundancyRatio n R ≤ 2 * M := by
      rw [hr_eq]
      refine Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hdiv_ge1).mpr ?_)
      have hdiv := Nat.div_add_mod n M
      have hmod := Nat.mod_lt n hM_pos
      have h2M_n : 2 * M ≤ n := by omega
      nlinarith
    have hr_le_2s : redundancyRatio n R ≤ 2 ^ s := by omega
    calc (redundancyRatio n R) ^ 10 ≤ (2 ^ s) ^ 10 := Nat.pow_le_pow_left hr_le_2s 10
      _ = 2 ^ (s * 10) := (Nat.pow_mul 2 s 10).symm
      _ ≤ 2 ^ t := Nat.pow_le_pow_right Nat.two_pos (by omega)
      _ ≤ L := ht_pow

theorem treeDepth_le_redundancyRatio (h : ValidRegime U V n R p_min q_min p_max q_max) :
    treeDepth U (redundancyRatio n R) ≤ redundancyRatio n R := by
  obtain ⟨hr256, hr_ls, _⟩ := h.redundancyRatio_bounds
  have hU_le : U ≤ n ^ (p_max + 1) := h.univ_le_pow
  set L := Nat.log 2 n
  have hL_ge4 : 4 ≤ L := (four_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
  have hpoly : 2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ L :=
    (poly_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
  have hbase_p : max q_min 1 + p_max + 4 ≤ (max q_min 1 + p_max + 4) ^ 4 :=
    Nat.le_self_pow (by decide) _
  have hU_tower : U ≤ 2 ^ (2 ^ L) := by
    have hn_lt : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two n
    have hexp_le : (L + 1) * (p_max + 1) ≤ 2 ^ L := by
      have hpL : 2 * (p_max + 1) ≤ L := by omega
      have hsq : L ^ 2 ≤ 2 ^ L := Nat.sq_le_two_pow hL_ge4
      have hmulL : (L + 1) * (p_max + 1) ≤ L ^ 2 := by
        calc (L + 1) * (p_max + 1) ≤ (2 * L) * (p_max + 1) :=
              Nat.mul_le_mul_right _ (by omega)
          _ = L * (2 * (p_max + 1)) := by ring
          _ ≤ L * L := Nat.mul_le_mul_left L hpL
          _ = L ^ 2 := (sq L).symm
      exact hmulL.trans hsq
    calc U ≤ n ^ (p_max + 1) := hU_le
      _ ≤ (2 ^ (L + 1)) ^ (p_max + 1) := Nat.pow_le_pow_left hn_lt.le _
      _ = 2 ^ ((L + 1) * (p_max + 1)) := (Nat.pow_mul 2 _ _).symm
      _ ≤ 2 ^ (2 ^ L) := Nat.pow_le_pow_right Nat.two_pos hexp_le
  have hlsU : Nat.floorLogStar U ≤ Nat.logStar n + 2 := by
    have hU_ls : Nat.logStar U ≤ Nat.logStar n + 2 := by
      rw [Nat.logStar_le_iff]
      have hn_tw : n ≤ Nat.twoTower (Nat.logStar n) := Nat.le_twoTower_logStar n
      have hL_tw : L ≤ Nat.twoTower (Nat.logStar n) := (Nat.log_le_self 2 n).trans hn_tw
      calc U ≤ 2 ^ (2 ^ L) := hU_tower
        _ ≤ 2 ^ (2 ^ Nat.twoTower (Nat.logStar n)) :=
            Nat.pow_le_pow_right Nat.two_pos (Nat.pow_le_pow_right Nat.two_pos hL_tw)
        _ = Nat.twoTower (Nat.logStar n + 2) := rfl
    exact (Nat.floorLogStar_le_logStar U).trans hU_ls
  have hk_le : treeDepth U (redundancyRatio n R) ≤ Nat.floorLogStar U + 2 :=
    treeDepth_le U _
  have hls_lt : Nat.logStar n + 4 ≤ 2 ^ Nat.logStar n := by
    have h3 : 3 ≤ Nat.logStar n := by
      by_contra hlt
      have hle2 : Nat.logStar n ≤ 2 := by omega
      have hn4 : n ≤ 4 := by
        have := Nat.le_twoTower_logStar n
        have htw : Nat.twoTower (Nat.logStar n) ≤ Nat.twoTower 2 :=
          Nat.twoTower_monotone hle2
        have h4 : Nat.twoTower 2 = 4 := by decide
        omega
      have h8 : 8 ≤ n := by
        have h3_le : 3 ≤ thresholdLogN q_min p_max := by
          have : 3 ≤ 2560000 * (max q_min 1 + p_max + 4) ^ 4 := by
            have := hbase_p; omega
          exact this.trans (poly_le_thresholdLogN q_min p_max)
        exact (show 8 = 2 ^ 3 by decide) ▸
          (Nat.pow_le_pow_right Nat.two_pos h3_le).trans h.n_ge_threshold
      omega
    rcases eq_or_lt_of_le h3 with h_eq3 | h_gt3
    · rw [← h_eq3]; decide
    · have hs4 : 4 ≤ Nat.logStar n := Nat.succ_le_of_lt h_gt3
      have hsq4 := Nat.sq_le_two_pow hs4
      nlinarith
  omega

theorem two_pow_eighteen_mul_log_univ_pow_le
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ n := by
  set L := Nat.log 2 n
  have hpoly : 2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ L :=
    (poly_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
  have hbase_p : max q_min 1 + p_max + 4 ≤ (max q_min 1 + p_max + 4) ^ 4 :=
    Nat.le_self_pow (by decide) _
  obtain ⟨_, hlogU_le⟩ := h.log_univ_bounds
  have hp_le_L : 8 * (p_max + 1) ≤ L := by omega
  have h2logU : 4 * Nat.log 2 U ≤ L ^ 2 := by
    calc 4 * Nat.log 2 U ≤ 4 * (2 * (p_max + 1) * L) := Nat.mul_le_mul_left 4 hlogU_le
      _ = (8 * (p_max + 1)) * L := by ring
      _ ≤ L * L := Nat.mul_le_mul_right L hp_le_L
      _ = L ^ 2 := (sq L).symm
  have hpow18 : 2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ L ^ 18 := by
    calc 2 ^ 18 * (Nat.log 2 U) ^ 9
        = (4 * Nat.log 2 U) ^ 9 := by
          have : (2 : ℕ) ^ 18 = 4 ^ 9 := by decide
          rw [this, ← Nat.mul_pow]
      _ ≤ (L ^ 2) ^ 9 := Nat.pow_le_pow_left h2logU 9
      _ = L ^ 18 := (Nat.pow_mul L 2 9).symm
  have hL18 : L ^ 18 ≤ 2 ^ L := Nat.pow_le_two_pow (by decide) (by omega)
  exact (hpow18.trans hL18).trans (Nat.pow_log_le_self 2 (by have := h.two_le_n; omega))

theorem four_mul_redundancyRatio_le_log_univ
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    4 * redundancyRatio n R ≤ Nat.log 2 U := by
  obtain ⟨hr256, _, hr10⟩ := h.redundancyRatio_bounds
  obtain ⟨hlogn, _⟩ := h.log_univ_bounds
  have h4r : 4 * redundancyRatio n R ≤ (redundancyRatio n R) ^ 10 := by
    have : 256 ≤ redundancyRatio n R := hr256
    calc 4 * redundancyRatio n R
        ≤ redundancyRatio n R * redundancyRatio n R := Nat.mul_le_mul_right _ (by omega)
      _ = (redundancyRatio n R) ^ 2 := (sq _).symm
      _ ≤ (redundancyRatio n R) ^ 10 := Nat.pow_le_pow_right (by omega) (by decide)
  exact (h4r.trans hr10).trans hlogn

end ValidRegime

/-- **Canonical Section 5 parameter schedule** instantiated from `(U, V, n, R, q_min, p_max)`
under `ValidRegime` ([LiLiangYuZhou2024, Sections 5.1–5.2]). -/
@[expose]
def canonicalSchedule {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) : TreeSchedule :=
  let r := redundancyRatio n R
  let k := treeDepth U r
  have hr256 : minRedundancyRatio ≤ r := h.redundancyRatio_bounds.1
  have h4r : 4 * r ≤ Nat.log 2 U := h.four_mul_redundancyRatio_le_log_univ
  have hn18 : 2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ n := h.two_pow_eighteen_mul_log_univ_pow_le
  have hstep : ∀ ℓ < k, 2 ^ 18 * targetSize n U r k (ℓ + 1) ≤ targetSize n U r k ℓ :=
    fun ℓ hlt => two_pow_eighteen_mul_targetSize_succ_le hr256 h4r hn18 hlt
  have hT_le : ∀ ℓ ≤ k, targetSize n U r k ℓ ≤ n := targetSize_le_of_step hstep
  have hT_pos : ∀ ℓ ≤ k, 1 ≤ targetSize n U r k ℓ := fun ℓ hℓ =>
    targetSize_pos (by have := h.two_le_n; omega) (by dsimp [minRedundancyRatio] at hr256; omega)
      h4r hℓ rfl
  have hS17 : ∀ ℓ < k, cumBranchBits n U r k ℓ + 17 ≤ cumBranchBits n U r k (ℓ + 1) :=
    fun ℓ hlt => cumBranchBits_add_seventeen_le (hT_pos ℓ hlt.le) (hT_pos (ℓ + 1) hlt)
      (hT_le ℓ hlt.le) (hstep ℓ hlt)
  have hnF8 : ∀ ℓ ≤ k, 256 ^ 9 ≤ nFloor n U r k ℓ := by
    intro ℓ hℓ
    obtain ⟨hlo, _⟩ := targetSize_le_nFloor_and_lt (hT_pos ℓ hℓ) (hT_le ℓ hℓ)
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · have : targetSize n U r k 0 = n := rfl
      have h1 : 256 ^ 9 ≤ 2 ^ 18 * (Nat.log 2 U) ^ 9 := by
        have hr_val : 256 ≤ Nat.log 2 U := by dsimp [minRedundancyRatio] at hr256; omega
        calc 256 ^ 9 ≤ (Nat.log 2 U) ^ 9 := Nat.pow_le_pow_left hr_val 9
          _ ≤ 2 ^ 18 * (Nat.log 2 U) ^ 9 := Nat.le_mul_of_pos_left _ (by positivity)
      exact (h1.trans hn18).trans (this ▸ hlo)
    · rw [targetSize_eq_levelScale_pow hpos] at hlo
      have hs : 256 ≤ levelScale U r k ℓ := hr256.trans (r_le_levelScale hpos h4r)
      exact (Nat.pow_le_pow_left hs 9).trans hlo
  have h1_le_256 : 1 ≤ 256 ^ 9 := Nat.one_le_pow 9 256 (by decide)
  have h8_le_256 : 8 ≤ 256 ^ 9 := by decide
  { univ := U
    valBound := V
    cap := n
    depth := k
    branchBits := branchBits n U r k
    nFloor := nFloor n U r k
    delta := delta n U r k
    idBits := idBits n U r k
    quotOne := quotUnivOne n U r k
    epsInv := routerEpsInv p_max
    alphaInv := routerAlphaInv q_min
    val_pos := h.val_pos
    two_le_cap := h.two_le_n
    two_le_depth := two_le_treeDepth U r
    quotOne_pos := by
      dsimp only [quotUnivOne]
      set step := branchFactor n U r k 0 * 2 ^ idBits n U r k 1
      have hstep_pos : 1 ≤ step := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
      exact (Nat.le_div_iff_mul_le hstep_pos).mpr (by have := h.two_le_n; omega)
    nFloor_zero := by simp [nFloor, numNodes, cumBranchBits]
    nFloor_pos := fun ℓ hℓ => h1_le_256.trans (hnF8 ℓ hℓ)
    branchBits_pos := fun ℓ hlt => by
      have := hS17 ℓ hlt
      dsimp only [branchBits]
      omega
    delta_lt_nFloor := fun ℓ h1 hℓ => by
      have hy8 := h8_le_256.trans (hnF8 ℓ hℓ)
      have h2d := two_mul_delta_le_nFloor_of_eight_le hy8
      omega
    nFloor_step_le := fun ℓ hlt => by
      have hle : cumBranchBits n U r k ℓ ≤ cumBranchBits n U r k (ℓ + 1) := by
        have := hS17 ℓ hlt; omega
      change branchFactor n U r k ℓ * nFloor n U r k (ℓ + 1) ≤ nFloor n U r k ℓ
      rw [nFloor_succ_eq_div hle]
      exact Nat.mul_div_le _ _
    inner_cap_le := fun ℓ h2 hlt => by
      have h10 := ten_mul_delta_le_branchFactor_mul_delta_succ (hS17 ℓ hlt)
        (h8_le_256.trans (hnF8 (ℓ + 1) hlt))
      have hstep_nf : branchFactor n U r k ℓ * nFloor n U r k (ℓ + 1) ≤ nFloor n U r k ℓ := by
        rw [nFloor_succ_eq_div (by have := hS17 ℓ hlt; omega)]
        exact Nat.mul_div_le _ _
      have hd_next := two_mul_delta_le_nFloor_of_eight_le
        (h8_le_256.trans (hnF8 (ℓ + 1) hlt))
      change branchFactor n U r k ℓ * (nFloor n U r k (ℓ + 1) - delta n U r k (ℓ + 1)) ≤
        nFloor n U r k ℓ - delta n U r k ℓ
      rw [Nat.mul_sub]
      omega
    root_cap_le := by
      have hk2 : 2 ≤ k := two_le_treeDepth U r
      have hstep1 : branchFactor n U r k 1 * nFloor n U r k 2 ≤ nFloor n U r k 1 := by
        rw [nFloor_succ_eq_div (by have := hS17 1 (by omega); omega)]
        exact Nat.mul_div_le _ _
      change branchFactor n U r k 1 * (nFloor n U r k 2 - delta n U r k 2) ≤
        nFloor n U r k 1 + delta n U r k 1
      calc branchFactor n U r k 1 * (nFloor n U r k 2 - delta n U r k 2)
          ≤ branchFactor n U r k 1 * nFloor n U r k 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ nFloor n U r k 1 := hstep1
        _ ≤ nFloor n U r k 1 + delta n U r k 1 := Nat.le_add_right _ _
    idBits_step_le := fun ℓ h1 hlt => by
      have h4 := four_mul_branchBits_add_idBits_succ_le (by have := hS17 ℓ hlt; omega)
        (h1_le_256.trans (hnF8 (ℓ + 1) hlt))
      have := hS17 ℓ hlt
      omega
    nHigh_le_two_pow_idBits := fun ℓ h1 hℓ => by
      have hd := two_mul_delta_le_nFloor_of_eight_le (h8_le_256.trans (hnF8 ℓ hℓ))
      have hy1 : 1 ≤ nFloor n U r k ℓ := h1_le_256.trans (hnF8 ℓ hℓ)
      calc nFloor n U r k ℓ + delta n U r k ℓ
          ≤ 2 * max (nFloor n U r k ℓ) 1 := by rw [max_eq_left hy1]; omega
        _ ≤ 2 ^ Nat.clog 2 (2 * max (nFloor n U r k ℓ) 1) := Nat.le_pow_clog Nat.one_lt_two _
        _ ≤ 2 ^ idBits n U r k ℓ :=
            Nat.pow_le_pow_right Nat.two_pos (by dsimp only [idBits]; omega)
    univ_le_padded := by
      dsimp only [quotUnivOne, branchFactor]
      set step := 2 ^ branchBits n U r k 0 * 2 ^ idBits n U r k 1
      have hstep_pos : 0 < step := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
      have hdiv := Nat.div_add_mod (U + n + step - 1) step
      have hmod := Nat.mod_lt (U + n + step - 1) hstep_pos
      have hn2 := h.two_le_n
      change U + n ≤ step * ((U + n + step - 1) / step)
      omega }

@[simp]
theorem canonicalSchedule_univ {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).univ = U := rfl

@[simp]
theorem canonicalSchedule_valBound {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).valBound = V := rfl

@[simp]
theorem canonicalSchedule_cap {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).cap = n := rfl

@[simp]
theorem canonicalSchedule_depth {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).depth = treeDepth U (redundancyRatio n R) := rfl

theorem canonicalSchedule_cumBranchBits_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    ∀ ℓ ≤ (canonicalSchedule h).depth,
      (canonicalSchedule h).cumBranchBits ℓ =
        cumBranchBits n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := by
  set r := redundancyRatio n R
  set k := treeDepth U r
  have hr256 : minRedundancyRatio ≤ r := h.redundancyRatio_bounds.1
  have h4r : 4 * r ≤ Nat.log 2 U := h.four_mul_redundancyRatio_le_log_univ
  have hn18 : 2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ n := h.two_pow_eighteen_mul_log_univ_pow_le
  have hstep : ∀ j < k, 2 ^ 18 * targetSize n U r k (j + 1) ≤ targetSize n U r k j :=
    fun j hlt => two_pow_eighteen_mul_targetSize_succ_le hr256 h4r hn18 hlt
  have hT_le : ∀ j ≤ k, targetSize n U r k j ≤ n := targetSize_le_of_step hstep
  have hT_pos : ∀ j ≤ k, 1 ≤ targetSize n U r k j := fun j hj =>
    targetSize_pos (by have := h.two_le_n; omega) (by dsimp [minRedundancyRatio] at hr256; omega)
      h4r hj rfl
  intro ℓ hℓ
  induction ℓ with
  | zero => simp [TreeSchedule.cumBranchBits, cumBranchBits]
  | succ j ih =>
    have hj : j < k := Nat.lt_of_succ_le hℓ
    have hS17 := cumBranchBits_add_seventeen_le (hT_pos j hj.le) (hT_pos (j + 1) hj)
      (hT_le j hj.le) (hstep j hj)
    change (canonicalSchedule h).cumBranchBits j + branchBits n U r k j =
      cumBranchBits n U r k (j + 1)
    rw [ih hj.le]
    dsimp only [branchBits]
    omega

theorem canonicalSchedule_numNodes_eq {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hℓ : ℓ ≤ (canonicalSchedule h).depth) :
    (canonicalSchedule h).numNodes ℓ =
      numNodes n U (redundancyRatio n R) (treeDepth U (redundancyRatio n R)) ℓ := by
  dsimp only [TreeSchedule.numNodes, numNodes]
  rw [canonicalSchedule_cumBranchBits_eq h ℓ hℓ]

/-- **`canonicalSchedule` concentration readiness**: across the entire `ValidRegime`,
`canonicalSchedule h` satisfies all six probabilistic concentration conditions in
`TreeSchedule.ConcentrationReady` (`Section 5.4`, `Claim 5.4`, and `Lemma 5.3`). -/
theorem canonicalSchedule_concentrationReady {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).ConcentrationReady := by
  set P := canonicalSchedule h
  set r := redundancyRatio n R
  set k := treeDepth U r
  have hr256 : minRedundancyRatio ≤ r := h.redundancyRatio_bounds.1
  have h4r : 4 * r ≤ Nat.log 2 U := h.four_mul_redundancyRatio_le_log_univ
  have hn18 : 2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ n := h.two_pow_eighteen_mul_log_univ_pow_le
  have hstep : ∀ ℓ < k, 2 ^ 18 * targetSize n U r k (ℓ + 1) ≤ targetSize n U r k ℓ :=
    fun ℓ hlt => two_pow_eighteen_mul_targetSize_succ_le hr256 h4r hn18 hlt
  have hT_le : ∀ ℓ ≤ k, targetSize n U r k ℓ ≤ n := targetSize_le_of_step hstep
  have hT_pos : ∀ ℓ ≤ k, 1 ≤ targetSize n U r k ℓ := fun ℓ hℓ =>
    targetSize_pos (by have := h.two_le_n; omega) (by dsimp [minRedundancyRatio] at hr256; omega)
      h4r hℓ rfl
  have hS17 : ∀ ℓ < k, cumBranchBits n U r k ℓ + 17 ≤ cumBranchBits n U r k (ℓ + 1) :=
    fun ℓ hlt => cumBranchBits_add_seventeen_le (hT_pos ℓ hlt.le) (hT_pos (ℓ + 1) hlt)
      (hT_le ℓ hlt.le) (hstep ℓ hlt)
  have hnF256 : ∀ ℓ ≤ k, 256 ^ 9 ≤ nFloor n U r k ℓ := by
    intro ℓ hℓ
    obtain ⟨hlo, _⟩ := targetSize_le_nFloor_and_lt (hT_pos ℓ hℓ) (hT_le ℓ hℓ)
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · have h0 : targetSize n U r k 0 = n := rfl
      have h1 : 256 ^ 9 ≤ 2 ^ 18 * (Nat.log 2 U) ^ 9 := by
        have hr_val : 256 ≤ Nat.log 2 U := by dsimp [minRedundancyRatio] at hr256; omega
        exact (Nat.pow_le_pow_left hr_val 9).trans (Nat.le_mul_of_pos_left _ (by positivity))
      exact (h1.trans hn18).trans (h0 ▸ hlo)
    · rw [targetSize_eq_levelScale_pow hpos] at hlo
      exact (Nat.pow_le_pow_left (hr256.trans (r_le_levelScale hpos h4r)) 9).trans hlo
  have h8_le : 8 ≤ 256 ^ 9 := by decide
  refine
    { six_le_nFloor := fun ℓ hℓ => (by decide : 6 ≤ 8).trans (h8_le.trans (hnF256 ℓ hℓ))
      two_mul_delta_le_nFloor := fun ℓ _ hℓ =>
        two_mul_delta_le_nFloor_of_eight_le (h8_le.trans (hnF256 ℓ hℓ))
      gap_bound := ?_
      conc_bound := ?_
      window_contained := ?_
      id_collision_bound := fun ℓ h1 hℓ =>
        nHigh_sq_mul_nFloor_sq_le_four_mul_two_pow_idBits h1 (h8_le.trans (hnF256 ℓ hℓ)) }
  · intro ℓ hlt
    have hα : max P.alphaInv 1 = q_min + 1 := by
      change max (max q_min 1 + 1) 1 = q_min + 1
      have := h.q_min_pos
      omega
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · change 2 ^ branchBits n U r k 0 * (2 ^ idBits n U r k 1 * quotUnivOne n U r k) ≤
        (2 ^ idBits n U r k 1 * quotUnivOne n U r k) ^ max P.alphaInv 1
      rw [hα]
      set T0 := 2 ^ idBits n U r k 1 * quotUnivOne n U r k
      have hB0_le : 2 ^ branchBits n U r k 0 ≤ n := by
        have h1_lt : 1 ≤ k := by have := two_le_treeDepth U r; omega
        obtain ⟨hNT1, _⟩ := numNodes_mul_targetSize_bounds (hT_pos 1 h1_lt) (hT_le 1 h1_lt)
        have hN1 : 2 ^ branchBits n U r k 0 = numNodes n U r k 1 := by
          simp [branchBits, numNodes, cumBranchBits]
        rw [hN1]
        exact (Nat.le_mul_of_pos_right _ (hT_pos 1 h1_lt)).trans hNT1
      have hU_le : U ≤ n * T0 := by
        have hpad : U + n ≤ 2 ^ branchBits n U r k 0 * T0 := by
          have := P.univ_le_padded
          dsimp only [P, canonicalSchedule, T0] at this ⊢
          linarith
        exact (Nat.le_add_right U n).trans (hpad.trans (Nat.mul_le_mul_right T0 hB0_le))
      have hn_T0 : n ≤ T0 ^ q_min := by
        have hpow : n ^ q_min * n ≤ n ^ q_min * T0 ^ q_min := by
          calc n ^ q_min * n = n ^ (q_min + 1) := (pow_succ n q_min).symm
            _ ≤ U ^ q_min := h.n_pow_succ_le_univ_pow
            _ ≤ (n * T0) ^ q_min := Nat.pow_le_pow_left hU_le q_min
            _ = n ^ q_min * T0 ^ q_min := Nat.mul_pow n T0 q_min
        exact Nat.le_of_mul_le_mul_left hpow (Nat.pow_pos (by have := h.two_le_n; omega))
      calc 2 ^ branchBits n U r k 0 * T0 ≤ n * T0 := Nat.mul_le_mul_right T0 hB0_le
        _ ≤ T0 ^ q_min * T0 := Nat.mul_le_mul_right T0 hn_T0
        _ = T0 ^ (q_min + 1) := (pow_succ T0 q_min).symm
    · change 2 ^ branchBits n U r k ℓ *
          (if ℓ = 0 then _ else 2 ^ (idBits n U r k ℓ - branchBits n U r k ℓ)) ≤
        (if ℓ = 0 then _ else 2 ^ (idBits n U r k ℓ - branchBits n U r k ℓ)) ^ max P.alphaInv 1
      rw [ite_eq_right hpos.ne', hα]
      have h4 := four_mul_branchBits_add_idBits_succ_le (by have := hS17 ℓ hlt; omega)
        ((Nat.one_le_pow 9 256 (by decide)).trans (hnF256 (ℓ + 1) hlt))
      have hexp : idBits n U r k ℓ ≤
          (idBits n U r k ℓ - branchBits n U r k ℓ) * (q_min + 1) := by
        have hsub_ge : 3 * branchBits n U r k ℓ ≤ idBits n U r k ℓ - branchBits n U r k ℓ := by
          omega
        calc idBits n U r k ℓ
            = branchBits n U r k ℓ + (idBits n U r k ℓ - branchBits n U r k ℓ) := by omega
          _ ≤ 2 * (idBits n U r k ℓ - branchBits n U r k ℓ) := by omega
          _ = (idBits n U r k ℓ - branchBits n U r k ℓ) * 2 := Nat.mul_comm _ _
          _ ≤ (idBits n U r k ℓ - branchBits n U r k ℓ) * (q_min + 1) :=
              Nat.mul_le_mul_left _ (by have := h.q_min_pos; omega)
      calc 2 ^ branchBits n U r k ℓ * 2 ^ (idBits n U r k ℓ - branchBits n U r k ℓ)
          = 2 ^ idBits n U r k ℓ := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ 2 ^ ((idBits n U r k ℓ - branchBits n U r k ℓ) * (q_min + 1)) :=
            Nat.pow_le_pow_right Nat.two_pos hexp
        _ = (2 ^ (idBits n U r k ℓ - branchBits n U r k ℓ)) ^ (q_min + 1) :=
            Nat.pow_mul 2 _ _
  · intro ℓ hlt
    set m := FeistelPerm.childRouterHalfInd (P.nHigh ℓ)
    rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
    · set L := Nat.log 2 n
      have hL_ge4 : 4 ≤ L :=
        (ValidRegime.four_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
      have hpoly : 2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ L :=
        (poly_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
      have hm_le : m ≤ 3 * L + 7 := by
        have hnh0 : P.nHigh 0 = n := rfl
        have hn_le : max n 2 ≤ 2 ^ (L + 1) := by
          rw [max_eq_left h.two_le_n]
          exact (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
        have hcl : Nat.clog 2 (max n 2) ≤ L + 1 := Nat.clog_le_of_le_pow hn_le
        dsimp only [m]
        rw [FeistelPerm.childRouterHalfInd_eq, hnh0]
        omega
      have h150_le : (150 * m) ^ 3 ≤ L ^ 8 := by
        have h150 : 150 * m ≤ 750 * L := by omega
        have h750_L : 750 ≤ L := by
          have : 1 ≤ (max q_min 1 + p_max + 4) ^ 4 := Nat.one_le_pow 4 _ (by omega)
          omega
        have hprod : 150 * m ≤ L ^ 2 := by
          calc 150 * m ≤ 750 * L := h150
            _ ≤ L * L := Nat.mul_le_mul_right L h750_L
            _ = L ^ 2 := (sq L).symm
        calc (150 * m) ^ 3 ≤ (L ^ 2) ^ 3 := Nat.pow_le_pow_left hprod 3
          _ = L ^ 6 := (Nat.pow_mul L 2 3).symm
          _ ≤ L ^ 8 := Nat.pow_le_pow_right (by omega) (by decide)
      obtain ⟨hNT1, _⟩ := numNodes_mul_targetSize_bounds
        (hT_pos 1 (by have := two_le_treeDepth U r; omega))
        (hT_le 1 (by have := two_le_treeDepth U r; omega))
      have hT1_ge : 2 * L ^ 8 ≤ targetSize n U r k 1 := by
        obtain ⟨hlogn, _⟩ := h.log_univ_bounds
        have hT1_eq : targetSize n U r k 1 = (Nat.log 2 U) ^ 9 := by
          rw [targetSize_eq_levelScale_pow le_rfl]
          dsimp only [levelScale]
          rw [ite_eq_left (by have := two_le_treeDepth U r; omega)]
          simp
        rw [hT1_eq]
        calc 2 * L ^ 8 ≤ L * L ^ 8 := Nat.mul_le_mul_right _ (by omega)
          _ = L ^ 9 := (pow_succ' L 8).symm
          _ ≤ (Nat.log 2 U) ^ 9 := Nat.pow_le_pow_left hlogn 9
      have hN1_eq : 2 ^ P.branchBits 0 = numNodes n U r k 1 := by
        change 2 ^ branchBits n U r k 0 = 2 ^ cumBranchBits n U r k 1
        simp [branchBits, cumBranchBits]
      have hmul2 : 2 * (2 ^ P.branchBits 0 * (150 * m) ^ 3) ≤ n := by
        rw [hN1_eq]
        calc 2 * (numNodes n U r k 1 * (150 * m) ^ 3)
            ≤ 2 * (numNodes n U r k 1 * L ^ 8) :=
              Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left _ h150_le)
          _ = numNodes n U r k 1 * (2 * L ^ 8) := by ring
          _ ≤ numNodes n U r k 1 * targetSize n U r k 1 := Nat.mul_le_mul_left _ hT1_ge
          _ ≤ n := hNT1
      have hnl0 : P.nLow 0 = n - 1 := rfl
      rw [hnl0]
      have := h.two_le_n
      omega
    · have hlt_k : ℓ < k := hlt
      have h2 : 2 ≤ ℓ + 1 := by omega
      have hle1 : ℓ + 1 ≤ k := hlt_k
      have hid_le : idBits n U r k ℓ ≤ 148 * levelScale U r k (ℓ + 1) := by
        have := idBits_pred_le_mul_levelScale hr256 h2 hle1 (hT_pos ℓ hlt_k.le) (hT_le ℓ hlt_k.le)
        simpa only [Nat.add_sub_cancel] using this
      set s_next := levelScale U r k (ℓ + 1)
      have hs_ge : 256 ≤ s_next := hr256.trans (r_le_levelScale (by omega) h4r)
      have hy1 : 1 ≤ nFloor n U r k ℓ :=
        (Nat.one_le_pow 9 256 (by decide)).trans (hnF256 ℓ hlt_k.le)
      have hd_cur := two_mul_delta_le_nFloor_of_eight_le (h8_le.trans (hnF256 ℓ hlt_k.le))
      have hnh_le_2y : max (P.nHigh ℓ) 2 ≤ 2 * max (nFloor n U r k ℓ) 1 := by
        have hnh_eq : P.nHigh ℓ = nFloor n U r k ℓ + delta n U r k ℓ := by
          change (if ℓ = 0 then n else nFloor n U r k ℓ + delta n U r k ℓ) = _
          rw [ite_eq_right hpos.ne']
        rw [hnh_eq, max_eq_left hy1]
        omega
      have hcl_le : 4 * Nat.clog 2 (max (P.nHigh ℓ) 2) ≤ idBits n U r k ℓ := by
        have := Nat.clog_mono_right 2 hnh_le_2y
        dsimp only [idBits]
        omega
      have hm_le : m ≤ 112 * s_next := by
        dsimp only [m]
        rw [FeistelPerm.childRouterHalfInd_eq]
        omega
      have hcube_s : 2 * (150 * m) ^ 3 ≤ s_next ^ 9 := by
        have h150 : 150 * m ≤ 16800 * s_next := by omega
        have hcoeff : 2 * 16800 ^ 3 ≤ 256 ^ 6 := by decide
        have hs6 : 256 ^ 6 ≤ s_next ^ 6 := Nat.pow_le_pow_left hs_ge 6
        calc 2 * (150 * m) ^ 3 ≤ 2 * (16800 * s_next) ^ 3 :=
              Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left h150 3)
          _ = (2 * 16800 ^ 3) * s_next ^ 3 := by ring
          _ ≤ s_next ^ 6 * s_next ^ 3 := Nat.mul_le_mul_right _ (hcoeff.trans hs6)
          _ = s_next ^ 9 := (Nat.pow_add s_next 6 3).symm
      obtain ⟨hlo_next, _⟩ := targetSize_le_nFloor_and_lt
        (hT_pos (ℓ + 1) hlt_k) (hT_le (ℓ + 1) hlt_k)
      rw [targetSize_eq_levelScale_pow (by omega)] at hlo_next
      have hstep_nf : 2 ^ P.branchBits ℓ * nFloor n U r k (ℓ + 1) ≤ nFloor n U r k ℓ :=
        P.nFloor_step_le ℓ hlt
      have hnl_eq : P.nLow ℓ = nFloor n U r k ℓ - delta n U r k ℓ := by
        change (if ℓ = 0 then n - 1 else nFloor n U r k ℓ - delta n U r k ℓ) = _
        rw [ite_eq_right hpos.ne']
      rw [hnl_eq]
      have h2mul : 2 * (2 ^ P.branchBits ℓ * (150 * m) ^ 3) ≤ nFloor n U r k ℓ := by
        calc 2 * (2 ^ P.branchBits ℓ * (150 * m) ^ 3)
            = 2 ^ P.branchBits ℓ * (2 * (150 * m) ^ 3) := by ring
          _ ≤ 2 ^ P.branchBits ℓ * s_next ^ 9 := Nat.mul_le_mul_left _ hcube_s
          _ ≤ 2 ^ P.branchBits ℓ * nFloor n U r k (ℓ + 1) := Nat.mul_le_mul_left _ hlo_next
          _ ≤ nFloor n U r k ℓ := hstep_nf
      omega
  · intro ℓ hlt m b_load hm_lo hm_hi hb_lo hb_hi
    have hlt_k : ℓ < k := hlt
    set B := branchFactor n U r k ℓ
    have hB_eq : 2 ^ P.branchBits ℓ = B := rfl
    set x := nFloor n U r k (ℓ + 1)
    set y := nFloor n U r k ℓ
    set d_next := delta n U r k (ℓ + 1)
    have hB_pos : (0 : ℝ) < (B : ℝ) := by dsimp only [B, branchFactor]; positivity
    have hx_ge : 256 ^ 9 ≤ x := hnF256 (ℓ + 1) hlt_k
    have hd_next_ge : 256 ^ 6 ≤ d_next := by
      dsimp only [d_next, delta]
      rw [Nat.le_nthRoot_iff (by decide)]
      calc (256 ^ 6) ^ 3 = (256 ^ 9) ^ 2 := by decide
        _ ≤ x ^ 2 := Nat.pow_le_pow_left hx_ge 2
    have hx_eq : x = y / B := nFloor_succ_eq_div (by have := hS17 ℓ hlt_k; omega)
    have hy_bounds : B * x ≤ y ∧ y < B * (x + 1) := by
      refine ⟨hx_eq ▸ Nat.mul_div_le y B, ?_⟩
      have hdiv := Nat.div_add_mod y B
      have hmod : y % B < B := Nat.mod_lt y (Nat.two_pow_pos _)
      rw [← hx_eq] at hdiv
      nlinarith
    have hm_lo' : (if ℓ = 0 then n - 1 else y - delta n U r k ℓ) ≤ m := hm_lo
    have hm_hi' : m ≤ (if ℓ = 0 then n else y + delta n U r k ℓ) := hm_hi
    have hm_bounds : B * x - (if ℓ = 0 then 1 else delta n U r k ℓ) ≤ m ∧
        m ≤ B * (x + 1) + (if ℓ = 0 then 0 else delta n U r k ℓ) := by
      split_ifs at hm_lo' hm_hi' ⊢ with h0
      · subst h0
        have hy0 : y = n := by simp [y, nFloor, numNodes, cumBranchBits]
        omega
      · omega
    have hd_div_nat : (if ℓ = 0 then 1 else delta n U r k ℓ) ≤ B * d_next / 10 + 1 := by
      split_ifs with h0
      · omega
      · have h10 : 10 * delta n U r k ℓ ≤ B * d_next :=
          ten_mul_delta_le_branchFactor_mul_delta_succ (hS17 ℓ hlt_k) (h8_le.trans hx_ge)
        omega
    set μ : ℝ := (m : ℝ) / (B : ℝ)
    have hB_cast : ((2 : ℝ) ^ P.branchBits ℓ) = (B : ℝ) := by
      rw [← hB_eq]
      exact (Nat.cast_pow 2 _).symm
    rw [hB_cast] at hb_lo hb_hi
    have hμ_def : (m : ℝ) / (B : ℝ) = μ := rfl
    rw [hμ_def] at hb_lo hb_hi
    have hm_pos : 1 ≤ m := (P.nLow_pos hlt.le).trans hm_lo
    have hμ_pos : 0 < μ := by dsimp only [μ]; positivity
    have hμ_hi : μ ≤ (x : ℝ) + (d_next : ℝ) / 10 + 2 := by
      dsimp only [μ]
      rw [div_le_iff₀ hB_pos]
      have h1 : m ≤ B * (x + 1) + (B * d_next / 10 + 1) := by
        have h01 : (if ℓ = 0 then 0 else delta n U r k ℓ) ≤
            (if ℓ = 0 then 1 else delta n U r k ℓ) := by split_ifs <;> omega
        have := hm_bounds.2
        omega
      have hm_hi_r : (m : ℝ) ≤ (B : ℝ) * ((x : ℝ) + 1) +
          ((B * d_next / 10 : ℕ) : ℝ) + 1 := by
        have hcast : ((B * (x + 1) + (B * d_next / 10 + 1) : ℕ) : ℝ) =
            (B : ℝ) * ((x : ℝ) + 1) + ((B * d_next / 10 : ℕ) : ℝ) + 1 := by
          push_cast; ring
        have h1r : (m : ℝ) ≤ ((B * (x + 1) + (B * d_next / 10 + 1) : ℕ) : ℝ) := by
          exact_mod_cast h1
        linarith
      have hdiv_r : ((B * d_next / 10 : ℕ) : ℝ) ≤ (B : ℝ) * (d_next : ℝ) / 10 := by
        rw [le_div_iff₀ (by norm_num)]
        have : (B * d_next / 10) * 10 ≤ B * d_next := Nat.div_mul_le_self _ 10
        exact_mod_cast this
      have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (Nat.two_pow_pos _ : 1 ≤ B)
      linarith
    have hμ_lo : (x : ℝ) - (d_next : ℝ) / 10 - 2 ≤ μ := by
      dsimp only [μ]
      rw [le_div_iff₀ hB_pos]
      have hBx_ge : B * d_next / 10 + 1 ≤ B * x := by
        have hd_le_x : 2 * d_next ≤ x := two_mul_delta_le_nFloor_of_eight_le (h8_le.trans hx_ge)
        have hB1 : 1 ≤ B := Nat.two_pow_pos _
        have : B * d_next / 10 + 1 ≤ B * d_next + 1 :=
          Nat.add_le_add_right (Nat.div_le_self _ 10) 1
        nlinarith
      have h1 : B * x - (B * d_next / 10 + 1) ≤ m := by
        have := hm_bounds.1
        omega
      have hm_lo_r : (B : ℝ) * (x : ℝ) - ((B * d_next / 10 : ℕ) : ℝ) - 1 ≤ (m : ℝ) := by
        have hcast : ((B * x - (B * d_next / 10 + 1) : ℕ) : ℝ) =
            (B : ℝ) * (x : ℝ) - ((B * d_next / 10 : ℕ) : ℝ) - 1 := by
          rw [Nat.cast_sub hBx_ge]; push_cast; ring
        linarith [(by exact_mod_cast h1 : ((B * x - (B * d_next / 10 + 1) : ℕ) : ℝ) ≤ (m : ℝ))]
      have hdiv_r : ((B * d_next / 10 : ℕ) : ℝ) ≤ (B : ℝ) * (d_next : ℝ) / 10 := by
        rw [le_div_iff₀ (by norm_num)]
        have : (B * d_next / 10) * 10 ≤ B * d_next := Nat.div_mul_le_self _ 10
        exact_mod_cast this
      have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast (Nat.two_pow_pos _ : 1 ≤ B)
      linarith
    have hμ_le_2x : μ ≤ 2 * (x : ℝ) := by
      have hd_r : (2 : ℝ) * (d_next : ℝ) ≤ (x : ℝ) := by
        exact_mod_cast two_mul_delta_le_nFloor_of_eight_le (h8_le.trans hx_ge)
      have hx_r : (100 : ℝ) ≤ (x : ℝ) := by
        have : 100 ≤ 256 ^ 9 := by decide
        exact_mod_cast this.trans hx_ge
      linarith
    have hdev_le : ((1 : ℝ) / 5) * μ ^ ((2 : ℝ) / 3) ≤ ((2 : ℝ) / 5) * ((d_next : ℝ) + 1) := by
      set u : ℝ := μ ^ ((1 : ℝ) / 3)
      have hu_pos : 0 < u := Real.rpow_pos_of_pos hμ_pos _
      have hu3 : u ^ 3 = μ := by
        dsimp only [u]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hμ_pos.le]
        norm_num
      have hu2 : μ ^ ((2 : ℝ) / 3) = u ^ 2 := by
        dsimp only [u]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hμ_pos.le]
        norm_num
      have hx2_lt : (x : ℝ) ^ 2 ≤ ((d_next : ℝ) + 1) ^ 3 := by
        have hlt_nat : x ^ 2 < (d_next + 1) ^ 3 := Nat.lt_pow_nthRoot_add_one (by decide) (x ^ 2)
        exact_mod_cast hlt_nat.le
      have hcube : (u ^ 2) ^ 3 ≤ (2 * ((d_next : ℝ) + 1)) ^ 3 := by
        calc (u ^ 2) ^ 3 = (u ^ 3) ^ 2 := by ring
          _ = μ ^ 2 := by rw [hu3]
          _ ≤ (2 * (x : ℝ)) ^ 2 := pow_le_pow_left₀ hμ_pos.le hμ_le_2x 2
          _ = 4 * (x : ℝ) ^ 2 := by ring
          _ ≤ 8 * ((d_next : ℝ) + 1) ^ 3 := by nlinarith [sq_nonneg (x : ℝ)]
          _ = (2 * ((d_next : ℝ) + 1)) ^ 3 := by ring
      have hu2_le : u ^ 2 ≤ 2 * ((d_next : ℝ) + 1) :=
        (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mp hcube
      rw [hu2]
      linarith
    have hd_big : (10 : ℝ) ≤ (d_next : ℝ) := by
      have : 10 ≤ 256 ^ 6 := by decide
      exact_mod_cast this.trans hd_next_ge
    have hnl_next : P.nLow (ℓ + 1) = x - d_next := by
      change (if ℓ + 1 = 0 then n - 1 else x - d_next) = x - d_next
      rw [ite_eq_right (by omega)]
    have hnh_next : P.nHigh (ℓ + 1) = x + d_next := by
      change (if ℓ + 1 = 0 then n else x + d_next) = x + d_next
      rw [ite_eq_right (by omega)]
    have hd_le_x : d_next ≤ x := by
      have := two_mul_delta_le_nFloor_of_eight_le (h8_le.trans hx_ge)
      omega
    rw [hnl_next, hnh_next]
    refine ⟨?_, ?_⟩
    · have hgt : ((x - d_next : ℕ) : ℝ) < ((b_load + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hd_le_x, Nat.cast_add, Nat.cast_one]
        linarith
      have hlt_nat : x - d_next < b_load + 1 := Nat.cast_lt.mp hgt
      omega
    · have hlt : (b_load : ℝ) < ((x + d_next + 1 : ℕ) : ℝ) := by
        push_cast
        linarith
      have hlt_nat : b_load < x + d_next + 1 := Nat.cast_lt.mp hlt
      omega

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
