/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SubconstantRedundancy.Canonical
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Padding Entropy and Regime-Switched Router Seed Bit Bounds

This module proves the sentinel-padding entropy bound `infoBits_paddedUniv_le`, the
`SuccinctBucket` metadata bound `succinctTableMetaBits_le`, and the uniform quadratic seed bound
`routerSeedBits_sq_le_nFloor` across both the `DoubleTabulation` (`nLow ℓ ≥ childRouterThreshold`)
and small-node `trinomialPolyHash` (`nLow ℓ < childRouterThreshold`) child-router regimes of
[LiLiangYuZhou2024] (`arXiv:2310.20536v1`, Sections 5.1–5.2 and 5.4, PDF pp. 25–30 and 32–33 /
printed pp. 24–29 and 31–32).

## Main results

* `infoBits_paddedUniv_le`: sentinel and alignment padding from `U` to `paddedUniv` increases
  `infoBits` by at most `2 * effRedundancy n R + 1` bits.
* `succinctTableMetaBits_le`: linear-in-`(m * I)` upper bound on `SuccinctBucket` metadata bits.
* `routerSeedBits_sq_le_nFloor`: `(routerSeedBits ℓ) ^ 2 ≤ nFloor ℓ` at every level `0 ≤ ℓ < depth`
  across both child-router regimes.

## References

* [T. Li, J. Liang, H. Yu, and R. Zhou,
  *Dynamic Dictionary with Subconstant Wasted Bits per Key*][LiLiangYuZhou2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.SubconstantRedundancy

open Cslib.DataStructure.Dictionary
open Finset

/-! ## Section 1: Inverse-redundancy scaling and sentinel-padding entropy bound -/

theorem n_le_two_mul_effRedundancy_mul_ratio {n R : ℕ}
    (hR : 1 ≤ R) (hr1 : 1 ≤ redundancyRatio n R) :
    n ≤ 2 * effRedundancy n R * redundancyRatio n R := by
  set Re := effRedundancy n R
  set r := redundancyRatio n R
  have hRe1 : 1 ≤ Re := effRedundancy_pos hR n
  have hr_eq : r = n / Re := by
    dsimp only [r, redundancyRatio]
    rw [max_eq_left hRe1]
  have hdiv := Nat.div_add_mod n Re
  have hmod := Nat.mod_lt n hRe1
  rw [← hr_eq] at hdiv
  nlinarith

theorem le_two_mul_effRedundancy_of_mul_ratio_le {n R Q C : ℕ}
    (hR : 1 ≤ R) (hr1 : 1 ≤ redundancyRatio n R)
    (hQ : Q * redundancyRatio n R ≤ C * n) :
    Q ≤ 2 * C * effRedundancy n R := by
  have hn := n_le_two_mul_effRedundancy_mul_ratio hR hr1
  have hmul : Q * redundancyRatio n R ≤ (2 * C * effRedundancy n R) * redundancyRatio n R := by
    calc Q * redundancyRatio n R ≤ C * n := hQ
      _ ≤ C * (2 * effRedundancy n R * redundancyRatio n R) := Nat.mul_le_mul_left C hn
      _ = (2 * C * effRedundancy n R) * redundancyRatio n R := by ring
  exact Nat.le_of_mul_le_mul_right hmul hr1

private theorem choose_add_le_choose_mul_pow_two {U E n Re : ℕ}
    (hnU : 2 * n ≤ U) (hnE : n * E ≤ (U + 1 - n) * Re) :
    (U + E).choose n ≤ U.choose n * 2 ^ (2 * Re) := by
  set W := U + 1 - n
  have hW_pos : 1 ≤ W := by dsimp only [W]; omega
  have hWr_pos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW_pos
  have hch := Nat.pow_mul_choose_le_choose_mul_pow (d := U) (m := U + E) (s := n)
    (Nat.le_add_right U E)
  have hWE : U + E + 1 - n = W + E := by dsimp only [W]; omega
  rw [hWE] at hch
  set δ : ℝ := (E : ℝ) / (W : ℝ)
  have h1δ : ((W + E : ℕ) : ℝ) = (W : ℝ) * (1 + δ) := by
    dsimp only [δ]
    push_cast
    field_simp
  have hexp_le : (1 + δ) ^ n ≤ (2 ^ (2 * Re) : ℝ) := by
    have h1 : 1 + δ ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
    have hnδ : (n : ℝ) * δ ≤ (Re : ℝ) := by
      dsimp only [δ]
      rw [mul_div_assoc', div_le_iff₀ hWr_pos, mul_comm (Re : ℝ)]
      exact_mod_cast hnE
    have hexp1 : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
    calc (1 + δ) ^ n ≤ (Real.exp δ) ^ n := pow_le_pow_left₀ (by dsimp only [δ]; positivity) h1 n
      _ = Real.exp ((n : ℝ) * δ) := (Real.exp_nat_mul δ n).symm
      _ ≤ Real.exp (Re : ℝ) := Real.exp_le_exp.mpr hnδ
      _ = (Real.exp 1) ^ Re := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ (4 : ℝ) ^ Re := pow_le_pow_left₀ (Real.exp_nonneg 1) hexp1 Re
      _ = (2 ^ (2 * Re) : ℝ) := by
          have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          rw [h4, ← pow_mul]
  have hch_r : (W : ℝ) ^ n * ((U + E).choose n : ℝ) ≤
      (W : ℝ) ^ n * ((U.choose n * 2 ^ (2 * Re) : ℕ) : ℝ) := by
    have h0 : (W : ℝ) ^ n * ((U + E).choose n : ℝ) ≤
        (U.choose n : ℝ) * ((W + E : ℕ) : ℝ) ^ n := by exact_mod_cast hch
    calc (W : ℝ) ^ n * ((U + E).choose n : ℝ)
        ≤ (U.choose n : ℝ) * ((W : ℝ) * (1 + δ)) ^ n := by rwa [h1δ] at h0
      _ = (W : ℝ) ^ n * ((U.choose n : ℝ) * (1 + δ) ^ n) := by rw [mul_pow]; ring
      _ ≤ (W : ℝ) ^ n * ((U.choose n : ℝ) * (2 ^ (2 * Re) : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp_le (Nat.cast_nonneg _)) (by positivity)
      _ = (W : ℝ) ^ n * ((U.choose n * 2 ^ (2 * Re) : ℕ) : ℝ) := by push_cast; ring
  have hres : ((U + E).choose n : ℝ) ≤ ((U.choose n * 2 ^ (2 * Re) : ℕ) : ℝ) :=
    le_of_mul_le_mul_left hch_r (pow_pos hWr_pos n)
  exact_mod_cast hres

/-- Sentinel and top-level alignment padding from `U` to `(canonicalSchedule h).paddedUniv`
increases `infoBits` by at most `2 * effRedundancy n R + 1` bits across `ValidRegime`. -/
theorem infoBits_paddedUniv_le {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    infoBits (canonicalSchedule h).paddedUniv V n ≤
      infoBits U V n + 2 * effRedundancy n R + 1 := by
  set P := canonicalSchedule h
  set r := redundancyRatio n R
  set k := treeDepth U r
  set Re := effRedundancy n R
  obtain ⟨hr256, _, hr10⟩ := h.redundancyRatio_bounds
  have h4r : 4 * r ≤ Nat.log 2 U := h.four_mul_redundancyRatio_le_log_univ
  have hn18 : 2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ n := h.two_pow_eighteen_mul_log_univ_pow_le
  have h1_lt : 1 ≤ k := by have := two_le_treeDepth U r; omega
  have hT1_pos : 1 ≤ targetSize n U r k 1 :=
    targetSize_pos (by have := h.two_le_n; omega) (by dsimp [minRedundancyRatio] at hr256; omega)
      h4r h1_lt rfl
  have hT1_le : targetSize n U r k 1 ≤ n := by
    rw [targetSize_eq_levelScale_pow le_rfl]
    dsimp only [levelScale]
    rw [ite_eq_left (by have := two_le_treeDepth U r; omega)]
    simpa only [Nat.iterLog_succ, Nat.iterLog_zero] using
      (Nat.le_mul_of_pos_left _ (by positivity : 0 < 2 ^ 18)).trans hn18
  obtain ⟨hNT1, hhi1⟩ := numNodes_mul_targetSize_bounds hT1_pos hT1_le
  obtain ⟨_, hnF1_lt⟩ := targetSize_le_nFloor_and_lt hT1_pos hT1_le
  set s1 := Nat.log 2 U
  have hT1_eq : targetSize n U r k 1 = s1 ^ 9 := by
    rw [targetSize_eq_levelScale_pow le_rfl]
    dsimp only [levelScale]
    rw [ite_eq_left (by have := two_le_treeDepth U r; omega)]
    rfl
  have hs1_ge : 256 ≤ s1 := by dsimp [minRedundancyRatio] at hr256; omega
  have hid1_pow : 2 ^ idBits n U r k 1 ≤ 4096 * s1 ^ 36 := by
    have hy1 : 1 ≤ nFloor n U r k 1 := hT1_pos.trans (targetSize_le_nFloor_and_lt hT1_pos hT1_le).1
    have hcl : 2 ^ Nat.clog 2 (2 * max (nFloor n U r k 1) 1) ≤ 8 * s1 ^ 9 := by
      rw [max_eq_left hy1]
      calc 2 ^ Nat.clog 2 (2 * nFloor n U r k 1)
          ≤ 2 * (2 * nFloor n U r k 1) := Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
        _ ≤ 4 * (2 * targetSize n U r k 1) := by omega
        _ = 8 * s1 ^ 9 := by rw [hT1_eq]; ring
    dsimp only [idBits]
    calc 2 ^ (4 * Nat.clog 2 (2 * max (nFloor n U r k 1) 1))
        = (2 ^ Nat.clog 2 (2 * max (nFloor n U r k 1) 1)) ^ 4 := by
          rw [Nat.mul_comm 4, Nat.pow_mul]
      _ ≤ (8 * s1 ^ 9) ^ 4 := Nat.pow_le_pow_left hcl 4
      _ = 4096 * s1 ^ 36 := by ring
  set step := branchFactor n U r k 0 * 2 ^ idBits n U r k 1
  have hstep_le : step ≤ 4096 * n * s1 ^ 27 := by
    have hB0 : branchFactor n U r k 0 = numNodes n U r k 1 := by
      simp [branchFactor, branchBits, numNodes, cumBranchBits]
    calc step = numNodes n U r k 1 * 2 ^ idBits n U r k 1 := by dsimp only [step]; rw [hB0]
      _ ≤ numNodes n U r k 1 * (4096 * s1 ^ 36) := Nat.mul_le_mul_left _ hid1_pow
      _ = (numNodes n U r k 1 * s1 ^ 9) * (4096 * s1 ^ 27) := by ring
      _ ≤ n * (4096 * s1 ^ 27) := Nat.mul_le_mul_right _ (hT1_eq ▸ hNT1)
      _ = 4096 * n * s1 ^ 27 := by ring
  have hUpad_le : P.paddedUniv ≤ U + n + step := by
    change branchFactor n U r k 0 * 2 ^ idBits n U r k 1 * quotUnivOne n U r k ≤ U + n + step
    dsimp only [quotUnivOne]
    have hmul : ((U + n + step - 1) / step) * step ≤ U + n + step - 1 :=
      Nat.div_mul_le_self _ step
    rw [Nat.mul_comm] at hmul
    change step * ((U + n + step - 1) / step) ≤ U + n + step
    have := h.two_le_n
    omega
  have hUpad_ge : U ≤ P.paddedUniv := by
    have hp := P.univ_le_padded
    change U + n ≤ P.paddedUniv at hp
    omega
  set E := P.paddedUniv - U
  have hUpad_eq : P.paddedUniv = U + E := (Nat.add_sub_of_le hUpad_ge).symm
  have hE_le : E ≤ 4097 * n * s1 ^ 27 := by
    have hs1_pos : 1 ≤ s1 ^ 27 := Nat.one_le_pow 27 s1 (by omega)
    have hn_le : n ≤ n * s1 ^ 27 := Nat.le_mul_of_pos_right n hs1_pos
    have : E ≤ n + step := by omega
    nlinarith
  set L := Nat.log 2 n
  have hr_le_L : r ≤ L :=
    (Nat.le_self_pow (by decide : 10 ≠ 0) r).trans hr10
  have hn_Re : n ≤ 2 * L * Re := by
    have hr1 : 1 ≤ r := by dsimp [minRedundancyRatio] at hr256; omega
    calc n ≤ 2 * Re * r := n_le_two_mul_effRedundancy_mul_ratio h.redundancy_pos hr1
      _ ≤ 2 * Re * L := Nat.mul_le_mul_left _ hr_le_L
      _ = 2 * L * Re := by ring
  have hgap_U : 16388 * n * s1 ^ 27 * L ≤ U := by
    have hpoly : 2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ L :=
      (poly_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
    have hbase_p : max q_min 1 + p_max + 4 ≤ (max q_min 1 + p_max + 4) ^ 4 :=
      Nat.le_self_pow (by decide) _
    obtain ⟨_, hs1_le⟩ := h.log_univ_bounds
    have hprod_L : 16388 * s1 ^ 27 * L ≤ L ^ 56 := by
      have hs1_L2 : s1 ≤ L ^ 2 := by
        have hp2 : 2 * (p_max + 1) ≤ L := by omega
        calc s1 ≤ 2 * (p_max + 1) * L := hs1_le
          _ ≤ L * L := Nat.mul_le_mul_right L hp2
          _ = L ^ 2 := (sq L).symm
      have h16 : 16388 ≤ L := by omega
      calc 16388 * s1 ^ 27 * L ≤ L * (L ^ 2) ^ 27 * L :=
            Nat.mul_le_mul_right L (Nat.mul_le_mul h16 (Nat.pow_le_pow_left hs1_L2 27))
        _ = L ^ 56 := by rw [← Nat.pow_mul]; ring
    set D := 56 * q_min
    have hD_pos : 1 ≤ D := by have := h.q_min_pos; dsimp only [D]; omega
    have h4D2 : 4 * D ^ 2 ≤ L := by
      dsimp only [D]
      have hq : q_min ≤ max q_min 1 + p_max + 4 := by omega
      have hq2 : q_min ^ 2 ≤ (max q_min 1 + p_max + 4) ^ 2 := Nat.pow_le_pow_left hq 2
      have h2_4 : (max q_min 1 + p_max + 4) ^ 2 ≤ (max q_min 1 + p_max + 4) ^ 4 :=
        Nat.pow_le_pow_right (by omega) (by decide)
      have : 4 * (56 * q_min) ^ 2 = 12544 * q_min ^ 2 := by ring
      omega
    have hLD : L ^ D ≤ n :=
      (Nat.pow_le_two_pow hD_pos h4D2).trans
        (Nat.pow_log_le_self 2 (by have := h.two_le_n; omega))
    have hpow_q : (16388 * n * s1 ^ 27 * L) ^ q_min ≤ U ^ q_min := by
      calc (16388 * n * s1 ^ 27 * L) ^ q_min
          = n ^ q_min * (16388 * s1 ^ 27 * L) ^ q_min := by ring
        _ ≤ n ^ q_min * (L ^ 56) ^ q_min :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hprod_L q_min)
        _ = n ^ q_min * L ^ D := by rw [← Nat.pow_mul]
        _ ≤ n ^ q_min * n := Nat.mul_le_mul_left _ hLD
        _ = n ^ (q_min + 1) := (pow_succ n q_min).symm
        _ ≤ U ^ q_min := h.n_pow_succ_le_univ_pow
    exact (Nat.pow_le_pow_iff_left (by have := h.q_min_pos; omega)).mp hpow_q
  have hnE : n * E ≤ (U + 1 - n) * Re := by
    have h2nU := h.two_mul_n_le_univ
    have hU2 : U ≤ 2 * (U + 1 - n) := by omega
    have h2_mul : 2 * (n * E) ≤ 2 * ((U + 1 - n) * Re) := by
      calc 2 * (n * E) ≤ 2 * ((2 * L * Re) * (4097 * n * s1 ^ 27)) :=
            Nat.mul_le_mul_left 2 (Nat.mul_le_mul hn_Re hE_le)
        _ ≤ (16388 * n * s1 ^ 27 * L) * Re := by nlinarith
        _ ≤ U * Re := Nat.mul_le_mul_right Re hgap_U
        _ ≤ (2 * (U + 1 - n)) * Re := Nat.mul_le_mul_right Re hU2
        _ = 2 * ((U + 1 - n) * Re) := by ring
    exact Nat.le_of_mul_le_mul_left h2_mul (by decide)
  have hch := choose_add_le_choose_mul_pow_two h.two_mul_n_le_univ hnE
  rw [← hUpad_eq] at hch
  have hXV_pos : 1 ≤ U.choose n * V ^ n :=
    Nat.mul_pos (Nat.choose_pos (by have := h.two_mul_n_le_univ; omega)) (Nat.pow_pos h.val_pos)
  refine Nat.clog_le_of_le_pow ?_
  calc P.paddedUniv.choose n * V ^ n
      ≤ (U.choose n * 2 ^ (2 * Re)) * V ^ n := Nat.mul_le_mul_right _ hch
    _ = (U.choose n * V ^ n) * 2 ^ (2 * Re) := by ring
    _ ≤ (2 ^ infoBits U V n) * 2 ^ (2 * Re) :=
        Nat.mul_le_mul_right _ (Nat.le_pow_clog Nat.one_lt_two _)
    _ ≤ 2 ^ (infoBits U V n + 2 * Re + 1) := by
        rw [← Nat.pow_add]
        exact Nat.pow_le_pow_right Nat.two_pos (by omega)

/-! ## Section 2: `SuccinctBucket` metadata and regime-switched `routerSeedBits` bounds -/

theorem succinctTableMetaBits_le {I m : ℕ} (hm : m ≤ 2 ^ I) :
    succinctTableMetaBits I m ≤ 75 * m * (I + 2) + 9 * (I + 2) := by
  have hq : FeistelQuotient.quotientBits (2 ^ I) m ≤ I := by
    calc FeistelQuotient.quotientBits (2 ^ I) m
        ≤ FeistelQuotient.keyBits (2 ^ I) := by
          have := FeistelQuotient.quotientBits_add_bucketBits hm
          omega
      _ = I := by simp [FeistelQuotient.keyBits]
  have hll : Dynamic.logLogFactor m ≤ I + 2 := by
    dsimp only [Dynamic.logLogFactor]
    have hm4 : max m 4 ≤ 2 ^ (I + 2) := by
      refine max_le (hm.trans (Nat.pow_le_pow_right Nat.two_pos (by omega))) ?_
      exact (show 4 = 2 ^ 2 by decide) ▸ Nat.pow_le_pow_right Nat.two_pos (by omega)
    have hcl1 : Nat.clog 2 (max m 4) ≤ I + 2 := Nat.clog_le_of_le_pow hm4
    exact (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le).trans hcl1
  have hloc := (SuccinctBucket.localMetaLen_mul_effBucketPosBits_le m).trans
    (Nat.mul_le_mul_left (54 * m) hll)
  have hglob := (SuccinctBucket.globalMetaLen_mul_globalPtrBits_le m).trans
    (Nat.mul_le_mul_left (20 * m) hll)
  have htri : 3 * Cslib.Probability.trinomialDeg
      (2 ^ FeistelQuotient.quotientBits (2 ^ I) m) (SuccinctBucket.totalMicroBits m) ≤
      9 * (I + 2) := by
    have htd := Cslib.Probability.trinomialDeg_le_three_mul
      (2 ^ FeistelQuotient.quotientBits (2 ^ I) m) (SuccinctBucket.totalMicroBits m)
    have h1 : Nat.clog 2 (max (2 ^ FeistelQuotient.quotientBits (2 ^ I) m) 2) ≤ I + 2 := by
      refine Nat.clog_le_of_le_pow (max_le ?_ ?_)
      · exact Nat.pow_le_pow_right Nat.two_pos (by omega)
      · exact (show 2 = 2 ^ 1 by decide) ▸ Nat.pow_le_pow_right Nat.two_pos (by omega)
    have h2 : max (SuccinctBucket.totalMicroBits m) 1 ≤ I + 2 := by
      have htmb : SuccinctBucket.totalMicroBits m ≤ I :=
        SuccinctBucket.totalMicroBits_le_of_le_pow hm le_rfl
      omega
    have hmax : max (Nat.clog 2 (max (2 ^ FeistelQuotient.quotientBits (2 ^ I) m) 2))
        (max (SuccinctBucket.totalMicroBits m) 1) ≤ I + 2 := max_le h1 h2
    omega
  have hmq : m * FeistelQuotient.quotientBits (2 ^ I) m ≤ m * (I + 2) :=
    Nat.mul_le_mul_left m (by omega)
  dsimp only [succinctTableMetaBits]
  nlinarith

private theorem mul_spaceConst_le_threshold (ε_inv α_inv : ℕ) :
    256 * FeistelPerm.childRouterSpaceConst ε_inv α_inv ≤
      FeistelPerm.childRouterThreshold ε_inv α_inv := by
  rw [FeistelPerm.childRouterSpaceConst_eq, FeistelPerm.childRouterThreshold_eq]
  set E := max ε_inv 1
  set c := FeistelPerm.childRouterChars ε_inv
  set A := c * max α_inv 1
  set q := FeistelPerm.childRouterRep ε_inv α_inv
  set d := 2 * q * c
  have hE1 : 1 ≤ E := le_max_right _ _
  have hc_eq : c = 2 * E := FeistelPerm.childRouterChars_eq ε_inv
  have hc2 : 2 ≤ c := by omega
  have hA2 : 2 ≤ A := by
    dsimp only [A]
    exact (show 2 = 2 * 1 by decide) ▸ Nat.mul_le_mul hc2 (le_max_right α_inv 1)
  have hq_eq : q = A + 2 := FeistelPerm.childRouterRep_eq ε_inv α_inv
  have hd_ge : 16 ≤ d := by dsimp only [d]; nlinarith
  have hd_pow : d ^ E ≤ 2 ^ (d * E) := by
    calc d ^ E ≤ (2 ^ d) ^ E := Nat.pow_le_pow_left Nat.lt_two_pow_self.le E
      _ = 2 ^ (d * E) := (Nat.pow_mul 2 d E).symm
  have hexp_le : 8 + d * E + (2 * c ^ 2 + c + 2) ≤
      A * max (4 * c * d ^ q * (c * (6 * A + 8)) ^ (2 * c * q)) (4 * (2 * c * q + 1) ^ 2) := by
    have hD_eq : 2 * c * q = d := by dsimp only [d]; ring
    rw [hD_eq]
    have h1 : 8 + d * E + (2 * c ^ 2 + c + 2) ≤ 4 * (d + 1) ^ 2 := by
      have hEc : E ≤ c := by omega
      have hcd : c ≤ d := by dsimp only [d]; nlinarith
      nlinarith
    calc 8 + d * E + (2 * c ^ 2 + c + 2)
        ≤ 4 * (d + 1) ^ 2 := h1
      _ ≤ max (4 * c * d ^ q * (c * (6 * A + 8)) ^ d) (4 * (d + 1) ^ 2) := le_max_right _ _
      _ ≤ A * max (4 * c * d ^ q * (c * (6 * A + 8)) ^ d) (4 * (d + 1) ^ 2) :=
          Nat.le_mul_of_pos_left _ (by omega)
  calc 256 * (d ^ E * 2 ^ (2 * c ^ 2 + c + 2))
      ≤ 2 ^ 8 * (2 ^ (d * E) * 2 ^ (2 * c ^ 2 + c + 2)) := by
        have h256 : (256 : ℕ) = 2 ^ 8 := by decide
        rw [h256]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hd_pow)
    _ = 2 ^ (8 + d * E + (2 * c ^ 2 + c + 2)) := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_right Nat.two_pos hexp_le

private theorem paddedUniv_le_two_mul_pow {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).paddedUniv ≤ 2 * n ^ (p_max + 2) := by
  set P := canonicalSchedule h
  set r := redundancyRatio n R
  set k := treeDepth U r
  have hr256 : minRedundancyRatio ≤ r := h.redundancyRatio_bounds.1
  have h4r : 4 * r ≤ Nat.log 2 U := h.four_mul_redundancyRatio_le_log_univ
  have hn18 : 2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ n := h.two_pow_eighteen_mul_log_univ_pow_le
  have h1_lt : 1 ≤ k := by have := two_le_treeDepth U r; omega
  have hT1_pos : 1 ≤ targetSize n U r k 1 :=
    targetSize_pos (by have := h.two_le_n; omega) (by dsimp [minRedundancyRatio] at hr256; omega)
      h4r h1_lt rfl
  have hT1_le : targetSize n U r k 1 ≤ n := by
    rw [targetSize_eq_levelScale_pow le_rfl]
    dsimp only [levelScale]
    rw [ite_eq_left (by have := two_le_treeDepth U r; omega)]
    simpa only [Nat.iterLog_succ, Nat.iterLog_zero] using
      (Nat.le_mul_of_pos_left _ (by positivity : 0 < 2 ^ 18)).trans hn18
  obtain ⟨hNT1, _⟩ := numNodes_mul_targetSize_bounds hT1_pos hT1_le
  obtain ⟨hlo1, hnF1_lt⟩ := targetSize_le_nFloor_and_lt hT1_pos hT1_le
  set s1 := Nat.log 2 U
  have hT1_eq : targetSize n U r k 1 = s1 ^ 9 := by
    rw [targetSize_eq_levelScale_pow le_rfl]
    dsimp only [levelScale]
    rw [ite_eq_left (by have := two_le_treeDepth U r; omega)]
    rfl
  have hid1_pow : 2 ^ idBits n U r k 1 ≤ 4096 * s1 ^ 36 := by
    have hy1 : 1 ≤ nFloor n U r k 1 := hT1_pos.trans hlo1
    have hcl : 2 ^ Nat.clog 2 (2 * max (nFloor n U r k 1) 1) ≤ 8 * s1 ^ 9 := by
      rw [max_eq_left hy1]
      calc 2 ^ Nat.clog 2 (2 * nFloor n U r k 1)
          ≤ 2 * (2 * nFloor n U r k 1) := Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
        _ ≤ 4 * (2 * targetSize n U r k 1) := by omega
        _ = 8 * s1 ^ 9 := by rw [hT1_eq]; ring
    dsimp only [idBits]
    calc 2 ^ (4 * Nat.clog 2 (2 * max (nFloor n U r k 1) 1))
        = (2 ^ Nat.clog 2 (2 * max (nFloor n U r k 1) 1)) ^ 4 := by
          rw [Nat.mul_comm 4, Nat.pow_mul]
      _ ≤ (8 * s1 ^ 9) ^ 4 := Nat.pow_le_pow_left hcl 4
      _ = 4096 * s1 ^ 36 := by ring
  set step := branchFactor n U r k 0 * 2 ^ idBits n U r k 1
  have hstep_le : step ≤ 4096 * n * s1 ^ 27 := by
    have hB0 : branchFactor n U r k 0 = numNodes n U r k 1 := by
      simp [branchFactor, branchBits, numNodes, cumBranchBits]
    calc step = numNodes n U r k 1 * 2 ^ idBits n U r k 1 := by dsimp only [step]; rw [hB0]
      _ ≤ numNodes n U r k 1 * (4096 * s1 ^ 36) := Nat.mul_le_mul_left _ hid1_pow
      _ = (numNodes n U r k 1 * s1 ^ 9) * (4096 * s1 ^ 27) := by ring
      _ ≤ n * (4096 * s1 ^ 27) := Nat.mul_le_mul_right _ (hT1_eq ▸ hNT1)
      _ = 4096 * n * s1 ^ 27 := by ring
  have hUpad_le : P.paddedUniv ≤ U + n + step := by
    change branchFactor n U r k 0 * 2 ^ idBits n U r k 1 * quotUnivOne n U r k ≤ _
    dsimp only [quotUnivOne]
    have hmul := Nat.div_mul_le_self (U + n + step - 1) step
    rw [Nat.mul_comm] at hmul
    change step * ((U + n + step - 1) / step) ≤ U + n + step
    have := h.two_le_n; omega
  set L := Nat.log 2 n
  have hpoly : 2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ L :=
    (poly_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
  have hbase_p : max q_min 1 + p_max + 4 ≤ (max q_min 1 + p_max + 4) ^ 4 :=
    Nat.le_self_pow (by decide) _
  obtain ⟨_, hs1_le⟩ := h.log_univ_bounds
  have hs1_L2 : s1 ≤ L ^ 2 := by
    have hp2 : 2 * (p_max + 1) ≤ L := by omega
    calc s1 ≤ 2 * (p_max + 1) * L := hs1_le
      _ ≤ L * L := Nat.mul_le_mul_right L hp2
      _ = L ^ 2 := (sq L).symm
  have h4097 : 4097 * s1 ^ 27 ≤ L ^ 55 := by
    have h4 : 4097 ≤ L := by omega
    calc 4097 * s1 ^ 27 ≤ L * (L ^ 2) ^ 27 :=
          Nat.mul_le_mul h4 (Nat.pow_le_pow_left hs1_L2 27)
      _ = L ^ 55 := by rw [← Nat.pow_mul]; ring
  have hL55 : L ^ 55 ≤ n :=
    (Nat.pow_le_two_pow (by decide) (by omega)).trans
      (Nat.pow_log_le_self 2 (by have := h.two_le_n; omega))
  have hs1_pos : 1 ≤ s1 ^ 27 :=
    Nat.one_le_pow 27 s1 (by dsimp [minRedundancyRatio] at hr256; omega)
  have hstep_n2 : n + step ≤ n ^ (p_max + 2) := by
    calc n + step ≤ n * s1 ^ 27 + 4096 * n * s1 ^ 27 :=
          Nat.add_le_add (Nat.le_mul_of_pos_right n hs1_pos) hstep_le
      _ = n * (4097 * s1 ^ 27) := by ring
      _ ≤ n * L ^ 55 := Nat.mul_le_mul_left n h4097
      _ ≤ n * n := Nat.mul_le_mul_left n hL55
      _ = n ^ 2 := (sq n).symm
      _ ≤ n ^ (p_max + 2) := Nat.pow_le_pow_right (by have := h.two_le_n; omega) (by omega)
  have hU_pow : U ≤ n ^ (p_max + 2) :=
    h.univ_le_pow.trans (Nat.pow_le_pow_right (by have := h.two_le_n; omega) (by omega))
  calc P.paddedUniv ≤ U + (n + step) := by omega
    _ ≤ n ^ (p_max + 2) + n ^ (p_max + 2) := Nat.add_le_add hU_pow hstep_n2
    _ = 2 * n ^ (p_max + 2) := (two_mul _).symm

theorem paddedUniv_le_two_pow_mul_log {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) :
    (canonicalSchedule h).paddedUniv ≤ 2 ^ (2 * (p_max + 2) * Nat.log 2 n) := by
  set L := Nat.log 2 n
  have hL4 : 4 ≤ L := (ValidRegime.four_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
  have hn_2L : n ≤ 2 ^ (L + 1) := (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
  have hexp : (L + 1) * (p_max + 2) + 1 ≤ 2 * (p_max + 2) * L := by
    calc (L + 1) * (p_max + 2) + 1
        = (p_max + 2) * L + ((p_max + 2) + 1) := by ring
      _ ≤ (p_max + 2) * L + (p_max + 2) * 2 := by omega
      _ ≤ (p_max + 2) * L + (p_max + 2) * L :=
          Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega : 2 ≤ L)) _
      _ = 2 * (p_max + 2) * L := by ring
  calc (canonicalSchedule h).paddedUniv
      ≤ 2 * n ^ (p_max + 2) := paddedUniv_le_two_mul_pow h
    _ ≤ 2 * (2 ^ (L + 1)) ^ (p_max + 2) :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hn_2L _)
    _ = 2 ^ ((L + 1) * (p_max + 2) + 1) := by rw [← Nat.pow_mul, ← pow_succ']
    _ ≤ 2 ^ (2 * (p_max + 2) * L) := Nat.pow_le_pow_right Nat.two_pos hexp

theorem nFloor_ge_pow_256 {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {j : ℕ}
    (hj : j ≤ (canonicalSchedule h).depth) :
    256 ^ 9 ≤ (canonicalSchedule h).nFloor j := by
  set r := redundancyRatio n R
  set k := treeDepth U r
  have hr256 : minRedundancyRatio ≤ r := h.redundancyRatio_bounds.1
  have h4r : 4 * r ≤ Nat.log 2 U := h.four_mul_redundancyRatio_le_log_univ
  have hn18 : 2 ^ 18 * (Nat.log 2 U) ^ 9 ≤ n := h.two_pow_eighteen_mul_log_univ_pow_le
  have hstep : ∀ i < k, 2 ^ 18 * targetSize n U r k (i + 1) ≤ targetSize n U r k i :=
    fun i hi => two_pow_eighteen_mul_targetSize_succ_le hr256 h4r hn18 hi
  have hT_le : targetSize n U r k j ≤ n := targetSize_le_of_step hstep j hj
  have hT_pos : 1 ≤ targetSize n U r k j :=
    targetSize_pos (by have := h.two_le_n; omega) (by dsimp [minRedundancyRatio] at hr256; omega)
      h4r hj rfl
  obtain ⟨hlo, _⟩ := targetSize_le_nFloor_and_lt hT_pos hT_le
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · have h0 : targetSize n U r k 0 = n := rfl
    rw [h0] at hlo
    have hr_val : 256 ≤ Nat.log 2 U := by dsimp [minRedundancyRatio] at hr256; omega
    exact ((Nat.pow_le_pow_left hr_val 9).trans
      ((Nat.le_mul_of_pos_left _ (by positivity)).trans hn18)).trans hlo
  · rw [targetSize_eq_levelScale_pow hpos] at hlo
    exact (Nat.pow_le_pow_left (hr256.trans (r_le_levelScale hpos h4r)) 9).trans hlo

private theorem routerSeedBits_sq_le_of_ge_threshold {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hlt : ℓ < (canonicalSchedule h).depth)
    (hth : FeistelPerm.childRouterThreshold (canonicalSchedule h).epsInv
      (canonicalSchedule h).alphaInv ≤ (canonicalSchedule h).nLow ℓ) :
    let P := canonicalSchedule h
    (FeistelPerm.childRouterSeedBits (FeistelPerm.childRouterChars P.epsInv)
      (FeistelPerm.childRouterRep P.epsInv P.alphaInv)
      (FeistelPerm.childRouterCharBits (FeistelPerm.childRouterChars P.epsInv)
        (P.routerRightUniv ℓ))
      (P.branchBits ℓ)) ^ 2 ≤ P.nFloor ℓ := by
  intro P
  set B_seed := FeistelPerm.childRouterSeedBits (FeistelPerm.childRouterChars P.epsInv)
    (FeistelPerm.childRouterRep P.epsInv P.alphaInv)
    (FeistelPerm.childRouterCharBits (FeistelPerm.childRouterChars P.epsInv)
      (P.routerRightUniv ℓ))
    (P.branchBits ℓ)
  have hT_r_pos : 1 ≤ P.routerRightUniv ℓ := by
    dsimp only [TreeSchedule.routerRightUniv]
    split_ifs
    · exact Nat.mul_pos (Nat.two_pow_pos _) P.quotOne_pos
    · exact Nat.two_pow_pos _
  have hpow := FeistelPerm.childRouterSeedBits_pow_le P.epsInv P.alphaInv (P.branchBits ℓ) hT_r_pos
  have h256C : 256 * FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv ≤ P.nFloor ℓ := by
    have hc := mul_spaceConst_le_threshold P.epsInv P.alphaInv
    have hnl_nf : P.nLow ℓ ≤ P.nFloor ℓ := by
      dsimp only [TreeSchedule.nLow]
      split_ifs with h0
      · subst h0; have : P.nFloor 0 = n := P.nFloor_zero; have : P.cap = n := rfl; omega
      · exact Nat.sub_le _ _
    exact (hc.trans hth).trans hnl_nf
  by_cases hB0_one : B_seed = 0
  · rw [hB0_one]; simp
  have hB_pos : 1 ≤ B_seed := Nat.pos_of_ne_zero hB0_one
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · have hE_ge : 2 * (p_max + 3) ≤ max P.epsInv 1 :=
      (le_max_right 12 _).trans (le_max_left _ 1)
    have hdom_eq : 2 ^ P.branchBits 0 * P.routerRightUniv 0 = P.paddedUniv := by
      dsimp only [TreeSchedule.routerRightUniv, TreeSchedule.paddedUniv,
        TreeSchedule.branchFactor]
      rw [ite_eq_left rfl, ← Nat.mul_assoc]
    have hUpad_le2 := paddedUniv_le_two_mul_pow h
    have hnf0 : P.nFloor 0 = n := P.nFloor_zero
    rw [hnf0] at h256C ⊢
    have hpow0 : (B_seed ^ 2) ^ (p_max + 3) ≤ n ^ (p_max + 3) := by
      calc (B_seed ^ 2) ^ (p_max + 3)
          = B_seed ^ (2 * (p_max + 3)) := (Nat.pow_mul B_seed 2 _).symm
        _ ≤ B_seed ^ max P.epsInv 1 := Nat.pow_le_pow_right hB_pos hE_ge
        _ ≤ FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv * P.paddedUniv := by
            rwa [hdom_eq] at hpow
        _ ≤ FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv * (2 * n ^ (p_max + 2)) :=
            Nat.mul_le_mul_left _ hUpad_le2
        _ = (2 * FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv) * n ^ (p_max + 2) := by
            ring
        _ ≤ n * n ^ (p_max + 2) := Nat.mul_le_mul_right _ (by omega)
        _ = n ^ (p_max + 3) := (pow_succ' n _).symm
    exact (Nat.pow_le_pow_iff_left (by omega : p_max + 3 ≠ 0)).mp hpow0
  · have hE_ge12 : 12 ≤ max P.epsInv 1 := (le_max_left 12 _).trans (le_max_left _ 1)
    set y := P.nFloor ℓ
    have hy1 : 1 ≤ y := (Nat.one_le_pow 9 256 (by decide)).trans (nFloor_ge_pow_256 h hlt.le)
    have hdom_ℓ : 2 ^ P.branchBits ℓ * P.routerRightUniv ℓ = 2 ^ P.idBits ℓ := by
      dsimp only [TreeSchedule.routerRightUniv]
      rw [ite_eq_right hpos.ne', ← Nat.pow_add]
      have hstep_id := P.idBits_step_le ℓ hpos hlt
      congr 1; omega
    have hid_pow : 2 ^ P.idBits ℓ ≤ 256 * y ^ 4 := by
      have hcl : 2 ^ Nat.clog 2 (2 * max y 1) ≤ 4 * y := by
        rw [max_eq_left hy1]
        calc 2 ^ Nat.clog 2 (2 * y) ≤ 2 * (2 * y) := Nat.pow_clog_le_mul Nat.one_lt_two (by omega)
          _ = 4 * y := by ring
      change 2 ^ (4 * Nat.clog 2 (2 * max y 1)) ≤ 256 * y ^ 4
      calc 2 ^ (4 * Nat.clog 2 (2 * max y 1))
          = (2 ^ Nat.clog 2 (2 * max y 1)) ^ 4 := by rw [Nat.mul_comm 4, Nat.pow_mul]
        _ ≤ (4 * y) ^ 4 := Nat.pow_le_pow_left hcl 4
        _ = 256 * y ^ 4 := by ring
    have hpow6 : (B_seed ^ 2) ^ 6 ≤ y ^ 6 := by
      calc (B_seed ^ 2) ^ 6 = B_seed ^ 12 := (Nat.pow_mul B_seed 2 6).symm
        _ ≤ B_seed ^ max P.epsInv 1 := Nat.pow_le_pow_right hB_pos hE_ge12
        _ ≤ FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv * 2 ^ P.idBits ℓ := by
            rwa [hdom_ℓ] at hpow
        _ ≤ FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv * (256 * y ^ 4) :=
            Nat.mul_le_mul_left _ hid_pow
        _ = (256 * FeistelPerm.childRouterSpaceConst P.epsInv P.alphaInv) * y ^ 4 := by ring
        _ ≤ y * y ^ 4 := Nat.mul_le_mul_right _ h256C
        _ = y ^ 5 := (pow_succ' y 4).symm
        _ ≤ y ^ 6 := Nat.pow_le_pow_right hy1 (by decide)
    exact (Nat.pow_le_pow_iff_left (by decide : 6 ≠ 0)).mp hpow6

private theorem routerSeedBits_sq_le_of_lt_threshold {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hlt : ℓ < (canonicalSchedule h).depth) :
    let P := canonicalSchedule h
    (2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) *
      Cslib.Probability.trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ)) ^ 2 ≤ P.nFloor ℓ := by
  intro P
  rcases Nat.eq_zero_or_pos ℓ with rfl | hpos
  · set L := Nat.log 2 n
    have hpoly : 2560000 * (max q_min 1 + p_max + 4) ^ 4 ≤ L :=
      (poly_le_thresholdLogN q_min p_max).trans h.thresholdLogN_le_log
    have hbase_p : max q_min 1 + p_max + 4 ≤ (max q_min 1 + p_max + 4) ^ 4 :=
      Nat.le_self_pow (by decide) _
    have hm_le : FeistelPerm.childRouterHalfInd (P.nHigh 0) ≤ 4 * L := by
      have hnh0 : P.nHigh 0 = n := rfl
      have hn_le : max n 2 ≤ 2 ^ (L + 1) := by
        rw [max_eq_left h.two_le_n]
        exact (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le
      have hcl : Nat.clog 2 (max n 2) ≤ L + 1 := Nat.clog_le_of_le_pow hn_le
      rw [FeistelPerm.childRouterHalfInd_eq, hnh0]
      omega
    have htd0 : Cslib.Probability.trinomialDeg (P.routerRightUniv 0) (P.branchBits 0) ≤
        6 * (p_max + 2) * L := by
      have htd := Cslib.Probability.trinomialDeg_le_three_mul (P.routerRightUniv 0) (P.branchBits 0)
      have hT0_le : P.routerRightUniv 0 ≤ P.paddedUniv := by
        dsimp only [TreeSchedule.routerRightUniv, TreeSchedule.paddedUniv,
          TreeSchedule.branchFactor]
        rw [ite_eq_left rfl, Nat.mul_assoc]
        exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
      have hUpad_pow : max (P.routerRightUniv 0) 2 ≤ 2 ^ (2 * (p_max + 2) * L) := by
        refine max_le (hT0_le.trans (paddedUniv_le_two_pow_mul_log h)) ?_
        have h1 : 1 ≤ 2 * (p_max + 2) * L :=
          Nat.mul_pos (by omega) (by omega)
        exact (show 2 = 2 ^ 1 by decide) ▸ Nat.pow_le_pow_right Nat.two_pos h1
      have hcl_T0 : Nat.clog 2 (max (P.routerRightUniv 0) 2) ≤ 2 * (p_max + 2) * L :=
        Nat.clog_le_of_le_pow hUpad_pow
      have hs0_le : max (P.branchBits 0) 1 ≤ 2 * (p_max + 2) * L := by
        have hb0 : P.branchBits 0 ≤ L := by
          change Nat.log 2 (n / max (targetSize n U (redundancyRatio n R)
            (treeDepth U (redundancyRatio n R)) 1) 1) - 0 ≤ L
          rw [Nat.sub_zero]
          exact Nat.log_mono_right (Nat.div_le_self n _)
        have h1_le : 1 ≤ 2 * (p_max + 2) := by omega
        calc max (P.branchBits 0) 1 ≤ L := max_le hb0 (by omega)
          _ = 1 * L := (one_mul L).symm
          _ ≤ (2 * (p_max + 2)) * L := Nat.mul_le_mul_right L h1_le
      have hmax := max_le hcl_T0 hs0_le
      calc Cslib.Probability.trinomialDeg (P.routerRightUniv 0) (P.branchBits 0)
          ≤ 3 * max (Nat.clog 2 (max (P.routerRightUniv 0) 2)) (max (P.branchBits 0) 1) := htd
        _ ≤ 3 * (2 * (p_max + 2) * L) := Nat.mul_le_mul_left 3 hmax
        _ = 6 * (p_max + 2) * L := by ring
    have hprod_L3 : 2 * FeistelPerm.childRouterHalfInd (P.nHigh 0) *
        Cslib.Probability.trinomialDeg (P.routerRightUniv 0) (P.branchBits 0) ≤ L ^ 3 := by
      have h48 : 48 * (p_max + 2) ≤ L := by omega
      calc 2 * FeistelPerm.childRouterHalfInd (P.nHigh 0) *
            Cslib.Probability.trinomialDeg (P.routerRightUniv 0) (P.branchBits 0)
          ≤ 2 * (4 * L) * (6 * (p_max + 2) * L) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm_le) htd0
        _ = (48 * (p_max + 2)) * L ^ 2 := by ring
        _ ≤ L * L ^ 2 := Nat.mul_le_mul_right _ h48
        _ = L ^ 3 := (pow_succ' L 2).symm
    rw [P.nFloor_zero]
    calc (2 * FeistelPerm.childRouterHalfInd (P.nHigh 0) *
          Cslib.Probability.trinomialDeg (P.routerRightUniv 0) (P.branchBits 0)) ^ 2
        ≤ (L ^ 3) ^ 2 := Nat.pow_le_pow_left hprod_L3 2
      _ = L ^ 6 := (Nat.pow_mul L 3 2).symm
      _ ≤ 2 ^ L := Nat.pow_le_two_pow (by decide) (by omega)
      _ ≤ n := Nat.pow_log_le_self 2 (by have := h.two_le_n; omega)
  · set y := P.nFloor ℓ
    have hy_ge : 256 ^ 9 ≤ y := nFloor_ge_pow_256 h hlt.le
    have hy1 : 1 ≤ y := (Nat.one_le_pow 9 256 (by decide)).trans hy_ge
    set ly := Nat.clog 2 (2 * max y 1)
    have hly_ge : 73 ≤ ly := by
      have hpow72 : 2 ^ 72 < 2 * max y 1 := by
        rw [max_eq_left hy1]
        have : (256 : ℕ) ^ 9 = 2 ^ 72 := by decide
        omega
      by_contra hlt73
      have hle : 2 * max y 1 ≤ 2 ^ ly := Nat.le_pow_clog Nat.one_lt_two (2 * max y 1)
      have hpow_le : 2 ^ ly ≤ 2 ^ 72 := Nat.pow_le_pow_right Nat.two_pos (by omega)
      omega
    have hhd : 2 * P.delta ℓ ≤ y :=
      two_mul_delta_le_nFloor_of_eight_le ((by decide : 8 ≤ 256 ^ 9).trans hy_ge)
    have hm_le : FeistelPerm.childRouterHalfInd (P.nHigh ℓ) ≤ 4 * ly := by
      have hnh_le : max (P.nHigh ℓ) 2 ≤ 2 * max y 1 := by
        have hnh_eq : P.nHigh ℓ = y + P.delta ℓ := by
          dsimp only [TreeSchedule.nHigh]
          rw [ite_eq_right hpos.ne']
        rw [hnh_eq, max_eq_left hy1]
        omega
      have hcl : Nat.clog 2 (max (P.nHigh ℓ) 2) ≤ ly := Nat.clog_mono_right 2 hnh_le
      rw [FeistelPerm.childRouterHalfInd_eq]
      omega
    have htd_le : Cslib.Probability.trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ) ≤
        12 * ly := by
      have htd := Cslib.Probability.trinomialDeg_le_three_mul
        (P.routerRightUniv ℓ) (P.branchBits ℓ)
      have hid_eq : P.idBits ℓ = 4 * ly := rfl
      have hT_le : max (P.routerRightUniv ℓ) 2 ≤ 2 ^ (4 * ly) := by
        dsimp only [TreeSchedule.routerRightUniv]
        rw [ite_eq_right hpos.ne']
        refine max_le (Nat.pow_le_pow_right Nat.two_pos ?_) ?_
        · omega
        · exact (show 2 = 2 ^ 1 by decide) ▸ Nat.pow_le_pow_right Nat.two_pos (by omega)
      have hs_le : max (P.branchBits ℓ) 1 ≤ 4 * ly := by
        have hstep_id := P.idBits_step_le ℓ hpos hlt
        omega
      have hcl_T : Nat.clog 2 (max (P.routerRightUniv ℓ) 2) ≤ 4 * ly :=
        Nat.clog_le_of_le_pow hT_le
      have := max_le hcl_T hs_le
      omega
    have hly_pow : 2 ^ (ly - 1) < 2 * y := by
      by_contra hge
      have hcl := Nat.clog_le_of_le_pow ((max_eq_left hy1).symm ▸ not_lt.mp hge)
      dsimp only [ly] at hcl; omega
    have h2_sq : 2 * (96 * ly ^ 2) ^ 2 ≤ 2 ^ (ly - 1) := by
      set q := (ly - 1) / 4
      have hq_ge : 18 ≤ q := by omega
      obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le hq_ge
      have h70q : 70 * q ≤ 2 ^ q := by
        have hsq : (8 + u) ^ 2 ≤ 2 ^ (8 + u) := Nat.sq_le_two_pow (by omega)
        have hmul : 2 ^ 10 * (8 + u) ^ 2 ≤ 2 ^ q := by
          calc 2 ^ 10 * (8 + u) ^ 2 ≤ 2 ^ 10 * 2 ^ (8 + u) := Nat.mul_le_mul_left _ hsq
            _ = 2 ^ q := by rw [← Nat.pow_add]; congr 1; omega
        have h10 : (2 : ℕ) ^ 10 = 1024 := by decide
        rw [h10] at hmul
        nlinarith
      have hly_le : ly ≤ 5 * q := by omega
      calc 2 * (96 * ly ^ 2) ^ 2
          ≤ 2 * (96 * (5 * q) ^ 2) ^ 2 :=
            Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left
              (Nat.mul_le_mul_left 96 (Nat.pow_le_pow_left hly_le 2)) 2)
        _ = 11520000 * q ^ 4 := by ring
        _ ≤ (70 * q) ^ 4 := by
            have : 11520000 ≤ 70 ^ 4 := by decide
            calc 11520000 * q ^ 4 ≤ 70 ^ 4 * q ^ 4 := Nat.mul_le_mul_right _ this
              _ = (70 * q) ^ 4 := (Nat.mul_pow 70 q 4).symm
        _ ≤ (2 ^ q) ^ 4 := Nat.pow_le_pow_left h70q 4
        _ = 2 ^ (q * 4) := (Nat.pow_mul 2 q 4).symm
        _ ≤ 2 ^ (ly - 1) := Nat.pow_le_pow_right Nat.two_pos (by omega)
    have hprod_le : 2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) *
        Cslib.Probability.trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ) ≤ 96 * ly ^ 2 := by
      calc 2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) *
            Cslib.Probability.trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ)
          ≤ 2 * (4 * ly) * (12 * ly) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm_le) htd_le
        _ = 96 * ly ^ 2 := by ring
    have h2y : 2 * (2 * FeistelPerm.childRouterHalfInd (P.nHigh ℓ) *
        Cslib.Probability.trinomialDeg (P.routerRightUniv ℓ) (P.branchBits ℓ)) ^ 2 ≤ 2 * y :=
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hprod_le 2)).trans (h2_sq.trans hly_pow.le)
    exact Nat.le_of_mul_le_mul_left h2y (by decide)

/-- Uniform quadratic bound on `routerSeedBits ℓ` across **both** the `DoubleTabulation`
(`nLow ℓ ≥ childRouterThreshold`) and small-node `trinomialPolyHash`
(`nLow ℓ < childRouterThreshold`) regimes: `(routerSeedBits ℓ) ^ 2 ≤ nFloor ℓ` for every
`0 ≤ ℓ < depth`. -/
theorem routerSeedBits_sq_le_nFloor {U V n R p_min q_min p_max q_max : ℕ}
    (h : ValidRegime U V n R p_min q_min p_max q_max) {ℓ : ℕ}
    (hlt : ℓ < (canonicalSchedule h).depth) :
    ((canonicalSchedule h).routerSeedBits ℓ) ^ 2 ≤ (canonicalSchedule h).nFloor ℓ := by
  dsimp only [TreeSchedule.routerSeedBits]
  split_ifs with hth
  · exact routerSeedBits_sq_le_of_ge_threshold h hlt hth
  · exact routerSeedBits_sq_le_of_lt_threshold h hlt

end Cslib.DataStructure.Dictionary.SubconstantRedundancy
