/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Dictatorship and random dictatorship mechanisms

Two canonical facility-location mechanisms that work on an arbitrary metric space `G`
([ProcacciaTennenholtz2013]):

* `dictatorship i₀` always places the facility at agent `i₀`'s reported location. It is
  strongly group strategyproof (`dictatorship_isGroupStrategyProof`) and achieves approximation
  ratio `max 1 (n - 1)` for `n` agents (`dictatorship_hasApproxRatio`).
* `randomDictatorship` chooses an agent uniformly at random and places the facility at its
  reported location (`(PMF.uniformOfFintype ι).map x`). It is strategyproof
  (`randomDictatorship_isStrategyProof`) and achieves approximation ratio `2 - 2 / n`
  (`randomDictatorship_hasApproxRatio`), hence `2` (`randomDictatorship_hasApproxRatio_two`),
  improving on deterministic dictatorship whenever `n ≥ 3`.

Unlike the median on `ℝ`, `randomDictatorship` is not group strategyproof (even on `ℝ` for 3
agents, and not even weakly group strategyproof on a 3-leaf star metric); see
`CslibFrontierTests.FacilityLocation`.

## Main definitions

* `Cslib.GameTheory.FacilityLocation.dictatorship`: deterministic dictatorship of agent `i₀`.
* `Cslib.GameTheory.FacilityLocation.randomDictatorship`: uniform random dictatorship.

## Main results

* `Cslib.GameTheory.FacilityLocation.dictatorship_isGroupStrategyProof`,
  `Cslib.GameTheory.FacilityLocation.dictatorship_isStrategyProof`: dictatorship is strongly group
  strategyproof (and hence strategyproof) on every pseudometric space.
* `Cslib.GameTheory.FacilityLocation.dictatorship_hasApproxRatio`,
  `Cslib.GameTheory.FacilityLocation.dictatorship_hasApproxRatio_card_sub_one`: worst-case social
  cost approximation ratio of dictatorship.
* `Cslib.GameTheory.FacilityLocation.randomDictatorship_isStrategyProof`: random dictatorship is
  strategyproof on every pseudometric space.
* `Cslib.GameTheory.FacilityLocation.randomDictatorship_hasApproxRatio`,
  `Cslib.GameTheory.FacilityLocation.randomDictatorship_hasApproxRatio_two`: random dictatorship is
  `(2 - 2 / n)`-approximate (and hence `2`-approximate) on every pseudometric space.

## References

* [A. D. Procaccia and M. Tennenholtz, *Approximate Mechanism Design without
  Money*][ProcacciaTennenholtz2013]
-/

public section

namespace Cslib.GameTheory.FacilityLocation

open MeasureTheory Finset
open scoped BigOperators

section Dictatorship

variable {ι G : Type*} [PseudoMetricSpace G] [MeasurableSpace G]

/-- The deterministic **dictatorship** of agent `i₀`: always place the facility at `x i₀`. -/
@[expose] noncomputable def dictatorship (i₀ : ι) : Mechanism ι G :=
  Mechanism.deterministic fun x => x i₀

variable [OpensMeasurableSpace G]

/-- Dictatorship is strongly group strategyproof on every pseudometric space: if a coalition `A`
excludes `i₀` the outcome is unchanged, and if `i₀ ∈ A` then `i₀` already pays `0` and any
deviation keeps `dist (x i₀) y = 0` so no other member can gain by the triangle inequality. -/
theorem dictatorship_isGroupStrategyProof [DecidableEq ι] (i₀ : ι) :
    (dictatorship (G := G) i₀).IsGroupStrategyProof := by
  rw [dictatorship, Mechanism.isGroupStrategyProof_deterministic_iff]
  rintro x z A ⟨hle, j, hj, hlt⟩
  by_cases hi : i₀ ∈ A
  · have hzero : dist (x i₀) (A.piecewise z x i₀) = 0 :=
      le_antisymm (by simpa only [dist_self] using hle i₀ hi) dist_nonneg
    have htri : dist (x j) (x i₀) ≤ dist (x j) (A.piecewise z x i₀) := by
      calc dist (x j) (x i₀)
          ≤ dist (x j) (A.piecewise z x i₀) + dist (A.piecewise z x i₀) (x i₀) :=
            dist_triangle _ _ _
        _ = dist (x j) (A.piecewise z x i₀) := by
            rw [dist_comm (A.piecewise z x i₀) (x i₀), hzero, add_zero]
    exact hlt.not_ge htri
  · rw [Finset.piecewise_eq_of_notMem _ _ _ hi] at hlt
    exact (lt_irrefl _ hlt)

theorem dictatorship_isStrategyProof [DecidableEq ι] (i₀ : ι) :
    (dictatorship (G := G) i₀).IsStrategyProof :=
  (dictatorship_isGroupStrategyProof i₀).isStrategyProof

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
theorem socialCost_dictatorship_le [Fintype ι] (i₀ : ι) (x : ι → G) (y : G) :
    socialCost x (x i₀) ≤ max 1 ((Fintype.card ι : ℝ) - 1) * socialCost x y := by
  classical
  have hi₀ : i₀ ∈ (Finset.univ : Finset ι) := Finset.mem_univ i₀
  have hsum : socialCost x (x i₀) = ∑ i ∈ Finset.univ.erase i₀, dist (x i) (x i₀) := by
    rw [socialCost, ← Finset.add_sum_erase _ _ hi₀, dist_self, zero_add]
  have hopt : socialCost x y = dist (x i₀) y + ∑ i ∈ Finset.univ.erase i₀, dist (x i) y := by
    rw [socialCost, ← Finset.add_sum_erase _ _ hi₀]
  have htri : ∑ i ∈ Finset.univ.erase i₀, dist (x i) (x i₀) ≤
      (∑ i ∈ Finset.univ.erase i₀, dist (x i) y) +
        ((Fintype.card ι : ℝ) - 1) * dist (x i₀) y := by
    calc ∑ i ∈ Finset.univ.erase i₀, dist (x i) (x i₀)
        ≤ ∑ i ∈ Finset.univ.erase i₀, (dist (x i) y + dist (x i₀) y) :=
          Finset.sum_le_sum fun i _ => by
            rw [dist_comm (x i₀) y]
            exact dist_triangle (x i) y (x i₀)
      _ = (∑ i ∈ Finset.univ.erase i₀, dist (x i) y) +
            ((Fintype.card ι : ℝ) - 1) * dist (x i₀) y := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem hi₀,
            Finset.card_univ, nsmul_eq_mul]
          have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨i₀⟩
          rw [Nat.cast_sub hpos, Nat.cast_one]
  set α : ℝ := max 1 ((Fintype.card ι : ℝ) - 1)
  have hα1 : 1 ≤ α := le_max_left _ _
  have hαn : (Fintype.card ι : ℝ) - 1 ≤ α := le_max_right _ _
  have hrest : ∑ i ∈ Finset.univ.erase i₀, dist (x i) y ≤
      α * ∑ i ∈ Finset.univ.erase i₀, dist (x i) y :=
    le_mul_of_one_le_left (Finset.sum_nonneg fun _ _ => dist_nonneg) hα1
  have hlead : ((Fintype.card ι : ℝ) - 1) * dist (x i₀) y ≤ α * dist (x i₀) y :=
    mul_le_mul_of_nonneg_right hαn dist_nonneg
  rw [hsum, hopt, mul_add]
  linarith

theorem dictatorship_hasApproxRatio [Fintype ι] [Nonempty G] (i₀ : ι) :
    (dictatorship (G := G) i₀).HasApproxRatio (max 1 ((Fintype.card ι : ℝ) - 1)) := by
  classical
  have hnn : 0 ≤ max 1 ((Fintype.card ι : ℝ) - 1) := le_trans zero_le_one (le_max_left _ _)
  rw [dictatorship, Mechanism.hasApproxRatio_deterministic_iff _ hnn]
  intro x
  exact le_mul_optSocialCost hnn (socialCost_dictatorship_le i₀ x)

theorem dictatorship_hasApproxRatio_one [Fintype ι] [Subsingleton ι] [Nonempty G] (i₀ : ι) :
    (dictatorship (G := G) i₀).HasApproxRatio 1 := by
  have := uniqueOfSubsingleton i₀
  have hcard : Fintype.card ι = 1 := Fintype.card_unique
  have hmax : max 1 ((Fintype.card ι : ℝ) - 1) = 1 := by
    rw [hcard]
    norm_num
  exact hmax ▸ dictatorship_hasApproxRatio i₀

theorem dictatorship_hasApproxRatio_card_sub_one [Fintype ι] [Nonempty G]
    (hcard : 2 ≤ Fintype.card ι) (i₀ : ι) :
    (dictatorship (G := G) i₀).HasApproxRatio ((Fintype.card ι : ℝ) - 1) := by
  have h2 : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
  have hmax : max 1 ((Fintype.card ι : ℝ) - 1) = (Fintype.card ι : ℝ) - 1 :=
    max_eq_right (by linarith)
  exact hmax ▸ dictatorship_hasApproxRatio i₀

end Dictatorship

section RandomDictatorship

variable {ι G : Type*} [PseudoMetricSpace G] [MeasurableSpace G] [Fintype ι] [Nonempty ι]

/-- **Random dictatorship**: choose an agent uniformly at random and place the facility at its
reported location. -/
@[expose] noncomputable def randomDictatorship : Mechanism ι G :=
  Mechanism.ofPMF fun x => (Cslib.Probability.PMF.uniformOfFintype ι).map x

variable [OpensMeasurableSpace G]

theorem randomDictatorship_hasFiniteCost (x : ι → G) :
    HasFiniteCost (randomDictatorship x) :=
  hasFiniteCost_ofPMF_map_finite _ x

theorem expectedCost_randomDictatorship (x : ι → G) (loc : G) :
    expectedCost (randomDictatorship x) loc = (∑ j, dist loc (x j)) / Fintype.card ι := by
  rw [randomDictatorship, Mechanism.ofPMF, expectedCost_ofPMF_map_fintype]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, inv_mul_eq_div, Finset.sum_div]

theorem expectedSocialCost_randomDictatorship (x : ι → G) :
    expectedSocialCost (randomDictatorship x) x =
      (∑ i, ∑ j, dist (x i) (x j)) / Fintype.card ι := by
  simp only [expectedSocialCost, expectedCost_randomDictatorship, ← Finset.sum_div]

/-- Random dictatorship is strategyproof on every pseudometric space: when agent `i` misreports
`z`, every term `j ≠ i` in its expected distance is unchanged, while the `j = i` term increases
from `0` to `dist (x i) z ≥ 0`. -/
theorem randomDictatorship_isStrategyProof [DecidableEq ι] :
    (randomDictatorship (ι := ι) (G := G)).IsStrategyProof := by
  rw [Mechanism.isStrategyProof_iff_expectedCost_le (M := randomDictatorship)
    randomDictatorship_hasFiniteCost]
  intro x i z
  rw [expectedCost_randomDictatorship, expectedCost_randomDictatorship]
  have hpos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  refine div_le_div_of_nonneg_right ?_ hpos.le
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ i), dist_self, zero_add]
  refine le_add_of_nonneg_of_le dist_nonneg (le_of_eq (Finset.sum_congr rfl fun j hj => ?_))
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Random dictatorship achieves approximation ratio `2 - 2 / n` for `n` agents on every
pseudometric space. -/
theorem randomDictatorship_hasApproxRatio :
    (randomDictatorship (ι := ι) (G := G)).HasApproxRatio
      (2 - 2 / (Fintype.card ι : ℝ)) := by
  classical
  have hpos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have h1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hratio : 0 ≤ 2 - 2 / (Fintype.card ι : ℝ) := by
    rw [sub_nonneg, div_le_iff₀ hpos]
    linarith
  intro x
  have : Nonempty G := ⟨x (Classical.arbitrary ι)⟩
  rw [expectedSocialECost_eq_ofReal_expectedSocialCost fun i =>
        randomDictatorship_hasFiniteCost x (x i),
    optSocialECost_eq_ofReal_optSocialCost, ← ENNReal.ofReal_mul hratio,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg hratio (optSocialCost_nonneg x))]
  refine le_mul_optSocialCost hratio fun y => ?_
  rw [expectedSocialCost_randomDictatorship, div_le_iff₀ hpos]
  have hsum : ∑ i, ∑ j, dist (x i) (x j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, dist (x i) (x j) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), dist_self, zero_add]
  have htri : ∑ i, ∑ j ∈ Finset.univ.erase i, dist (x i) (x j) ≤
      2 * ((Fintype.card ι : ℝ) - 1) * socialCost x y := by
    calc ∑ i, ∑ j ∈ Finset.univ.erase i, dist (x i) (x j)
        ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, (dist (x i) y + dist (x j) y) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [dist_comm (x j) y]
          exact dist_triangle (x i) y (x j)
      _ = ∑ i, (((Fintype.card ι : ℝ) - 1) * dist (x i) y +
            ∑ j ∈ Finset.univ.erase i, dist (x j) y) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, nsmul_eq_mul,
            Nat.cast_sub Fintype.card_pos, Nat.cast_one]
      _ = ((Fintype.card ι : ℝ) - 1) * socialCost x y +
            ∑ i, ∑ j ∈ Finset.univ.erase i, dist (x j) y := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, socialCost]
      _ = 2 * ((Fintype.card ι : ℝ) - 1) * socialCost x y := by
          have hswap : ∑ i : ι, ∑ j ∈ Finset.univ.erase i, dist (x j) y =
              ((Fintype.card ι : ℝ) - 1) * socialCost x y := by
            have hite : ∀ i j : ι,
                (if j ∈ Finset.univ.erase i then dist (x j) y else 0) =
                  (if i ∈ Finset.univ.erase j then dist (x j) y else 0) := by
              intro i j
              by_cases hij : j = i
              · simp [hij]
              · simp [hij, Ne.symm hij]
            calc ∑ i, ∑ j ∈ Finset.univ.erase i, dist (x j) y
                = ∑ i, ∑ j, if j ∈ Finset.univ.erase i then dist (x j) y else 0 := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
              _ = ∑ j, ∑ i, if i ∈ Finset.univ.erase j then dist (x j) y else 0 := by
                  rw [Finset.sum_comm]
                  exact Finset.sum_congr rfl fun j _ =>
                    Finset.sum_congr rfl fun i _ => hite i j
              _ = ∑ j, ∑ _i ∈ Finset.univ.erase j, dist (x j) y := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
              _ = ∑ j, ((Fintype.card ι : ℝ) - 1) * dist (x j) y := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
                    Finset.card_univ, nsmul_eq_mul, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
              _ = ((Fintype.card ι : ℝ) - 1) * socialCost x y := by
                  rw [← Finset.mul_sum, socialCost]
          rw [hswap]
          ring
  rw [hsum]
  refine htri.trans_eq ?_
  field_simp [hpos.ne']

/-- Random dictatorship is `2`-approximate for social cost on every pseudometric space. -/
theorem randomDictatorship_hasApproxRatio_two :
    (randomDictatorship (ι := ι) (G := G)).HasApproxRatio 2 := by
  have hpos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hle : 2 - 2 / (Fintype.card ι : ℝ) ≤ 2 := by
    have : 0 ≤ 2 / (Fintype.card ι : ℝ) := by positivity
    linarith
  exact randomDictatorship_hasApproxRatio.mono hle

end RandomDictatorship

end Cslib.GameTheory.FacilityLocation
