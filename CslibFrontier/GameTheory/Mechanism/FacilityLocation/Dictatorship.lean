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

Two canonical facility-location mechanisms that work on an arbitrary pseudometric space `G`:

* `dictatorship i₀` always places the facility at agent `i₀`'s reported location. It is
  strongly group strategyproof (`dictatorship_isGroupStrategyProof`) and achieves the elementary
  worst-case approximation ratio `max 1 (n - 1)` for `n` agents (`dictatorship_hasApproxRatio`),
  included here for baseline comparison.
* `randomDictatorship` chooses an agent uniformly at random and places the facility at its
  reported location (`(PMF.uniformOfFintype ι).map x`), which is Mechanism 1 of
  [AlonFeldmanProcacciaTennenholtz2010] (§3.2, arXiv:0907.2049v1 pp. 6–7). It is strategyproof
  (`randomDictatorship_isStrategyProof`) and achieves approximation ratio `2 - 2 / n`
  (`randomDictatorship_hasApproxRatio`), hence `2` (`randomDictatorship_hasApproxRatio_two`),
  extending Theorem 3.1 of [AlonFeldmanProcacciaTennenholtz2010] from graphs to arbitrary
  pseudometric spaces (cf. §3.2, first remark, arXiv p. 7) and improving on deterministic
  dictatorship whenever `n ≥ 3`.

Unlike the median on `ℝ`, `randomDictatorship` fails coalitional strategyproofness: on a 3-leaf
star metric (`Star4` in `CslibFrontierTests.FacilityLocation`) it is not even weakly group
strategyproof ([AlonFeldmanProcacciaTennenholtz2010] §3.2, third remark, arXiv p. 7), and even
on `ℝ` for 3 agents (where it is weakly group strategyproof, §3.2, fourth remark) it fails strong
group strategyproofness (`CslibFrontierTests.FacilityLocation`).

## Main definitions

* `Cslib.GameTheory.FacilityLocation.dictatorship`: deterministic dictatorship of agent `i₀`.
* `Cslib.GameTheory.FacilityLocation.randomDictatorship`: uniform random dictatorship.

## Main results

* `Cslib.GameTheory.FacilityLocation.socialCost_self_le`: shared triangle-inequality shift bound
  from [AlonFeldmanProcacciaTennenholtz2010] (§3.2, proof of Theorem 3.1).
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

* [N. Alon, M. Feldman, A. D. Procaccia, and M. Tennenholtz, *Strategyproof Approximation of the
  Minimax on Networks*][AlonFeldmanProcacciaTennenholtz2010]
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
/-- Shifting a facility from any location `y` to agent `i`'s location `x i` increases total
social cost by at most `(n - 2) * dist (x i) y` ([AlonFeldmanProcacciaTennenholtz2010] §3.2,
proof of Theorem 3.1, arXiv:0907.2049v1 p. 6). -/
theorem socialCost_self_le [Fintype ι] (i : ι) (x : ι → G) (y : G) :
    socialCost x (x i) ≤ socialCost x y + ((Fintype.card ι : ℝ) - 2) * dist (x i) y := by
  classical
  have hi : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
  have hsum : socialCost x (x i) = ∑ j ∈ Finset.univ.erase i, dist (x j) (x i) := by
    rw [socialCost, ← Finset.add_sum_erase _ _ hi, dist_self, zero_add]
  have htri : ∑ j ∈ Finset.univ.erase i, dist (x j) (x i) ≤
      ∑ j ∈ Finset.univ.erase i, (dist (x j) y + dist (x i) y) :=
    Finset.sum_le_sum fun j _ => by
      rw [dist_comm (x i) y]
      exact dist_triangle (x j) y (x i)
  have hcard : ((Finset.univ.erase i : Finset ι).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
    rw [Finset.card_erase_of_mem hi, Finset.card_univ, Nat.cast_sub hpos, Nat.cast_one]
  have hrest : ∑ j ∈ Finset.univ.erase i, dist (x j) y = socialCost x y - dist (x i) y := by
    rw [socialCost, Finset.sum_erase_eq_sub hi]
  rw [hsum]
  calc ∑ j ∈ Finset.univ.erase i, dist (x j) (x i)
      ≤ ∑ j ∈ Finset.univ.erase i, (dist (x j) y + dist (x i) y) := htri
    _ = (socialCost x y - dist (x i) y) + ((Fintype.card ι : ℝ) - 1) * dist (x i) y := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard, hrest]
    _ = socialCost x y + ((Fintype.card ι : ℝ) - 2) * dist (x i) y := by ring

omit [MeasurableSpace G] [OpensMeasurableSpace G] in
theorem socialCost_dictatorship_le [Fintype ι] (i₀ : ι) (x : ι → G) (y : G) :
    socialCost x (x i₀) ≤ max 1 ((Fintype.card ι : ℝ) - 1) * socialCost x y := by
  set α : ℝ := max 1 ((Fintype.card ι : ℝ) - 1)
  have hsub : (Fintype.card ι : ℝ) - 2 ≤ α - 1 := by
    linarith [le_max_right (1 : ℝ) ((Fintype.card ι : ℝ) - 1)]
  have hpos : 0 ≤ α - 1 := by
    linarith [le_max_left (1 : ℝ) ((Fintype.card ι : ℝ) - 1)]
  have hle : dist (x i₀) y ≤ socialCost x y :=
    Finset.single_le_sum (fun _ _ => dist_nonneg) (Finset.mem_univ i₀)
  calc socialCost x (x i₀)
      ≤ socialCost x y + ((Fintype.card ι : ℝ) - 2) * dist (x i₀) y := socialCost_self_le i₀ x y
    _ ≤ socialCost x y + (α - 1) * dist (x i₀) y := by
        have : ((Fintype.card ι : ℝ) - 2) * dist (x i₀) y ≤ (α - 1) * dist (x i₀) y :=
          mul_le_mul_of_nonneg_right hsub dist_nonneg
        linarith
    _ ≤ socialCost x y + (α - 1) * socialCost x y := by
        have : (α - 1) * dist (x i₀) y ≤ (α - 1) * socialCost x y :=
          mul_le_mul_of_nonneg_left hle hpos
        linarith
    _ = α * socialCost x y := by ring

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
reported location (Mechanism 1 of [AlonFeldmanProcacciaTennenholtz2010] §3.2,
arXiv:0907.2049v1 p. 6). -/
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
from `0` to `dist (x i) z ≥ 0` ([AlonFeldmanProcacciaTennenholtz2010] §3.2, Theorem 3.1 and
first remark, arXiv:0907.2049v1 pp. 6–7). -/
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
pseudometric space ([AlonFeldmanProcacciaTennenholtz2010] §3.2, Theorem 3.1 and first remark,
arXiv:0907.2049v1 pp. 6–7). -/
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
  have hsum : ∑ i, ∑ j, dist (x i) (x j) = ∑ j, socialCost x (x j) := Finset.sum_comm
  have htri : ∑ j, socialCost x (x j) ≤ (2 * (Fintype.card ι : ℝ) - 2) * socialCost x y := by
    calc ∑ j, socialCost x (x j)
        ≤ ∑ j, (socialCost x y + ((Fintype.card ι : ℝ) - 2) * dist (x j) y) :=
          Finset.sum_le_sum fun j _ => socialCost_self_le j x y
      _ = (Fintype.card ι : ℝ) * socialCost x y +
            ((Fintype.card ι : ℝ) - 2) * socialCost x y := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            ← Finset.mul_sum, socialCost]
      _ = (2 * (Fintype.card ι : ℝ) - 2) * socialCost x y := by ring
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
