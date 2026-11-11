/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Basic
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Dictatorship
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Median
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Facility-location mechanisms: checked clients and counterexamples

Nonvacuous instantiations and separations for `Cslib.GameTheory.FacilityLocation`:

1. **Median and order statistics on `ℝ`**:
   - For `Fin 3`, `medianMechanism` and `orderStatisticMechanism k` (even clamped `k = 5 ≥ 3`) are
     group strategyproof, strategyproof, and `medianMechanism` is `1`-approximate; on
     `![0, 1, 10]`, `Fintype.lowerMedian = 1` achieves `socialCost = 10 = optSocialCost`, strictly
     below `socialCost ![0, 1, 10] 3 = 12`.
   - For even `n = 4` on `![0, 1, 2, 10]`, `Fintype.lowerMedian = 1` and `Fintype.upperMedian = 2`
     both attain `socialCost = 11 = optSocialCost`.
2. **Non-strategyproof counterexamples**:
   - `meanMechanism` fails strategyproofness on `Fin 3`, demonstrated both abstractly and
     explicitly on `![0, 1, 1]` (`2/3` vs `0` when agent `0` misreports `-2`).
   - The even-`n` midpoint median `(Fintype.orderStatistic x 1 + Fintype.orderStatistic x 2) / 2`
     on `Fin 4` fails strategyproofness on `![0, 1, 2, 3]` when agent `1` misreports `0`.
3. **Dictatorship and random dictatorship**:
   - `dictatorship 0` on `Fin 3` is group strategyproof and `2`-approximate, with tightness witness
     `![0, 10, 10]` showing ratio `α < 2` is impossible.
   - `randomDictatorship` on `Fin 3` over `ℝ` is strategyproof and `(4/3)`-approximate, yet fails
     `IsGroupStrategyProof` via coalition `{0, 1, 2}` deviating on `![0, 1, 2]` to `![1, 1, 1]`.
   - Over a finite 4-point star metric space `Star4` (3 leaves of pairwise distance `1`, center at
     distance `1/2`), `randomDictatorship` fails `IsWeakGroupStrategyProof`.
4. **Continuous `ProbabilityMeasure ℝ` client and constant mechanism**:
   - The uniform distribution on `[0, 1]` has `HasFiniteCost`, `expectedCost unif (1/2) = 1/4`, and
     `expectedECost unif (1/2) = ENNReal.ofReal (1/4)`.
   - The constant mechanism at `0` on `Fin 2 → ℝ` is group strategyproof yet satisfies
     `HasApproxRatio α` for no `α : ℝ`; conversely any `HasApproxRatio α` mechanism has `1 ≤ α`.
-/

namespace CslibFrontierTests.FacilityLocation

open Cslib.GameTheory.FacilityLocation
open MeasureTheory

/-! ### Median and order statistics on ℝ -/

example : (medianMechanism (ι := Fin 3)).IsGroupStrategyProof :=
  medianMechanism_isGroupStrategyProof

example : (medianMechanism (ι := Fin 3)).IsStrategyProof :=
  medianMechanism_isStrategyProof

example : (medianMechanism (ι := Fin 3)).HasApproxRatio 1 :=
  medianMechanism_hasApproxRatio_one

example : (orderStatisticMechanism (ι := Fin 3) 5).IsGroupStrategyProof :=
  orderStatisticMechanism_isGroupStrategyProof 5

private theorem orderStatistic_fin_eq {n : ℕ} {x : Fin (n + 1) → ℝ} {k : ℕ} {y : ℝ}
    (i : Fin (n + 1)) (hi : x i = y) (hk : k < n + 1) {sLt sLe : Finset (Fin (n + 1))}
    (hLt : ∀ j : Fin (n + 1), x j < y ↔ j ∈ sLt)
    (hLe : ∀ j : Fin (n + 1), x j ≤ y ↔ j ∈ sLe)
    (hc1 : sLt.card ≤ k) (hc2 : k < sLe.card) :
    Fintype.orderStatistic x k = y := by
  refine Fintype.orderStatistic_eq_of_isOrderStatistic
    (by simpa only [Fintype.card_fin] using hk) ⟨⟨i, hi⟩, ?_, ?_⟩
  · have heq : (Finset.univ.filter fun j => x j < y) = sLt := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hLt]
    rw [heq]; exact hc1
  · have heq : (Finset.univ.filter fun j => x j ≤ y) = sLe := by
      ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hLe]
    rw [heq]; exact hc2

private theorem lowerMedian_vec3 :
    Fintype.lowerMedian (![0, 1, 10] : Fin 3 → ℝ) = 1 := by
  rw [Fintype.lowerMedian_def]
  exact orderStatistic_fin_eq (n := 2) 1 (by norm_num) (by decide) (sLt := {0}) (sLe := {0, 1})
    (fun j => by fin_cases j <;> simp) (fun j => by fin_cases j <;> simp)
    (by decide) (by decide)

example :
    expectedSocialCost (medianMechanism (![0, 1, 10] : Fin 3 → ℝ)) ![0, 1, 10] = 10 := by
  rw [medianMechanism, Mechanism.expectedSocialCost_deterministic, lowerMedian_vec3, socialCost,
    Fin.sum_univ_three]
  norm_num [Real.dist_eq]

example : optSocialCost (![0, 1, 10] : Fin 3 → ℝ) = 10 := by
  rw [← (lowerMedian_isOptimal (![0, 1, 10] : Fin 3 → ℝ)).socialCost_eq_optSocialCost,
    lowerMedian_vec3, socialCost, Fin.sum_univ_three]
  norm_num [Real.dist_eq]

example :
    optSocialCost (![0, 1, 10] : Fin 3 → ℝ) < socialCost (![0, 1, 10] : Fin 3 → ℝ) 3 := by
  rw [← (lowerMedian_isOptimal (![0, 1, 10] : Fin 3 → ℝ)).socialCost_eq_optSocialCost,
    lowerMedian_vec3, socialCost, socialCost, Fin.sum_univ_three, Fin.sum_univ_three]
  norm_num [Real.dist_eq]

private theorem lowerMedian_vec4 :
    Fintype.lowerMedian (![0, 1, 2, 10] : Fin 4 → ℝ) = 1 := by
  rw [Fintype.lowerMedian_def]
  exact orderStatistic_fin_eq (n := 3) 1 (by norm_num) (by decide) (sLt := {0}) (sLe := {0, 1})
    (fun j => by fin_cases j <;> simp) (fun j => by fin_cases j <;> simp)
    (by decide) (by decide)

private theorem upperMedian_vec4 :
    Fintype.upperMedian (![0, 1, 2, 10] : Fin 4 → ℝ) = 2 := by
  rw [Fintype.upperMedian_def]
  exact orderStatistic_fin_eq (n := 3) 2 (by norm_num) (by decide)
    (sLt := {0, 1}) (sLe := {0, 1, 2})
    (fun j => by fin_cases j <;> (simp; try norm_num))
    (fun j => by fin_cases j <;> (simp; try norm_num))
    (by decide) (by decide)

example :
    socialCost (![0, 1, 2, 10] : Fin 4 → ℝ) (Fintype.lowerMedian ![0, 1, 2, 10]) = 11 ∧
      socialCost (![0, 1, 2, 10] : Fin 4 → ℝ) (Fintype.upperMedian ![0, 1, 2, 10]) = 11 ∧
      optSocialCost (![0, 1, 2, 10] : Fin 4 → ℝ) = 11 := by
  have h1 : socialCost (![0, 1, 2, 10] : Fin 4 → ℝ) 1 = 11 := by
    rw [socialCost, Fin.sum_univ_four]
    norm_num [Real.dist_eq]
  have h2 : socialCost (![0, 1, 2, 10] : Fin 4 → ℝ) 2 = 11 := by
    rw [socialCost, Fin.sum_univ_four]
    norm_num [Real.dist_eq]
  rw [← (lowerMedian_isOptimal (![0, 1, 2, 10] : Fin 4 → ℝ)).socialCost_eq_optSocialCost,
    lowerMedian_vec4, upperMedian_vec4]
  exact ⟨h1, h2, h1⟩

/-! ### Non-strategyproof counterexamples -/

example : ¬ (meanMechanism (ι := Fin 3)).IsStrategyProof :=
  not_isStrategyProof_meanMechanism (by decide)

example :
    expectedCost (meanMechanism (![0, 1, 1] : Fin 3 → ℝ)) 0 = 2 / 3 ∧
      expectedCost (meanMechanism (Function.update (![0, 1, 1] : Fin 3 → ℝ) 0 (-2))) 0 = 0 := by
  simp only [meanMechanism, Mechanism.expectedCost_deterministic, mean_def, Fintype.card_fin]
  constructor
  · rw [Fin.sum_univ_three]
    norm_num [Real.dist_eq]
  · rw [Fin.sum_univ_three]
    norm_num [Function.update, Real.dist_eq]

/-- For even `n = 4`, averaging the two middle order statistics fails strategyproofness on
`![0, 1, 2, 3]` when agent `1` misreports `0`. -/
noncomputable def midpointMedian4 : Mechanism (Fin 4) ℝ :=
  Mechanism.deterministic fun x => (Fintype.orderStatistic x 1 + Fintype.orderStatistic x 2) / 2

theorem not_isStrategyProof_midpointMedian4 : ¬ midpointMedian4.IsStrategyProof := by
  rw [midpointMedian4, Mechanism.isStrategyProof_deterministic_iff]
  intro hsp
  let x : Fin 4 → ℝ := ![0, 1, 2, 3]
  have hx1 : Fintype.orderStatistic x 1 = 1 :=
    orderStatistic_fin_eq (n := 3) 1 rfl (by decide) (sLt := {0}) (sLe := {0, 1})
      (fun j => by fin_cases j <;> simp [x]) (fun j => by fin_cases j <;> simp [x])
      (by decide) (by decide)
  have hx2 : Fintype.orderStatistic x 2 = 2 :=
    orderStatistic_fin_eq (n := 3) 2 rfl (by decide) (sLt := {0, 1}) (sLe := {0, 1, 2})
      (fun j => by fin_cases j <;> (simp [x]; try norm_num))
      (fun j => by fin_cases j <;> (simp [x]; try norm_num))
      (by decide) (by decide)
  let x' : Fin 4 → ℝ := Function.update x 1 0
  have hx'1 : Fintype.orderStatistic x' 1 = 0 :=
    orderStatistic_fin_eq (n := 3) 1 (by simp [x']) (by decide) (sLt := ∅) (sLe := {0, 1})
      (fun j => by fin_cases j <;> simp [x', x]) (fun j => by fin_cases j <;> simp [x', x])
      (by decide) (by decide)
  have hx'2 : Fintype.orderStatistic x' 2 = 2 :=
    orderStatistic_fin_eq (n := 3) 2 (by simp [x', x]) (by decide)
      (sLt := {0, 1}) (sLe := {0, 1, 2})
      (fun j => by fin_cases j <;> (simp [x', x]; try norm_num))
      (fun j => by fin_cases j <;> (simp [x', x]; try norm_num))
      (by decide) (by decide)
  have hle := hsp x 1 0
  change dist (x 1) ((Fintype.orderStatistic x 1 + Fintype.orderStatistic x 2) / 2) ≤
    dist (x 1) ((Fintype.orderStatistic x' 1 + Fintype.orderStatistic x' 2) / 2) at hle
  rw [hx1, hx2, hx'1, hx'2] at hle
  have hx1val : x 1 = 1 := rfl
  rw [hx1val, Real.dist_eq, Real.dist_eq] at hle
  norm_num at hle

/-! ### Dictatorship and random dictatorship -/

example : (dictatorship (ι := Fin 3) (G := ℝ) 0).IsGroupStrategyProof :=
  dictatorship_isGroupStrategyProof 0

example : (dictatorship (ι := Fin 3) (G := ℝ) 0).HasApproxRatio 2 := by
  have h := dictatorship_hasApproxRatio_card_sub_one (ι := Fin 3) (G := ℝ) (by decide) 0
  rw [Fintype.card_fin] at h
  norm_num at h
  exact h

example {α : ℝ} (h : (dictatorship (ι := Fin 3) (G := ℝ) 0).HasApproxRatio α) : 2 ≤ α := by
  have hα1 : 1 ≤ α := h.one_le (ι := Fin 3) (by decide)
  have hx := h (![0, 10, 10] : Fin 3 → ℝ)
  have hsc :
      expectedSocialECost (dictatorship (ι := Fin 3) (G := ℝ) 0 ![0, 10, 10]) ![0, 10, 10] =
        ENNReal.ofReal 20 := by
    rw [dictatorship, expectedSocialECost_eq_ofReal_expectedSocialCost
        (fun i => Mechanism.hasFiniteCost_deterministic _ _ _),
      Mechanism.expectedSocialCost_deterministic, socialCost, Fin.sum_univ_three]
    norm_num [Real.dist_eq]
  have hopt : optSocialECost (![0, 10, 10] : Fin 3 → ℝ) = ENNReal.ofReal 10 := by
    have hmed : Fintype.lowerMedian (![0, 10, 10] : Fin 3 → ℝ) = 10 := by
      rw [Fintype.lowerMedian_def]
      exact orderStatistic_fin_eq (n := 2) 1 (by norm_num) (by decide)
        (sLt := {0}) (sLe := {0, 1, 2})
        (fun j => by fin_cases j <;> simp) (fun j => by fin_cases j <;> simp)
        (by decide) (by decide)
    rw [optSocialECost_eq_ofReal_optSocialCost,
      ← (lowerMedian_isOptimal (![0, 10, 10] : Fin 3 → ℝ)).socialCost_eq_optSocialCost,
      hmed, socialCost, Fin.sum_univ_three]
    norm_num [Real.dist_eq]
  rw [hsc, hopt, ← ENNReal.ofReal_mul (le_trans zero_le_one hα1),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (le_trans zero_le_one hα1) (by norm_num))] at hx
  linarith

example : (randomDictatorship (ι := Fin 3) (G := ℝ)).IsStrategyProof :=
  randomDictatorship_isStrategyProof

example : (randomDictatorship (ι := Fin 3) (G := ℝ)).HasApproxRatio (4 / 3) := by
  have h := randomDictatorship_hasApproxRatio (ι := Fin 3) (G := ℝ)
  have hval : (2 : ℝ) - 2 / (Fintype.card (Fin 3) : ℝ) = 4 / 3 := by
    rw [Fintype.card_fin]
    norm_num
  exact hval ▸ h

/-- Random dictatorship on `ℝ` fails strong group strategyproofness: on `![0, 1, 2]`, the grand
coalition reporting `![1, 1, 1]` strictly lowers agent `1`'s expected cost from `2/3` to `0` while
keeping agents `0` and `2` at `1`. -/
theorem not_isGroupStrategyProof_randomDictatorship_real :
    ¬ (randomDictatorship (ι := Fin 3) (G := ℝ)).IsGroupStrategyProof := by
  intro hgsp
  let x : Fin 3 → ℝ := ![0, 1, 2]
  let z : Fin 3 → ℝ := ![1, 1, 1]
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      expectedECost (randomDictatorship (Finset.univ.piecewise z x)) (x i) ≤
        expectedECost (randomDictatorship x) (x i) := by
    intro i _
    rw [expectedECost_le_iff_expectedCost_le
        (randomDictatorship_hasFiniteCost _ _) (randomDictatorship_hasFiniteCost _ _),
      expectedCost_randomDictatorship, expectedCost_randomDictatorship, Finset.piecewise_univ,
      Fintype.card_fin, Fin.sum_univ_three, Fin.sum_univ_three]
    fin_cases i <;> norm_num [x, z, Real.dist_eq]
  have hlt : expectedECost (randomDictatorship ((Finset.univ : Finset (Fin 3)).piecewise z x))
      (x 1) < expectedECost (randomDictatorship x) (x 1) := by
    rw [← not_le, expectedECost_le_iff_expectedCost_le
        (randomDictatorship_hasFiniteCost _ _) (randomDictatorship_hasFiniteCost _ _),
      not_le, expectedCost_randomDictatorship, expectedCost_randomDictatorship,
      Finset.piecewise_univ, Fintype.card_fin, Fin.sum_univ_three, Fin.sum_univ_three]
    norm_num [x, z, Real.dist_eq]
  exact hgsp x z Finset.univ ⟨hle, 1, Finset.mem_univ 1, hlt⟩

/-- Four-point star metric space: three leaves `a`, `b`, `c` at pairwise distance `1` and center
`center` at distance `1/2` from every leaf. -/
inductive Star4 : Type
  | center
  | a
  | b
  | c
  deriving DecidableEq

namespace Star4

noncomputable instance : Dist Star4 where
  dist x y := if x = y then 0 else if x = .center ∨ y = .center then 1 / 2 else 1

noncomputable instance : MetricSpace Star4 where
  dist_self x := by simp [dist]
  dist_comm x y := by
    simp only [dist]
    by_cases h : x = y
    · subst h; simp
    · simp [h, Ne.symm h, or_comm]
  dist_triangle x y z := by
    rcases x <;> rcases y <;> rcases z <;> norm_num [dist]
  eq_of_dist_eq_zero {x y} h := by
    rcases x <;> rcases y <;> first | rfl | (exfalso; norm_num [dist] at h)

noncomputable instance : MeasurableSpace Star4 := borel Star4

instance : BorelSpace Star4 := ⟨rfl⟩

end Star4

/-- Random dictatorship fails weak group strategyproofness on `Star4`: when three agents occupy the
leaves `(a, b, c)`, every agent has expected cost `2/3`, whereas all three reporting `center` gives
every agent expected cost `1/2 < 2/3`. -/
theorem not_isWeakGroupStrategyProof_randomDictatorship_star4 :
    ¬ (randomDictatorship (ι := Fin 3) (G := Star4)).IsWeakGroupStrategyProof := by
  intro hwsp
  let x : Fin 3 → Star4 := ![.a, .b, .c]
  let z : Fin 3 → Star4 := ![.center, .center, .center]
  obtain ⟨i, _, hi⟩ := hwsp x z Finset.univ ⟨0, Finset.mem_univ 0⟩
  rw [expectedECost_le_iff_expectedCost_le
      (randomDictatorship_hasFiniteCost _ _) (randomDictatorship_hasFiniteCost _ _),
    expectedCost_randomDictatorship, expectedCost_randomDictatorship, Finset.piecewise_univ,
    Fintype.card_fin, Fin.sum_univ_three, Fin.sum_univ_three] at hi
  fin_cases i <;> norm_num [x, z, dist] at hi

/-! ### Continuous `ProbabilityMeasure ℝ` client and constant mechanism -/

private noncomputable def uniformUnit : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Set.Icc (0 : ℝ) 1), ⟨by simp⟩⟩

example : HasFiniteCost uniformUnit := by
  intro a
  exact (continuous_const.dist continuous_id).continuousOn.integrableOn_Icc

example :
    expectedCost uniformUnit (1 / 2 : ℝ) = 1 / 4 ∧
      expectedECost uniformUnit (1 / 2 : ℝ) = ENNReal.ofReal (1 / 4) := by
  have hfin : Integrable (fun y : ℝ => dist (1 / 2 : ℝ) y) (uniformUnit : Measure ℝ) :=
    (continuous_const.dist continuous_id).continuousOn.integrableOn_Icc
  have hcost : expectedCost uniformUnit (1 / 2 : ℝ) = 1 / 4 := by
    change ∫ y in Set.Icc (0 : ℝ) 1, |1 / 2 - y| = 1 / 4
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (f := fun y : ℝ => |1 / 2 - y|) (a := 0) (b := 1 / 2) (c := 1)
      ((continuous_const.sub continuous_id).abs.intervalIntegrable (μ := volume) 0 (1 / 2))
      ((continuous_const.sub continuous_id).abs.intervalIntegrable (μ := volume) (1 / 2) 1)
    have hleft : ∫ y in (0 : ℝ)..(1 / 2), |1 / 2 - y| = 1 / 8 := by
      have hcongr : Set.EqOn (fun y : ℝ => |1 / 2 - y|) (fun y : ℝ => 1 / 2 - y)
          (Set.uIcc 0 (1 / 2)) := by
        intro y hy
        dsimp only
        rw [Set.uIcc_of_le (by norm_num)] at hy
        exact abs_of_nonneg (by linarith [hy.2])
      rw [intervalIntegral.integral_congr hcongr,
        intervalIntegral.integral_sub (f := fun _ : ℝ => (1 / 2 : ℝ)) (g := fun x : ℝ => x)
          (continuous_const.intervalIntegrable 0 (1 / 2))
          (continuous_id.intervalIntegrable 0 (1 / 2)),
        intervalIntegral.integral_const, integral_id]
      norm_num
    have hright : ∫ y in (1 / 2 : ℝ)..1, |1 / 2 - y| = 1 / 8 := by
      have hcongr : Set.EqOn (fun y : ℝ => |1 / 2 - y|) (fun y : ℝ => y - 1 / 2)
          (Set.uIcc (1 / 2) 1) := by
        intro y hy
        dsimp only
        rw [Set.uIcc_of_le (by norm_num)] at hy
        rw [abs_of_nonpos (by linarith [hy.1]), neg_sub]
      rw [intervalIntegral.integral_congr hcongr,
        intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun _ : ℝ => (1 / 2 : ℝ))
          (continuous_id.intervalIntegrable (1 / 2) 1)
          (continuous_const.intervalIntegrable (1 / 2) 1),
        integral_id, intervalIntegral.integral_const]
      norm_num
    linarith
  have hecost : expectedECost uniformUnit (1 / 2 : ℝ) = ENNReal.ofReal (1 / 4) := by
    rw [expectedECost_eq_ofReal_expectedCost hfin, hcost]
  exact ⟨hcost, hecost⟩

/-- Constant mechanism at `0`: strongly group strategyproof, yet fails every finite approximation
ratio. -/
noncomputable def constantZero2 : Mechanism (Fin 2) ℝ :=
  Mechanism.deterministic fun _ => 0

example : constantZero2.IsGroupStrategyProof := by
  rw [constantZero2, Mechanism.isGroupStrategyProof_deterministic_iff]
  rintro x z A ⟨_, i, _, hlt⟩
  exact (lt_irrefl _ hlt).elim

example (α : ℝ) : ¬ constantZero2.HasApproxRatio α := by
  intro h
  have hx := h (![1, 1] : Fin 2 → ℝ)
  have hsc : expectedSocialECost (constantZero2 ![1, 1]) ![1, 1] = ENNReal.ofReal 2 := by
    rw [constantZero2, expectedSocialECost_eq_ofReal_expectedSocialCost
        (fun i => Mechanism.hasFiniteCost_deterministic _ _ _),
      Mechanism.expectedSocialCost_deterministic, socialCost, Fin.sum_univ_two]
    norm_num [Real.dist_eq]
  have hopt : optSocialECost (![1, 1] : Fin 2 → ℝ) = 0 := by
    have hle : optSocialECost (![1, 1] : Fin 2 → ℝ) ≤ socialECost (![1, 1] : Fin 2 → ℝ) 1 :=
      optSocialECost_le_socialECost _ _
    have hzero : socialECost (![1, 1] : Fin 2 → ℝ) 1 = 0 := by
      simp [socialECost, Fin.sum_univ_two]
    exact le_zero_iff.1 (hle.trans_eq hzero)
  rw [hsc, hopt, mul_zero, le_zero_iff, ENNReal.ofReal_eq_zero] at hx
  norm_num at hx

example {M : Mechanism (Fin 2) ℝ} {α : ℝ} (h : M.HasApproxRatio α) : 1 ≤ α :=
  h.one_le (by decide)

end CslibFrontierTests.FacilityLocation
