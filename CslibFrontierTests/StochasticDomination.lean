/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Probability.StochasticDomination
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.Tactic.NormNum

/-!
# Checked clients for stochastic domination and Poisson-binomial bounds

Nonvacuous tests covering:
- first-order stochastic order on `Measure` and `PMF` (`ℕ`, `ℝ`, `Bool`), antisymmetry,
  strictness, `ProbabilityTheory.cdf` equivalence, and monotone expectation inequalities;
- concrete `poissonBinomial` computations, `ProbabilityTheory.binomial` specialization, and the
  negative-binomial waiting-time sum `∑' t, Bin(t, 1/2)(< 2) = 4`;
- finite-horizon adapted domination (`PMF.seqProcess`/`seqCount`, both full and
  active-before-target where a stopped kernel drops to `0` after reaching target `r = 1`);
- state-dependent non-i.i.d. Markov-kernel trajectories via `ProbabilityTheory.Kernel.traj` and
  `Kernel.trajMeasure`, including lower/upper envelopes, `r = 0` and `p = 1` boundary cases,
  and a target-stopped kernel whose success probability drops to `0` once `r = 2` successes
  are reached, yet satisfies `𝔼[τ_2] ≤ 4`.
-/

namespace CslibFrontierTests.StochasticDomination

open MeasureTheory ProbabilityTheory Cslib.Probability
open scoped BigOperators ENNReal unitInterval

private def mkUnit (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : I :=
  ⟨q, hq0, hq1⟩

private noncomputable def pZero : I := mkUnit 0 (by norm_num) (by norm_num)
private noncomputable def pThird : I := mkUnit (1 / 3) (by norm_num) (by norm_num)
private noncomputable def pHalf : I := mkUnit (1 / 2) (by norm_num) (by norm_num)
private noncomputable def pTwoThirds : I := mkUnit (2 / 3) (by norm_num) (by norm_num)
private noncomputable def pThreeFourths : I := mkUnit (3 / 4) (by norm_num) (by norm_num)
private noncomputable def pOne : I := mkUnit 1 (by norm_num) (by norm_num)

section BasicOrderTests

theorem pure_two_stochasticallyDominates_one :
    PMF.StochasticallyDominates (PMF.pure (2 : ℕ)) (PMF.pure 1) := by
  intro U hU
  by_cases h1 : (1 : ℕ) ∈ U
  · have h2 : (2 : ℕ) ∈ U := hU (by omega) h1
    simp [h1, h2]
  · simp [h1]

theorem pure_one_not_stochasticallyDominates_two :
    ¬ PMF.StochasticallyDominates (PMF.pure (1 : ℕ)) (PMF.pure 2) := by
  intro h
  have hle := h (Set.Ici 2) (IsUpperSet.Ici 2)
  rw [← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ measurableSet_Ici,
    ← PMF.toMeasure_apply_eq_toOuterMeasure_apply _ measurableSet_Ici,
    PMF.toMeasure_pure, PMF.toMeasure_pure,
    Measure.dirac_apply' _ measurableSet_Ici, Measure.dirac_apply' _ measurableSet_Ici] at hle
  simp at hle

theorem dirac_two_stochasticallyDominates_one :
    Cslib.Probability.StochasticallyDominates
      (Measure.dirac (2 : ℝ)) (Measure.dirac (1 : ℝ)) := by
  have h :
      Cslib.Probability.StochasticallyDominates
        ((Measure.dirac ((2 : ℝ), (1 : ℝ))).map Prod.fst)
        ((Measure.dirac ((2 : ℝ), (1 : ℝ))).map Prod.snd) :=
    StochasticallyDominates.of_coupling (by simp)
  simpa using h

theorem coin_threeFourths_stochasticallyDominates_half :
    Cslib.Probability.PMF.StochasticallyDominates
      (Cslib.Probability.PMF.coin pThreeFourths)
      (Cslib.Probability.PMF.coin pHalf) := by
  rw [Cslib.Probability.PMF.coin_stochasticallyDominates_iff]
  norm_num [pThreeFourths, pHalf, mkUnit]

theorem coin_half_not_stochasticallyDominates_threeFourths :
    ¬ Cslib.Probability.PMF.StochasticallyDominates
      (Cslib.Probability.PMF.coin pHalf)
      (Cslib.Probability.PMF.coin pThreeFourths) := by
  rw [Cslib.Probability.PMF.coin_stochasticallyDominates_iff]
  norm_num [pThreeFourths, pHalf, mkUnit]

theorem coin_expect_mono :
    (∑ b : Bool, ((Cslib.Probability.PMF.coin pHalf) b).toReal * if b then (1 : ℝ) else 0) ≤
      ∑ b : Bool,
        ((Cslib.Probability.PMF.coin pThreeFourths) b).toReal * if b then (1 : ℝ) else 0 := by
  have hdom :
      Cslib.Probability.PMF.StochasticallyDominates
        (Cslib.Probability.PMF.coin pThreeFourths)
        (Cslib.Probability.PMF.coin pHalf) :=
    Cslib.Probability.PMF.coin_stochasticallyDominates (by norm_num [pThreeFourths, pHalf, mkUnit])
  refine hdom.sum_toReal_mul_le fun a b hab => ?_
  cases a <;> cases b
  · exact le_rfl
  · norm_num
  · exact absurd hab (by decide)
  · exact le_rfl

theorem dirac_add_prod_stochasticallyDominates :
    Cslib.Probability.StochasticallyDominates
      (((Measure.dirac (2 : ℕ)).prod (Measure.dirac (1 : ℕ))).map fun p => p.1 + p.2)
      (((Measure.dirac (1 : ℕ)).prod (Measure.dirac (0 : ℕ))).map fun p => p.1 + p.2) := by
  refine StochasticallyDominates.add_prod ?_ ?_
  · intro U hUm hU
    by_cases h1 : (1 : ℕ) ∈ U
    · simp [Measure.dirac_apply' _ hUm, h1, hU (by omega : (1 : ℕ) ≤ 2) h1]
    · simp [Measure.dirac_apply' _ hUm, h1]
  · intro U hUm hU
    by_cases h0 : (0 : ℕ) ∈ U
    · simp [Measure.dirac_apply' _ hUm, h0, hU (by omega : (0 : ℕ) ≤ 1) h0]
    · simp [Measure.dirac_apply' _ hUm, h0]

theorem real_cdf_le_of_stochasticallyDominates {μ ν : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : Cslib.Probability.StochasticallyDominates μ ν) (x : ℝ) :
    ProbabilityTheory.cdf μ x ≤ ProbabilityTheory.cdf ν x :=
  (Cslib.Probability.stochasticallyDominates_real_iff_cdf.mp h) x

end BasicOrderTests

section PoissonBinomialTests

theorem poissonBinomial_half_third_zero :
    (Cslib.Probability.PMF.poissonBinomial [pHalf, pThird] 0).toReal = 1 / 3 := by
  rw [Cslib.Probability.PMF.poissonBinomial_cons_zero_toReal,
    Cslib.Probability.PMF.poissonBinomial_cons_zero_toReal,
    Cslib.Probability.PMF.poissonBinomial_nil, PMF.pure_apply]
  norm_num [pHalf, pThird, mkUnit]

theorem poissonBinomial_half_third_one :
    (Cslib.Probability.PMF.poissonBinomial [pHalf, pThird] 1).toReal = 1 / 2 := by
  rw [Cslib.Probability.PMF.poissonBinomial_cons_succ_toReal,
    Cslib.Probability.PMF.poissonBinomial_cons_succ_toReal,
    Cslib.Probability.PMF.poissonBinomial_cons_zero_toReal,
    Cslib.Probability.PMF.poissonBinomial_nil]
  simp only [PMF.pure_apply, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ENNReal.toReal_zero, ENNReal.toReal_one]
  norm_num [pHalf, pThird, mkUnit]

theorem poissonBinomial_half_third_two :
    (Cslib.Probability.PMF.poissonBinomial [pHalf, pThird] 2).toReal = 1 / 6 := by
  rw [Cslib.Probability.PMF.poissonBinomial_cons_succ_toReal,
    Cslib.Probability.PMF.poissonBinomial_cons_succ_toReal,
    Cslib.Probability.PMF.poissonBinomial_cons_succ_toReal,
    Cslib.Probability.PMF.poissonBinomial_nil]
  simp only [PMF.pure_apply, ↓reduceIte, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ENNReal.toReal_zero, ENNReal.toReal_one]
  norm_num [pHalf, pThird, mkUnit]

theorem poissonBinomial_half_third_three :
    Cslib.Probability.PMF.poissonBinomial [pHalf, pThird] 3 = 0 :=
  Cslib.Probability.PMF.poissonBinomial_eq_zero_of_lt (by decide)

theorem poissonBinomial_half_third_perm :
    Cslib.Probability.PMF.poissonBinomial [pHalf, pThird] =
      Cslib.Probability.PMF.poissonBinomial [pThird, pHalf] :=
  Cslib.Probability.PMF.poissonBinomial_perm (List.Perm.swap pThird pHalf [])

theorem poissonBinomial_half_half_eq_binomial :
    (Cslib.Probability.PMF.poissonBinomial [pHalf, pHalf]).toMeasure =
      ProbabilityTheory.binomial 2 pHalf := by
  simpa using Cslib.Probability.PMF.toMeasure_poissonBinomial_replicate 2 pHalf

theorem binomial_three_threeFourths_dom_two_half :
    Cslib.Probability.StochasticallyDominates
      (ProbabilityTheory.binomial 3 pThreeFourths)
      (ProbabilityTheory.binomial 2 pHalf) :=
  (Cslib.Probability.binomial_stochasticallyDominates_of_le 3
    (by norm_num [pHalf, pThreeFourths, mkUnit])).trans
    (Cslib.Probability.binomial_stochasticallyDominates_of_nat_le (by omega) pHalf)

theorem tsum_binomial_two_half :
    ∑' t : ℕ, (ProbabilityTheory.binomial t pHalf).real (Set.Iio 2) = 4 := by
  rw [Cslib.Probability.tsum_binomial_real_Iio 2 (by norm_num [pHalf, mkUnit])]
  norm_num [pHalf, mkUnit]

end PoissonBinomialTests

section SequentialPMFTests

private noncomputable def depStep (t : ℕ) (h : Fin t → Bool) : PMF Bool :=
  match t with
  | 0 => Cslib.Probability.PMF.coin pHalf
  | 1 => Cslib.Probability.PMF.coin (if h ⟨0, by omega⟩ then pThreeFourths else pHalf)
  | _ + 2 => Cslib.Probability.PMF.coin pHalf

private def depEvent (t : ℕ) (_ : Fin t → Bool) : Set Bool :=
  {true}

theorem seqCount_dep_stochasticallyDominates :
    Cslib.Probability.PMF.StochasticallyDominates
      ((Cslib.Probability.PMF.seqProcess depStep [pHalf, pHalf].length).map
        (Cslib.Probability.PMF.seqCount depEvent [pHalf, pHalf].length))
      (Cslib.Probability.PMF.poissonBinomial [pHalf, pHalf]) := by
  refine Cslib.Probability.PMF.seqCount_stochasticallyDominates_poissonBinomial
    depStep depEvent [pHalf, pHalf] fun t ht h => ?_
  rcases t with _ | _ | t
  · simp [depStep, depEvent, Cslib.Probability.PMF.coin_apply, pHalf, mkUnit]
  · simp only [depStep, depEvent]
    split_ifs <;>
      norm_num [Cslib.Probability.PMF.coin_apply, pHalf, pThreeFourths, mkUnit]
  · simp only [List.length_cons, List.length_nil] at ht
    omega

private noncomputable def stopStep (t : ℕ) (h : Fin t → Bool) : PMF Bool :=
  if Cslib.Probability.PMF.seqCount depEvent t h < 1 then
    Cslib.Probability.PMF.coin pHalf
  else
    Cslib.Probability.PMF.coin pZero

theorem seqCount_stop_active_Iio_le :
    (((Cslib.Probability.PMF.seqProcess stopStep 2).map
        (Cslib.Probability.PMF.seqCount depEvent 2)).toOuterMeasure (Set.Iio 1)).toReal ≤
      (ProbabilityTheory.binomial 2 pHalf).real (Set.Iio 1) := by
  refine Cslib.Probability.PMF.seqCount_active_toReal_Iio_le stopStep depEvent 2 1 pHalf
    fun t _ h hlt => ?_
  simp only [stopStep, depEvent, hlt, ↓reduceIte]
  rw [show (Cslib.Probability.PMF.coin pHalf).toOuterMeasure {true} =
      (Cslib.Probability.PMF.coin pHalf) true from by simp]
  simp [Cslib.Probability.PMF.coin_apply, pHalf, mkUnit]

end SequentialPMFTests

section KernelTrajAndStoppingTests

private abbrev BoolSeq : ℕ → Type := fun _ => Bool

private noncomputable def boolMarkovKernel (qLo qHi : I) (n : ℕ) :
    Kernel (Π i : Finset.Iic n, BoolSeq i) (BoolSeq (n + 1)) where
  toFun h := (Cslib.Probability.PMF.coin
    (if h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ then qHi else qLo)).toMeasure
  measurable' := Measurable.of_discrete

private instance boolMarkovKernel_isMarkov (qLo qHi : I) (n : ℕ) :
    IsMarkovKernel (boolMarkovKernel qLo qHi n) where
  isProbabilityMeasure h := by
    dsimp [boolMarkovKernel]
    infer_instance

private theorem traj_apply_succ_true
    (κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, BoolSeq i) (BoolSeq (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] (m : ℕ) (z : Π i : Finset.Iic m, BoolSeq i) :
    (Kernel.traj κ m z) {x : Π n, BoolSeq n | x (m + 1) = true} = κ m z {true} := by
  let B : Set (Π i : Finset.Iic (m + 1), BoolSeq i) :=
    {y | y ⟨m + 1, Finset.mem_Iic.mpr le_rfl⟩ = true}
  have hBm : MeasurableSet B := MeasurableSet.of_discrete
  have hpre : Preorder.frestrictLe (m + 1) ⁻¹' B =
      {x : Π n, BoolSeq n | x (m + 1) = true} := rfl
  rw [← hpre, ← Measure.map_apply (Preorder.measurable_frestrictLe (m + 1)) hBm,
    ← Kernel.map_apply _ (Preorder.measurable_frestrictLe (m + 1)),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_succ_self,
    Kernel.map_apply _ (Measurable.of_discrete),
    Measure.map_apply (Measurable.of_discrete) hBm,
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_apply (Measurable.of_discrete) MeasurableSet.of_discrete,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton m).measurable,
    Measure.map_apply (MeasurableEquiv.piSingleton m).measurable MeasurableSet.of_discrete]
  have hpre2 :
      (MeasurableEquiv.piSingleton m) ⁻¹'
        (Prod.mk z ⁻¹' (IicProdIoc m (m + 1) ⁻¹' B)) = ({true} : Set Bool) := by
    ext b
    simp [B, IicProdIoc, MeasurableEquiv.piSingleton]
  rw [hpre2]

private def succTrueEvent (k : ℕ) : Set (Π n, BoolSeq n) :=
  {x | x (k + 1) = true}

private theorem measurableSet_succTrueEvent (k : ℕ) :
    MeasurableSet[Filtration.piLE (X := BoolSeq) (k + 1)] (succTrueEvent k) := by
  rw [Filtration.piLE_eq_comap_frestrictLe (X := BoolSeq)]
  exact ⟨{y | y ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩ = true},
    MeasurableSet.of_discrete, rfl⟩

private theorem boolMarkovKernel_traj_real (qLo qHi : I) (m : ℕ) (x : Π n, BoolSeq n) :
    (Kernel.traj (X := BoolSeq) (boolMarkovKernel qLo qHi) m (Preorder.frestrictLe m x)).real
        (succTrueEvent m) =
      if Preorder.frestrictLe m x ⟨m, Finset.mem_Iic.mpr le_rfl⟩ then (qHi : ℝ) else qLo := by
  rw [measureReal_def, succTrueEvent, traj_apply_succ_true]
  dsimp [boolMarkovKernel]
  split_ifs with hcond <;>
    simp [hcond, Cslib.Probability.PMF.coin_apply, ENNReal.toReal_ofReal (unitInterval.nonneg _)]

private def histCount (n : ℕ) (h : Π i : Finset.Iic n, BoolSeq i) : ℕ :=
  ∑ t : Fin n, if h ⟨t.1 + 1, Finset.mem_Iic.mpr t.isLt⟩ then 1 else 0

private theorem histCount_frestrictLe (n : ℕ) (x : Π i, BoolSeq i) :
    histCount n (Preorder.frestrictLe n x) = adaptedCount succTrueEvent n x := by
  rw [histCount, adaptedCount, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hx : x (s.1 + 1) = true <;> simp [succTrueEvent, Preorder.frestrictLe, hx]

private noncomputable def stopCountKernel (r : ℕ) (qLo qHi : I) (n : ℕ) :
    Kernel (Π i : Finset.Iic n, BoolSeq i) (BoolSeq (n + 1)) where
  toFun h :=
    (Cslib.Probability.PMF.coin (if histCount n h < r then
      (if h ⟨n, Finset.mem_Iic.mpr le_rfl⟩ then qHi else qLo) else pZero)).toMeasure
  measurable' := Measurable.of_discrete

private instance stopCountKernel_isMarkov (r : ℕ) (qLo qHi : I) (n : ℕ) :
    IsMarkovKernel (stopCountKernel r qLo qHi n) where
  isProbabilityMeasure h := by
    dsimp [stopCountKernel]
    infer_instance

private theorem stopCountKernel_ge_of_lt {r : ℕ} {qLo qHi : I} (hle : (qLo : ℝ) ≤ qHi)
    {n : ℕ} {h : Π i : Finset.Iic n, BoolSeq i} (hlt : histCount n h < r) :
    (qLo : ℝ) ≤ ((stopCountKernel r qLo qHi n h) {true}).toReal := by
  dsimp [stopCountKernel]
  rw [PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    Cslib.Probability.PMF.coin_apply]
  simp only [↓reduceIte, hlt, ENNReal.toReal_ofReal (unitInterval.nonneg _)]
  cases h ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  · simp
  · simpa using hle

theorem traj_noniid_lower_dom (z₀ : Π i : Finset.Iic 0, BoolSeq i) :
    StochasticallyDominates
      ((Kernel.traj (X := BoolSeq) (boolMarkovKernel pHalf pThreeFourths) 0 z₀).map
        (adaptedCount succTrueEvent [pHalf, pHalf].length))
      (Cslib.Probability.PMF.poissonBinomial [pHalf, pHalf]).toMeasure := by
  refine traj_adaptedCount_stochasticallyDominates_poissonBinomial (X := BoolSeq)
    (boolMarkovKernel pHalf pThreeFourths) z₀
    (fun t => by rw [Nat.zero_add]; exact measurableSet_succTrueEvent t) [pHalf, pHalf]
    fun t ht => ?_
  refine ae_of_all _ fun x => ?_
  rw [Nat.zero_add, boolMarkovKernel_traj_real]
  rcases t with _ | _ | t
  · split_ifs <;> norm_num [pHalf, pThreeFourths, mkUnit]
  · split_ifs <;> norm_num [pHalf, pThreeFourths, mkUnit]
  · simp only [List.length_cons, List.length_nil] at ht
    omega

theorem traj_noniid_upper_dom (z₀ : Π i : Finset.Iic 0, BoolSeq i) :
    StochasticallyDominates
      (Cslib.Probability.PMF.poissonBinomial [pThreeFourths, pThreeFourths]).toMeasure
      ((Kernel.traj (X := BoolSeq) (boolMarkovKernel pHalf pThreeFourths) 0 z₀).map
        (adaptedCount succTrueEvent [pThreeFourths, pThreeFourths].length)) := by
  refine poissonBinomial_stochasticallyDominates_traj_adaptedCount (X := BoolSeq)
    (boolMarkovKernel pHalf pThreeFourths) z₀
    (fun t => by rw [Nat.zero_add]; exact measurableSet_succTrueEvent t)
    [pThreeFourths, pThreeFourths] fun t ht => ?_
  refine ae_of_all _ fun x => ?_
  rw [Nat.zero_add, boolMarkovKernel_traj_real]
  rcases t with _ | _ | t
  · split_ifs <;> norm_num [pHalf, pThreeFourths, mkUnit]
  · split_ifs <;> norm_num [pHalf, pThreeFourths, mkUnit]
  · simp only [List.length_cons, List.length_nil] at ht
    omega

theorem trajMeasure_noniid_lower_dom :
    StochasticallyDominates
      ((Kernel.trajMeasure (X := BoolSeq) (Cslib.Probability.PMF.coin pTwoThirds).toMeasure
          (boolMarkovKernel pHalf pThreeFourths)).map
        (adaptedCount succTrueEvent [pHalf, pHalf].length))
      (Cslib.Probability.PMF.poissonBinomial [pHalf, pHalf]).toMeasure := by
  refine trajMeasure_adaptedCount_stochasticallyDominates_poissonBinomial (X := BoolSeq)
    (Cslib.Probability.PMF.coin pTwoThirds).toMeasure (boolMarkovKernel pHalf pThreeFourths)
    measurableSet_succTrueEvent [pHalf, pHalf] fun t ht => ?_
  refine ae_of_all _ fun x => ?_
  rw [boolMarkovKernel_traj_real]
  rcases t with _ | _ | t
  · split_ifs <;> norm_num [pHalf, pThreeFourths, mkUnit]
  · split_ifs <;> norm_num [pHalf, pThreeFourths, mkUnit]
  · simp only [List.length_cons, List.length_nil] at ht
    omega

theorem traj_hittingTime_zero_target (z₀ : Π i : Finset.Iic 0, BoolSeq i) :
    (∀ᵐ x ∂Kernel.traj (X := BoolSeq) (boolMarkovKernel pHalf pThreeFourths) 0 z₀,
      countHittingTime succTrueEvent 0 x ≠ ⊤) ∧
    Integrable (fun x => (((countHittingTime succTrueEvent 0 x).untopD 0 : ℕ) : ℝ))
      (Kernel.traj (X := BoolSeq) (boolMarkovKernel pHalf pThreeFourths) 0 z₀) ∧
    ∫ x, (((countHittingTime succTrueEvent 0 x).untopD 0 : ℕ) : ℝ)
      ∂Kernel.traj (X := BoolSeq) (boolMarkovKernel pHalf pThreeFourths) 0 z₀ ≤ 0 := by
  have h := traj_countHittingTime_mean_le (X := BoolSeq)
    (boolMarkovKernel pHalf pThreeFourths) z₀
    (fun t => by rw [Nat.zero_add]; exact measurableSet_succTrueEvent t) (r := 0) (p := pOne)
    (by norm_num [pOne, mkUnit]) fun t => by
      have hempty : {x : Π n, BoolSeq n | adaptedCount succTrueEvent t x < 0} = ∅ := by
        ext x
        simp
      rw [hempty, Measure.restrict_empty]
      simp
  simpa [pOne, mkUnit] using h

theorem traj_hittingTime_prob_one (z₀ : Π i : Finset.Iic 0, BoolSeq i) :
    (∀ᵐ x ∂Kernel.traj (X := BoolSeq) (boolMarkovKernel pOne pOne) 0 z₀,
      countHittingTime succTrueEvent 2 x ≠ ⊤) ∧
    Integrable (fun x => (((countHittingTime succTrueEvent 2 x).untopD 0 : ℕ) : ℝ))
      (Kernel.traj (X := BoolSeq) (boolMarkovKernel pOne pOne) 0 z₀) ∧
    ∫ x, (((countHittingTime succTrueEvent 2 x).untopD 0 : ℕ) : ℝ)
      ∂Kernel.traj (X := BoolSeq) (boolMarkovKernel pOne pOne) 0 z₀ ≤ 2 := by
  have h := traj_countHittingTime_mean_le (X := BoolSeq)
    (boolMarkovKernel pOne pOne) z₀
    (fun t => by rw [Nat.zero_add]; exact measurableSet_succTrueEvent t) (r := 2) (p := pOne)
    (by norm_num [pOne, mkUnit]) fun t => ae_of_all _ fun x => by
      rw [Nat.zero_add, boolMarkovKernel_traj_real]
      split_ifs <;> norm_num [pOne, mkUnit]
  simpa [pOne, mkUnit] using h

theorem trajMeasure_stopCount_hittingTime_mean_le :
    (∀ᵐ x ∂Kernel.trajMeasure (X := BoolSeq)
        (Cslib.Probability.PMF.coin pTwoThirds).toMeasure
        (stopCountKernel 2 pHalf pThreeFourths),
      countHittingTime succTrueEvent 2 x ≠ ⊤) ∧
    Integrable (fun x => (((countHittingTime succTrueEvent 2 x).untopD 0 : ℕ) : ℝ))
      (Kernel.trajMeasure (X := BoolSeq)
        (Cslib.Probability.PMF.coin pTwoThirds).toMeasure
        (stopCountKernel 2 pHalf pThreeFourths)) ∧
    ∫ x, (((countHittingTime succTrueEvent 2 x).untopD 0 : ℕ) : ℝ)
      ∂Kernel.trajMeasure (X := BoolSeq)
        (Cslib.Probability.PMF.coin pTwoThirds).toMeasure
        (stopCountKernel 2 pHalf pThreeFourths) ≤ 4 := by
  have h := trajMeasure_countHittingTime_mean_le (X := BoolSeq)
    (Cslib.Probability.PMF.coin pTwoThirds).toMeasure (stopCountKernel 2 pHalf pThreeFourths)
    measurableSet_succTrueEvent (r := 2) (p := pHalf)
    (by norm_num [pHalf, mkUnit]) fun t => ae_of_all _ fun x hlt => by
      rw [measureReal_def, succTrueEvent, traj_apply_succ_true]
      refine stopCountKernel_ge_of_lt (by norm_num [pHalf, pThreeFourths, mkUnit]) ?_
      rwa [histCount_frestrictLe]
  have hdiv : ((2 : ℕ) : ℝ) / (pHalf : ℝ) = 4 := by norm_num [pHalf, mkUnit]
  rwa [hdiv] at h

end KernelTrajAndStoppingTests

end CslibFrontierTests.StochasticDomination
