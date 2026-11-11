/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.MachineLearning.Replicable.Basic
public import CslibFrontier.Languages.Probabilistic.Basic
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import CslibFrontier.Languages.Probabilistic.Semantics
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.Order.Floor.BigOperators

/-!
# Randomized-threshold rounding rules

This module formalizes the randomized-threshold and periodic grid rounding primitives from
Impagliazzo–Lei–Pitassi–Sorrell [ImpagliazzoLeiPitassiSorrell2022]:

* **Bounded interval threshold rounding**: `thresholdRound a b N i x` compares a real statistic `x`
  against a discrete uniform grid threshold `thresholdValue a b N i ∈ [a, b)` for `i : Fin N`, and
  `continuousThresholdRound a b u x` is its continuous counterpart for `u ∈ [0, 1)`. Two inputs
  `x₁, x₂` disagree with probability at most `|x₁ - x₂| / (b - a) + 1 / N` discretely, and with
  Lebesgue measure at most `|x₁ - x₂| / (b - a)` continuously.
* **Periodic grid rounding**: `roundGrid w N i x` snaps an arbitrary real `x` to the midpoint of a
  randomly shifted interval of width `w` with discrete shift `i / N` (`i : Fin N`). Every rounded
  output lies within `w / 2` of `x` (`abs_roundGrid_sub_le`), and two inputs `x₁, x₂` land in
  different grid bins with probability at most `|x₁ - x₂| / w + 1 / N` (`roundGrid_disagree_le`,
  proved via Hermite's identity `Int.sum_floor_add_div`). The continuous counterpart
  `continuousRoundGrid w u x` has disagreement Lebesgue measure at most `|x₁ - x₂| / w`.
* **Replicable rounding of concentrating estimators**: any deterministic estimator `est` that
  concentrates within `δ` of `target D` except with probability `β` becomes both
  `(w / 2 + δ, β)`-accurate and `(2 * δ / w + 1 / N + 2 * β)`-replicable under `roundGridProg`.

## Main definitions

* `Cslib.MachineLearning.Replicable.thresholdValue`,
  `Cslib.MachineLearning.Replicable.thresholdRound`,
  `Cslib.MachineLearning.Replicable.thresholdProg`: discrete shared-seed threshold rounding.
* `Cslib.MachineLearning.Replicable.roundGridBin`, `Cslib.MachineLearning.Replicable.roundGrid`,
  `Cslib.MachineLearning.Replicable.roundGridProg`: periodic shared-seed grid rounding.
* `Cslib.MachineLearning.Replicable.continuousThresholdRound`,
  `Cslib.MachineLearning.Replicable.continuousRoundGridBin`,
  `Cslib.MachineLearning.Replicable.continuousRoundGrid`: continuous `[0, 1)` rounding rules.

## Main results

* `Cslib.MachineLearning.Replicable.thresholdRound_disagree_le`: discrete `[a, b)` threshold
  disagreement probability `≤ |x₁ - x₂| / (b - a) + 1 / N`.
* `Cslib.MachineLearning.Replicable.abs_roundGrid_sub_le`: `|roundGrid w N i x - x| ≤ w / 2`.
* `Cslib.MachineLearning.Replicable.roundGrid_disagree_le`: periodic grid rounding disagreement
  probability `≤ |x₁ - x₂| / w + 1 / N`.
* `Cslib.MachineLearning.Replicable.volume_thresholdRound_ne_le`,
  `Cslib.MachineLearning.Replicable.volume_roundGrid_ne_le`: continuous Lebesgue-measure rounding
  lemmas.
* `Cslib.MachineLearning.Replicable.isAccurateFor_roundGridProg_of_concentrates`,
  `Cslib.MachineLearning.Replicable.isReplicableFor_roundGridProg_of_concentrates`: turning any
  concentrating estimator into a replicable accurate `Program`.

## References

* [Impagliazzo, Lei, Pitassi, Sorrell (STOC 2022)][ImpagliazzoLeiPitassiSorrell2022],
  *Reproducibility in Learning* (paper PDF not directly inspected; rounding bounds and
  `MeasureTheory.volume` / `ProbComp` formulations are formalized directly in Lean).
-/

public section

namespace Cslib.MachineLearning.Replicable

section Definitions

/-- Grid threshold at index `i : Fin N` partitioning `[a, b)`. -/
@[expose] noncomputable def thresholdValue (a b : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  a + (b - a) * (i : ℝ) / N

/-- Randomized-threshold boolean rounding on `[a, b)` using shared discrete seed `i : Fin N`. -/
@[expose] noncomputable def thresholdRound (a b : ℝ) (N : ℕ) (i : Fin N) (x : ℝ) : Bool :=
  decide (thresholdValue a b N i ≤ x)

/-- `ProbComp`-backed ideal real-arithmetic threshold-rounding `Program` applied to a real
estimator `est` (interpreted via `Program.toAlgorithm`). -/
@[expose] noncomputable def thresholdProg {X : Type} {m : ℕ} (a b : ℝ) (N : ℕ) [NeZero N]
    (est : (Fin m → X) → ℝ) : Program X (Fin N) Bool m :=
  Program.deterministic (ProbComp.uniform (Fin N)) (fun S i => thresholdRound a b N i (est S))

/-- Periodic grid bin index of `x` with grid width `w` and discrete random phase `i : Fin N`. -/
@[expose] noncomputable def roundGridBin (w : ℝ) (N : ℕ) (i : Fin N) (x : ℝ) : ℤ :=
  ⌊x / w + (i : ℝ) / N⌋

/-- Periodic randomized grid rounding: snaps `x` to the midpoint of its shifted `w`-bin. -/
@[expose] noncomputable def roundGrid (w : ℝ) (N : ℕ) (i : Fin N) (x : ℝ) : ℝ :=
  ((roundGridBin w N i x : ℝ) + 1 / 2 - (i : ℝ) / N) * w

/-- `ProbComp`-backed ideal real-arithmetic periodic grid-rounding `Program` applied to a real
estimator `est` (interpreted via `Program.toAlgorithm`). -/
@[expose] noncomputable def roundGridProg {X : Type} {m : ℕ} (w : ℝ) (N : ℕ) [NeZero N]
    (est : (Fin m → X) → ℝ) : Program X (Fin N) ℝ m :=
  Program.deterministic (ProbComp.uniform (Fin N)) (fun S i => roundGrid w N i (est S))

/-- Continuous randomized-threshold boolean rounding on `[a, b]` using `u ∈ [0, 1)`. -/
@[expose] noncomputable def continuousThresholdRound (a b u x : ℝ) : Bool :=
  decide (a + (b - a) * u ≤ x)

/-- Continuous periodic grid bin index with width `w` and shift `u ∈ [0, 1)`. -/
@[expose] noncomputable def continuousRoundGridBin (w u x : ℝ) : ℤ :=
  ⌊x / w + u⌋

/-- Continuous periodic grid rounding with width `w` and shift `u ∈ [0, 1)`. -/
@[expose] noncomputable def continuousRoundGrid (w u x : ℝ) : ℝ :=
  ((continuousRoundGridBin w u x : ℝ) + 1 / 2 - u) * w

end Definitions

section DeterministicProperties

theorem thresholdRound_false_of_lt_left {a b : ℝ} (hab : a ≤ b) {N : ℕ} (i : Fin N) {x : ℝ}
    (hx : x < a) : thresholdRound a b N i x = false := by
  have hnonneg : 0 ≤ (b - a) * (i : ℝ) / N := by positivity [sub_nonneg.mpr hab]
  exact decide_eq_false (not_le.mpr (by unfold thresholdValue; linarith))

theorem thresholdRound_true_of_right_le {a b : ℝ} (hab : a ≤ b) {N : ℕ} (i : Fin N) {x : ℝ}
    (hx : b ≤ x) : thresholdRound a b N i x = true := by
  rcases eq_or_ne N 0 with rfl | hN
  · exact i.elim0
  · have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hle : (i : ℝ) / N ≤ 1 := (div_le_one hpos).mpr (by exact_mod_cast i.isLt.le)
    have hmul : (b - a) * ((i : ℝ) / N) ≤ b - a := mul_le_of_le_one_right (sub_nonneg.mpr hab) hle
    exact decide_eq_true (by
      unfold thresholdValue
      linarith [show (b - a) * (i : ℝ) / N = (b - a) * ((i : ℝ) / N) by ring])

/-- Deterministic discretization error of `roundGrid`: always within `w / 2` of `x`. -/
theorem abs_roundGrid_sub_le {w : ℝ} (hw : 0 < w) (N : ℕ) (i : Fin N) (x : ℝ) :
    |roundGrid w N i x - x| ≤ w / 2 := by
  let t : ℝ := x / w + (i : ℝ) / N
  have hdiff : roundGrid w N i x - x = ((⌊t⌋ : ℝ) + 1 / 2 - t) * w := by
    simp only [roundGrid, roundGridBin, t]
    field_simp [hw.ne']
    ring
  have ht : |(⌊t⌋ : ℝ) + 1 / 2 - t| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [Int.lt_floor_add_one t], by linarith [Int.floor_le t]⟩
  rw [hdiff, abs_mul, abs_of_pos hw]
  simpa only [one_div_mul_eq_div] using mul_le_mul_of_nonneg_right ht hw.le

/-- Deterministic discretization error of `continuousRoundGrid`: always within `w / 2` of `x`. -/
theorem abs_continuousRoundGrid_sub_le {w : ℝ} (hw : 0 < w) (u x : ℝ) :
    |continuousRoundGrid w u x - x| ≤ w / 2 := by
  let t : ℝ := x / w + u
  have hdiff : continuousRoundGrid w u x - x = ((⌊t⌋ : ℝ) + 1 / 2 - t) * w := by
    simp only [continuousRoundGrid, continuousRoundGridBin, t]
    field_simp [hw.ne']
    ring
  have ht : |(⌊t⌋ : ℝ) + 1 / 2 - t| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [Int.lt_floor_add_one t], by linarith [Int.floor_le t]⟩
  rw [hdiff, abs_mul, abs_of_pos hw]
  simpa only [one_div_mul_eq_div] using mul_le_mul_of_nonneg_right ht hw.le

end DeterministicProperties

section DiscreteDisagreement

private theorem thresholdRound_disagree_le_of_le {a b : ℝ} (hab : a < b) {N : ℕ} [NeZero N]
    {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) :
    ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure
      {i : Fin N | thresholdRound a b N i x₁ ≠ thresholdRound a b N i x₂}).toReal ≤
      (x₂ - x₁) / (b - a) + 1 / N := by
  classical
  rw [Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, Fintype.card_fin]
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hba : 0 < b - a := sub_pos.mpr hab
  let u₁ : ℝ := (N : ℝ) * (x₁ - a) / (b - a)
  let u₂ : ℝ := (N : ℝ) * (x₂ - a) / (b - a)
  have hu : u₁ ≤ u₂ := by
    dsimp only [u₁, u₂]
    gcongr
  have hevent :
      (Finset.univ.filter
        (· ∈ {i : Fin N | thresholdRound a b N i x₁ ≠ thresholdRound a b N i x₂})) =
      Finset.univ.filter fun i : Fin N =>
        thresholdRound a b N i x₁ ≠ thresholdRound a b N i x₂ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  rw [hevent]
  have hcard :
      (Finset.univ.filter fun i : Fin N =>
        thresholdRound a b N i x₁ ≠ thresholdRound a b N i x₂).card ≤
      (Finset.Ioc ⌊u₁⌋ ⌊u₂⌋).card := by
    refine Finset.card_le_card_of_injOn (fun i : Fin N => (i.1 : ℤ)) ?_ ?_
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      simp only [thresholdRound, ne_eq] at hi
      have hnot : ¬ (thresholdValue a b N i ≤ x₁ ↔ thresholdValue a b N i ≤ x₂) := by
        intro heq
        exact hi.2 (decide_eq_decide.mpr heq)
      have h1 : x₁ < thresholdValue a b N i := by
        by_contra hle
        rw [not_lt] at hle
        exact hnot ⟨fun _ => hle.trans hx, fun _ => hle⟩
      have h2 : thresholdValue a b N i ≤ x₂ := by
        by_contra hlt
        rw [not_le] at hlt
        exact hnot ⟨fun h => absurd (h.trans hx) (not_le.mpr hlt),
          fun h => absurd h (not_le.mpr hlt)⟩
      have hu1 : u₁ < ((i.1 : ℤ) : ℝ) := by
        dsimp only [u₁, thresholdValue] at h1 ⊢
        rw [div_lt_iff₀ hba]
        have h1' : (x₁ - a) * N < (b - a) * (i.1 : ℝ) :=
          (lt_div_iff₀ hN).mp (by linarith : x₁ - a < (b - a) * (i.1 : ℝ) / N)
        push_cast
        linarith
      have hu2 : ((i.1 : ℤ) : ℝ) ≤ u₂ := by
        dsimp only [u₂, thresholdValue] at h2 ⊢
        rw [le_div_iff₀ hba]
        have h2' : (b - a) * (i.1 : ℝ) ≤ (x₂ - a) * N :=
          (div_le_iff₀ hN).mp (by linarith : (b - a) * (i.1 : ℝ) / N ≤ x₂ - a)
        push_cast
        linarith
      exact Finset.mem_Ioc.mpr ⟨Int.floor_lt.mpr hu1, Int.le_floor.mpr hu2⟩
    · intro i _ j _ hij
      exact Fin.ext (Int.ofNat.inj hij)
  have hfloor : (⌊u₁⌋ : ℤ) ≤ ⌊u₂⌋ := Int.floor_mono hu
  have hcast : ((Finset.Ioc ⌊u₁⌋ ⌊u₂⌋).card : ℝ) ≤ (N : ℝ) * ((x₂ - x₁) / (b - a)) + 1 := by
    have hsz : ((Finset.Ioc ⌊u₁⌋ ⌊u₂⌋).card : ℤ) = ⌊u₂⌋ - ⌊u₁⌋ := by
      rw [Int.card_Ioc, Int.toNat_of_nonneg (sub_nonneg.mpr hfloor)]
    have hszR : ((Finset.Ioc ⌊u₁⌋ ⌊u₂⌋).card : ℝ) = (⌊u₂⌋ : ℝ) - (⌊u₁⌋ : ℝ) := by
      exact_mod_cast hsz
    rw [hszR]
    have hlt1 : u₁ - 1 < (⌊u₁⌋ : ℝ) := Int.sub_one_lt_floor u₁
    have hle2 : (⌊u₂⌋ : ℝ) ≤ u₂ := Int.floor_le u₂
    have hudiff : u₂ - u₁ = (N : ℝ) * ((x₂ - x₁) / (b - a)) := by
      dsimp only [u₁, u₂]
      ring
    linarith
  have hreal :
      ((Finset.univ.filter fun i : Fin N =>
        thresholdRound a b N i x₁ ≠ thresholdRound a b N i x₂).card : ℝ) ≤
      (N : ℝ) * ((x₂ - x₁) / (b - a)) + 1 :=
    (Nat.cast_le.mpr hcard).trans hcast
  rw [div_le_iff₀ hN]
  have hrhs : ((x₂ - x₁) / (b - a) + 1 / N) * N = (N : ℝ) * ((x₂ - x₁) / (b - a)) + 1 := by
    rw [add_mul, one_div_mul_cancel hN.ne']
    ring
  linarith

/-- **Discrete randomized-threshold rounding lemma** [ImpagliazzoLeiPitassiSorrell2022]: for any
`a < b` and `[NeZero N]`, two real numbers `x₁, x₂` thresholded against a shared uniform seed
`i : Fin N` on `[a, b)` disagree with probability at most `|x₁ - x₂| / (b - a) + 1 / N`. -/
theorem thresholdRound_disagree_le {a b : ℝ} (hab : a < b) {N : ℕ} [NeZero N] (x₁ x₂ : ℝ) :
    ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure
      {i : Fin N | thresholdRound a b N i x₁ ≠ thresholdRound a b N i x₂}).toReal ≤
      |x₁ - x₂| / (b - a) + 1 / N := by
  rcases le_total x₁ x₂ with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    exact thresholdRound_disagree_le_of_le hab hle
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    have heq : {i : Fin N | thresholdRound a b N i x₁ ≠ thresholdRound a b N i x₂} =
        {i : Fin N | thresholdRound a b N i x₂ ≠ thresholdRound a b N i x₁} := by
      ext i
      exact ne_comm
    rw [heq]
    exact thresholdRound_disagree_le_of_le hab hle

private theorem roundGrid_eq_iff_bin_eq {w : ℝ} (hw : 0 < w) {N : ℕ} (i : Fin N) (x₁ x₂ : ℝ) :
    roundGrid w N i x₁ = roundGrid w N i x₂ ↔ roundGridBin w N i x₁ = roundGridBin w N i x₂ := by
  constructor
  · intro h
    simp only [roundGrid] at h
    have h1 := mul_right_cancel₀ hw.ne' h
    have h2 : (roundGridBin w N i x₁ : ℝ) = (roundGridBin w N i x₂ : ℝ) := by linarith
    exact Int.cast_injective h2
  · intro h
    simp only [roundGrid, h]

private theorem roundGrid_disagree_le_of_le {w : ℝ} (hw : 0 < w) {N : ℕ} [NeZero N]
    {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) :
    ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure
      {i : Fin N | roundGrid w N i x₁ ≠ roundGrid w N i x₂}).toReal ≤
      (x₂ - x₁) / w + 1 / N := by
  classical
  rw [Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, Fintype.card_fin]
  have hevent :
      (Finset.univ.filter (· ∈ {i : Fin N | roundGrid w N i x₁ ≠ roundGrid w N i x₂})) =
      Finset.univ.filter fun i : Fin N => roundGrid w N i x₁ ≠ roundGrid w N i x₂ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  rw [hevent]
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hbin : ∀ i : Fin N, roundGridBin w N i x₁ ≤ roundGridBin w N i x₂ := fun i =>
    Int.floor_mono (by gcongr)
  have hcard :
      ((Finset.univ.filter fun i : Fin N =>
        roundGrid w N i x₁ ≠ roundGrid w N i x₂).card : ℤ) ≤
      ⌊(N : ℝ) * (x₂ / w)⌋ - ⌊(N : ℝ) * (x₁ / w)⌋ := by
    have hfilt :
        ((Finset.univ.filter fun i : Fin N =>
          roundGrid w N i x₁ ≠ roundGrid w N i x₂).card : ℤ) =
        ∑ i : Fin N, if roundGridBin w N i x₁ ≠ roundGridBin w N i x₂ then (1 : ℤ) else 0 := by
      have hcongr :
          (Finset.univ.filter fun i : Fin N => roundGrid w N i x₁ ≠ roundGrid w N i x₂) =
          (Finset.univ.filter fun i : Fin N => roundGridBin w N i x₁ ≠ roundGridBin w N i x₂) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
          roundGrid_eq_iff_bin_eq hw]
      rw [hcongr, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    rw [hfilt]
    have hle_sum :
        (∑ i : Fin N, if roundGridBin w N i x₁ ≠ roundGridBin w N i x₂ then (1 : ℤ) else 0) ≤
        ∑ i : Fin N, (roundGridBin w N i x₂ - roundGridBin w N i x₁) := by
      refine Finset.sum_le_sum fun i _ => ?_
      split_ifs with hne
      · exact Int.sub_pos.mpr (lt_of_le_of_ne (hbin i) hne)
      · exact sub_nonneg.mpr (hbin i)
    refine hle_sum.trans_eq ?_
    simp only [roundGridBin, Finset.sum_sub_distrib]
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ⌊x₂ / w + (i : ℝ) / N⌋) N,
      Fin.sum_univ_eq_sum_range (fun i : ℕ => ⌊x₁ / w + (i : ℝ) / N⌋) N,
      Int.sum_floor_add_div (x₂ / w) N, Int.sum_floor_add_div (x₁ / w) N]
  have hcast :
      ((Finset.univ.filter fun i : Fin N =>
        roundGrid w N i x₁ ≠ roundGrid w N i x₂).card : ℝ) ≤
      (N : ℝ) * ((x₂ - x₁) / w) + 1 := by
    have hcardR :
        ((Finset.univ.filter fun i : Fin N =>
          roundGrid w N i x₁ ≠ roundGrid w N i x₂).card : ℝ) ≤
        (⌊(N : ℝ) * (x₂ / w)⌋ : ℝ) - (⌊(N : ℝ) * (x₁ / w)⌋ : ℝ) := by
      exact_mod_cast hcard
    have h1 := Int.sub_one_lt_floor ((N : ℝ) * (x₁ / w))
    have h2 := Int.floor_le ((N : ℝ) * (x₂ / w))
    have hr : (N : ℝ) * (x₂ / w) - (N : ℝ) * (x₁ / w) = (N : ℝ) * ((x₂ - x₁) / w) := by ring
    linarith
  rw [div_le_iff₀ hN]
  have hrhs : ((x₂ - x₁) / w + 1 / N) * N = (N : ℝ) * ((x₂ - x₁) / w) + 1 := by
    rw [add_mul, one_div_mul_cancel hN.ne']
    ring
  linarith

/-- **Periodic grid rounding lemma** [ImpagliazzoLeiPitassiSorrell2022]: for any `w > 0` and
`[NeZero N]`, two real numbers `x₁, x₂` fall into different bins of `roundGrid w N` under a
uniform shared seed `i : Fin N` with probability at most `|x₁ - x₂| / w + 1 / N`. -/
theorem roundGrid_disagree_le {w : ℝ} (hw : 0 < w) {N : ℕ} [NeZero N] (x₁ x₂ : ℝ) :
    ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure
      {i : Fin N | roundGrid w N i x₁ ≠ roundGrid w N i x₂}).toReal ≤
      |x₁ - x₂| / w + 1 / N := by
  rcases le_total x₁ x₂ with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    exact roundGrid_disagree_le_of_le hw hle
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    have heq : {i : Fin N | roundGrid w N i x₁ ≠ roundGrid w N i x₂} =
        {i : Fin N | roundGrid w N i x₂ ≠ roundGrid w N i x₁} := by
      ext i
      exact ne_comm
    rw [heq]
    exact roundGrid_disagree_le_of_le hw hle

end DiscreteDisagreement

section ContinuousDisagreement

private theorem volume_thresholdRound_ne_le_of_le {a b : ℝ} (hab : a < b) {x₁ x₂ : ℝ}
    (hx : x₁ ≤ x₂) :
    MeasureTheory.volume
      {u ∈ Set.Ico (0 : ℝ) 1 |
        continuousThresholdRound a b u x₁ ≠ continuousThresholdRound a b u x₂} ≤
      ENNReal.ofReal ((x₂ - x₁) / (b - a)) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hsub :
      {u ∈ Set.Ico (0 : ℝ) 1 |
        continuousThresholdRound a b u x₁ ≠ continuousThresholdRound a b u x₂} ⊆
      Set.Ioc ((x₁ - a) / (b - a)) ((x₂ - a) / (b - a)) := by
    intro u hu
    simp only [Set.mem_ofPred_eq, continuousThresholdRound, ne_eq] at hu
    have hnot : ¬ (a + (b - a) * u ≤ x₁ ↔ a + (b - a) * u ≤ x₂) := fun heq =>
      hu.2 (decide_eq_decide.mpr heq)
    have h1 : x₁ < a + (b - a) * u := by
      by_contra hle
      rw [not_lt] at hle
      exact hnot ⟨fun _ => hle.trans hx, fun _ => hle⟩
    have h2 : a + (b - a) * u ≤ x₂ := by
      by_contra hlt
      rw [not_le] at hlt
      exact hnot ⟨fun h => absurd (h.trans hx) (not_le.mpr hlt),
        fun h => absurd h (not_le.mpr hlt)⟩
    exact ⟨(div_lt_iff₀' hba).mpr (by linarith), (le_div_iff₀' hba).mpr (by linarith)⟩
  refine (MeasureTheory.measure_mono hsub).trans ?_
  rw [Real.volume_Ioc]
  have hdiff : (x₂ - a) / (b - a) - (x₁ - a) / (b - a) = (x₂ - x₁) / (b - a) := by ring
  rw [hdiff]

/-- **Continuous randomized-threshold rounding lemma**: for `a < b` and `u ~ Uniform([0, 1))`, the
disagreement measure is at most `|x₁ - x₂| / (b - a)`. -/
theorem volume_thresholdRound_ne_le {a b : ℝ} (hab : a < b) (x₁ x₂ : ℝ) :
    MeasureTheory.volume
      {u ∈ Set.Ico (0 : ℝ) 1 |
        continuousThresholdRound a b u x₁ ≠ continuousThresholdRound a b u x₂} ≤
      ENNReal.ofReal (|x₁ - x₂| / (b - a)) := by
  rcases le_total x₁ x₂ with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    exact volume_thresholdRound_ne_le_of_le hab hle
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    have heq :
        {u ∈ Set.Ico (0 : ℝ) 1 |
          continuousThresholdRound a b u x₁ ≠ continuousThresholdRound a b u x₂} =
        {u ∈ Set.Ico (0 : ℝ) 1 |
          continuousThresholdRound a b u x₂ ≠ continuousThresholdRound a b u x₁} := by
      ext u
      simp only [Set.mem_ofPred_eq, ne_comm]
    rw [heq]
    exact volume_thresholdRound_ne_le_of_le hab hle

private theorem volume_continuousRoundGridBin_ne_le_of_le {w : ℝ} (hw : 0 < w) {x₁ x₂ : ℝ}
    (hx : x₁ ≤ x₂) :
    MeasureTheory.volume
      {u ∈ Set.Ico (0 : ℝ) 1 |
        continuousRoundGridBin w u x₁ ≠ continuousRoundGridBin w u x₂} ≤
      ENNReal.ofReal ((x₂ - x₁) / w) := by
  let y₁ : ℝ := x₁ / w
  let y₂ : ℝ := x₂ / w
  have hy : y₁ ≤ y₂ := by dsimp only [y₁, y₂]; gcongr
  have hydiff : y₂ - y₁ = (x₂ - x₁) / w := by dsimp only [y₁, y₂]; ring
  rcases le_or_gt 1 (y₂ - y₁) with hbig | hsmall
  · refine (MeasureTheory.measure_mono (Set.sep_subset (Set.Ico (0 : ℝ) 1) _)).trans ?_
    rw [Real.volume_Ico, sub_zero, ← hydiff]
    exact ENNReal.ofReal_le_ofReal hbig
  · let k : ℤ := ⌊y₁⌋ + 1
    have hsub :
        {u ∈ Set.Ico (0 : ℝ) 1 |
          continuousRoundGridBin w u x₁ ≠ continuousRoundGridBin w u x₂} ⊆
        Set.Ico ((k : ℝ) - y₂) ((k : ℝ) - y₁) ∪ Set.Ico ((k : ℝ) + 1 - y₂) 1 := by
      intro u hu
      rcases hu with ⟨⟨hu0, hu1⟩, hne⟩
      have hfloor_lt : ⌊y₁ + u⌋ < ⌊y₂ + u⌋ :=
        lt_of_le_of_ne (Int.floor_mono (by linarith)) hne
      let m : ℤ := ⌊y₁ + u⌋ + 1
      have hm1 : y₁ + u < (m : ℝ) := by
        exact_mod_cast Int.lt_floor_add_one (y₁ + u)
      have hm2 : (m : ℝ) ≤ y₂ + u := by
        have : m ≤ ⌊y₂ + u⌋ := hfloor_lt
        exact (Int.cast_le.mpr this).trans (Int.floor_le (y₂ + u))
      have hm_lo : k ≤ m := by
        have : ⌊y₁⌋ ≤ ⌊y₁ + u⌋ := Int.floor_mono (by linarith)
        omega
      have hm_hi : m ≤ k + 1 := by
        have : ⌊y₁ + u⌋ < ⌊y₁⌋ + 2 := by
          refine Int.floor_lt.mpr ?_
          push_cast
          linarith [Int.lt_floor_add_one y₁]
        omega
      have hm_cases : m = k ∨ m = k + 1 := by omega
      rcases hm_cases with hmk | hmk
      · have hmkR : (m : ℝ) = k := congrArg Int.cast hmk
        exact Or.inl ⟨by linarith, by linarith⟩
      · have hmkR : (m : ℝ) = k + 1 := by exact_mod_cast hmk
        exact Or.inr ⟨by linarith, hu1⟩
    have hmeas1 :
        MeasureTheory.volume (Set.Ico ((k : ℝ) - y₂) ((k : ℝ) - y₁)) =
          ENNReal.ofReal (y₂ - y₁) := by
      rw [Real.volume_Ico]
      congr 1
      ring
    have hmeas2 :
        MeasureTheory.volume (Set.Ico ((k : ℝ) + 1 - y₂) 1) =
          ENNReal.ofReal (y₂ - (k : ℝ)) := by
      rw [Real.volume_Ico]
      congr 1
      ring
    rcases le_or_gt y₂ (k : ℝ) with hk2 | hk2
    · have hempty : Set.Ico ((k : ℝ) + 1 - y₂) 1 = ∅ :=
        Set.Ico_eq_empty_of_le (by linarith)
      rw [hempty, Set.union_empty] at hsub
      exact (MeasureTheory.measure_mono hsub).trans (hmeas1.le.trans_eq (by rw [hydiff]))
    · have hsub' :
          Set.Ico ((k : ℝ) - y₂) ((k : ℝ) - y₁) ∩ Set.Ico (0 : ℝ) 1 ⊆
          Set.Ico 0 ((k : ℝ) - y₁) := fun u hu => ⟨hu.2.1, hu.1.2⟩
      have hfull :
          {u ∈ Set.Ico (0 : ℝ) 1 |
            continuousRoundGridBin w u x₁ ≠ continuousRoundGridBin w u x₂} ⊆
          Set.Ico 0 ((k : ℝ) - y₁) ∪ Set.Ico ((k : ℝ) + 1 - y₂) 1 := by
        intro u hu
        rcases hsub hu with hA | hB
        · exact Or.inl ⟨hu.1.1, hA.2⟩
        · exact Or.inr hB
      have hbound :
          MeasureTheory.volume (Set.Ico 0 ((k : ℝ) - y₁) ∪ Set.Ico ((k : ℝ) + 1 - y₂) 1) ≤
            ENNReal.ofReal ((k : ℝ) - y₁) + ENNReal.ofReal (y₂ - (k : ℝ)) := by
        refine (MeasureTheory.measure_union_le _ _).trans ?_
        rw [Real.volume_Ico, sub_zero, hmeas2]
      have hpos1 : 0 ≤ (k : ℝ) - y₁ := by
        have : y₁ < (k : ℝ) := by
          dsimp only [k]
          push_cast
          exact Int.lt_floor_add_one y₁
        linarith
      have hpos2 : 0 ≤ y₂ - (k : ℝ) := by linarith
      calc MeasureTheory.volume
            {u ∈ Set.Ico (0 : ℝ) 1 |
              continuousRoundGridBin w u x₁ ≠ continuousRoundGridBin w u x₂}
          ≤ MeasureTheory.volume
              (Set.Ico 0 ((k : ℝ) - y₁) ∪ Set.Ico ((k : ℝ) + 1 - y₂) 1) :=
            MeasureTheory.measure_mono hfull
        _ ≤ ENNReal.ofReal ((k : ℝ) - y₁) + ENNReal.ofReal (y₂ - (k : ℝ)) := hbound
        _ = ENNReal.ofReal (((k : ℝ) - y₁) + (y₂ - (k : ℝ))) :=
            (ENNReal.ofReal_add hpos1 hpos2).symm
        _ = ENNReal.ofReal ((x₂ - x₁) / w) := by
            rw [← hydiff]
            ring_nf

/-- **Continuous periodic grid rounding lemma**: for `w > 0` and `u ~ Uniform([0, 1))`, the
disagreement measure of `continuousRoundGrid w u` is at most `|x₁ - x₂| / w`. -/
theorem volume_roundGrid_ne_le {w : ℝ} (hw : 0 < w) (x₁ x₂ : ℝ) :
    MeasureTheory.volume
      {u ∈ Set.Ico (0 : ℝ) 1 | continuousRoundGrid w u x₁ ≠ continuousRoundGrid w u x₂} ≤
      ENNReal.ofReal (|x₁ - x₂| / w) := by
  have hbin : ∀ u, continuousRoundGrid w u x₁ ≠ continuousRoundGrid w u x₂ ↔
      continuousRoundGridBin w u x₁ ≠ continuousRoundGridBin w u x₂ := by
    intro u
    simp only [continuousRoundGrid, ne_eq]
    constructor
    · intro h heq
      exact h (by rw [heq])
    · intro h heq
      have h1 := mul_right_cancel₀ hw.ne' heq
      have h2 : (continuousRoundGridBin w u x₁ : ℝ) = (continuousRoundGridBin w u x₂ : ℝ) := by
        linarith
      exact h (Int.cast_injective h2)
  have heq :
      {u ∈ Set.Ico (0 : ℝ) 1 | continuousRoundGrid w u x₁ ≠ continuousRoundGrid w u x₂} =
      {u ∈ Set.Ico (0 : ℝ) 1 | continuousRoundGridBin w u x₁ ≠ continuousRoundGridBin w u x₂} := by
    ext u
    simp only [Set.mem_ofPred_eq, hbin]
  rw [heq]
  rcases le_total x₁ x₂ with hle | hle
  · rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
    exact volume_continuousRoundGridBin_ne_le_of_le hw hle
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    have hcomm :
        {u ∈ Set.Ico (0 : ℝ) 1 |
          continuousRoundGridBin w u x₁ ≠ continuousRoundGridBin w u x₂} =
        {u ∈ Set.Ico (0 : ℝ) 1 |
          continuousRoundGridBin w u x₂ ≠ continuousRoundGridBin w u x₁} := by
      ext u
      simp only [Set.mem_ofPred_eq, ne_comm]
    rw [hcomm]
    exact volume_continuousRoundGridBin_ne_le_of_le hw hle

end ContinuousDisagreement

section RoundingPrograms

variable {X : Type} {m : ℕ}

/-- Accuracy of `roundGridProg`: whenever `est S` is within `δ` of `target D` except with
probability `β`, rounding to a periodic grid of width `w` preserves estimation within `w / 2 + δ`
with the same failure probability `β`. -/
theorem isAccurateFor_roundGridProg_of_concentrates {w δ β : ℝ} (hw : 0 < w)
    (N : ℕ) [NeZero N] (est : (Fin m → X) → ℝ) (𝒟 : Set (PMF X)) (target : PMF X → ℝ)
    (hconc : ∀ D ∈ 𝒟,
      ((Probability.PMF.iid D m).toOuterMeasure {S | δ < |est S - target D|}).toReal ≤ β) :
    EstimatesFor (roundGridProg w N est).toAlgorithm 𝒟 target (w / 2 + δ) β := by
  intro D hD
  have hβ : 0 ≤ β := ENNReal.toReal_nonneg.trans (hconc D hD)
  have hmarg : (roundGridProg w N est).toAlgorithm.marginal D =
      (ProbComp.eval (ProbComp.uniform (Fin N))).bind fun i =>
        (Probability.PMF.iid D m).map fun S => roundGrid w N i (est S) := by
    simp only [roundGridProg, Program.toAlgorithm_deterministic, Algorithm.marginal_eq_seed_bind,
      Algorithm.deterministic]
    rfl
  rw [hmarg, ProbComp.eval_uniform]
  refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ Set.univ _ hβ
    fun i _ _ => ?_).trans_eq ?_
  · rw [PMF.toOuterMeasure_map_apply]
    have hsub : (fun S => roundGrid w N i (est S)) ⁻¹' {y | |y - target D| ≤ w / 2 + δ}ᶜ ⊆
        {S | δ < |est S - target D|} := by
      intro S hS
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hS ⊢
      have htri : |roundGrid w N i (est S) - target D| ≤ w / 2 + |est S - target D| := by
        calc |roundGrid w N i (est S) - target D|
            = |(roundGrid w N i (est S) - est S) + (est S - target D)| := by ring_nf
          _ ≤ |roundGrid w N i (est S) - est S| + |est S - target D| := abs_add_le _ _
          _ ≤ w / 2 + |est S - target D| :=
              add_le_add (abs_roundGrid_sub_le hw N i (est S)) le_rfl
      linarith
    exact (Probability.PMF.toOuterMeasure_toReal_mono _ hsub).trans (hconc D hD)
  · simp

/-- Replicability of `roundGridProg`: if `est S` concentrates within `δ` of `target D` except with
probability `β` for every `D ∈ 𝒟`, then `roundGridProg w N est` is
`(2 * δ / w + 1 / N + 2 * β)`-replicable over `𝒟`. -/
theorem isReplicableFor_roundGridProg_of_concentrates {w δ β : ℝ} (hw : 0 < w)
    (N : ℕ) [NeZero N] (est : (Fin m → X) → ℝ) (𝒟 : Set (PMF X)) (target : PMF X → ℝ)
    (hδ : 0 ≤ δ) (hβ : 0 ≤ β)
    (hconc : ∀ D ∈ 𝒟,
      ((Probability.PMF.iid D m).toOuterMeasure {S | δ < |est S - target D|}).toReal ≤ β) :
    IsReplicableFor (roundGridProg w N est).toAlgorithm 𝒟 (2 * δ / w + 1 / N + 2 * β) := by
  intro D hD
  have hcomm :
      (roundGridProg w N est).toAlgorithm.pairedOutput D =
        (Probability.PMF.iid D m).bind fun S₁ =>
          (Probability.PMF.iid D m).bind fun S₂ =>
            (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
              (roundGrid w N i (est S₁), roundGrid w N i (est S₂)) := by
    simp only [roundGridProg, Program.toAlgorithm_deterministic,
      Algorithm.pairedOutput_deterministic, ProbComp.eval_uniform]
    rw [PMF.bind_comm]
    exact congrArg (PMF.bind (Probability.PMF.iid D m)) (funext fun S₁ => PMF.bind_comm _ _ _)
  rw [Algorithm.disagreeProb, hcomm]
  let good : Set (Fin m → X) := {S | |est S - target D| ≤ δ}
  let c : ℝ := 2 * δ / w + 1 / N
  have hc : 0 ≤ c := by positivity
  have hgoodc : ((Probability.PMF.iid D m).toOuterMeasure goodᶜ).toReal ≤ β := by
    have heq : goodᶜ = {S | δ < |est S - target D|} := by
      ext S
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, good]
    rw [heq]
    exact hconc D hD
  have hinner :
      ∀ S₁ ∈ good,
        (((Probability.PMF.iid D m).bind fun S₂ =>
          (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
            (roundGrid w N i (est S₁), roundGrid w N i (est S₂))).toOuterMeasure
          {p : ℝ × ℝ | p.1 ≠ p.2}).toReal ≤ β + c := by
    intro S₁ hS₁
    refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ good _ hc ?_).trans
      (add_le_add hgoodc le_rfl)
    intro S₂ _ hS₂
    rw [PMF.toOuterMeasure_map_apply]
    have hpre : (fun i : Fin N => (roundGrid w N i (est S₁), roundGrid w N i (est S₂))) ⁻¹'
        {p : ℝ × ℝ | p.1 ≠ p.2} =
        {i : Fin N | roundGrid w N i (est S₁) ≠ roundGrid w N i (est S₂)} :=
      rfl
    rw [hpre]
    have hdist : |est S₁ - est S₂| ≤ 2 * δ := by
      have h1 : |est S₁ - target D| ≤ δ := hS₁
      have h2 : |target D - est S₂| ≤ δ := by rw [abs_sub_comm]; exact hS₂
      calc |est S₁ - est S₂|
          = |(est S₁ - target D) + (target D - est S₂)| := by ring_nf
        _ ≤ |est S₁ - target D| + |target D - est S₂| := abs_add_le _ _
        _ ≤ δ + δ := add_le_add h1 h2
        _ = 2 * δ := by ring
    refine (roundGrid_disagree_le hw (est S₁) (est S₂)).trans ?_
    dsimp only [c]
    gcongr
  have houter := Probability.PMF.toOuterMeasure_bind_failure_toReal_le (Probability.PMF.iid D m)
    (fun S₁ => (Probability.PMF.iid D m).bind fun S₂ =>
      (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
        (roundGrid w N i (est S₁), roundGrid w N i (est S₂)))
    good {p : ℝ × ℝ | p.1 ≠ p.2} (add_nonneg hβ hc) (fun S₁ _ hS₁ => hinner S₁ hS₁)
  calc (((Probability.PMF.iid D m).bind fun S₁ =>
          (Probability.PMF.iid D m).bind fun S₂ =>
            (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
              (roundGrid w N i (est S₁), roundGrid w N i (est S₂))).toOuterMeasure
        {p : ℝ × ℝ | p.1 ≠ p.2}).toReal
      ≤ ((Probability.PMF.iid D m).toOuterMeasure goodᶜ).toReal + (β + c) := houter
    _ ≤ β + (β + c) := add_le_add hgoodc le_rfl
    _ = 2 * δ / w + 1 / N + 2 * β := by dsimp only [c]; ring

end RoundingPrograms

end Cslib.MachineLearning.Replicable
