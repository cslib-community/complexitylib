/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.MachineLearning.Replicable.Basic
public import CslibFrontier.MachineLearning.Replicable.Rounding
public import CslibFrontier.Languages.Probabilistic.Basic
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.ToReal

/-!
# Replicable bounded-mean and coin bias estimation

This module provides an end-to-end replicable estimation client based on Hoeffding concentration
and periodic grid rounding (`roundGridProg`) [ImpagliazzoLeiPitassiSorrell2022]:

* **Bounded mean estimation (`replicableMeanProg`)**: given any finite domain `X` and bounded
  observable `f : X → ℝ` taking values in `[a, b]`, empirical averaging combined with
  `roundGridProg w N` yields a `ProbComp`-backed `Program` that is both strongly `ρ`-replicable
  over all distributions `D : PMF X` and `(ε, β)`-accurate for estimating `𝔼_{x ~ D}[f x]`.
* **Coin bias estimation (`replicableBiasProg`)**: specializing to `X = Bool` and
  `coinBias D = (D true).toReal`, empirical head frequency plus `roundGridProg` gives an explicit
  strongly `ρ`-replicable and `(ε, β)`-accurate coin bias estimator with concrete sample-complexity
  guarantees.

## Main definitions

* `Cslib.MachineLearning.Replicable.empiricalMean`,
  `Cslib.MachineLearning.Replicable.distExpectation`: sample average and population expectation.
* `Cslib.MachineLearning.Replicable.replicableMeanProg`: `ProbComp` replicable mean-estimation
  program.
* `Cslib.MachineLearning.Replicable.coinBias`,
  `Cslib.MachineLearning.Replicable.empiricalBias`,
  `Cslib.MachineLearning.Replicable.replicableBiasProg`: replicable coin bias-estimation program.

## Main results

* `Cslib.MachineLearning.Replicable.boundedMean_concentrates`: Hoeffding concentration of
  `empiricalMean` around `distExpectation`.
* `Cslib.MachineLearning.Replicable.estimates_replicableMeanProg`,
  `Cslib.MachineLearning.Replicable.isReplicable_replicableMeanProg`,
  `Cslib.MachineLearning.Replicable.exists_replicableMeanProg`: strong `ρ`-replicability and
  `(ε, β)`-accuracy for bounded-mean estimation.
* `Cslib.MachineLearning.Replicable.estimates_replicableBiasProg`,
  `Cslib.MachineLearning.Replicable.isReplicable_replicableBiasProg`,
  `Cslib.MachineLearning.Replicable.exists_replicableBiasProg`: concrete quantitative guarantees
  and parameter synthesis for replicable coin bias estimation.

## References

* [Impagliazzo, Lei, Pitassi, Sorrell (STOC 2022)][ImpagliazzoLeiPitassiSorrell2022],
  *Reproducibility in Learning* (paper PDF not directly inspected in this formalization;
  `ProbComp` bias-estimation programs and Hoeffding/grid-rounding proofs are formalized directly).
-/

public section

namespace Cslib.MachineLearning.Replicable

section BoundedMean

variable {X : Type}

/-- Sample average of `f : X → ℝ` over `S : Fin m → X`. -/
@[expose] noncomputable def empiricalMean {X : Type*} (f : X → ℝ) {m : ℕ} (S : Fin m → X) : ℝ :=
  (∑ j : Fin m, f (S j)) / m

/-- Population expectation `∑ x, (D x).toReal * f x` on a finite domain `X`. -/
@[expose] noncomputable def distExpectation {X : Type*} [Fintype X] (D : PMF X) (f : X → ℝ) : ℝ :=
  ∑ x : X, (D x).toReal * f x

/-- `ProbComp`-backed ideal real-arithmetic program for replicable bounded-mean estimation via
periodic grid rounding of `empiricalMean f` (interpreted semantically via `Program.toAlgorithm`). -/
@[expose] noncomputable def replicableMeanProg (f : X → ℝ) (w : ℝ) (N m : ℕ) [NeZero N] :
    Program X (Fin N) ℝ m :=
  roundGridProg w N (empiricalMean f)

/-- Hoeffding concentration of the empirical mean of an observable `f : X → [a, b]` under
`m ≥ 1` i.i.d. draws from `D`, using effective width `M = max (b - a) 1`. -/
theorem boundedMean_concentrates {X : Type*} [Fintype X] (D : PMF X) (f : X → ℝ) {a b : ℝ}
    (hf : ∀ x ∈ D.support, f x ∈ Set.Icc a b) (m : ℕ) [NeZero m] {δ : ℝ} (hδ : 0 ≤ δ) :
    ((Probability.PMF.iid D m).toOuterMeasure
      {S : Fin m → X | δ < |empiricalMean f S - distExpectation D f|}).toReal ≤
      2 * Real.exp (-2 * (m : ℝ) * δ ^ 2 / (max (b - a) 1) ^ 2) := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  let bound : ℝ := max (b - a) 1
  have hbound : 0 ≤ bound := le_trans zero_le_one (le_max_right _ _)
  let score : Fin m → X → ℝ := fun _ x => f x - a
  have hscore : ∀ j (x : X), x ∈ D.support → score j x ∈ Set.Icc 0 bound := by
    intro _ x hx
    obtain ⟨hlo, hhi⟩ := hf x hx
    exact ⟨sub_nonneg.mpr hlo, (sub_le_sub_right hhi a).trans (le_max_left _ _)⟩
  have hhoeff := Probability.PMF.pi_sum_abs_sub_mean_ge (fun _ : Fin m => D) score hbound hscore
    (mul_nonneg hm.le hδ)
  rw [← Probability.PMF.iid_eq_pi, Fintype.card_fin] at hhoeff
  have hmean : ∑ j : Fin m, ∑ x : X, (D x).toReal * score j x =
      (m : ℝ) * (distExpectation D f - a) := by
    have hD1 : ∑ x : X, (D x).toReal = 1 := Probability.PMF.sum_toReal D
    calc ∑ _j : Fin m, ∑ x : X, (D x).toReal * (f x - a)
        = ∑ _j : Fin m, ((∑ x : X, (D x).toReal * f x) - (∑ x : X, (D x).toReal) * a) := by
          refine Finset.sum_congr rfl fun _ _ => ?_
          simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
      _ = (m : ℝ) * (distExpectation D f - a) := by
          simp [distExpectation, hD1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hsub :
      {S : Fin m → X | δ < |empiricalMean f S - distExpectation D f|} ⊆
      {outcome : Fin m → X |
        (m : ℝ) * δ ≤ |∑ j : Fin m, score j (outcome j) - ∑ j : Fin m, ∑ x : X,
          (D x).toReal * score j x|} := by
    intro S hS
    simp only [Set.mem_ofPred_eq, empiricalMean] at hS ⊢
    rw [hmean]
    have hdiff : (∑ j : Fin m, score j (S j)) - (m : ℝ) * (distExpectation D f - a) =
        (m : ℝ) * ((∑ j : Fin m, f (S j)) / m - distExpectation D f) := by
      have hsub_sum : ∑ j : Fin m, score j (S j) = (∑ j : Fin m, f (S j)) - (m : ℝ) * a := by
        simp [score, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [hsub_sum]
      field_simp [hm.ne']
      ring
    rw [hdiff, abs_mul, abs_of_pos hm]
    exact (mul_lt_mul_of_pos_left hS hm).le
  refine (Probability.PMF.toOuterMeasure_toReal_mono _ hsub).trans (hhoeff.trans_eq ?_)
  dsimp only [bound]
  congr 1
  field_simp [hm.ne']

/-- Strong `(w / 2 + δ, 2 * exp (-2 * m * δ^2 / (max (b - a) 1)^2))`-estimation accuracy of
`replicableMeanProg`. -/
theorem estimates_replicableMeanProg [Fintype X] (f : X → ℝ) {a b : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc a b) {w δ : ℝ} (hw : 0 < w) (hδ : 0 ≤ δ) (N m : ℕ)
    [NeZero N] [NeZero m] :
    Estimates (replicableMeanProg f w N m).toAlgorithm (fun D => distExpectation D f)
      (w / 2 + δ) (2 * Real.exp (-2 * (m : ℝ) * δ ^ 2 / (max (b - a) 1) ^ 2)) :=
  isAccurateFor_roundGridProg_of_concentrates hw N (empiricalMean f) Set.univ
    (fun D => distExpectation D f) fun D _ =>
      boundedMean_concentrates D f (fun x _ => hf x) m hδ

/-- Strong `ρ`-replicability of `replicableMeanProg` for any bounded observable `f : X → [a, b]`. -/
theorem isReplicable_replicableMeanProg [Finite X] (f : X → ℝ) {a b : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc a b) {w δ : ℝ} (hw : 0 < w) (hδ : 0 ≤ δ) (N m : ℕ)
    [NeZero N] [NeZero m] :
    IsReplicable (replicableMeanProg f w N m).toAlgorithm
      (2 * δ / w + 1 / N + 2 * (2 * Real.exp (-2 * (m : ℝ) * δ ^ 2 / (max (b - a) 1) ^ 2))) := by
  let _ : Fintype X := Fintype.ofFinite X
  exact isReplicableFor_roundGridProg_of_concentrates hw N (empiricalMean f) Set.univ
    (fun D => distExpectation D f) hδ (by positivity) fun D _ =>
      boundedMean_concentrates D f (fun x _ => hf x) m hδ

/-- **Parameter synthesis for replicable bounded-mean estimation**: for any finite domain `X`,
bounded `f : X → [a, b]`, and target `(ε, ρ, β)` with `ε, ρ, β > 0`, there exist `w > 0` and
`N, m ≥ 1` making `(replicableMeanProg f w N m).toAlgorithm` strongly `ρ`-replicable and
strongly `(ε, β)`-accurate. -/
theorem exists_replicableMeanProg [Fintype X] (f : X → ℝ) {a b ε ρ β : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc a b) (hε : 0 < ε) (hρ : 0 < ρ) (hβ : 0 < β) :
    ∃ (w : ℝ) (N m : ℕ) (_ : NeZero N) (_ : NeZero m), 0 < w ∧
      IsReplicable (replicableMeanProg f w N m).toAlgorithm ρ ∧
      Estimates (replicableMeanProg f w N m).toAlgorithm (fun D => distExpectation D f) ε β := by
  let w : ℝ := ε
  have hw : 0 < w := hε
  let δ : ℝ := min (ε / 2) ((ρ / 8) * w)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨N, hN_gt⟩ := exists_nat_gt (4 / ρ)
  have hNpos : 0 < N := by
    have : 0 < 4 / ρ := by positivity
    exact_mod_cast this.trans hN_gt
  have hN_inst : NeZero N := ⟨Nat.ne_of_gt hNpos⟩
  have hN_bound : (1 : ℝ) / N ≤ ρ / 4 := by
    have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
    have hmul : 4 < (N : ℝ) * ρ := (div_lt_iff₀ hρ).mp hN_gt
    rw [div_le_div_iff₀ hNR (by norm_num : (0 : ℝ) < 4), one_mul]
    linarith
  let width : ℝ := max (b - a) 1
  have hwidth : 0 < width := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let errTarget : ℝ := min (ρ / 4) β
  have herrTarget : 0 < errTarget := lt_min (by positivity) hβ
  let t : ℝ := Real.log (2 / errTarget) * width ^ 2 / (2 * δ ^ 2)
  obtain ⟨m, hm_gt⟩ := exists_nat_gt (max t 0)
  have hmpos : 0 < m := by
    exact_mod_cast lt_of_le_of_lt (le_max_right t 0) hm_gt
  have hm_inst : NeZero m := ⟨Nat.ne_of_gt hmpos⟩
  have hm_bound : 2 * Real.exp (-2 * (m : ℝ) * δ ^ 2 / width ^ 2) ≤ errTarget := by
    have hmt : t < (m : ℝ) := lt_of_le_of_lt (le_max_left t 0) hm_gt
    have hdenom : 0 < 2 * δ ^ 2 := by positivity
    have hw2 : 0 < width ^ 2 := by positivity
    have harg : Real.log (2 / errTarget) < 2 * (m : ℝ) * δ ^ 2 / width ^ 2 := by
      have hmul : Real.log (2 / errTarget) * width ^ 2 < (m : ℝ) * (2 * δ ^ 2) := by
        calc Real.log (2 / errTarget) * width ^ 2
            = t * (2 * δ ^ 2) := by
              dsimp only [t]
              field_simp [hdenom.ne']
          _ < (m : ℝ) * (2 * δ ^ 2) := mul_lt_mul_of_pos_right hmt hdenom
      rw [lt_div_iff₀ hw2]
      linarith
    have hexp : Real.exp (-2 * (m : ℝ) * δ ^ 2 / width ^ 2) ≤ errTarget / 2 := by
      rw [show -2 * (m : ℝ) * δ ^ 2 / width ^ 2 = -(2 * (m : ℝ) * δ ^ 2 / width ^ 2) by ring,
        Real.exp_neg, inv_eq_one_div, one_div_le (Real.exp_pos _) (div_pos herrTarget two_pos),
        one_div_div]
      calc 2 / errTarget = Real.exp (Real.log (2 / errTarget)) :=
            (Real.exp_log (div_pos two_pos herrTarget)).symm
        _ ≤ Real.exp (2 * (m : ℝ) * δ ^ 2 / width ^ 2) := Real.exp_le_exp.mpr harg.le
    linarith
  refine ⟨w, N, m, hN_inst, hm_inst, hw, ?_, ?_⟩
  · refine (isReplicable_replicableMeanProg f hf hw hδ.le N m).mono ?_
    have h1 : 2 * δ / w ≤ ρ / 4 := by
      have hle : δ ≤ (ρ / 8) * w := min_le_right _ _
      calc 2 * δ / w ≤ 2 * ((ρ / 8) * w) / w := by gcongr
        _ = ρ / 4 := by field_simp [hw.ne']; ring
    have h2 : 2 * Real.exp (-2 * (m : ℝ) * δ ^ 2 / (max (b - a) 1) ^ 2) ≤ ρ / 4 :=
      hm_bound.trans (min_le_left _ _)
    linarith
  · exact (estimates_replicableMeanProg f hf hw hδ.le N m).mono
      (by have : δ ≤ ε / 2 := min_le_left _ _; dsimp only [w]; linarith)
      (hm_bound.trans (min_le_right _ _))

end BoundedMean

section CoinBias

/-- True bias `Pr_{x ~ D}[x = true]` of a Bernoulli distribution `D : PMF Bool`. -/
@[expose] noncomputable def coinBias (D : PMF Bool) : ℝ :=
  (D true).toReal

/-- Empirical bias (fraction of `true` samples) of `S : Fin m → Bool`. -/
@[expose] noncomputable def empiricalBias {m : ℕ} (S : Fin m → Bool) : ℝ :=
  ((Finset.univ.filter fun j : Fin m => S j = true).card : ℝ) / m

/-- `ProbComp`-backed ideal real-arithmetic program for replicable coin bias estimation via
periodic grid rounding of `empiricalBias` (interpreted semantically via `Program.toAlgorithm`). -/
@[expose] noncomputable def replicableBiasProg (w : ℝ) (N m : ℕ) [NeZero N] :
    Program Bool (Fin N) ℝ m :=
  roundGridProg w N empiricalBias

private theorem empiricalBias_eq_empiricalMean {m : ℕ} (S : Fin m → Bool) :
    empiricalBias S = empiricalMean (fun b => if b then (1 : ℝ) else 0) S := by
  simp only [empiricalBias, empiricalMean, Finset.card_filter, Nat.cast_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  cases S j <;> simp

private theorem coinBias_eq_distExpectation (D : PMF Bool) :
    coinBias D = distExpectation D (fun b => if b then (1 : ℝ) else 0) := by
  simp [coinBias, distExpectation]

private theorem replicableBiasProg_toAlgorithm_eq (w : ℝ) (N m : ℕ) [NeZero N] :
    (replicableBiasProg w N m).toAlgorithm =
      (replicableMeanProg (fun b : Bool => if b then (1 : ℝ) else 0) w N m).toAlgorithm := by
  simp only [Program.toAlgorithm, replicableBiasProg, replicableMeanProg, roundGridProg]
  congr 2
  ext S i
  simp [empiricalBias_eq_empiricalMean]

/-- Strong `(w / 2 + δ, 2 * exp (-2 * m * δ^2))`-estimation accuracy of `replicableBiasProg`
for estimating `coinBias D` across all Bernoulli distributions `D : PMF Bool`. -/
theorem estimates_replicableBiasProg {w δ : ℝ} (hw : 0 < w) (hδ : 0 ≤ δ) (N m : ℕ)
    [NeZero N] [NeZero m] :
    Estimates (replicableBiasProg w N m).toAlgorithm coinBias
      (w / 2 + δ) (2 * Real.exp (-2 * (m : ℝ) * δ ^ 2)) := by
  have hf : ∀ b : Bool, (if b then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := fun b => by
    cases b <;> simp
  have hest := estimates_replicableMeanProg (fun b : Bool => if b then (1 : ℝ) else 0) hf hw hδ
    N m
  have hmax : max ((1 : ℝ) - 0) 1 = 1 := by norm_num
  rw [hmax, one_pow, div_one] at hest
  intro D hD
  dsimp only
  rw [replicableBiasProg_toAlgorithm_eq, coinBias_eq_distExpectation]
  exact hest D hD

/-- Strong `ρ`-replicability of `replicableBiasProg` across all distributions `D : PMF Bool`. -/
theorem isReplicable_replicableBiasProg {w δ : ℝ} (hw : 0 < w) (hδ : 0 ≤ δ) (N m : ℕ)
    [NeZero N] [NeZero m] :
    IsReplicable (replicableBiasProg w N m).toAlgorithm
      (2 * δ / w + 1 / N + 2 * (2 * Real.exp (-2 * (m : ℝ) * δ ^ 2))) := by
  have hf : ∀ b : Bool, (if b then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := fun b => by
    cases b <;> simp
  have hrep := isReplicable_replicableMeanProg (fun b : Bool => if b then (1 : ℝ) else 0) hf hw hδ
    N m
  have hmax : max ((1 : ℝ) - 0) 1 = 1 := by norm_num
  rw [hmax, one_pow, div_one] at hrep
  intro D hD
  rw [replicableBiasProg_toAlgorithm_eq]
  exact hrep D hD

/-- **Replicable coin bias-estimation theorem** [ImpagliazzoLeiPitassiSorrell2022]: for any
`ε > 0`, `ρ > 0`, and `β > 0`, there exist `w > 0` and `N, m ≥ 1` such that
`(replicableBiasProg w N m).toAlgorithm` is strongly `ρ`-replicable and strongly
`(ε, β)`-accurate for estimating `coinBias D`. -/
theorem exists_replicableBiasProg {ε ρ β : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hβ : 0 < β) :
    ∃ (w : ℝ) (N m : ℕ) (_ : NeZero N) (_ : NeZero m), 0 < w ∧
      IsReplicable (replicableBiasProg w N m).toAlgorithm ρ ∧
      Estimates (replicableBiasProg w N m).toAlgorithm coinBias ε β := by
  have hf : ∀ b : Bool, (if b then (1 : ℝ) else 0) ∈ Set.Icc (0 : ℝ) 1 := fun b => by
    cases b <;> simp
  obtain ⟨w, N, m, hN, hm, hw, hrep, hest⟩ :=
    exists_replicableMeanProg (fun b : Bool => if b then (1 : ℝ) else 0) hf hε hρ hβ
  refine ⟨w, N, m, hN, hm, hw, fun D hD => ?_, fun D hD => ?_⟩
  · rw [replicableBiasProg_toAlgorithm_eq]
    exact hrep D hD
  · dsimp only
    rw [replicableBiasProg_toAlgorithm_eq, coinBias_eq_distExpectation]
    exact hest D hD

end CoinBias

end Cslib.MachineLearning.Replicable
