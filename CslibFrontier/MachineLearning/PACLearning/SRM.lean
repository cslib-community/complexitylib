/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.PACLearning.UniformConvergence
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

import Mathlib.Analysis.SpecificLimits.Basic

/-! # Structural risk minimization

A class `H` has *uniform convergence rate* `ε` over a family `𝒟` of distributions if, for every
`D ∈ 𝒟`, sample size `m > 0` and confidence `δ > 0`, a sample of `m` i.i.d. examples is
`ε m δ`-representative for `H` with probability at least `1 - δ`; with `ε m δ → 0` as `m → ∞`
this is the uniform convergence property of [ShalevShwartzBenDavid2014, Definition 4.3], with an
explicit rate instead of a sample complexity. Structural risk minimization (SRM) handles a class
`⋃ i, H i` that is a countable union of classes `H i` with rates `ε i`. A *weighting* `w` of the
indices (positive weights with `∑ w i ≤ 1`) splits the confidence `δ` among the classes, and a
union bound gives
[ShalevShwartzBenDavid2014, Theorem 7.4]: with probability at least `1 - δ`, every `h ∈ H i`
satisfies `|L_S(h) - L_D(h)| ≤ ε i m (w i · δ)`. The SRM rule outputs a hypothesis minimizing the
resulting bound `L_S(h) + ε i m (w i · δ)` over all pairs `(i, h)` with `h ∈ H i`. With the same
probability its error is at most `L_D(h) + 2 ε i m (w i · δ)` for every `i` and `h ∈ H i`, the
excess-risk guarantee behind [ShalevShwartzBenDavid2014, Theorem 7.5].

The bounds hold for arbitrary measurable domain and label spaces, and the union bound needs no
measurability of the failure events. The SRM rule here ranges over pairs `(i, h)` and charges each
`h` the smallest bound of a class containing it; [ShalevShwartzBenDavid2014, Section 7.2] charges
`h` the bound of the first class containing it, which coincides when the bounds grow with `i`.
Learners are semantic maps: no running time is claimed.

## Main definitions

- `Weighting ι`: positive weights on `ι` with sum at most `1`.
- `HasUniformConvergenceRate H 𝒟 ε`: `H` has uniform convergence rate `ε` over `𝒟`.
- `IsSRM A H pen`: on every sample, `A` outputs a minimizer of `L_S(h) + pen i` over `h ∈ H i`.

## Main results

- `Weighting.measure_pi_exists_not_isRepresentative_le`: the SRM uniform bound (Theorem 7.4) in
  representativeness form.
- `Weighting.measure_pi_exists_lt_error_le`: its one-sided form `L_D(h) ≤ L_S(h) + ε i m (w i · δ)`.
- `hasUniformConvergenceRate_finset`, `hasUniformConvergenceRate_singleton`: Hoeffding rates
  `√(log (2 |H| / δ) / (2 m))` for finite classes and `√(log (2 / δ) / (2 m))` for one hypothesis.
- `IsSRM.measure_pi_exists_lt_error_le`: the excess-risk guarantee of the SRM rule.
- `exists_isSRM`: an SRM learner exists when the penalties tend to infinity along the indices.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace Cslib.MachineLearning.PACLearning

/-! ### Weightings -/

/-- A *weighting* of a type `ι`: positive real weights with sum at most `1`
[ShalevShwartzBenDavid2014, Section 7.2]. SRM spends confidence `w i · δ` on the `i`-th class. The
weights are positive so that each class receives a nonzero share of the confidence. -/
structure Weighting (ι : Type*) where
  /-- The weight of each index. -/
  toFun : ι → ℝ
  /-- Every weight is positive. -/
  pos : ∀ i, 0 < toFun i
  /-- The weights are summable. -/
  summable : Summable toFun
  /-- The weights sum to at most `1`. -/
  tsum_le_one : ∑' i, toFun i ≤ 1

namespace Weighting

variable {ι κ : Type*}

instance : CoeFun (Weighting ι) fun _ => ι → ℝ := ⟨toFun⟩

/-- The geometric weighting `n ↦ 2⁻¹ ^ (n + 1)` of `ℕ`, whose weights sum to `1`. -/
noncomputable def geometric : Weighting ℕ where
  toFun n := (1 / 2 : ℝ) ^ (n + 1)
  pos n := by positivity
  summable := summable_geometric_two.mul_left (1 / 2) |>.congr fun n => by ring
  tsum_le_one := by
    rw [show (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) = fun n => 1 / 2 * (1 / 2) ^ n from
      funext fun n => by ring, tsum_mul_left, tsum_geometric_two]
    norm_num

@[simp] theorem geometric_apply (n : ℕ) : geometric n = (1 / 2 : ℝ) ^ (n + 1) := by
  unfold geometric
  rfl

/-- Pull a weighting back along an injection. -/
noncomputable def comap (w : Weighting κ) {e : ι → κ} (he : e.Injective) :
    Weighting ι where
  toFun i := w (e i)
  pos i := w.pos (e i)
  summable := w.summable.comp_injective he
  tsum_le_one := (tsum_comp_le_tsum_of_inj w.summable (fun i => (w.pos i).le) he).trans
    w.tsum_le_one

@[simp] theorem comap_apply (w : Weighting κ) {e : ι → κ} (he : e.Injective) (i : ι) :
    w.comap he i = w (e i) := by
  unfold comap
  rfl

/-- Every countable type has a weighting. -/
theorem nonempty [Countable ι] : Nonempty (Weighting ι) :=
  ⟨geometric.comap (Classical.choose_spec (exists_injective_nat ι))⟩

/-- Weights tend to `0` along the cofinite filter. -/
theorem tendsto_cofinite_zero (w : Weighting ι) : Tendsto w cofinite (𝓝 0) :=
  w.summable.tendsto_cofinite_zero

end Weighting

/-! ### Uniform convergence rates -/

section Rates

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [DecidableEq β]

/-- The class `H` has *uniform convergence rate* `ε` over the family `𝒟`: for every probability
measure `D ∈ 𝒟`, sample size `m > 0` and confidence `δ > 0`, `m` i.i.d. examples from `D` fail to
be `ε m δ`-representative for `H` with probability at most `δ`. On its own this is weak: for the
0-1 loss every rate `ε ≥ 1` qualifies. The uniform convergence property of
[ShalevShwartzBenDavid2014, Definition 4.3], a finite sample complexity `m_H(ε, δ)`, is a rate
with `ε m δ → 0` as `m → ∞` for every `δ > 0`, the extra hypothesis of
`isNonuniformLearnable_iUnion`. -/
@[expose] def HasUniformConvergenceRate (H : ConceptClass α β) (𝒟 : Set (Measure (α × β)))
    (ε : ℕ → ℝ → ℝ) : Prop :=
  ∀ (D : Measure (α × β)) [IsProbabilityMeasure D], D ∈ 𝒟 → ∀ m, 0 < m → ∀ δ : ℝ, 0 < δ →
    Measure.pi (fun _ : Fin m => D) {S | ¬ IsRepresentative D H (ε m δ) S} ≤ ENNReal.ofReal δ

/-- A rate can be replaced by a pointwise larger one. -/
theorem HasUniformConvergenceRate.mono {H : ConceptClass α β} {𝒟 : Set (Measure (α × β))}
    {ε ε' : ℕ → ℝ → ℝ} (hH : HasUniformConvergenceRate H 𝒟 ε) (hε : ∀ m δ, ε m δ ≤ ε' m δ) :
    HasUniformConvergenceRate H 𝒟 ε' := by
  intro D _ hD m hm δ hδ
  refine (measure_mono fun S hS => ?_).trans (hH D hD m hm δ hδ)
  exact fun hrep => hS (hrep.mono (hε m δ))

/-- **Uniform convergence for a finite class**, rate form [ShalevShwartzBenDavid2014, Corollary
4.6]: a finite class `H` has uniform convergence rate `√(log (2 |H| / δ) / (2 m))` over all
distributions. -/
theorem hasUniformConvergenceRate_finset {H : Finset (α → β)}
    (hH : ∀ h ∈ H, MeasurableSet {p : α × β | h p.1 ≠ p.2}) :
    HasUniformConvergenceRate (H : Set (α → β)) Set.univ
      fun m δ => √(Real.log (2 * H.card / δ) / (2 * m)) := by
  intro D _ _ m hm δ hδ
  refine measure_pi_not_isRepresentative_le_of_log_le D hH (Real.sqrt_nonneg _) hδ ?_
  set L := Real.log (2 * H.card / δ)
  rcases le_or_gt L 0 with hL | hL
  · exact hL.trans (by positivity)
  · have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    rw [Real.sq_sqrt (by positivity)]
    field_simp
    rfl

/-- **Hoeffding's inequality as a rate**: one hypothesis with a measurable misclassification set
has uniform convergence rate `√(log (2 / δ) / (2 m))` over all distributions. -/
theorem hasUniformConvergenceRate_singleton {h : α → β}
    (hh : MeasurableSet {p : α × β | h p.1 ≠ p.2}) :
    HasUniformConvergenceRate {h} Set.univ fun m δ => √(Real.log (2 / δ) / (2 * m)) := by
  have := hasUniformConvergenceRate_finset (H := {h}) (by simpa using hh)
  simpa using this

/-- The Hoeffding rate `√(log c / (2 m))` tends to `0` as `m → ∞`. -/
theorem tendsto_sqrt_log_div_two_mul_atTop (c : ℝ) :
    Tendsto (fun m : ℕ => √(Real.log c / (2 * m))) atTop (𝓝 0) := by
  have h := (tendsto_const_div_atTop_nhds_zero_nat (Real.log c / 2 : ℝ)).sqrt
  rw [Real.sqrt_zero] at h
  exact h.congr fun m => by rw [div_div]

end Rates

/-! ### The SRM rule -/

section Rule

variable {α β ι : Type*} [DecidableEq β]

/-- The learner `A` follows the *structural risk minimization* rule for the classes `H i` with
penalties `pen i` [ShalevShwartzBenDavid2014, Section 7.2]: on every sample `S`, it outputs a
hypothesis `h` of some class `H i` minimizing `L_S(h) + pen i` over all pairs `(i, h)` with
`h ∈ H i`. Choosing `pen i = ε i m (w i · δ)` makes `L_S(h) + pen i` the SRM bound. -/
@[expose] def IsSRM {m : ℕ} (A : Learner α β m) (H : ι → ConceptClass α β) (pen : ι → ℝ) : Prop :=
  ∀ S, ∃ i, A S ∈ H i ∧ ∀ j, ∀ h ∈ H j,
    (empiricalMiscount (A S) S : ℝ) / m + pen i ≤ (empiricalMiscount h S : ℝ) / m + pen j

/-- **Existence of an SRM learner.** If some class is nonempty and the penalties tend to infinity
along the cofinite filter, then every sample admits a minimizer of `L_S(h) + pen i`, so an SRM
learner exists. Only finitely many classes have penalty below any bound, and on each of them the
empirical miscount takes finitely many values. -/
theorem exists_isSRM {m : ℕ} {H : ι → ConceptClass α β} (hne : ∃ i, (H i).Nonempty)
    {pen : ι → ℝ} (hpen : Tendsto pen cofinite atTop) :
    ∃ A : Learner α β m, IsSRM A H pen := by
  classical
  obtain ⟨i₀, h₀, hh₀⟩ := hne
  have key : ∀ S : LabeledSample α β m, ∃ i, ∃ g ∈ H i, ∀ j, ∀ h ∈ H j,
      (empiricalMiscount g S : ℝ) / m + pen i ≤ (empiricalMiscount h S : ℝ) / m + pen j := by
    intro S
    set c := (empiricalMiscount h₀ S : ℝ) / m + pen i₀
    have hfin : {i | pen i ≤ c}.Finite :=
      (eventually_cofinite.1 (hpen.eventually (eventually_gt_atTop c))).subset
        fun i (hi : pen i ≤ c) => not_lt.2 hi
    -- Candidate pairs `(i, k)`: an index with small penalty and a miscount attained in `H i`.
    let P : Set (ι × ℕ) := {p | pen p.1 ≤ c ∧ p.2 ≤ m ∧ ∃ h ∈ H p.1, empiricalMiscount h S = p.2}
    have hPfin : P.Finite :=
      (hfin.prod (Set.finite_le_nat m)).subset fun p hp => ⟨hp.1, hp.2.1⟩
    have hmis : ∀ h : α → β, empiricalMiscount h S ≤ m := fun h =>
      (Finset.card_filter_le _ _).trans_eq (Finset.card_fin m)
    have hP₀ : (i₀, empiricalMiscount h₀ S) ∈ P :=
      ⟨le_add_of_nonneg_left (by positivity), hmis h₀, h₀, hh₀, rfl⟩
    obtain ⟨⟨i, k⟩, ⟨-, -, g, hg, rfl⟩, hle⟩ :=
      P.exists_min_image (fun p : ι × ℕ => (p.2 : ℝ) / m + pen p.1) hPfin ⟨_, hP₀⟩
    refine ⟨i, g, hg, fun j h hh => ?_⟩
    by_cases hj : pen j ≤ c
    · exact hle (j, empiricalMiscount h S) ⟨hj, hmis h, h, hh, rfl⟩
    · calc (empiricalMiscount g S : ℝ) / m + pen i ≤ c := hle _ hP₀
        _ ≤ (empiricalMiscount h S : ℝ) / m + pen j := by
          have : (0 : ℝ) ≤ (empiricalMiscount h S : ℝ) / m := by positivity
          linarith [not_le.1 hj]
  choose I g hg hmin using key
  exact ⟨g, fun S => ⟨I S, hg S, hmin S⟩⟩

end Rule

/-! ### The SRM bound -/

section SRM

variable {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [DecidableEq β] [Countable ι]

/-- **The SRM bound** [ShalevShwartzBenDavid2014, Theorem 7.4], representativeness form: if each
class `H i` has uniform convergence rate `ε i` over `𝒟` and `w` is a weighting of the countable
index type, then for every `D ∈ 𝒟`, `m > 0` and `δ > 0`, with probability at least `1 - δ` the
sample is `ε i m (w i · δ)`-representative for every `H i` simultaneously. -/
theorem Weighting.measure_pi_exists_not_isRepresentative_le {H : ι → ConceptClass α β}
    {𝒟 : Set (Measure (α × β))} {ε : ι → ℕ → ℝ → ℝ}
    (hH : ∀ i, HasUniformConvergenceRate (H i) 𝒟 (ε i)) (w : Weighting ι)
    (D : Measure (α × β)) [IsProbabilityMeasure D] (hD : D ∈ 𝒟) {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D)
        {S | ∃ i, ¬ IsRepresentative D (H i) (ε i m (w i * δ)) S} ≤ ENNReal.ofReal δ := by
  rw [ofPred_exists]
  refine (measure_iUnion_le _).trans ?_
  calc ∑' i, Measure.pi (fun _ : Fin m => D)
        {S | ¬ IsRepresentative D (H i) (ε i m (w i * δ)) S}
      ≤ ∑' i, ENNReal.ofReal (w i * δ) :=
        tsum_le_tsum fun i => hH i D hD m hm _ (mul_pos (w.pos i) hδ)
    _ = ENNReal.ofReal (∑' i, w i * δ) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => (mul_pos (w.pos i) hδ).le)
          (w.summable.mul_right δ)).symm
    _ ≤ ENNReal.ofReal δ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [tsum_mul_right]
        exact mul_le_of_le_one_left hδ.le w.tsum_le_one

/-- **The SRM bound** [ShalevShwartzBenDavid2014, Theorem 7.4]: with probability at least `1 - δ`,
every `h ∈ H i` has `L_D(h) ≤ L_S(h) + ε i m (w i · δ)`. -/
theorem Weighting.measure_pi_exists_lt_error_le {H : ι → ConceptClass α β}
    {𝒟 : Set (Measure (α × β))} {ε : ι → ℕ → ℝ → ℝ}
    (hH : ∀ i, HasUniformConvergenceRate (H i) 𝒟 (ε i)) (w : Weighting ι)
    (D : Measure (α × β)) [IsProbabilityMeasure D] (hD : D ∈ 𝒟) {m : ℕ} (hm : 0 < m)
    {δ : ℝ} (hδ : 0 < δ) :
    Measure.pi (fun _ : Fin m => D)
        {S | ∃ i, ∃ h ∈ H i,
          (empiricalMiscount h S : ℝ) / m + ε i m (w i * δ) < (error D h).toReal} ≤
      ENNReal.ofReal δ := by
  refine (measure_mono fun S => ?_).trans
    (w.measure_pi_exists_not_isRepresentative_le hH D hD hm hδ)
  rintro ⟨i, h, hh, hlt⟩
  exact ⟨i, fun hrep => by linarith [(abs_le.1 (hrep h hh)).1]⟩

/-- **Excess risk of SRM** [ShalevShwartzBenDavid2014, Theorem 7.5, proof]: an SRM learner whose
penalties dominate the rates `ε i m (w i · δ)` satisfies, with probability at least `1 - δ`,
`L_D(A S) ≤ L_D(h) + 2 pen i` for every `i` and every `h ∈ H i`. -/
theorem IsSRM.measure_pi_exists_lt_error_le {H : ι → ConceptClass α β}
    {𝒟 : Set (Measure (α × β))} {ε : ι → ℕ → ℝ → ℝ}
    (hH : ∀ i, HasUniformConvergenceRate (H i) 𝒟 (ε i)) (w : Weighting ι)
    {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 < δ) {pen : ι → ℝ}
    (hpen : ∀ i, ε i m (w i * δ) ≤ pen i) {A : Learner α β m} (hA : IsSRM A H pen)
    (D : Measure (α × β)) [IsProbabilityMeasure D] (hD : D ∈ 𝒟) :
    Measure.pi (fun _ : Fin m => D)
        {S | ∃ i, ∃ h ∈ H i, (error D h).toReal + 2 * pen i < (error D (A S)).toReal} ≤
      ENNReal.ofReal δ := by
  refine (measure_mono fun S => ?_).trans
    (w.measure_pi_exists_not_isRepresentative_le hH D hD hm hδ)
  rintro ⟨j, h, hh, hlt⟩
  by_contra hbad
  have hall : ∀ i, IsRepresentative D (H i) (ε i m (w i * δ)) S := fun i =>
    by_contra fun hi => hbad ⟨i, hi⟩
  obtain ⟨i, hAi, hmin⟩ := hA S
  have hA' := (abs_le.1 (((hall i).mono (hpen i)) _ hAi)).1
  have hh' := (abs_le.1 (((hall j).mono (hpen j)) h hh)).2
  linarith [hmin j h hh]

end SRM

end Cslib.MachineLearning.PACLearning
