/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Hellinger
public import CslibFrontier.Probability.HypothesisSelection.LeCamBirge
public import CslibFrontier.Probability.IID
import CslibFrontier.Probability.HypothesisSelection.Likelihood
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.StatisticalDistance.Event
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Scheffé and Le Cam–Birgé tournament hypothesis selection

This module implements parameter-free tournament selection algorithms over finite candidate families
using the robust pairwise tests from
`CslibFrontier.Probability.HypothesisSelection.LeCamBirge`:

1. **Scheffé TV minimum-distance / tournament selection (`scheffeSelect`):** scores each candidate
   `qᵢ` by its worst empirical Scheffé discrepancy `max_{j ∈ s} |μ_n(A_{j,i}) - qᵢ(A_{j,i})|`
   over the pairwise Scheffé witness sets `A_{j,i} = {a | qᵢ(a) < qⱼ(a)}`, and selects a
   minimizer. Under any true distribution `p` (not necessarily in the family), it outputs a model
   satisfying `dist p q_hat ≤ 3 * dist p q_* + 2 * γ` simultaneously for all `q_* ∈ s`, except
   with probability at most `2 * M * (M - 1) * Real.exp (-2 * n * γ ^ 2)` (this one-sided
   `scheffeScore` formulation and Hoeffding union-bound proof are this library's formulation; see
   [DevroyeLugosi2001] as background).
2. **Adaptive Le Cam–Birgé Hellinger tournament (`birgeTournamentSelect`):** runs all pairwise
   `leCamBirgeTest` comparisons, defines each candidate's maximum defeat radius, and selects a
   minimizer without needing prior knowledge of the approximation error `r`. Whenever some
   candidate `q₀` satisfies `h(p, q₀) ≤ r`, the selected model satisfies `h(p, q_hat) ≤ 11 * r`
   except with probability at most `2 * (M - 1) * Real.exp (-4 * n * r ^ 2)` (this library's
   explicit constants derived from the clipped `1/3`–`2/3` `birgeWeight` test; see [LeCam1973]
   and [Birge1983] as background). Taking a finite Hellinger `r`-cover yields `11 * r` agnostic
   selection over an arbitrary distribution class (`birgeTournamentSelect_of_cover`).

## Main definitions

* `Cslib.Probability.HypothesisSelection.scheffeScore`,
  `Cslib.Probability.HypothesisSelection.scheffeSelect`,
  `Cslib.Probability.HypothesisSelection.scheffeSelectFin`: Scheffé tournament score and selector.
* `Cslib.Probability.HypothesisSelection.maxDefeatRadius`,
  `Cslib.Probability.HypothesisSelection.birgeTournamentSelect`,
  `Cslib.Probability.HypothesisSelection.birgeTournamentSelectFin`: parameter-free Le Cam–Birgé
  Hellinger tournament selector.

## Main results

* `Cslib.Probability.HypothesisSelection.scheffeSelect_dist_le_of_forall`,
  `Cslib.Probability.HypothesisSelection.scheffeSelect_prob_gt_le`: `3 * OPT + 2 * γ` TV guarantee
  with probability at least `1 - 2 * M * (M - 1) * Real.exp (-2 * n * γ ^ 2)`.
* `Cslib.Probability.HypothesisSelection.birgeTournamentSelect_hellingerDist_le_of_good`,
  `Cslib.Probability.HypothesisSelection.birgeTournamentSelect_prob_gt_le`,
  `Cslib.Probability.HypothesisSelection.birgeTournamentSelect_of_cover`: adaptive `11 * r`
  Hellinger tournament guarantee with probability at least `1 - 2 * (M - 1) * exp (-4 * n * r ^ 2)`.

## References

* [Lucien Birgé, *Approximation dans les espaces métriques et théorie de l'estimation*][Birge1983]
  (bibliographic metadata only; article text not inspected).
* [Luc Devroye and Gábor Lugosi, *Combinatorial Methods in Density Estimation*][DevroyeLugosi2001]
  (bibliographic metadata only; book text not inspected, no chapter/theorem numbers claimed).
* [Lucien Le Cam, *Convergence of Estimates Under Dimensionality Restrictions*][LeCam1973]
  (bibliographic metadata only; article text not inspected).
-/

public section

namespace Cslib.Probability.HypothesisSelection

open Cslib.Probability.PMF Finset
open scoped BigOperators ENNReal

variable {ι α : Type*}

section ScheffeTournament

variable [Fintype α] [DecidableEq α]

/-- Worst empirical Scheffé discrepancy of candidate `i` against challengers in `s`:
`max_{j ∈ s} |empiricalMass (scheffeSet (models j) (models i)) x - (models i)(scheffeSet ...)|`.
-/
@[expose] noncomputable def scheffeScore (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) {n : ℕ} (x : Fin n → α) (i : ι) : ℝ :=
  s.sup' hs fun j =>
    |empiricalMass (scheffeSet (models j) (models i)) x -
      ((models i).toOuterMeasure (scheffeSet (models j) (models i) : Set α)).toReal|

/-- Scheffé tournament selector: picks an index in `s` minimizing `scheffeScore`. -/
@[expose] noncomputable def scheffeSelect (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) {n : ℕ} (x : Fin n → α) : ι :=
  Classical.choose (s.exists_min_image (scheffeScore s hs models x) hs)

/-- Membership of `scheffeSelect s hs models x` in `s`. -/
theorem scheffeSelect_mem (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) {n : ℕ} (x : Fin n → α) :
    scheffeSelect s hs models x ∈ s :=
  (Classical.choose_spec (s.exists_min_image (scheffeScore s hs models x) hs)).1

private theorem scheffeSelect_le (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) {n : ℕ} (x : Fin n → α) {j : ι} (hj : j ∈ s) :
    scheffeScore s hs models x (scheffeSelect s hs models x) ≤ scheffeScore s hs models x j :=
  (Classical.choose_spec (s.exists_min_image (scheffeScore s hs models x) hs)).2 j hj

private theorem abs_empiricalMass_sub_model_le (p q₀ q₁ : _root_.PMF α) {n : ℕ}
    (x : Fin n → α) :
    |empiricalMass (scheffeSet q₀ q₁) x - (q₁.toOuterMeasure (scheffeSet q₀ q₁ : Set α)).toReal| ≤
      |empiricalMass (scheffeSet q₀ q₁) x - (p.toOuterMeasure (scheffeSet q₀ q₁ : Set α)).toReal| +
        dist p q₁ := by
  let A := scheffeSet q₀ q₁
  have h2 : |(p.toOuterMeasure (A : Set α)).toReal -
      (q₁.toOuterMeasure (A : Set α)).toReal| ≤ dist p q₁ :=
    abs_toOuterMeasure_toReal_sub_le_dist p q₁ (A : Set α)
  calc |empiricalMass A x - (q₁.toOuterMeasure (A : Set α)).toReal|
      = |(empiricalMass A x - (p.toOuterMeasure (A : Set α)).toReal) +
          ((p.toOuterMeasure (A : Set α)).toReal -
            (q₁.toOuterMeasure (A : Set α)).toReal)| := by ring_nf
    _ ≤ |empiricalMass A x - (p.toOuterMeasure (A : Set α)).toReal| +
          |(p.toOuterMeasure (A : Set α)).toReal -
            (q₁.toOuterMeasure (A : Set α)).toReal| := abs_add_le _ _
    _ ≤ _ := add_le_add le_rfl h2

private theorem scheffeScore_le_of_forall {p : _root_.PMF α} {s : Finset ι} {hs : s.Nonempty}
    {models : ι → _root_.PMF α} {n : ℕ} {x : Fin n → α} {γ : ℝ} (hγ : 0 ≤ γ)
    (hgood : ∀ j ∈ s, ∀ k ∈ s, j ≠ k →
      |empiricalMass (scheffeSet (models j) (models k)) x -
        (p.toOuterMeasure (scheffeSet (models j) (models k) : Set α)).toReal| ≤ γ)
    {i : ι} (hi : i ∈ s) :
    scheffeScore s hs models x i ≤ dist p (models i) + γ := by
  refine Finset.sup'_le hs _ fun j hj => ?_
  have h1 : |empiricalMass (scheffeSet (models j) (models i)) x -
      (p.toOuterMeasure (scheffeSet (models j) (models i) : Set α)).toReal| ≤ γ := by
    by_cases hji : j = i
    · subst hji; simp [scheffeSet_self, empiricalMass, hγ]
    · exact hgood j hj i hi hji
  linarith [abs_empiricalMass_sub_model_le p (models j) (models i) x]

private theorem scheffeScore_lt_of_forall {p : _root_.PMF α} {s : Finset ι} {hs : s.Nonempty}
    {models : ι → _root_.PMF α} {n : ℕ} {x : Fin n → α} {γ : ℝ} (hγ : 0 < γ)
    (hgood : ∀ j ∈ s, ∀ k ∈ s, j ≠ k →
      |empiricalMass (scheffeSet (models j) (models k)) x -
        (p.toOuterMeasure (scheffeSet (models j) (models k) : Set α)).toReal| < γ)
    {i : ι} (hi : i ∈ s) :
    scheffeScore s hs models x i < dist p (models i) + γ := by
  rcases Finset.exists_mem_eq_sup' hs (fun j =>
      |empiricalMass (scheffeSet (models j) (models i)) x -
        ((models i).toOuterMeasure (scheffeSet (models j) (models i) : Set α)).toReal|) with
    ⟨j, hj, hsup⟩
  rw [scheffeScore, hsup]
  have h1 : |empiricalMass (scheffeSet (models j) (models i)) x -
      (p.toOuterMeasure (scheffeSet (models j) (models i) : Set α)).toReal| < γ := by
    by_cases hji : j = i
    · subst hji; simp [scheffeSet_self, empiricalMass, hγ]
    · exact hgood j hj i hi hji
  linarith [abs_empiricalMass_sub_model_le p (models j) (models i) x]

private theorem scheffe_pair_dist_bound {p : _root_.PMF α} {s : Finset ι} {hs : s.Nonempty}
    {models : ι → _root_.PMF α} {n : ℕ} {x : Fin n → α} {i₀ ihat : ι} (hi₀ : i₀ ∈ s) :
    dist (models i₀) (models ihat) ≤
      |empiricalMass (scheffeSet (models i₀) (models ihat)) x -
        (p.toOuterMeasure (scheffeSet (models i₀) (models ihat) : Set α)).toReal| +
      dist p (models i₀) + scheffeScore s hs models x ihat := by
  let A := scheffeSet (models i₀) (models ihat)
  have h2 := (abs_le.mp (abs_toOuterMeasure_toReal_sub_le_dist p (models i₀) (A : Set α))).1
  have h3 := (abs_le.mp (Finset.le_sup' (fun j =>
    |empiricalMass (scheffeSet (models j) (models ihat)) x -
      ((models ihat).toOuterMeasure (scheffeSet (models j) (models ihat) : Set α)).toReal|)
    hi₀)).2
  have hgap := scheffeSet_sub_eq_dist (models i₀) (models ihat)
  change ((models i₀).toOuterMeasure (A : Set α)).toReal -
      ((models ihat).toOuterMeasure (A : Set α)).toReal = dist (models i₀) (models ihat) at hgap
  change empiricalMass A x - ((models ihat).toOuterMeasure (A : Set α)).toReal ≤
      scheffeScore s hs models x ihat at h3
  have hle : (p.toOuterMeasure (A : Set α)).toReal - empiricalMass A x ≤
      |empiricalMass A x - (p.toOuterMeasure (A : Set α)).toReal| := by
    rw [← abs_neg]
    simpa only [neg_sub] using le_abs_self
      ((p.toOuterMeasure (A : Set α)).toReal - empiricalMass A x)
  linarith

/-- Deterministic TV guarantee for `scheffeSelect`: if empirical frequencies on all pairwise Scheffé
sets approximate `p` within `γ ≥ 0`, then `dist p q_hat ≤ 3 * dist p q₀ + 2 * γ` for every
`i₀ ∈ s`. -/
theorem scheffeSelect_dist_le_of_forall {p : _root_.PMF α} (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) {n : ℕ} {x : Fin n → α} {γ : ℝ} (hγ : 0 ≤ γ)
    {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hgood : ∀ j ∈ s, ∀ k ∈ s, j ≠ k →
      |empiricalMass (scheffeSet (models j) (models k)) x -
        (p.toOuterMeasure (scheffeSet (models j) (models k) : Set α)).toReal| ≤ γ) :
    dist p (models (scheffeSelect s hs models x)) ≤ 3 * dist p (models i₀) + 2 * γ := by
  let ihat := scheffeSelect s hs models x
  have hscore_hat : scheffeScore s hs models x ihat ≤ dist p (models i₀) + γ :=
    (scheffeSelect_le s hs models x hi₀).trans (scheffeScore_le_of_forall hγ hgood hi₀)
  have h1 : |empiricalMass (scheffeSet (models i₀) (models ihat)) x -
      (p.toOuterMeasure (scheffeSet (models i₀) (models ihat) : Set α)).toReal| ≤ γ := by
    by_cases hne : i₀ = ihat
    · subst hne; simp [scheffeSet_self, empiricalMass, hγ]
    · exact hgood i₀ hi₀ ihat (scheffeSelect_mem s hs models x) hne
  linarith [scheffe_pair_dist_bound (p := p) (s := s) (hs := hs) (models := models)
    (x := x) (ihat := ihat) hi₀, dist_triangle p (models i₀) (models ihat)]

/-- Strict deterministic TV guarantee for `scheffeSelect` when `γ > 0`. -/
theorem scheffeSelect_dist_lt_of_forall {p : _root_.PMF α} (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) {n : ℕ} {x : Fin n → α} {γ : ℝ} (hγ : 0 < γ)
    {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hgood : ∀ j ∈ s, ∀ k ∈ s, j ≠ k →
      |empiricalMass (scheffeSet (models j) (models k)) x -
        (p.toOuterMeasure (scheffeSet (models j) (models k) : Set α)).toReal| < γ) :
    dist p (models (scheffeSelect s hs models x)) < 3 * dist p (models i₀) + 2 * γ := by
  let ihat := scheffeSelect s hs models x
  by_cases hsame : i₀ = ihat
  · change dist p (models ihat) < 3 * dist p (models i₀) + 2 * γ
    rw [← hsame]
    linarith [dist_nonneg (x := p) (y := models i₀)]
  have hscore_hat : scheffeScore s hs models x ihat < dist p (models i₀) + γ :=
    (scheffeSelect_le s hs models x hi₀).trans_lt (scheffeScore_lt_of_forall hγ hgood hi₀)
  have h1 : |empiricalMass (scheffeSet (models i₀) (models ihat)) x -
      (p.toOuterMeasure (scheffeSet (models i₀) (models ihat) : Set α)).toReal| < γ :=
    hgood i₀ hi₀ ihat (scheffeSelect_mem s hs models x) hsame
  linarith [scheffe_pair_dist_bound (p := p) (s := s) (hs := hs) (models := models)
    (x := x) (ihat := ihat) hi₀, dist_triangle p (models i₀) (models ihat)]

private theorem toOuterMeasure_scheffe_bad_union_le (p : _root_.PMF α)
    (s : Finset ι) (hs : s.Nonempty) (models : ι → _root_.PMF α) (n : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    ((iid p n).toOuterMeasure
      (⋃ jk ∈ s.offDiag,
        {x | γ ≤ |empiricalMass (scheffeSet (models jk.1) (models jk.2)) x -
          (p.toOuterMeasure (scheffeSet (models jk.1) (models jk.2) : Set α)).toReal|})).toReal ≤
      2 * (s.card * (s.card - 1) : ℝ) * Real.exp (-2 * (n : ℝ) * γ ^ 2) := by
  have hunion := toOuterMeasure_toReal_biUnion_finset_le (iid p n) s.offDiag fun jk =>
    {x | γ ≤ |empiricalMass (scheffeSet (models jk.1) (models jk.2)) x -
      (p.toOuterMeasure (scheffeSet (models jk.1) (models jk.2) : Set α)).toReal|}
  have hsum : ∑ jk ∈ s.offDiag, ((iid p n).toOuterMeasure
      {x | γ ≤ |empiricalMass (scheffeSet (models jk.1) (models jk.2)) x -
        (p.toOuterMeasure (scheffeSet (models jk.1) (models jk.2) : Set α)).toReal|}).toReal ≤
      ∑ _jk ∈ s.offDiag, 2 * Real.exp (-2 * (n : ℝ) * γ ^ 2) :=
    Finset.sum_le_sum fun jk _ =>
      abs_empiricalMass_sub_ge_le p (scheffeSet (models jk.1) (models jk.2)) n hγ
  have hcard : (s.offDiag.card : ℝ) = (s.card * (s.card - 1) : ℝ) := by
    have hnat : s.offDiag.card = s.card * (s.card - 1) := by
      rw [Finset.offDiag_card, Nat.mul_sub_left_distrib, mul_one]
    rw [hnat, Nat.cast_mul, Nat.cast_sub hs.card_pos, Nat.cast_one]
  refine hunion.trans (hsum.trans_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, hcard]
  ring

/-- Probabilistic TV localization guarantee for `scheffeSelect` (`0 ≤ γ`, strict failure event):
for every `p` and `i₀ ∈ s`, `dist p (models (scheffeSelect s hs models x)) ≤ 3 * dist p (models i₀)
+ 2 * γ` except with probability at most `2 * M * (M - 1) * Real.exp (-2 * n * γ ^ 2)`. -/
theorem scheffeSelect_prob_gt_le (p : _root_.PMF α) (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) {i₀ : ι} (hi₀ : i₀ ∈ s) (n : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    ((iid p n).toOuterMeasure
      {x | 3 * dist p (models i₀) + 2 * γ < dist p (models (scheffeSelect s hs models x))}).toReal
      ≤ 2 * (s.card * (s.card - 1) : ℝ) * Real.exp (-2 * (n : ℝ) * γ ^ 2) := by
  have hsub :
      {x : Fin n → α |
          3 * dist p (models i₀) + 2 * γ < dist p (models (scheffeSelect s hs models x))} ⊆
        ⋃ jk ∈ s.offDiag,
          {x | γ ≤ |empiricalMass (scheffeSet (models jk.1) (models jk.2)) x -
            (p.toOuterMeasure (scheffeSet (models jk.1) (models jk.2) : Set α)).toReal|} := by
    intro x hx
    classical
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_offDiag, not_exists,
      not_le] at hnot
    have hle := scheffeSelect_dist_le_of_forall s hs models hγ hi₀ fun j hj k hk hjk =>
      (hnot (j, k) ⟨hj, hk, hjk⟩).le
    have hlt : 3 * dist p (models i₀) + 2 * γ <
        dist p (models (scheffeSelect s hs models x)) := hx
    linarith
  classical
  exact (toOuterMeasure_toReal_mono _ hsub).trans
    (toOuterMeasure_scheffe_bad_union_le p s hs models n hγ)

/-- Probabilistic TV localization guarantee for `scheffeSelect` (`0 < γ`, non-strict failure
event). -/
theorem scheffeSelect_prob_ge_le (p : _root_.PMF α) (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) {i₀ : ι} (hi₀ : i₀ ∈ s) (n : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ((iid p n).toOuterMeasure
      {x | 3 * dist p (models i₀) + 2 * γ ≤ dist p (models (scheffeSelect s hs models x))}).toReal
      ≤ 2 * (s.card * (s.card - 1) : ℝ) * Real.exp (-2 * (n : ℝ) * γ ^ 2) := by
  have hsub :
      {x : Fin n → α |
          3 * dist p (models i₀) + 2 * γ ≤ dist p (models (scheffeSelect s hs models x))} ⊆
        ⋃ jk ∈ s.offDiag,
          {x | γ ≤ |empiricalMass (scheffeSet (models jk.1) (models jk.2)) x -
            (p.toOuterMeasure (scheffeSet (models jk.1) (models jk.2) : Set α)).toReal|} := by
    intro x hx
    classical
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_offDiag, not_exists,
      not_le] at hnot
    have hlt := scheffeSelect_dist_lt_of_forall s hs models hγ hi₀ fun j hj k hk hjk =>
      hnot (j, k) ⟨hj, hk, hjk⟩
    have hle : 3 * dist p (models i₀) + 2 * γ ≤
        dist p (models (scheffeSelect s hs models x)) := hx
    linarith
  classical
  exact (toOuterMeasure_toReal_mono _ hsub).trans
    (toOuterMeasure_scheffe_bad_union_le p s hs models n hγ.le)

/-- `Fin M`-indexed specialization of `scheffeSelect`. -/
@[expose] noncomputable def scheffeSelectFin {M : ℕ} [NeZero M] (models : Fin M → _root_.PMF α)
    {n : ℕ} (x : Fin n → α) : Fin M :=
  scheffeSelect Finset.univ Finset.univ_nonempty models x

/-- `Fin M` TV localization guarantee for `scheffeSelectFin` (`0 ≤ γ`). -/
theorem scheffeSelectFin_prob_gt_le (p : _root_.PMF α) {M : ℕ} [NeZero M]
    (models : Fin M → _root_.PMF α) (i₀ : Fin M) (n : ℕ) {γ : ℝ} (hγ : 0 ≤ γ) :
    ((iid p n).toOuterMeasure
      {x | 3 * dist p (models i₀) + 2 * γ < dist p (models (scheffeSelectFin models x))}).toReal ≤
      2 * (M * (M - 1) : ℝ) * Real.exp (-2 * (n : ℝ) * γ ^ 2) := by
  simpa only [scheffeSelectFin, Finset.card_univ, Fintype.card_fin] using
    scheffeSelect_prob_gt_le p Finset.univ Finset.univ_nonempty models (Finset.mem_univ i₀) n hγ

/-- `Fin M` TV localization guarantee for `scheffeSelectFin` (`0 < γ`). -/
theorem scheffeSelectFin_prob_ge_le (p : _root_.PMF α) {M : ℕ} [NeZero M]
    (models : Fin M → _root_.PMF α) (i₀ : Fin M) (n : ℕ) {γ : ℝ} (hγ : 0 < γ) :
    ((iid p n).toOuterMeasure
      {x | 3 * dist p (models i₀) + 2 * γ ≤ dist p (models (scheffeSelectFin models x))}).toReal ≤
      2 * (M * (M - 1) : ℝ) * Real.exp (-2 * (n : ℝ) * γ ^ 2) := by
  simpa only [scheffeSelectFin, Finset.card_univ, Fintype.card_fin] using
    scheffeSelect_prob_ge_le p Finset.univ Finset.univ_nonempty models (Finset.mem_univ i₀) n hγ

/-- Sample complexity for `scheffeSelectFin`: `n ≥ log (2 * M^2 / δ) / (2 * γ^2)` suffices for
`dist p (models (scheffeSelectFin models x)) < 3 * dist p (models i₀) + 2 * γ` with probability at
least `1 - δ`. -/
theorem scheffeSelectFin_ge_le_of_log (p : _root_.PMF α) {M : ℕ} [NeZero M]
    (models : Fin M → _root_.PMF α) (i₀ : Fin M) {n : ℕ} {γ δ : ℝ}
    (hγ : 0 < γ) (hδ : 0 < δ)
    (hn : Real.log (2 * (M : ℝ) ^ 2 / δ) / (2 * γ ^ 2) ≤ n) :
    ((iid p n).toOuterMeasure
      {x | 3 * dist p (models i₀) + 2 * γ ≤ dist p (models (scheffeSelectFin models x))}).toReal ≤
      δ := by
  refine (scheffeSelectFin_prob_ge_le p models i₀ n hγ).trans ?_
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  have hcK : 2 * ((M : ℝ) * ((M : ℝ) - 1)) ≤ 2 * (M : ℝ) ^ 2 := by nlinarith
  rw [show (-2 : ℝ) * (n : ℝ) * γ ^ 2 = -(2 * γ ^ 2 * (n : ℝ)) by ring]
  exact mul_exp_neg_le_of_log hcK (by positivity) (by positivity) hδ hn

/-- Agnostic finite-cover TV guarantee for `scheffeSelect`: if `models` on `s` forms an `r`-cover
of `ℱ` in TV distance, then for every `p ∈ ℱ`, `scheffeSelect` recovers a model within
`3 * r + 2 * γ` except with probability at most `2 * M * (M - 1) * Real.exp (-2 * n * γ ^ 2)`. -/
theorem scheffeSelect_of_cover (s : Finset ι) (hs : s.Nonempty) (models : ι → _root_.PMF α)
    (ℱ : Set (_root_.PMF α)) {r γ : ℝ} (hγ : 0 ≤ γ)
    (hcov : ∀ p ∈ ℱ, ∃ i ∈ s, dist p (models i) ≤ r)
    {p : _root_.PMF α} (hp : p ∈ ℱ) (n : ℕ) :
    ((iid p n).toOuterMeasure
      {x | 3 * r + 2 * γ < dist p (models (scheffeSelect s hs models x))}).toReal ≤
      2 * (s.card * (s.card - 1) : ℝ) * Real.exp (-2 * (n : ℝ) * γ ^ 2) := by
  rcases hcov p hp with ⟨i₀, hi₀, hdist⟩
  have hsub :
      {x : Fin n → α | 3 * r + 2 * γ < dist p (models (scheffeSelect s hs models x))} ⊆
        {x : Fin n → α |
          3 * dist p (models i₀) + 2 * γ < dist p (models (scheffeSelect s hs models x))} := by
    intro x hx
    have hlt : 3 * r + 2 * γ < dist p (models (scheffeSelect s hs models x)) := hx
    exact lt_of_le_of_lt (by linarith) hlt
  exact (toOuterMeasure_toReal_mono _ hsub).trans
    (scheffeSelect_prob_gt_le p s hs models hi₀ n hγ)

end ScheffeTournament

section BirgeTournament

/-- Maximum Hellinger defeat radius of candidate `i` in the pairwise Le Cam–Birgé tournament over
`s`: the largest Hellinger distance `h(models i, models j)` to any challenger `j ∈ s` that defeats
`i` (`leCamBirgeTest (models i) (models j) x = false`), or `0` if none defeats `i`. -/
@[expose] noncomputable def maxDefeatRadius (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) {n : ℕ} (x : Fin n → α) (i : ι) : ℝ :=
  s.sup' hs fun j =>
    if leCamBirgeTest (models i) (models j) x then 0 else hellingerDist (models i) (models j)

/-- Parameter-free Le Cam–Birgé Hellinger tournament selector: returns an index in `s` minimizing
`maxDefeatRadius`. -/
@[expose] noncomputable def birgeTournamentSelect (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) {n : ℕ} (x : Fin n → α) : ι :=
  Classical.choose (s.exists_min_image (maxDefeatRadius s hs models x) hs)

/-- Membership of `birgeTournamentSelect s hs models x` in `s`. -/
theorem birgeTournamentSelect_mem (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) {n : ℕ} (x : Fin n → α) :
    birgeTournamentSelect s hs models x ∈ s :=
  (Classical.choose_spec (s.exists_min_image (maxDefeatRadius s hs models x) hs)).1

private theorem birgeTournamentSelect_le (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) {n : ℕ} (x : Fin n → α) {j : ι} (hj : j ∈ s) :
    maxDefeatRadius s hs models x (birgeTournamentSelect s hs models x) ≤
      maxDefeatRadius s hs models x j :=
  (Classical.choose_spec (s.exists_min_image (maxDefeatRadius s hs models x) hs)).2 j hj

private theorem birge_pair_not_le_of_true {s : Finset ι} {models : ι → _root_.PMF α} {n : ℕ}
    {x : Fin n → α} {r : ℝ} {i₀ ihat : ι} (hihat : ihat ∈ s)
    (hlose : ∀ j ∈ s, j ≠ i₀ → 10 * r ≤ hellingerDist (models j) (models i₀) →
      leCamBirgeTest (models j) (models i₀) x = false)
    (hsame : ihat ≠ i₀) (htest : leCamBirgeTest (models ihat) (models i₀) x = true) :
    ¬ (10 * r ≤ hellingerDist (models ihat) (models i₀)) := by
  intro hsep
  have hf := hlose ihat hihat hsame hsep
  rw [htest] at hf
  cases hf

private theorem le_maxDefeatRadius_of_ne_true {s : Finset ι} {hs : s.Nonempty}
    {models : ι → _root_.PMF α} {n : ℕ} {x : Fin n → α} {i₀ ihat : ι} (hi₀ : i₀ ∈ s)
    (htest : leCamBirgeTest (models ihat) (models i₀) x ≠ true) :
    hellingerDist (models ihat) (models i₀) ≤ maxDefeatRadius s hs models x ihat := by
  have hterm := Finset.le_sup' (fun j =>
    if leCamBirgeTest (models ihat) (models j) x then 0
    else hellingerDist (models ihat) (models j)) hi₀
  change (if leCamBirgeTest (models ihat) (models i₀) x then 0
    else hellingerDist (models ihat) (models i₀)) ≤ maxDefeatRadius s hs models x ihat at hterm
  split_ifs at hterm with hc
  · exact absurd hc htest
  · exact hterm

/-- Deterministic `11 * r` Hellinger guarantee for `birgeTournamentSelect`: if `h(p, models i₀) ≤ r`
and no test involving `i₀` makes a `10 * r`-separated error, then the selected model satisfies
`h(p, models i_hat) ≤ 11 * r`. -/
theorem birgeTournamentSelect_hellingerDist_le_of_good [Finite α] {p : _root_.PMF α}
    (s : Finset ι) (hs : s.Nonempty) (models : ι → _root_.PMF α) {n : ℕ} {x : Fin n → α} {r : ℝ}
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hp : hellingerDist p (models i₀) ≤ r)
    (hwin : ∀ j ∈ s, j ≠ i₀ → 10 * r ≤ hellingerDist (models i₀) (models j) →
      leCamBirgeTest (models i₀) (models j) x = true)
    (hlose : ∀ j ∈ s, j ≠ i₀ → 10 * r ≤ hellingerDist (models j) (models i₀) →
      leCamBirgeTest (models j) (models i₀) x = false) :
    hellingerDist p (models (birgeTournamentSelect s hs models x)) ≤ 11 * r := by
  have hr : 0 ≤ r := (hellingerDist_nonneg p (models i₀)).trans hp
  let ihat := birgeTournamentSelect s hs models x
  have hihat : ihat ∈ s := birgeTournamentSelect_mem s hs models x
  have hi₀_rad : maxDefeatRadius s hs models x i₀ ≤ 10 * r := by
    refine Finset.sup'_le hs _ fun j hj => ?_
    split_ifs with htest
    · exact mul_nonneg (by norm_num) hr
    · by_cases hji : j = i₀
      · subst hji
        simpa only [hellingerDist_self] using mul_nonneg (by norm_num) hr
      · exact le_of_not_ge fun hsep => htest (hwin j hj hji hsep)
  have hihat_rad : maxDefeatRadius s hs models x ihat ≤ 10 * r :=
    (birgeTournamentSelect_le s hs models x hi₀).trans hi₀_rad
  have hpair : hellingerDist (models i₀) (models ihat) ≤ 10 * r := by
    rw [hellingerDist_comm]
    by_cases htest : leCamBirgeTest (models ihat) (models i₀) x = true
    · by_cases hsame : ihat = i₀
      · rw [hsame, hellingerDist_self]; exact mul_nonneg (by norm_num) hr
      · exact le_of_not_ge (birge_pair_not_le_of_true hihat hlose hsame htest)
    · exact (le_maxDefeatRadius_of_ne_true hi₀ htest).trans hihat_rad
  calc hellingerDist p (models ihat)
      ≤ hellingerDist p (models i₀) + hellingerDist (models i₀) (models ihat) :=
        hellingerDist_triangle p _ _
    _ ≤ r + 10 * r := add_le_add hp hpair
    _ = 11 * r := by ring

/-- Strict deterministic `11 * r` Hellinger guarantee for `birgeTournamentSelect` when `r > 0`. -/
theorem birgeTournamentSelect_hellingerDist_lt_of_good [Finite α] {p : _root_.PMF α}
    (s : Finset ι) (hs : s.Nonempty) (models : ι → _root_.PMF α) {n : ℕ} {x : Fin n → α} {r : ℝ}
    (hr : 0 < r) {i₀ : ι} (hi₀ : i₀ ∈ s) (hp : hellingerDist p (models i₀) ≤ r)
    (hwin : ∀ j ∈ s, j ≠ i₀ → 10 * r ≤ hellingerDist (models i₀) (models j) →
      leCamBirgeTest (models i₀) (models j) x = true)
    (hlose : ∀ j ∈ s, j ≠ i₀ → 10 * r ≤ hellingerDist (models j) (models i₀) →
      leCamBirgeTest (models j) (models i₀) x = false) :
    hellingerDist p (models (birgeTournamentSelect s hs models x)) < 11 * r := by
  let ihat := birgeTournamentSelect s hs models x
  have hihat : ihat ∈ s := birgeTournamentSelect_mem s hs models x
  have hi₀_rad : maxDefeatRadius s hs models x i₀ < 10 * r := by
    rcases Finset.exists_mem_eq_sup' hs (fun j =>
      if leCamBirgeTest (models i₀) (models j) x then 0
      else hellingerDist (models i₀) (models j)) with ⟨j, hj, hsup⟩
    rw [maxDefeatRadius, hsup]
    split_ifs with htest
    · positivity
    · by_cases hji : j = i₀
      · subst hji
        simpa only [hellingerDist_self] using (by positivity : (0 : ℝ) < 10 * r)
      · exact lt_of_not_ge fun hsep => htest (hwin j hj hji hsep)
  have hihat_rad : maxDefeatRadius s hs models x ihat < 10 * r :=
    (birgeTournamentSelect_le s hs models x hi₀).trans_lt hi₀_rad
  have hpair : hellingerDist (models i₀) (models ihat) < 10 * r := by
    rw [hellingerDist_comm]
    by_cases htest : leCamBirgeTest (models ihat) (models i₀) x = true
    · by_cases hsame : ihat = i₀
      · rw [hsame, hellingerDist_self]; positivity
      · exact lt_of_not_ge (birge_pair_not_le_of_true hihat hlose hsame htest)
    · exact (le_maxDefeatRadius_of_ne_true hi₀ htest).trans_lt hihat_rad
  linarith [hellingerDist_triangle p (models i₀) (models ihat)]

private theorem toOuterMeasure_birge_bad_union_le [Finite α] [DecidableEq ι] {p : _root_.PMF α}
    (s : Finset ι) (models : ι → _root_.PMF α) {i₀ : ι} (hi₀ : i₀ ∈ s) (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hp : hellingerDist p (models i₀) ≤ r) :
    ((iid p n).toOuterMeasure
      (⋃ j ∈ s.erase i₀,
        ({x | 10 * r ≤ hellingerDist (models i₀) (models j) ∧
            leCamBirgeTest (models i₀) (models j) x = false} ∪
          {x | 10 * r ≤ hellingerDist (models j) (models i₀) ∧
            leCamBirgeTest (models j) (models i₀) x = true}))).toReal ≤
      2 * (s.card - 1 : ℝ) * Real.exp (-4 * (n : ℝ) * r ^ 2) := by
  let E₁ : ι → Set (Fin n → α) := fun j =>
    {x | 10 * r ≤ hellingerDist (models i₀) (models j) ∧
      leCamBirgeTest (models i₀) (models j) x = false}
  let E₂ : ι → Set (Fin n → α) := fun j =>
    {x | 10 * r ≤ hellingerDist (models j) (models i₀) ∧
      leCamBirgeTest (models j) (models i₀) x = true}
  have hunion := toOuterMeasure_toReal_biUnion_finset_le (iid p n) (s.erase i₀) fun j => E₁ j ∪ E₂ j
  have hsep_bound (P : Prop) (Q : (Fin n → α) → Prop)
      (hb : P → ((iid p n).toOuterMeasure {x | Q x}).toReal ≤ Real.exp (-4 * (n : ℝ) * r ^ 2)) :
      ((iid p n).toOuterMeasure {x | P ∧ Q x}).toReal ≤ Real.exp (-4 * (n : ℝ) * r ^ 2) := by
    by_cases hP : P
    · exact (toOuterMeasure_toReal_mono _
        (show {x | P ∧ Q x} ⊆ {x | Q x} from fun _ hx => hx.2)).trans (hb hP)
    · have hemp : {x : Fin n → α | P ∧ Q x} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun _ hx => hP hx.1
      rw [hemp, MeasureTheory.measure_empty, ENNReal.toReal_zero]
      exact (Real.exp_pos _).le
  have hterm (j : ι) :
      ((iid p n).toOuterMeasure (E₁ j ∪ E₂ j)).toReal ≤ 2 * Real.exp (-4 * (n : ℝ) * r ^ 2) := by
    have hadd : ((iid p n).toOuterMeasure (E₁ j ∪ E₂ j)).toReal ≤
        ((iid p n).toOuterMeasure (E₁ j)).toReal + ((iid p n).toOuterMeasure (E₂ j)).toReal :=
      ENNReal.toReal_le_add (MeasureTheory.measure_union_le _ _)
        (toOuterMeasure_ne_top _ _) (toOuterMeasure_ne_top _ _)
    have hb₁ := hsep_bound (10 * r ≤ hellingerDist (models i₀) (models j))
      (fun x => leCamBirgeTest (models i₀) (models j) x = false)
      fun hsep => leCamBirgeTest_false_le_of_radius hr hp hsep n
    have hb₂ := hsep_bound (10 * r ≤ hellingerDist (models j) (models i₀))
      (fun x => leCamBirgeTest (models j) (models i₀) x = true)
      fun hsep => leCamBirgeTest_true_le_of_radius hr hp hsep n
    linarith
  have hsum : ∑ j ∈ s.erase i₀, ((iid p n).toOuterMeasure (E₁ j ∪ E₂ j)).toReal ≤
      ∑ _j ∈ s.erase i₀, 2 * Real.exp (-4 * (n : ℝ) * r ^ 2) :=
    Finset.sum_le_sum fun j _ => hterm j
  have hcard : ((s.erase i₀).card : ℝ) = (s.card - 1 : ℝ) := by
    rw [Finset.card_erase_of_mem hi₀, Nat.cast_sub (Finset.Nonempty.card_pos ⟨i₀, hi₀⟩),
      Nat.cast_one]
  refine hunion.trans (hsum.trans_eq ?_)
  rw [Finset.sum_const, nsmul_eq_mul, hcard]
  ring

/-- Adaptive Hellinger localization guarantee for `birgeTournamentSelect` (`r ≥ 0`, strict failure
event): whenever some candidate `models i₀` satisfies `h(p, models i₀) ≤ r`, the selected model
satisfies `h(p, models i_hat) ≤ 11 * r` except with probability at most
`2 * (M - 1) * Real.exp (-4 * n * r ^ 2)`. -/
theorem birgeTournamentSelect_prob_gt_le [Finite α] {p : _root_.PMF α} (s : Finset ι)
    (hs : s.Nonempty) (models : ι → _root_.PMF α) {i₀ : ι} (hi₀ : i₀ ∈ s) (n : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hp : hellingerDist p (models i₀) ≤ r) :
    ((iid p n).toOuterMeasure
      {x | 11 * r < hellingerDist p (models (birgeTournamentSelect s hs models x))}).toReal ≤
      2 * (s.card - 1 : ℝ) * Real.exp (-4 * (n : ℝ) * r ^ 2) := by
  classical
  have hsub :
      {x : Fin n → α |
          11 * r < hellingerDist p (models (birgeTournamentSelect s hs models x))} ⊆
        ⋃ j ∈ s.erase i₀,
          ({x | 10 * r ≤ hellingerDist (models i₀) (models j) ∧
              leCamBirgeTest (models i₀) (models j) x = false} ∪
            {x | 10 * r ≤ hellingerDist (models j) (models i₀) ∧
              leCamBirgeTest (models j) (models i₀) x = true}) := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, Finset.mem_erase, not_exists,
      not_and, not_or] at hnot
    have hle := birgeTournamentSelect_hellingerDist_le_of_good s hs models hi₀ hp
      (fun j hj hji hsep => by
        cases hres : leCamBirgeTest (models i₀) (models j) x
        · exact False.elim ((hnot j ⟨hji, hj⟩).1 hsep hres)
        · rfl)
      (fun j hj hji hsep => by
        cases hres : leCamBirgeTest (models j) (models i₀) x
        · rfl
        · exact False.elim ((hnot j ⟨hji, hj⟩).2 hsep hres))
    have hlt : 11 * r < hellingerDist p (models (birgeTournamentSelect s hs models x)) := hx
    linarith
  exact (toOuterMeasure_toReal_mono _ hsub).trans
    (toOuterMeasure_birge_bad_union_le s models hi₀ n hr hp)

/-- Non-strict failure event form of `birgeTournamentSelect_prob_gt_le` when `r > 0`. -/
theorem birgeTournamentSelect_prob_ge_le [Finite α] {p : _root_.PMF α} (s : Finset ι)
    (hs : s.Nonempty) (models : ι → _root_.PMF α) {i₀ : ι} (hi₀ : i₀ ∈ s) (n : ℕ) {r : ℝ}
    (hr : 0 < r) (hp : hellingerDist p (models i₀) ≤ r) :
    ((iid p n).toOuterMeasure
      {x | 11 * r ≤ hellingerDist p (models (birgeTournamentSelect s hs models x))}).toReal ≤
      2 * (s.card - 1 : ℝ) * Real.exp (-4 * (n : ℝ) * r ^ 2) := by
  classical
  have hsub :
      {x : Fin n → α |
          11 * r ≤ hellingerDist p (models (birgeTournamentSelect s hs models x))} ⊆
        ⋃ j ∈ s.erase i₀,
          ({x | 10 * r ≤ hellingerDist (models i₀) (models j) ∧
              leCamBirgeTest (models i₀) (models j) x = false} ∪
            {x | 10 * r ≤ hellingerDist (models j) (models i₀) ∧
              leCamBirgeTest (models j) (models i₀) x = true}) := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_ofPred_eq, Finset.mem_erase, not_exists,
      not_and, not_or] at hnot
    have hlt := birgeTournamentSelect_hellingerDist_lt_of_good s hs models hr hi₀ hp
      (fun j hj hji hsep => by
        cases hres : leCamBirgeTest (models i₀) (models j) x
        · exact False.elim ((hnot j ⟨hji, hj⟩).1 hsep hres)
        · rfl)
      (fun j hj hji hsep => by
        cases hres : leCamBirgeTest (models j) (models i₀) x
        · rfl
        · exact False.elim ((hnot j ⟨hji, hj⟩).2 hsep hres))
    have hle : 11 * r ≤ hellingerDist p (models (birgeTournamentSelect s hs models x)) := hx
    linarith
  exact (toOuterMeasure_toReal_mono _ hsub).trans
    (toOuterMeasure_birge_bad_union_le s models hi₀ n hr.le hp)

/-- `Fin M`-indexed specialization of `birgeTournamentSelect`. -/
@[expose] noncomputable def birgeTournamentSelectFin {M : ℕ} [NeZero M]
    (models : Fin M → _root_.PMF α) {n : ℕ} (x : Fin n → α) : Fin M :=
  birgeTournamentSelect Finset.univ Finset.univ_nonempty models x

/-- `Fin M` Hellinger tournament bound (`r ≥ 0`). -/
theorem birgeTournamentSelectFin_prob_gt_le [Finite α] {p : _root_.PMF α} {M : ℕ} [NeZero M]
    (models : Fin M → _root_.PMF α) (i₀ : Fin M) (n : ℕ) {r : ℝ} (hr : 0 ≤ r)
    (hp : hellingerDist p (models i₀) ≤ r) :
    ((iid p n).toOuterMeasure
      {x | 11 * r < hellingerDist p (models (birgeTournamentSelectFin models x))}).toReal ≤
      2 * (M - 1 : ℝ) * Real.exp (-4 * (n : ℝ) * r ^ 2) := by
  simpa only [birgeTournamentSelectFin, Finset.card_univ, Fintype.card_fin] using
    birgeTournamentSelect_prob_gt_le Finset.univ Finset.univ_nonempty models (Finset.mem_univ i₀) n
      hr hp

/-- `Fin M` Hellinger tournament bound (`r > 0`). -/
theorem birgeTournamentSelectFin_prob_ge_le [Finite α] {p : _root_.PMF α} {M : ℕ} [NeZero M]
    (models : Fin M → _root_.PMF α) (i₀ : Fin M) (n : ℕ) {r : ℝ} (hr : 0 < r)
    (hp : hellingerDist p (models i₀) ≤ r) :
    ((iid p n).toOuterMeasure
      {x | 11 * r ≤ hellingerDist p (models (birgeTournamentSelectFin models x))}).toReal ≤
      2 * (M - 1 : ℝ) * Real.exp (-4 * (n : ℝ) * r ^ 2) := by
  simpa only [birgeTournamentSelectFin, Finset.card_univ, Fintype.card_fin] using
    birgeTournamentSelect_prob_ge_le Finset.univ Finset.univ_nonempty models (Finset.mem_univ i₀) n
      hr hp

/-- Sample complexity for `birgeTournamentSelectFin`: `n ≥ log (2 * M / δ) / (4 * r^2)` suffices
for `hellingerDist p (models (birgeTournamentSelectFin models x)) < 11 * r` with probability at
least `1 - δ`. -/
theorem birgeTournamentSelectFin_ge_le_of_log [Finite α] {p : _root_.PMF α} {M : ℕ} [NeZero M]
    (models : Fin M → _root_.PMF α) (i₀ : Fin M) {n : ℕ} {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) (hp : hellingerDist p (models i₀) ≤ r)
    (hn : Real.log (2 * (M : ℝ) / δ) / (4 * r ^ 2) ≤ n) :
    ((iid p n).toOuterMeasure
      {x | 11 * r ≤ hellingerDist p (models (birgeTournamentSelectFin models x))}).toReal ≤
      δ := by
  refine (birgeTournamentSelectFin_prob_ge_le models i₀ n hr hp).trans ?_
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  have hcK : 2 * ((M : ℝ) - 1) ≤ 2 * (M : ℝ) := by linarith
  have hK : 0 < 2 * (M : ℝ) := by linarith
  rw [show (-4 : ℝ) * (n : ℝ) * r ^ 2 = -(4 * r ^ 2 * (n : ℝ)) by ring]
  exact mul_exp_neg_le_of_log hcK hK (by positivity) hδ hn

/-- Agnostic finite-cover Hellinger guarantee: if `models` on `s` is a finite Hellinger `r`-cover
of a class `ℱ`, then for every `p ∈ ℱ`, `birgeTournamentSelect` outputs a model within Hellinger
radius `11 * r` except with probability at most `2 * (s.card - 1) * Real.exp (-4 * n * r ^ 2)`. -/
theorem birgeTournamentSelect_of_cover [Finite α] (s : Finset ι) (hs : s.Nonempty)
    (models : ι → _root_.PMF α) (ℱ : Set (_root_.PMF α)) {r : ℝ} (hr : 0 ≤ r)
    (hcov : ∀ p ∈ ℱ, ∃ i ∈ s, hellingerDist p (models i) ≤ r)
    {p : _root_.PMF α} (hp : p ∈ ℱ) (n : ℕ) :
    ((iid p n).toOuterMeasure
      {x | 11 * r < hellingerDist p (models (birgeTournamentSelect s hs models x))}).toReal ≤
      2 * (s.card - 1 : ℝ) * Real.exp (-4 * (n : ℝ) * r ^ 2) := by
  rcases hcov p hp with ⟨i₀, hi₀, hdist⟩
  exact birgeTournamentSelect_prob_gt_le s hs models hi₀ n hr hdist

end BirgeTournament

end Cslib.Probability.HypothesisSelection
