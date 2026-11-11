/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/`)

public import CslibFrontier.Init
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Algebra.Monoid

/-!
# Bonferroni inequalities and Poisson convergence via factorial moments

For a finite family of measurable events `A : ι → Set Ω` on a finite measure space `(Ω, μ)`,
writing `S r := ∑ s ∈ Finset.powersetCard r Finset.univ, μ.real (⋂ i ∈ s, A i)` for the `r`-th
binomial (factorial) moment of the count `X ω = Nat.card {i : ι // ω ∈ A i}`:

* `ProbabilityTheory.measureReal_natCard_eq_le_bonferroni` and
  `ProbabilityTheory.bonferroni_le_measureReal_natCard_eq`: the truncated inclusion-exclusion
  (**Bonferroni**) upper and lower bounds for `μ.real {ω | Nat.card {i // ω ∈ A i} = k}` at any
  odd (`2 * m + 1`) or even (`2 * m`) truncation depth (see [FriezeKaronski2016] Lemma 33.10,
  pp. 696–697).
* `ProbabilityTheory.measureReal_forall_notMem_le_bonferroni` and
  `ProbabilityTheory.bonferroni_le_measureReal_forall_notMem`: the `k = 0` specialization for
  `μ.real {ω | ∀ i, ω ∉ A i}`.
* `ProbabilityTheory.tendsto_measureReal_natCard_eq_poisson_of_factorialMoments`: **Brun's sieve**
  (Poisson convergence from factorial moments): if for every fixed `r : ℕ` the `r`-th binomial
  moment converges to `lam ^ r / r!`, then
  `(μ n).real {ω | Nat.card {i // ω ∈ A n i} = k} → exp (-lam) * (lam ^ k / k!)` for every
  `k : ℕ` (see [FriezeKaronski2016] Theorem 33.11, pp. 697–698).

The source's `B_r` (written `B_k = E[choose(S_n, k)]`) is formalized here as the sum of `r`-fold
intersection measures with limit `lam ^ r / r!` (binomial-moment normalization). The formalization
deliberately extends the result to finite measures by using the `r = 0` hypothesis to require that
the total mass converges to 1.

## Main results

* `ProbabilityTheory.measurableSet_natCard_eq`
* `ProbabilityTheory.measureReal_natCard_eq_le_bonferroni`
* `ProbabilityTheory.bonferroni_le_measureReal_natCard_eq`
* `ProbabilityTheory.measureReal_forall_notMem_le_bonferroni`
* `ProbabilityTheory.bonferroni_le_measureReal_forall_notMem`
* `ProbabilityTheory.tendsto_measureReal_natCard_eq_poisson_of_factorialMoments`
-/

public section

open MeasureTheory Finset Filter
open scoped Topology

namespace ProbabilityTheory

section Bonferroni

variable {Ω ι : Type*}

/-- Pointwise alternating binomial identity:
`∑ r ∈ range (M + 1), (-1)^r * C(d + 1, r) = (-1)^M * C(d, M)`. -/
private theorem sum_neg_one_pow_mul_choose_succ (d M : ℕ) :
    ∑ r ∈ Finset.range (M + 1), (-1 : ℝ) ^ r * ((d + 1).choose r : ℝ) =
      (-1 : ℝ) ^ M * (d.choose M : ℝ) := by
  have h := congrArg (Int.cast (R := ℝ))
    (Int.alternating_sum_range_choose_eq_choose (n := d) (m := M))
  push_cast at h
  exact h

private theorem sum_neg_one_pow_mul_choose_eq_zero (N : ℕ) (hN : 0 < N) :
    ∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * ((0 : ℕ).choose r : ℝ) = 1 := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.choose_zero_succ,
    Nat.cast_zero, mul_zero, Finset.sum_const_zero, zero_add]

private theorem sum_neg_one_pow_mul_choose_odd_nonneg (d m : ℕ) (hd : 0 < d) :
    0 ≤ ∑ r ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ r * (d.choose r : ℝ) := by
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  rw [sum_neg_one_pow_mul_choose_succ d' (2 * m), pow_mul, neg_one_sq, one_pow, one_mul]
  exact Nat.cast_nonneg _

private theorem sum_neg_one_pow_mul_choose_even_nonpos (d m : ℕ) (hd : 0 < d) :
    ∑ r ∈ Finset.range (2 * m), (-1 : ℝ) ^ r * (d.choose r : ℝ) ≤ 0 := by
  rcases m with _ | m
  · simp
  · obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
    have heq : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
    rw [heq, sum_neg_one_pow_mul_choose_succ d' (2 * m + 1), pow_succ, pow_mul, neg_one_sq,
      one_pow, one_mul, neg_one_mul]
    exact neg_nonpos.mpr (Nat.cast_nonneg _)

private theorem natCard_subtype_mem_eq_card [Fintype ι] (A : ι → Set Ω) (ω : Ω)
    [DecidablePred fun i => ω ∈ A i] :
    Nat.card {i : ι // ω ∈ A i} = (Finset.univ.filter fun i : ι => ω ∈ A i).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- Pointwise counting identity: for a finite family `A : ι → Set Ω` and `ω : Ω`, the sum over
`r`-subsets `s` of `{ω | ∀ i ∈ s, ω ∈ A i}.indicator 1 ω` equals `C(Nat.card {i | ω ∈ A i}, r)`. -/
private theorem sum_powersetCard_indicator [Fintype ι] (A : ι → Set Ω) (r : ℕ) (ω : Ω) :
    ∑ s ∈ (Finset.univ : Finset ι).powersetCard r,
        (⋂ i ∈ s, A i).indicator (1 : Ω → ℝ) ω =
      ((Nat.card {i : ι // ω ∈ A i}).choose r : ℝ) := by
  classical
  rw [natCard_subtype_mem_eq_card]
  set T : Finset ι := Finset.univ.filter fun i : ι => ω ∈ A i
  have hmem : ∀ s : Finset ι, (ω ∈ ⋂ i ∈ s, A i) ↔ s ∈ T.powerset := fun s => by
    simp only [Set.mem_iInter, Finset.mem_powerset, Finset.subset_iff, T, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hsum :
      ∑ s ∈ (Finset.univ : Finset ι).powersetCard r,
          (⋂ i ∈ s, A i).indicator (1 : Ω → ℝ) ω =
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard r,
          if s ∈ T.powerset then (1 : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Set.indicator_apply, Pi.one_apply]
    simp only [hmem s]
  rw [hsum, Finset.sum_boole, Finset.filter_mem_eq_inter]
  have hinter : (Finset.univ : Finset ι).powersetCard r ∩ T.powerset = T.powersetCard r := by
    ext s
    simp only [Finset.mem_inter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
      Finset.mem_powerset]
    tauto
  rw [hinter, Finset.card_powersetCard]

/-- Pointwise Bonferroni identity expressing the truncated inclusion-exclusion error in terms of
alternating binomial coefficients. -/
private theorem bonferroni_pointwise [Fintype ι] (A : ι → Set Ω) (k N : ℕ) (hN : 0 < N)
    (ω : Ω) :
    (∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) *
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard (r + k),
          (⋂ i ∈ s, A i).indicator (1 : Ω → ℝ) ω) -
      ({ω' : Ω | Nat.card {i : ι // ω' ∈ A i} = k} : Set Ω).indicator
        (1 : Ω → ℝ) ω =
      ((Nat.card {i : ι // ω ∈ A i}).choose k : ℝ) *
        if k < Nat.card {i : ι // ω ∈ A i} then
          ∑ r ∈ Finset.range N, (-1 : ℝ) ^ r *
            ((Nat.card {i : ι // ω ∈ A i} - k).choose r : ℝ)
        else 0 := by
  set t : ℕ := Nat.card {i : ι // ω ∈ A i}
  simp_rw [sum_powersetCard_indicator]
  have hmul : ∀ r : ℕ, ((r + k).choose k : ℝ) * (t.choose (r + k) : ℝ) =
      (t.choose k : ℝ) * ((t - k).choose r : ℝ) := fun r => by
    have h := congrArg (Nat.cast (R := ℝ)) (Nat.choose_mul (n := t) (k := r + k) (s := k)
      (Nat.le_add_left k r))
    rw [Nat.add_sub_cancel] at h
    push_cast at h
    rw [mul_comm ((r + k).choose k : ℝ) _, h]
  calc
    (∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) * (t.choose (r + k) : ℝ)) -
        ({ω' : Ω | Nat.card {i : ι // ω' ∈ A i} = k} : Set Ω).indicator (1 : Ω → ℝ) ω
      = (∑ r ∈ Finset.range N, (t.choose k : ℝ) * ((-1 : ℝ) ^ r * ((t - k).choose r : ℝ))) -
          (if t = k then (1 : ℝ) else 0) := by
          congr 1
          · refine Finset.sum_congr rfl fun r _ => ?_
            rw [mul_assoc, hmul r]
            ring
          · simp [Set.indicator_apply, t]
    _ = (t.choose k : ℝ) * (∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * ((t - k).choose r : ℝ)) -
          (if t = k then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
    _ = (t.choose k : ℝ) * if k < t then
          ∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * ((t - k).choose r : ℝ) else 0 := by
          rcases Nat.lt_trichotomy t k with hlt | rfl | hgt
          · have hch : t.choose k = 0 := Nat.choose_eq_zero_of_lt hlt
            simp [hch, hlt.ne, Nat.not_lt_of_gt hlt]
          · simp [sum_neg_one_pow_mul_choose_eq_zero N hN]
          · simp [hgt, hgt.ne']

private theorem setOf_natCard_eq_zero [Finite ι] (A : ι → Set Ω) :
    {ω : Ω | Nat.card {i : ι // ω ∈ A i} = 0} = {ω : Ω | ∀ i, ω ∉ A i} := by
  ext ω
  have hfin : Finite {i : ι // ω ∈ A i} := Subtype.finite
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Nat.card_eq_zero, or_iff_left hfin.not_infinite,
    isEmpty_subtype]

section Measure

variable [MeasurableSpace Ω]

/-- The set of points belonging to exactly `k` of finitely many measurable events is measurable. -/
theorem measurableSet_natCard_eq [Finite ι] {A : ι → Set Ω}
    (hA : ∀ i, MeasurableSet (A i)) (k : ℕ) :
    MeasurableSet {ω : Ω | Nat.card {i : ι // ω ∈ A i} = k} := by
  classical
  let _ := Fintype.ofFinite ι
  have heq :
      {ω : Ω | Nat.card {i : ι // ω ∈ A i} = k} =
        ⋃ t ∈ (Finset.univ : Finset ι).powersetCard k,
          (⋂ i ∈ t, A i) ∩ ⋂ i ∈ tᶜ, (A i)ᶜ := by
    ext ω
    rw [Set.mem_ofPred_eq, natCard_subtype_mem_eq_card]
    simp only [Set.mem_iUnion, Finset.mem_powersetCard, Finset.subset_univ,
      true_and, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_compl, Set.mem_compl_iff]
    constructor
    · intro hcard
      refine ⟨Finset.univ.filter fun i : ι => ω ∈ A i, hcard, ?_, ?_⟩
      · intro i hi
        exact (Finset.mem_filter.mp hi).2
      · intro i hi
        simpa [Finset.mem_filter] using hi
    · rintro ⟨t, rfl, hmem, hnmem⟩
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hω => by_contra fun hnt => hnmem i hnt hω, hmem i⟩
  rw [heq]
  refine MeasurableSet.biUnion (Finset.countable_toSet _) fun t _ => ?_
  exact (MeasurableSet.biInter (Finset.countable_toSet _) fun i _ => hA i).inter
    (MeasurableSet.biInter (Finset.countable_toSet _) fun i _ => (hA i).compl)

private theorem integrable_bonferroni_sum [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i)) (k N : ℕ) :
    Integrable (fun ω => ∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) *
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard (r + k),
          (⋂ i ∈ s, A i).indicator (1 : Ω → ℝ) ω) μ :=
  integrable_finsetSum _ fun _ _ =>
    (integrable_finsetSum _ fun _ _ => (integrable_const (1 : ℝ)).indicator
      (MeasurableSet.biInter (Finset.countable_toSet _) fun i _ => hA i)).const_mul _

/-- Integral representation of the `N`-term alternating Bonferroni sum. -/
private theorem integral_bonferroni_sum [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i)) (k N : ℕ) :
    ∫ ω, (∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) *
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard (r + k),
          (⋂ i ∈ s, A i).indicator (1 : Ω → ℝ) ω) ∂μ =
      ∑ r ∈ Finset.range N, (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) *
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard (r + k), μ.real (⋂ i ∈ s, A i) := by
  have hint_s : ∀ s : Finset ι,
      Integrable (fun ω => (⋂ i ∈ s, A i).indicator (1 : Ω → ℝ) ω) μ := fun s =>
    (integrable_const (1 : ℝ)).indicator
      (MeasurableSet.biInter (Finset.countable_toSet _) fun i _ => hA i)
  have hint_r : ∀ r : ℕ, Integrable (fun ω =>
      (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) *
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard (r + k),
          (⋂ i ∈ s, A i).indicator (1 : Ω → ℝ) ω) μ := fun r =>
    (integrable_finsetSum _ fun s _ => hint_s s).const_mul _
  rw [integral_finsetSum _ fun r _ => hint_r r]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun s _ => hint_s s]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  exact integral_indicator_one (MeasurableSet.biInter (Finset.countable_toSet _) fun i _ => hA i)

/-- **Bonferroni upper bound**: for any finite family `A : ι → Set Ω` of measurable events in a
finite measure space and any `k, m : ℕ`, truncating the inclusion-exclusion sum for
`Nat.card {i | ω ∈ A i} = k` at odd length `2 * m + 1` gives an upper bound on
`μ.real {ω | Nat.card {i | ω ∈ A i} = k}`. -/
theorem measureReal_natCard_eq_le_bonferroni [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i)) (k m : ℕ) :
    μ.real {ω : Ω | Nat.card {i : ι // ω ∈ A i} = k} ≤
      ∑ r ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) *
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard (r + k), μ.real (⋂ i ∈ s, A i) := by
  have hle : ∀ ω : Ω,
      ({ω' : Ω | Nat.card {i : ι // ω' ∈ A i} = k} : Set Ω).indicator 1 ω ≤
        ∑ r ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) *
          ∑ s ∈ (Finset.univ : Finset ι).powersetCard (r + k),
            (⋂ i ∈ s, A i).indicator (1 : Ω → ℝ) ω := fun ω => by
    have hpt := bonferroni_pointwise A k (2 * m + 1) (Nat.succ_pos _) ω
    have hrhs : 0 ≤ (∑ r ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) *
          ∑ s ∈ (Finset.univ : Finset ι).powersetCard (r + k),
            (⋂ i ∈ s, A i).indicator (1 : Ω → ℝ) ω) -
        ({ω' : Ω | Nat.card {i : ι // ω' ∈ A i} = k} : Set Ω).indicator 1 ω := by
      rw [hpt]
      refine mul_nonneg (Nat.cast_nonneg _) ?_
      split_ifs with hkt
      · exact sum_neg_one_pow_mul_choose_odd_nonneg _ m (Nat.sub_pos_of_lt hkt)
      · exact le_rfl
    linarith
  have hmono := integral_mono ((integrable_const (1 : ℝ)).indicator (measurableSet_natCard_eq hA k))
    (integrable_bonferroni_sum μ hA k (2 * m + 1)) hle
  change ∫ ω, ({ω' : Ω | Nat.card {i : ι // ω' ∈ A i} = k} : Set Ω).indicator 1 ω ∂μ ≤ _ at hmono
  rwa [integral_indicator_one (measurableSet_natCard_eq hA k),
    integral_bonferroni_sum μ hA k (2 * m + 1)] at hmono

/-- **Bonferroni lower bound**: truncating the inclusion-exclusion sum for
`Nat.card {i | ω ∈ A i} = k` at even length `2 * m` gives a lower bound on
`μ.real {ω | Nat.card {i | ω ∈ A i} = k}`. -/
theorem bonferroni_le_measureReal_natCard_eq [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i)) (k m : ℕ) :
    ∑ r ∈ Finset.range (2 * m), (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) *
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard (r + k), μ.real (⋂ i ∈ s, A i) ≤
      μ.real {ω : Ω | Nat.card {i : ι // ω ∈ A i} = k} := by
  rcases m with _ | m
  · simp [measureReal_nonneg]
  have hle : ∀ ω : Ω,
      (∑ r ∈ Finset.range (2 * (m + 1)), (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) *
          ∑ s ∈ (Finset.univ : Finset ι).powersetCard (r + k),
            (⋂ i ∈ s, A i).indicator (1 : Ω → ℝ) ω) ≤
        ({ω' : Ω | Nat.card {i : ι // ω' ∈ A i} = k} : Set Ω).indicator 1 ω := fun ω => by
    have hpt := bonferroni_pointwise A k (2 * (m + 1)) (by omega) ω
    have hrhs : (∑ r ∈ Finset.range (2 * (m + 1)), (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) *
          ∑ s ∈ (Finset.univ : Finset ι).powersetCard (r + k),
            (⋂ i ∈ s, A i).indicator (1 : Ω → ℝ) ω) -
        ({ω' : Ω | Nat.card {i : ι // ω' ∈ A i} = k} : Set Ω).indicator 1 ω ≤ 0 := by
      rw [hpt]
      refine mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) ?_
      split_ifs with hkt
      · exact sum_neg_one_pow_mul_choose_even_nonpos _ (m + 1) (Nat.sub_pos_of_lt hkt)
      · exact le_rfl
    linarith
  have hmono := integral_mono (integrable_bonferroni_sum μ hA k (2 * (m + 1)))
    ((integrable_const (1 : ℝ)).indicator (measurableSet_natCard_eq hA k)) hle
  change _ ≤ ∫ ω, ({ω' : Ω | Nat.card {i : ι // ω' ∈ A i} = k} : Set Ω).indicator 1 ω ∂μ at hmono
  rwa [integral_indicator_one (measurableSet_natCard_eq hA k),
    integral_bonferroni_sum μ hA k (2 * (m + 1))] at hmono

/-- Specialization of `measureReal_natCard_eq_le_bonferroni` to `k = 0`: the event that none
of `A i` holds has probability at most the odd-length alternating sum of intersection
probabilities. -/
theorem measureReal_forall_notMem_le_bonferroni [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i)) (m : ℕ) :
    μ.real {ω : Ω | ∀ i, ω ∉ A i} ≤
      ∑ r ∈ Finset.range (2 * m + 1), (-1 : ℝ) ^ r *
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard r, μ.real (⋂ i ∈ s, A i) := by
  have h := measureReal_natCard_eq_le_bonferroni μ hA 0 m
  rw [setOf_natCard_eq_zero] at h
  simpa only [add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] using h

/-- Specialization of `bonferroni_le_measureReal_natCard_eq` to `k = 0`: the even-length
alternating sum of intersection probabilities bounds `μ.real {ω | ∀ i, ω ∉ A i}` from below. -/
theorem bonferroni_le_measureReal_forall_notMem [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i)) (m : ℕ) :
    ∑ r ∈ Finset.range (2 * m), (-1 : ℝ) ^ r *
        ∑ s ∈ (Finset.univ : Finset ι).powersetCard r, μ.real (⋂ i ∈ s, A i) ≤
      μ.real {ω : Ω | ∀ i, ω ∉ A i} := by
  have h := bonferroni_le_measureReal_natCard_eq μ hA 0 m
  rw [setOf_natCard_eq_zero] at h
  simpa only [add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] using h

end Measure

end Bonferroni

section PoissonLimit

/-- **Brun's sieve (Poisson limit from factorial moments)**: given finite measure spaces
`(Ω n, μ n)` and finite families of measurable events `A n : ι n → Set (Ω n)` whose `r`-th
binomial moments converge to `lam ^ r / r!` for every fixed `r : ℕ`, the count
`Nat.card {i // ω ∈ A n i}` converges in distribution to `Poisson(lam)`:
`(μ n).real {ω | Nat.card {i // ω ∈ A n i} = k} → exp (-lam) * (lam ^ k / k!)` for every
`k : ℕ`. -/
theorem tendsto_measureReal_natCard_eq_poisson_of_factorialMoments
    {Ω : ℕ → Type*} {ι : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, Fintype (ι n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsFiniteMeasure (μ n)]
    (A : ∀ n, ι n → Set (Ω n)) (hA : ∀ n i, MeasurableSet (A n i))
    {lam : ℝ}
    (hmom : ∀ r : ℕ, Tendsto (fun n => ∑ s ∈ (Finset.univ : Finset (ι n)).powersetCard r,
        (μ n).real (⋂ i ∈ s, A n i)) atTop (𝓝 (lam ^ r / r.factorial)))
    (k : ℕ) :
    Tendsto (fun n => (μ n).real {ω : Ω n | Nat.card {i : ι n // ω ∈ A n i} = k})
      atTop (𝓝 (Real.exp (-lam) * (lam ^ k / k.factorial))) := by
  have hexp : Tendsto (fun M : ℕ =>
      (∑ r ∈ Finset.range M, (-1 : ℝ) ^ r * (lam ^ r / r.factorial)) *
        (lam ^ k / k.factorial)) atTop (𝓝 (Real.exp (-lam) * (lam ^ k / k.factorial))) := by
    have hseries : HasSum (fun r : ℕ => (-lam) ^ r / r.factorial) (Real.exp (-lam)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (-lam)
    have hpow : Tendsto (fun M : ℕ => ∑ r ∈ Finset.range M, (-1 : ℝ) ^ r * (lam ^ r / r.factorial))
        atTop (𝓝 (Real.exp (-lam))) := by
      refine hseries.tendsto_sum_nat.congr fun M => Finset.sum_congr rfl fun r _ => ?_
      rw [neg_eq_neg_one_mul, mul_pow, mul_div_assoc]
    exact hpow.mul_const _
  have hterm : ∀ r : ℕ,
      ((r + k).choose k : ℝ) * (lam ^ (r + k) / (r + k).factorial) =
        (lam ^ r / r.factorial) * (lam ^ k / k.factorial) := by
    intro r
    have hnat : (r + k).choose k * (r.factorial * k.factorial) = (r + k).factorial := by
      have h0 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left k r)
      rw [Nat.add_sub_cancel] at h0
      linarith [h0]
    have hchoose :
        ((r + k).choose k : ℝ) * (r.factorial * k.factorial : ℝ) = (r + k).factorial := by
      exact_mod_cast hnat
    have hfac_ne : ((r + k).factorial : ℝ) ≠ 0 := by positivity
    have hpow : lam ^ (r + k) = lam ^ r * lam ^ k := pow_add lam r k
    calc ((r + k).choose k : ℝ) * (lam ^ (r + k) / (r + k).factorial)
        = (((r + k).choose k : ℝ) * (r.factorial * k.factorial : ℝ) / (r + k).factorial) *
            (lam ^ r / r.factorial) * (lam ^ k / k.factorial) := by
            rw [hpow]
            field_simp
      _ = (lam ^ r / r.factorial) * (lam ^ k / k.factorial) := by
            rw [hchoose, div_self hfac_ne, one_mul]
  have hsum_lim : ∀ M : ℕ,
      Tendsto (fun n => ∑ r ∈ Finset.range M, (-1 : ℝ) ^ r * ((r + k).choose k : ℝ) *
          ∑ s ∈ (Finset.univ : Finset (ι n)).powersetCard (r + k),
            (μ n).real (⋂ i ∈ s, A n i))
        atTop
        (𝓝 ((∑ r ∈ Finset.range M, (-1 : ℝ) ^ r * (lam ^ r / r.factorial)) *
          (lam ^ k / k.factorial))) := by
    intro M
    have hfin := tendsto_finsetSum (Finset.range M) fun r _ =>
      ((hmom (r + k)).const_mul (((r + k).choose k : ℝ))).const_mul ((-1 : ℝ) ^ r)
    have hsum_eq :
        ∑ r ∈ Finset.range M, (-1 : ℝ) ^ r * (((r + k).choose k : ℝ) *
            (lam ^ (r + k) / (r + k).factorial)) =
          (∑ r ∈ Finset.range M, (-1 : ℝ) ^ r * (lam ^ r / r.factorial)) *
            (lam ^ k / k.factorial) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hterm r]
      ring
    rw [← hsum_eq]
    exact hfin.congr fun n => Finset.sum_congr rfl fun r _ => by ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M₀, hM₀⟩ := (Metric.tendsto_atTop.mp hexp) (ε / 2) (by positivity)
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp (hsum_lim (2 * M₀))) (ε / 2) hε2
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp (hsum_lim (2 * M₀ + 1))) (ε / 2) hε2
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h1 := hN₁ n (le_of_max_le_left hn)
  have h2 := hN₂ n (le_of_max_le_right hn)
  have hlim_lo := hM₀ (2 * M₀) (by omega)
  have hlim_hi := hM₀ (2 * M₀ + 1) (by omega)
  rw [Real.dist_eq, abs_lt] at h1 h2 hlim_lo hlim_hi ⊢
  have hlo := bonferroni_le_measureReal_natCard_eq (μ n) (hA n) k M₀
  have hhi := measureReal_natCard_eq_le_bonferroni (μ n) (hA n) k M₀
  constructor <;> linarith

end PoissonLimit

end ProbabilityTheory
