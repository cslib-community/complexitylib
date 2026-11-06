/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Rewinding
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Event

/-!
# Rewinding against a committed table

A two-stage experiment draws a first-stage outcome `s`, then runs a second stage with outcome `r`,
and accepts when `acc s r` holds. Each run also *opens* positions `j` to bits `b`
(`opens s r j b`), as a prover opens positions of a committed table. If, at every possible saved
state, runs that accept while agreeing with a fixed table `π : ℕ → Bool` are rare (probability at
most `ε`, for every `π`), then an accepting prover must answer inconsistently across runs: rewinding
the second stage, two runs that both accept and open some position to different bits occur with
probability `δ` satisfying

`ε₁ ≤ ε + M * √δ` (`le_add_mul_sqrt_disagreement`),

where `ε₁` is the one-run acceptance probability and every accepting run opens only positions below
`M`.

The proof fixes the saved state `s` and chooses, at each position, the bit that accepting runs
open more often. A run that accepts but disagrees with that table opens some position to its less
likely bit `b`, an event of probability `p_j(b) = min (p_j(false), p_j(true))`, whose square is at
most the probability `p_j(false) * p_j(true)` that two independent runs open `j` to both bits.
Jensen's inequality (`Cslib.Probability.PMF.sq_tsum_le_tsum_sq`) averages over `s`.

This is the probabilistic core of the soundness of Kilian's protocol
([BarakGoldreich2001], Construction 3.4 and Lemma 3.5): positions are the leaves of a hash tree,
and two accepted openings of one leaf to different bits are a binding break. The statement and the
constants are our own packaging; Barak and Goldreich bound the extraction of an oracle for
superpolynomially long proofs, while here the table is indexed below `M`.

These are exact statements about experiment laws, with no efficiency claim.

## Main definitions

* `Cslib.Probability.Rewinding.acceptance`: one run of the two-stage experiment.
* `Cslib.Probability.Rewinding.disagreement`: two runs sharing the first stage that both accept and
  open a common position to different bits.

## Main results

* `Cslib.Probability.Rewinding.le_add_mul_sqrt_disagreement`: `ε₁ ≤ ε + M * √δ`.

## References

* [B. Barak, O. Goldreich, *Universal Arguments and their Applications*][BarakGoldreich2001],
  Construction 3.4 and Lemma 3.5.
-/

@[expose] public section

namespace Cslib.Probability.Rewinding

open scoped ENNReal

variable {S R : Type} (first : PMF S) (run : S → PMF R) (acc : S → R → Bool)
  (opens : S → R → ℕ → Bool → Bool) (M : ℕ)

/-- The law of one run of a two-stage experiment: a first-stage outcome, a second-stage run from
it, and the acceptance test. -/
noncomputable def acceptance : PMF Bool := do
  let s ← first
  let r ← run s
  return acc s r

/-- The law of rewinding the second stage: one first-stage outcome and two independent runs from
it. It succeeds when both runs accept and some position below `M` is opened to `false` by the
first run and to `true` by the second. -/
noncomputable def disagreement : PMF Bool := do
  let s ← first
  let r ← run s
  let r' ← run s
  return acc s r && acc s r' && (List.range M).any fun j => opens s r j false && opens s r' j true

/-! ### At one saved state -/

/-- A run that accepts either agrees with the table `π`, or opens some position below `M` to the
other bit. -/
private theorem toOuterMeasure_accept_le (μ : PMF R) (acc : R → Bool)
    (opens : R → ℕ → Bool → Bool) (M : ℕ)
    (hpos : ∀ r ∈ μ.support, ∀ j b, acc r = true → opens r j b = true → j < M) (π : ℕ → Bool) :
    μ.toOuterMeasure {r | acc r = true} ≤
      μ.toOuterMeasure {r | acc r = true ∧ ∀ j b, opens r j b = true → b = π j} +
        ∑ j ∈ Finset.range M, μ.toOuterMeasure {r | acc r = true ∧ opens r j (!π j) = true} := by
  rw [← PMF.toOuterMeasure_apply_inter_support]
  calc μ.toOuterMeasure ({r | acc r = true} ∩ μ.support)
      ≤ μ.toOuterMeasure ({r | acc r = true ∧ ∀ j b, opens r j b = true → b = π j} ∪
          ⋃ j ∈ Finset.range M, {r | acc r = true ∧ opens r j (!π j) = true}) := by
        refine MeasureTheory.measure_mono fun r ⟨hacc, hr⟩ => ?_
        by_cases hc : ∀ j b, opens r j b = true → b = π j
        · exact Or.inl ⟨hacc, hc⟩
        · simp only [not_forall, exists_prop] at hc
          obtain ⟨j, b, hj, hb⟩ := hc
          have hb' : b = !π j := by cases b <;> cases h : π j <;> simp_all
          refine Or.inr (Set.mem_biUnion (Finset.mem_range.mpr (hpos r hr j b hacc hj)) ?_)
          exact ⟨hacc, hb' ▸ hj⟩
    _ ≤ _ := (MeasureTheory.measure_union_le _ _).trans
        (add_le_add le_rfl (MeasureTheory.measure_biUnion_finset_le _ _))

/-- Two independent runs land in `A` and `B` with the product probability, which is at most the
probability of any event `E` containing all such pairs. -/
private theorem mul_le_bind_bind (μ : PMF R) (A B : Set R) (E : R → R → Bool)
    (h : ∀ r r', r ∈ A → r' ∈ B → E r r' = true) :
    μ.toOuterMeasure A * μ.toOuterMeasure B ≤
      (μ.bind fun r => μ.bind fun r' => PMF.pure (E r r')) true := by
  simp only [PMF.toOuterMeasure_apply, PMF.bind_apply, PMF.pure_apply]
  rw [← ENNReal.tsum_mul_right]
  refine tsum_le_tsum fun r => ?_
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun r' => ?_
  by_cases hr : r ∈ A
  · by_cases hr' : r' ∈ B
    · simp [Set.indicator_of_mem hr, Set.indicator_of_mem hr', h r r' hr hr']
    · simp [Set.indicator_of_notMem hr']
  · simp [Set.indicator_of_notMem hr]

/-- The square of the smaller of two numbers is at most their product. -/
private theorem sq_le_mul_of_choose (a : Bool → ℝ≥0∞) :
    a (!decide (a false ≤ a true)) ^ 2 ≤ a false * a true := by
  by_cases h : a false ≤ a true
  · rw [decide_eq_true h, Bool.not_true, sq]
    gcongr
  · rw [decide_eq_false h, Bool.not_false, sq, mul_comm (a false)]
    gcongr
    exact (not_le.mp h).le

/-! ### The bound -/

/-- One-run acceptance averages the conditional acceptance probabilities. -/
private theorem toReal_acceptance :
    (acceptance first run acc true).toReal =
      ∑' s, (first s).toReal * ((run s).toOuterMeasure {r | acc s r = true}).toReal := by
  simp only [acceptance, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
  rw [Probability.PMF.bind_apply_toReal_tsum]
  refine tsum_congr fun s => congrArg _ (congrArg _ ?_)
  simp only [PMF.bind_apply, PMF.pure_apply, PMF.toOuterMeasure_apply, Set.indicator_apply,
    Set.mem_ofPred_eq, mul_ite, mul_one, mul_zero, eq_comm]

/-- Two-run disagreement averages the conditional two-run probabilities. -/
private theorem toReal_disagreement :
    (disagreement first run acc opens M true).toReal =
      ∑' s, (first s).toReal * (((run s).bind fun r => (run s).bind fun r' =>
        PMF.pure (acc s r && acc s r' &&
          (List.range M).any fun j => opens s r j false && opens s r' j true)) true).toReal := by
  simp only [disagreement, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure]
  rw [Probability.PMF.bind_apply_toReal_tsum]

/-- **Rewinding against a committed table.** Suppose that at every possible saved state `s`,
every accepting run opens only positions below `M`, and runs that accept while agreeing with any
fixed table `π` have probability at most `ε`. Then the one-run acceptance probability `ε₁` and the
probability `δ` that two runs from one saved state both accept and open a position to different
bits satisfy `ε₁ ≤ ε + M * √δ`.

This is an original packaging of the extraction step in the soundness of Kilian's protocol
([BarakGoldreich2001], Lemma 3.5). It concerns experiment laws, with no efficiency claim. -/
theorem le_add_mul_sqrt_disagreement {ε : ℝ}
    (hpos : ∀ s ∈ first.support, ∀ r ∈ (run s).support, ∀ j b,
      acc s r = true → opens s r j b = true → j < M)
    (hcons : ∀ s ∈ first.support, ∀ π : ℕ → Bool,
      ((run s).toOuterMeasure
        {r | acc s r = true ∧ ∀ j b, opens s r j b = true → b = π j}).toReal ≤ ε) :
    (acceptance first run acc true).toReal ≤
      ε + M * √(disagreement first run acc opens M true).toReal := by
  set E : S → R → R → Bool := fun s r r' => acc s r && acc s r' &&
    (List.range M).any fun j => opens s r j false && opens s r' j true
  set p : S → ℝ := fun s => ((run s).toOuterMeasure {r | acc s r = true}).toReal
  set d : S → ℝ := fun s =>
    (((run s).bind fun r => (run s).bind fun r' => PMF.pure (E s r r')) true).toReal
  have hp (s : S) : 0 ≤ p s ∧ p s ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact Probability.PMF.toOuterMeasure_le_one _ _)⟩
  have hd (s : S) : 0 ≤ d s ∧ d s ≤ 1 :=
    ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact PMF.coe_le_one _ _)⟩
  obtain ⟨s₀, hs₀⟩ := first.support_nonempty
  have hε : 0 ≤ ε := ENNReal.toReal_nonneg.trans (hcons s₀ hs₀ fun _ => false)
  have hpoint (s : S) (hs : s ∈ first.support) : p s ≤ ε + M * √(d s) := by
    set μ := run s
    set a : ℕ → Bool → ℝ≥0∞ := fun j b =>
      μ.toOuterMeasure {r | acc s r = true ∧ opens s r j b = true}
    set π : ℕ → Bool := fun j => decide (a j false ≤ a j true)
    have hsplit := toOuterMeasure_accept_le μ (acc s) (opens s) M (hpos s hs) π
    have hmin (j : ℕ) (hj : j ∈ Finset.range M) : (a j (!π j)).toReal ≤ √(d s) := by
      refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
      rw [← ENNReal.toReal_pow]
      refine ENNReal.toReal_mono (PMF.apply_ne_top _ _) ?_
      refine (sq_le_mul_of_choose (a j)).trans (mul_le_bind_bind μ _ _ (E s) ?_)
      rintro r r' ⟨hr, hrj⟩ ⟨hr', hrj'⟩
      simp only [E, hr, hr', Bool.true_and, List.any_eq_true, List.mem_range, Bool.and_eq_true]
      exact ⟨j, Finset.mem_range.mp hj, hrj, hrj'⟩
    have hfin (t : Set R) : μ.toOuterMeasure t ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (Probability.PMF.toOuterMeasure_le_one _ _)
    calc p s ≤ (μ.toOuterMeasure
          {r | acc s r = true ∧ ∀ j b, opens s r j b = true → b = π j}).toReal +
          ∑ j ∈ Finset.range M, (a j (!π j)).toReal := by
          rw [← ENNReal.toReal_sum fun j _ => hfin _, ← ENNReal.toReal_add (hfin _)
            (ENNReal.sum_ne_top.mpr fun j _ => hfin _)]
          exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin _,
            ENNReal.sum_ne_top.mpr fun j _ => hfin _⟩) hsplit
      _ ≤ ε + ∑ _j ∈ Finset.range M, √(d s) :=
          add_le_add (hcons s hs π) (Finset.sum_le_sum hmin)
      _ = ε + M * √(d s) := by simp
  have hm := Probability.PMF.summable_toReal first
  have hsum {f : S → ℝ} (f0 : ∀ s, 0 ≤ f s) (f1 : ∀ s, f s ≤ 1) :
      Summable fun s => (first s).toReal * f s :=
    hm.of_nonneg_of_le (fun s => mul_nonneg ENNReal.toReal_nonneg (f0 s))
      fun s => mul_le_of_le_one_right ENNReal.toReal_nonneg (f1 s)
  have hsqrt := hsum (f := fun s => √(d s)) (fun s => Real.sqrt_nonneg _)
    fun s => Real.sqrt_le_one.mpr (hd s).2
  have hjensen : ∑' s, (first s).toReal * √(d s) ≤ √(∑' s, (first s).toReal * d s) := by
    have h := Probability.PMF.sq_tsum_le_tsum_sq first (g := fun s => √(d s))
      (fun s => Real.sqrt_nonneg _)
      fun s => Real.sqrt_le_one.mpr (hd s).2
    simp only [Real.sq_sqrt (hd _).1] at h
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h)
  rw [toReal_acceptance, toReal_disagreement]
  change ∑' s, (first s).toReal * p s ≤ ε + M * √(∑' s, (first s).toReal * d s)
  calc ∑' s, (first s).toReal * p s
      ≤ ∑' s, ((first s).toReal * ε + M * ((first s).toReal * √(d s))) := by
        refine (hsum (fun s => (hp s).1) fun s => (hp s).2).tsum_le_tsum (fun s => ?_)
          ((hm.mul_right ε).add (hsqrt.mul_left (M : ℝ)))
        by_cases hs : s ∈ first.support
        · nlinarith [hpoint s hs, (ENNReal.toReal_nonneg : 0 ≤ (first s).toReal)]
        · simp [(PMF.apply_eq_zero_iff first s).mpr hs]
    _ = ε + M * ∑' s, (first s).toReal * √(d s) := by
        rw [(hm.mul_right ε).tsum_add (hsqrt.mul_left (M : ℝ)), tsum_mul_right, tsum_mul_left,
          Probability.PMF.tsum_toReal, one_mul]
    _ ≤ ε + M * √(∑' s, (first s).toReal * d s) := by gcongr

end Cslib.Probability.Rewinding
