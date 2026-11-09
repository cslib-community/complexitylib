/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.AdaptiveBinomial
public import CslibFrontier.Probability.StochasticOracle.PartialCover
import Mathlib.Tactic

/-!
# Actual retained-set progress

For [Wang2027], Theorem 5(1), PDF p. 12 and Appendix A.5, PDF p. 16,
responses are finite lists of proposed subfamilies. `selected` executes the existing
local dual test on every proposal, in chronological order. `productive` is computed
from the actual residual cardinalities, with success extended by ones after completion.
`residual_le` derives the productive-count bridge; no terminal cover implication is
assumed. This is a finite semantic execution, without machine resource certificates.

## Main results

* `count_completes`: sufficiently many productive turns force actual coverage.
* `reach_le_binomial_complement`: retained-completion stopping bounds reached turns.
* `historyExpectation_accruedBill`: finite tower identity for response-dependent bills.
* `accruedBill_le_binomial_sum`: the finite stopped expected token-cost sum.
* `accruedBill_le_mean`: its horizon-uniform `c * r / p` bound for positive `p`.
* `expectedBills_summable_le`: derived finiteness of the marginal expected-bill series.

The cost and reach results formalize the finite-sum step of Appendix A.5.
The binomial tail-series mean is proved in `AdaptiveBinomial`; these results do not
establish an infinite-execution stopping-time bridge or an infinite-horizon limit.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.AdaptiveSelection
open Finset PartialCover MeasureTheory
variable {E J Ω : Type*} [DecidableEq E] [DecidableEq J]

/-- History-dependent proposal decoder; responses may also contain auxiliary data. -/
@[expose] def selected (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) : List Ω → Finset J
  | [] => ∅
  | x :: h => I.retain ρ (selected I ρ proposal h) (proposal h x)

/-- The actual retained family carries the dual certificate throughout execution. -/
theorem selected_bound (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (h : List Ω) :
    I.cost (selected I ρ proposal h) ≤
      ρ * ∑ e ∈ I.covered (selected I ρ proposal h), I.dual e := by
  induction h with
  | nil => simp [selected, Instance.cost, Instance.covered]
  | cons x h ih => exact I.retain_bound (proposal h x) _ ih

/-- The number of elements actually left uncovered by the retained family. -/
@[expose] def residual (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (h : List Ω) : ℕ :=
  (I.ground \ I.covered (selected I ρ proposal h)).card

/-- Count productive indicators along a newest-first transcript. -/
@[expose] def count (b : List Ω → Ω → Bool) : List Ω → ℕ
  | [] => 0
  | x :: h => count b h + if b h x then 1 else 0

open scoped Classical in
/-- A productive turn removes at least `a` residual elements, truncated at zero.
After completion every turn is declared productive, as in Appendix A.5. -/
@[expose] def productive (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (a : ℕ) (h : List Ω) (x : Ω) : Bool :=
  decide (residual I ρ proposal (x :: h) ≤ residual I ρ proposal h - a)

private theorem retain_mono (I : Instance E J) (ρ : ℝ)
    (C : Finset J) (ps : List (Finset J)) : C ⊆ I.retain ρ C ps := by
  classical
  induction ps generalizing C with
  | nil => exact Subset.rfl
  | cons P ps ih =>
    simp only [Instance.retain]
    split_ifs
    · exact subset_trans subset_union_left (ih _)
    · exact ih _

/-- Retention never increases the actual residual. -/
theorem residual_mono (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (h : List Ω) (x : Ω) :
    residual I ρ proposal (x :: h) ≤ residual I ρ proposal h := by
  apply card_le_card
  apply sdiff_subset_sdiff_right
  intro e he
  obtain ⟨j, hj, he⟩ := mem_biUnion.mp he
  exact mem_biUnion.mpr ⟨j, retain_mono I ρ _ _ hj, he⟩

/-- Each productive turn subtracts `a`, with natural subtraction handling the final
short turn and the artificial successes after completion. -/
theorem residual_le (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (a : ℕ) (h : List Ω) :
    residual I ρ proposal h ≤
      I.ground.card - a * count (productive I ρ proposal a) h := by
  classical
  induction h with
  | nil => simp [residual, selected, Instance.covered, count]
  | cons x h ih =>
    by_cases hb : productive I ρ proposal a h x = true
    · have hd : residual I ρ proposal (x :: h) ≤ residual I ρ proposal h - a := by
        simpa only [productive, decide_eq_true_eq] using hb
      calc
        _ ≤ (I.ground.card - a * count (productive I ρ proposal a) h) - a :=
          hd.trans (Nat.sub_le_sub_right ih a)
        _ = _ := by simp [count, hb, Nat.mul_add, Nat.sub_sub]
    · simpa only [count, hb, Bool.false_eq_true, ite_false, Nat.add_zero]
        using (residual_mono I ρ proposal h x).trans ih

/-- Actual retained coverage follows from the count threshold, rather than being
an operational-bridge premise. For `a > 0`, choose the ceiling of `n/a`. -/
theorem count_completes (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J)) (a : ℕ) (h : List Ω)
    (hc : I.ground.card ≤ a * count (productive I ρ proposal a) h) :
    I.covered (selected I ρ proposal h) = I.ground := by
  have hz := residual_le I ρ proposal a h
  have hr : residual I ρ proposal h = 0 := by omega
  apply Subset.antisymm (I.covered_subset _)
  exact sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp hr)

/-- Actual finite execution probability/expectation of an observable of the transcript. -/
@[expose] def historyExpectation [Fintype Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (f : List Ω → ℝ) : ℕ → List Ω → ℝ
  | 0, h => f h
  | n + 1, h => (law h).mean fun x => historyExpectation law f n (x :: h)

/-- Computing the count in the actual transcript agrees with the comparison API. -/
theorem historyExpectation_count {Ω : Type} [Fintype Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (b : List Ω → Ω → Bool) (f : ℕ → ℝ) (n : ℕ) (h : List Ω) :
    historyExpectation law (fun h => f (count b h)) n h =
      progressExpectation law b f n h (count b h) := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [historyExpectation, progressExpectation]
    apply sum_congr rfl
    intro x _
    dsimp only
    rw [ih]
    rfl

/-- Expectations preserve pointwise bounds on transcript observables. -/
theorem historyExpectation_mono [Fintype Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (f g : List Ω → ℝ) (hfg : ∀ h, f h ≤ g h) (n : ℕ) (h : List Ω) :
    historyExpectation law f n h ≤ historyExpectation law g n h := by
  induction n generalizing h with
  | zero => exact hfg h
  | succ n ih =>
    exact sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (ih _) ((law h).nonneg x)

open scoped Classical in
/-- Theorem 5(1)'s finite coverage probability, for actual locally tested proposals
and a full-history conditional productivity envelope. Stopped costs and resources
are separate obligations. Neither a terminal coverage bound nor a count bridge is
an input. `r` may be the source ceiling `ceil(n/a)`. -/
theorem binomial_le_completion {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r n : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0)) :
    (∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial n p) ≤
      historyExpectation law
        (fun h => if I.covered (selected I ρ proposal h) = I.ground then 1 else 0) n [] := by
  have hc : ∀ h, (if r ≤ count (productive I ρ proposal a) h then (1 : ℝ) else 0) ≤
      (if I.covered (selected I ρ proposal h) = I.ground then 1 else 0) := by
    intro h
    by_cases hh : r ≤ count (productive I ρ proposal a) h
    · have hd := count_completes I ρ proposal a h (hr.trans (Nat.mul_le_mul_left a hh))
      simp [hh, hd]
    · simp only [hh, ite_false]
      split_ifs <;> norm_num
  have ht := le_progress_tail law (productive I ρ proposal a) p hp n r
  have hm := historyExpectation_mono law _ _ hc n []
  rw [historyExpectation_count law (productive I ρ proposal a)
    (fun k => if r ≤ k then 1 else 0) n []] at hm
  exact ht.trans hm

/-- All elements revealed by actual proposals, whether or not the local test accepts
those proposals. This is the information available to a selection-only policy. -/
@[expose] def revealed (I : Instance E J)
    (proposal : List Ω → Ω → List (Finset J)) : List Ω → Finset E
  | [] => ∅
  | x :: h => I.covered ((proposal h x).foldr (· ∪ ·) ∅) ∪ revealed I proposal h

open scoped Classical in
/-- A turn makes revealed progress exactly when its proposals reveal a new element. -/
@[expose] def reveals (I : Instance E J)
    (proposal : List Ω → Ω → List (Finset J)) (h : List Ω) (x : Ω) : Bool :=
  decide ((revealed I proposal (x :: h) \ revealed I proposal h).Nonempty)

/-- Local cardinality caps on newly proposed elements imply a pathwise productive
count requirement for every transcript. No desired aggregate progress bound is assumed. -/
theorem revealed_card_le (I : Instance E J)
    (proposal : List Ω → Ω → List (Finset J)) (b : ℕ)
    (hb : ∀ h x, (revealed I proposal (x :: h) \ revealed I proposal h).card ≤ b)
    (h : List Ω) :
    (revealed I proposal h).card ≤ b * count (reveals I proposal) h := by
  classical
  induction h with
  | nil => simp [revealed, count]
  | cons x h ih =>
    have hm : revealed I proposal h ⊆ revealed I proposal (x :: h) := subset_union_right
    have he := card_sdiff_add_card_eq_card hm
    by_cases hx : reveals I proposal h x = true
    · simp only [count, hx, ite_true, Nat.mul_add, Nat.mul_one]
      have := hb h x
      omega
    · have hz : (revealed I proposal (x :: h) \ revealed I proposal h).card = 0 := by
        simpa only [reveals, decide_eq_true_eq, not_nonempty_iff_eq_empty, card_eq_zero]
          using hx
      simpa only [count, hx, Bool.false_eq_true, ite_false, Nat.add_zero] using
        (show (revealed I proposal (x :: h)).card ≤
          b * count (reveals I proposal) h by omega)

open scoped Classical in
/-- The universal finite revealed-cover probability bound, under the local cap
`n > b*(r-1)` and a full-history upper progress envelope. The observable is coverage
by all actual proposals, so any selection-only returned cover must satisfy it.
This theorem does not assert a universal machine model or a latency bound. -/
theorem revealed_completion_le_binomial {Ω : Type} [Fintype Ω]
    (I : Instance E J) (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (b r n : ℕ) (hr : ∀ k < r, b * k < I.ground.card)
    (hb : ∀ h x, (revealed I proposal (x :: h) \ revealed I proposal h).card ≤ b)
    (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, (law h).mean (fun x => if reveals I proposal h x then 1 else 0) ≤ p) :
    historyExpectation law
      (fun h => if I.ground ⊆ revealed I proposal h then 1 else 0) n [] ≤
      ∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial n p := by
  have hc : ∀ h, (if I.ground ⊆ revealed I proposal h then (1 : ℝ) else 0) ≤
      (if r ≤ count (reveals I proposal) h then 1 else 0) := by
    intro h
    by_cases hh : I.ground ⊆ revealed I proposal h
    · have hn := (card_le_card hh).trans (revealed_card_le I proposal b hb h)
      have ht : r ≤ count (reveals I proposal) h := by
        by_contra ht
        have := hr _ (Nat.lt_of_not_ge ht)
        omega
      simp [hh, ht]
    · simp only [hh, ite_false]
      split_ifs <;> norm_num
  have hm := historyExpectation_mono law _ _ hc n []
  rw [historyExpectation_count law (reveals I proposal)
    (fun k => if r ≤ k then 1 else 0) n []] at hm
  exact hm.trans (progress_tail_le law (reveals I proposal) p hp n r)

/-- Constant transcript observables retain their value. -/
theorem historyExpectation_const {Ω : Type} [Fintype Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (c : ℝ) (n : ℕ) (h : List Ω) :
    historyExpectation law (fun _ => c) n h = c := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => simp only [historyExpectation, ih,
      Cslib.Optimization.OneConstraint.Distribution.mean_const]

/-- Transcript expectation is additive, including history-dependent observables. -/
theorem historyExpectation_add {Ω : Type} [Fintype Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (f g : List Ω → ℝ) (n : ℕ) (h : List Ω) :
    historyExpectation law (fun h => f h + g h) n h =
      historyExpectation law f n h + historyExpectation law g n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => simp only [historyExpectation, ih,
      Cslib.Optimization.OneConstraint.Distribution.mean_add]

/-- Constant factors can be taken outside transcript expectation. -/
theorem historyExpectation_mul {Ω : Type} [Fintype Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (c : ℝ) (f : List Ω → ℝ) (n : ℕ) (h : List Ω) :
    historyExpectation law (fun h => c * f h) n h =
      c * historyExpectation law f n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => simp only [historyExpectation, ih,
      Cslib.Optimization.OneConstraint.Distribution.mean_mul]

/-- Expected accumulated bill over a finite execution. The bill is charged before
sampling the next response; use the conditional mean bill at that history. -/
@[expose] def executionCost {Ω : Type} [Fintype Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (bill : List Ω → ℝ) : ℕ → List Ω → ℝ
  | 0, _ => 0
  | n + 1, h => bill h + (law h).mean (fun x => executionCost law bill n (x :: h))

/-- Finite tower-property accounting: cost is the sum of marginal expected bills.
No independence between bills, responses or stopping decisions is required. -/
theorem executionCost_eq_sum {Ω : Type} [Fintype Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (bill : List Ω → ℝ) (n : ℕ) (h : List Ω) :
    executionCost law bill n h =
      ∑ t ∈ Finset.range n, historyExpectation law bill t h := by
  induction n generalizing h with
  | zero => simp [executionCost]
  | succ n ih =>
    simp only [executionCost, ih,
      Cslib.Optimization.OneConstraint.Distribution.mean]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_range_succ']
    simp only [historyExpectation, Cslib.Optimization.OneConstraint.Distribution.mean,
      add_comm]

/-- Actual accumulated response-dependent bills along a newest-first transcript.
Stopping is represented by setting the bill to zero after retained completion. -/
@[expose] def accruedBill (bill : List Ω → Ω → ℝ) : List Ω → ℝ
  | [] => 0
  | x :: h => accruedBill bill h + bill h x

/-- The finite expected-cost recursion equals expectation of actual accumulated
response-dependent bills, using their conditional means under the execution law.
This is the tower-property bridge, allowing arbitrary bill/response correlation. -/
theorem historyExpectation_accruedBill {Ω : Type} [Fintype Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (bill : List Ω → Ω → ℝ) (n : ℕ) (h : List Ω) :
    historyExpectation law (accruedBill bill) n h = accruedBill bill h +
      executionCost law (fun h => (law h).mean (bill h)) n h := by
  induction n generalizing h with
  | zero => simp [historyExpectation, executionCost]
  | succ n ih =>
    simp only [historyExpectation, ih, accruedBill, executionCost,
      Cslib.Optimization.OneConstraint.Distribution.mean_add,
      Cslib.Optimization.OneConstraint.Distribution.mean_const]
    ring

open scoped Classical in
/-- A conditional upper bill bound on each reached turn gives the stopped-cost
sum in Appendix A.5. Completion is tested on the actual retained family. Bills
are zero after completion; the law may continue sampling auxiliary responses.
The horizon is finite, and no untruncated stopping-time claim is made. -/
theorem stoppedCost_le_reach_sum {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (bill : List Ω → ℝ) (c : ℝ)
    (hb : ∀ h, bill h ≤ c *
      (if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)) (n : ℕ) :
    executionCost law bill n [] ≤
      ∑ t ∈ Finset.range n, historyExpectation law
        (fun h => c * (if I.covered (selected I ρ proposal h) = I.ground
          then 0 else 1)) t [] := by
  rw [executionCost_eq_sum]
  exact Finset.sum_le_sum fun t _ => historyExpectation_mono law _ _ hb t []

open scoped Classical in
/-- Probability that the next turn is reached when stopping at actual retained
completion. This is at most the complementary binomial tail from Appendix A.5,
with index `t` counting turns already sampled (the reached turn is `t+1`). -/
theorem reach_le_binomial_complement {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r t : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0)) :
    historyExpectation law
      (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1) t [] ≤
      1 - ∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial t p := by
  have hb := binomial_le_completion I ρ proposal law a r t hr p hp
  have he : (fun h =>
      (if I.covered (selected I ρ proposal h) = I.ground then (0 : ℝ) else 1) +
      (if I.covered (selected I ρ proposal h) = I.ground then (1 : ℝ) else 0)) =
      (fun _ => 1) := by
    funext h
    split_ifs <;> norm_num
  have hs := historyExpectation_add law
    (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)
    (fun h => if I.covered (selected I ρ proposal h) = I.ground then 1 else 0) t []
  rw [he, historyExpectation_const] at hs
  linarith

open scoped Classical in
/-- The finite stopped token-cost bound of Appendix A.5, derived from actual
retained-set reach probabilities and conditional mean bills. No expected-total-cost
bound is a premise. See `accruedBill_le_mean` for the derived untruncated-mean bound. -/
theorem stoppedCost_le_binomial_sum {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r n : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0))
    (bill : List Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ h, bill h ≤ c *
      (if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)) :
    executionCost law bill n [] ≤
      ∑ t ∈ Finset.range n, c *
        (1 - ∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial t p) := by
  apply (stoppedCost_le_reach_sum I ρ proposal law bill c hb n).trans
  apply Finset.sum_le_sum
  intro t _
  rw [historyExpectation_mul]
  exact mul_le_mul_of_nonneg_left
    (reach_le_binomial_complement I ρ proposal law a r t hr p hp) hc

open scoped Classical in
/-- The stopped-cost sum for actual response-dependent bills. The only cost
premise is the one-turn conditional upper bound, zero after actual completion. -/
theorem accruedBill_le_binomial_sum {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r n : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0))
    (bill : List Ω → Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ h, (law h).mean (bill h) ≤ c *
      (if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)) :
    historyExpectation law (accruedBill bill) n [] ≤
      ∑ t ∈ Finset.range n, c *
        (1 - ∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial t p) := by
  rw [historyExpectation_accruedBill, accruedBill, zero_add]
  exact stoppedCost_le_binomial_sum I ρ proposal law a r n hr p hp _ c hc hb

open scoped Classical in
/-- The actual response-bill expectation is bounded by `c * r / p`, uniformly
in the finite horizon, under the source's conditional productivity/cost bounds. -/
theorem accruedBill_le_mean {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r n : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ))
    (hp : ∀ h, (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0))
    (bill : List Ω → Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hb : ∀ h, (law h).mean (bill h) ≤ c *
      (if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)) :
    historyExpectation law (accruedBill bill) n [] ≤ c * ((r : ℝ) / p) := by
  apply (accruedBill_le_binomial_sum I ρ proposal law a r n hr p hp bill c hc hb).trans
  simp only [← binomialFailure_eq_complement, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_binomialFailure_le p hp0 n r) hc

open scoped Classical in
/-- Actual noncompletion probabilities are summable, derived from the productivity
condition. Consequently their limit is zero. This is a statement about consistent
finite-horizon laws; it does not construct an infinite path-space measure. -/
theorem summable_noncompletion {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ))
    (hp : ∀ h, (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0)) :
    Summable (fun t => historyExpectation law
      (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1) t []) := by
  apply (summable_binomialFailure p hp0 r).of_nonneg_of_le
  · intro t
    have hm := historyExpectation_mono law (fun _ => 0)
      (fun h => if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)
      (fun h => by split_ifs <;> norm_num) t []
    simpa only [historyExpectation_const] using hm
  · intro t
    rw [binomialFailure_eq_complement]
    exact reach_le_binomial_complement I ρ proposal law a r t hr p hp

open scoped Classical in
/-- Nonnegative actual bills have a summable series of marginal expected charges,
with total at most `c * r / p`. This derives finiteness before any limit passage.
The finite tower identity identifies its partial sums with actual accrued-bill
expectations. No infinite path-space random variable is asserted here. -/
theorem expectedBills_summable_le {Ω : Type} [Fintype Ω]
    (I : Instance E J) (ρ : ℝ)
    (proposal : List Ω → Ω → List (Finset J))
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (a r : ℕ) (hr : I.ground.card ≤ a * r) (p : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ))
    (hp : ∀ h, (p : ℝ) ≤ (law h).mean
      (fun x => if productive I ρ proposal a h x then 1 else 0))
    (bill : List Ω → Ω → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hbn : ∀ h x, 0 ≤ bill h x)
    (hb : ∀ h, (law h).mean (bill h) ≤ c *
      (if I.covered (selected I ρ proposal h) = I.ground then 0 else 1)) :
    Summable (fun t => historyExpectation law (fun h => (law h).mean (bill h)) t []) ∧
    (∑' t, historyExpectation law (fun h => (law h).mean (bill h)) t []) ≤
      c * ((r : ℝ) / p) := by
  let f := fun t => historyExpectation law (fun h => (law h).mean (bill h)) t []
  have hn : ∀ t, 0 ≤ f t := by
    intro t
    have hm : ∀ h, 0 ≤ (law h).mean (bill h) := by
      intro h
      exact Finset.sum_nonneg fun x _ => mul_nonneg ((law h).nonneg x) (hbn h x)
    have hh := historyExpectation_mono law (fun _ => 0) _ hm t []
    simpa only [historyExpectation_const] using hh
  have hsum : ∀ n, ∑ t ∈ Finset.range n, f t ≤ c * ((r : ℝ) / p) := by
    intro n
    rw [← executionCost_eq_sum]
    have ht := accruedBill_le_mean I ρ proposal law a r n hr p hp0 hp bill c hc hb
    simpa only [historyExpectation_accruedBill, accruedBill, zero_add] using ht
  exact ⟨summable_of_sum_range_le hn hsum, Real.tsum_le_of_sum_range_le hn hsum⟩

end Cslib.Probability.StochasticOracle.AdaptiveSelection
