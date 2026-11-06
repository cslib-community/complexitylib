/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.CutoffFamilies
public import Complexity.Algorithms.Lean.DynamicProgramming.RoundedProduct
import Mathlib.Tactic

/-!
# Executable rounded-product two-batch selection

The algorithm in [Wang2027], Theorem 2(2), PDF p. 8, on rational input indexed
by `Fin k`. Thresholds, optional items, maximum-cost members, rounded tables and
witnesses are explicitly enumerated. There is no optimization oracle or powerset
in the implementation. `choose` compares exact rational savings and returns the
best nonempty first batch found; the full batch is a fallback.

This module supplies executable code, not a completed FPTAS theorem. The generic
DP has checked soundness, dominance, approximation and operation bounds, and the
cutoff reduction has checked deadline soundness and coverage. Their global
approximation bridge and binary bit-cost bound remain open. In particular,
executability and a polynomial number of table states do not imply a certified
polynomial bit runtime.

## Main definitions

* `TwoBatchApproximation.candidates`: actual cutoff/maximum-cost/DP enumeration.
* `TwoBatchApproximation.choose`: best candidate by exact savings comparison.

## Main results

* `choose_feasible`, `choose_schedule_feasible`: nonempty batches and exact deadlines.
* `choose_success`, `choose_expectedCost`: maximum success and actual stopped cost.
* `gain_choose_ge`: exact savings dominate every enumerated candidate.
-/

public section
namespace Cslib.Probability.StochasticOracle.TwoBatchApproximation
open Cslib.Algorithms.Lean.DynamicProgramming.MinProduct

variable {k : ℕ} (I : FullCoverInstance (Fin k) ℚ)

/-- The full finite input population, in canonical index order. -/
@[expose] def population : List (Fin k) := List.finRange k

/-- Independent per-opportunity failure probability. -/
@[expose] def failure (i : Fin k) : ℚ := 1 - I.success i

/-- Sum of expected billed token costs in an explicit list. -/
@[expose] def cost (items : List (Fin k)) : ℚ := (items.map I.cost).sum

/-- Independent failure product in an explicit list. -/
@[expose] def failureProduct (items : List (Fin k)) : ℚ :=
  (items.map (failure I)).prod

/-- Optional opportunities: permitted in the first batch but not forced there. -/
@[expose] def optional (a b : ℚ) : List (Fin k) :=
  population.filter (fun i => I.cutoff i ≤ a ∧ I.cutoff i ≤ b)

/-- Opportunities forced into the first batch by the second cutoff. -/
@[expose] def forced (b : ℚ) : List (Fin k) :=
  population.filter (fun i => b < I.cutoff i)

/-- Reconstruct the first batch from selected optional second-batch opportunities. -/
@[expose] def firstBatch (a b : ℚ) (second : List (Fin k)) : Finset (Fin k) :=
  (forced I b ++ (optional I a b).filter (· ∉ second)).toFinset

/-- One maximum-cost-member branch, with all more costly optional members omitted. -/
@[expose] def maximumBranch (ε a b : ℚ) (r : Fin k) : List (Finset (Fin k)) :=
  let items := (optional I a b).filter (fun i => I.cost i ≤ I.cost r ∧ i ≠ r)
  let outside := failureProduct I ((optional I a b).filter (fun i => I.cost r < I.cost i))
  (branch I.cost (failure I) ε r outside items).map (fun e => firstBatch I a b e.selected)

/-- Enumerate empty-second-selection and maximum-cost-member candidates for a
valid family, discarding empty first batches. -/
@[expose] def familyCandidates (ε a b : ℚ) : List (Finset (Fin k)) :=
  if (forced I b).all (fun i => decide (I.cutoff i ≤ a)) then
    (firstBatch I a b [] :: (optional I a b).flatMap (maximumBranch I ε a b)).filter
      (fun A => decide A.Nonempty)
  else []

/-- Enumerate the actual threshold pairs, including a zero second cutoff. -/
@[expose] def candidates (ε D : ℚ) : List (Finset (Fin k)) :=
  (population.map I.cutoff).flatMap fun a =>
    (0 :: population.map I.cutoff).flatMap fun b =>
      if a + b ≤ D then familyCandidates I ε a b else []

/-- Exact saving, computed directly from the input and reconstructed first batch. -/
@[expose] def gain (A : Finset (Fin k)) : ℚ :=
  (1 - I.batchFailure A) * I.batchCost (Finset.univ \ A)

/-- Compare exact savings, retaining a deterministic tie-breaking convention. -/
@[expose] def better (A B : Finset (Fin k)) : Finset (Fin k) :=
  if gain I A < gain I B then B else A

/-- Return the best enumerated candidate, with the concurrent full batch as a
zero-saving fallback. The intended preconditions are `k > 0`, positive tolerance
below one, and a deadline admitting the full concurrent batch. -/
@[expose] def choose (ε D : ℚ) : Finset (Fin k) :=
  (candidates I ε D).foldl (better I) Finset.univ

/-- The selected result dominates each enumerated candidate in exact savings. -/
theorem gain_choose_ge (ε D : ℚ) {A : Finset (Fin k)} (hA : A ∈ candidates I ε D) :
    gain I A ≤ gain I (choose I ε D) := by
  have hb (B C : Finset (Fin k)) : gain I B ≤ gain I (better I B C) ∧
      gain I C ≤ gain I (better I B C) := by
    unfold better
    split_ifs with h
    · exact ⟨h.le,le_rfl⟩
    · exact ⟨le_rfl,le_of_not_gt h⟩
  have hf : ∀ (xs : List (Finset (Fin k))) (B : Finset (Fin k)),
      gain I B ≤ gain I (xs.foldl (better I) B) ∧
        ∀ C ∈ xs, gain I C ≤ gain I (xs.foldl (better I) B) := by
    intro xs
    induction xs with
    | nil => intro B; exact ⟨le_rfl,by simp⟩
    | cons C cs ih =>
      intro B
      obtain ⟨h₀,h₁⟩ := ih (better I B C)
      refine ⟨(hb B C).1.trans h₀,?_⟩
      intro E hE
      rcases List.mem_cons.mp hE with rfl | hE
      · exact (hb B E).2.trans h₀
      · exact h₁ E hE
  exact (hf (candidates I ε D) Finset.univ).2 A hA

private theorem firstBatch_mem_family (a b : ℚ) (second : List (Fin k))
    (h : ∀ i ∈ forced I b, I.cutoff i ≤ a) :
    I.InCutoffFamily a b (firstBatch I a b second) := by
  constructor
  · intro i hi
    have hib : b < I.cutoff i := (Finset.mem_filter.mp hi).2
    simp [firstBatch, forced, population, hib]
  · intro i hi
    have hm : i ∈ forced I b ∨ i ∈ optional I a b ∧ i ∉ second := by
      simpa [firstBatch] using hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases hm with hi | ⟨hi,_⟩
    · exact h i hi
    · exact (show I.cutoff i ≤ a ∧ I.cutoff i ≤ b by
        simpa [optional, population] using hi).1

private theorem familyCandidates_feasible {ε D a b : ℚ}
    (hab : (a, b) ∈ I.cutoffPairs D) {A : Finset (Fin k)}
    (hA : A ∈ familyCandidates I ε a b) : I.TwoBatchFeasible D A := by
  unfold familyCandidates at hA
  split_ifs at hA with hf
  · obtain ⟨hA,hn⟩ := List.mem_filter.mp hA
    have hfamily : ∀ i ∈ forced I b, I.cutoff i ≤ a := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using hf
    have hA' : ∃ second, A = firstBatch I a b second := by
      rcases List.mem_cons.mp hA with h | h
      · exact ⟨[],h⟩
      · obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp h
        obtain ⟨e,_,he⟩ := List.mem_map.mp hr
        exact ⟨e.selected,he.symm⟩
    obtain ⟨second,rfl⟩ := hA'
    exact cutoff_family_feasible I hab (of_decide_eq_true hn)
      (firstBatch_mem_family I a b second hfamily)
  · simp at hA

/-- Every enumerated candidate is nonempty and satisfies the original deadline,
regardless of any approximation or running-time claim. -/
theorem candidates_feasible {ε D : ℚ} {A : Finset (Fin k)}
    (hA : A ∈ candidates I ε D) : I.TwoBatchFeasible D A := by
  obtain ⟨a,ha,ha'⟩ := List.mem_flatMap.mp hA
  obtain ⟨b,hb,hA⟩ := List.mem_flatMap.mp ha'
  by_cases hab : a + b ≤ D
  · simp only [hab, ite_true] at hA
    have hpair : (a, b) ∈ I.cutoffPairs D := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hab⟩
      · simpa [population] using ha
      · simpa [population] using hb
    exact familyCandidates_feasible I hpair hA
  · simp [hab] at hA

/-- The chosen first batch is nonempty and deadline-feasible on nonempty inputs
admitting a concurrent full batch. -/
theorem choose_feasible {ε D : ℚ} (hk : 0 < k)
    (hD : I.batchDuration Finset.univ ≤ D) : I.TwoBatchFeasible D (choose I ε D) := by
  have huniv : I.TwoBatchFeasible D Finset.univ := by
    refine ⟨⟨⟨0,hk⟩,Finset.mem_univ _⟩,?_⟩
    simpa [FullCoverInstance.batchDuration] using hD
  have step (xs : List (Finset (Fin k))) (hxs : ∀ A ∈ xs, I.TwoBatchFeasible D A)
      (B : Finset (Fin k)) (hB : I.TwoBatchFeasible D B) :
      I.TwoBatchFeasible D (xs.foldl (better I) B) := by
    induction xs generalizing B with
    | nil => exact hB
    | cons A as ih =>
      apply ih (fun C hC => hxs C (List.mem_cons_of_mem _ hC))
      unfold better
      split_ifs
      · exact hxs A (List.mem_cons_self ..)
      · exact hB
  exact step (candidates I ε D) (fun _ h => candidates_feasible I h) _ huniv

open scoped Classical in
/-- The actual complementary schedule meets the deadline and uses no opportunity
twice. Local computation time is excluded from the source deadline convention. -/
theorem choose_schedule_feasible {ε D : ℚ} (hk : 0 < k)
    (hD : I.batchDuration Finset.univ ≤ D) :
    Plan.Feasible I (n := 2) (choose I ε D,((choose I ε D)ᶜ,())) D := by
  have hf := choose_feasible I (ε := ε) hk hD
  constructor
  · simp [Plan.NoReuse, Plan.used, Finset.disjoint_left]
  · simp only [Plan.duration, add_zero]
    convert hf.2 using 1
    congr 2
    ext i
    simp

/-- The stopped cost of the implemented selection is exactly baseline cost minus
its computed saving; the whole reached batch is charged. -/
theorem choose_expectedCost (ε D : ℚ) :
    Plan.expectedCost I (n := 2) (choose I ε D,((choose I ε D)ᶜ,())) =
      I.batchCost Finset.univ - gain I (choose I ε D) := by
  have hs : I.batchCost (choose I ε D) + I.batchCost (choose I ε D)ᶜ =
      I.batchCost Finset.univ := Finset.sum_add_sum_compl _ I.cost
  have hc : Finset.univ \ choose I ε D = (choose I ε D)ᶜ := by
    ext i
    simp
  simp only [Plan.expectedCost, mul_zero, add_zero, gain, hc]
  linear_combination hs

/-- The selected schedule has the exact maximum success probability, with no
oracle for the desired output or assumed success guarantee. -/
theorem choose_success (ε D : ℚ) :
    Plan.success I (n := 2) (choose I ε D,((choose I ε D)ᶜ,())) =
      1 - I.batchFailure Finset.univ := by
  apply (Plan.success_eq_total_iff I _ ?_).mpr
  · ext i
    simp only [Plan.used, Finset.mem_union, Finset.mem_compl, Finset.notMem_empty,
      or_false, Finset.mem_univ, iff_true]
    exact Classical.em _
  · simp [Plan.NoReuse, Plan.used, Finset.disjoint_left]

end Cslib.Probability.StochasticOracle.TwoBatchApproximation
