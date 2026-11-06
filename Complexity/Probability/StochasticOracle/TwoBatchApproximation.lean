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

The global approximation theorem compares the actual selected candidate with
every nonempty deadline-feasible first batch. Its proof reconstructs the DP
witnesses and proves that minimum-product dominance preserves nonemptiness.
`choose_policy_approximation` extends the bound to randomized rational policies;
`TwoBatchGuarantees` covers arbitrary real private randomization. A polynomial
binary runtime for the complete selector remains a separate obligation.

## Main definitions

* `TwoBatchApproximation.candidates`: actual cutoff/maximum-cost/DP enumeration.
* `TwoBatchApproximation.choose`: best candidate by exact savings comparison.

## Main results

* `choose_feasible`, `choose_schedule_feasible`: nonempty batches and exact deadlines.
* `choose_success`, `choose_expectedCost`: maximum success and actual stopped cost.
* `gain_choose_ge`: exact savings dominate every enumerated candidate.
* `choose_approximation`: the global savings guarantee for every feasible first batch.
* `choose_policy_approximation`: savings and cost guarantees against randomized policies.
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

private theorem optional_nodup (a b : ℚ) : (optional I a b).Nodup :=
  (List.nodup_finRange k).filter _

private theorem failure_bounds (i : Fin k) : 0 < failure I i ∧ failure I i < 1 := by
  dsimp [failure]
  constructor <;> linarith [I.success_pos i, I.success_lt_one i]

private theorem failureProduct_bounds (xs : List (Fin k)) :
    0 ≤ failureProduct I xs ∧ failureProduct I xs ≤ 1 := by
  induction xs with
  | nil => simp [failureProduct]
  | cons i xs ih =>
    have hi := failure_bounds I i
    simp only [failureProduct, List.map_cons, List.prod_cons] at *
    exact ⟨mul_nonneg hi.1.le ih.1,
      (mul_le_mul_of_nonneg_right hi.2.le ih.1).trans (by simpa using ih.2)⟩

private theorem firstBatch_eq (a b : ℚ) (xs : List (Fin k)) :
    firstBatch I a b xs = (forced I b).toFinset ∪ ((optional I a b).toFinset \ xs.toFinset) := by
  ext i
  simp [firstBatch]

private theorem branch_reconstruction (ε a b : ℚ) (r : Fin k)
    (hr : r ∈ optional I a b) {e : Entry (Fin k)}
    (he : e ∈ choices
      (rounded I.cost (branchScale I.cost ε r
        ((optional I a b).filter (fun i => I.cost i ≤ I.cost r ∧ i ≠ r))))
      (failure I) (branchInitial I.cost ε r
        (failureProduct I ((optional I a b).filter (fun i => I.cost r < I.cost i)))
        ((optional I a b).filter (fun i => I.cost i ≤ I.cost r ∧ i ≠ r)))
      ((optional I a b).filter (fun i => I.cost i ≤ I.cost r ∧ i ≠ r))) :
    e.selected.Nodup ∧ e.selected.toFinset ⊆ (optional I a b).toFinset ∧
      e.product = I.batchFailure ((optional I a b).toFinset \ e.selected.toFinset) := by
  let items := (optional I a b).filter (fun i => I.cost i ≤ I.cost r ∧ i ≠ r)
  let initial := branchInitial I.cost ε r
    (failureProduct I ((optional I a b).filter (fun i => I.cost r < I.cost i))) items
  have he' : e ∈ choices (rounded I.cost (branchScale I.cost ε r items))
      (failure I) initial items := he
  have hn : (items ++ initial.selected).Nodup := by
    simp only [initial, branchInitial, List.nodup_append, List.nodup_cons,
      List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_true]
    refine ⟨(optional_nodup I a b).filter _, ?_⟩
    simp [items]
  have hs := choices_selected_sublist _ _ _ _ he'
  have hsub : e.selected.toFinset ⊆ (optional I a b).toFinset := by
    intro i hi
    have hi' := hs.subset (List.mem_toFinset.mp hi)
    simp only [initial, branchInitial, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hi'
    rcases hi' with hi' | rfl
    · exact List.mem_toFinset.mpr (List.mem_filter.mp hi').1
    · exact List.mem_toFinset.mpr hr
  refine ⟨hn.sublist hs,hsub,?_⟩
  rw [choices_product _ _ _ _ hn he']
  change failureProduct I ((optional I a b).filter (fun i => I.cost r < I.cost i)) *
    failureProduct I (items.filter (· ∉ e.selected)) = _
  have hrsel : r ∈ e.selected := by
    exact (choices_initial_sublist _ _ _ _ he').subset (by simp [initial, branchInitial])
  rw [failureProduct, failureProduct, ← List.prod_toFinset _ ((optional_nodup I a b).filter _),
    ← List.prod_toFinset _ (((optional_nodup I a b).filter _).filter _)]
  rw [← Finset.prod_union]
  · congr 1
    ext i
    have hc := le_total (I.cost i) (I.cost r)
    have hi : i ∈ e.selected → I.cost i ≤ I.cost r := by
      intro hi
      have := hs.subset hi
      have hh : i ∈ optional I a b ∧ I.cost i ≤ I.cost r ∧ i ≠ r ∨ i = r := by
        simpa [items, initial, branchInitial] using this
      rcases hh with hh | rfl
      · exact hh.2.1
      · exact le_rfl
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (⟨hi',hlt⟩ | ⟨⟨hi',hle,hne⟩,hnot⟩)
      · exact ⟨hi',fun h => (not_lt_of_ge (hi h)) hlt⟩
      · exact ⟨hi',hnot⟩
    · rintro ⟨hi',hnot⟩
      by_cases hle : I.cost i ≤ I.cost r
      · exact Or.inr ⟨⟨hi',hle,fun h => hnot (h ▸ hrsel)⟩,hnot⟩
      · exact Or.inl ⟨hi',lt_of_not_ge hle⟩
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hi hj
    exact (not_lt_of_ge hj.1.2.1) hi.2

private theorem reconstructed_gain (a b : ℚ) (xs : List (Fin k))
    (hn : xs.Nodup) (hs : xs.toFinset ⊆ (optional I a b).toFinset)
    (hf : ∀ i ∈ forced I b, I.cutoff i ≤ a) :
    gain I (firstBatch I a b xs) =
      (cost I (population.filter (fun i => a < I.cutoff i)) + (xs.map I.cost).sum) *
        (1 - I.batchFailure (forced I b).toFinset *
          I.batchFailure ((optional I a b).toFinset \ xs.toFinset)) := by
  let E := (population.filter (fun i => a < I.cutoff i)).toFinset
  let L := (forced I b).toFinset
  let S := (optional I a b).toFinset
  have hSL : Disjoint L S := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [L, S, forced, optional, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq] at hi hj
    exact (not_lt_of_ge hj.2.2) hi.2
  have hES : Disjoint E xs.toFinset := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hh := hs hj
    simp only [E, optional, List.mem_toFinset, List.mem_filter,
      decide_eq_true_eq] at hi hh
    exact (not_lt_of_ge hh.2.1) hi.2
  have hcompl : Finset.univ \ firstBatch I a b xs = E ∪ xs.toFinset := by
    ext i
    have hforce : b < I.cutoff i → I.cutoff i ≤ a := by
      intro hi
      exact hf i (by simp [forced, population, hi])
    have hsel : i ∈ xs → I.cutoff i ≤ a ∧ I.cutoff i ≤ b := by
      intro hi
      have := hs (List.mem_toFinset.mpr hi)
      simpa [optional, population] using this
    simp only [firstBatch_eq, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_sdiff, List.mem_toFinset, forced, optional,
      List.mem_filter, decide_eq_true_eq, population, List.mem_finRange, true_and, E]
    by_cases hi : i ∈ xs <;> by_cases hb : b < I.cutoff i <;>
      by_cases ha : I.cutoff i ≤ a <;> simp_all; linarith
  rw [gain, hcompl, FullCoverInstance.batchCost, Finset.sum_union hES,
    List.sum_toFinset I.cost hn]
  have hEcost : ∑ i ∈ E, I.cost i = cost I
      (population.filter (fun i => a < I.cutoff i)) :=
    List.sum_toFinset I.cost ((List.nodup_finRange k).filter _)
  rw [hEcost, firstBatch_eq, FullCoverInstance.batchFailure,
    Finset.prod_union (hSL.mono_right Finset.sdiff_subset)]
  change (1 - I.batchFailure L * I.batchFailure (S \ xs.toFinset)) * _ = _
  exact mul_comm _ _

private theorem branch_gain (ε a b : ℚ) (r : Fin k)
    (hr : r ∈ optional I a b)
    (hf : ∀ i ∈ forced I b, I.cutoff i ≤ a) {e : Entry (Fin k)}
    (he : e ∈ branch I.cost (failure I) ε r
      (failureProduct I ((optional I a b).filter (fun i => I.cost r < I.cost i)))
      ((optional I a b).filter (fun i => I.cost i ≤ I.cost r ∧ i ≠ r))) :
    gain I (firstBatch I a b e.selected) =
      e.gain I.cost (cost I (population.filter (fun i => a < I.cutoff i)))
        (I.batchFailure (forced I b).toFinset) := by
  obtain ⟨hn,hs,hp⟩ := branch_reconstruction I ε a b r hr (run_sound _ _ _ _ he)
  rw [reconstructed_gain I a b e.selected hn hs hf, Entry.gain, Entry.cost, hp]

private theorem family_approximation {ε a b : ℚ} (hε : 0 < ε)
    {A : Finset (Fin k)} (hn : A.Nonempty)
    (hfamily : I.InCutoffFamily a b A) :
    ∃ C ∈ familyCandidates I ε a b, (1 - ε) * gain I A ≤ gain I C := by
  let S := (optional I a b).toFinset
  let B := S \ A
  have hf : ∀ i ∈ forced I b, I.cutoff i ≤ a := by
    intro i hi
    have hi' : i ∈ I.forcedFirst b := by simpa [forced, population,
      FullCoverInstance.forcedFirst] using hi
    exact (Finset.mem_filter.mp (hfamily.2 (hfamily.1 hi'))).2
  have hA : firstBatch I a b B.toList = A := by
    ext i
    have hl := hfamily.1
    have hu := hfamily.2
    simp only [FullCoverInstance.forcedFirst,
      FullCoverInstance.allowedFirst, Finset.subset_iff, Finset.mem_filter,
      Finset.mem_univ, true_and] at hl hu
    simp only [firstBatch_eq, Finset.mem_union, List.mem_toFinset,
      Finset.mem_toList, Finset.mem_sdiff, forced, optional, List.mem_filter,
      decide_eq_true_eq, population, List.mem_finRange, true_and, B, S]
    constructor
    · rintro (h | ⟨h,hh⟩)
      · exact hl h
      · tauto
    · intro hi
      by_cases hb : b < I.cutoff i
      · exact Or.inl hb
      · exact Or.inr ⟨⟨hu hi,le_of_not_gt hb⟩,by tauto⟩
  have hall : (forced I b).all (fun i => decide (I.cutoff i ≤ a)) = true := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using hf
  by_cases hB : B.Nonempty
  · obtain ⟨r,hrB,hrmax⟩ := Finset.exists_max_image B I.cost hB
    have hrS : r ∈ optional I a b := List.mem_toFinset.mp (Finset.sdiff_subset hrB)
    let items := (optional I a b).filter (fun i => I.cost i ≤ I.cost r ∧ i ≠ r)
    let outside := failureProduct I
      ((optional I a b).filter (fun i => I.cost r < I.cost i))
    let initial := branchInitial I.cost ε r outside items
    let z := rounded I.cost (branchScale I.cost ε r items)
    let e := select z (failure I) initial B items
    have he : e ∈ choices z (failure I) initial items := select_mem_choices ..
    have heB : e.selected.toFinset = B := by
      rw [select_selected]
      ext i
      simp only [initial, branchInitial, List.mem_toFinset, List.mem_append,
        List.mem_filter, decide_eq_true_eq, List.mem_cons, List.not_mem_nil,
        or_false, items]
      constructor
      · rintro (⟨_,hi⟩ | rfl)
        · exact hi
        · exact hrB
      · intro hi
        by_cases hir : i = r
        · exact Or.inr hir
        · exact Or.inl ⟨⟨List.mem_toFinset.mp (Finset.sdiff_subset hi),
            hrmax i hi,hir⟩,hi⟩
    have her := branch_reconstruction I ε a b r hrS he
    have heA : firstBatch I a b e.selected = A := by
      rw [firstBatch_eq, heB, ← hA, firstBatch_eq, Finset.toList_toFinset]
    have hegain : e.gain I.cost
        (cost I (population.filter (fun i => a < I.cutoff i)))
        (I.batchFailure (forced I b).toFinset) = gain I A := by
      rw [← heA, reconstructed_gain I a b e.selected her.1 her.2.1 hf,
        Entry.gain, Entry.cost, her.2.2]
    obtain ⟨d,hd,_,hp,hgain⟩ := branch_approximation I.cost (failure I) r
      (fun i => (I.cost_pos i).le) (I.cost_pos r) hε
      (fun i => (failure_bounds I i).1.le) (fun i => (failure_bounds I i).2.le)
      (E := cost I (population.filter (fun i => a < I.cutoff i)))
      (f := I.batchFailure (forced I b).toFinset)
      (by unfold cost; exact List.sum_nonneg (fun x hx => by
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx; exact (I.cost_pos i).le))
      (Finset.prod_nonneg fun i _ => (failure_bounds I i).1.le)
      (I.batchFailure_le_one _) (failureProduct_bounds I _).1
      (failureProduct_bounds I _).2 items he
    have hdrec := branch_reconstruction I ε a b r hrS (run_sound _ _ _ _ hd)
    have hdnonempty : (firstBatch I a b d.selected).Nonempty := by
      by_contra hnot
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hnot
      have hLempty : (forced I b).toFinset = ∅ := by
        have hh : (forced I b).toFinset ⊆ firstBatch I a b d.selected := by
          rw [firstBatch_eq]; exact Finset.subset_union_left
        rw [hempty] at hh
        exact Finset.subset_empty.mp hh
      have hSempty : (optional I a b).toFinset \ d.selected.toFinset = ∅ := by
        have hh : (optional I a b).toFinset \ d.selected.toFinset ⊆
            firstBatch I a b d.selected := by
          rw [firstBatch_eq]; exact Finset.subset_union_right
        rw [hempty] at hh
        exact Finset.subset_empty.mp hh
      have hdprod : d.product = 1 := by
        rw [hdrec.2.2, hSempty]; simp [FullCoverInstance.batchFailure]
      have heprod : e.product < 1 := by
        have hnon : ((optional I a b).toFinset \ e.selected.toFinset).Nonempty := by
          rw [← heA, firstBatch_eq, hLempty, Finset.empty_union] at hn
          exact hn
        rw [her.2.2]
        obtain ⟨i,hi⟩ := hnon
        unfold FullCoverInstance.batchFailure
        rw [← Finset.mul_prod_erase _ _ hi]
        have hb := I.batchFailure_le_one
          (((optional I a b).toFinset \ e.selected.toFinset).erase i)
        change (1 - I.success i) * _ < 1
        calc
          _ ≤ (1 - I.success i) * 1 :=
            mul_le_mul_of_nonneg_left hb (sub_pos.mpr (I.success_lt_one i)).le
          _ < 1 := by linarith [I.success_pos i]
      rw [hdprod] at hp
      exact (not_lt_of_ge hp) heprod
    refine ⟨firstBatch I a b d.selected, ?_, ?_⟩
    · simp only [familyCandidates, hall, ite_true, List.mem_filter,
        decide_eq_true_eq]
      refine ⟨List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨r,hrS,?_⟩),hdnonempty⟩
      exact List.mem_map.mpr ⟨d,hd,rfl⟩
    · rw [branch_gain I ε a b r hrS hf hd, ← hegain]
      exact hgain
  · have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    have hAempty : firstBatch I a b [] = A := by simpa [hBempty] using hA
    refine ⟨A, ?_, ?_⟩
    · simp only [familyCandidates, hall, ite_true, List.mem_filter,
        decide_eq_true_eq]
      exact ⟨List.mem_cons.mpr (Or.inl hAempty.symm),hn⟩
    · have hg : 0 ≤ gain I A := by
        unfold gain
        apply mul_nonneg (sub_nonneg.mpr (I.batchFailure_le_one A))
        exact Finset.sum_nonneg (fun i _ => (I.cost_pos i).le)
      nlinarith

/-- The implemented selector approximates every nonempty deadline-feasible first
batch. The returned DP witness remains nonempty because its failure product is
no greater than the strictly subunit product of the comparison first batch.
This is the global approximation part of [Wang2027], Theorem 2(2); binary running
time is a separate obligation. -/
theorem choose_approximation {ε D : ℚ} (hε : 0 < ε)
    {A : Finset (Fin k)} (hA : I.TwoBatchFeasible D A) :
    (1 - ε) * gain I A ≤ gain I (choose I ε D) := by
  obtain ⟨⟨a,b⟩,hab,hfamily⟩ := cutoff_families_cover I hA
  obtain ⟨C,hC,hgain⟩ := family_approximation I hε hA.1 hfamily
  apply hgain.trans (gain_choose_ge I ε D ?_)
  obtain ⟨hp,hD⟩ := Finset.mem_filter.mp hab
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
  apply List.mem_flatMap.mpr
  refine ⟨a,?_,List.mem_flatMap.mpr ⟨b,?_,?_⟩⟩
  · simpa [population] using ha
  · simpa [population] using hb
  · simpa only [hD, ite_true] using hC

/-- Savings and stopped-cost guarantees against every randomized, feasible,
maximum-success two-turn policy in the paper's failure-oblivious model. No
optimizer, approximate output or global savings inequality is assumed. The
selected schedule's deadline and success are `choose_schedule_feasible` and
`choose_success`. This theorem does not assert binary running time. -/
theorem choose_policy_approximation {ε D : ℚ} (hk : 0 < k)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (π : Policy (Fin k) ℚ 2)
    (hπ : π.Feasible I D)
    (hp : (π.execution I).mean executionSuccess = 1 - I.batchFailure Finset.univ) :
    (1 - ε) * (I.batchCost Finset.univ -
      (π.execution I).mean (executionCost I)) ≤ gain I (choose I ε D) ∧
    Plan.expectedCost I (n := 2) (choose I ε D,((choose I ε D)ᶜ,())) ≤
      (π.execution I).mean (executionCost I) + ε *
        (I.batchCost Finset.univ - (π.execution I).mean (executionCost I)) := by
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  obtain ⟨A,hA,hcost⟩ := two_batch_reduction I D π hπ hp
  have hs : I.twoBatchCost A = I.batchCost Finset.univ - gain I A := by
    unfold gain
    convert twoBatchCost_eq_total_sub I A using 1
    congr 3
    ext i
    simp
  have hgain := choose_approximation I hε₀ hA
  have hbound : (1 - ε) * (I.batchCost Finset.univ -
      (π.execution I).mean (executionCost I)) ≤ gain I (choose I ε D) := by
    have hm := mul_le_mul_of_nonneg_left (show I.batchCost Finset.univ -
      (π.execution I).mean (executionCost I) ≤ gain I A by linarith)
      (sub_nonneg.mpr hε₁.le)
    exact hm.trans hgain
  refine ⟨hbound,?_⟩
  rw [choose_expectedCost]
  nlinarith

end Cslib.Probability.StochasticOracle.TwoBatchApproximation
