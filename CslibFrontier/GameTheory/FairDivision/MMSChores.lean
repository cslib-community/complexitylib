/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.FairDivision.MMSImpossibility
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.ByContra

/-!
# Four-agent chores maximin-share impossibility

[EzraGarbuz2027], Theorem 4, PDF p. 14 and Appendix B.2, pp. 18:
eleven strictly positive chores, two agents of each cost type, exact chores
MMS equal to proportional share 90, and unavoidable cost at least 93.
Allocations are complete assignments, including possibly empty bundles.
The upper-bound convention for chores is explicit in `Caps`: its least
attainable threshold is MMS. The allocation utilities and the two source
partitions are shared with the goods instance.

The finite certificate checks all candidate unions of the two type-1 bundles,
and all their possible splits, with kernel `decide`. No allocation restrictions
or assumed rigidity enter the conclusion. This is the concrete witness for
31/30, rather than a definition of the global supremum over all instances.
-/

public section

namespace Cslib.FairDivision.MMSChores

open MMSImpossibility (Allocation bundle witness agentType)

/-- The source's type-1 and type-2 cost functions, respectively. -/
@[expose] def itemCost (t : Bool) : Fin 11 → ℕ :=
  if t then ![21, 45, 27, 39, 15, 39, 24, 45, 24, 27, 54]
  else ![19, 40, 31, 37, 16, 37, 25, 40, 25, 31, 59]

/-- Additive cost of a bundle. -/
@[expose] def cost (t : Bool) (s : Finset (Fin 11)) : ℕ :=
  ∑ g ∈ s, itemCost t g

/-- A cost cap attainable in a four-way partition for one cost function.
The least attainable cap is the chores maximin share. -/
@[expose] def Caps (t : Bool) (n : ℕ) : Prop :=
  ∃ a : Allocation, ∀ i, cost t (bundle a i) ≤ n

/-- All chores have strictly positive cost for either type. -/
theorem positive : ∀ t g, 0 < itemCost t g := by decide

/-- Each cost function has total 360. -/
theorem total : ∀ t, cost t Finset.univ = 360 := by decide

private theorem split_cost (t : Bool) (s : Finset (Fin 11)) :
    cost t s + cost t (Finset.univ \ s) = 360 := by
  unfold cost
  rw [Nat.add_comm, Finset.sum_sdiff (Finset.subset_univ s)]
  exact total t

/-- A bundle can be divided into two bundles of cost at most 92. -/
private def Splits (t : Bool) (s : Finset (Fin 11)) : Prop :=
  ∃ u ∈ s.powerset, cost t u ≤ 92 ∧ cost t (s \ u) ≤ 92

private instance (t : Bool) (s : Finset (Fin 11)) : Decidable (Splits t s) :=
  inferInstanceAs (Decidable (∃ u ∈ s.powerset,
    cost t u ≤ 92 ∧ cost t (s \ u) ≤ 92))

-- Reduction traverses the 2048-subset powerset; no native evaluator is used.
set_option maxRecDepth 16384 in
private theorem split_certificate : ∀ s ∈ (Finset.univ : Finset (Fin 11)).powerset,
    cost false s ≤ 184 → 176 ≤ cost true s →
    ¬ (Splits false s ∧ Splits true (Finset.univ \ s)) := by decide

/-- Every cell in the corresponding witness partition has cost exactly 90. -/
theorem witness_cost : ∀ t i, cost t (bundle (witness t) i) = 90 := by decide

private theorem allocation_total (t : Bool) (a : Allocation) :
    cost t (bundle a 0) + cost t (bundle a 1) +
      cost t (bundle a 2) + cost t (bundle a 3) = 360 := by
  have h := total t
  unfold cost bundle at *
  simp only [Finset.sum_filter] at *
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [← h]
  apply Finset.sum_congr rfl
  intro g _
  generalize a g = j
  fin_cases j <;> simp

/-- Exact maximin-share semantics: a cost cap is attainable iff it is at least 90. -/
theorem caps_iff (t : Bool) (n : ℕ) : Caps t n ↔ 90 ≤ n := by
  constructor
  · rintro ⟨a, ha⟩
    have h := allocation_total t a
    have h0 := ha 0
    have h1 := ha 1
    have h2 := ha 2
    have h3 := ha 3
    omega
  · intro h
    exact ⟨witness t, fun i => (witness_cost t i).symm ▸ h⟩

/-- Every complete allocation gives an agent cost at least 93. -/
theorem unavoidable_loss (a : Allocation) :
    ∃ i, 93 ≤ cost (agentType i) (bundle a i) := by
  by_contra! h
  let s := bundle a 0 ∪ bundle a 1
  have disj (i j : Fin 4) (hne : i ≠ j) : Disjoint (bundle a i) (bundle a j) := by
    simp only [bundle, Finset.disjoint_filter]
    intro g _ hi hj
    exact hne (hi.symm.trans hj)
  have hs (t : Bool) : cost t s = cost t (bundle a 0) + cost t (bundle a 1) := by
    exact Finset.sum_union (disj 0 1 (by decide))
  have hc : Finset.univ \ s = bundle a 2 ∪ bundle a 3 := by
    ext g
    simp only [s, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      bundle, Finset.mem_filter, Finset.mem_univ, true_and]
    generalize a g = j
    fin_cases j <;> simp
  have hv : cost true (Finset.univ \ s) =
      cost true (bundle a 2) + cost true (bundle a 3) := by
    rw [hc]
    exact Finset.sum_union (disj 2 3 (by decide))
  have h0 : cost false (bundle a 0) ≤ 92 := by
    have hi : cost false (bundle a 0) < 93 := h 0
    omega
  have h1 : cost false (bundle a 1) ≤ 92 := by
    have hi : cost false (bundle a 1) < 93 := h 1
    omega
  have h2 : cost true (bundle a 2) ≤ 92 := by
    have hi : cost true (bundle a 2) < 93 := h 2
    omega
  have h3 : cost true (bundle a 3) ≤ 92 := by
    have hi : cost true (bundle a 3) < 93 := h 3
    omega
  have lower : cost false s ≤ 184 := by rw [hs]; omega
  have upper : 176 ≤ cost true s := by
    have ht := split_cost true s
    omega
  have diff (i j : Fin 4) (hne : i ≠ j) :
      (bundle a i ∪ bundle a j) \ bundle a i = bundle a j := by
    exact Finset.union_sdiff_cancel_left (disj i j hne)
  apply split_certificate s (Finset.mem_powerset.mpr (Finset.subset_univ s)) lower upper
  constructor
  · refine ⟨bundle a 0, Finset.mem_powerset.mpr Finset.subset_union_left, h0, ?_⟩
    change cost false ((bundle a 0 ∪ bundle a 1) \ bundle a 0) ≤ 92
    rw [diff 0 1 (by decide)]
    exact h1
  · rw [hc]
    refine ⟨bundle a 2, Finset.mem_powerset.mpr Finset.subset_union_left, h2, ?_⟩
    rw [diff 2 3 (by decide)]
    exact h3

/-- Appendix B.2's minimum possible maximum cost is exactly 93. -/
theorem allocation_cap_iff (c : ℕ) :
    (∃ a : Allocation, ∀ i, cost (agentType i) (bundle a i) ≤ c) ↔ 93 ≤ c := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨i, hi⟩ := unavoidable_loss a
    exact hi.trans (ha i)
  · intro hc
    refine ⟨witness false, fun i => le_trans ?_ hc⟩
    have hw : ∀ i, cost (agentType i) (bundle (witness false) i) ≤ 93 := by decide
    exact hw i

end Cslib.FairDivision.MMSChores
