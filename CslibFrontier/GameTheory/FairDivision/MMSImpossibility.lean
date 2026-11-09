/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.ByContra

/-!
# Four-agent maximin-share impossibility

[EzraGarbuz2027], Theorem 2, PDF p. 13: eleven strictly positive indivisible
goods, two agents of each additive valuation, maximin share 21 for every agent,
and no complete allocation giving everyone more than 20. Goods are indexed
in the source order a,...,k. Allocations assign each good to exactly one of four
agents; empty bundles are permitted. `Guarantees` is the actual maximin-share
feasibility predicate, maximizing over all four-way partitions, not just the
partitions displayed in the paper.

The proof replaces Appendix B's enumeration of 4^11 allocations by a certificate
on unions S of the two type-1 agents' bundles. Necessary inequalities leave only
85 out of 2048 subsets. Each remaining subset is checked for possible two-way
splits of S and its complement. All finite checking uses kernel `decide`.

## Main definitions

* `itemValue`, `value`, `bundle`: the positive source table and complete-allocation utilities.
* `Guarantees`: a threshold attainable in an arbitrary four-way partition.

## Main results

* `guarantees_iff`: every agent's maximin share is exactly 21.
* `unavoidable_loss`: every complete allocation leaves an agent with utility at most 20.

## References

* [T. Ezra and T. Garbuz, *Improved Impossibility Bounds for Maximin Share Allocations*]
  [EzraGarbuz2027],
  Theorem 2, PDF p. 13, with the finite certificate in Appendix B.
-/

public section

namespace Cslib.FairDivision.MMSImpossibility

/-- The source's type-1 and type-2 valuations, respectively. -/
@[expose] def itemValue (t : Bool) : Fin 11 → ℕ :=
  if t then ![1, 14, 5, 10, 1, 9, 6, 7, 7, 5, 19]
  else ![1, 17, 3, 10, 1, 10, 7, 7, 7, 3, 18]

/-- Additive value of a bundle. -/
@[expose] def value (t : Bool) (s : Finset (Fin 11)) : ℕ :=
  ∑ g ∈ s, itemValue t g

/-- A complete allocation of all eleven goods. -/
abbrev Allocation := Fin 11 → Fin 4

/-- The bundle delivered to agent i. -/
@[expose] def bundle (a : Allocation) (i : Fin 4) : Finset (Fin 11) :=
  Finset.univ.filter fun g => a g = i

/-- A threshold attainable simultaneously in a four-way partition for one valuation.
The greatest attainable threshold is that valuation's maximin share. -/
@[expose] def Guarantees (t : Bool) (n : ℕ) : Prop :=
  ∃ a : Allocation, ∀ i, n ≤ value t (bundle a i)

/-- All goods have strictly positive value for either type. -/
theorem positive : ∀ t g, 0 < itemValue t g := by decide

/-- Each valuation has total 84. -/
theorem total : ∀ t, value t Finset.univ = 84 := by decide

private theorem split_value (t : Bool) (s : Finset (Fin 11)) :
    value t s + value t (Finset.univ \ s) = 84 := by
  unfold value
  rw [Nat.add_comm, Finset.sum_sdiff (Finset.subset_univ s)]
  exact total t

/-- A bundle can be divided into two bundles of value at least 21. -/
@[expose] def Splits (t : Bool) (s : Finset (Fin 11)) : Prop :=
  ∃ u ∈ s.powerset, 21 ≤ value t u ∧ 21 ≤ value t (s \ u)

private instance (t : Bool) (s : Finset (Fin 11)) : Decidable (Splits t s) :=
  inferInstanceAs (Decidable (∃ u ∈ s.powerset,
    21 ≤ value t u ∧ 21 ≤ value t (s \ u)))

-- Reduction traverses the 2048-subset powerset; no native evaluator is used.
set_option maxRecDepth 16384 in
private theorem split_certificate : ∀ s ∈ (Finset.univ : Finset (Fin 11)).powerset,
    42 ≤ value false s → value true s ≤ 42 →
    ¬ (Splits false s ∧ Splits true (Finset.univ \ s)) := by decide

/-- The explicit MMS partitions in the source, as assignment functions. -/
@[expose] def witness (t : Bool) : Allocation :=
  if t then ![1, 2, 3, 0, 1, 3, 0, 2, 3, 0, 1]
  else ![0, 0, 0, 1, 1, 1, 2, 2, 2, 3, 3]

/-- Every cell in the corresponding witness partition has value exactly 21. -/
theorem witness_value : ∀ t i, value t (bundle (witness t) i) = 21 := by decide

private theorem allocation_total (t : Bool) (a : Allocation) :
    value t (bundle a 0) + value t (bundle a 1) +
      value t (bundle a 2) + value t (bundle a 3) = 84 := by
  have h := total t
  unfold value bundle at *
  simp only [Finset.sum_filter] at *
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [← h]
  apply Finset.sum_congr rfl
  intro g _
  generalize a g = j
  fin_cases j <;> simp

/-- Exact maximin-share semantics: a threshold is attainable iff it is at most 21. -/
theorem guarantees_iff (t : Bool) (n : ℕ) : Guarantees t n ↔ n ≤ 21 := by
  constructor
  · rintro ⟨a, ha⟩
    have h := allocation_total t a
    have h0 := ha 0
    have h1 := ha 1
    have h2 := ha 2
    have h3 := ha 3
    omega
  · intro h
    exact ⟨witness t, fun i => (witness_value t i).symm ▸ h⟩

/-- Agents 0 and 1 use type 1; agents 2 and 3 use type 2. -/
@[expose] def agentType (i : Fin 4) : Bool := decide (2 ≤ i.val)

/-- Every complete allocation leaves an agent with value at most 20. -/
theorem unavoidable_loss (a : Allocation) :
    ∃ i, value (agentType i) (bundle a i) ≤ 20 := by
  by_contra! h
  let s := bundle a 0 ∪ bundle a 1
  have disj (i j : Fin 4) (hne : i ≠ j) : Disjoint (bundle a i) (bundle a j) := by
    simp only [bundle, Finset.disjoint_filter]
    intro g _ hi hj
    exact hne (hi.symm.trans hj)
  have hs (t : Bool) : value t s = value t (bundle a 0) + value t (bundle a 1) := by
    exact Finset.sum_union (disj 0 1 (by decide))
  have hc : Finset.univ \ s = bundle a 2 ∪ bundle a 3 := by
    ext g
    simp only [s, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
      bundle, Finset.mem_filter, Finset.mem_univ, true_and]
    generalize a g = j
    fin_cases j <;> simp
  have hv : value true (Finset.univ \ s) =
      value true (bundle a 2) + value true (bundle a 3) := by
    rw [hc]
    exact Finset.sum_union (disj 2 3 (by decide))
  have h0 : 21 ≤ value false (bundle a 0) := h 0
  have h1 : 21 ≤ value false (bundle a 1) := h 1
  have h2 : 21 ≤ value true (bundle a 2) := h 2
  have h3 : 21 ≤ value true (bundle a 3) := h 3
  have lower : 42 ≤ value false s := by rw [hs]; omega
  have upper : value true s ≤ 42 := by
    have ht := split_value true s
    omega
  have diff (i j : Fin 4) (hne : i ≠ j) :
      (bundle a i ∪ bundle a j) \ bundle a i = bundle a j := by
    exact Finset.union_sdiff_cancel_left (disj i j hne)
  apply split_certificate s (Finset.mem_powerset.mpr (Finset.subset_univ s)) lower upper
  constructor
  · refine ⟨bundle a 0, Finset.mem_powerset.mpr Finset.subset_union_left, h0, ?_⟩
    change 21 ≤ value false ((bundle a 0 ∪ bundle a 1) \ bundle a 0)
    rw [diff 0 1 (by decide)]
    exact h1
  · rw [hc]
    refine ⟨bundle a 2, Finset.mem_powerset.mpr Finset.subset_union_left, h2, ?_⟩
    rw [diff 2 3 (by decide)]
    exact h3

end Cslib.FairDivision.MMSImpossibility
