/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Counting

/-!
# Unit insertion accounting for counting sparsification

The width-one base case of Appendix A.2–A.3 [OpenAI2026ETH] counts actual first-insertion events,
including the negated-heart units of the counting B-child. A unit persists because its only strict
subclause is empty, and a legal step does not introduce an empty clause. Thus unit insertions
increase the number of units without deleting earlier units; they cannot be charged twice.

This module does not establish the higher-width deletion recurrence, depth, leaf-count or native
runtime bounds. The counting-tree construction is separate.

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.countingIntro`: the actual clauses added by a step.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingUnitInsertions`: its new unit clauses.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.card_units_countingChild`: one-step unit accounting.
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V]

/-- The heart in the A-child, or the petals together with every negated-heart unit in the B-child.
This records the payload before reduction, including clauses already present in the parent. -/
def countingIntro (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) : Bool → ClauseSet V
  | false => {H}
  | true => petals ψ c H ∪ negatedHeartUnits H

/-- New width-one payload clauses, excluding those already present immediately before the step.
Their cardinalities are insertion events; a later sum must not silently deduplicate events. -/
def countingUnitInsertions (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) (b : Bool) :
    ClauseSet V :=
  ((countingIntro ψ c H b) \ ψ).filter fun C => C.card = 1

/-- Both counting children use the payload recorded for insertion accounting. -/
theorem countingChild_eq_reduce_union (ψ : ClauseSet V) (c : ℕ)
    (H : Finset (Literal V)) (b : Bool) :
    countingChild ψ c H b = reduce (ψ ∪ countingIntro ψ c H b) := by
  cases b <;> simp only [countingChild, countingIntro, child, intro, union_assoc]

/-- Every payload clause in a proper nonempty-heart step is nonempty. -/
theorem countingIntro_nonempty {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (hH : 1 ≤ H.card) (hproper : H.card < c) {b : Bool} {C : Finset (Literal V)}
    (hC : C ∈ countingIntro ψ c H b) : C.Nonempty := by
  rw [← card_pos]
  cases b with
  | false =>
    have hCH : C = H := by simpa only [countingIntro, mem_singleton] using hC
    rw [hCH]
    omega
  | true =>
    rcases mem_union.mp hC with hC | hC
    · rw [card_of_mem_petals hC]
      omega
    · obtain ⟨l, -, rfl⟩ := mem_image.mp hC
      simp

/-- A step cannot introduce an empty clause when none was present. -/
theorem empty_notMem_countingChild {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (hψ : ∅ ∉ ψ) (hH : 1 ≤ H.card) (hproper : H.card < c) (b : Bool) :
    ∅ ∉ countingChild ψ c H b := by
  rw [countingChild_eq_reduce_union]
  intro h
  rcases mem_union.mp (reduce_subset _ h) with h | h
  · exact hψ h
  · exact Finset.not_nonempty_empty (countingIntro_nonempty hH hproper h)

private theorem mem_reduce_union_unit_iff {ψ X : ClauseSet V}
    (hψ : ∅ ∉ ψ) (hX : ∀ C ∈ X, C.Nonempty) {C : Finset (Literal V)} (hC : C.card = 1) :
    C ∈ reduce (ψ ∪ X) ↔ C ∈ ψ ∪ X := by
  constructor
  · intro h
    exact reduce_subset (ψ ∪ X) h
  · intro hmem
    rw [mem_reduce]
    refine ⟨hmem, ?_⟩
    intro D hD hDC
    have hDzero : D.card = 0 := by have := card_lt_card hDC; omega
    have hDEmpty : D = ∅ := card_eq_zero.mp hDzero
    subst D
    rcases mem_union.mp hD with hD | hD
    · exact hψ hD
    · exact Finset.not_nonempty_empty (hX _ hD)

/-- Existing units persist, and every payload unit survives immediate reduction.
No nontautology assumption is needed for this width-one fact. -/
theorem mem_countingChild_unit_iff {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (hψ : ∅ ∉ ψ) (hH : 1 ≤ H.card) (hproper : H.card < c) (b : Bool)
    {C : Finset (Literal V)} (hC : C.card = 1) :
    C ∈ countingChild ψ c H b ↔ C ∈ ψ ∨ C ∈ countingIntro ψ c H b := by
  rw [countingChild_eq_reduce_union, mem_reduce_union_unit_iff hψ
    (fun _ h => countingIntro_nonempty hH hproper h) hC, mem_union]

/-- Units after a step are precisely the existing units plus its new unit insertion batch. -/
theorem units_countingChild {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (hψ : ∅ ∉ ψ) (hH : 1 ≤ H.card) (hproper : H.card < c) (b : Bool) :
    (countingChild ψ c H b).filter (fun C => C.card = 1) =
      ψ.filter (fun C => C.card = 1) ∪ countingUnitInsertions ψ c H b := by
  ext C
  by_cases hC : C.card = 1
  · simp only [mem_filter, hC, and_true, mem_union, countingUnitInsertions, mem_sdiff]
    rw [mem_countingChild_unit_iff hψ hH hproper b hC]
    tauto
  · simp [hC, countingUnitInsertions]

/-- A counting step increases the number of units by exactly its number of new payload units.
In particular the added negated-heart units receive the same charge as all other unit insertions.
-/
theorem card_units_countingChild {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (hψ : ∅ ∉ ψ) (hH : 1 ≤ H.card) (hproper : H.card < c) (b : Bool) :
    ((countingChild ψ c H b).filter fun C => C.card = 1).card =
      (ψ.filter fun C => C.card = 1).card + (countingUnitInsertions ψ c H b).card := by
  rw [units_countingChild hψ hH hproper]
  apply card_union_of_disjoint
  rw [disjoint_left]
  intro C hC hnew
  exact (mem_sdiff.mp (mem_filter.mp hnew).1).2 (mem_filter.mp hC).1

end Cslib.Logic.PL.ClauseSet.Sparsification
