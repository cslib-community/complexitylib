/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Counting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

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
* `Cslib.Logic.PL.ClauseSet.Sparsification.sum_countingUnitInsertions_le`: unit insertion budget.
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

/-- Unit insertion events telescope exactly to the final number of units minus the initial units.
The step and proper-heart premises refer to actual counting children, not a supplied bound. -/
theorem sum_countingUnitInsertions_add_card_units
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hproper : ∀ i < N, 1 ≤ (H i).card ∧ (H i).card < c i) (hψ : ∅ ∉ ψ 0) :
    (∑ i ∈ range N, (countingUnitInsertions (ψ i) (c i) (H i) (b i)).card) +
      ((ψ 0).filter fun C => C.card = 1).card =
      ((ψ N).filter fun C => C.card = 1).card := by
  have hempty : ∀ i, i ≤ N → ∅ ∉ ψ i := by
    intro i
    induction i with
    | zero => exact fun _ => hψ
    | succ i ih =>
      intro hi
      rw [hstep i (by omega)]
      exact empty_notMem_countingChild (ih (by omega))
        (hproper i (by omega)).1 (hproper i (by omega)).2 (b i)
  suffices ∀ n, n ≤ N →
      (∑ i ∈ range n, (countingUnitInsertions (ψ i) (c i) (H i) (b i)).card) +
        ((ψ 0).filter fun C => C.card = 1).card =
        ((ψ n).filter fun C => C.card = 1).card from this N le_rfl
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro hn
    have hprev := ih (by omega)
    have hinc := card_units_countingChild (hempty n (by omega))
      (hproper n (by omega)).1 (hproper n (by omega)).2 (b n)
    rw [← hstep n (by omega)] at hinc
    rw [sum_range_succ]
    omega

/-- The width-one base case of Appendix A.3: actual unit insertion events along a finite path
have total at most twice the number of declared variables. This charges heart units, petal units
and negated-heart units together, and excludes all units already present in the root.

The path consists of actual counting children with heavy proper hearts. Reducedness is needed
only at the root: if a legal first step exists, its nonempty flower rules out an empty root clause.
No finite ambient variable type, nontautology or native construction-cost premise is used. -/
theorem sum_countingUnitInsertions_le
    {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j)
    (N : ℕ) (ψ : ℕ → ClauseSet V) (c : ℕ → ℕ) (H : ℕ → Finset (Literal V)) (b : ℕ → Bool)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy θ (ψ i) (c i) (H i)) (hred : Reduced (ψ 0))
    (declared : Finset V) (hsupport : ∀ C ∈ ψ 0, ∀ l ∈ C, l.1 ∈ declared) :
    (∑ i ∈ range N, (countingUnitInsertions (ψ i) (c i) (H i) (b i)).card) ≤
      2 * declared.card := by
  by_cases hN : N = 0
  · subst N
    simp
  have hpos : 0 < N := Nat.pos_of_ne_zero hN
  have hempty : ∅ ∉ ψ 0 := by
    intro he
    obtain ⟨C, hC⟩ := (hheavy 0 hpos).flower_nonempty hθ
    have hCpos : 0 < C.card := by
      rw [(mem_flower.mp hC).2.1]
      have := (hheavy 0 hpos).1
      have := (hheavy 0 hpos).2.1
      omega
    exact hred C (flower_subset _ _ _ hC) ∅ he (empty_ssubset.mpr (card_pos.mp hCpos))
  have hs : ∀ n, n ≤ N → ∀ C ∈ ψ n, ∀ l ∈ C, l.1 ∈ declared := by
    intro n
    induction n with
    | zero => exact fun _ => hsupport
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      obtain ⟨D, hD⟩ := (hheavy n (by omega)).flower_nonempty hθ
      have hH : ∀ l ∈ H n, l.1 ∈ declared :=
        fun l hl => hprev D (flower_subset _ _ _ hD) l ((mem_flower.mp hD).2.2 hl)
      rw [hstep n (by omega)]
      exact support_countingChild (ψ n) (c n) (H n) declared hprev hH (b n)
  let possible : ClauseSet V := (declared ×ˢ (univ : Finset Bool)).image fun l => {l}
  have hsub : (ψ N).filter (fun C => C.card = 1) ⊆ possible := by
    intro C hC
    obtain ⟨l, hCl⟩ := card_eq_one.mp (mem_filter.mp hC).2
    apply mem_image.mpr
    refine ⟨l, mem_product.mpr ⟨?_, mem_univ _⟩, hCl.symm⟩
    exact hs N le_rfl C (mem_filter.mp hC).1 l (by simp [hCl])
  have hcard : ((ψ N).filter fun C => C.card = 1).card ≤ 2 * declared.card := by
    calc
      _ ≤ possible.card := card_le_card hsub
      _ ≤ (declared ×ˢ (univ : Finset Bool)).card := card_image_le
      _ = 2 * declared.card := by simp [Nat.mul_comm]
  have hsum := sum_countingUnitInsertions_add_card_units N ψ c H b hstep
    (fun i hi => ⟨(hheavy i hi).1, (hheavy i hi).2.1⟩) hempty
  omega

end Cslib.Logic.PL.ClauseSet.Sparsification
