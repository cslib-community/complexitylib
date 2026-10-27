/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingPathBounds
import all ComplexityTests.SparsificationCountingInsertions

public section

open Cslib.Logic.PL
open ClauseSet.Sparsification Finset

namespace ComplexityTests.SparsificationCountingPathBounds

-- Reuse the full-Choice, two-step concrete fixture from the insertion-count tests. Its first
-- B-step inserts four pairs; its second step is selectable as A or B. The source/tests stay frozen.
open SparsificationCountingInsertions

example : ((range 2).filter fun m => dirs true m = true).card = 2 := by decide
example : ((range 2).filter fun m => dirs false m = true).card = 1 := by decide

example : ((range 2).filter fun m =>
    dirs true m = true ∧ sizes m - (hearts m).card = 2).card = 1 := by decide
example : ((range 2).filter fun m =>
    dirs true m = true ∧ sizes m - (hearts m).card = 1).card = 1 := by decide
example : ((range 2).filter fun m =>
    dirs false m = true ∧ sizes m - (hearts m).card = 1).card = 0 := by decide

-- The first B-step saturates its petal charge: four width-two petals for theta(2)=4.
example : 4 ≤ countingInsertionCount 2 (nodes true) sizes hearts (dirs true) 2 := by
  exact mul_card_counting_petalSteps_le θpos 2 (nodes true) sizes hearts (dirs true)
    (steps true) (fun i hi => (choices true i hi).1) rootReduced 2

example : countingInsertionCount 2 (nodes true) sizes hearts (dirs true) 2 = 4 := by decide

-- Unit-petal charges are valid too: the second B-step inserts two unit petals as well as its
-- negated-heart unit. Unit events from the earlier step remain part of the total.
example : 2 ≤ countingInsertionCount 2 (nodes true) sizes hearts (dirs true) 1 := by
  exact mul_card_counting_petalSteps_le θpos 2 (nodes true) sizes hearts (dirs true)
    (steps true) (fun i hi => (choices true i hi).1) rootReduced 1

-- Obtain a positive new-clause witness from the actual second step, then prove it has width one.
example : ∃ C ∈ countingIntro (nodes true 1) (sizes 1) (hearts 1) (dirs true 1) \
    (nodes true 1 ∪ nodes true 0), C.card = 1 := by
  obtain ⟨C, hC⟩ := counting_new_nonempty θpos 2 (nodes true) sizes hearts (dirs true)
    (steps true) (fun i hi => (choices true i hi).1) rootReduced (m := 1) (by decide)
  have hCI := (mem_sdiff.mp hC).1
  have hpos := card_pos.mpr (countingIntro_nonempty (choices true 1 (by decide)).1.1
    (choices true 1 (by decide)).1.2.1 hCI)
  have hlt := card_lt_of_mem_countingIntro (choices true 1 (by decide)).1 hCI
  change C.card < 2 at hlt
  exact ⟨C, hC, by omega⟩

example : 2 ≤ ∑ j ∈ Ico 1 3, countingInsertionCount 2 (nodes true) sizes hearts (dirs true) j := by
  exact counting_length_le_sum_insertions θpos 2 (nodes true) sizes hearts (dirs true)
    (steps true) (fun i hi => (choices true i hi).1) rootReduced (by decide)

example :
    (∑ j ∈ Ico 1 3, countingInsertionCount 2 (nodes true) sizes hearts (dirs true) j) = 8 := by
  decide

-- The preserved width is three, not two; this root-width premise is checked on the fixture.
example : ¬ ∀ C ∈ root, C.card ≤ 2 := by decide
example : ∀ C ∈ nodes true 2, C.card ≤ 3 := by
  exact card_le_counting_node θpos 2 (nodes true) sizes hearts (dirs true) (steps true)
    (fun i hi => (choices true i hi).1) (by decide) le_rfl

-- For k=3 and M=2 the source constants are C=28 and Gamma=16, rather than a coarser rate.
example : 2 ≤ 252 := by
  exact counting_length_le (M := 2) (by decide) 2 (nodes true) sizes hearts (dirs true)
    (steps true) (choices true) rootReduced rootNontautological (k := 3) (by decide) univ
    (by intro C hC l hl; exact mem_univ _)

example : 2 * ((range 2).filter fun m => dirs true m = true).card ≤ 144 := by
  exact mul_card_counting_B_le (M := 2) (by decide) 2 (nodes true) sizes hearts (dirs true)
    (steps true) (choices true) rootReduced rootNontautological (k := 3) (by decide) univ
    (by intro C hC l hl; exact mem_univ _)

example : 2 * ((range 2).filter fun m => dirs false m = true).card ≤ 144 := by
  exact mul_card_counting_B_le (M := 2) (by decide) 2 (nodes false) sizes hearts (dirs false)
    (steps false) (choices false) rootReduced rootNontautological (k := 3) (by decide) univ
    (by intro C hC l hl; exact mem_univ _)

example : 2 ≤ 280 ∧ 2 * ((range 2).filter fun m => dirs true m = true).card ≤ 160 := by
  exact counting_path_budgets_of_card_le (M := 2) (by decide) 2 (nodes true) sizes hearts
    (dirs true) (steps true) (choices true) rootReduced rootNontautological (k := 3)
    (by decide) univ (by intro C hC l hl; exact mem_univ _) (n := 10) (by decide)

/-- A root of two contradictory unit clauses cannot make even one legal branching step.
This derives zero length from the width-one bound; zero length is not a premise. -/
theorem unit_root_cannot_branch (N : ℕ) (ψ : ℕ → ClauseSet Unit) (c : ℕ → ℕ)
    (H : ℕ → Finset (Literal Unit)) (b : ℕ → Bool)
    (hroot : ψ 0 = {{((), true)}, {((), false)}})
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice (fun j => 2 ^ j) (ψ i) (c i) (H i)) : N = 0 := by
  have hbound := counting_length_le (M := 2) (by decide) N ψ c H b hstep hchoice
    (by rw [hroot]; unfold Reduced; decide) (by rw [hroot]; decide)
    (k := 1) (by rw [hroot]; decide) {()}
    (by intro C hC l hl; exact mem_singleton.mpr (Subsingleton.elim _ _))
  simpa using Nat.eq_zero_of_le_zero hbound

example : ∃ (ψ : ℕ → ClauseSet Unit), ψ 0 = {{((), true)}, {((), false)}} ∧
    (∀ i < 0, ψ (i + 1) = countingChild (ψ i) 2 {((), true)} true) ∧
    (∀ i < 0, Choice (fun j => 2 ^ j) (ψ i) 2 {((), true)}) :=
  ⟨fun _ => {{((), true)}, {((), false)}}, rfl, by simp, by simp⟩

-- At zero width and zero variables the same theorem forces zero steps, even with an empty
-- root clause. No ambient inhabitance or division by the declared-variable count is used.
example (N : ℕ) (ψ : ℕ → ClauseSet Empty) (c : ℕ → ℕ)
    (H : ℕ → Finset (Literal Empty)) (b : ℕ → Bool) (hroot : ψ 0 = {∅})
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hchoice : ∀ i < N, Choice (fun j => 2 ^ j) (ψ i) (c i) (H i)) : N = 0 := by
  have hbound := counting_path_budgets_of_card_le (M := 2) (by decide) N ψ c H b hstep hchoice
    (by rw [hroot]; unfold Reduced; decide) (by rw [hroot]; simp)
    (k := 0) (by rw [hroot]; simp) ∅ (by rw [hroot]; simp) (n := 0) (by simp)
  simpa using Nat.eq_zero_of_le_zero hbound.1

end ComplexityTests.SparsificationCountingPathBounds
