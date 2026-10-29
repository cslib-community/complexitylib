/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingUnits

public section

open Cslib.Logic.PL
open ClauseSet.Sparsification Finset

namespace ComplexityTests.SparsificationCountingUnits

-- The no-empty-clause hypothesis is essential for immediate survival.
theorem empty_clause_drops_new_unit :
    countingChild ({∅} : ClauseSet (Fin 1)) 2 {(0, true)} false = {∅} := by decide

example : (countingUnitInsertions ({∅} : ClauseSet (Fin 1)) 2 {(0, true)} false).card = 1 := by
  decide

private def root : ClauseSet (Fin 5) :=
  {{(0, true), (1, true)}, {(0, true), (2, true)}, {(0, true), (3, true), (4, true)}}

private def heart : Finset (Literal (Fin 5)) := {(0, true)}

private def middle := countingChild root 2 heart true

private def nodes (i : ℕ) : ClauseSet (Fin 5) :=
  if i = 0 then root else if i = 1 then middle else countingChild middle 3 heart true

private def sizes (i : ℕ) : ℕ := if i = 0 then 2 else 3

-- The first B step inserts y, z and not-x. The second payload mentions not-x AGAIN.
example : countingUnitInsertions root 2 heart true =
    ({ {(1, true)}, {(2, true)}, {(0, false)} } : ClauseSet (Fin 5)) := by decide

example : ((countingIntro middle 3 heart true).filter fun C => C.card = 1).card = 1 := by
  decide

-- Its negated-heart unit is already present, so the second step has no new unit event.
example : countingUnitInsertions middle 3 heart true = ∅ := by decide

example : (∑ i ∈ range 2, (countingUnitInsertions (nodes i) (sizes i) heart true).card) = 3 := by
  decide

example : ((nodes 2).filter fun C => C.card = 1).card = 3 := by decide

-- Exercise the actual path budget on any legal counting path starting from `root`: total unit
-- insertions across all `N` steps are bounded by `2 * 5 = 10`.
example (N : ℕ) (ψ : ℕ → ClauseSet (Fin 5)) (c : ℕ → ℕ)
    (H : ℕ → Finset (Literal (Fin 5))) (b : ℕ → Bool) (hroot : ψ 0 = root)
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy (fun _ => 1) (ψ i) (c i) (H i)) :
    (∑ i ∈ range N, (countingUnitInsertions (ψ i) (c i) (H i) (b i)).card) ≤ 10 := by
  have hred : Reduced (ψ 0) := by rw [hroot]; unfold Reduced; decide
  have h := sum_countingUnitInsertions_le (θ := fun _ => 1) (by intro; decide)
    N ψ c H b hstep hheavy hred univ (by intro C _ l _; exact mem_univ _)
  simpa using h

-- Exercise the actual path budget, with both proper heavy steps checked and root support charged.
example : (∑ i ∈ range 2, (countingUnitInsertions (nodes i) (sizes i) heart true).card) ≤ 10 := by
  have hstep : ∀ i < 2, nodes (i + 1) = countingChild (nodes i) (sizes i) heart true := by
    intro i hi
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> rfl
  have hheavy : ∀ i < 2, Heavy (fun _ => 1) (nodes i) (sizes i) heart := by
    intro i hi
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> unfold Heavy <;> decide
  have hred : Reduced (nodes 0) := by unfold Reduced; decide
  have h := sum_countingUnitInsertions_le (θ := fun _ => 1) (by intro; decide)
    2 nodes sizes (fun _ => heart) (fun _ => true) hstep hheavy hred univ
    (by intro C hC l hl; exact mem_univ _)
  simpa using h

-- A second A step may create the opposite unit; neither signed unit is deleted.
example : countingUnitInsertions middle 3 heart false =
    ({ {(0, true)} } : ClauseSet (Fin 5)) := by decide

example : {(0, false)} ∈ countingChild middle 3 heart false ∧
    {(0, true)} ∈ countingChild middle 3 heart false := by decide

-- Initial units are not charged again, including a negated-heart unit already present at the root.
example : (countingUnitInsertions (insert {(0, false)} root) 2 heart true).card = 2 := by decide

example : ((countingChild (insert {(0, false)} root) 2 heart true).filter
    fun C => C.card = 1).card = 3 := by decide

-- The empty variable type and an empty root clause force `0` unit insertions along any path.
example (N : ℕ) (ψ : ℕ → ClauseSet Empty) (c : ℕ → ℕ)
    (H : ℕ → Finset (Literal Empty)) (b : ℕ → Bool) (hroot : ψ 0 = {∅})
    (hstep : ∀ i < N, ψ (i + 1) = countingChild (ψ i) (c i) (H i) (b i))
    (hheavy : ∀ i < N, Heavy (fun _ => 1) (ψ i) (c i) (H i)) :
    (∑ i ∈ range N, (countingUnitInsertions (ψ i) (c i) (H i) (b i)).card) = 0 := by
  have h := sum_countingUnitInsertions_le (θ := fun _ => 1) (by intro; decide)
    N ψ c H b hstep hheavy (by rw [hroot]; simp [Reduced]) ∅ (by rw [hroot]; simp)
  simpa using Nat.eq_zero_of_le_zero h

-- No nontautology assumption is needed for units: the petal and negated unit may coincide.
example : countingUnitInsertions ({{(0, true), (0, false)}} : ClauseSet (Fin 1))
    2 {(0, true)} true = {{(0, false)}} := by decide

-- Without root support in the declared set, the claimed numerical budget would be false.
example : ¬ (countingUnitInsertions ({{(0, true), (0, false)}} : ClauseSet (Fin 1))
    2 {(0, true)} false).card ≤ 2 * (∅ : Finset (Fin 1)).card := by decide

end ComplexityTests.SparsificationCountingUnits
