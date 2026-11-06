/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.FullCover
import Mathlib.Tactic

/-!
# Feasibility of stopped oracle executions

Every positive-probability execution of a feasible full-cover policy is contained
slot by slot in some possible all-failure schedule. Thus stopping early preserves
the no-reuse condition and cannot increase the sum of allotted batch durations.
This justifies the nontruncating deadline and turn interpretation in [Wang2027],
Section 4 and Theorem 1, PDF pp. 6–7.

## Main results

* `execution_feasible`: every supported stopped trace satisfies the deadline contract.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle
open Finset Cslib.Optimization.OneConstraint
variable {ι K : Type} [Fintype ι]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Each issued batch is contained in the corresponding all-failure batch. -/
@[expose] def Plan.Subplan : {n : ℕ} → Plan ι n → Plan ι n → Prop
  | 0, _, _ => True
  | _+1, (A,C), (B,D) => A ⊆ B ∧ C.Subplan D

omit [Fintype ι] in
private theorem empty_subplan {n : ℕ} (B : Plan ι n) : (Plan.empty n).Subplan B := by
  induction n with
  | zero => trivial
  | succ n ih => rcases B with ⟨A,B⟩; exact ⟨empty_subset _,ih B⟩

/-- Every supported stopped trace lies inside a supported all-failure schedule. -/
theorem execution_subplan (I : FullCoverInstance ι K) {n : ℕ} (π : Policy ι K n)
    (e : Bool × Plan ι n) (he : e ∈ (π.execution I).support) :
    ∃ B ∈ π.scheduleLaw.support, e.2.Subplan B := by
  induction π with
  | halt n =>
    rw [Policy.execution, Distribution.mem_support_pure] at he
    subst e
    exact ⟨Plan.empty n, (Distribution.mem_support_pure _ _).mpr rfl, empty_subplan _⟩
  | @issue n A π ih =>
    rw [Policy.execution, Distribution.mem_support_bind] at he
    obtain ⟨b,_,he⟩ := he
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at he
      obtain ⟨e',he',rfl⟩ := (Distribution.mem_support_map _ _ _).mp he
      obtain ⟨B,hB,hsub⟩ := ih e' he'
      refine ⟨(A,B),?_,Subset.rfl,hsub⟩
      exact (Distribution.mem_support_map _ _ _).mpr ⟨B,hB,rfl⟩
    · simp only [↓reduceIte, Distribution.mem_support_pure] at he
      subst e
      obtain ⟨B,hB⟩ := π.scheduleLaw.support_nonempty
      refine ⟨(A,B),?_,Subset.rfl,empty_subplan B⟩
      exact (Distribution.mem_support_map _ _ _).mpr ⟨B,hB,rfl⟩
  | random w next ih =>
    obtain ⟨i,hi,he⟩ := (Distribution.mem_support_bind _ _ _).mp he
    obtain ⟨B,hB,hsub⟩ := ih i e he
    exact ⟨B,(Distribution.mem_support_bind _ _ _).mpr ⟨i,hi,hB⟩,hsub⟩

omit [Fintype ι] [IsStrictOrderedRing K] in
/-- Inclusion of batches implies inclusion of used call opportunities. -/
theorem Plan.used_subset_of_subplan {n : ℕ} (C B : Plan ι n) (h : C.Subplan B) :
    C.used ⊆ B.used := by
  classical
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
    rcases C with ⟨A,C⟩
    rcases B with ⟨B,D⟩
    exact union_subset_union h.1 (ih C D h.2)

omit [Fintype ι] in
/-- Deleting calls or stopping early preserves the nontruncating deadline contract. -/
theorem Plan.feasible_of_subplan (I : FullCoverInstance ι K) {n : ℕ}
    (C B : Plan ι n) (h : C.Subplan B) (D : K) (hB : B.Feasible I D) :
    C.Feasible I D := by
  classical
  have hm : ∀ A B : Finset ι, A ⊆ B → I.batchDuration A ≤ I.batchDuration B := by
    intro A B hAB
    exact max'_subset (by simp) (insert_subset_insert _ (image_subset_image hAB))
  have haux : ∀ {n : ℕ} (C B : Plan ι n), C.Subplan B → B.NoReuse →
      C.NoReuse ∧ C.duration I ≤ B.duration I := by
    intro n C B h hB
    induction n with
    | zero => exact ⟨trivial,le_rfl⟩
    | succ n ih =>
      rcases C with ⟨A,C⟩
      rcases B with ⟨B,E⟩
      obtain ⟨hC,hDur⟩ := ih C E h.2 hB.2
      exact ⟨⟨hB.1.mono h.1 (Plan.used_subset_of_subplan C E h.2),hC⟩,
        add_le_add (hm A B h.1) hDur⟩
  obtain ⟨hC,hDur⟩ := haux C B h hB.1
  exact ⟨hC,hDur.trans hB.2⟩

/-- Every actual execution, including one that stops early on success, obeys the
prescribed cutoff deadline, single-use contract and number-of-slots turn bound. -/
theorem execution_feasible (I : FullCoverInstance ι K) {n : ℕ} (π : Policy ι K n)
    (D : K) (hπ : π.Feasible I D) (e : Bool × Plan ι n)
    (he : e ∈ (π.execution I).support) : e.2.Feasible I D := by
  obtain ⟨B,hB,hsub⟩ := execution_subplan I π e he
  exact Plan.feasible_of_subplan I _ B hsub D (hπ B hB)

end Cslib.Probability.StochasticOracle
