/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.BranchingVector
import CslibFrontier.Logics.Propositional.CNF.Branching
import CslibFrontier.Computability.Complexity.FineGrained.SchoeningMachine
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Tests for branching-vector recurrences, SAT branching rules, and multitape Schöning

Concrete nonvacuous checks exercising:
* `Cslib.BranchingVector.BranchingRecurrence` and `goldenBranchFactor` / `prefixBranchFactor` on
  Fibonacci-style recurrences,
* covering versus partitioning SAT branching rules (`not_partitionsModels_clauseCoverBranches_two`
  and `clausePrefixTree` exact model-count conservation and golden-ratio leaf bounds),
* `Cslib.Complexity.Schoening.exists_decidesWithBoundedErrorInTime_ThreeSAT` on concrete
  satisfiable and unsatisfiable `3`-CNF formulas over `ℕ`.
-/

namespace CslibFrontierTests.BranchingAndSchoening

open scoped ENNReal
open Cslib Cslib.BranchingVector Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.Schoening

/-! ### 1. Generic branching-vector recurrence on a concrete Fibonacci sequence -/

def fibRec : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => fibRec (n + 1) + fibRec n

theorem fibRec_le_goldenBranchFactor_pow (n : ℕ) :
    (fibRec n : ℝ) ≤ goldenBranchFactor ^ n := by
  have hrec : BranchingRecurrence (fun m => (fibRec m : ℝ)) [1, 2] 1 :=
    BranchingRecurrence.of_step zero_le_one (by decide)
      (fun m => by
        rcases m with _ | _ | k
        · simp only [fibRec, Nat.cast_one, le_max_iff, le_refl, true_or]
        · simp only [fibRec, Nat.cast_one, le_max_iff, le_refl, true_or]
        · have hfilt : List.filter (· ≤ k + 2) [1, 2] = [1, 2] := by
            simp only [List.filter_cons, decide_eq_true_eq]
            have h1 : 1 ≤ k + 2 := by omega
            have h2 : 2 ≤ k + 2 := by omega
            simp only [h1, h2, ↓reduceIte, List.filter_nil]
          rw [hfilt]
          simp only [fibRec, List.map_cons, List.map_nil, show k + 1 + 1 - 1 = k + 1 by omega,
            show k + 1 + 1 - 2 = k by omega, List.sum_cons, List.sum_nil, add_zero, Nat.cast_add,
            le_max_iff]
          exact Or.inr le_rfl)
  exact hrec.le_pow one_lt_goldenBranchFactor.le charSum_fibonacci.le n

def skippedRec : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | n + 3 => skippedRec (n + 1) + skippedRec n

theorem skippedRec_le_pow (n : ℕ) :
    (skippedRec n : ℝ) ≤ (2 : ℝ) ^ n := by
  have hrec : BranchingRecurrence (fun m => (skippedRec m : ℝ)) [2, 3] 1 :=
    BranchingRecurrence.of_step zero_le_one (by decide)
      (fun m => by
        rcases m with _ | _ | _ | k
        · simp only [skippedRec, Nat.cast_one, le_max_iff, le_refl, true_or]
        · simp only [skippedRec, Nat.cast_one, le_max_iff, le_refl, true_or]
        · simp only [skippedRec, Nat.cast_one, le_max_iff, le_refl, true_or]
        · have hfilt : List.filter (· ≤ k + 3) [2, 3] = [2, 3] := by
            have h2 : 2 ≤ k + 3 := by omega
            have h3 : 3 ≤ k + 3 := by omega
            simp [h2, h3]
          rw [hfilt]
          simp only [skippedRec, List.map_cons, List.map_nil, show k + 2 + 1 - 2 = k + 1 by omega,
            show k + 2 + 1 - 3 = k by omega, List.sum_cons, List.sum_nil, add_zero, Nat.cast_add,
            le_max_iff]
          exact Or.inr le_rfl)
  exact hrec.le_pow one_le_two (by norm_num [charSum]) n

theorem prefixBranchFactor_three_eq : prefixBranchFactor 3 = (15 / 8 : ℝ) := by
  unfold prefixBranchFactor
  norm_num

/-! ### 2. Covering vs partitioning SAT branching and `2`-CNF golden-ratio tree bound -/

theorem cover_not_partition_fin3 :
    let c : Clause (Fin 3) := [(0, true), (1, true)]
    ¬ CNF.PartitionsModels [c] (CNF.clauseCoverBranches c [c]) :=
  CNF.not_partitionsModels_clauseCoverBranches_two (by decide)

def sampleTwoCNF : CNF (Fin 3) :=
  [[(0, true), (1, true)], [(1, false), (2, true)]]

theorem sampleTwoCNF_tree_bounds :
    let init : CNF.ClauseBranchState (Fin 3) :=
      { unassigned := Finset.univ, formula := sampleTwoCNF }
    let tree := CNF.clausePrefixTree 2 (V := Fin 3)
    sampleTwoCNF.modelCountOn Finset.univ =
        ((tree.leaves init).map fun lf =>
          if [] ∈ lf.formula then 0 else 2 ^ lf.unassigned.card).sum ∧
      ((tree.leafCount init : ℝ) ≤ goldenBranchFactor ^ 3) := by
  intro init tree
  have hwidth : ∀ c ∈ sampleTwoCNF, c.length ≤ 2 := by decide
  have hvars : sampleTwoCNF.vars.toFinset ⊆ Finset.univ := Finset.subset_univ _
  refine ⟨CNF.modelCountOn_eq_sum_clausePrefixTree_leaves hwidth hvars, ?_⟩
  simpa only [init, Finset.card_univ, Fintype.card_fin] using
    CNF.leafCount_clausePrefixTree_two_le init

/-! ### 3. Nonvacuous multitape Schöning `3`-SAT decider on concrete formulas -/

def satThreeCNF : CNF ℕ :=
  [[(0, true), (1, false), (2, true)], [(0, false), (1, true), (2, true)]]

def unsatThreeCNF : CNF ℕ :=
  [[(0, true)], [(0, false)]]

theorem satThreeCNF_mem_ThreeSAT : satThreeCNF ∈ ThreeSAT := by
  refine ⟨by decide, ⟨fun _ => true, ?_⟩⟩
  decide

theorem unsatThreeCNF_not_mem_ThreeSAT : unsatThreeCNF ∉ ThreeSAT := by
  rintro ⟨_, σ, hσ⟩
  simp only [unsatThreeCNF, CNF.eval_cons, CNF.eval_nil, Clause.eval_cons, Clause.eval_nil,
    Literal.eval, Bool.or_false, Bool.and_true, Bool.and_eq_true] at hσ
  rcases hσ with ⟨h0t, h0f⟩
  cases σ 0 <;> simp_all

theorem schoening_multitape_concrete_threeSAT :
    ∃ (K : ℕ) (Control : Type) (_ : Finite Control)
      (machine : Turing.MultiTapePTM K Bool Control) (T : CNF ℕ → ℕ) (C E : ℕ),
      (2 / 3 : ℝ≥0∞) ≤
          ProbComp.eval (machine.runClosed (T satThreeCNF) (encCNF satThreeCNF)) [true] ∧
        ProbComp.eval (machine.runClosed (T unsatThreeCNF) (encCNF unsatThreeCNF)) =
          PMF.pure [false] ∧
        ((T satThreeCNF : ℝ) ≤
          (C : ℝ) * ((4 / 3 : ℝ) ^ satThreeCNF.numVars *
            ((encCNF satThreeCNF).length + 1 : ℝ) ^ E)) ∧
        machine.toNTM.RunsInSpace (encCNF satThreeCNF)
          (C * ((encCNF satThreeCNF).length + 1) ^ E) := by
  obtain ⟨K, Control, hfin, machine, T, C, E, hdec, hbounds⟩ :=
    exists_decidesWithBoundedErrorInTime_ThreeSAT
  refine ⟨K, Control, hfin, machine, T, C, E, ?_, ?_, ?_, ?_⟩
  · have hsat := (hdec satThreeCNF).2
    have hind : Turing.MultiTapeTM.indicator ThreeSAT satThreeCNF = true := by
      unfold Turing.MultiTapeTM.indicator
      split_ifs with h
      · rfl
      · exact absurd satThreeCNF_mem_ThreeSAT h
    rwa [hind] at hsat
  · exact (hbounds unsatThreeCNF).2.2 unsatThreeCNF_not_mem_ThreeSAT
  · exact (hbounds satThreeCNF).1
  · exact (hbounds satThreeCNF).2.1

end CslibFrontierTests.BranchingAndSchoening
