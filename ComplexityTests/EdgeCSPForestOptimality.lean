/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import Complexity.Algorithms.Lean.EdgeCSP.Forest.Optimality
import Complexity.Foundations.Data.BitString.DeltaMatroid.ExchangeBound
import Mathlib.Tactic.FinCases

/-! Fresh exhausted-search optimality, including obstructed reachability and sparse names. -/

namespace ComplexityTests.EdgeCSPForestOptimality

open Cslib Cslib.BitString Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Logic.PL.CSP.Forest Finset

private def tableSem (r : List (List Bool)) (x : List Bool) : Bool := r.contains x

-- The feasible-pair graph at 000 is the connected path 0--1--2. The pinned tuple 101 is
-- nevertheless infeasible: reaching a coordinate is insufficient for augmentation.
private abbrev pathInstance : CSP (List (List Bool)) ℕ :=
  [([[false, false, false], [true, true, false], [false, true, true]],
      [2 ^ 100, 2 ^ 200, 2 ^ 250]),
    ([[true]], [2 ^ 100]), ([[false]], [2 ^ 200]), ([[true]], [2 ^ 250])]

private def pathLabels : pathInstance.OccurrenceLabeling Bool :=
  fun o => o.1.val == 1 || o.1.val == 3

private theorem path_edge : EdgeInstance pathInstance := by unfold EdgeInstance; decide
private theorem path_valid : ValidLabeling tableSem pathLabels := by
  unfold ValidLabeling
  decide

private theorem path_even : EdgeInstance.EvenConstraints tableSem pathInstance := by
  intro i
  fin_cases i
  all_goals
    constructor
    · constructor <;> simp only [Set.Nonempty, Set.mem_ofPred_eq] <;> decide
    · simp only [Set.mem_ofPred_eq]
      decide

private def pathLog : Log pathInstance :=
  match search tableSem pathLabels with
  | .exhausted es => es
  | _ => []

private theorem path_exhausted : search tableSem pathLabels = .exhausted pathLog := by
  decide +kernel

example : (defects pathLabels).card = 2 := by decide
example : pathLog.used.length = 6 ∧ pathLog.outgoing.length = 1 := by decide +kernel
example : IsOptimalLabeling tableSem pathLabels :=
  search_exhausted_isOptimalLabeling tableSem pathLabels path_edge path_valid path_even
    path_exhausted

-- Both nontrivial feasible moves enter the middle coordinate; the counting lemma does not
-- confuse their connected pair graph with arbitrary feasible simultaneous changes.
private abbrev pathRelation : Set (Fin 3 → Bool) :=
  {x | tableSem [[false, false, false], [true, true, false], [false, true, true]]
    (List.ofFn x) = true}

example : flipOn {0, 1} (fun _ => false) ∈ pathRelation ∧
    flipOn {1, 2} (fun _ => false) ∈ pathRelation ∧
    flipOn {0, 2} (fun _ => false) ∉ pathRelation := by decide

example {y : Fin 3 → Bool} (hy : y ∈ pathRelation) :
    (({0, 2} : Finset (Fin 3)).filter fun i => (false : Bool) ≠ y i).card ≤
      (({1} : Finset (Fin 3)).filter fun i => (false : Bool) ≠ y i).card := by
  have he : IsEvenDeltaMatroid pathRelation := path_even 0
  exact he.card_disagree_le (by decide) hy _ _ (by decide) (by decide)

-- Odd local parity is permitted: the binary relation has tuples 10 and 01, whereas both
-- unary endpoints are pinned to zero. One defect is unavoidable.
private abbrev oddInstance : CSP (List (List Bool)) ℕ :=
  [([[true, false], [false, true]], [7, 2 ^ 240]),
    ([[false]], [7]), ([[false]], [2 ^ 240])]

private def oddLabels : oddInstance.OccurrenceLabeling Bool :=
  fun o => o.1.val == 0 && o.2.val == 0

private theorem odd_edge : EdgeInstance oddInstance := by unfold EdgeInstance; decide
private theorem odd_valid : ValidLabeling tableSem oddLabels := by
  unfold ValidLabeling
  decide

private theorem odd_even : EdgeInstance.EvenConstraints tableSem oddInstance := by
  intro i
  fin_cases i
  all_goals
    constructor
    · constructor <;> simp only [Set.Nonempty, Set.mem_ofPred_eq] <;> decide
    · simp only [Set.mem_ofPred_eq]
      decide

private def oddLog : Log oddInstance :=
  match search tableSem oddLabels with
  | .exhausted es => es
  | _ => []

example : (defects oddLabels).card = 1 := by decide
example : IsOptimalLabeling tableSem oddLabels := by
  apply search_exhausted_isOptimalLabeling tableSem oddLabels odd_edge odd_valid odd_even
    (es := oddLog)
  decide +kernel

private abbrev emptyInstance : CSP Unit ℕ := []

example : IsOptimalLabeling (fun _ _ => false)
    (F := emptyInstance) (fun _ => false) := by
  apply search_exhausted_isOptimalLabeling (es := [])
  · intro o
    exact Fin.elim0 o.1
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i
  · decide +kernel

-- Fresh search can exhaust even when its base labeling violates a nullary constraint.
-- This prevents dropping validity from the optimality endpoint.
private abbrev rejected : CSP Unit ℕ := [((), [])]

example : search (fun _ _ => false) (F := rejected) (fun _ => false) = .exhausted [] := by
  decide +kernel

example : ¬ IsOptimalLabeling (fun _ _ => false) (F := rejected) (fun _ => false) := by
  intro h
  have hv := h.1 (0 : Fin rejected.length)
  contradiction

end ComplexityTests.EdgeCSPForestOptimality
