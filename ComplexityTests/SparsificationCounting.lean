/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Counting
import Complexity.Logics.Propositional.ClauseSet.Sparsification.Path

public section

open Cslib.Logic.PL
open ClauseSet.Sparsification

namespace ComplexityTests.SparsificationCounting

-- Avoid choosing an order for toCNF: count its assignments using the existing semantic bridge.
private theorem count_eq_card {V : Type*} [DecidableEq V]
    (ψ : ClauseSet V) (s : Finset V) :
    ψ.toCNF.modelCountOn s = (Finset.univ.filter fun σ : s → Bool =>
      ψ.Sat (fun v => if h : v ∈ s then σ ⟨v, h⟩ else false)).card := by
  unfold CNF.modelCountOn
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ClauseSet.eval_toCNF_eq_true_iff]

private def parent : ClauseSet (Fin 3) :=
  {{(0, true), (1, true)}, {(0, true), (2, true)}}

private def heart : Finset (Literal (Fin 3)) := {(0, true)}

-- Five satisfying assignments, including the four with x=true.
example : parent.toCNF.modelCountOn Finset.univ = 5 := by
  rw [count_eq_card]
  decide

-- The old decision branches overlap at x=y=z=true, so their counts must not simply be added.
example : (child parent 2 heart false).toCNF.modelCountOn Finset.univ = 4 := by
  rw [count_eq_card]
  decide

example : (child parent 2 heart true).toCNF.modelCountOn Finset.univ = 2 := by
  rw [count_eq_card]
  decide

example : (child parent 2 heart false).Sat (fun _ => true) ∧
    (child parent 2 heart true).Sat (fun _ => true) := by decide

-- The explicit negated-heart unit removes precisely that overlap.
example : (countingChild parent 2 heart false).toCNF.modelCountOn Finset.univ = 4 := by
  rw [count_eq_card]
  decide

example : (countingChild parent 2 heart true).toCNF.modelCountOn Finset.univ = 1 := by
  rw [count_eq_card]
  decide

example : ¬ (countingChild parent 2 heart true).Sat (fun _ => true) := by decide

example : parent.toCNF.modelCountOn Finset.univ =
    (countingChild parent 2 heart false).toCNF.modelCountOn Finset.univ +
    (countingChild parent 2 heart true).toCNF.modelCountOn Finset.univ :=
  modelCountOn_countingChild parent 2 heart Finset.univ

-- A fourth declared variable remains free in every branch, even though it never occurs.
private def parentFour : ClauseSet (Fin 4) :=
  {{(0, true), (1, true)}, {(0, true), (2, true)}}

example : parentFour.toCNF.modelCountOn Finset.univ = 10 := by
  rw [count_eq_card]
  decide

example : (countingChild parentFour 2 {(0, true)} false).toCNF.modelCountOn Finset.univ = 8 := by
  rw [count_eq_card]
  decide

example : (countingChild parentFour 2 {(0, true)} true).toCNF.modelCountOn Finset.univ = 2 := by
  rw [count_eq_card]
  decide

-- With the parent AND heart support hypotheses, the unused fourth variable is not introduced.
example : ∀ C ∈ countingChild parentFour 2 {(0, true)} true,
    ∀ l ∈ C, l.1 ∈ ({0, 1, 2} : Finset (Fin 4)) :=
  support_countingChild parentFour 2 {(0, true)} {0, 1, 2} (by decide) (by decide) true

-- Parent support alone cannot control an arbitrary heart: its negated units may add a variable.
example : ¬ (∀ C ∈ countingChild (∅ : ClauseSet (Fin 1)) 1 {(0, true)} true,
    ∀ l ∈ C, l.1 ∈ (∅ : Finset (Fin 1))) := by decide

-- Empty variable type and empty heart require no inhabitance or heavy-heart assumption.
example : (countingChild (∅ : ClauseSet Empty) 0 ∅ false).toCNF.modelCountOn ∅ = 0 := by
  rw [count_eq_card]
  decide

theorem empty_count :
    (countingChild (∅ : ClauseSet Empty) 0 ∅ true).toCNF.modelCountOn ∅ = 1 := by
  rw [count_eq_card]
  decide

-- A contradictory heart is always satisfied; its negated units cannot both hold.
example : (countingChild parent 2 {(0, true), (0, false)} false).toCNF.modelCountOn
    Finset.univ = 5 := by
  rw [count_eq_card]
  decide

example : (countingChild parent 2 {(0, true), (0, false)} true).toCNF.modelCountOn
    Finset.univ = 0 := by
  rw [count_eq_card]
  decide

-- A pre-existing negated unit remains a single set clause after refinement and reduction.
example : countingChild (insert {(0, false)} parent) 2 heart true =
    ({ {(0, false)}, {(1, true)}, {(2, true)} } : ClauseSet (Fin 3)) := by decide

-- The new negated unit need not refine any old clause; old Refines bounds do not apply.
example : ¬ Refines (countingChild parent 2 heart true) parent := by
  unfold Refines
  decide

-- Repetition in a list presentation does not create extra models or erase declared variables.
example :
    (CNF.toClauseSet ([[(0, true), (1, true)], [(0, true), (1, true)],
      [(0, true), (2, true)]] : CNF (Fin 3))).toCNF.modelCountOn Finset.univ = 5 := by
  rw [count_eq_card]
  decide

end ComplexityTests.SparsificationCounting
