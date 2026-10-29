/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.DecisionTree.Composition
import Complexity.Computability.DecisionTree.Parity
import Mathlib.Data.Fintype.BigOperators

/-! Tests of decision-tree composition on parity of disjoint conjunctions. -/

namespace ComplexityTests.DecisionTreeComposition

open Cslib Cslib.DecisionTree Finset

/-- The parity of conjunctions on disjoint blocks, including blocks of different sizes. -/
private def parityAnd {ι : Type*} [Fintype ι] (κ : ι → Type*) [∀ i, Fintype (κ i)]
    (x : (Σ i, κ i) → Bool) : Bool :=
  parityOn univ fun i => decide (∀ j : κ i, x ⟨i, j⟩ = true)

/-- Every coordinate is sensitive at the all-true input, so the number of variables is sharp.
This supplies a lower bound independent of the composition construction. -/
private theorem complexity_parityAnd {ι : Type*} [Fintype ι] (κ : ι → Type*)
    [∀ i, Fintype (κ i)] :
    complexity (parityAnd κ) = ∑ i, Fintype.card (κ i) := by
  classical
  rw [← Fintype.card_sigma]
  apply complexity_eq_card_of_forall_update_ne (x := fun _ => true)
  intro p
  have hblocks :
      (fun i => decide (∀ j : κ i,
        Function.update (fun _ : Σ i, κ i => true) p false ⟨i, j⟩ = true)) =
      Function.update (fun _ : ι => true) p.1 false := by
    funext i
    by_cases hi : i = p.1
    · subst i
      rw [Function.update_self, decide_eq_false_iff_not]
      intro h
      have hfalse := h p.2
      rw [Function.update_self] at hfalse
      cases hfalse
    · rw [Function.update_of_ne hi]
      apply decide_eq_true
      intro j
      exact Function.update_of_ne (fun h => hi (congrArg Sigma.fst h)) _ _
  have htrue : (fun i : ι => decide (∀ _j : κ i, true = true)) = fun _ : ι => true := by
    funext i
    exact decide_eq_true fun _ => rfl
  change parityOn univ (fun i => decide (∀ j : κ i,
      Function.update (fun _ : Σ i, κ i => true) p false ⟨i, j⟩ = true)) ≠
    parityOn univ (fun i => decide (∀ _j : κ i, true = true))
  rw [hblocks, htrue]
  change parityOn univ (Function.update (fun _ : ι => true) p.1 (!true)) ≠
    parityOn univ (fun _ : ι => true)
  rw [parityOn_update_not (mem_univ p.1)]
  cases parityOn univ (fun _ : ι => true) <;> decide

-- The new block-composition rule constructs the matching uniform upper bound.
example (m n : ℕ) : complexity (parityAnd (fun _ : Fin m => Fin n)) ≤ m * n := by
  have h := complexity_blockCompose_le_mul (parity m)
    (fun _ : Fin m => fun x : Fin n → Bool => decide (∀ j, x j = true)) (d := n)
    (fun _ => (complexity_le_card _).trans_eq (Fintype.card_fin n))
  rw [complexity_parity] at h
  convert h using 2
  funext x
  unfold parityAnd parity
  congr 1
  funext i
  exact decide_eq_decide.mpr Iff.rfl

-- A nontrivial composition has exactly six queries in the worst case.
example : complexity (parityAnd (fun _ : Fin 2 => Fin 3)) = 6 := by
  rw [complexity_parityAnd]
  norm_num

-- Dependent blocks of sizes 1, 2, and 3 have the same total cost.
example : complexity (parityAnd (fun i : Fin 3 => Fin (i.val + 1))) = 6 := by
  rw [complexity_parityAnd]
  norm_num [Fin.sum_univ_succ]

example : parityAnd (fun _ : Fin 2 => Fin 3) (fun _ => true) = false := by decide

example : parityAnd (fun _ : Fin 2 => Fin 3)
    (Function.update (fun _ => true) ⟨0, 0⟩ false) = true := by decide

-- Both an empty outer input and empty inner blocks give a constant function.
example : complexity (parityAnd (fun _ : Fin 0 => Fin 3)) = 0 := by
  rw [complexity_parityAnd]
  simp

example : complexity (parityAnd (fun _ : Fin 3 => Fin 0)) = 0 := by
  rw [complexity_parityAnd]
  simp

/-! ### Heterogeneous costs and adaptive execution -/

private def query (i : Fin 5) : DecisionTree (Fin 5) Bool :=
  .node i (.leaf false) (.leaf true)

private def selector : DecisionTree (Fin 3) Bool :=
  .node 0 (.node 1 (.leaf false) (.leaf true)) (.node 2 (.leaf false) (.leaf true))

private def subroutine : Fin 3 → DecisionTree (Fin 5) Bool
  | 0 => query 0
  | 1 => query 1
  | 2 => .node 2 (.leaf false) (.node 3 (.leaf false) (query 4))

-- Charging the three subroutines separately gives 4, while depth times maximum cost gives 6.
example : (selector.substitute subroutine).depth ≤ 4 := by
  calc
    (selector.substitute subroutine).depth ≤
        selector.weightedDepth (fun i => (subroutine i).depth) :=
      selector.depth_substitute_le subroutine
    _ = 4 := by decide

example : selector.depth * 3 = 6 := by decide

example : ∀ x : Fin 5 → Bool, (selector.substitute subroutine).eval x =
    if x 0 then x 2 && x 3 && x 4 else x 1 := by decide

-- The same compiled tree has different execution costs on its short and long branches.
example : (selector.substitute subroutine).cost (fun _ => false) = 2 := by decide

example : (selector.substitute subroutine).cost (fun _ => true) = 4 := by decide

example : (selector.substitute subroutine).cost
    (Function.update (fun _ => true) 2 false) = 2 := by decide

-- Zero-cost constants select a continuation without issuing any query.
example : (selector.substitute (fun _ => .leaf false : Fin 3 → DecisionTree (Fin 5) Bool)).depth =
    0 := by decide

/-! ### Shared variables and unreachable structural paths -/

private def xorTree : DecisionTree Bool Bool :=
  .node false (.node true (.leaf false) (.leaf true))
    (.node true (.leaf true) (.leaf false))

private def sharedQuery (_ : Bool) : DecisionTree Unit Bool :=
  .node () (.leaf false) (.leaf true)

-- Replacing both XOR inputs by the same bit gives a constant function, while executing two
-- queries. This rules out interpreting substitution as memoization or its bound as equality.
example : ∀ x : Unit → Bool,
    (xorTree.substitute sharedQuery).eval x = false ∧
      (xorTree.substitute sharedQuery).cost x = 2 := by decide

example : complexity (fun x => (xorTree.substitute sharedQuery).eval x) = 0 := by
  apply complexity_eq_zero_iff.mpr
  intro x y
  simp only [eval_substitute]
  cases hx : x () <;> cases hy : y () <;>
    simp [xorTree, sharedQuery, hx, hy]

private def unreachable : DecisionTree Unit Bool :=
  .node () (.leaf false)
    (.node () (.node () (.leaf false) (.leaf true)) (.leaf true))

-- The depth-three structural path asks the same bit for inconsistent answers.
example : unreachable.depth = 3 ∧ ∀ x : Unit → Bool, unreachable.cost x ≤ 2 := by decide

end ComplexityTests.DecisionTreeComposition
