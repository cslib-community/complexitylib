/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BinaryBranching
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Path
import Mathlib.Data.Nat.Find
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Sparsification -- the branching tree

A *branching rule* (`BranchingRule`) makes the procedure deterministic: it is a step on states
that represent clause sets, which at every state that is not sparse takes the heart (`false`) or
the petal (`true`) child for one valid choice. Any valid choice will do, so a rule may compute its
choice, and its states may be any representation of clause sets. The canonical rule
(`chooseRule`) works on clause sets themselves, with a valid choice made by `chooseBranch`.

The tree of a rule (`BranchingRule.tree`) is the binary branching whose leaves are the sparse
states; its words, node words and leaf words are those of `Cslib.BinaryBranching`. Each step
decreases the potential, so the tree terminates (`BranchingRule.tree_terminating`). Every leaf
word yields a `Path` with the same length and the same petal steps (`exists_path_of_isLeafWord`),
and every solution of the root reaches a leaf containing it (`exists_isLeafWord_sat`).

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule`: a deterministic branching step.
* `Cslib.Logic.PL.ClauseSet.Sparsification.chooseRule`: the canonical rule on clause sets.
* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.tree`: the branching tree of a rule.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.tree_terminating`: the tree terminates.
* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.exists_isLeafWord_sat_iff`: a state is
  satisfiable exactly when one of its leaves is.
* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.exists_path_of_isLeafWord`: leaf words are
  branches.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
* [C. Calabro, *The Exponential Complexity of Satisfiability Problems*][Calabro2009]
-/
@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V] {θ : ℕ → ℕ}

/-- A clause set that is not sparse has a valid branching choice. -/
theorem exists_choice (θ : ℕ → ℕ) {ψ : ClauseSet V} (h : ¬ Sparse θ ψ) :
    ∃ c H, Choice θ ψ c H := by
  classical
  have hex : ∃ c, ∃ H, Heavy θ ψ c H := by
    simp only [Sparse, not_forall, not_not] at h
    exact h
  set c₀ := Nat.find hex
  -- the largest heart at the smallest clause size
  have hP : ∃ h, h ≤ c₀ ∧ ∃ H : Finset (Literal V), H.card = h ∧ Heavy θ ψ c₀ H := by
    obtain ⟨H₀, hH₀⟩ := Nat.find_spec hex
    exact ⟨H₀.card, hH₀.2.1.le, H₀, rfl, hH₀⟩
  obtain ⟨h₀, hh₀, H, hH, hheavy⟩ := hP
  set m := Nat.findGreatest (fun h => ∃ H : Finset (Literal V), H.card = h ∧ Heavy θ ψ c₀ H) c₀
  obtain ⟨H', hH', hheavy'⟩ : ∃ H : Finset (Literal V), H.card = m ∧ Heavy θ ψ c₀ H :=
    Nat.findGreatest_spec (P := fun h => ∃ H : Finset (Literal V), H.card = h ∧ Heavy θ ψ c₀ H)
      hh₀ ⟨H, hH, hheavy⟩
  refine ⟨c₀, H', hheavy', fun c' H'' h'' => Nat.find_min' hex ⟨H'', h''⟩, fun H'' h'' => ?_⟩
  rw [hH']
  exact Nat.le_findGreatest h''.2.1.le ⟨H'', rfl, h''⟩

/-- The canonical branching choice: a valid choice if there is one. -/
noncomputable def chooseBranch (θ : ℕ → ℕ) (ψ : ClauseSet V) : ℕ × Finset (Literal V) :=
  open Classical in
  if h : Sparse θ ψ then (0, ∅)
  else ((exists_choice θ h).choose, (exists_choice θ h).choose_spec.choose)

/-- `chooseBranch θ ψ` yields a valid branching choice whenever `ψ` is not sparse. -/
theorem choice_chooseBranch {ψ : ClauseSet V} (h : ¬ Sparse θ ψ) :
    Choice θ ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2 := by
  unfold chooseBranch
  rw [dite_eq_right h]
  exact (exists_choice θ h).choose_spec.choose_spec

/-- A *branching rule* for the thresholds `θ`: a deterministic step `next` on states `σ`, each
representing the clause set `toClauseSet s`, which at every state that is not sparse takes the
heart (`false`) or petal (`true`) child for one valid choice. -/
structure BranchingRule (θ : ℕ → ℕ) (V : Type*) [DecidableEq V] (σ : Type*) where
  /-- The clause set a state represents. -/
  toClauseSet : σ → ClauseSet V
  /-- The heart (`false`) or petal (`true`) child of a state. -/
  next : σ → Bool → σ
  /-- At a state that is not sparse, both children are taken for one valid choice. -/
  exists_choice_next : ∀ s, ¬ Sparse θ (toClauseSet s) →
    ∃ c H, Choice θ (toClauseSet s) c H ∧ ∀ b, toClauseSet (next s b) = child (toClauseSet s) c H b

/-- The canonical branching rule on clause sets, with the choice `chooseBranch`. -/
noncomputable def chooseRule (θ : ℕ → ℕ) : BranchingRule θ V (ClauseSet V) where
  toClauseSet := id
  next ψ := child ψ (chooseBranch θ ψ).1 (chooseBranch θ ψ).2
  exists_choice_next _ h := ⟨_, _, choice_chooseBranch h, fun _ => rfl⟩

namespace BranchingRule

variable {σ : Type*} (R : BranchingRule θ V σ)

/-- The branching tree of a rule: its leaves are the sparse states. -/
@[simps]
def tree : BinaryBranching σ where
  IsLeaf s := Sparse θ (R.toClauseSet s)
  next := R.next

variable {R}

/-! ### One step -/

/-- A child only loses solutions: its solutions are solutions of the parent. -/
private theorem sat_of_sat_next {s : σ} (hs : ¬ Sparse θ (R.toClauseSet s)) {b : Bool}
    {x : V → Bool} (hx : (R.toClauseSet (R.next s b)).Sat x) : (R.toClauseSet s).Sat x := by
  obtain ⟨c, H, -, hnext⟩ := R.exists_choice_next s hs
  rw [hnext] at hx
  exact sat_of_sat_child hx

/-- **The branches cover.** Every solution of a state that is not sparse is a solution of one of
its children. -/
private theorem exists_sat_next {s : σ} (hs : ¬ Sparse θ (R.toClauseSet s)) {x : V → Bool}
    (hx : (R.toClauseSet s).Sat x) : ∃ b, (R.toClauseSet (R.next s b)).Sat x := by
  obtain ⟨c, H, -, hnext⟩ := R.exists_choice_next s hs
  refine ⟨decide ¬ ∃ l ∈ H, x l.1 = l.2, ?_⟩
  rw [hnext]
  exact sat_child_of_sat hx

/-- Every clause of a child is contained in a clause of its parent. -/
private theorem refines_next (hθ : ∀ j, 1 ≤ θ j) {s : σ} (hs : ¬ Sparse θ (R.toClauseSet s))
    (b : Bool) : Refines (R.toClauseSet (R.next s b)) (R.toClauseSet s) := by
  obtain ⟨c, H, hch, hnext⟩ := R.exists_choice_next s hs
  intro C hC
  rw [hnext] at hC
  rcases mem_union.mp (child_subset _ _ _ _ hC) with hC | hC
  · exact ⟨C, hC, subset_rfl⟩
  · obtain ⟨D, hD, hCD⟩ := exists_flower_ssuperset hθ hch.1 hC
    exact ⟨D, flower_subset _ _ _ hD, hCD.subset⟩

/-! ### The tree -/

section

variable (hθ : ∀ j, 1 ≤ θ j)
include hθ

/-- **Termination.** Each branching step strictly decreases the potential. -/
theorem tree_terminating : R.tree.Terminating :=
  .of_lt (fun s => potential (R.toClauseSet s)) fun s hs b => by
    obtain ⟨c, H, hch, hnext⟩ := R.exists_choice_next s hs
    rw [tree_next, hnext]
    exact potential_child_lt hθ hch.1 b

/-- Every clause reached along a node word is contained in a clause of the start. -/
theorem refines_walk {s : σ} {w : List Bool} (h : R.tree.IsNodeWord s w) :
    Refines (R.toClauseSet (R.tree.walk s w)) (R.toClauseSet s) := by
  induction w generalizing s with
  | nil => exact fun C hC => ⟨C, hC, subset_rfl⟩
  | cons b w ih => exact (ih h.2).trans (refines_next hθ h.1 b)

/-- **Covering.** Every solution of a state reaches a leaf of which it is a solution. -/
theorem exists_isLeafWord_sat (s : σ) {x : V → Bool} (hx : (R.toClauseSet s).Sat x) :
    ∃ w, R.tree.IsLeafWord s w ∧ (R.toClauseSet (R.tree.walk s w)).Sat x := by
  induction s using BinaryBranching.Terminating.induction (tree_terminating (R := R) hθ) with
  | leaf s hs => exact ⟨[], hs, hx⟩
  | node s hs ih =>
    obtain ⟨b, hb⟩ := exists_sat_next hs hx
    obtain ⟨w, hw, hwx⟩ := ih b hb
    exact ⟨b :: w, ⟨hs, hw⟩, hwx⟩

end

/-- Solutions of a state reached along a node word are solutions of the start. -/
theorem sat_of_sat_walk {s : σ} {w : List Bool} (h : R.tree.IsNodeWord s w)
    {x : V → Bool} (hx : (R.toClauseSet (R.tree.walk s w)).Sat x) : (R.toClauseSet s).Sat x := by
  induction w generalizing s with
  | nil => exact hx
  | cons b w ih => exact sat_of_sat_next h.1 (ih h.2 hx)

/-- A state is satisfiable exactly when one of its leaves is. -/
theorem exists_isLeafWord_sat_iff (hθ : ∀ j, 1 ≤ θ j) (s : σ) (x : V → Bool) :
    (∃ w, R.tree.IsLeafWord s w ∧ (R.toClauseSet (R.tree.walk s w)).Sat x) ↔
      (R.toClauseSet s).Sat x :=
  ⟨fun ⟨_, hw, hx⟩ => sat_of_sat_walk hw.isNodeWord hx, exists_isLeafWord_sat hθ s⟩

/-- **A leaf word is a branch.** From a reduced state, it yields a `Path` with the same length,
ending in a sparse node, whose nodes are the states along the word and whose petal steps are the
positions of `true` in the word. -/
theorem exists_path_of_isLeafWord {s : σ} (hred : Reduced (R.toClauseSet s)) {w : List Bool}
    (hw : R.tree.IsLeafWord s w) :
    ∃ P : Path θ V, (∀ i ≤ w.length, P.node i = R.toClauseSet (R.tree.walk s (w.take i))) ∧
      P.len = w.length ∧ Sparse θ (P.node P.len) ∧
      (range P.len).filter (fun i => P.dir i = true) =
        (range w.length).filter fun i => w.getD i false = true := by
  classical
  have hns := hw.isNodeWord.not_isLeaf_take
  have hch (i : ℕ) (hi : i < w.length) := R.exists_choice_next _ (hns i hi)
  let size (i : ℕ) : ℕ := if hi : i < w.length then (hch i hi).choose else 0
  let heart (i : ℕ) : Finset (Literal V) :=
    if hi : i < w.length then (hch i hi).choose_spec.choose else ∅
  have hspec (i : ℕ) (hi : i < w.length) :
      Choice θ (R.toClauseSet (R.tree.walk s (w.take i))) (size i) (heart i) ∧
        ∀ b, R.toClauseSet (R.next (R.tree.walk s (w.take i)) b) =
          child (R.toClauseSet (R.tree.walk s (w.take i))) (size i) (heart i) b := by
    simp only [size, heart, dite_eq_left hi]
    exact (hch i hi).choose_spec.choose_spec
  refine ⟨{ len := w.length
            node := fun i => R.toClauseSet (R.tree.walk s (w.take i))
            size := size
            heart := heart
            dir := fun i => w.getD i false
            choice := fun i hi => (hspec i hi).1
            step := fun i hi => by
              rw [R.tree.walk_take_succ s w hi]
              exact (hspec i hi).2 _
            reduced_zero := by simpa [BinaryBranching.walk] using hred },
    fun i _ => rfl, rfl, ?_, rfl⟩
  simpa [List.take_length] using hw.isLeaf_walk

end BranchingRule

end Cslib.Logic.PL.ClauseSet.Sparsification
