/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

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

A word `w : List Bool` names the state reached by taking the heart (`false`) or petal (`true`)
branch at each step (`walk`). A *node word* is one whose proper prefixes reach states that are
not sparse (`IsNodeWord`); a *leaf word* is a node word that reaches a sparse state
(`IsLeafWord`). Every leaf word yields a `Path` with the same length and the same petal steps
(`exists_path_of_isLeafWord`), every node word extends to a leaf word
(`IsNodeWord.exists_isLeafWord_append`), and leaf words are determined by their petal steps
(`IsLeafWord.eq_of_getD_eq`).

Every solution of the root reaches a leaf containing it (`exists_isLeafWord_sat`, by induction on
the potential). The leaves are recovered from the positions of their petal steps: following any
branch sequence `f : ℕ → Bool` until a sparse state is reached (`walkSeq`) ends at the leaf of
every leaf word that agrees with `f` (`walkSeq_eq_walk`).

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule`: a deterministic branching step.
* `Cslib.Logic.PL.ClauseSet.Sparsification.chooseRule`: the canonical rule on clause sets.
* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.walk`, `.IsNodeWord`, `.IsLeafWord`:
  the branching tree of a rule.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.exists_isLeafWord_sat`: every solution
  reaches a leaf.
* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.exists_path_of_isLeafWord`: leaf words are
  branches.
* `Cslib.Logic.PL.ClauseSet.Sparsification.BranchingRule.IsLeafWord.eq_of_getD_eq`: leaf words are
  determined by their petal steps.

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

/-- The state reached along a word of branches. -/
def walk : σ → List Bool → σ
  | s, [] => s
  | s, b :: w => walk (R.next s b) w

/-- A *node word*: its proper prefixes reach states that are not sparse. -/
def IsNodeWord : σ → List Bool → Prop
  | _, [] => True
  | s, b :: w => ¬ Sparse θ (R.toClauseSet s) ∧ IsNodeWord (R.next s b) w

/-- A *leaf word*: its proper prefixes reach states that are not sparse and it reaches a sparse
state. -/
def IsLeafWord : σ → List Bool → Prop
  | s, [] => Sparse θ (R.toClauseSet s)
  | s, b :: w => ¬ Sparse θ (R.toClauseSet s) ∧ IsLeafWord (R.next s b) w

/-- Follow the branch sequence `f` for at most `n` steps, stopping at a sparse state. -/
noncomputable def walkSeq : ℕ → σ → (ℕ → Bool) → σ
  | 0, s, _ => s
  | n + 1, s, f =>
    open Classical in
    if Sparse θ (R.toClauseSet s) then s else walkSeq n (R.next s (f 0)) fun i => f (i + 1)

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

/-- **Termination.** Each branching step strictly decreases the potential. -/
theorem potential_next_lt (hθ : ∀ j, 1 ≤ θ j) {s : σ} (hs : ¬ Sparse θ (R.toClauseSet s))
    (b : Bool) : potential (R.toClauseSet (R.next s b)) < potential (R.toClauseSet s) := by
  obtain ⟨c, H, hch, hnext⟩ := R.exists_choice_next s hs
  rw [hnext]
  exact potential_child_lt hθ hch.1 b

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

/-! ### Words -/

private theorem walk_append (s : σ) (u v : List Bool) :
    R.walk s (u ++ v) = R.walk (R.walk s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih => exact ih (R.next s a)

private theorem walk_take_succ (s : σ) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    R.walk s (w.take (i + 1)) = R.next (R.walk s (w.take i)) (w.getD i false) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, walk_append,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rfl

/-- Every leaf word is a node word. -/
theorem IsLeafWord.isNodeWord {s : σ} {w : List Bool} (h : R.IsLeafWord s w) :
    R.IsNodeWord s w := by
  induction w generalizing s with
  | nil => trivial
  | cons b w ih => exact ⟨h.1, ih h.2⟩

/-- Walking along a leaf word reaches a sparse clause set. -/
theorem IsLeafWord.sparse_walk {s : σ} {w : List Bool} (h : R.IsLeafWord s w) :
    Sparse θ (R.toClauseSet (R.walk s w)) := by
  induction w generalizing s with
  | nil => exact h
  | cons b w ih => exact ih h.2

private theorem IsNodeWord.isLeafWord {s : σ} {w : List Bool} (hn : R.IsNodeWord s w)
    (hs : Sparse θ (R.toClauseSet (R.walk s w))) : R.IsLeafWord s w := by
  induction w generalizing s with
  | nil => exact hs
  | cons b w ih => exact ⟨hn.1, ih hn.2 hs⟩

/-- A leaf word is a node word reaching a sparse state. -/
private theorem isLeafWord_iff {s : σ} {w : List Bool} :
    R.IsLeafWord s w ↔ R.IsNodeWord s w ∧ Sparse θ (R.toClauseSet (R.walk s w)) :=
  ⟨fun h => ⟨h.isNodeWord, h.sparse_walk⟩, fun h => h.1.isLeafWord h.2⟩

private theorem IsNodeWord.append {s : σ} {u v : List Bool} (hu : R.IsNodeWord s u)
    (hv : R.IsNodeWord (R.walk s u) v) : R.IsNodeWord s (u ++ v) := by
  induction u generalizing s with
  | nil => exact hv
  | cons b u ih => exact ⟨hu.1, ih hu.2 hv⟩

private theorem IsNodeWord.of_append {s : σ} {u v : List Bool} (h : R.IsNodeWord s (u ++ v)) :
    R.IsNodeWord s u ∧ R.IsNodeWord (R.walk s u) v := by
  induction u generalizing s with
  | nil => exact ⟨trivial, h⟩
  | cons b u ih =>
    obtain ⟨h₁, h₂⟩ := ih h.2
    exact ⟨⟨h.1, h₁⟩, h₂⟩

private theorem IsNodeWord.not_sparse_take {s : σ} {w : List Bool} (h : R.IsNodeWord s w) :
    ∀ i < w.length, ¬ Sparse θ (R.toClauseSet (R.walk s (w.take i))) := by
  induction w generalizing s with
  | nil => intro i hi; simp at hi
  | cons b w ih =>
    intro i hi
    cases i with
    | zero => exact h.1
    | succ i =>
      rw [List.take_succ_cons, walk]
      exact ih h.2 i (by simpa using hi)

/-- **Leaf words are determined by their petal steps.** Two leaf words with petal steps at the
same positions are equal. -/
theorem IsLeafWord.eq_of_getD_eq {s : σ} {w w' : List Bool} (hw : R.IsLeafWord s w)
    (hw' : R.IsLeafWord s w') (h : ∀ i, w.getD i false = w'.getD i false) : w = w' := by
  induction w generalizing s w' with
  | nil =>
    cases w' with
    | nil => rfl
    | cons b' w' => exact absurd hw hw'.1
  | cons b w ih =>
    cases w' with
    | nil => exact absurd hw' hw.1
    | cons b' w' =>
      have hb : b = b' := by simpa using h 0
      subst hb
      rw [ih hw.2 hw'.2 fun i => by simpa using h (i + 1)]

/-! ### Termination and covering -/

section

variable (hθ : ∀ j, 1 ≤ θ j)
include hθ

/-- Every state has a leaf word. -/
theorem exists_isLeafWord (s : σ) : ∃ w, R.IsLeafWord s w := by
  induction h : potential (R.toClauseSet s) using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases hs : Sparse θ (R.toClauseSet s)
    · exact ⟨[], hs⟩
    · obtain ⟨w, hw⟩ := ih _ (h ▸ potential_next_lt hθ hs false) (R.next s false) rfl
      exact ⟨false :: w, hs, hw⟩

/-- Every node word extends to a leaf word. -/
theorem IsNodeWord.exists_isLeafWord_append {s : σ} {w : List Bool} (h : R.IsNodeWord s w) :
    ∃ u, R.IsLeafWord s (w ++ u) := by
  obtain ⟨u, hu⟩ := exists_isLeafWord (R := R) hθ (R.walk s w)
  rw [isLeafWord_iff] at hu
  exact ⟨u, isLeafWord_iff.mpr ⟨h.append hu.1, by rw [walk_append]; exact hu.2⟩⟩

/-- Every clause reached along a node word is contained in a clause of the start. -/
theorem IsNodeWord.refines_walk {s : σ} {w : List Bool} (h : R.IsNodeWord s w) :
    Refines (R.toClauseSet (R.walk s w)) (R.toClauseSet s) := by
  induction w generalizing s with
  | nil => exact fun C hC => ⟨C, hC, subset_rfl⟩
  | cons b w ih => exact (ih h.2).trans (refines_next hθ h.1 b)

/-- Every clause reached by following branches is contained in a clause of the start. -/
theorem refines_walkSeq {n : ℕ} {s : σ} {f : ℕ → Bool} :
    Refines (R.toClauseSet (R.walkSeq n s f)) (R.toClauseSet s) := by
  induction n generalizing s f with
  | zero => exact fun C hC => ⟨C, hC, subset_rfl⟩
  | succ n ih =>
    unfold walkSeq
    split_ifs with hsparse
    · exact fun C hC => ⟨C, hC, subset_rfl⟩
    · exact ih.trans (refines_next hθ hsparse _)

/-- **Covering.** Every solution of a state reaches a leaf of which it is a solution. -/
theorem exists_isLeafWord_sat (s : σ) {x : V → Bool} (hx : (R.toClauseSet s).Sat x) :
    ∃ w, R.IsLeafWord s w ∧ (R.toClauseSet (R.walk s w)).Sat x := by
  induction h : potential (R.toClauseSet s) using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases hs : Sparse θ (R.toClauseSet s)
    · exact ⟨[], hs, hx⟩
    · obtain ⟨b, hb⟩ := exists_sat_next hs hx
      obtain ⟨w, hw, hwx⟩ := ih _ (h ▸ potential_next_lt hθ hs b) (R.next s b) hb rfl
      exact ⟨b :: w, ⟨hs, hw⟩, hwx⟩

end

/-- Solutions of a state reached along a node word are solutions of the start. -/
theorem IsNodeWord.sat_of_sat_walk {s : σ} {w : List Bool} (h : R.IsNodeWord s w)
    {x : V → Bool} (hx : (R.toClauseSet (R.walk s w)).Sat x) : (R.toClauseSet s).Sat x := by
  induction w generalizing s with
  | nil => exact hx
  | cons b w ih => exact sat_of_sat_next h.1 (ih h.2 hx)

/-- Every satisfying assignment of the state reached by `walkSeq` satisfies the starting state. -/
theorem sat_of_sat_walkSeq {n : ℕ} {s : σ} {f : ℕ → Bool} {x : V → Bool}
    (hx : (R.toClauseSet (R.walkSeq n s f)).Sat x) : (R.toClauseSet s).Sat x := by
  induction n generalizing s f with
  | zero => exact hx
  | succ n ih =>
    unfold walkSeq at hx
    split_ifs at hx with hsparse
    · exact hx
    · exact sat_of_sat_next hsparse (ih hx)

/-- Following a branch sequence that agrees with a leaf word, for at least as many steps, ends at
that leaf. -/
theorem walkSeq_eq_walk {s : σ} {w : List Bool} (hw : R.IsLeafWord s w)
    {f : ℕ → Bool} (hf : ∀ i < w.length, f i = w.getD i false) {n : ℕ} (hn : w.length ≤ n) :
    R.walkSeq n s f = R.walk s w := by
  induction w generalizing s f n with
  | nil =>
    cases n with
    | zero => rfl
    | succ n => simp only [walkSeq, walk]; exact ite_eq_left hw
  | cons b w ih =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    simp only [walkSeq, walk]
    rw [ite_eq_right hw.1]
    have hf0 : f 0 = b := by simpa using hf 0 (by simp)
    rw [hf0]
    refine ih hw.2 (fun i hi => ?_) (by simpa using hn)
    simpa using hf (i + 1) (by simpa using hi)

/-- **A leaf word is a branch.** From a reduced state, it yields a `Path` with the same length,
ending in a sparse node, whose nodes are the states along the word and whose petal steps are the
positions of `true` in the word. -/
theorem exists_path_of_isLeafWord {s : σ} (hred : Reduced (R.toClauseSet s)) {w : List Bool}
    (hw : R.IsLeafWord s w) :
    ∃ P : Path θ V, (∀ i ≤ w.length, P.node i = R.toClauseSet (R.walk s (w.take i))) ∧
      P.len = w.length ∧ Sparse θ (P.node P.len) ∧
      (range P.len).filter (fun i => P.dir i = true) =
        (range w.length).filter fun i => w.getD i false = true := by
  classical
  have hns := hw.isNodeWord.not_sparse_take
  have hch (i : ℕ) (hi : i < w.length) := R.exists_choice_next _ (hns i hi)
  let size (i : ℕ) : ℕ := if hi : i < w.length then (hch i hi).choose else 0
  let heart (i : ℕ) : Finset (Literal V) :=
    if hi : i < w.length then (hch i hi).choose_spec.choose else ∅
  have hspec (i : ℕ) (hi : i < w.length) :
      Choice θ (R.toClauseSet (R.walk s (w.take i))) (size i) (heart i) ∧
        ∀ b, R.toClauseSet (R.next (R.walk s (w.take i)) b) =
          child (R.toClauseSet (R.walk s (w.take i))) (size i) (heart i) b := by
    simp only [size, heart, dite_eq_left hi]
    exact (hch i hi).choose_spec.choose_spec
  refine ⟨{ len := w.length
            node := fun i => R.toClauseSet (R.walk s (w.take i))
            size := size
            heart := heart
            dir := fun i => w.getD i false
            choice := fun i hi => (hspec i hi).1
            step := fun i hi => by
              rw [walk_take_succ s w hi]
              exact (hspec i hi).2 _
            reduced_zero := by simpa [walk] using hred }, fun i _ => rfl, rfl, ?_, rfl⟩
  simpa [List.take_length] using hw.sparse_walk

end BranchingRule

end Cslib.Logic.PL.ClauseSet.Sparsification
