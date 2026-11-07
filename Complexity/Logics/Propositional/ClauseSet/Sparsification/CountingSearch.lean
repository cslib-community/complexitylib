/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingList
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingTree
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Bounds
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Counting sparsification -- branching rules

A *counting branching rule* (`CountingBranchingRule`) is the counting-sparsification analogue of
`BranchingRule` (`Complexity/Logics/Propositional/ClauseSet/Sparsification/Tree.lean`): a
deterministic step `next : σ → Bool → σ` on states `σ` representing clause sets via `toClauseSet`,
which at every state that is not sparse takes the heart (`false`) or petal-plus-negated-heart-units
(`true`) child (`ClauseSet.Sparsification.countingChild`) for some valid choice `Choice θ`. Its
tree (`CountingBranchingRule.tree`) is the binary branching whose leaves are the sparse states;
words, leaf words and the depth-first search are those of `Cslib.BinaryBranching`.

When all thresholds for `j ≥ 1` are at least `2` (in particular for `countingThreshold M` with
`M ≥ 2`), every non-sparse step strictly decreases the clause-set potential
`potential ψ = ∑ C ∈ ψ, 2 ^ C.card` (`potential_countingChild_lt` from `CountingTree.lean`), so the
tree terminates (`CountingBranchingRule.tree_terminating`): removing a flower of `|F| ≥ 2` clauses
of width `c` decreases the potential by `|F| · 2 ^ c`, while adding the `|F|` petals of width
`c - |H| ≤ c - 1` and `|H| ≤ c - 1` unit clauses adds at most `|F| · 2 ^ (c - 1) + 2 (c - 1) <
|F| · 2 ^ c`. Furthermore, because `reduce` eliminates every clause of the flower `F` on both
branches, each step increases the total clause count by at most `K` (`card_countingChild_le`,
`CountingBranchingRule.card_walk_le`).

At the list level, `Cslib.Logic.PL.CNF.Sparsification.countingRule` instantiates
`CountingBranchingRule` on `{ψ : CNF V // CountingNormalized k ψ}` using `countingNext θ k`. The
model count is additive at its inner states, so it is the sum of the model counts of the leaves
(`Cslib.Logic.PL.CNF.Sparsification.sum_leafWords_countingRule_modelCountOn`).

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule`: a deterministic
  counting-sparsification branching rule.
* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.tree`: its branching tree.
* `Cslib.Logic.PL.CNF.Sparsification.countingRule`: the list-level counting branching rule on
  `{ψ : CNF V // CountingNormalized k ψ}`.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.tree_terminating`: strict
  potential decrease on both counting branches when `∀ j, 1 ≤ j → 2 ≤ θ j`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.card_countingChild_le`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.card_walk_le`:
  each counting step increases the number of clauses by at most the width `K`.
* `Cslib.Logic.PL.CNF.Sparsification.sum_leafWords_countingRule_modelCountOn`: the sum of
  `modelCountOn declared` over all leaf words equals the root `modelCountOn declared`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 6.4,
  Proposition 6.4 (pp. 43–44) and Appendix A (pp. 44–47).
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V] {θ : ℕ → ℕ}

/-! ### Clause-set properties of `countingChild` -/

/-- Every clause of `countingChild ψ c H true` belongs to `(ψ \ flower ψ c H) ∪ petals ψ c H ∪
negatedHeartUnits H`. -/
private theorem countingChild_true_subset {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (h : Heavy θ ψ c H) :
    countingChild ψ c H true ⊆ (ψ \ flower ψ c H) ∪ petals ψ c H ∪ negatedHeartUnits H := by
  intro C hC
  rcases mem_union.mp (reduce_subset _ hC) with hC' | hCu
  · rcases mem_union.mp hC' with hCψ | hCp
    · refine mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨hCψ, fun hF => ?_⟩))
      exact disjoint_left.mp (disjoint_flower_countingChild ψ h.1 h.2.1 true) hF hC
    · exact mem_union_left _ (mem_union_right _ hCp)
  · exact mem_union_right _ hCu

/-- Every clause of `countingChild ψ c H false` belongs to `(ψ \ flower ψ c H) ∪ {H}`. -/
private theorem countingChild_false_subset {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (h : Heavy θ ψ c H) :
    countingChild ψ c H false ⊆ (ψ \ flower ψ c H) ∪ {H} := by
  intro C hC
  rcases mem_union.mp (reduce_subset _ hC) with hCψ | hCH
  · refine mem_union_left _ (mem_sdiff.mpr ⟨hCψ, fun hF => ?_⟩)
    exact disjoint_left.mp (disjoint_flower_countingChild ψ h.1 h.2.1 false) hF hC
  · exact mem_union_right _ hCH

/-- Each counting child increases the number of clauses by at most `k`: the flower `F` is removed
from `ψ` while at most `|F| + |H| ≤ |F| + k` clauses are added. -/
theorem card_countingChild_le (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet V} {c k : ℕ}
    {H : Finset (Literal V)} (h : Heavy θ ψ c H) (hk : ∀ C ∈ ψ, C.card ≤ k) (b : Bool) :
    (countingChild ψ c H b).card ≤ ψ.card + k := by
  set F := flower ψ c H
  have hFsub : F ⊆ ψ := flower_subset ψ c H
  have hFcard : (ψ \ F).card + F.card = ψ.card := card_sdiff_add_card_eq_card hFsub
  obtain ⟨D, hD⟩ := h.flower_nonempty hθ
  have hFpos : 1 ≤ F.card := card_pos.mpr ⟨D, hD⟩
  have hck : c ≤ k := (mem_flower.mp hD).2.1 ▸ hk D (hFsub hD)
  cases b with
  | false =>
    calc (countingChild ψ c H false).card
        ≤ ((ψ \ F) ∪ {H}).card := card_le_card (countingChild_false_subset h)
      _ ≤ (ψ \ F).card + ({H} : Finset (Finset (Literal V))).card := card_union_le _ _
      _ = (ψ \ F).card + 1 := by rw [card_singleton]
      _ ≤ ψ.card + k := by omega
  | true =>
    have hpet : (petals ψ c H).card = F.card := card_petals ψ c H
    have huni : (negatedHeartUnits H).card ≤ H.card := card_image_le
    have hHc : H.card < c := h.2.1
    calc (countingChild ψ c H true).card
        ≤ ((ψ \ F) ∪ petals ψ c H ∪ negatedHeartUnits H).card :=
          card_le_card (countingChild_true_subset h)
      _ ≤ ((ψ \ F) ∪ petals ψ c H).card + (negatedHeartUnits H).card := card_union_le _ _
      _ ≤ (ψ \ F).card + (petals ψ c H).card + (negatedHeartUnits H).card :=
          Nat.add_le_add_right (card_union_le _ _) _
      _ ≤ ψ.card + k := by omega

/-! ### Counting branching rules -/

/-- A *counting branching rule* for the thresholds `θ`: a deterministic step `next` on states `σ`,
each representing the clause set `toClauseSet s`, which at every state that is not sparse takes the
heart (`false`) or petal + negated-heart-units (`true`) child `countingChild` for one valid choice.
-/
structure CountingBranchingRule (θ : ℕ → ℕ) (V : Type*) [DecidableEq V] (σ : Type*) where
  /-- The clause set a state represents. -/
  toClauseSet : σ → ClauseSet V
  /-- The heart (`false`) or petal + negated-heart-units (`true`) child of a state. -/
  next : σ → Bool → σ
  /-- At a state that is not sparse, both children are taken for one valid choice. -/
  exists_choice_next : ∀ s, ¬ Sparse θ (toClauseSet s) →
    ∃ c H, Choice θ (toClauseSet s) c H ∧
      ∀ b, toClauseSet (next s b) = countingChild (toClauseSet s) c H b

namespace CountingBranchingRule

variable {σ : Type*} (R : CountingBranchingRule θ V σ)

/-- The branching tree of a counting rule: its leaves are the sparse states. -/
@[simps]
def tree : BinaryBranching σ where
  IsLeaf s := Sparse θ (R.toClauseSet s)
  next := R.next

variable {R}

/-- **Termination.** When `∀ j, 1 ≤ j → 2 ≤ θ j`, each counting branching step strictly decreases
the potential. -/
theorem tree_terminating (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j) : R.tree.Terminating :=
  .of_lt (fun s => potential (R.toClauseSet s)) fun s hs b => by
    obtain ⟨c, H, hch, hnext⟩ := R.exists_choice_next s hs
    rw [tree_next, hnext]
    exact potential_countingChild_lt hθ hch.1 b

/-- Node words preserve clause width `≤ k`. -/
theorem card_le_of_mem_walk (hθ : ∀ j, 1 ≤ θ j) {k : ℕ} {s : σ}
    (hk : ∀ C ∈ R.toClauseSet s, C.card ≤ k) {w : List Bool} (hw : R.tree.IsNodeWord s w) :
    ∀ C ∈ R.toClauseSet (R.tree.walk s w), C.card ≤ k := by
  induction w generalizing s with
  | nil => exact hk
  | cons b w ih =>
    obtain ⟨c, H, hch, hnext⟩ := R.exists_choice_next s hw.1
    refine ih (fun C hC => ?_) hw.2
    rw [tree_next, hnext b] at hC
    exact card_le_of_mem_countingChild hch.1.1 hch.1.2.1 (hch.1.flower_nonempty hθ) hk hC

/-- Along a node word `w` from a state of width `≤ k`, the number of clauses increases by at most
`k * w.length`. -/
theorem card_walk_le (hθ : ∀ j, 1 ≤ θ j) {k : ℕ} {s : σ}
    (hk : ∀ C ∈ R.toClauseSet s, C.card ≤ k) {w : List Bool} (hw : R.tree.IsNodeWord s w) :
    (R.toClauseSet (R.tree.walk s w)).card ≤ (R.toClauseSet s).card + k * w.length := by
  induction w generalizing s with
  | nil => simp [BinaryBranching.walk]
  | cons b w ih =>
    obtain ⟨c, H, hch, hnext⟩ := R.exists_choice_next s hw.1
    have hk_next : ∀ C ∈ R.toClauseSet (R.next s b), C.card ≤ k := by
      intro C hC
      rw [hnext b] at hC
      exact card_le_of_mem_countingChild hch.1.1 hch.1.2.1 (hch.1.flower_nonempty hθ) hk hC
    have hcard_next : (R.toClauseSet (R.next s b)).card ≤ (R.toClauseSet s).card + k := by
      rw [hnext b]
      exact card_countingChild_le hθ hch.1 hk b
    have hih := ih hk_next hw.2
    simp only [BinaryBranching.walk, tree_next, List.length_cons] at hih ⊢
    calc (R.toClauseSet (R.tree.walk (R.next s b) w)).card
        ≤ (R.toClauseSet (R.next s b)).card + k * w.length := hih
      _ ≤ ((R.toClauseSet s).card + k) + k * w.length := Nat.add_le_add_right hcard_next _
      _ = (R.toClauseSet s).card + k * (w.length + 1) := by ring

end CountingBranchingRule

end Cslib.Logic.PL.ClauseSet.Sparsification

namespace Cslib.Logic.PL.CNF.Sparsification

open ClauseSet.Sparsification

variable {V : Type*} [DecidableEq V]

/-- For `2 ≤ M` and `1 ≤ j`, `2 ≤ countingThreshold M j`. -/
theorem two_le_countingThreshold {M : ℕ} (hM : 2 ≤ M) {j : ℕ} (hj : 1 ≤ j) :
    2 ≤ countingThreshold M j := by
  unfold countingThreshold
  calc 2 = 2 ^ 1 := rfl
    _ ≤ M ^ 1 := Nat.pow_le_pow_left hM 1
    _ ≤ M ^ j := Nat.pow_le_pow_right (by omega) hj

/-- **The list-level counting branching rule**, on formulas in nontautological normal form
(`CountingNormalized k`): uses `countingNext θ k`. -/
def countingRule {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {k : ℕ} (hk : 1 ≤ k) :
    CountingBranchingRule θ V {ψ : CNF V // CountingNormalized k ψ} where
  toClauseSet ψ := ψ.1.toClauseSet
  next ψ b := ⟨countingNext θ k ψ.1 b, countingNormalized_countingNext θ hk ψ.2 b⟩
  exists_choice_next ψ hns :=
    ⟨_, _, (choice_spec hθ ψ.2.toNormalized hns).1,
      fun b => toClauseSet_countingNext ψ.2.toNormalized b⟩

/-- Walking along `countingRule` preserves variable support containment for any word `w`. -/
theorem support_walk_countingRule {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {k : ℕ} (hk : 1 ≤ k)
    {s : {ψ : CNF V // CountingNormalized k ψ}} {declared : Finset V}
    (hs : ∀ C ∈ s.1, ∀ l ∈ C, l.1 ∈ declared) (w : List Bool) :
    ∀ C ∈ ((countingRule hθ hk).tree.walk s w).1, ∀ l ∈ C, l.1 ∈ declared := by
  induction w generalizing s with
  | nil => exact hs
  | cons b w ih => exact ih (support_countingNext θ k hs b)

/-- **List-level leaf model-count partition.** If `f` computes `CNF.modelCountOn · declared` on
every leaf of `s` under `countingRule`, then the sum of `f` over the leaf words of `s` equals
`s.1.modelCountOn declared`. -/
theorem sum_leafWords_countingRule_modelCountOn {θ : ℕ → ℕ} (hθ1 : ∀ j, 1 ≤ θ j)
    (hθ2 : ∀ j, 1 ≤ j → 2 ≤ θ j) {k : ℕ} (hk : 1 ≤ k) (declared : Finset V)
    {f : {ψ : CNF V // CountingNormalized k ψ} → ℕ}
    (s : {ψ : CNF V // CountingNormalized k ψ})
    (hf : ∀ w, (countingRule hθ1 hk).tree.IsLeafWord s w →
      f ((countingRule hθ1 hk).tree.walk s w) =
        ((countingRule hθ1 hk).tree.walk s w).1.modelCountOn declared)
    {W : Finset (List Bool)} (hW : ∀ w, w ∈ W ↔ (countingRule hθ1 hk).tree.IsLeafWord s w) :
    ∑ w ∈ W, f ((countingRule hθ1 hk).tree.walk s w) = s.1.modelCountOn declared := by
  rw [Finset.sum_congr rfl fun w hw => hf w ((hW w).mp hw)]
  exact BinaryBranching.sum_leafWords_eq (CountingBranchingRule.tree_terminating hθ2)
    (g := fun t => t.1.modelCountOn declared)
    (fun t _ => modelCountOn_countingNext t.2.toNormalized declared) s hW

end Cslib.Logic.PL.CNF.Sparsification
