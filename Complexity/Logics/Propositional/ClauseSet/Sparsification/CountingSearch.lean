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
# Counting sparsification -- branching rules and depth-first tree search

A *counting branching rule* (`CountingBranchingRule`) is the counting-sparsification analogue of
`BranchingRule` (`Complexity/Logics/Propositional/ClauseSet/Sparsification/Tree.lean`): a
deterministic step `next : σ → Bool → σ` on states `σ` representing clause sets via `toClauseSet`,
which at every state that is not sparse takes the heart (`false`) or petal-plus-negated-heart-units
(`true`) child (`ClauseSet.Sparsification.countingChild`) for some valid choice `Choice θ`.

When all thresholds for `j ≥ 1` are at least `2` (in particular for `countingThreshold M` with
`M ≥ 2`), every non-sparse step strictly decreases the clause-set potential
`potential ψ = ∑ C ∈ ψ, 2 ^ C.card` (`potential_countingChild_lt` from `CountingTree.lean`,
`CountingBranchingRule.potential_next_lt`): removing a flower of `|F| ≥ 2` clauses of width `c`
decreases the potential by `|F| · 2 ^ c`, while adding the `|F|` petals of width `c - |H| ≤ c - 1`
and `|H| ≤ c - 1` unit clauses adds at most `|F| · 2 ^ (c - 1) + 2 (c - 1) < |F| · 2 ^ c`.
Furthermore, because `reduce` eliminates every clause of the flower `F` on both branches, each
step increases the total clause count by at most `K` (`card_countingChild_le`,
`CountingBranchingRule.IsNodeWord.card_walk_le`).

A depth-first search of the counting branching tree (`CountingBranchingRule.searchStep`) keeps a
stack of states and a `cap`-bounded `ℕ` accumulator. Started from `(s :: rest, acc)`, after `N`
steps (with `N + 1 ≤ 2 * W.card` for the finset `W` of leaf words of `s`) the stack is back to
`rest` and the accumulator records `min cap (acc + ∑ w ∈ W, f (R.walk s w))`
(`CountingBranchingRule.exists_iterate_searchStep`). When `f` is additive across non-sparse
branches (in particular when `f` computes `modelCountOn declared` at the leaves), the leaf sum
equals the root value (`CountingBranchingRule.sum_leafWords_eq`,
`CountingBranchingRule.sum_leafWords_modelCountOn`).

At the list level, `Cslib.Logic.PL.CNF.Sparsification.countingRule` instantiates
`CountingBranchingRule` on `{ψ : CNF V // CountingNormalized k ψ}` using `countingNext θ k`.

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule`: a deterministic
  counting-sparsification branching rule.
* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.walk`, `.IsNodeWord`,
  `.IsLeafWord`: nodes and leaves of the counting branching tree.
* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.searchStep`: one step of the
  depth-first counting search with a capped `ℕ` accumulator.
* `Cslib.Logic.PL.CNF.Sparsification.countingRule`: the list-level counting branching rule on
  `{ψ : CNF V // CountingNormalized k ψ}`.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.potential_next_lt`: strict
  potential decrease on both counting branches when `∀ j, 1 ≤ j → 2 ≤ θ j`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.card_countingChild_le`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.IsNodeWord.card_walk_le`:
  each counting step increases the number of clauses by at most the width `K`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.exists_iterate_searchStep`:
  depth-first counting search visits every leaf within `2 * W.card` steps with stack height
  at most `h + 1` and accumulator bounded by `max acc cap`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.CountingBranchingRule.sum_leafWords_modelCountOn`:
  the sum of `modelCountOn declared` over all leaf words equals the root `modelCountOn declared`.

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

/-- One step of the depth-first counting search of the branching tree, on a stack of states and a
`cap`-bounded `ℕ` accumulator: a sparse state on top is popped and `f s` is added to the
accumulator (capped at `cap`); any other state on top is replaced by its `false` and `true`
counting children. -/
noncomputable def searchStep (cap : ℕ) (f : σ → ℕ) : List σ × ℕ → List σ × ℕ
  | ([], acc) => ([], acc)
  | (s :: rest, acc) =>
    open Classical in
    if Sparse θ (R.toClauseSet s) then (rest, min cap (acc + f s))
    else (R.next s false :: R.next s true :: rest, acc)

variable {R}

/-- **Termination.** When `∀ j, 1 ≤ j → 2 ≤ θ j`, each counting branching step strictly decreases
the potential. -/
theorem potential_next_lt (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j) {s : σ}
    (hs : ¬ Sparse θ (R.toClauseSet s)) (b : Bool) :
    potential (R.toClauseSet (R.next s b)) < potential (R.toClauseSet s) := by
  obtain ⟨c, H, hch, hnext⟩ := R.exists_choice_next s hs
  rw [hnext]
  exact potential_countingChild_lt hθ hch.1 b

/-- **Additive model-count conservation.** At any non-sparse state, the declared-variable model
count equals the sum of the model counts of its two children. -/
theorem modelCountOn_next {s : σ} (hs : ¬ Sparse θ (R.toClauseSet s)) (declared : Finset V) :
    (R.toClauseSet s).toCNF.modelCountOn declared =
      (R.toClauseSet (R.next s false)).toCNF.modelCountOn declared +
      (R.toClauseSet (R.next s true)).toCNF.modelCountOn declared := by
  obtain ⟨c, H, -, hnext⟩ := R.exists_choice_next s hs
  rw [hnext false, hnext true]
  exact modelCountOn_countingChild (R.toClauseSet s) c H declared

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

/-- The only leaf word of a sparse state is the empty word. -/
private theorem IsLeafWord.eq_nil {s : σ} (hs : Sparse θ (R.toClauseSet s)) {w : List Bool}
    (hw : R.IsLeafWord s w) : w = [] := by
  cases w with
  | nil => rfl
  | cons b w => exact absurd hs hw.1

/-- Every state has a leaf word when `∀ j, 1 ≤ j → 2 ≤ θ j`. -/
theorem exists_isLeafWord (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j) (s : σ) :
    ∃ w, R.IsLeafWord s w := by
  induction h : potential (R.toClauseSet s) using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    by_cases hs : Sparse θ (R.toClauseSet s)
    · exact ⟨[], hs⟩
    · obtain ⟨w, hw⟩ := ih _ (h ▸ potential_next_lt hθ hs false) (R.next s false) rfl
      exact ⟨false :: w, hs, hw⟩

/-- Node words preserve clause width `≤ k` when `1 ≤ k`. -/
theorem IsNodeWord.card_le_of_mem_walk (hθ : ∀ j, 1 ≤ θ j) {k : ℕ} (_hk1 : 1 ≤ k) {s : σ}
    (hk : ∀ C ∈ R.toClauseSet s, C.card ≤ k) {w : List Bool} (hw : R.IsNodeWord s w) :
    ∀ C ∈ R.toClauseSet (R.walk s w), C.card ≤ k := by
  induction w generalizing s with
  | nil => exact hk
  | cons b w ih =>
    obtain ⟨c, H, hch, hnext⟩ := R.exists_choice_next s hw.1
    refine ih (fun C hC => ?_) hw.2
    rw [hnext b] at hC
    exact card_le_of_mem_countingChild hch.1.1 hch.1.2.1 (hch.1.flower_nonempty hθ) hk hC

/-- Along a node word `w` from a state of width `≤ k` (`1 ≤ k`), the number of clauses increases by
at most `k * w.length`. -/
theorem IsNodeWord.card_walk_le (hθ : ∀ j, 1 ≤ θ j) {k : ℕ} (_hk1 : 1 ≤ k) {s : σ}
    (hk : ∀ C ∈ R.toClauseSet s, C.card ≤ k) {w : List Bool} (hw : R.IsNodeWord s w) :
    (R.toClauseSet (R.walk s w)).card ≤ (R.toClauseSet s).card + k * w.length := by
  induction w generalizing s with
  | nil => simp [walk]
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
    simp only [walk, List.length_cons]
    calc (R.toClauseSet (R.walk (R.next s b) w)).card
        ≤ (R.toClauseSet (R.next s b)).card + k * w.length := hih
      _ ≤ ((R.toClauseSet s).card + k) + k * w.length := Nat.add_le_add_right hcard_next _
      _ = (R.toClauseSet s).card + k * (w.length + 1) := by ring

/-- Node words preserve declared-variable support containment. -/
theorem IsNodeWord.support_walk (hθ : ∀ j, 1 ≤ θ j) {s : σ} {declared : Finset V}
    (hU : ∀ C ∈ R.toClauseSet s, ∀ l ∈ C, l.1 ∈ declared) {w : List Bool}
    (hw : R.IsNodeWord s w) :
    ∀ C ∈ R.toClauseSet (R.walk s w), ∀ l ∈ C, l.1 ∈ declared := by
  induction w generalizing s with
  | nil => exact hU
  | cons b w ih =>
    obtain ⟨c, H, hch, hnext⟩ := R.exists_choice_next s hw.1
    refine ih (fun C hC l hl => ?_) hw.2
    rw [hnext b] at hC
    obtain ⟨D, hD⟩ := hch.1.flower_nonempty hθ
    have hHD : H ⊆ D := (mem_flower.mp hD).2.2
    have hDψ : D ∈ R.toClauseSet s := flower_subset _ _ _ hD
    exact support_countingChild (R.toClauseSet s) c H declared hU
      (fun a ha => hU D hDψ a (hHD ha)) b C hC l hl

private theorem min_add_assoc (cap a b c : ℕ) :
    min cap (min cap (a + b) + c) = min cap (a + (b + c)) := by
  omega

open Classical in
/-- **Depth-first counting search.** Started from a state `s` above `rest` with accumulator
`acc ≤ cap`, the search takes `N` steps (`N + 1 ≤ 2 * W.card` for the finset `W` of all leaf words
of `s`) to return to `rest`, with accumulator `min cap (acc + ∑ w ∈ W, f (R.walk s w))`. If all
leaf words of `s` have length at most `h`, the stack above `rest` has height at most `h + 1` at
every intermediate step `i ≤ N` and the accumulator remains at most `cap`. -/
theorem exists_iterate_searchStep (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    (cap : ℕ) (f : σ → ℕ) (s : σ) {h : ℕ} (hh : ∀ w, R.IsLeafWord s w → w.length ≤ h) :
    ∃ W : Finset (List Bool), (∀ w, w ∈ W ↔ R.IsLeafWord s w) ∧ ∃ N, N + 1 ≤ 2 * W.card ∧
      ∀ rest acc, acc ≤ cap →
        (R.searchStep cap f)^[N] (s :: rest, acc) =
          (rest, min cap (acc + ∑ w ∈ W, f (R.walk s w))) ∧
        ∀ i ≤ N, ∃ stk acc', (R.searchStep cap f)^[i] (s :: rest, acc) = (stk ++ rest, acc') ∧
          stk.length ≤ h + 1 ∧ acc' ≤ cap ∧
          ∀ t ∈ stk, ∃ w, R.IsNodeWord s w ∧ w.length ≤ h ∧ R.walk s w = t := by
  classical
  induction hp : potential (R.toClauseSet s) using Nat.strong_induction_on generalizing s h with
  | _ n ih =>
    by_cases hs : Sparse θ (R.toClauseSet s)
    · refine ⟨{[]}, fun w => ?_, 1, by simp, fun rest acc hacc => ⟨?_, fun i hi => ?_⟩⟩
      · simp only [mem_singleton]
        exact ⟨fun h => h ▸ hs, fun hw => hw.eq_nil hs⟩
      · simp only [Function.iterate_one, searchStep, hs, ↓reduceIte, sum_singleton, walk]
      · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
        · exact ⟨[s], acc, rfl, by simp, hacc,
            fun t ht => ⟨[], trivial, Nat.zero_le h, (List.mem_singleton.mp ht).symm⟩⟩
        · refine ⟨[], min cap (acc + f s), ?_, by simp, Nat.min_le_left _ _, by simp⟩
          simp only [Function.iterate_one, searchStep, hs, ↓reduceIte, List.nil_append]
    · have hlt (b : Bool) : potential (R.toClauseSet (R.next s b)) < n :=
        hp ▸ potential_next_lt hθ hs b
      have hh' (b : Bool) : ∀ w, R.IsLeafWord (R.next s b) w → w.length ≤ h - 1 := fun w hw => by
        have := hh (b :: w) ⟨hs, hw⟩
        simp only [List.length_cons] at this
        omega
      obtain ⟨u, hu⟩ := exists_isLeafWord (R := R) hθ s
      have hh1 : 1 ≤ h := by
        cases u with
        | nil => exact absurd hu hs
        | cons b u => have := hh _ hu; simp only [List.length_cons] at this; omega
      obtain ⟨W₀, hW₀, N₀, hN₀, h₀⟩ := ih _ (hlt false) (R.next s false) (hh' false) rfl
      obtain ⟨W₁, hW₁, N₁, hN₁, h₁⟩ := ih _ (hlt true) (R.next s true) (hh' true) rfl
      have hstep (rest : List σ) (acc : ℕ) : R.searchStep cap f (s :: rest, acc) =
          (R.next s false :: R.next s true :: rest, acc) := by
        simp only [searchStep, hs, ↓reduceIte]
      have hdisj : Disjoint (W₀.image (false :: ·)) (W₁.image (true :: ·)) := by
        rw [Finset.disjoint_left]
        intro w hw₀ hw₁
        obtain ⟨u₀, -, rfl⟩ := mem_image.mp hw₀
        obtain ⟨u₁, -, hu₁⟩ := mem_image.mp hw₁
        exact Bool.false_ne_true (List.head_eq_of_cons_eq hu₁).symm
      set W := W₀.image (false :: ·) ∪ W₁.image (true :: ·)
      have hW_sum : ∑ w ∈ W, f (R.walk s w) =
          (∑ u ∈ W₀, f (R.walk (R.next s false) u)) +
          (∑ u ∈ W₁, f (R.walk (R.next s true) u)) := by
        rw [sum_union hdisj, sum_image (fun _ _ _ _ h => List.cons_injective h),
          sum_image (fun _ _ _ _ h => List.cons_injective h)]
        rfl
      refine ⟨W, fun w => ?_, N₁ + (N₀ + 1), ?_,
        fun rest acc hacc => ⟨?_, fun i hi => ?_⟩⟩
      · constructor
        · intro hw
          rcases mem_union.mp hw with hw | hw
          · obtain ⟨u, hu, rfl⟩ := mem_image.mp hw
            exact ⟨hs, (hW₀ u).mp hu⟩
          · obtain ⟨u, hu, rfl⟩ := mem_image.mp hw
            exact ⟨hs, (hW₁ u).mp hu⟩
        · intro hw
          cases w with
          | nil => exact absurd hw hs
          | cons b u =>
            cases b
            · exact mem_union_left _ (mem_image.mpr ⟨u, (hW₀ u).mpr hw.2, rfl⟩)
            · exact mem_union_right _ (mem_image.mpr ⟨u, (hW₁ u).mpr hw.2, rfl⟩)
      · rw [card_union_of_disjoint hdisj, card_image_of_injective _ List.cons_injective,
          card_image_of_injective _ List.cons_injective]
        omega
      · have h₀_step := (h₀ (R.next s true :: rest) acc hacc).1
        have h₁_step := (h₁ rest (min cap (acc + ∑ w ∈ W₀, f (R.walk (R.next s false) w)))
          (Nat.min_le_left _ _)).1
        rw [Function.iterate_add_apply, Function.iterate_succ_apply, hstep, h₀_step, h₁_step,
          min_add_assoc, hW_sum]
      · rcases Nat.eq_zero_or_pos i with rfl | hi0
        · exact ⟨[s], acc, rfl, by simp, hacc,
            fun t ht => ⟨[], trivial, Nat.zero_le h, (List.mem_singleton.mp ht).symm⟩⟩
        by_cases hi₀ : i ≤ N₀ + 1
        · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
          obtain ⟨stk, acc', heq, hlen, hacc', hmem⟩ :=
            (h₀ (R.next s true :: rest) acc hacc).2 j (by omega)
          refine ⟨stk ++ [R.next s true], acc', ?_, ?_, hacc', fun t ht => ?_⟩
          · rw [Function.iterate_succ_apply, hstep, heq, List.append_assoc, List.singleton_append]
          · simp only [List.length_append, List.length_singleton]
            omega
          · rcases List.mem_append.mp ht with ht | ht
            · obtain ⟨w, hw, hwlen, rfl⟩ := hmem t ht
              exact ⟨false :: w, ⟨hs, hw⟩, by simp only [List.length_cons]; omega, rfl⟩
            · exact ⟨[true], ⟨hs, trivial⟩, by simp only [List.length_singleton]; omega,
                (List.mem_singleton.mp ht).symm⟩
        · obtain ⟨j, rfl⟩ : ∃ j, i = j + (N₀ + 1) := ⟨i - (N₀ + 1), by omega⟩
          obtain ⟨stk, acc', heq, hlen, hacc', hmem⟩ :=
            (h₁ rest (min cap (acc + ∑ w ∈ W₀, f (R.walk (R.next s false) w)))
              (Nat.min_le_left _ _)).2 j (by omega)
          refine ⟨stk, acc', ?_, by omega, hacc', fun t ht => ?_⟩
          · rw [Function.iterate_add_apply, Function.iterate_succ_apply, hstep,
              (h₀ _ acc hacc).1, heq]
          · obtain ⟨w, hw, hwlen, rfl⟩ := hmem t ht
            exact ⟨true :: w, ⟨hs, hw⟩, by simp only [List.length_cons]; omega, rfl⟩

/-- If `M : σ → ℕ` is additive across non-sparse steps
(`M t = M (R.next t false) + M (R.next t true)`) and `f` agrees with `M` on the leaves of `s`, then
the sum of `f (R.walk s w)` over any finset `W` containing exactly the leaf words of `s` equals
`M s`. -/
theorem sum_leafWords_eq (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    {M f : σ → ℕ}
    (hM : ∀ t, ¬ Sparse θ (R.toClauseSet t) → M t = M (R.next t false) + M (R.next t true))
    (s : σ) (hf : ∀ w, R.IsLeafWord s w → f (R.walk s w) = M (R.walk s w))
    {W : Finset (List Bool)} (hW : ∀ w, w ∈ W ↔ R.IsLeafWord s w) :
    ∑ w ∈ W, f (R.walk s w) = M s := by
  classical
  induction hp : potential (R.toClauseSet s) using Nat.strong_induction_on generalizing s W with
  | _ n ih =>
    by_cases hs : Sparse θ (R.toClauseSet s)
    · have hWeq : W = {[]} := by
        ext w
        rw [hW, mem_singleton]
        exact ⟨fun hw => hw.eq_nil hs, fun h => h ▸ hs⟩
      rw [hWeq, sum_singleton]
      exact hf [] hs
    · have hlt (b : Bool) : potential (R.toClauseSet (R.next s b)) < n :=
        hp ▸ potential_next_lt hθ hs b
      let W₀ := (W.filter fun w => w.head? = some false).image List.tail
      let W₁ := (W.filter fun w => w.head? = some true).image List.tail
      have hW₀ (u : List Bool) : u ∈ W₀ ↔ R.IsLeafWord (R.next s false) u := by
        simp only [W₀, mem_image, mem_filter]
        constructor
        · rintro ⟨w, ⟨hwW, hwhead⟩, rfl⟩
          cases w with
          | nil => simp at hwhead
          | cons b u' =>
            simp only [List.head?_cons, Option.some.injEq] at hwhead
            subst hwhead
            exact ((hW (false :: u')).mp hwW).2
        · intro hu
          exact ⟨false :: u, ⟨(hW (false :: u)).mpr ⟨hs, hu⟩, rfl⟩, rfl⟩
      have hW₁ (u : List Bool) : u ∈ W₁ ↔ R.IsLeafWord (R.next s true) u := by
        simp only [W₁, mem_image, mem_filter]
        constructor
        · rintro ⟨w, ⟨hwW, hwhead⟩, rfl⟩
          cases w with
          | nil => simp at hwhead
          | cons b u' =>
            simp only [List.head?_cons, Option.some.injEq] at hwhead
            subst hwhead
            exact ((hW (true :: u')).mp hwW).2
        · intro hu
          exact ⟨true :: u, ⟨(hW (true :: u)).mpr ⟨hs, hu⟩, rfl⟩, rfl⟩
      have hdisj : Disjoint (W₀.image (false :: ·)) (W₁.image (true :: ·)) := by
        rw [Finset.disjoint_left]
        intro w hw₀ hw₁
        obtain ⟨u₀, -, rfl⟩ := mem_image.mp hw₀
        obtain ⟨u₁, -, hu₁⟩ := mem_image.mp hw₁
        exact Bool.false_ne_true (List.head_eq_of_cons_eq hu₁).symm
      have hWeq : W = W₀.image (false :: ·) ∪ W₁.image (true :: ·) := by
        ext w
        rw [mem_union, mem_image, mem_image, hW]
        constructor
        · intro hw
          cases w with
          | nil => exact absurd hw hs
          | cons b u =>
            cases b
            · exact Or.inl ⟨u, (hW₀ u).mpr hw.2, rfl⟩
            · exact Or.inr ⟨u, (hW₁ u).mpr hw.2, rfl⟩
        · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
          · exact ⟨hs, (hW₀ u).mp hu⟩
          · exact ⟨hs, (hW₁ u).mp hu⟩
      rw [hWeq, sum_union hdisj, sum_image (fun _ _ _ _ h => List.cons_injective h),
        sum_image (fun _ _ _ _ h => List.cons_injective h)]
      have ih₀ := ih _ (hlt false) (R.next s false) (fun u hu => hf (false :: u) ⟨hs, hu⟩) hW₀ rfl
      have ih₁ := ih _ (hlt true) (R.next s true) (fun u hu => hf (true :: u) ⟨hs, hu⟩) hW₁ rfl
      change (∑ x ∈ W₀, f (R.walk (R.next s false) x)) +
        (∑ x ∈ W₁, f (R.walk (R.next s true) x)) = M s
      rw [ih₀, ih₁, ← hM s hs]

/-- **Leaf model-count partition.** If `f` computes `(R.toClauseSet ·).toCNF.modelCountOn declared`
on every leaf of `s`, then the sum of `f (R.walk s w)` over the leaf words of `s` equals
`(R.toClauseSet s).toCNF.modelCountOn declared`. -/
theorem sum_leafWords_modelCountOn (hθ : ∀ j, 1 ≤ j → 2 ≤ θ j)
    (declared : Finset V) {f : σ → ℕ} (s : σ)
    (hf : ∀ w, R.IsLeafWord s w →
      f (R.walk s w) = (R.toClauseSet (R.walk s w)).toCNF.modelCountOn declared)
    {W : Finset (List Bool)} (hW : ∀ w, w ∈ W ↔ R.IsLeafWord s w) :
    ∑ w ∈ W, f (R.walk s w) = (R.toClauseSet s).toCNF.modelCountOn declared :=
  sum_leafWords_eq hθ (fun _ ht => modelCountOn_next ht declared) s hf hW

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
    ∀ C ∈ ((countingRule hθ hk).walk s w).1, ∀ l ∈ C, l.1 ∈ declared := by
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
    (hf : ∀ w, (countingRule hθ1 hk).IsLeafWord s w →
      f ((countingRule hθ1 hk).walk s w) =
        ((countingRule hθ1 hk).walk s w).1.modelCountOn declared)
    {W : Finset (List Bool)} (hW : ∀ w, w ∈ W ↔ (countingRule hθ1 hk).IsLeafWord s w) :
    ∑ w ∈ W, f ((countingRule hθ1 hk).walk s w) = s.1.modelCountOn declared :=
  CountingBranchingRule.sum_leafWords_eq (R := countingRule hθ1 hk)
    (M := fun t => t.1.modelCountOn declared) hθ2
    (fun t _ => modelCountOn_countingNext t.2.toNormalized declared) s hf hW

end Cslib.Logic.PL.CNF.Sparsification
