/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.OptimalBST.Knuth

/-!
# Optimal binary search trees: worked instances

These kernel-checked examples (using no `native_decide`) exercise:

1. The five-key instance of CLRS Section 15.5 (weights scaled by `100`): both algorithms return
   cost `235`, which is CLRS's expected cost `2.75` minus the failure weights `∑ q = 0.40`; the
   cubic algorithm scans `35 = 5 · 6 · 7 / 6` candidate roots and Knuth's `28 ≤ 2 · 5²`.
2. Brute force over all trees: `allTrees` enumerates every binary search tree on `i + 1, …, j`
   (`mem_allTrees`), and for `n ≤ 4` the cost returned by each algorithm is at most every tree's
   cost and is attained by the returned tree.
3. The hypotheses of Knuth's speedup are needed: for a weight violating both, one that is monotone
   on intervals but violates the quadrangle inequality, and one (integer-valued) that satisfies the
   quadrangle inequality but is not monotone, Knuth's algorithm returns a cost above the optimum,
   while the cubic algorithm stays optimal.
-/

public section

namespace ComplexityTests.OptimalBST

open Cslib.Algorithms.Lean.OptimalBST

/-- All trees on the keys `i + 1, …, j`, given fuel at least `j - i`. -/
def allTrees : ℕ → ℕ → ℕ → List (BinaryTree ℕ)
  | 0, _, _ => [.nil]
  | f + 1, i, j =>
    if i < j then
      (List.range' (i + 1) (j - i)).flatMap fun k =>
        (allTrees f i (k - 1)).flatMap fun l => (allTrees f k j).map fun r => .node k l r
    else [.nil]

/-- The enumeration is complete. -/
theorem mem_allTrees {i j : ℕ} {t : BinaryTree ℕ} (h : IsBST i j t) :
    ∀ f, j - i ≤ f → t ∈ allTrees f i j := by
  induction h with
  | nil i =>
    intro f _
    cases f with
    | zero => exact List.mem_singleton_self _
    | succ f => simp only [allTrees, lt_irrefl, ↓reduceIte, List.mem_singleton]
  | @node i j k l r hik hkj _ _ ihl ihr =>
    intro f hf
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [allTrees, show i < j by omega, ↓reduceIte, List.mem_flatMap, List.mem_map,
      List.mem_range'_1]
    exact ⟨k, ⟨by omega, by omega⟩, l, ihl f (by omega), r, ihr f (by omega), rfl⟩

example : (allTrees 4 0 4).length = 14 := by decide

/-! ### The CLRS instance -/

/-- CLRS Section 15.5 access weights, scaled by `100`. -/
def p : ℕ → ℕ := fun k => [0, 15, 10, 5, 10, 20].getD k 0

/-- CLRS Section 15.5 failure weights, scaled by `100`. -/
def q : ℕ → ℕ := fun g => [5, 10, 5, 5, 5, 10].getD g 0

/-- The CLRS weight. -/
abbrev wC : ℕ → ℕ → ℕ := knuthWeight p q

example : QuadrangleIneq wC ∧ MonotoneOnIntervals wC :=
  ⟨quadrangleIneq_knuthWeight p q,
    monotoneOnIntervals_knuthWeight (fun _ => Nat.zero_le _) (fun _ => Nat.zero_le _)⟩

example : (plainBST wC 5).ret.cost = 235 := by decide
example : (knuthBST wC 5).ret.cost = 235 := by decide
example : (knuthBST wC 5).ret.cost + ∑ g ∈ Finset.range 6, q g = 275 := by decide

/-- The tree read off the largest optimal roots. CLRS's Figure 15.9(b) breaks the tie at the root
the other way (root `k₂`), at the same cost. -/
def optTreeC : BinaryTree ℕ :=
  .node 4 (.node 2 (.node 1 .nil .nil) (.node 3 .nil .nil)) (.node 5 .nil .nil)

/-- CLRS's tree of Figure 15.9(b). -/
def clrsTree : BinaryTree ℕ :=
  .node 2 (.node 1 .nil .nil) (.node 5 (.node 4 (.node 3 .nil .nil) .nil) .nil)

example : (knuthBST wC 5).ret.tree = optTreeC := by decide +kernel
example : treeCost wC 0 5 optTreeC = 235 ∧ treeCost wC 0 5 clrsTree = 235 := by decide
example : IsBST 0 5 clrsTree :=
  .node (by decide) (by decide) (.node (by decide) (by decide) (.nil 0) (.nil 1))
    (.node (by decide) (by decide)
      (.node (by decide) (by decide) (.node (by decide) (by decide) (.nil 2) (.nil 3)) (.nil 4))
      (.nil 5))

example : (plainBST wC 5).time = 35 := by decide
example : (knuthBST wC 5).time = 28 := by decide

/-- Brute force: for `n ≤ 4` the dynamic program is at most the cost of every tree and is
attained by its tree. -/
example : ∀ n ≤ 4, (∀ t ∈ allTrees n 0 n, (plainBST wC n).ret.cost ≤ treeCost wC 0 n t) ∧
    (plainBST wC n).ret.tree ∈ allTrees n 0 n ∧
    treeCost wC 0 n (plainBST wC n).ret.tree = (plainBST wC n).ret.cost := by decide

/-- Brute force for Knuth's algorithm. -/
example : ∀ n ≤ 4, (∀ t ∈ allTrees n 0 n, (knuthBST wC n).ret.cost ≤ treeCost wC 0 n t) ∧
    (knuthBST wC n).ret.tree ∈ allTrees n 0 n ∧
    treeCost wC 0 n (knuthBST wC n).ret.tree = (knuthBST wC n).ret.cost := by decide

/-! ### The hypotheses of Knuth's speedup are needed -/

/-- A nonnegative weight violating both hypotheses. -/
def wBad : ℕ → ℕ → ℕ := fun i j => if i = 1 ∧ j = 2 then 2 else if i = 2 ∧ j = 3 then 1 else 0

example : (plainBST wBad 3).ret.cost = 0 ∧ (knuthBST wBad 3).ret.cost = 1 := by decide

example : ¬ QuadrangleIneq wBad := fun h =>
  absurd (h (show 1 ≤ 2 by decide) (show 2 ≤ 2 by decide) (show 2 ≤ 3 by decide)) (by decide)

example : ¬ MonotoneOnIntervals wBad := fun h =>
  absurd (h (show 1 ≤ 1 by decide) (show 1 ≤ 2 by decide) (show 2 ≤ 3 by decide)) (by decide)

/-- Look up a `5 × 5` table, clamping the indices to `4`. -/
def table5 {γ : Type*} (t : List (List γ)) (z : γ) (i j : ℕ) : γ :=
  (t.getD (min i 4) []).getD (min j 4) z

theorem table5_clamp {γ : Type*} (t : List (List γ)) (z : γ) (i j : ℕ) :
    table5 t z i j = table5 t z (min i 4) (min j 4) := by
  rw [table5, table5, min_eq_left (min_le_right i 4), min_eq_left (min_le_right j 4)]

/-- A nonnegative weight that is monotone on intervals but violates the quadrangle inequality. -/
def wMono : ℕ → ℕ → ℕ :=
  table5 [[0, 2, 3, 4, 9], [0, 0, 0, 2, 2], [0, 0, 0, 0, 2], [0, 0, 0, 0, 1], [0, 0, 0, 0, 0]] 0

theorem monotoneOnIntervals_wMono : MonotoneOnIntervals wMono := by
  have H : ∀ a b c d : Fin 5, a.val ≤ b.val → b.val ≤ c.val → c.val ≤ d.val →
      wMono b c ≤ wMono a d := by decide
  intro i i' j j' h₁ h₂ h₃
  rw [wMono, table5_clamp, table5_clamp _ _ i]
  exact H ⟨_, by omega⟩ ⟨_, by omega⟩ ⟨_, by omega⟩ ⟨_, by omega⟩ (by dsimp only; omega)
    (by dsimp only; omega) (by dsimp only; omega)

example : ¬ QuadrangleIneq wMono := fun h =>
  absurd (h (show 0 ≤ 1 by decide) (show 1 ≤ 2 by decide) (show 2 ≤ 3 by decide)) (by decide)

example : (plainBST wMono 4).ret.cost = 12 ∧ (knuthBST wMono 4).ret.cost = 13 := by decide

/-- An integer weight satisfying the quadrangle inequality but not monotone on intervals. -/
def wQI : ℕ → ℕ → ℤ :=
  table5 [[0, -1, 3, 7, 6], [0, 0, 2, 5, 4], [0, 0, 0, 3, 2], [0, 0, 0, 0, -1], [0, 0, 0, 0, 0]] 0

theorem quadrangleIneq_wQI : QuadrangleIneq wQI := by
  have H : ∀ a b c d : Fin 5, a.val ≤ b.val → b.val ≤ c.val → c.val ≤ d.val →
      wQI a c + wQI b d ≤ wQI a d + wQI b c := by decide
  intro i i' j j' h₁ h₂ h₃
  rw [wQI, table5_clamp _ _ i j, table5_clamp _ _ i' j', table5_clamp _ _ i j',
    table5_clamp _ _ i' j]
  exact H ⟨_, by omega⟩ ⟨_, by omega⟩ ⟨_, by omega⟩ ⟨_, by omega⟩ (by dsimp only; omega)
    (by dsimp only; omega) (by dsimp only; omega)

example : ¬ MonotoneOnIntervals wQI := fun h =>
  absurd (h (show 0 ≤ 0 by decide) (show 0 ≤ 0 by decide) (show 0 ≤ 1 by decide)) (by decide)

example : (plainBST wQI 4).ret.cost = 6 ∧ (knuthBST wQI 4).ret.cost = 7 := by decide

/-- The cubic algorithm needs no hypothesis: brute force on the two weights above. -/
example : ∀ t ∈ allTrees 4 0 4, (plainBST wMono 4).ret.cost ≤ treeCost wMono 0 4 t := by decide
example : ∀ t ∈ allTrees 4 0 4, (plainBST wQI 4).ret.cost ≤ treeCost wQI 0 4 t := by decide

end ComplexityTests.OptimalBST
