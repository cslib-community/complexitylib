/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.SplayTree.Stateful
public import ComplexityTests.OrderedSet

/-!
# Worked Splay-Tree Examples and Non-Vacuity Witnesses

These kernel-checked examples (using no `native_decide`) exercise:

1. Bottom-up `zig`, `zig-zig`, and `zig-zag` splaying, including path compression on a degenerate
   7-node spine where splaying the deepest leaf halves the spine depth via paired `zig-zig`
   rotations (unlike single-rotation move-to-root).
2. Exact rotation counts, `rotations + 1 = searchVisits` / `minimumVisits` correspondence on
   non-empty trees, and last-visited-node splaying on unsuccessful searches.
3. Total set-idempotent `insert` and `erase`, `split`, `join`, `minimum`, and `successor` across
   empty, present, absent, and boundary keys.
4. Non-vacuity instances of Sleator–Tarjan's weighted **Access Lemma**
   (`splay_splayTime_amortized_le_of_mem`), **Balance Theorem** (`splaySeqTime_le_balance`), and
   **Static Optimality Theorem** (`splaySeqTime_le_static_optimality`) on skewed access sequences.
5. Self-adjusting `OrderedSet.spec` execution (`SplayTree.run`), showing that read queries
   restructure the concrete tree (reducing repeat-query rotations to `0`) while preserving
   `Finset` semantics and satisfying both continuous (`realHistoryCost`) and discrete
   (`amortizedCharge`) amortized bounds.
-/

public section

namespace ComplexityTests.SplayTree

open Cslib.Algorithms.Lean.SplayTree Cslib.OrderedSet Cslib.Stateful
open Cslib.Algorithms.Lean.SearchTree (elements Ordered Rep searchVisits minimumVisits)

/-- Degenerate 7-node right spine `1 → 2 → 3 → 4 → 5 → 6 → 7` of height `7`. -/
private def rightSpine7 : BinaryTree ℕ :=
  .node 1 .nil
    (.node 2 .nil
      (.node 3 .nil
        (.node 4 .nil
          (.node 5 .nil
            (.node 6 .nil
              (.node 7 .nil .nil))))))

private theorem ordered_rightSpine7 : Ordered rightSpine7 := by
  unfold rightSpine7
  simp [Ordered, elements]

private theorem ne_nil_rightSpine7 : rightSpine7 ≠ .nil := by decide

/-- Unbalanced 3-node left-right zig-zag tree `30 → 10 → 20` of height `3`. -/
private def zigzagTree : BinaryTree ℕ :=
  .node 30 (.node 10 .nil (.node 20 .nil .nil)) .nil

-- 1. `zig`, `zig-zig` path compression, and `zig-zag` balancing:
-- Splaying leaf `7` in `rightSpine7` (height 7) performs 3 `zig-zig` steps (6 rotations), moves `7`
-- to the root, and compresses height from `7` to `5`; splaying the new deepest leaf `5` next
-- compresses height further to `4`.
-- Splaying `20` in `zigzagTree` performs 1 `zig-zag` step (2 rotations) to yield height `2`.
example :
    rightSpine7.height = 7 ∧
      (splay 7 rightSpine7).rotations = 6 ∧
      rootKey (splay 7 rightSpine7).tree = some 7 ∧
      (splay 7 rightSpine7).tree.height = 5 ∧
      (splay 5 (splay 7 rightSpine7).tree).tree.height = 4 ∧
      Ordered (splay 7 rightSpine7).tree ∧
      elements (splay 7 rightSpine7).tree = ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ) ∧
      (splay 20 zigzagTree).rotations = 2 ∧
      (splay 20 zigzagTree).tree = .node 20 (.node 10 .nil .nil) (.node 30 .nil .nil) ∧
      (splay 20 zigzagTree).tree.height = 2 :=
  ⟨rfl, rfl, rfl, rfl, rfl,
   ordered_splay ordered_rightSpine7 7,
   by rw [elements_splay]; simp [rightSpine7, elements],
   rfl, rfl, rfl⟩

-- 2. Rotation-to-visit correspondence, empty/root-hit edge cases, and unsuccessful search splaying
-- the last visited node along the search path.
example :
    (splay 7 rightSpine7).rotations + 1 = searchVisits 7 rightSpine7 ∧
      (splay 1 rightSpine7).rotations = 0 ∧
      splayTime (splay 1 rightSpine7) = 1 ∧
      (splay 42 (.nil : BinaryTree ℕ)).rotations = 0 ∧
      (splayMin zigzagTree).rotations + 1 = minimumVisits zigzagTree ∧
      rootKey (splay 25 (.node 10 .nil (.node 30 .nil .nil))).tree = some 30 ∧
      (splay 25 (.node 10 .nil (.node 30 .nil .nil))).rotations = 1 :=
  ⟨rotations_splay_add_one_eq_searchVisits ne_nil_rightSpine7 7,
   rfl, rfl, rfl,
   rotations_splayMin_add_one_eq_minimumVisits (by decide),
   rfl, rfl⟩

-- 3. Self-adjusting `insert`, `erase`, `split`, `join`, `minimum`, and `successor`, including
-- duplicate-insert and absent-erase set-idempotence.
def build (xs : List ℕ) : BinaryTree ℕ :=
  (run .nil (insertAll xs)).tree

theorem ordered_build (xs : List ℕ) : Ordered (build xs) := by
  obtain ⟨_, ⟨hord, _⟩, _⟩ := run_correct_empty (insertAll xs)
  exact hord

theorem elements_build (xs : List ℕ) : elements (build xs) = xs.toFinset := by
  obtain ⟨_, ⟨_, helt⟩, _⟩ := run_correct_empty (insertAll xs)
  simpa only [build, insertAll_run, Finset.empty_union] using helt

example :
    let t := build [4, 1, 7, 3, 6, 2, 5]
    -- Duplicate insert leaves `elements` unchanged while splaying `3` to the root:
    rootKey (insert 3 t).tree = some 3 ∧
      elements (insert 3 t).tree = elements t ∧
      -- Absent erase leaves `elements` unchanged while splaying the last visited node:
      elements (erase 99 t).tree = elements t ∧
      Ordered (erase 4 t).tree ∧
      elements (erase 4 t).tree = ({1, 2, 3, 5, 6, 7} : Finset ℕ) ∧
      -- `split` partitions keys into `≤ 4` and `> 4`:
      elements (split 4 t).left = ({1, 2, 3, 4} : Finset ℕ) ∧
      elements (split 4 t).right = ({5, 6, 7} : Finset ℕ) ∧
      -- `join` recombines disjoint split halves:
      elements (join (split 4 t).left (split 4 t).right).tree =
        ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ) ∧
      -- Queries on present, absent, maximal, and empty cases:
      (minimum t).answer = some 1 ∧
      (minimum (.nil : BinaryTree ℕ)).answer = none ∧
      (successor 4 t).answer = some 5 ∧
      (successor 7 t).answer = none ∧
      rootKey (successor 7 t).tree = some 7 := by
  intro t
  have ht : Ordered t := ordered_build _
  have het : elements t = ({1, 2, 3, 4, 5, 6, 7} : Finset ℕ) := by
    rw [elements_build]; decide
  refine ⟨rfl, ?_, ?_, ordered_erase ht 4, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · rw [elements_insert, het]; decide
  · rw [elements_erase ht, het]; decide
  · rw [elements_erase ht, het]; decide
  · rw [elements_split_left ht, het]; decide
  · rw [elements_split_right ht, het]; decide
  · rw [elements_join, elements_split_left ht, elements_split_right ht, het]; decide

-- 4. Non-vacuity witnesses for Sleator–Tarjan's Access Lemma, Balance Theorem, and Static
-- Optimality Theorem.

-- 4a. Weighted Access Lemma with non-uniform positive weights `w x = x + 1` on `rightSpine7`:
private noncomputable def linearWeight (x : ℕ) : ℝ := (x : ℝ) + 1

private theorem linearWeight_pos (x : ℕ) : 0 < linearWeight x := by
  simp only [linearWeight]
  positivity

example :
    (splayTime (splay 7 rightSpine7) : ℝ) +
        potential linearWeight (splay 7 rightSpine7).tree -
        potential linearWeight rightSpine7 ≤
      3 * Real.logb 2 (subtreeWeight linearWeight rightSpine7 / linearWeight 7) + 1 :=
  splay_splayTime_amortized_le_of_mem linearWeight_pos ordered_rightSpine7 (by decide)

-- 4b. Balance Theorem on `rightSpine7` across successful and unsuccessful accesses:
private def mixedSeq : List ℕ := [7, 1, 99, 4, 0, 7]

example :
    (splaySeqTime mixedSeq rightSpine7 : ℝ) ≤
      (3 * (mixedSeq.length : ℝ) + (elements rightSpine7).card) *
        Real.logb 2 (elements rightSpine7).card + mixedSeq.length :=
  splaySeqTime_le_balance mixedSeq ordered_rightSpine7 ne_nil_rightSpine7

-- 4c. Static Optimality Theorem on `rightSpine7` with a skewed access sequence where key `7`
-- is accessed 6 times and keys `1..6` once each (`m = 12`):
private def skewedSeq : List ℕ := [7, 7, 7, 7, 7, 1, 2, 3, 4, 5, 6, 7]

example :
    (splaySeqTime skewedSeq rightSpine7 : ℝ) ≤ (skewedSeq.length : ℝ) +
      4 * ∑ y ∈ elements rightSpine7,
        (skewedSeq.count y : ℝ) * Real.logb 2 ((skewedSeq.length : ℝ) / skewedSeq.count y) :=
  splaySeqTime_le_static_optimality skewedSeq ordered_rightSpine7 (by decide) (by decide)

-- 5. Self-adjusting `OrderedSet.spec` execution (`SplayTree.run`):
-- A read query `contains 7` on `rightSpine7` performs 6 rotations and restructures the tree so
-- `7` becomes the root; an immediate repeat `contains 7` performs 0 rotations, while both leave
-- the abstract `Finset` state unchanged.
private def repeatContains7 : (spec ℕ).Client (Bool × Bool) :=
  .liftBind (.contains 7) fun b1 =>
    .liftBind (.contains 7) fun b2 =>
      .pure (b1, b2)

example :
    let r := run rightSpine7 repeatContains7
    r.value = (true, true) ∧
      r.rotations = [6, 0] ∧
      rootKey r.tree = some 7 ∧
      Rep (elements rightSpine7) r.tree := by
  intro r
  obtain ⟨_, hrep, _⟩ :=
    run_correct repeatContains7 (s := elements rightSpine7) ⟨ordered_rightSpine7, rfl⟩
  exact ⟨rfl, rfl, rfl, hrep⟩

-- Shared adaptive `OrderedSet` clients (`insertAll`, `firstTwo`, `extractMin`) execute unchanged
-- on `SplayTree` with both real-valued (`realHistoryCost`) and discrete (`amortizedCharge`)
-- amortized bounds starting from `.nil`.
private def buildAndQueryClient : (spec ℕ).Client (Option ℕ × Option ℕ × Option ℕ) := do
  insertAll [1, 2, 3, 4, 5, 6, 7]
  let (a, b) ← firstTwo
  let c ← extractMin
  pure (a, b, c)

example :
    let r := run .nil buildAndQueryClient
    let (_, _, history) := (spec ℕ).runClient ∅ buildAndQueryClient
    r.value = (some 1, some 2, some 1) ∧
      elements r.tree = ({2, 3, 4, 5, 6, 7} : Finset ℕ) ∧
      (total id r.rotations : ℝ) ≤ realHistoryCost ∅ history ∧
      total id r.rotations ≤ (spec ℕ).totalCost amortizedCharge ∅ history := by
  intro r
  have hc := run_correct_empty buildAndQueryClient
  dsimp only at hc
  obtain ⟨_, ⟨_, helt_rep⟩, hcost⟩ := hc
  have hreal := executes_rotations_le_realHistoryCost_of_empty (run_exec buildAndQueryClient .nil)
  have helt :
      (let (_, finalState, _) := (spec ℕ).runClient ∅ buildAndQueryClient
       finalState) = ({2, 3, 4, 5, 6, 7} : Finset ℕ) := by decide
  dsimp only at helt
  exact ⟨rfl, helt_rep.trans helt, hreal, hcost⟩

end ComplexityTests.SplayTree
