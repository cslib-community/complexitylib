/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.Lean.AVLTree.Stateful
public import Complexity.Algorithms.Lean.SearchTree.Stateful
public import ComplexityTests.OrderedSet

/-!
# Worked AVL search-tree examples

These kernel-checked examples (using no `native_decide`) exercise:

1. Sorted insertion `[1, 2, 3, 4, 5, 6, 7]` versus median-first insertion `[4, 2, 6, 1, 3, 5, 7]`:
   unlike `SearchTree` (where sorted insertion degenerates to a spine of height `7`), `AVLTree`
   rebalances sorted insertion to height `3`, reducing worst-case `searchVisits` from `7` to `3`.
2. Single and double rotations (left-left, right-right, left-right, and right-left) on both
   insertion and deletion, together with tight Fibonacci/logarithmic boundary cases.
3. Shared `OrderedSet` adaptive clients (`extractMin`, `firstTwo`, `insertAll`) running unchanged
   over `AVLTree` with logarithmic `charge` bounds (`2 * Nat.log 2 (s.card + 1)`).
4. Necessity of `Balanced`: an ordered, height-consistent spine violates `Balanced` and exceeds
   `2 * Nat.log 2 ((elements t).card + 1)`.
-/

public section

namespace ComplexityTests.AVLTree

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.AVLTree Cslib.OrderedSet Cslib.Stateful

def build (xs : List ℕ) : AVLTree ℕ :=
  (run .nil (insertAll xs)).2.1

theorem valid_build (xs : List ℕ) : Valid (build xs) :=
  (run_correct (insertAll xs) rep_nil).2.1.valid

theorem elements_build (xs : List ℕ) : elements (build xs) = xs.toFinset := by
  have h := (run_correct (insertAll xs) rep_nil).2.1.elements_eq
  simpa only [build, insertAll_run, Finset.empty_union] using h

private def sortedSeven : AVLTree ℕ := build [1, 2, 3, 4, 5, 6, 7]
private def reverseSeven : AVLTree ℕ := build [7, 6, 5, 4, 3, 2, 1]
private def zigzagLR : AVLTree ℕ := build [30, 10, 20]
private def zigzagRL : AVLTree ℕ := build [10, 30, 20]

-- Sorted and reverse-sorted insertions rebalance to height 3 (versus height 7 in unbalanced
-- `SearchTree`), while left-right `[30, 10, 20]` and right-left `[10, 30, 20]` double rotations
-- produce height 2.
example :
    Valid sortedSeven ∧
      Valid reverseSeven ∧
      Valid zigzagLR ∧
      Valid zigzagRL ∧
      sortedSeven.cachedHeight = 3 ∧
      reverseSeven.cachedHeight = 3 ∧
      ((Cslib.Algorithms.Lean.SearchTree.run .nil (insertAll [1, 2, 3, 4, 5, 6, 7])).2.1).height =
        7 ∧
      searchVisits 7 sortedSeven = 3 ∧
      searchVisits 8 sortedSeven = 3 ∧
      zigzagLR.cachedHeight = 2 ∧
      zigzagRL.cachedHeight = 2 ∧
      elements zigzagLR = ({10, 20, 30} : Finset ℕ) ∧
      elements zigzagRL = ({10, 20, 30} : Finset ℕ) :=
  ⟨valid_build _, valid_build _, valid_build _, valid_build _,
   rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩

-- Tightness of the Fibonacci and logarithmic height bounds:
-- empty tree (`h = 0, 2 * log₂ 1 = 0`), 2-node tree (`h = 2 = 2 * log₂ 3`), and minimal 4-node
-- AVL tree `[2, 1, 3, 4]` (`h = 3, fib 5 = 5 = 4 + 1`).
private def sparseHeight3 : AVLTree ℕ := build [2, 1, 3, 4]

example :
    (.nil : AVLTree ℕ).cachedHeight = 2 * Nat.log 2 ((elements (.nil : AVLTree ℕ)).card + 1) ∧
      (build [1, 2]).cachedHeight = 2 ∧
      2 * Nat.log 2 ((elements (build [1, 2])).card + 1) = 2 ∧
      sparseHeight3.cachedHeight = 3 ∧
      Nat.fib (sparseHeight3.cachedHeight + 2) = sparseHeight3.numNodes + 1 ∧
      insert 4 sortedSeven = sortedSeven :=
  ⟨rfl, rfl, by decide, rfl, rfl, insert_eq_self (valid_build _) (by decide)⟩

-- Rebalancing deletion: deleting `1` from `sparseHeight3` (`[2, 1, 3, 4]`, where root `2` had left
-- height 1 and right height 2) triggers a rotation reducing height from 3 to 2, while deleting an
-- absent key leaves the tree unchanged.
example :
    Valid (erase 1 sparseHeight3) ∧
      (erase 1 sparseHeight3).cachedHeight = 2 ∧
      elements (erase 1 sparseHeight3) = ({2, 3, 4} : Finset ℕ) ∧
      erase 99 sortedSeven = sortedSeven ∧
      elements (erase 4 sortedSeven) = ({1, 2, 3, 5, 6, 7} : Finset ℕ) :=
  ⟨valid_erase (valid_build _) 1, rfl, by decide,
   erase_eq_of_notMem (valid_build _) (by decide), by decide⟩

-- Shared adaptive `OrderedSet` clients (`extractMin`, `firstTwo`) execute unchanged on `AVLTree`
-- with logarithmic `charge` certificates (`2 * Nat.log 2 (s.card + 1)`).
private def extractAllFour :
    (spec ℕ).Client (Option ℕ × Option ℕ × Option ℕ × Option ℕ × Option ℕ) := do
  let a ← extractMin
  let b ← extractMin
  let c ← extractMin
  let d ← extractMin
  let e ← extractMin
  pure (a, b, c, d, e)

example :
    (run sparseHeight3 extractAllFour).1 = (some 1, some 2, some 3, some 4, none) ∧
      (run sparseHeight3 extractAllFour).2.1 = .nil ∧
      (run sortedSeven firstTwo).1 = (some 1, some 2) ∧
      (run (.nil : AVLTree ℕ) extractMin).1 = none ∧
      (run (.nil : AVLTree ℕ) extractMin).2.2 = [0] ∧
      total id (run sortedSeven extractMin).2.2 ≤
        (spec ℕ).totalCost charge (elements sortedSeven)
          ((spec ℕ).runClient (elements sortedSeven) extractMin).2.2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, (run_correct extractMin ⟨valid_build _, rfl⟩).2.2⟩

example :
    ∃ t' ns,
      Executes Exec ((insertAll [1, 2, 3, 4, 5, 6, 7]).bind fun _ => extractMin) .nil
        ((spec ℕ).runClient ∅ ((insertAll [1, 2, 3, 4, 5, 6, 7]).bind fun _ => extractMin)).1
        t' ns ∧
      Rep ((spec ℕ).runClient ∅ ((insertAll [1, 2, 3, 4, 5, 6, 7]).bind fun _ => extractMin)).2.1
        t' ∧
      total id ns ≤
        (spec ℕ).totalCost charge ∅
          ((spec ℕ).runClient ∅ ((insertAll [1, 2, 3, 4, 5, 6, 7]).bind fun _ => extractMin)).2.2 :=
  realized_client _ rep_nil

-- Necessity of `Balanced`: an ordered, height-consistent 4-node right spine has height `4`,
-- exceeding `2 * Nat.log 2 (4 + 1) = 4` at `5` nodes (`5 > 2 * Nat.log 2 (5 + 1) = 4`).
private def unbalancedFiveSpine : AVLTree ℕ :=
  mkNode 1 .nil (mkNode 2 .nil (mkNode 3 .nil (mkNode 4 .nil (mkNode 5 .nil .nil))))

example :
    Ordered unbalancedFiveSpine ∧
      HeightConsistent unbalancedFiveSpine ∧
      ¬ Balanced unbalancedFiveSpine ∧
      unbalancedFiveSpine.cachedHeight = 5 ∧
      2 * Nat.log 2 ((elements unbalancedFiveSpine).card + 1) = 4 := by
  refine ⟨?_, ?_, ?_, rfl, by decide⟩
  · simp [unbalancedFiveSpine, mkNode, Ordered, Cslib.Algorithms.Lean.SearchTree.Ordered,
      Cslib.Algorithms.Lean.SearchTree.elements]
  · exact heightConsistent_mkNode trivial (heightConsistent_mkNode trivial
      (heightConsistent_mkNode trivial (heightConsistent_mkNode trivial
        (heightConsistent_mkNode trivial trivial))))
  · simp [unbalancedFiveSpine, mkNode, Balanced]

end ComplexityTests.AVLTree
