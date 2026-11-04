/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of Complexity.Foundations.Data.BinaryBranching)

public import Complexity.Foundations.Data.BinaryBranching
import Mathlib.Data.Nat.Fib.Basic

/-!
# Tests for binary branchings

The Fibonacci tree on `ℕ`: the states `n ≤ 1` are leaves, and an inner state `n` branches to
`n - 1` (`false`) and `n - 2` (`true`).
-/

public section

namespace ComplexityTests.BinaryBranching

open Cslib

/-- The Fibonacci tree. -/
def fib : BinaryBranching ℕ where
  IsLeaf n := n ≤ 1
  next n b := if b then n - 2 else n - 1

/-- The Fibonacci tree terminates: the state decreases at every inner node. -/
theorem fib_terminating : fib.Terminating :=
  .of_lt id fun n hn b => by cases b <;> simp [fib] at hn ⊢ <;> omega

-- `4 → 2 → 1`: the word `[true, false]` reaches the leaf `1`, so it is a leaf word.
example : fib.walk 4 [true, false] = 1 := rfl

example : fib.IsLeafWord 4 [true, false] := by simp [BinaryBranching.IsLeafWord, fib]

-- Continuing past the leaf `1` is not a leaf word, and `[true]` stops at the inner state `2`.
example : ¬ fib.IsLeafWord 4 [true, false, true] := by simp [BinaryBranching.IsLeafWord, fib]

example : ¬ fib.IsLeafWord 4 [true] := by simp [BinaryBranching.IsLeafWord, fib]

-- The following branch sequence `true, false, true, …` stops at the leaf `1` after two steps.
example : fib.walkSeq 10 4 (fun i => decide (i % 2 = 0)) = 1 :=
  BinaryBranching.walkSeq_eq_walk (w := [true, false]) (f := fun i => decide (i % 2 = 0))
    (by simp [BinaryBranching.IsLeafWord, fib]) (fun i hi => by
      obtain rfl | rfl : i = 0 ∨ i = 1 := by simp at hi; omega
      all_goals rfl) (by simp)

/-- The state `4` has five leaves: `n ↦ Nat.fib (n + 1)` is additive at inner states and `1` at
the leaves, so `sum_leafWords_eq` counts them as `Nat.fib 5`. -/
example {W : Finset (List Bool)} (hW : ∀ w, w ∈ W ↔ fib.IsLeafWord 4 w) : W.card = 5 := by
  have hsum := BinaryBranching.sum_leafWords_eq fib_terminating (g := fun n => Nat.fib (n + 1))
    (fun n hn => by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by simp [fib] at hn; omega⟩
      simp only [fib, Bool.false_eq_true, ↓reduceIte]
      rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, Nat.fib_add_two,
        add_comm]) 4 hW
  rw [Finset.sum_congr rfl fun w hw => (?_ : Nat.fib (fib.walk 4 w + 1) = 1)] at hsum
  · simp only [Finset.sum_const, smul_eq_mul, mul_one] at hsum
    exact hsum.trans (by decide)
  · have hleaf : fib.walk 4 w ≤ 1 := ((hW w).mp hw).isLeaf_walk
    obtain h | h : fib.walk 4 w = 0 ∨ fib.walk 4 w = 1 := by omega
    all_goals rw [h]; rfl

end ComplexityTests.BinaryBranching
