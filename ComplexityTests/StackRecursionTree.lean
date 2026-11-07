/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.GenericRAM.Native.StackRecursionTree

/-! # Derivations from recursion trees on a toy scheme

The full binary tree of height `k`: a node with `x > 0` levels below it has two children with
`x - 1` levels, a leaf has value `1`, and a call adds its children's values. The value of a node
with `x` levels is `2 ^ x`. `exists_eval_of_counted` derives its value with at most
`Nat.recursionBound (fun _ => 2) k 0` nodes. The values are tagged with the depth, and
`value_of_run_eq_some` shows that a value tagged `0` returned by the run, with any fuel, is the
root's. -/

namespace ComplexityTests.StackRecursionTree

open Cslib.GenericRAM Cslib.GenericRAM.StackRecursion

/-- The binary tree scheme on `(depth, levels below)`, with values tagged by the depth. The
accumulator counts the children done and sums their values. -/
def tree : Scheme (ℕ × ℕ) (ℕ × ℕ) (ℕ × ℕ) where
  isLeaf x := x.2 == 0
  leaf x := (x.1, 1)
  start _ := (0, 0)
  next x a := if a.1 < 2 then some (x.1 + 1, x.2 - 1) else none
  absorb _ a y := (a.1 + 1, a.2 + y.2)
  finish x a := (x.1, a.2)

/-- The nodes of the tree of height `k`, and the root's value `2 ^ k` for the depth-`0` tag. -/
def inv (k : ℕ) : Invariant (ℕ × ℕ) (ℕ × ℕ) (ℕ × ℕ) :=
  ⟨fun x => x.1 + x.2 = k, fun _ _ => True, fun y => y.1 = 0 → y.2 = 2 ^ k⟩

/-- **The derivation of the root**, with the node count of the recursion tree. -/
theorem exists_eval_tree (k : ℕ) :
    ∃ n h, tree.Eval (inv k) (0, k) (0, 2 ^ k) n h ∧
      n ≤ Nat.recursionBound (fun _ => 2) k 0 ∧ h ≤ k := by
  have := Scheme.exists_eval_of_counted (R := tree) (I := inv k) (fun x => x.2) (fun x => x.1)
    (fun x => (x.1, 2 ^ x.2)) (fun _ => 2) k
    (fun x _ hl => by
      simp only [tree, beq_iff_eq] at hl ⊢
      rw [hl, pow_zero])
    (fun x hx hl => by
      simp only [tree, beq_eq_false_iff_ne, ne_eq] at hl
      simp only [inv] at hx
      refine ⟨by omega, 2, fun c => (c, c * 2 ^ (x.2 - 1)), fun _ => (x.1 + 1, x.2 - 1), le_rfl,
        by simp [tree], fun c hc => by simp [tree]; omega, by simp [tree], fun c hc => ?_,
        fun c hc => ⟨trivial, by simp only [inv]; omega, show x.2 - 1 < x.2 by omega, rfl⟩, ?_⟩
      · simp only [tree, Prod.mk.injEq, true_and]
        ring
      · simp only [tree, Prod.mk.injEq, true_and]
        rw [show x.2 = x.2 - 1 + 1 by omega, pow_succ]
        simp only [Nat.add_sub_cancel]
        ring)
    (fun x hx h0 => by
      simp only [inv] at hx
      simp only at h0 ⊢
      rw [show x.2 = k by omega]) (0, k) (by simp [inv]) (by simp)
  simpa using this

/-- **A tagged value returned by the run is the root's**, for every fuel. -/
theorem run_tree {k f y : ℕ}
    (hrun : tree.run (fun _ : Unit => f) (fun _ => (0, k)) () = some (0, y)) : y = 2 ^ k := by
  obtain ⟨n, h, he, -, -⟩ := exists_eval_tree k
  exact Scheme.value_of_run_eq_some (fuel := fun _ : Unit => f) (root := fun _ => (0, k))
    (a := ()) he hrun rfl

-- The tree of height `3` has `15` nodes, within the bound.
example : Nat.recursionBound (fun _ => 2) 3 0 = 15 := by decide

-- With `2 * 15 - 1` steps the run returns the root's value.
example : tree.run (fun _ : Unit => 29) (fun _ => (0, 3)) () = some (0, 8) := by decide

-- With too little fuel it may return a child's value, tagged with a positive depth.
example : tree.run (fun _ : Unit => 28) (fun _ => (0, 3)) () = some (1, 4) := by decide

end ComplexityTests.StackRecursionTree
