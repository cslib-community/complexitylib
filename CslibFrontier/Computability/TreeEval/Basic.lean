/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Pi

/-!
# The Tree Evaluation problem

An instance of Tree Evaluation with height `h` and value length `ℓ` is a perfect binary tree
with every leaf at depth `h`. Its leaves carry `ℓ`-bit values and its internal nodes carry
arbitrary gates
`{0,1}^ℓ × {0,1}^ℓ → {0,1}^ℓ`. The value of a node is its gate applied to the values of its two
children; the answer is the value of the root.

We follow Goldreich's parametrization by the value length `ℓ`, rather than by the alphabet size
`k = 2^ℓ`, so that values are bit strings `Fin ℓ → Bool` without rounding.

## Main definitions

* `Cslib.TreeEval.Tree ℓ h`: a Tree Evaluation instance of height `h` and value length `ℓ`.
* `Cslib.TreeEval.Tree.eval`: the value of the root.
* `Cslib.TreeEval.Tree.nodeAt`: the node at a path from the root.

## References

* [S. Cook, P. McKenzie, D. Wehr, M. Braverman and R. Santhanam, *Pebbles and branching programs
  for tree evaluation*][CMWBS2012] introduce the problem.
* [O. Goldreich, *On the Cook–Mertz Tree Evaluation procedure*][Goldreich2024TreeEval] uses the
  parametrization by value length.
-/

@[expose] public section

namespace Cslib.TreeEval

/-- A gate on `ℓ`-bit values: a function of the values of the two children. -/
abbrev Gate (ℓ : ℕ) : Type := (Fin ℓ → Bool) → (Fin ℓ → Bool) → Fin ℓ → Bool

/-- A Tree Evaluation instance: a perfect binary tree with all leaves at depth `h`, carrying
`ℓ`-bit values, and internal nodes carrying gates on pairs of `ℓ`-bit values. -/
inductive Tree (ℓ : ℕ) : ℕ → Type
  /-- A leaf carrying a value. -/
  | leaf (v : Fin ℓ → Bool) : Tree ℓ 0
  /-- An internal node carrying a gate, with its left and right subtrees. -/
  | node {h : ℕ} (f : Gate ℓ) (l r : Tree ℓ h) :
      Tree ℓ (h + 1)
  deriving DecidableEq

namespace Tree

variable {ℓ h : ℕ}

/-- The value of the root: each gate is applied to the values of its children. -/
def eval : {h : ℕ} → Tree ℓ h → Fin ℓ → Bool
  | _, leaf v => v
  | _, node f l r => f l.eval r.eval

@[simp] theorem eval_leaf (v : Fin ℓ → Bool) : (leaf v).eval = v := rfl

@[simp] theorem eval_node (f : Gate ℓ)
    (l r : Tree ℓ h) : (node f l r).eval = f l.eval r.eval := rfl

/-- What a path from the root leads to: a leaf with its value, a gate, or nothing. -/
inductive Node (ℓ : ℕ) where
  /-- A leaf with its value. -/
  | leaf (v : Fin ℓ → Bool)
  /-- An internal node with its gate. -/
  | gate (f : Gate ℓ)
  /-- A path leaving the tree. -/
  | none

/-- The node reached from the root along a path, where `false` is the left child. -/
def nodeAt : {h : ℕ} → Tree ℓ h → List Bool → Node ℓ
  | _, leaf v, [] => .leaf v
  | _, leaf _, _ :: _ => .none
  | _, node f _ _, [] => .gate f
  | _, node _ l _, false :: P => l.nodeAt P
  | _, node _ _ r, true :: P => r.nodeAt P

@[simp] theorem nodeAt_leaf_nil (v : Fin ℓ → Bool) : (leaf v).nodeAt [] = .leaf v := rfl

@[simp] theorem nodeAt_node_nil (f : Gate ℓ)
    (l r : Tree ℓ h) : (node f l r).nodeAt [] = .gate f := rfl

@[simp] theorem nodeAt_node_false (f : Gate ℓ)
    (l r : Tree ℓ h) (P : List Bool) : (node f l r).nodeAt (false :: P) = l.nodeAt P := rfl

@[simp] theorem nodeAt_node_true (f : Gate ℓ)
    (l r : Tree ℓ h) (P : List Bool) : (node f l r).nodeAt (true :: P) = r.nodeAt P := rfl

/-- Leaves are at depth `h`. -/
theorem length_of_nodeAt_leaf {U : Tree ℓ h} {P : List Bool} {v : Fin ℓ → Bool}
    (hP : U.nodeAt P = .leaf v) : P.length = h := by
  induction U generalizing P <;> rcases P with _ | ⟨_ | _, P⟩ <;> simp_all [nodeAt]

/-- Gates are at depth less than `h`. -/
theorem length_lt_of_nodeAt_gate {U : Tree ℓ h} {P : List Bool}
    {f : Gate ℓ} (hP : U.nodeAt P = .gate f) :
    P.length < h := by
  induction U generalizing P <;> rcases P with _ | ⟨_ | _, P⟩ <;> simp_all [nodeAt]

end Tree

end Cslib.TreeEval
