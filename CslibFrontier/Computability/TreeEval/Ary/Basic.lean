/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.TreeEval.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Tree Evaluation with fan-in `d`

An instance of `d`-ary Tree Evaluation with height `h` and value length `ℓ` is a perfect `d`-ary
tree with every leaf at depth `h`. Its leaves carry `ℓ`-bit values and its internal nodes carry
arbitrary gates `({0,1}^ℓ)^d → {0,1}^ℓ`. The value of a node is its gate applied to the values of
its children; the answer is the value of the root. Fan-in `2` is the binary problem
`Cslib.TreeEval.Tree`, which embeds by `Cslib.TreeEval.Ary.Tree.ofBinary`.

Fan-in larger than two arises when Tree Evaluation is used to simulate time-bounded multi-tape
machines, where a block of the computation depends on one earlier block per tape.

## Main definitions

* `Cslib.TreeEval.Ary.Tree d ℓ h`: a `d`-ary instance of height `h` and value length `ℓ`.
* `Cslib.TreeEval.Ary.Tree.eval`: the value of the root.
* `Cslib.TreeEval.Ary.Tree.nodeAt`: the node at a path from the root.
* `Cslib.TreeEval.Ary.Tree.ofBinary`: a binary instance as an instance of fan-in `2`.

## Main results

* `Cslib.TreeEval.Ary.Tree.eval_ofBinary`: the embedding preserves the value.

## References

* [S. Cook, P. McKenzie, D. Wehr, M. Braverman and R. Santhanam, *Pebbles and branching programs
  for tree evaluation*][CMWBS2012] introduce the problem for arbitrary fan-in.
* [J. Cook and I. Mertz, *Tree Evaluation is in Space O(log n · log log n)*][CookMertz2024]
  treat fan-in `d`.
-/

@[expose] public section

namespace Cslib.TreeEval.Ary

/-- A gate of fan-in `d` on `ℓ`-bit values: a function of the values of the `d` children. -/
abbrev Gate (d ℓ : ℕ) : Type := (Fin d → Fin ℓ → Bool) → Fin ℓ → Bool

/-- A binary gate as a gate of fan-in `2`, reading child `0` as the left one. -/
def Gate.ofBinary {ℓ : ℕ} (f : TreeEval.Gate ℓ) : Gate 2 ℓ := fun v => f (v 0) (v 1)

/-- A `d`-ary Tree Evaluation instance: a perfect `d`-ary tree with all leaves at depth `h`,
carrying `ℓ`-bit values, and internal nodes carrying gates of fan-in `d`. -/
inductive Tree (d ℓ : ℕ) : ℕ → Type
  /-- A leaf carrying a value. -/
  | leaf (v : Fin ℓ → Bool) : Tree d ℓ 0
  /-- An internal node carrying a gate, with its `d` subtrees. -/
  | node {h : ℕ} (f : Gate d ℓ) (c : Fin d → Tree d ℓ h) : Tree d ℓ (h + 1)

namespace Tree

variable {d ℓ h : ℕ}

/-- The value of the root: each gate is applied to the values of its children. -/
def eval : {h : ℕ} → Tree d ℓ h → Fin ℓ → Bool
  | _, leaf v => v
  | _, node f c => f fun j => (c j).eval

@[simp] theorem eval_leaf (v : Fin ℓ → Bool) : (leaf v : Tree d ℓ 0).eval = v := rfl

@[simp] theorem eval_node (f : Gate d ℓ) (c : Fin d → Tree d ℓ h) :
    (node f c).eval = f fun j => (c j).eval := rfl

/-- What a path from the root leads to: a leaf with its value, a gate, or nothing. -/
inductive Node (d ℓ : ℕ) where
  /-- A leaf with its value. -/
  | leaf (v : Fin ℓ → Bool)
  /-- An internal node with its gate. -/
  | gate (f : Gate d ℓ)
  /-- A path leaving the tree. -/
  | none

/-- The node reached from the root along a path, where `j` selects the `j`-th child. -/
def nodeAt : {h : ℕ} → Tree d ℓ h → List (Fin d) → Node d ℓ
  | _, leaf v, [] => .leaf v
  | _, leaf _, _ :: _ => .none
  | _, node f _, [] => .gate f
  | _, node _ c, j :: P => (c j).nodeAt P

@[simp] theorem nodeAt_leaf_nil (v : Fin ℓ → Bool) :
    (leaf v : Tree d ℓ 0).nodeAt [] = .leaf v := rfl

@[simp] theorem nodeAt_node_nil (f : Gate d ℓ) (c : Fin d → Tree d ℓ h) :
    (node f c).nodeAt [] = .gate f := rfl

@[simp] theorem nodeAt_node_cons (f : Gate d ℓ) (c : Fin d → Tree d ℓ h) (j : Fin d)
    (P : List (Fin d)) : (node f c).nodeAt (j :: P) = (c j).nodeAt P := rfl

/-- A binary instance as an instance of fan-in `2`, with child `0` on the left. -/
def ofBinary : {h : ℕ} → TreeEval.Tree ℓ h → Tree 2 ℓ h
  | _, .leaf v => leaf v
  | _, .node f l r => node (Gate.ofBinary f) ![ofBinary l, ofBinary r]

/-- The embedding of binary instances preserves the value. -/
@[simp] theorem eval_ofBinary (T : TreeEval.Tree ℓ h) : (ofBinary T).eval = T.eval := by
  induction T with
  | leaf v => rfl
  | node f l r ihl ihr => simp [ofBinary, Gate.ofBinary, ihl, ihr]

end Tree

end Cslib.TreeEval.Ary
