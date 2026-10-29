/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Formula

/-!
# The number of nodes of a formula

The node count of a formula is the number of nodes of its syntax tree: the operation nodes, nullary
ones such as constants included (`Cslib.Circuits.Formula.size`), together with the input leaves
(`Cslib.Circuits.Formula.leafSize`). It is the size of a formula in the usual sense of algebraic
complexity, where leaves labelled by variables and by constants both count.

## Main definitions

* `Cslib.Circuits.Formula.nodeCount`: the number of syntax-tree nodes.

## Main results

* `Cslib.Circuits.Formula.nodeCount_input`, `Cslib.Circuits.Formula.nodeCount_gate`: an input is
  one node, and an operation node adds one to the nodes of its arguments.
* `Cslib.Circuits.Formula.nodeCount_pos`: every formula has a node.
-/

@[expose] public section

namespace Cslib.Circuits.Formula

universe v

variable {σ : Signature.{v}} {n : ℕ}

/-- The number of syntax-tree nodes, counting input leaves, constants and operations alike: the
operation nodes `Formula.size` together with the input leaves `Formula.leafSize`. -/
def nodeCount (F : Formula σ n) : ℕ :=
  F.size + F.leafSize

/-- An input is one node. -/
@[simp] theorem nodeCount_input (i : Fin n) : (input i : Formula σ n).nodeCount = 1 :=
  rfl

/-- An operation node adds one node to those of its arguments. -/
@[simp] theorem nodeCount_gate (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n) :
    (gate op args).nodeCount = (∑ j, (args j).nodeCount) + 1 := by
  simp only [nodeCount, size_gate, leafSize_gate, Finset.sum_add_distrib]
  omega

/-- Every formula has a node. -/
theorem nodeCount_pos : ∀ F : Formula σ n, 0 < F.nodeCount
  | .input _ => Nat.one_pos
  | .gate op args => by
    rw [nodeCount_gate]
    omega

end Cslib.Circuits.Formula
