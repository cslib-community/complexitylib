/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Card

/-!
# Negation normal form circuits, DNNF and d-DNNF

A *negation normal form circuit* (NNF, also called a De Morgan circuit) over variables `ι` is a
directed acyclic graph whose nodes are literals `xᵢ` or `¬xᵢ`, constants, or fan-in-two `∧` and
`∨` gates (`Cslib.Circuits.NNF`). Nodes are numbered `0, …, size - 1` and every gate's children
have smaller numbers, so nodes are shared: the circuit is a DAG, not a formula, and its *size* is
its number of nodes (gates, literals and constants alike). One node is the output.

* An `∧` gate is *decomposable* when its two children mention disjoint sets of variables
  (`NNF.vars`); a circuit all of whose `∧` gates are decomposable is a **DNNF**
  (`NNF.IsDecomposable`) [Darwiche2001].
* An `∨` gate is *deterministic* when on no assignment both of its children evaluate to true; a
  DNNF all of whose `∨` gates are deterministic is a **d-DNNF** (`NNF.IsDeterministic`)
  [Darwiche2001].

These are the definitions of [ArenasBroadrickLiewVanDenBroeck2026, Section 3.1], with constant
leaves also allowed, as in [Darwiche2001]. Allowing constants only enlarges the class against
which lower bounds hold.

**Relation to `DecomposableDAG`.** `Cslib.Circuits.DecomposableDAG`
(`CslibFrontier/Computability/Circuit/Decomposable.lean`) is a semantic model of *smooth* DNNF:
every union's children share its scope. NNF circuits here need not be smooth, and smoothing a DNNF
can cost more than a constant factor in size, so size lower bounds for `DecomposableDAG` do not
transfer to the paper's DNNF size. This file therefore keeps a separate syntactic model with literal
leaves, explicit node sharing and size counting every node. The certificate argument of `NNF.Occurs`
(`CslibFrontier/Computability/Circuit/NNF/Rectangle.lean`) is the unsmoothed counterpart of
`DecomposableDAG.Occurs`.

Evaluation and variable sets are both instances of one bottom-up fold (`NNF.fold`, with the
unfolding equation `NNF.fold_eq`), defined by structural recursion on a bound for the node
number, so concrete circuits evaluate by `decide`.

## Main definitions

* `Cslib.Circuits.NNF.Gate`, `Cslib.Circuits.NNF`: NNF gates and NNF circuits.
* `Cslib.Circuits.NNF.eval`, `Cslib.Circuits.NNF.toFun`: the value of a node and the function
  computed by the circuit.
* `Cslib.Circuits.NNF.vars`: the variables mentioned below a node.
* `Cslib.Circuits.NNF.IsDecomposable`, `Cslib.Circuits.NNF.IsDeterministic`: DNNF and the
  determinism of every `∨` gate.

## Main results

* `Cslib.Circuits.NNF.eval_congr`: a node's value depends only on the variables it mentions.

## References

* [A. Darwiche, *Decomposable negation normal form*][Darwiche2001]
* [M. Arenas, O. Broadrick, V. Liew, G. Van den Broeck, *d-DNNF is not polynomially closed under
  negation*][ArenasBroadrickLiewVanDenBroeck2026]
-/

@[expose] public section

namespace Cslib.Circuits

/-- A gate of a negation normal form circuit over the variables `ι`, with children among the
nodes `N`. -/
inductive NNF.Gate (ι N : Type*) where
  /-- The literal `xᵢ` when `b` is true, `¬xᵢ` when `b` is false. -/
  | lit (i : ι) (b : Bool)
  /-- A constant. -/
  | const (b : Bool)
  /-- A fan-in-two conjunction. -/
  | and (l r : N)
  /-- A fan-in-two disjunction. -/
  | or (l r : N)
  deriving DecidableEq

/-- A *negation normal form circuit* (NNF) over the variables `ι` on the nodes `N`: every node is
a literal, a constant, or a fan-in-two `∧` or `∨` gate, a rank decreasing from each gate to its
children makes the graph acyclic, and one node is the output. Nodes may be shared, so this is a
DAG. For finite `N`, its size is the number of nodes (`NNF.size`). -/
structure NNF (ι N : Type*) where
  /-- The gate at each node. -/
  gate : N → NNF.Gate ι N
  /-- A rank that decreases from each gate to its children. -/
  rank : N → ℕ
  /-- The children of an `∧` gate have lower rank. -/
  and_lt : ∀ v l r, gate v = .and l r → rank l < rank v ∧ rank r < rank v
  /-- The children of an `∨` gate have lower rank. -/
  or_lt : ∀ v l r, gate v = .or l r → rank l < rank v ∧ rank r < rank v
  /-- The output node. -/
  root : N

namespace NNF

variable {ι N : Type*} (C : NNF ι N) {α : Type*}

/-- The bottom-up fold of an NNF below a node of number less than `k`, by structural recursion on
`k`. -/
def foldBelow (lit : ι → Bool → α) (const : Bool → α) (and or : α → α → α) :
    (k : ℕ) → (v : N) → C.rank v < k → α
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, v, h =>
    match hg : C.gate v with
    | .lit i b => lit i b
    | .const b => const b
    | .and l r =>
      and (foldBelow lit const and or k l
          (Nat.lt_of_lt_of_le ((C.and_lt v l r hg).1) (Nat.le_of_lt_succ h)))
        (foldBelow lit const and or k r
          (Nat.lt_of_lt_of_le ((C.and_lt v l r hg).2) (Nat.le_of_lt_succ h)))
    | .or l r =>
      or (foldBelow lit const and or k l
          (Nat.lt_of_lt_of_le ((C.or_lt v l r hg).1) (Nat.le_of_lt_succ h)))
        (foldBelow lit const and or k r
          (Nat.lt_of_lt_of_le ((C.or_lt v l r hg).2) (Nat.le_of_lt_succ h)))

/-- The bottom-up fold of an NNF at a node: leaves are mapped by `lit` and `const`, and gates
combine the values of their children by `and` and `or`. -/
def fold (lit : ι → Bool → α) (const : Bool → α) (and or : α → α → α) (v : N) : α :=
  C.foldBelow lit const and or (C.rank v + 1) v (Nat.lt_succ_self _)

theorem foldBelow_congr (lit : ι → Bool → α) (const : Bool → α) (and or : α → α → α) :
    ∀ (k k' : ℕ) (v : N) (h : C.rank v < k) (h' : C.rank v < k'),
      C.foldBelow lit const and or k v h = C.foldBelow lit const and or k' v h'
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h' => absurd h' (Nat.not_lt_zero _)
  | k + 1, k' + 1, v, h, h' => by
    simp only [foldBelow]
    split <;> first | rfl | (congr 1 <;> apply foldBelow_congr)

/-- **Unfolding the fold** at a node by its gate. -/
theorem fold_eq (lit : ι → Bool → α) (const : Bool → α) (and or : α → α → α) (v : N) :
    C.fold lit const and or v =
      match C.gate v with
      | .lit i b => lit i b
      | .const b => const b
      | .and l r => and (C.fold lit const and or l) (C.fold lit const and or r)
      | .or l r => or (C.fold lit const and or l) (C.fold lit const and or r) := by
  conv_lhs => rw [fold, foldBelow]
  split <;> rename_i heq <;> simp only [heq] <;> congr 1 <;> apply foldBelow_congr

/-- The value of a node on the assignment `x`. -/
def eval (x : ι → Bool) : N → Bool :=
  C.fold (fun i b => x i == b) id (· && ·) (· || ·)

/-- The function computed by the circuit: the value of its output node. -/
def toFun (x : ι → Bool) : Bool :=
  C.eval x C.root

/-- The size of a circuit on finitely many nodes: its number of nodes. -/
@[nolint unusedArguments]
def size (_C : NNF ι N) [Fintype N] : ℕ :=
  Fintype.card N

variable {C}

theorem eval_lit {x : ι → Bool} {v : N} {i : ι} {b : Bool} (h : C.gate v = .lit i b) :
    C.eval x v = (x i == b) := by
  rw [eval, fold_eq, h]

theorem eval_const {x : ι → Bool} {v : N} {b : Bool} (h : C.gate v = .const b) :
    C.eval x v = b := by
  rw [eval, fold_eq, h]
  rfl

theorem eval_and {x : ι → Bool} {v l r : N} (h : C.gate v = .and l r) :
    C.eval x v = (C.eval x l && C.eval x r) := by
  rw [eval, fold_eq, h]

theorem eval_or {x : ι → Bool} {v l r : N} (h : C.gate v = .or l r) :
    C.eval x v = (C.eval x l || C.eval x r) := by
  rw [eval, fold_eq, h]

/-- **Induction on nodes**: a property holding at every node whose children satisfy it holds at
every node. -/
theorem induction_on {P : N → Prop}
    (h : ∀ v, (∀ u, C.rank u < C.rank v → P u) → P v) (v : N) : P v := by
  obtain ⟨n, hn⟩ : ∃ n, C.rank v = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing v with
  | _ n ih => exact h v fun u hu => ih (C.rank u) (hn ▸ hu) u rfl

section Vars

variable [DecidableEq ι]

variable (C) in
/-- The variables mentioned by the subcircuit below a node. -/
def vars : N → Finset ι :=
  C.fold (fun i _ => {i}) (fun _ => ∅) (· ∪ ·) (· ∪ ·)

theorem vars_lit {v : N} {i : ι} {b : Bool} (h : C.gate v = .lit i b) :
    C.vars v = {i} := by
  rw [vars, fold_eq, h]

theorem vars_const {v : N} {b : Bool} (h : C.gate v = .const b) : C.vars v = ∅ := by
  rw [vars, fold_eq, h]

theorem vars_and {v l r : N} (h : C.gate v = .and l r) :
    C.vars v = C.vars l ∪ C.vars r := by
  rw [vars, fold_eq, h]

theorem vars_or {v l r : N} (h : C.gate v = .or l r) :
    C.vars v = C.vars l ∪ C.vars r := by
  rw [vars, fold_eq, h]

/-- A node mentions at most one variable when it is a literal or a constant. -/
theorem card_vars_le_one_of_not_gate {v : N}
    (h : ∀ l r, C.gate v ≠ .and l r ∧ C.gate v ≠ .or l r) : (C.vars v).card ≤ 1 := by
  cases hg : C.gate v with
  | lit i b => simp [vars_lit hg]
  | const b => simp [vars_const hg]
  | and l r => exact absurd hg (h l r).1
  | or l r => exact absurd hg (h l r).2

/-- **Locality.** The value of a node depends only on the variables it mentions. -/
theorem eval_congr {x y : ι → Bool} (v : N) (h : ∀ i ∈ C.vars v, x i = y i) :
    C.eval x v = C.eval y v := by
  induction v using induction_on with
  | h v ih =>
    cases hg : C.gate v with
    | lit i b => simp [eval_lit hg, h i (by simp [vars_lit hg])]
    | const b => simp [eval_const hg]
    | and l r =>
      have hl := (C.and_lt v l r hg)
      rw [eval_and hg, eval_and hg,
        ih l hl.1 fun i hi => h i (by rw [vars_and hg]; exact Finset.mem_union_left _ hi),
        ih r hl.2 fun i hi => h i (by rw [vars_and hg]; exact Finset.mem_union_right _ hi)]
    | or l r =>
      have hl := (C.or_lt v l r hg)
      rw [eval_or hg, eval_or hg,
        ih l hl.1 fun i hi => h i (by rw [vars_or hg]; exact Finset.mem_union_left _ hi),
        ih r hl.2 fun i hi => h i (by rw [vars_or hg]; exact Finset.mem_union_right _ hi)]

variable (C) in
/-- A circuit is **decomposable** (a DNNF) when the two children of each of its `∧` gates
mention disjoint sets of variables. -/
def IsDecomposable : Prop :=
  ∀ v l r, C.gate v = .and l r → Disjoint (C.vars l) (C.vars r)

end Vars

variable (C) in
/-- A circuit is **deterministic** when the two children of each of its `∨` gates are never both
true. A deterministic DNNF is a d-DNNF. -/
def IsDeterministic : Prop :=
  ∀ v l r, C.gate v = .or l r → ∀ x : ι → Bool, ¬(C.eval x l = true ∧ C.eval x r = true)

end NNF

end Cslib.Circuits
