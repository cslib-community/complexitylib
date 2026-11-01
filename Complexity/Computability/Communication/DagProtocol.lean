/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Protocol

/-!
# Dag-like protocols

A *dag-like protocol* for a search problem `R : X → Y → O → Prop` is a directed acyclic graph
through which Alice, holding `x : X`, and Bob, holding `y : Y`, walk from a source to a leaf
labelled by an answer. At each inner node the players run a deterministic tree protocol
(`Cslib.Communication.Protocol`) that decides whether the node is *consistent* with their inputs
and, if it is, names the next node. A protocol solves `R` on `A × B` when, for inputs from
`A × B`, the source is consistent and consistent nodes lead only to consistent nodes, where a leaf
is consistent when its answer is related to the inputs (`DagProtocol.Solves`). The walk from the
source then ends at a related answer (`DagProtocol.Solves.exists_run_eq`). Its communication
complexity is the largest depth of the tree protocols at the inner nodes (`DagProtocol.depth`).

This is Krajíček's notion of a protocol for the Karchmer–Wigderson game
[Krajíček, Definition 2.2][Krajicek1997], for the relation `DiffersAt` (or `ExceedsAt` for
monotone protocols), which he describes as a variant of Razborov's formulation with PLS problems
[Razborov1995b]. Tree
protocols for this game correspond to formulas (`Cslib.Communication.KWProtocol`); dag-like
protocols, whose nodes can be reached along many paths, correspond to circuits: one with `k` inner
nodes and communication complexity `t` gives a separating circuit with `k · 2 ^ O(t)` gates
(`Complexity.Computability.Circuit.DagProtocol`). The representation differs from Definition 2.2
in inessential ways:

* The inner nodes are numbered `0, …, k - 1` so that every step goes to an earlier inner node or
  to a leaf, which rules out cycles. Leaves are identified with their answers, so leaves with the
  same label are merged and `k` counts only inner nodes. The source is any node.
* Krajíček's consistency condition `F(u, v)` and strategy `S(u, v, x)` are not separate data: the
  tree protocol at node `j` answers `none` exactly when `j ∉ F`, and otherwise its answer is the
  next node. The strategy matters only at consistent nodes, and closure of `F` under the paths of
  the strategy reduces to closure under one step.
* Definition 2.2 bounds the bits needed to "decide whether `x ∈ F(u, v)` and compute `S(u, v, x)`";
  here one tree protocol does both, so if the two tasks are counted separately, the depth here is
  at most their sum.

## Main definitions

* `Cslib.Communication.DagProtocol`: dag-like protocols.
* `Cslib.Communication.DagProtocol.Consistent`: consistency of a node with the inputs.
* `Cslib.Communication.DagProtocol.Solves`: a dag-like protocol solves a relation.
* `Cslib.Communication.DagProtocol.depth`: the communication complexity of a dag-like protocol.
* `Cslib.Communication.DagProtocol.run`: the answer at the end of the walk from the source.

## Main results

* `Cslib.Communication.DagProtocol.Solves.exists_run_eq`: a dag-like protocol solving `R` on
  `A × B` answers every pair of inputs from `A × B` with a related answer.

## References

* [J. Krajíček, *Interpolation theorems, lower bounds for proof systems, and independence results
  for bounded arithmetic*][Krajicek1997]
* [A. A. Razborov, *Unprovability of lower bounds on the circuit size in certain fragments of
  bounded arithmetic*][Razborov1995b]
-/

@[expose] public section

namespace Cslib.Communication

/-- A **dag-like protocol** with `k` inner nodes between Alice, holding `x : X`, and Bob, holding
`y : Y`, with answers in `O` [Krajíček, Definition 2.2][Krajicek1997]. The inner nodes are
`0, …, k - 1` and the leaves are labelled by answers. At inner node `j` the players run the tree
protocol `step j`: it answers `none` if `j` is not consistent with the inputs, and otherwise names
the next node, an earlier inner node `i < j` or a leaf labelled by an answer. -/
structure DagProtocol (X Y O : Type*) (k : ℕ) where
  /-- The tree protocol at inner node `j`, which answers `none` if `j` is inconsistent with the
  inputs and otherwise names the next node: an earlier inner node or an answer. -/
  step : (j : Fin k) → Protocol X Y (Option (Fin j ⊕ O))
  /-- The source: an inner node or an answer. -/
  root : Fin k ⊕ O

namespace DagProtocol

variable {X Y O : Type*} {k : ℕ}

/-- The node named by an answer of the tree protocol at inner node `j`, among all nodes. -/
def node (j : Fin k) : Fin j ⊕ O → Fin k ⊕ O :=
  Sum.map (Fin.castLE j.isLt.le) id

@[simp] theorem node_inl (j : Fin k) (i : Fin j) :
    node (O := O) j (.inl i) = .inl (Fin.castLE j.isLt.le i) :=
  rfl

@[simp] theorem node_inr (j : Fin k) (o : O) : node (O := O) j (.inr o) = .inr o :=
  rfl

variable (P : DagProtocol X Y O k)

/-- Node `s` is **consistent** with Alice's input `x` and Bob's input `y` for the relation `R`:
an inner node when its tree protocol does not answer `none`, and a leaf when its answer is
related to `x` and `y`. This is Krajíček's consistency condition `F(x, y)`. -/
def Consistent (R : X → Y → O → Prop) : Fin k ⊕ O → X → Y → Prop
  | .inl j, x, y => (P.step j).run x y ≠ none
  | .inr o, x, y => R x y o

@[simp] theorem consistent_inl (R : X → Y → O → Prop) (j : Fin k) (x : X) (y : Y) :
    P.Consistent R (.inl j) x y ↔ (P.step j).run x y ≠ none :=
  Iff.rfl

@[simp] theorem consistent_inr (R : X → Y → O → Prop) (o : O) (x : X) (y : Y) :
    P.Consistent R (.inr o) x y ↔ R x y o :=
  Iff.rfl

/-- A dag-like protocol **solves** the relation `R` on `A × B` when, for every pair of inputs from
`A × B`, the source is consistent, and every node named by the tree protocol at an inner node is
consistent [Krajíček, Definition 2.2 (4)][Krajicek1997]. The tree protocol names a node only when
its own node is consistent, so consistency is closed under the steps of the walk, and the walk
from the source ends at a related answer (`DagProtocol.Solves.exists_run_eq`). -/
def Solves (R : X → Y → O → Prop) (A : Set X) (B : Set Y) : Prop :=
  (∀ x ∈ A, ∀ y ∈ B, P.Consistent R P.root x y) ∧
    ∀ j, ∀ x ∈ A, ∀ y ∈ B, ∀ s, (P.step j).run x y = some s → P.Consistent R (node j s) x y

/-- The **communication complexity** of a dag-like protocol: the largest depth of the tree
protocols at its inner nodes. -/
def depth : ℕ :=
  Finset.univ.sup fun j => (P.step j).depth

theorem depth_step_le (j : Fin k) : (P.step j).depth ≤ P.depth :=
  Finset.le_sup (f := fun j => (P.step j).depth) (Finset.mem_univ j)

/-- The walk from node `s` on Alice's input `x` and Bob's input `y`: the answer at the leaf it
reaches, or `none` if it meets an inner node whose tree protocol answers `none`. -/
def runFrom (x : X) (y : Y) : Fin k ⊕ O → Option O
  | .inr o => some o
  | .inl j =>
    match (P.step j).run x y with
    | none => none
    | some s => runFrom x y (node j s)
termination_by s => s.elim (fun j => j.val + 1) fun _ => 0
decreasing_by
  rcases s with i | _
  · simp only [node_inl, Sum.elim_inl, Fin.val_castLE]
    exact Nat.succ_lt_succ i.isLt
  · simp

/-- The answer at the end of the walk from the source, or `none` if the walk meets an
inconsistent inner node. -/
def run (x : X) (y : Y) : Option O :=
  P.runFrom x y P.root

variable {P} {R : X → Y → O → Prop} {A : Set X} {B : Set Y}

/-- From a consistent node, the walk of a protocol solving `R` ends at a related answer. -/
theorem Solves.exists_runFrom_eq (hP : P.Solves R A B) {x : X} (hx : x ∈ A) {y : Y} (hy : y ∈ B)
    (s : Fin k ⊕ O) (hs : P.Consistent R s x y) : ∃ o, P.runFrom x y s = some o ∧ R x y o := by
  induction s using runFrom.induct P x y with
  | case1 o => exact ⟨o, by rw [runFrom], hs⟩
  | case2 j h => exact absurd h hs
  | case3 j s h ih =>
    rw [runFrom, h]
    exact ih (hP.2 j x hx y hy s h)

/-- **A dag-like protocol solving `R` on `A × B` solves the search problem**: on every pair of
inputs from `A × B`, the walk from the source ends at an answer related to them. -/
theorem Solves.exists_run_eq (hP : P.Solves R A B) {x : X} (hx : x ∈ A) {y : Y} (hy : y ∈ B) :
    ∃ o, P.run x y = some o ∧ R x y o :=
  hP.exists_runFrom_eq hx hy P.root (hP.1 x hx y hy)

/-- A protocol solving a relation on `A × B` solves it on smaller sets. -/
theorem Solves.mono (hP : P.Solves R A B) {A' : Set X} {B' : Set Y} (hA : A' ⊆ A) (hB : B' ⊆ B) :
    P.Solves R A' B' :=
  ⟨fun x hx y hy => hP.1 x (hA hx) y (hB hy),
    fun j x hx y hy => hP.2 j x (hA hx) y (hB hy)⟩

end DagProtocol

end Cslib.Communication
