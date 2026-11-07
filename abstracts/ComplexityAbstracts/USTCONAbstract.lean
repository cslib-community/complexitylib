/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.USTCONBridge

/-! # Reingold's theorem: undirected connectivity is in logarithmic space

Reingold's theorem decides whether two vertices are joined by a path using too little memory
even to mark the vertices already visited: only logarithmic work space. It replaces the graph
by a bounded-degree expander construction in which connectivity can be detected by short walks.
Evaluating the transformed graph's rotation map in place lets the algorithm enumerate those walks
while repeatedly rereading the input instead of retaining the graph.

Instances are simple undirected graphs given by adjacency matrices, with unary headers for the
vertex count and the two endpoints. The native machine bound applies to valid encoded instances,
including a single vertex joined to itself by the empty walk; malformed-input recognition is
outside the statement. Read-only input and write-only output are excluded from work space.

Lean checks the encoding-preserving transfer through the bridge; `#check_abstract` audits its
public dependency boundary.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [H. R. Lewis, C. H. Papadimitriou, *Symmetric space-bounded computation*][LewisPapadimitriou1982]
-/

namespace ComplexityTests.Abstracts.USTCONAbstract

/-- A Boolean is encoded as one bit. -/
def encBool : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/-- A simple graph on `Fin n`, with its symmetric zero-diagonal Boolean adjacency matrix
and two distinguished vertices. The sigma type records the common vertex count. -/
abbrev Instance := Σ n : ℕ,
  {adj : Fin n → Fin n → Bool //
    (∀ a b, adj a b = adj b a) ∧ (∀ a, adj a a = false)} × Fin n × Fin n

/-- The number of vertices of an instance. -/
def Instance.vertexCount (I : Instance) : ℕ := I.1

/-- The symmetric, zero-diagonal adjacency matrix of an instance. -/
def Instance.adjacency (I : Instance) : Fin I.vertexCount → Fin I.vertexCount → Bool :=
  I.2.1.val

/-- The source vertex. Its existence ensures that the vertex count is positive. -/
def Instance.source (I : Instance) : Fin I.vertexCount := I.2.2.1

/-- The target vertex. -/
def Instance.target (I : Instance) : Fin I.vertexCount := I.2.2.2

/-- The graph determined by the adjacency matrix. -/
def graph (I : Instance) : SimpleGraph (Fin I.vertexCount) where
  Adj a b := I.adjacency a b = true
  symm.symm a b h := (I.2.1.property.1 b a).trans h
  loopless.irrefl a h := by simp only [Instance.adjacency, I.2.1.property.2 a,
    Bool.false_eq_true] at h

/-- Undirected s–t connectivity: a finite walk connects the distinguished vertices. -/
def USTCON : Set Instance := {I | (graph I).Reachable I.source I.target}

/-- Encode the unary header `1^n 0 1^s 0 1^t 0`, then the adjacency matrix row by row.
`List.ofFn` lists coordinates in increasing order; flattening the list of rows gives exactly
`n²` matrix bits. This is the same binary encoding used by the machine theorem. -/
def encode (I : Instance) : List Bool :=
  List.replicate I.vertexCount true ++ false :: (List.replicate I.source.val true ++ false ::
    (List.replicate I.target.val true ++ false ::
      (List.ofFn fun row => List.ofFn (I.adjacency row)).flatten))

theorem encode_injective : Function.Injective encode := USTCONBridge.encode_injective

/-- Injective adjacency-matrix instance encoding. -/
def encInstance : Instance ↪ List Bool := ⟨encode, encode_injective⟩

/-- One fixed finite-state binary multi-tape machine computes a total function within
`c * (floor(log₂(input length)) + 1)` work-tape cells and halts on every encoded input.
Read-only input and write-only output are excluded. -/
def ComputableInLogSpace {α β : Type} (f : α → β)
    (a : α ↪ List Bool) (b : β ↪ List Bool) : Prop :=
  ∃ t c, Turing.MultiTapeTM.ComputableInTimeAndSpace f a b t
    (fun x => c * (Nat.log2 (a x).length + 1))

/-- Deterministic logarithmic-space decision. -/
def L {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ f : α → Bool, ComputableInLogSpace f enc encBool ∧ ∀ a, a ∈ A ↔ f a = true}

/-- Undirected s–t connectivity is decided in logarithmic work space. -/
theorem ustcon_mem_l : USTCON ∈ L encInstance := USTCONBridge.ustcon_mem_l

/--
info: abstract audit passed for `ComplexityTests.Abstracts.USTCONAbstract`:
18 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.USTCONAbstract

end ComplexityTests.Abstracts.USTCONAbstract
