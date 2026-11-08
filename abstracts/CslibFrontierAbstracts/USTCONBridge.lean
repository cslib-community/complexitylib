/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontier.Computability.Complexity.Classes.LogSpace.USTCON
import CslibFrontier.Foundations.Data.Nat.Div
import Mathlib.Data.List.OfFn

/-! # Transfer of Reingold's theorem along the exact adjacency-matrix encoding -/

namespace ComplexityTests.Abstracts.USTCONBridge

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

def toInternal (I : Instance) : Cslib.Complexity.USTCONInstance :=
  ⟨I.1, I.2.1.val, I.2.1.property.1, I.2.1.property.2, I.2.2.1, I.2.2.2⟩

def ofInternal (I : Cslib.Complexity.USTCONInstance) : Instance :=
  ⟨I.n, ⟨⟨I.adj, I.symm, I.loopless⟩, I.s, I.t⟩⟩

theorem of_to (I : Instance) : ofInternal (toInternal I) = I := rfl

theorem to_of (I : Cslib.Complexity.USTCONInstance) : toInternal (ofInternal I) = I := rfl

theorem encode_eq (I : Instance) : encode I = Cslib.Complexity.encUSTCON (toInternal I) := by
  have matrix_eq : (List.ofFn fun row => List.ofFn (I.adjacency row)).flatten =
      (toInternal I).toSTCONInstance.matrix := by
    rw [Cslib.Complexity.STCONInstance.matrix, List.ofFn_mul]
    congr 1
    apply congrArg List.ofFn
    funext row
    apply congrArg List.ofFn
    funext col
    change I.adjacency row col = I.adjacency _ _
    congr 1
    · apply Fin.ext
      change row.val = (row.val * I.vertexCount + col.val) / I.vertexCount
      rw [Nat.mul_add_div_of_lt row.val col.isLt]
    · apply Fin.ext
      change col.val = (row.val * I.vertexCount + col.val) % I.vertexCount
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt col.isLt]
  change _ = List.replicate I.vertexCount true ++ false ::
    (List.replicate I.source.val true ++ false ::
      (List.replicate I.target.val true ++ false :: (toInternal I).toSTCONInstance.matrix))
  rw [encode, matrix_eq]

theorem encode_injective : Function.Injective encode := by
  intro I J h
  rw [encode_eq, encode_eq] at h
  exact congrArg ofInternal (Cslib.Complexity.encUSTCON.injective h)

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

theorem l_eq {α : Type} (enc : α ↪ List Bool) : L enc = Cslib.Complexity.L enc := rfl

theorem ustcon_mem_l : USTCON ∈ L encInstance := by
  obtain ⟨f, ⟨t, c, k, State, hfin, M, hM⟩, hA⟩ := Cslib.Complexity.USTCON_mem_L
  refine ⟨fun I => f (toInternal I), ⟨fun I => t (toInternal I), c, k, State, hfin, M, ?_⟩,
    fun I => hA (toInternal I)⟩
  intro I
  change M.ComputesInTimeAndSpace (encode I) _ _
    (c * (Nat.log2 (encode I).length + 1))
  rw [encode_eq]
  exact hM (toInternal I)

end ComplexityTests.Abstracts.USTCONBridge
