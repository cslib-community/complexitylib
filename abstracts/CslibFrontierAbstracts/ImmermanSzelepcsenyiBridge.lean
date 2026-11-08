/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Complement
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic
import CslibFrontier.Computability.Complexity.Problems.STCON.Completeness
import Mathlib.Data.List.OfFn

/-! # Transfer of the Immerman–Szelepcsényi theorem to plain machine definitions -/

namespace ComplexityAbstracts.ImmermanSzelepcsenyiBridge

/-- A nondeterministic machine accepts if an actual computation path ends halted with output 1. -/
def Accepts {k : ℕ} {State : Type} (M : Turing.MultiTapeNTM k Bool State)
    (input : List Bool) : Prop :=
  ∃ p : M.ComputationPath input, p.last.Halted ∧ p.last.output = [true]

/-- Every computation prefix respects the workspace bound, membership is accepting-path
existence, and on each input some finite time bounds all paths. A stuck branch rejects. -/
def DecidesInSpace {α : Type} {k : ℕ} {State : Type}
    (M : Turing.MultiTapeNTM k Bool State) (enc : α ↪ List Bool) (A : Set α) (s : α → ℕ) : Prop :=
  (∀ a, M.RunsInSpace (enc a) (s a) ∧ (a ∈ A ↔ Accepts M (enc a))) ∧
    ∀ a, ∃ t, M.RunsInTime (enc a) t

/-- Nondeterministic logarithmic space, with one fixed finite-state machine. -/
def NL {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : Turing.MultiTapeNTM k Bool State)
    (c : ℕ), DecidesInSpace M enc A fun a => c * (Nat.log2 (enc a).length + 1)}

/-- The complements of the problems in `NL`, with the same encoding. -/
def coNL {α : Type} (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ NL enc}

/-- Nondeterministic space `O(s n)`, with one fixed finite-state machine. -/
def NSPACE {α : Type} (enc : α ↪ List Bool) (s : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : Turing.MultiTapeNTM k Bool State)
    (c₁ c₂ : ℕ), DecidesInSpace M enc A fun a => c₁ * s (enc a).length + c₂}

/-- The complements of the problems in `NSPACE enc s`, with the same encoding. -/
def coNSPACE {α : Type} (enc : α ↪ List Bool) (s : ℕ → ℕ) : Set (Set α) :=
  {A | Aᶜ ∈ NSPACE enc s}

theorem nspace_eq_conspace {α : Type} (enc : α ↪ List Bool) (s : ℕ → ℕ)
    (hs : ∀ n, Nat.log2 n ≤ s n) : NSPACE enc s = coNSPACE enc s :=
  Cslib.Complexity.NSPACE_eq_coNSPACE hs

theorem nl_eq {α : Type} (enc : α ↪ List Bool) : NL enc = Cslib.Complexity.NL enc := rfl

theorem conl_eq {α : Type} (enc : α ↪ List Bool) : coNL enc = Cslib.Complexity.coNL enc := rfl

theorem nl_eq_conl {α : Type} (enc : α ↪ List Bool) : NL enc = coNL enc := by
  rw [nl_eq, conl_eq]
  exact Cslib.Complexity.NL_eq_coNL

/-- Membership in `NL` transfers along a map that preserves the encoding. -/
theorem preimage_mem_NL {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α}
    (g : β → α) (hg : ∀ b, encB b = enc (g b)) (h : A ∈ Cslib.Complexity.NL enc) :
    g ⁻¹' A ∈ NL encB := by
  obtain ⟨k, State, hfin, M, c, hM, ht⟩ := h
  refine ⟨k, State, hfin, M, c, fun b => ?_, fun b => ?_⟩
  · beta_reduce
    rw [hg b]
    exact hM (g b)
  · rw [hg b]
    exact ht (g b)

/-- A directed graph on `Fin n`, given by its Boolean adjacency matrix, with a source and a
target. The sigma type records the common vertex count. -/
abbrev Instance := Σ n : ℕ, (Fin n → Fin n → Bool) × Fin n × Fin n

/-- The number of vertices of an instance. -/
def Instance.vertexCount (I : Instance) : ℕ := I.1

/-- The adjacency matrix: `adjacency a b` when there is an arc from `a` to `b`. -/
def Instance.adjacency (I : Instance) : Fin I.vertexCount → Fin I.vertexCount → Bool := I.2.1

/-- The source vertex. -/
def Instance.source (I : Instance) : Fin I.vertexCount := I.2.2.1

/-- The target vertex. -/
def Instance.target (I : Instance) : Fin I.vertexCount := I.2.2.2

/-- Directed s–t connectivity: a directed path, possibly empty, leads from the source to the
target. -/
def STCON : Set Instance :=
  {I | Relation.ReflTransGen (fun a b => I.adjacency a b = true) I.source I.target}

/-- Encode the unary header `1^n 0 1^s 0 1^t 0`, then the adjacency matrix row by row. -/
def encode (I : Instance) : List Bool :=
  List.replicate I.vertexCount true ++ false :: (List.replicate I.source.val true ++ false ::
    (List.replicate I.target.val true ++ false ::
      (List.ofFn fun row => List.ofFn (I.adjacency row)).flatten))

/-- The library's instance with the same graph and vertices. -/
def toInternal (I : Instance) : Cslib.Complexity.STCONInstance :=
  ⟨I.1, I.2.1, I.2.2.1, I.2.2.2⟩

/-- The instance of the abstract with the same graph and vertices. -/
def ofInternal (I : Cslib.Complexity.STCONInstance) : Instance :=
  ⟨I.n, I.adj, I.s, I.t⟩

theorem of_to (I : Instance) : ofInternal (toInternal I) = I := rfl

theorem to_of (I : Cslib.Complexity.STCONInstance) : toInternal (ofInternal I) = I := rfl

theorem encode_eq (I : Instance) : encode I = Cslib.Complexity.encSTCON (toInternal I) := by
  have matrix_eq : (List.ofFn fun row => List.ofFn (I.adjacency row)).flatten =
      (toInternal I).matrix := by
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
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Fin.pos row),
        Nat.div_eq_of_lt col.isLt, Nat.zero_add]
    · apply Fin.ext
      change col.val = (row.val * I.vertexCount + col.val) % I.vertexCount
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt col.isLt]
  change _ = List.replicate I.vertexCount true ++ false ::
    (List.replicate I.source.val true ++ false ::
      (List.replicate I.target.val true ++ false :: (toInternal I).matrix))
  rw [encode, matrix_eq]

theorem encode_injective : Function.Injective encode := by
  intro I J h
  rw [encode_eq, encode_eq] at h
  exact congrArg ofInternal (Cslib.Complexity.encSTCON.injective h)

/-- Injective adjacency-matrix instance encoding. -/
def encInstance : Instance ↪ List Bool := ⟨encode, encode_injective⟩

theorem stcon_compl_mem_nl : STCONᶜ ∈ NL encInstance :=
  preimage_mem_NL toInternal encode_eq Cslib.Complexity.STCON.compl_mem_NL

end ComplexityAbstracts.ImmermanSzelepcsenyiBridge
