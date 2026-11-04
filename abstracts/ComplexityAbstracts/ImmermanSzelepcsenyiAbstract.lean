/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.ImmermanSzelepcsenyiBridge

/-! # Immerman–Szelepcsényi: nondeterministic space is closed under complement

A nondeterministic machine accepts when some computation path accepts, so certifying that no path
accepts seems to require looking at all of them. Immerman and Szelepcsényi showed that with at
least logarithmic space this asymmetry disappears. A nondeterministic machine can count the
configurations reachable from the start, one distance at a time, by guessing each reachable
configuration again together with a path to it and checking the count. With the final count it
certifies that no accepting configuration is reachable. Hence nondeterministic space `s` is closed
under complement whenever `s n ≥ log₂ n`, and in particular `NL = coNL`. The central example is
directed non-reachability, the complement of the `NL`-complete problem of directed reachability.

Each problem has one fixed finite-state binary multi-tape nondeterministic machine. The machine
runs on the binary encoding `enc a` of an instance `a`, for an arbitrary injective encoding
`enc`. Along every computation prefix, including rejecting branches, it visits at most
`c₁ * s n + c₂` work-tape cells, where `n` is the input length; for `NL` the bound is
`c * (floor(log₂ n) + 1)`. Read-only input and write-only output are not charged. Every branch
terminates: on each input, some finite time bounds all computation paths. A stuck branch rejects.
The complement classes consist of the complements of the problems in the classes, under the same
encoding. The bound `s` need not be constructible: since every sequence of choices respects the
space bound, the complement machine lets the space increase as needed, as Immerman remarks after
his Theorem 1. Lean checks the transfer through the bridge, and `#check_abstract` audits the
public dependencies. The library proof generalizes Erik Demaine's streaming inductive-counting
construction.

## References

* [N. Immerman, *Nondeterministic Space Is Closed under Complementation*, Theorem 1][Immerman1988]
* [R. Szelepcsényi, *The Method of Forcing for Nondeterministic Automata*][Szelepcsenyi1987]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.6][Sipser2013]
-/

namespace ComplexityAbstracts.ImmermanSzelepcsenyiAbstract

/-! ## Nondeterministic space -/

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

/-- Nondeterministic space `O(s n)`: one fixed finite-state machine decides the problem with at
most `c₁ * s n + c₂` work-tape cells on inputs of length `n`, along every computation prefix,
every branch terminating. -/
def NSPACE {α : Type} (enc : α ↪ List Bool) (s : ℕ → ℕ) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : Turing.MultiTapeNTM k Bool State)
    (c₁ c₂ : ℕ), DecidesInSpace M enc A fun a => c₁ * s (enc a).length + c₂}

/-- The complements of the problems in `NSPACE enc s`, with the same encoding. -/
def coNSPACE {α : Type} (enc : α ↪ List Bool) (s : ℕ → ℕ) : Set (Set α) :=
  {A | Aᶜ ∈ NSPACE enc s}

/-- Nondeterministic logarithmic space: one fixed finite-state machine decides the problem with
at most `c * (floor(log₂ n) + 1)` work-tape cells on inputs of length `n`, along every computation
prefix, every branch terminating. -/
def NL {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (k : ℕ) (State : Type) (_ : Finite State) (M : Turing.MultiTapeNTM k Bool State)
    (c : ℕ), DecidesInSpace M enc A fun a => c * (Nat.log2 (enc a).length + 1)}

/-- The complements of the problems in `NL`, with the same encoding. -/
def coNL {α : Type} (enc : α ↪ List Bool) : Set (Set α) := {A | Aᶜ ∈ NL enc}

/-! ## Directed reachability -/

/-- A directed graph on `Fin n`, given by its Boolean adjacency matrix, with a source and a
target. The sigma type records the common vertex count. -/
abbrev Instance := Σ n : ℕ, (Fin n → Fin n → Bool) × Fin n × Fin n

/-- The number of vertices of an instance. -/
def Instance.vertexCount (I : Instance) : ℕ := I.1

/-- The adjacency matrix: `adjacency a b` when there is an arc from `a` to `b`. -/
def Instance.adjacency (I : Instance) : Fin I.vertexCount → Fin I.vertexCount → Bool := I.2.1

/-- The source vertex. Its existence ensures that the vertex count is positive. -/
def Instance.source (I : Instance) : Fin I.vertexCount := I.2.2.1

/-- The target vertex. -/
def Instance.target (I : Instance) : Fin I.vertexCount := I.2.2.2

/-- Directed s–t connectivity: a directed path, possibly empty, leads from the source to the
target. `Relation.ReflTransGen r` is the reflexive-transitive closure of the arc relation `r`. -/
def STCON : Set Instance :=
  {I | Relation.ReflTransGen (fun a b => I.adjacency a b = true) I.source I.target}

/-! ## Representation details

Graphs are encoded with unary sizes, so the input length is at least the number of vertices and
logarithmic space can hold a vertex.
-/

/-- Encode the unary header `1^n 0 1^s 0 1^t 0`, then the adjacency matrix row by row.
`List.ofFn` lists coordinates in increasing order; flattening the list of rows gives exactly
`n²` matrix bits. This is the same binary encoding used by the machine theorem. -/
def encode (I : Instance) : List Bool :=
  List.replicate I.vertexCount true ++ false :: (List.replicate I.source.val true ++ false ::
    (List.replicate I.target.val true ++ false ::
      (List.ofFn fun row => List.ofFn (I.adjacency row)).flatten))

theorem encode_injective : Function.Injective encode :=
  ImmermanSzelepcsenyiBridge.encode_injective

/-- Injective adjacency-matrix instance encoding. -/
def encInstance : Instance ↪ List Bool := ⟨encode, encode_injective⟩

/-! ## Main results -/

/-- **Theorem (Immerman–Szelepcsényi):** nondeterministic space `s` is closed under complement
whenever `log₂ n ≤ s n`, for every injective binary encoding of instances. No constructibility
of `s` is assumed. -/
theorem nspace_eq_conspace {α : Type} (enc : α ↪ List Bool) (s : ℕ → ℕ)
    (hs : ∀ n, Nat.log2 n ≤ s n) : NSPACE enc s = coNSPACE enc s :=
  ImmermanSzelepcsenyiBridge.nspace_eq_conspace enc s hs

/-- **Corollary:** nondeterministic logarithmic space is closed under complement. -/
theorem nl_eq_conl {α : Type} (enc : α ↪ List Bool) : NL enc = coNL enc :=
  ImmermanSzelepcsenyiBridge.nl_eq_conl enc

/-- **Corollary:** directed non-reachability is in nondeterministic logarithmic space. -/
theorem stcon_compl_mem_nl : STCONᶜ ∈ NL encInstance :=
  ImmermanSzelepcsenyiBridge.stcon_compl_mem_nl

/--
info: abstract audit passed for `ComplexityAbstracts.ImmermanSzelepcsenyiAbstract`:
18 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.ImmermanSzelepcsenyiAbstract

end ComplexityAbstracts.ImmermanSzelepcsenyiAbstract
