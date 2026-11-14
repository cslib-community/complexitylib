/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON
import CslibFrontier.Foundations.Data.List.Append
import CslibFrontier.Foundations.Data.List.UnaryCode

/-!
# Strongly connected digraphs

A digraph instance (`Cslib.Complexity.DigraphInstance`) is a directed graph on `Fin n`, given by
its adjacency matrix; it belongs to `Cslib.Complexity.StronglyConnected` when every vertex reaches
every vertex by a directed path, of any length, including the empty path. The adjacency matrix
need not be symmetric and may have loops; the empty digraph is strongly connected.

Instances are encoded (`Cslib.Complexity.encDigraph`) as instances of directed connectivity are
(`Cslib.Complexity.encSTCON`), without the source and the target: the unary header `1^n 0`
followed by the adjacency matrix row by row (`Cslib.Complexity.adjacencyMatrix`), so that the bit
at `n + 1 + a * n + b` is the entry of the row `a` and the column `b`. This is the encoding of
[Arora and Barak, Exercise 4.4][AroraBarak09], which asks to show that the language is
`NL`-complete (`Cslib.Complexity.StronglyConnected.logSpaceComplete`).

## Main definitions

* `Cslib.Complexity.DigraphInstance`: digraphs given by adjacency matrices.
* `Cslib.Complexity.DigraphInstance.Adj`: the arcs of a digraph.
* `Cslib.Complexity.encDigraph`: the encoding of digraphs.
* `Cslib.Complexity.StronglyConnected`: the strongly connected digraphs.

## Main results

* `Cslib.Complexity.DigraphInstance.getElem?_encode_n`,
  `Cslib.Complexity.DigraphInstance.getElem?_encode_matrix`: the bits of the header and of the
  matrix, read by position.
* `Cslib.Complexity.DigraphInstance.length_encode`: the length of the encoding.
* `Cslib.Complexity.DigraphInstance.encode_injective`: the encoding is injective.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

/-- A **digraph** on `Fin n`, given by its adjacency matrix. -/
structure DigraphInstance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The adjacency matrix: `adj a b` when there is an arc from `a` to `b`. -/
  adj : Fin n → Fin n → Bool

namespace DigraphInstance

variable (G : DigraphInstance)

/-- The arcs of a digraph: there is an arc from `a` to `b` when the entry of the row `a` and the
column `b` of the adjacency matrix is set. -/
def Adj (a b : Fin G.n) : Prop := G.adj a b = true

/-- The encoding of a digraph: the unary header `1^n 0`, then the adjacency matrix row by row. -/
def encode : List Bool :=
  List.replicate G.n true ++ false :: adjacencyMatrix G.adj

/-- The length of the encoding: the header and the `n ^ 2` entries of the matrix. -/
theorem length_encode : G.encode.length = G.n + 1 + G.n * G.n := by
  simp only [encode, List.length_append, List.length_replicate, List.length_cons,
    length_adjacencyMatrix]
  omega

/-- A bit of the encoding, read by position. -/
private theorem getElem?_encode {i : ℕ} (h : i < G.encode.length) :
    G.encode[i]? = some (G.encode.getD i false) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The header, read by position: the bit at `i ≤ n` is set exactly when `i < n`. -/
theorem getElem?_encode_n {i : ℕ} (h : i ≤ G.n) : G.encode[i]? = some (decide (i < G.n)) := by
  rw [G.getElem?_encode (by rw [G.length_encode]; omega), encode,
    List.getD_replicate_true_append_false_of_le _ h]

/-- **The entries of the matrix, read by position**: the bit at `n + 1 + (a * n + b)` is the entry
of the row `a` and the column `b`. -/
theorem getElem?_encode_matrix {a b : ℕ} (ha : a < G.n) (hb : b < G.n) :
    G.encode[G.n + 1 + (a * G.n + b)]? = some (G.adj ⟨a, ha⟩ ⟨b, hb⟩) := by
  have hlt : a * G.n + b < G.n * G.n := by
    rw [Nat.mul_comm a]
    exact Nat.mul_add_lt_mul_of_lt_of_lt ha hb
  rw [G.getElem?_encode (by rw [G.length_encode]; omega), encode,
    List.getD_replicate_true_append_false_add]
  exact congrArg some (getD_adjacencyMatrix G.adj ⟨a, ha⟩ ⟨b, hb⟩)

/-- **The encoding is injective.** -/
theorem encode_injective : Function.Injective encode := by
  rintro ⟨n, adj⟩ ⟨n', adj'⟩ h
  obtain ⟨rfl, h⟩ := List.replicate_true_append_false_inj h
  obtain rfl : adj = adj' := adjacencyMatrix_injective h
  rfl

end DigraphInstance

/-- The encoding of digraphs: the unary header `1^n 0`, then the adjacency matrix row by row. -/
def encDigraph : DigraphInstance ↪ List Bool :=
  ⟨DigraphInstance.encode, DigraphInstance.encode_injective⟩

@[simp]
theorem encDigraph_apply (G : DigraphInstance) : encDigraph G = G.encode := rfl

/-- **Strongly connected digraphs**: every vertex reaches every vertex by a directed path. -/
def StronglyConnected : Set DigraphInstance :=
  {G | ∀ a b, Relation.ReflTransGen G.Adj a b}

theorem mem_StronglyConnected {G : DigraphInstance} :
    G ∈ StronglyConnected ↔ ∀ a b, Relation.ReflTransGen G.Adj a b :=
  Iff.rfl

end Cslib.Complexity
