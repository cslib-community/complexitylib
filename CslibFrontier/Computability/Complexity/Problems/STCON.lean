/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Logic.Relation
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.List.Range
public import Mathlib.Data.List.FinRange
import CslibFrontier.Foundations.Data.List.Append
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Foundations.Data.List.UnaryCode

/-!
# Directed s–t connectivity

An instance of directed `s`–`t` connectivity (`Cslib.Complexity.STCONInstance`) is a directed
graph on `Fin n`, given by its adjacency matrix, together with two vertices `s` and `t`; it
belongs to `Cslib.Complexity.STCON` when the graph has a directed path from `s` to `t`, of any
length, including the empty path when `s = t`. This is the problem `PATH` of
[Sipser, Section 7.2 and Example 8.19][Sipser2013], also called `REACHABILITY`
[Papadimitriou, Section 1.1][Papadimitriou94]. The adjacency matrix need not be symmetric and
may have loops.

Instances are encoded (`Cslib.Complexity.encSTCON`) by the unary header `1^n 0 1^s 0 1^t 0`
followed by the adjacency matrix, row by row: the bit at `n + s + t + 3 + a * n + b` is the entry
of the row `a` and the column `b`. The matrix has `n ^ 2` bits, so every number a machine reads
from the header has logarithmically many binary digits in the length of the encoding. This is the
encoding of undirected connectivity (`Cslib.Complexity.encUSTCON`), which is defined through it.

## Main definitions

* `Cslib.Complexity.adjacencyMatrix`: the adjacency matrix of a relation on `Fin n`, row by row,
  shared with the encoding of strongly connected digraphs (`Cslib.Complexity.encDigraph`).
* `Cslib.Complexity.STCONInstance`: instances of directed `s`–`t` connectivity.
* `Cslib.Complexity.STCONInstance.Adj`: the arcs of an instance.
* `Cslib.Complexity.encSTCON`: the encoding of instances.
* `Cslib.Complexity.STCON`: the instances with a directed path from `s` to `t`.

## Main results

* `Cslib.Complexity.getD_adjacencyMatrix`, `Cslib.Complexity.adjacencyMatrix_eq_flatMap`,
  `Cslib.Complexity.adjacencyMatrix_injective`: the entries of an adjacency matrix, its rows, and
  its injectivity.
* `Cslib.Complexity.STCONInstance.getD_encode_n`, `.getD_encode_s`, `.getD_encode_t`,
  `.getD_encode_matrix`: the bits of the header and of the matrix in the encoding;
  `.getElem?_encode_n`, `.getElem?_encode_s`, `.getElem?_encode_t`, `.getElem?_encode_matrix`:
  the same bits, read by position.
* `Cslib.Complexity.STCONInstance.length_encode`: the length of the encoding.
* `Cslib.Complexity.STCONInstance.matrix_eq_flatMap`: the matrix as the concatenation of its rows.
* `Cslib.Complexity.STCONInstance.encode_injective`: the encoding is injective.
* `Cslib.Complexity.STCONInstance.size_n_le_log2`: the number of vertices has logarithmically many
  binary digits in the length of the encoding.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

/-! ### Adjacency matrices -/

/-- **The adjacency matrix** of a relation on `Fin n`, row by row: the row `a` lists the entries
`adj a b` for the columns `b`, so that its bit at `a * n + b` is the entry of the row `a` and the
column `b`. It is the body of the encodings of directed connectivity
(`Cslib.Complexity.encSTCON`) and of digraphs (`Cslib.Complexity.encDigraph`). -/
def adjacencyMatrix {n : ℕ} (adj : Fin n → Fin n → Bool) : List Bool :=
  (List.finRange n).flatMap fun a ↦ List.ofFn (adj a)

section AdjacencyMatrix

variable {n : ℕ} (adj : Fin n → Fin n → Bool)

/-- The adjacency matrix has `n ^ 2` entries. -/
@[simp]
theorem length_adjacencyMatrix : (adjacencyMatrix adj).length = n * n := by
  simp [adjacencyMatrix, List.flatMap_ofFn_prod]

/-- The entry of the row `a` and the column `b` is the bit at `a * n + b` of the matrix. -/
theorem getD_adjacencyMatrix (a b : Fin n) :
    (adjacencyMatrix adj).getD (a * n + b) false = adj a b :=
  List.getD_flatMap_ofFn adj false a b

/-- **The matrix row by row**: the rows `0, …, n - 1`, each listing its entries in the columns
`0, …, n - 1`, for any function `g` on natural numbers giving the entries. -/
theorem adjacencyMatrix_eq_flatMap (g : ℕ → ℕ → Bool) (hg : ∀ a b : Fin n, adj a b = g a b) :
    adjacencyMatrix adj = (List.range n).flatMap fun u => (List.range n).map (g u) := by
  have hr : (List.finRange n).map Fin.val = List.range n :=
    List.ext_getElem (by simp) fun i _ _ => by simp
  rw [adjacencyMatrix, ← hr, List.flatMap_map]
  refine List.flatMap_congr fun a _ => ?_
  rw [List.map_map, List.ofFn_eq_map]
  exact List.map_congr_left fun b _ => hg a b

/-- **The adjacency matrix determines the relation.** -/
theorem adjacencyMatrix_injective : Function.Injective (adjacencyMatrix (n := n)) := by
  intro adj adj' h
  funext a b
  rw [← getD_adjacencyMatrix adj, ← getD_adjacencyMatrix adj', h]

end AdjacencyMatrix

/-- An instance of **directed `s`–`t` connectivity**: a directed graph on `Fin n`, given by its
adjacency matrix, and two vertices `s` and `t`. -/
structure STCONInstance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The adjacency matrix: `adj a b` when there is an arc from `a` to `b`. -/
  adj : Fin n → Fin n → Bool
  /-- The source. -/
  s : Fin n
  /-- The target. -/
  t : Fin n

namespace STCONInstance

variable (I : STCONInstance)

/-- An instance has a vertex, its source. -/
theorem n_pos : 0 < I.n :=
  Fin.pos I.s

/-- The arcs of an instance: there is an arc from `a` to `b` when the entry of the row `a` and the
column `b` of the adjacency matrix is set. -/
def Adj (a b : Fin I.n) : Prop := I.adj a b = true

/-- The adjacency matrix, row by row (`Cslib.Complexity.adjacencyMatrix`). -/
def matrix : List Bool := adjacencyMatrix I.adj

/-- The adjacency matrix has `n ^ 2` entries. -/
@[simp]
theorem length_matrix : I.matrix.length = I.n * I.n :=
  length_adjacencyMatrix I.adj

/-- The position `a * n + b` of an entry lies within the matrix. -/
theorem mul_add_lt (a b : Fin I.n) : (a : ℕ) * I.n + b < I.n * I.n := by
  rw [Nat.mul_comm (a : ℕ)]
  exact Nat.mul_add_lt_mul_of_lt_of_lt a.isLt b.isLt

/-- The entry of the row `a` and the column `b` is the bit at `a * n + b` of the matrix. -/
theorem getD_matrix (a b : Fin I.n) : I.matrix.getD (a * I.n + b) false = I.adj a b :=
  getD_adjacencyMatrix I.adj a b

/-- **The matrix row by row**: the rows `0, …, n - 1`, each listing its entries in the columns
`0, …, n - 1`, for any function `g` on natural numbers giving the entries. -/
theorem matrix_eq_flatMap (g : ℕ → ℕ → Bool) (hg : ∀ a b : Fin I.n, I.adj a b = g a b) :
    I.matrix = (List.range I.n).flatMap fun u => (List.range I.n).map (g u) :=
  adjacencyMatrix_eq_flatMap I.adj g hg

/-- The encoding of an instance: the unary header `1^n 0 1^s 0 1^t 0`, then the adjacency matrix
row by row. -/
def encode : List Bool :=
  List.replicate I.n true ++ false :: (List.replicate I.s true ++ false ::
    (List.replicate I.t true ++ false :: I.matrix))

/-- The length of the encoding: the header and the `n ^ 2` entries of the matrix. -/
theorem length_encode : I.encode.length = I.n + I.s + I.t + 3 + I.n * I.n := by
  simp only [encode, List.length_append, List.length_replicate, List.length_cons, length_matrix]
  omega

/-- The number of vertices is at most the length of the encoding. -/
theorem n_le_length_encode : I.n ≤ I.encode.length := by
  rw [length_encode]
  omega

/-- The number of binary digits of `n` is logarithmic in the length of the encoding. -/
theorem size_n_le_log2 : Nat.size I.n ≤ Nat.log2 I.encode.length + 1 :=
  Nat.size_le.2 (I.n_le_length_encode.trans_lt Nat.lt_log2_self)

/-- The header of the number of vertices: the bit at `i ≤ n` is set exactly when `i < n`. -/
theorem getD_encode_n {i : ℕ} (h : i ≤ I.n) : I.encode.getD i false = decide (i < I.n) :=
  List.getD_replicate_true_append_false_of_le _ h

/-- The header of the source: the bit at `n + 1 + i`, for `i ≤ s`, is set exactly when `i < s`. -/
theorem getD_encode_s {i : ℕ} (h : i ≤ I.s) :
    I.encode.getD (I.n + 1 + i) false = decide (i < I.s) := by
  rw [encode, List.getD_replicate_true_append_false_add]
  exact List.getD_replicate_true_append_false_of_le _ h

/-- The header of the target: the bit at `n + 1 + s + 1 + i`, for `i ≤ t`, is set exactly when
`i < t`. -/
theorem getD_encode_t {i : ℕ} (h : i ≤ I.t) :
    I.encode.getD (I.n + 1 + I.s + 1 + i) false = decide (i < I.t) := by
  rw [encode, show I.n + 1 + I.s + 1 + i = I.n + 1 + (I.s + 1 + i) by omega,
    List.getD_replicate_true_append_false_add, List.getD_replicate_true_append_false_add]
  exact List.getD_replicate_true_append_false_of_le _ h

/-- **The bits of the matrix**: the bit at `n + s + t + 3 + a * n + b` of the encoding is the entry
of the row `a` and the column `b`. -/
theorem getD_encode_matrix (a b : Fin I.n) :
    I.encode.getD (I.n + I.s + I.t + 3 + (a * I.n + b)) false = I.adj a b := by
  rw [encode, show I.n + I.s + I.t + 3 + (a * I.n + b) =
      I.n + 1 + (I.s + 1 + (I.t + 1 + (a * I.n + b))) by omega,
    List.getD_replicate_true_append_false_add, List.getD_replicate_true_append_false_add,
    List.getD_replicate_true_append_false_add, getD_matrix]

/-- A bit of the encoding, read by position. -/
private theorem getElem?_encode {i : ℕ} (h : i < I.encode.length) :
    I.encode[i]? = some (I.encode.getD i false) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The header of the number of vertices, read by position. -/
theorem getElem?_encode_n {i : ℕ} (h : i ≤ I.n) : I.encode[i]? = some (decide (i < I.n)) := by
  rw [I.getElem?_encode (by rw [I.length_encode]; omega), I.getD_encode_n h]

/-- The header of the source, read by position. -/
theorem getElem?_encode_s {i : ℕ} (h : i ≤ I.s) :
    I.encode[I.n + 1 + i]? = some (decide (i < I.s)) := by
  rw [I.getElem?_encode (by rw [I.length_encode]; omega), I.getD_encode_s h]

/-- The header of the target, read by position. -/
theorem getElem?_encode_t {i : ℕ} (h : i ≤ I.t) :
    I.encode[I.n + 1 + I.s + 1 + i]? = some (decide (i < I.t)) := by
  rw [I.getElem?_encode (by rw [I.length_encode]; omega), I.getD_encode_t h]

/-- The entries of the matrix, read by position. -/
theorem getElem?_encode_matrix {a b : ℕ} (ha : a < I.n) (hb : b < I.n) :
    I.encode[I.n + I.s + I.t + 3 + (a * I.n + b)]? = some (I.adj ⟨a, ha⟩ ⟨b, hb⟩) := by
  have := I.mul_add_lt ⟨a, ha⟩ ⟨b, hb⟩
  rw [I.getElem?_encode (by rw [I.length_encode]; simp only at this; omega)]
  exact congrArg some (I.getD_encode_matrix ⟨a, ha⟩ ⟨b, hb⟩)

/-- **The encoding is injective.** -/
theorem encode_injective : Function.Injective encode := by
  rintro ⟨n, adj, s, t⟩ ⟨n', adj', s', t'⟩ h
  obtain ⟨rfl, h⟩ := List.replicate_true_append_false_inj h
  obtain ⟨hs, h⟩ := List.replicate_true_append_false_inj h
  obtain ⟨ht, h⟩ := List.replicate_true_append_false_inj h
  have hadj : adj = adj' := adjacencyMatrix_injective h
  subst hadj
  have hs' : s = s' := Fin.ext hs
  have ht' : t = t' := Fin.ext ht
  subst hs' ht'
  rfl

end STCONInstance

/-- The encoding of instances of directed `s`–`t` connectivity: the unary header
`1^n 0 1^s 0 1^t 0`, then the adjacency matrix row by row. -/
def encSTCON : STCONInstance ↪ List Bool :=
  ⟨STCONInstance.encode, STCONInstance.encode_injective⟩

@[simp]
theorem encSTCON_apply (I : STCONInstance) : encSTCON I = I.encode := rfl

/-- **Directed `s`–`t` connectivity**: the instances whose graph has a directed path from `s` to
`t`, the problem `PATH` of [Sipser, Example 8.19][Sipser2013]. -/
def STCON : Set STCONInstance :=
  {I | Relation.ReflTransGen I.Adj I.s I.t}

theorem mem_STCON {I : STCONInstance} : I ∈ STCON ↔ Relation.ReflTransGen I.Adj I.s I.t :=
  Iff.rfl

end Cslib.Complexity
