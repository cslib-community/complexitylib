/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.STCON
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Undirected s–t connectivity

An instance of undirected `s`–`t` connectivity (`Cslib.Complexity.USTCONInstance`) is a simple
graph on `Fin n`, given by its adjacency matrix, symmetric and with zero diagonal, together with
two vertices `s` and `t`; it belongs to `Cslib.Complexity.USTCON` when `t` is reachable from `s`
[Arora and Barak, Section 21.4][AroraBarak09] [Reingold, Section 4][Reingold2008].

Instances are encoded (`Cslib.Complexity.encUSTCON`) as their directed graphs
(`Cslib.Complexity.USTCONInstance.toSTCONInstance`, encoded by `Cslib.Complexity.encSTCON`): the
unary header `1^n 0 1^s 0 1^t 0` followed by the adjacency matrix, row by row, so that the bit at
`n + s + t + 3 + a * n + b` is the entry of the row `a` and the column `b`. The matrix has `n ^ 2`
bits, so the header is no longer than the matrix plus three bits and every number a machine reads
from it has logarithmically many binary digits; this is the adjacency matrix representation of
Reingold's algorithm, with a header that a machine reading its input by address can parse by
counting.

## Main definitions

* `Cslib.Complexity.USTCONInstance`: instances of undirected `s`–`t` connectivity.
* `Cslib.Complexity.USTCONInstance.graph`: the simple graph of an instance.
* `Cslib.Complexity.USTCONInstance.toSTCONInstance`: the directed graph of an instance.
* `Cslib.Complexity.USTCONInstance.edgeTwo`, `Cslib.Complexity.USTCONInstance.emptyTwo`,
  `Cslib.Complexity.USTCONInstance.ofBool`: canonical two-vertex connected and disconnected
  instances.
* `Cslib.Complexity.encUSTCON`: the encoding of instances.
* `Cslib.Complexity.USTCON`: the instances in which `t` is reachable from `s`.

## Main results

* `Cslib.Complexity.USTCONInstance.getD_encode_n`, `.getD_encode_s`, `.getD_encode_t`,
  `.getD_encode_matrix`: the bits of the header and of the matrix in the encoding.
* `Cslib.Complexity.USTCONInstance.encode_injective`: the encoding is injective.
* `Cslib.Complexity.USTCONInstance.size_n_le_log2`: the number of vertices has logarithmically many
  binary digits in the length of the encoding.
* `Cslib.Complexity.USTCONInstance.edgeTwo_mem_USTCON`,
  `Cslib.Complexity.USTCONInstance.emptyTwo_notMem_USTCON`,
  `Cslib.Complexity.USTCONInstance.ofBool_mem_USTCON`: membership of the canonical two-vertex
  instances in `USTCON`.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

/-- An instance of **undirected `s`–`t` connectivity**: a simple graph on `Fin n`, given by its
adjacency matrix, symmetric and with zero diagonal, and two vertices `s` and `t`. -/
structure USTCONInstance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The adjacency matrix. -/
  adj : Fin n → Fin n → Bool
  /-- The adjacency matrix is symmetric. -/
  symm : ∀ a b, adj a b = adj b a
  /-- No vertex is adjacent to itself. -/
  loopless : ∀ a, adj a a = false
  /-- The source. -/
  s : Fin n
  /-- The target. -/
  t : Fin n

namespace USTCONInstance

variable (I : USTCONInstance)

/-- An instance has a vertex, its source. -/
theorem n_pos : 0 < I.n :=
  Fin.pos I.s

/-- The simple graph of an instance: `a` and `b` are adjacent when the entry of the row `a` and the
column `b` of the adjacency matrix is set. -/
def graph : SimpleGraph (Fin I.n) where
  Adj a b := I.adj a b = true
  symm.symm a b h := (I.symm b a).trans h
  loopless.irrefl a h := by simp [I.loopless] at h

/-- Adjacency in the graph of an instance is decidable. -/
instance : DecidableRel I.graph.Adj :=
  fun a b ↦ inferInstanceAs (Decidable (I.adj a b = true))

/-- Adjacency in the graph of an instance is the entry of the adjacency matrix. -/
@[simp]
theorem graph_adj {a b : Fin I.n} : I.graph.Adj a b ↔ I.adj a b = true :=
  Iff.rfl

/-- The directed graph of an instance, with its source and target: an arc in each direction for
every edge. -/
def toSTCONInstance : STCONInstance := ⟨I.n, I.adj, I.s, I.t⟩

/-- Distinct instances have distinct directed graphs, since the adjacency matrix determines the
proofs of symmetry and looplessness. -/
theorem toSTCONInstance_injective : Function.Injective toSTCONInstance := by
  rintro ⟨n, adj, symm, loopless, s, t⟩ ⟨n', adj', symm', loopless', s', t'⟩ h
  simp only [toSTCONInstance, STCONInstance.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- The encoding of an instance, that of its directed graph (`Cslib.Complexity.encSTCON`): the
unary header `1^n 0 1^s 0 1^t 0`, then the adjacency matrix row by row. -/
def encode : List Bool := I.toSTCONInstance.encode

/-- The number of binary digits of `n` is logarithmic in the length of the encoding. -/
theorem size_n_le_log2 : Nat.size I.n ≤ Nat.log2 I.encode.length + 1 :=
  I.toSTCONInstance.size_n_le_log2

/-- The header of the number of vertices: the bit at `i ≤ n` is set exactly when `i < n`. -/
theorem getD_encode_n {i : ℕ} (h : i ≤ I.n) : I.encode.getD i false = decide (i < I.n) :=
  I.toSTCONInstance.getD_encode_n h

/-- The header of the source: the bit at `n + 1 + i`, for `i ≤ s`, is set exactly when `i < s`. -/
theorem getD_encode_s {i : ℕ} (h : i ≤ I.s) :
    I.encode.getD (I.n + 1 + i) false = decide (i < I.s) :=
  I.toSTCONInstance.getD_encode_s h

/-- The header of the target: the bit at `n + 1 + s + 1 + i`, for `i ≤ t`, is set exactly when
`i < t`. -/
theorem getD_encode_t {i : ℕ} (h : i ≤ I.t) :
    I.encode.getD (I.n + 1 + I.s + 1 + i) false = decide (i < I.t) :=
  I.toSTCONInstance.getD_encode_t h

/-- **The bits of the matrix**: the bit at `n + s + t + 3 + a * n + b` of the encoding is the entry
of the row `a` and the column `b`. -/
theorem getD_encode_matrix (a b : Fin I.n) :
    I.encode.getD (I.n + I.s + I.t + 3 + (a * I.n + b)) false = I.adj a b :=
  I.toSTCONInstance.getD_encode_matrix a b

/-- **The encoding is injective.** -/
theorem encode_injective : Function.Injective encode :=
  STCONInstance.encode_injective.comp toSTCONInstance_injective

end USTCONInstance

/-- The encoding of instances of undirected `s`–`t` connectivity: the unary header
`1^n 0 1^s 0 1^t 0`, then the adjacency matrix row by row. -/
def encUSTCON : USTCONInstance ↪ List Bool :=
  ⟨USTCONInstance.encode, USTCONInstance.encode_injective⟩

/-- **Undirected `s`–`t` connectivity**: the instances in which `t` is reachable from `s`
[Arora and Barak, Section 21.4][AroraBarak09], [Reingold][Reingold2008]. -/
def USTCON : Set USTCONInstance :=
  {I | I.graph.Reachable I.s I.t}

namespace USTCONInstance

/-- The single edge on two vertices `0` and `1`, with source `0` and target `1`. -/
def edgeTwo : USTCONInstance where
  n := 2
  adj a b := decide (a ≠ b)
  symm a b := by simp [ne_comm]
  loopless a := by simp
  s := 0
  t := 1

/-- The edgeless graph on two vertices `0` and `1`, with source `0` and target `1`. -/
def emptyTwo : USTCONInstance where
  n := 2
  adj _ _ := false
  symm _ _ := rfl
  loopless _ := rfl
  s := 0
  t := 1

/-- Canonical two-vertex `USTCON` instance encoding a Boolean truth value: `edgeTwo` for `true`
and `emptyTwo` for `false`. -/
def ofBool (b : Bool) : USTCONInstance :=
  if b then edgeTwo else emptyTwo

/-- The single edge on two vertices belongs to `USTCON`. -/
theorem edgeTwo_mem_USTCON : edgeTwo ∈ USTCON :=
  SimpleGraph.Adj.reachable (by decide)

/-- The edgeless graph on two vertices does not belong to `USTCON`. -/
theorem emptyTwo_notMem_USTCON : emptyTwo ∉ USTCON := by
  rintro ⟨p⟩
  cases p with
  | cons hadj _ => exact absurd hadj (by simp [emptyTwo, graph])

/-- `USTCONInstance.ofBool b` belongs to `USTCON` if and only if `b = true`. -/
@[simp]
theorem ofBool_mem_USTCON {b : Bool} : ofBool b ∈ USTCON ↔ b = true := by
  cases b
  · simp [ofBool, emptyTwo_notMem_USTCON]
  · simp [ofBool, edgeTwo_mem_USTCON]

end USTCONInstance

end Cslib.Complexity
