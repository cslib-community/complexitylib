/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Logic.Relation
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.List.Range
import Complexity.Foundations.Data.List.Append
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.Nat.Div

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

* `Cslib.Complexity.STCONInstance`: instances of directed `s`–`t` connectivity.
* `Cslib.Complexity.STCONInstance.Adj`: the arcs of an instance.
* `Cslib.Complexity.encSTCON`: the encoding of instances.
* `Cslib.Complexity.STCON`: the instances with a directed path from `s` to `t`.

## Main results

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

/-- The column of an index below `n * n` is below `n`. -/
theorem mod_lt_of_lt_mul {i n : ℕ} (h : i < n * n) : i % n < n :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at h)

/-- The adjacency matrix, row by row: its bit at `i` is the entry of the row `i / n` and the
column `i % n`. -/
def matrix : List Bool :=
  List.ofFn fun i : Fin (I.n * I.n) ↦
    I.adj ⟨i / I.n, Nat.div_lt_of_lt_mul i.isLt⟩ ⟨i % I.n, mod_lt_of_lt_mul i.isLt⟩

/-- The adjacency matrix has `n ^ 2` entries. -/
@[simp]
theorem length_matrix : I.matrix.length = I.n * I.n := by
  simp [matrix]

/-- The position `a * n + b` of an entry lies within the matrix. -/
theorem mul_add_lt (a b : Fin I.n) : (a : ℕ) * I.n + b < I.n * I.n := by
  have := Nat.mul_le_mul_right I.n (Nat.succ_le_of_lt a.isLt)
  rw [Nat.succ_mul] at this
  omega

/-- The entry of the row `a` and the column `b` is the bit at `a * n + b` of the matrix. -/
theorem getD_matrix (a b : Fin I.n) : I.matrix.getD (a * I.n + b) false = I.adj a b := by
  unfold matrix
  rw [List.getD_ofFn_of_lt _ (I.mul_add_lt a b)]
  congr 1
  · ext
    simp only
    rw [Nat.mul_add_div_fin]
  · ext
    simp only
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt b.isLt]

/-- A row-major list of `m` rows of `N` entries is the concatenation of its rows. -/
private theorem ofFn_mul_eq_flatMap {N : ℕ} (g : ℕ → ℕ → Bool) : ∀ m : ℕ,
    List.ofFn (fun i : Fin (m * N) => g (i / N) (i % N)) =
      (List.range m).flatMap fun u => (List.range N).map (g u)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, ← ofFn_mul_eq_flatMap g m, List.flatMap_singleton,
      List.ofFn_congr (Nat.succ_mul m N), List.ofFn_add]
    congr 1
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    have hi : i < N := by simpa using h₂
    simp only [List.getElem_ofFn, Fin.val_cast, Fin.val_natAdd, List.getElem_map,
      List.getElem_range]
    rw [Nat.mul_add_div_of_lt m hi, Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hi]

/-- **The matrix row by row**: the rows `0, …, n - 1`, each listing its entries in the columns
`0, …, n - 1`, for any function `g` on natural numbers giving the entries. -/
theorem matrix_eq_flatMap (g : ℕ → ℕ → Bool) (hg : ∀ a b : Fin I.n, I.adj a b = g a b) :
    I.matrix = (List.range I.n).flatMap fun u => (List.range I.n).map (g u) := by
  rw [← ofFn_mul_eq_flatMap g I.n, matrix]
  exact List.ofFn_inj.mpr (funext fun i => hg _ _)

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

/-- Within a unary block followed by `false`, the bits are set before the end of the block. -/
private theorem getD_replicate_append_false_of_le {m i : ℕ} (l : List Bool) (h : i ≤ m) :
    (List.replicate m true ++ false :: l).getD i false = decide (i < m) := by
  rcases h.lt_or_eq with h | rfl
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

/-- After a unary block of length `m` followed by `false`, the bits are those of the rest. -/
private theorem getD_replicate_append_false_add (m i : ℕ) (l : List Bool) :
    (List.replicate m true ++ false :: l).getD (m + 1 + i) false = l.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
  simp only [List.length_replicate, show m + 1 + i - m = i + 1 by omega, List.getD_cons_succ]

/-- The header of the number of vertices: the bit at `i ≤ n` is set exactly when `i < n`. -/
theorem getD_encode_n {i : ℕ} (h : i ≤ I.n) : I.encode.getD i false = decide (i < I.n) :=
  getD_replicate_append_false_of_le _ h

/-- The header of the source: the bit at `n + 1 + i`, for `i ≤ s`, is set exactly when `i < s`. -/
theorem getD_encode_s {i : ℕ} (h : i ≤ I.s) :
    I.encode.getD (I.n + 1 + i) false = decide (i < I.s) := by
  rw [encode, getD_replicate_append_false_add]
  exact getD_replicate_append_false_of_le _ h

/-- The header of the target: the bit at `n + 1 + s + 1 + i`, for `i ≤ t`, is set exactly when
`i < t`. -/
theorem getD_encode_t {i : ℕ} (h : i ≤ I.t) :
    I.encode.getD (I.n + 1 + I.s + 1 + i) false = decide (i < I.t) := by
  rw [encode, show I.n + 1 + I.s + 1 + i = I.n + 1 + (I.s + 1 + i) by omega,
    getD_replicate_append_false_add, getD_replicate_append_false_add]
  exact getD_replicate_append_false_of_le _ h

/-- **The bits of the matrix**: the bit at `n + s + t + 3 + a * n + b` of the encoding is the entry
of the row `a` and the column `b`. -/
theorem getD_encode_matrix (a b : Fin I.n) :
    I.encode.getD (I.n + I.s + I.t + 3 + (a * I.n + b)) false = I.adj a b := by
  rw [encode, show I.n + I.s + I.t + 3 + (a * I.n + b) =
      I.n + 1 + (I.s + 1 + (I.t + 1 + (a * I.n + b))) by omega,
    getD_replicate_append_false_add, getD_replicate_append_false_add,
    getD_replicate_append_false_add, getD_matrix]

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
  have hadj : adj = adj' := by
    funext a b
    have := congrArg (fun l ↦ l.getD (a * n + b) false) h
    exact (getD_matrix ⟨n, adj, s, t⟩ a b).symm.trans
      (this.trans (getD_matrix ⟨n, adj', s', t'⟩ a b))
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
