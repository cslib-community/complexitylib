/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Permanent.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Foundations.Data.Matrix.Permanent.Blocks
import CslibFrontier.Foundations.Data.Matrix.Permanent.Relay

/-!
# From nonnegative integer tables to 0/1 tables

The second step of Goldreich's proof of Proposition 6.22 [Goldreich2007Draft]: the permanent of
a table of natural numbers equals the permanent of an explicit 0/1 table
(`zeroOnePermanent_natTableToZeroOne`). Read a square matrix as a weighted digraph; its permanent
is the total weight of its cycle covers. An edge `u → v` of weight `w` with binary digits
`w₀, …, w_{L-1}` is replaced by a chain of fresh vertices `d₀, …, d_{L-1}`, each with a self-loop:
level `k` has the edge `u → tₖ` of weight `wₖ`, where `t₀ = v` and `tₖ = d_{k-1}`, and two
parallel unit paths from `dₖ` to `tₖ`, one direct and one through a fresh relay vertex `rₖ` with
a self-loop. Removing the relay vertices from the last one down
(`Matrix.permanent_eq_of_relay`) turns each pair of parallel paths into an edge of weight `2`,
and removing `dₖ` adds `2 · (w >> (k + 1))` to the weight of `u → tₖ`.

The construction is stated for lists of weighted edges (`WeightedEdge`), whose matrix
(`edgeMatrix`) adds the weights of parallel edges. All emitted weights are `0` or `1`, and no
pair of vertices carries two edges of positive weight, so the final matrix is a 0/1 matrix
(`edgeWeight_tableChain_le_one`), read off as a Boolean table.

## Main definitions

* `Cslib.Complexity.PermanentZeroOne.edgeWeight`, `Cslib.Complexity.PermanentZeroOne.edgeMatrix`:
  weighted edge lists as matrices.
* `Cslib.Complexity.PermanentZeroOne.entryChain`: the binary chain replacing one edge.
* `Cslib.Complexity.natTableToZeroOne`: the 0/1 table of a table of natural numbers.

## Main results

* `Cslib.Complexity.PermanentZeroOne.permanent_tableChain`: the chains preserve the permanent.
* `Cslib.Complexity.zeroOnePermanent_natTableToZeroOne`: **the nonnegative step of Proposition
  6.22**.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
-/

@[expose] public section

namespace Cslib.Complexity

namespace PermanentZeroOne

open Turing.MultiTapeTM

/-- A weighted edge `src → dst` of weight `weight` between numbered vertices. -/
structure WeightedEdge where
  /-- The source vertex. -/
  src : ℕ
  /-- The target vertex. -/
  dst : ℕ
  /-- The weight. -/
  weight : ℕ
  deriving DecidableEq

/-- Weighted edges as the tuple of their fields: source and target in unary, weight in binary. -/
enc_structure encWeightedEdge : WeightedEdge where
  src : encUnary, dst : encUnary, weight : encNat

/-- The total weight of the edges from `i` to `j` in a list of weighted edges. -/
def edgeWeight (E : List WeightedEdge) (i j : ℕ) : ℕ :=
  (E.map fun e => if e.src = i ∧ e.dst = j then e.weight else 0).sum

/-- The `N × N` weighted adjacency matrix of a list of weighted edges; edges with an endpoint
outside `[0, N)` are ignored and parallel edges add. -/
def edgeMatrix (N : ℕ) (E : List WeightedEdge) : Matrix (Fin N) (Fin N) ℕ :=
  Matrix.of fun i j => edgeWeight E i j

/-- Level `k` of the chain replacing the edge `u → v` of weight `w`, with fresh vertices from `N`:
the edge `u → tₖ` weighted by bit `k` of `w`, and the doubling vertex `d = N + 2k` and relay
vertex `d + 1`, each with a self-loop, joined to `tₖ` by two unit paths. Here `t₀ = v` and
`tₖ = d - 2` for `k > 0`. -/
def chainLevel (N u v w k : ℕ) : List WeightedEdge :=
  [⟨u, if k = 0 then v else N + 2 * k - 2, if w.testBit k then 1 else 0⟩,
    ⟨N + 2 * k, N + 2 * k, 1⟩,
    ⟨N + 2 * k, if k = 0 then v else N + 2 * k - 2, 1⟩,
    ⟨N + 2 * k + 1, N + 2 * k + 1, 1⟩,
    ⟨N + 2 * k, N + 2 * k + 1, 1⟩,
    ⟨N + 2 * k + 1, if k = 0 then v else N + 2 * k - 2, 1⟩]

/-- The `L`-level chain replacing the edge `u → v` of weight `w < 2 ^ L`, with fresh vertices
`N, …, N + 2L - 1`. -/
def entryChain (N u v w L : ℕ) : List WeightedEdge :=
  (List.range L).flatMap (chainLevel N u v w)

/-- The chains of a list of weighted edges, consecutive chains using consecutive blocks of `2L`
fresh vertices from `N`. -/
def tableChain (N L : ℕ) : List WeightedEdge → List WeightedEdge
  | [] => []
  | t :: ts => entryChain N t.src t.dst t.weight L ++ tableChain (N + 2 * L) L ts

/-! ### Edge weights -/

@[simp] theorem edgeWeight_nil (i j : ℕ) : edgeWeight [] i j = 0 := rfl

@[simp] theorem edgeWeight_cons (e : WeightedEdge) (E : List WeightedEdge) (i j : ℕ) :
    edgeWeight (e :: E) i j =
      (if e.src = i ∧ e.dst = j then e.weight else 0) + edgeWeight E i j := by
  simp [edgeWeight]

@[simp] theorem edgeWeight_append (E F : List WeightedEdge) (i j : ℕ) :
    edgeWeight (E ++ F) i j = edgeWeight E i j + edgeWeight F i j := by
  simp [edgeWeight]

theorem edgeWeight_flatMap {ι : Type*} (l : List ι) (g : ι → List WeightedEdge) (i j : ℕ) :
    edgeWeight (l.flatMap g) i j = (l.map fun x => edgeWeight (g x) i j).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem edgeWeight_perm {E F : List WeightedEdge} (h : E.Perm F) (i j : ℕ) :
    edgeWeight E i j = edgeWeight F i j :=
  (h.map _).sum_eq

theorem edgeMatrix_perm (N : ℕ) {E F : List WeightedEdge} (h : E.Perm F) :
    edgeMatrix N E = edgeMatrix N F := by
  ext i j
  exact edgeWeight_perm h i j

theorem edgeWeight_eq_zero {E : List WeightedEdge} {i j : ℕ}
    (h : ∀ e ∈ E, e.src = i → e.dst ≠ j) : edgeWeight E i j = 0 := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    rw [edgeWeight_cons, ih fun e' he' => h e' (List.mem_cons_of_mem _ he')]
    have := h e List.mem_cons_self
    split_ifs with h' <;> simp_all

/-- The edges of `E` have both endpoints below `N`. -/
def Within (N : ℕ) (E : List WeightedEdge) : Prop :=
  ∀ e ∈ E, e.src < N ∧ e.dst < N

theorem Within.mono {N N' : ℕ} {E : List WeightedEdge} (h : Within N E) (hN : N ≤ N') :
    Within N' E :=
  fun e he => ⟨(h e he).1.trans_le hN, (h e he).2.trans_le hN⟩

theorem edgeWeight_eq_zero_of_within {N : ℕ} {E : List WeightedEdge} (h : Within N E) {i j : ℕ}
    (hij : N ≤ i ∨ N ≤ j) : edgeWeight E i j = 0 :=
  edgeWeight_eq_zero fun e he hi hj => by have := h e he; omega

/-- **Removing a relay vertex from an edge list**: if the last vertex `K` has a unit self-loop, one
other outgoing edge to `t` of weight `b` and one other incoming edge from `s` of weight `a`, then
deleting it and adding the edge `s → t` of weight `a * b` preserves the permanent. -/
theorem permanent_edgeMatrix_relay {K s t a b : ℕ} (E : List WeightedEdge) (hs : s < K)
    (ht : t < K) (hll : edgeWeight E K K = 1)
    (hrow : ∀ j < K, edgeWeight E K j = if j = t then b else 0)
    (hcol : ∀ i < K, edgeWeight E i K = if i = s then a else 0) :
    (edgeMatrix (K + 1) E).permanent = (edgeMatrix K (E ++ [⟨s, t, a * b⟩])).permanent := by
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 1 := ⟨K - 1, by omega⟩
  rw [Matrix.permanent_eq_of_relay (edgeMatrix (n + 2) E) ⟨s, hs⟩ ⟨t, ht⟩ a b]
  · congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.submatrix_apply, edgeMatrix, Matrix.of_apply,
      Fin.val_castSucc, edgeWeight_append, edgeWeight_cons, edgeWeight_nil, add_zero, Fin.ext_iff]
    congr 1
    split_ifs <;> omega
  · simpa [edgeMatrix] using hll
  · intro j
    simpa [edgeMatrix, Fin.ext_iff] using hrow j j.isLt
  · intro i
    simpa [edgeMatrix, Fin.ext_iff] using hcol i i.isLt

/-! ### One chain -/

theorem entryChain_zero (N u v w : ℕ) : entryChain N u v w 0 = [] := rfl

theorem chainLevel_succ (N u v w k : ℕ) :
    chainLevel N u v w (k + 1) = chainLevel (N + 2) u N (w / 2) k := by
  have h1 : N + 2 * (k + 1) = N + 2 + 2 * k := by ring
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [chainLevel, Nat.testBit_succ]
  · simp only [chainLevel, h1, Nat.testBit_succ, Nat.add_one_ne_zero, Nat.pos_iff_ne_zero.1 hk,
      ite_false]

theorem entryChain_succ (N u v w L : ℕ) :
    entryChain N u v w (L + 1) = chainLevel N u v w 0 ++ entryChain (N + 2) u N (w / 2) L := by
  simp only [entryChain, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
    chainLevel_succ]

theorem within_entryChain {N u v w L : ℕ} (hu : u < N) (hv : v < N) :
    Within (N + 2 * L) (entryChain N u v w L) := by
  intro e he
  simp only [entryChain, List.mem_flatMap, List.mem_range] at he
  obtain ⟨k, hk, he⟩ := he
  simp only [chainLevel, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> (try split_ifs) <;> omega

private theorem edgeWeight_chainLevel_zero_row_succ {N u v w : ℕ} (hu : u < N) (hv : v < N)
    (j : ℕ) : edgeWeight (chainLevel N u v w 0) (N + 1) j =
      (if N + 1 = j then 1 else 0) + (if v = j then 1 else 0) := by
  simp only [chainLevel, edgeWeight_cons, edgeWeight_nil, ↓reduceIte, true_and]
  split_ifs <;> omega

private theorem edgeWeight_chainLevel_zero_col_succ {N u v w : ℕ} (_hu : u < N) (hv : v < N)
    (i : ℕ) : edgeWeight (chainLevel N u v w 0) i (N + 1) =
      (if N + 1 = i then 1 else 0) + (if N = i then 1 else 0) := by
  simp only [chainLevel, edgeWeight_cons, edgeWeight_nil, ↓reduceIte, and_true]
  split_ifs <;> omega

private theorem edgeWeight_chainLevel_zero_row {N u v w : ℕ} (hu : u < N) (hv : v < N)
    (j : ℕ) : edgeWeight (chainLevel N u v w 0) N j =
      (if N = j then 1 else 0) + (if v = j then 1 else 0) + (if N + 1 = j then 1 else 0) := by
  simp only [chainLevel, edgeWeight_cons, edgeWeight_nil, ↓reduceIte]
  split_ifs <;> omega

private theorem edgeWeight_chainLevel_zero_col {N u v w : ℕ} (_hu : u < N) (hv : v < N)
    (i : ℕ) : edgeWeight (chainLevel N u v w 0) i N = if N = i then 1 else 0 := by
  simp only [chainLevel, edgeWeight_cons, edgeWeight_nil, ↓reduceIte]
  split_ifs <;> omega

private theorem edgeWeight_chainLevel_zero_of_lt {N u v w i j : ℕ} (hi : i < N) (hj : j < N) :
    edgeWeight (chainLevel N u v w 0) i j = if u = i ∧ v = j then w % 2 else 0 := by
  simp only [chainLevel, edgeWeight_cons, edgeWeight_nil, ↓reduceIte, Nat.testBit_zero]
  split_ifs <;> simp_all <;> omega

/-- **One chain preserves the permanent**: for `w < 2 ^ L`, replacing the edge `u → v` of weight
`w` by `entryChain N u v w L` preserves the permanent, whatever the other edges below `N`. -/
theorem permanent_entryChain (L : ℕ) :
    ∀ {N M u v w : ℕ} (E : List WeightedEdge), M = N + 2 * L → Within N E → u < N → v < N →
      w < 2 ^ L →
      (edgeMatrix M (E ++ entryChain N u v w L)).permanent =
        (edgeMatrix N (E ++ [⟨u, v, w⟩])).permanent := by
  induction L with
  | zero =>
    intro N M u v w E hM _ _ _ hw
    subst hM
    have hw : w = 0 := by simpa using hw
    subst hw
    congr 1
    ext i j
    simp [edgeMatrix, entryChain_zero]
  | succ L ih =>
    intro N M u v w E hM hE hu hv hw
    rw [entryChain_succ, ← List.append_assoc]
    have hE1 : Within (N + 2) (E ++ chainLevel N u v w 0) := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact ⟨(hE e he).1.trans_le (by omega), (hE e he).2.trans_le (by omega)⟩
      · simp only [chainLevel, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
    rw [ih (N := N + 2) _ (by omega) hE1 (by omega) (by omega)
      (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hw; exact hw)]
    have hz : ∀ i j, (N ≤ i ∨ N ≤ j) → edgeWeight E i j = 0 :=
      fun i j h => edgeWeight_eq_zero_of_within hE h
    -- remove the relay vertex `N + 1`
    rw [permanent_edgeMatrix_relay (K := N + 1) (s := N) (t := v) (a := 1) (b := 1) _ (by omega)
      (by omega)]
    rotate_left
    · simp only [edgeWeight_append, edgeWeight_cons, edgeWeight_nil,
        edgeWeight_chainLevel_zero_row_succ hu hv, hz (N + 1) (N + 1) (by omega)]
      split_ifs <;> omega
    · intro j hj
      simp only [edgeWeight_append, edgeWeight_cons, edgeWeight_nil,
        edgeWeight_chainLevel_zero_row_succ hu hv, hz (N + 1) j (by omega)]
      split_ifs <;> omega
    · intro i hi
      simp only [edgeWeight_append, edgeWeight_cons, edgeWeight_nil,
        edgeWeight_chainLevel_zero_col_succ hu hv, hz i (N + 1) (by omega)]
      split_ifs <;> omega
    -- remove the doubling vertex `N`
    rw [permanent_edgeMatrix_relay (K := N) (s := u) (t := v) (a := w / 2) (b := 2) _ hu hv]
    rotate_left
    · simp only [edgeWeight_append, edgeWeight_cons, edgeWeight_nil,
        edgeWeight_chainLevel_zero_row hu hv, hz N N (by omega)]
      split_ifs <;> omega
    · intro j hj
      simp only [edgeWeight_append, edgeWeight_cons, edgeWeight_nil,
        edgeWeight_chainLevel_zero_row hu hv, hz N j (by omega), true_and]
      split_ifs <;> omega
    · intro i hi
      simp only [edgeWeight_append, edgeWeight_cons, edgeWeight_nil,
        edgeWeight_chainLevel_zero_col hu hv, hz i N (by omega), and_true]
      split_ifs <;> omega
    refine congrArg Matrix.permanent ?_
    ext i j
    have hi := i.isLt
    have hj := j.isLt
    simp only [edgeMatrix, Matrix.of_apply, edgeWeight_append, edgeWeight_cons, edgeWeight_nil,
      edgeWeight_chainLevel_zero_of_lt hi hj]
    split_ifs <;> omega

/-! ### Chains of a table -/

theorem tableChain_nil (N L : ℕ) : tableChain N L [] = [] := rfl

theorem tableChain_cons (N L : ℕ) (t : WeightedEdge) (ts : List WeightedEdge) :
    tableChain N L (t :: ts) = entryChain N t.src t.dst t.weight L ++ tableChain (N + 2 * L) L ts :=
  rfl

/-- **The chains of a table preserve the permanent.** -/
theorem permanent_tableChain (L : ℕ) :
    ∀ (ts : List WeightedEdge) {N M : ℕ} (E : List WeightedEdge), M = N + 2 * L * ts.length →
      Within N E → (∀ t ∈ ts, t.src < N ∧ t.dst < N ∧ t.weight < 2 ^ L) →
      (edgeMatrix M (E ++ tableChain N L ts)).permanent = (edgeMatrix N (E ++ ts)).permanent := by
  intro ts
  induction ts with
  | nil =>
    intro N M E hM _ _
    subst hM
    simp [tableChain_nil]
  | cons t ts ih =>
    intro N M E hM hE hts
    obtain ⟨htu, htv, htw⟩ := hts t List.mem_cons_self
    rw [tableChain_cons, ← List.append_assoc]
    have hE' : Within (N + 2 * L) (E ++ entryChain N t.src t.dst t.weight L) := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact ⟨(hE e he).1.trans_le (by omega), (hE e he).2.trans_le (by omega)⟩
      · exact within_entryChain htu htv e he
    rw [ih (N := N + 2 * L) _ (by rw [hM, List.length_cons]; ring) hE'
      fun t' ht' => by
        obtain ⟨h1, h2, h3⟩ := hts t' (List.mem_cons_of_mem _ ht')
        exact ⟨by omega, by omega, h3⟩]
    have hrest : Within N (E ++ ts) := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact hE e he
      · obtain ⟨h1, h2, _⟩ := hts e (List.mem_cons_of_mem _ he)
        exact ⟨h1, h2⟩
    rw [edgeMatrix_perm _ (show (E ++ entryChain N t.src t.dst t.weight L ++ ts).Perm
        ((E ++ ts) ++ entryChain N t.src t.dst t.weight L) by
      rw [List.append_assoc, List.append_assoc]
      exact List.Perm.append_left _ List.perm_append_comm),
      permanent_entryChain L _ rfl hrest htu htv htw]
    congr 1
    apply edgeMatrix_perm
    rw [List.append_assoc]
    exact List.Perm.append_left _ (List.perm_append_comm.trans (by simp))

/-! ### The chains form a 0/1 matrix -/

/-- A list sum over `range L` whose terms are at most `1` and vanish away from one index `κ` is at
most `1`. -/
private theorem sum_range_le_one {L κ : ℕ} {f : ℕ → ℕ} (hf : ∀ k, f k ≤ 1)
    (hκ : ∀ k, f k ≠ 0 → k = κ) : ((List.range L).map f).sum ≤ 1 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases hL : f L = 0
    · simpa [hL] using ih
    · have hLκ := hκ L hL
      have hrest : ((List.range L).map f).sum = 0 := by
        rw [List.sum_eq_zero_iff]
        intro x hx
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
        by_contra h
        have := hκ k h
        simp at hk
        omega
      have := hf L
      omega

theorem edgeWeight_chainLevel_le_one (N u v w k i j : ℕ) (hu : u < N) (hv : v < N) :
    edgeWeight (chainLevel N u v w k) i j ≤ 1 := by
  simp only [chainLevel, edgeWeight_cons, edgeWeight_nil]
  split_ifs <;> omega

/-- A list sum over `range L` whose terms vanish away from `0`. -/
private theorem sum_range_eq_of_zero {L : ℕ} {f : ℕ → ℕ} (hf : ∀ k, k ≠ 0 → f k = 0) :
    ((List.range L).map f).sum = if 0 < L then f 0 else 0 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    rcases L with _ | L
    · simp
    · simp [hf (L + 1) (by omega)]

/-- A list sum over `range n` of the terms at one index `a`. -/
private theorem sum_range_ite_eq {n a : ℕ} (f : ℕ → ℕ) :
    ((List.range n).map fun k => if k = a then f k else 0).sum = if a < n then f a else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    split_ifs <;> subst_vars <;> omega

/-- Entries of one chain between old vertices: only the edge `u → v` of level `0` remains. -/
theorem edgeWeight_entryChain_of_lt {N u v w L i j : ℕ} (hi : i < N) (hj : j < N) :
    edgeWeight (entryChain N u v w L) i j =
      if 0 < L then (if u = i ∧ v = j then (if w.testBit 0 then 1 else 0) else 0) else 0 := by
  rw [entryChain, edgeWeight_flatMap, sum_range_eq_of_zero]
  · simp only [chainLevel, edgeWeight_cons, edgeWeight_nil, ite_true]
    split_ifs <;> omega
  · intro k hk
    simp only [chainLevel, edgeWeight_cons, edgeWeight_nil, hk, ite_false]
    split_ifs <;> omega

/-- Entries of one chain at a fresh vertex are at most `1`. -/
theorem edgeWeight_entryChain_le_one {N u v w L i j : ℕ} (hu : u < N) (hv : v < N)
    (hij : N ≤ i ∨ N ≤ j) : edgeWeight (entryChain N u v w L) i j ≤ 1 := by
  rw [entryChain, edgeWeight_flatMap]
  refine sum_range_le_one (κ := if N ≤ i then (i - N) / 2 else (j - N) / 2 + 1)
    (fun k => edgeWeight_chainLevel_le_one N u v w k i j hu hv) fun k hk => ?_
  simp only [chainLevel, edgeWeight_cons, edgeWeight_nil] at hk
  split_ifs at hk ⊢ <;> omega

/-- The edges of a table, one per pair `(i, j)` with `i, j < n`, weighted by `g i j`. -/
def gridEdges (n : ℕ) (g : ℕ → ℕ → ℕ) : List WeightedEdge :=
  (List.range n).flatMap fun i => (List.range n).map fun j => ⟨i, j, g i j⟩

theorem edgeWeight_gridEdges (n : ℕ) (g : ℕ → ℕ → ℕ) (i j : ℕ) :
    edgeWeight (gridEdges n g) i j = if i < n ∧ j < n then g i j else 0 := by
  rw [gridEdges, edgeWeight_flatMap]
  have hinner : ∀ i', edgeWeight ((List.range n).map fun j' => ⟨i', j', g i' j'⟩) i j =
      if i' = i then (if j < n then g i j else 0) else 0 := by
    intro i'
    simp only [edgeWeight, List.map_map, Function.comp_def]
    by_cases h : i' = i
    · subst h
      simp only [true_and, ite_true]
      exact sum_range_ite_eq (a := j) (fun j' => g i' j')
    · simp [h]
  simp only [hinner]
  rw [sum_range_ite_eq (a := i) (fun _ => if j < n then g i j else 0)]
  split_ifs <;> simp_all

theorem mem_gridEdges {n : ℕ} {g : ℕ → ℕ → ℕ} {t : WeightedEdge} (ht : t ∈ gridEdges n g) :
    t.src < n ∧ t.dst < n ∧ t.weight = g t.src t.dst := by
  simp only [gridEdges, List.mem_flatMap, List.mem_range, List.mem_map] at ht
  obtain ⟨i, hi, j, hj, rfl⟩ := ht
  exact ⟨hi, hj, rfl⟩

/-- Entries of the chains of a table between old vertices: the parities of the replaced
weights, when `L > 0`. -/
theorem edgeWeight_tableChain_of_lt (L : ℕ) :
    ∀ (ts : List WeightedEdge) {N : ℕ}, (∀ t ∈ ts, t.src < N ∧ t.dst < N) → ∀ {i j : ℕ}, i < N →
      j < N → edgeWeight (tableChain N L ts) i j =
        edgeWeight (ts.map fun t => ⟨t.src, t.dst,
          if 0 < L then (if t.weight.testBit 0 then 1 else 0) else 0⟩) i j := by
  intro ts
  induction ts with
  | nil => intros; rfl
  | cons t ts ih =>
    intro N hts i j hi hj
    rw [tableChain_cons, edgeWeight_append, edgeWeight_entryChain_of_lt hi hj,
      ih (N := N + 2 * L) (fun t' ht' => by
        have := hts t' (List.mem_cons_of_mem _ ht'); omega) (by omega) (by omega)]
    simp only [List.map_cons, edgeWeight_cons]
    congr 1
    split_ifs <;> simp_all

/-- Entries of the chains of a table at a fresh vertex are at most `1`. -/
theorem edgeWeight_tableChain_le_one (L : ℕ) :
    ∀ (ts : List WeightedEdge) {N : ℕ}, (∀ t ∈ ts, t.src < N ∧ t.dst < N) → ∀ {i j : ℕ},
      (N ≤ i ∨ N ≤ j) → edgeWeight (tableChain N L ts) i j ≤ 1 := by
  intro ts
  induction ts with
  | nil => intros; simp [tableChain_nil]
  | cons t ts ih =>
    intro N hts i j hij
    obtain ⟨htu, htv⟩ := hts t List.mem_cons_self
    have hts' : ∀ t' ∈ ts, t'.src < N + 2 * L ∧ t'.dst < N + 2 * L := fun t' ht' => by
      have := hts t' (List.mem_cons_of_mem _ ht'); omega
    rw [tableChain_cons, edgeWeight_append]
    by_cases hbig : N + 2 * L ≤ i ∨ N + 2 * L ≤ j
    · rw [edgeWeight_eq_zero_of_within (within_entryChain htu htv) hbig, zero_add]
      exact ih hts' hbig
    · have hzero : edgeWeight (ts.map fun t => ⟨t.src, t.dst,
          if 0 < L then (if t.weight.testBit 0 then 1 else 0) else 0⟩) i j = 0 :=
        edgeWeight_eq_zero fun e he hei hej => by
          obtain ⟨t', ht', rfl⟩ := List.mem_map.1 he
          have := hts t' (List.mem_cons_of_mem _ ht')
          dsimp only at hei hej
          omega
      rw [edgeWeight_tableChain_of_lt L ts hts' (by omega) (by omega), hzero, add_zero]
      exact edgeWeight_entryChain_le_one htu htv hij

end PermanentZeroOne

open PermanentZeroOne

/-! ### The 0/1 table of a table of natural numbers -/

/-- Entry `(i, j)` of a table of natural numbers, `0` when missing. -/
def natTableEntry (A : List (List ℕ)) (i j : ℕ) : ℕ :=
  (A.getD i []).getD j 0

/-- The weighted edges of a table of natural numbers: one edge `i → j` of weight `A i j` per
pair. -/
def natTableTriples (A : List (List ℕ)) : List WeightedEdge :=
  gridEdges A.length (natTableEntry A)

/-- The number of chain levels: the binary length of the sum of the entries, which bounds the
binary length of each entry. -/
def natChainLength (A : List (List ℕ)) : ℕ :=
  ((natTableTriples A).map fun t : WeightedEdge => t.weight).sum.size

/-- The edges of the chains replacing the entries of a table of natural numbers. -/
def natTableEdges (A : List (List ℕ)) : List WeightedEdge :=
  tableChain A.length (natChainLength A) (natTableTriples A)

/-- The dimension of the 0/1 table: `n` old vertices and `2L` fresh vertices per entry. -/
def natTableDim (A : List (List ℕ)) : ℕ :=
  A.length + 2 * natChainLength A * (A.length * A.length)

/-- The `N × N` Boolean table whose entry `(i, j)` records an edge `i → j` of positive weight. -/
def edgeTable (N : ℕ) (E : List WeightedEdge) : List (List Bool) :=
  (List.range N).map fun i => (List.range N).map fun j =>
    E.any fun e => e.src == i && e.dst == j && e.weight != 0

/-- **The 0/1 table of a table of natural numbers** (Goldreich, proof of Proposition 6.22): every
entry is replaced by a binary chain of relay vertices. -/
def natTableToZeroOne (A : List (List ℕ)) : List (List Bool) :=
  edgeTable (natTableDim A) (natTableEdges A)

theorem length_edgeTable (N : ℕ) (E : List WeightedEdge) : (edgeTable N E).length = N := by
  simp [edgeTable]

/-- The dimension of `natTableToZeroOne A` is `n + 2 L n²`. -/
theorem length_natTableToZeroOne (A : List (List ℕ)) :
    (natTableToZeroOne A).length = A.length + 2 * natChainLength A * (A.length * A.length) :=
  length_edgeTable _ _

theorem any_edgeTable_iff (E : List WeightedEdge) (i j : ℕ) :
    (E.any fun e => e.src == i && e.dst == j && e.weight != 0) = true ↔ edgeWeight E i j ≠ 0 := by
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, edgeWeight]
  rw [List.sum_eq_zero_iff]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall]
  constructor
  · rintro ⟨e, he, ⟨h1, h2⟩, h3⟩
    exact ⟨e, he, by simp [h1, h2, h3]⟩
  · rintro ⟨e, he, h⟩
    split_ifs at h with h'
    · exact ⟨e, he, h', h⟩
    · exact absurd rfl h

theorem getD_edgeTable {N : ℕ} {E : List WeightedEdge} {i j : ℕ} (hi : i < (edgeTable N E).length)
    (hj : j < N) :
    (edgeTable N E)[i].getD j false = E.any fun e => e.src == i && e.dst == j && e.weight != 0 := by
  simp [edgeTable, List.getD_eq_getElem?_getD, hj]

/-- Reading a 0/1 edge matrix as a Boolean table preserves the permanent. -/
theorem zeroOnePermanent_edgeTable {N : ℕ} {E : List WeightedEdge}
    (h : ∀ i < N, ∀ j < N, edgeWeight E i j ≤ 1) :
    ZeroOnePermanent (edgeTable N E) = (edgeMatrix N E).permanent := by
  have hl := length_edgeTable N E
  rw [ZeroOnePermanent, ← Matrix.permanent_submatrix_equiv_equiv (finCongr hl.symm)
    (finCongr hl.symm)]
  refine congrArg Matrix.permanent ?_
  ext i j
  have hij := h i i.isLt j j.isLt
  simp only [Matrix.submatrix_apply, boolTableMatrix_apply, edgeMatrix, Matrix.of_apply]
  simp only [finCongr_apply, Fin.getElem_fin, Fin.val_cast]
  rw [getD_edgeTable _ j.isLt]
  by_cases hw : edgeWeight E i j = 0
  · rw [hw]
    have : ¬ ((E.any fun e => e.src == (i : ℕ) && e.dst == (j : ℕ) && e.weight != 0) = true) := by
      rw [any_edgeTable_iff]; exact not_not.2 hw
    simp only [Bool.not_eq_true] at this
    rw [this]
    rfl
  · rw [(any_edgeTable_iff E i j).2 hw]
    simp only [Bool.toNat_true]
    omega

theorem natTableTriples_bounds {A : List (List ℕ)} {t : WeightedEdge} (ht : t ∈ natTableTriples A) :
    t.src < A.length ∧ t.dst < A.length ∧ t.weight < 2 ^ natChainLength A := by
  obtain ⟨h1, h2, h3⟩ := mem_gridEdges ht
  refine ⟨h1, h2, ?_⟩
  refine lt_of_le_of_lt ?_ (Nat.lt_size_self _)
  exact List.le_sum_of_mem (List.mem_map_of_mem ht)

/-- **The nonnegative step of Goldreich's Proposition 6.22**: the 0/1 table `natTableToZeroOne A`
has the same permanent as the table of natural numbers `A`. -/
theorem zeroOnePermanent_natTableToZeroOne (A : List (List ℕ)) :
    ZeroOnePermanent (natTableToZeroOne A) = (tableMatrix A).permanent := by
  have hts : ∀ t ∈ natTableTriples A, t.src < A.length ∧ t.dst < A.length :=
    fun t ht => ⟨(natTableTriples_bounds ht).1, (natTableTriples_bounds ht).2.1⟩
  rw [natTableToZeroOne, zeroOnePermanent_edgeTable]
  · rw [natTableEdges, ← List.nil_append (tableChain _ _ _),
      permanent_tableChain _ _ _ (by simp [natTableDim, natTableTriples, gridEdges])
        (fun _ h => absurd h List.not_mem_nil) fun t ht => natTableTriples_bounds ht]
    congr 1
    ext i j
    simp [edgeMatrix, natTableTriples, edgeWeight_gridEdges, tableMatrix_apply, natTableEntry]
  · intro i _ j _
    by_cases hij : A.length ≤ i ∨ A.length ≤ j
    · exact edgeWeight_tableChain_le_one _ _ hts hij
    · rw [natTableEdges, edgeWeight_tableChain_of_lt _ _ hts (by omega) (by omega),
        natTableTriples, gridEdges, List.map_flatMap]
      simp only [List.map_map, Function.comp_def]
      rw [← gridEdges, edgeWeight_gridEdges]
      split_ifs <;> omega

end Cslib.Complexity
