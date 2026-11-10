/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Karger.Contraction
public import Complexity.DataStructure.Memory.Field
public import Complexity.DataStructure.StateTransition.WP

/-!
# The contraction structure over memory: layout and queries

This file lays out the contraction structure `Karger.spec` in memory and implements its three
queries as programs over the memory oracle `Memory.spec w`. The contraction itself is a separate
module.

The storage for at most `capacity` supervertices is one contiguous region with four named fields
(`Layout`): a cell `size` holding the number `k` of supervertices, a cell `total` holding the total
doubled weight `S`, a `degree` array whose entry `i` holds the weighted degree of supervertex `i`,
and the `weight` matrix, stored row by row with row stride `capacity` (`Layout.row`). The
abstraction function reads the first `k` rows and columns of the matrix (`abs`). The invariant
records that the degree array and the total cell are consistent with the matrix, that the matrix
is a multigraph, and that the total fits a word (`Inv`).

`size` and `total` read one cell each. `pairAt r` finds the pair sampled at offset `r` by two
prefix-sum scans (`scan`): along the degree array for the row `u`, then along row `u` for the
column `v`. It reads at most `2 k + 1` cells (`wp_pairAt`). The scan is the single-draw sampling
of `Karger.Graph`, and its answer is `sampledPair` (`IsSampledPair`, `sampledPair_eq`).

Programs are evaluated with the weakest precondition `StateTransitionSpec.wp`, which carries the
answer, the final state and the memory charge. No register, word bound beyond `Memory.valid`, or
instruction count appears. The machine-level counterparts are `uScan_exec` and `vScan_exec` in
`Cslib.Algorithms.WordRAM.Karger`.

## Main definitions

* `Layout`, `Layout.size`, `Layout.total`, `Layout.degree`, `Layout.weight`, `Layout.row`: the
  storage and its fields.
* `Layout.mat`, `Layout.graph`, `abs`: the matrix view of memory and the abstraction function.
* `Inv`: the implementation invariant.
* `scan`, `pairAt`: the prefix-sum scan and the sampling query.

## Main results

* `wp_scan`: a scan finds the first entry whose prefix sum exceeds the offset.
* `wp_pairAt`: `pairAt r` answers `sampledPair` and reads at most `2 k + 1` cells.
* `degBefore_eq_sum_range`, `weightBefore_eq_sum_range`, `totalDoubledWeight_eq_sum_range`,
  `rowDeg_eq_sum_range`: the prefix sums of `Karger.Graph` as sums over ranges.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Karger.Memory

open Finset Cslib.WordRAM Cslib.WeightedCut Cslib.Algorithms.WordRAM.Karger Cslib.DataStructure
  Cslib.DataStructure.Memory Cslib.DataStructure.StateTransitionSpec

/-! ## Layout -/

/-- The storage of the contraction structure for at most `capacity` supervertices: one region
from address `base`, holding the fields `size`, `total`, `degree` and `weight` in that order. -/
structure Layout where
  /-- The first address of the region. -/
  base : ℕ
  /-- The largest number of supervertices, and the row stride of the matrix. -/
  capacity : ℕ

namespace Layout

variable (L : Layout)

/-- The cell holding the number of supervertices. -/
def size : Block := ⟨L.base, 1⟩

/-- The cell holding the total doubled weight. -/
def total : Block := ⟨L.base + 1, 1⟩

/-- The degree array: entry `i` holds the weighted degree of supervertex `i`. -/
def degree : Block := ⟨L.base + 2, L.capacity⟩

/-- The weight matrix, row by row, with row stride `capacity`. -/
def weight : Block := ⟨L.base + 2 + L.capacity, L.capacity * L.capacity⟩

/-- Row `i` of the weight matrix. -/
def row (i : ℕ) : Block := ⟨L.weight.base + i * L.capacity, L.capacity⟩

/-- One past the last address of the region. -/
def limit : ℕ := L.base + 2 + L.capacity + L.capacity * L.capacity

/-- The cells of the region. -/
def footprint : Finset ℕ := Finset.Ico L.base L.limit

/-- Entry `(i, j)` of the weight matrix in memory `m`. -/
def mat (m : ℕ → ℕ) (i j : ℕ) : ℕ := m ((L.row i).base + j)

/-- The graph on `k` supervertices that memory `m` holds. -/
def graph (k : ℕ) (m : ℕ → ℕ) : Graph := ⟨k, fun i j => L.mat m i j⟩

/-! ### Addresses -/

variable {L}

/-- A matrix entry within the capacity lies in the weight field. -/
theorem row_base_add_lt {i j : ℕ} (hi : i < L.capacity) (hj : j < L.capacity) :
    (L.row i).base + j < L.weight.base + L.weight.length := by
  simp only [row, weight]
  nlinarith

/-- Distinct matrix entries within the capacity have distinct addresses. -/
theorem row_base_add_inj {i j a b : ℕ} (hj : j < L.capacity) (hb : b < L.capacity)
    (h : (L.row i).base + j = (L.row a).base + b) : i = a ∧ j = b := by
  simp only [row] at h
  have h' : j + L.capacity * i = b + L.capacity * a := by linarith
  have hpos : 0 < L.capacity := by omega
  have hi : i = a := by
    have := congrArg (· / L.capacity) h'
    simp only [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hj, Nat.div_eq_of_lt hb] at this
    omega
  subst hi
  exact ⟨rfl, by omega⟩

/-- Writing a matrix entry within the capacity updates that entry of the matrix view. -/
theorem mat_update {m : ℕ → ℕ} {a b : ℕ} (hb : b < L.capacity) (x : ℕ) {i j : ℕ}
    (hj : j < L.capacity) :
    L.mat (Function.update m ((L.row a).base + b) x) i j =
      if i = a ∧ j = b then x else L.mat m i j := by
  unfold mat
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact Function.update_self _ _ _
  · refine Function.update_of_ne (fun he => h ?_) _ _
    exact row_base_add_inj hj hb he

/-- Writing outside the weight field leaves the matrix view unchanged. -/
theorem mat_update_of_not_owns {m : ℕ → ℕ} {a : ℕ} (ha : ¬L.weight.Owns a) (x : ℕ) {i j : ℕ}
    (hi : i < L.capacity) (hj : j < L.capacity) :
    L.mat (Function.update m a x) i j = L.mat m i j := by
  refine Function.update_of_ne (fun he => ha ?_) _ _
  rw [← he]
  exact ⟨by simp only [row, weight]; omega, row_base_add_lt hi hj⟩

/-- The matrix view of the first `k` rows and columns depends only on those cells. -/
theorem graph_congr {k : ℕ} {m m' : ℕ → ℕ} (h : ∀ i j, i < k → j < k → L.mat m' i j = L.mat m i j) :
    L.graph k m' = L.graph k m := by
  simp only [graph]
  congr
  funext i j
  exact h i j i.isLt j.isLt

end Layout

variable (L : Layout) {w : ℕ}

/-- The abstraction function: the graph on the first `k` rows and columns of the matrix, where
`k` is the size cell. -/
def abs (s : Memory.State) : Graph := L.graph (s.mem L.size.base) s.mem

@[simp] theorem abs_size (s : Memory.State) : (abs L s).size = s.mem L.size.base := rfl

/-- The implementation invariant at word size `w`. The region is allocated and the size is within
the capacity, which fits a word. The matrix is a multigraph, the degree array and the total cell
agree with it, and the total fits a word. -/
structure Inv (w : ℕ) (s : Memory.State) : Prop where
  /-- The region is allocated. -/
  allocated : L.limit ≤ s.frontier
  /-- The capacity fits a word, hence so does every size. -/
  capacity_fits : Fits w L.capacity
  /-- The size is within the capacity. -/
  size_le : s.mem L.size.base ≤ L.capacity
  /-- The matrix is a multigraph. -/
  multigraph : IsMultigraph (abs L s).weight
  /-- The degree array holds the weighted degrees. -/
  degree_eq : ∀ i : Fin (abs L s).size, s.mem (L.degree.base + i) = rowDeg (abs L s).weight i
  /-- The total cell holds the total doubled weight. -/
  total_eq : s.mem L.total.base = totalDoubledWeight (abs L s).weight
  /-- The total fits a word. -/
  total_fits : Fits w (s.mem L.total.base)

variable {L}

/-- Every cell of the region is allocated. -/
theorem Inv.lt_frontier {s : Memory.State} (hs : Inv L w s) {a : ℕ} (ha : a ∈ L.footprint) :
    a < s.frontier :=
  (Finset.mem_Ico.mp ha).2.trans_le hs.allocated

/-- **A state holding a graph.** If the size cell holds `k ≤ capacity`, and the matrix, the degree
array and the total cell hold a multigraph `W`, its degrees and its total, which fits a word, then
the state abstracts to `W` and satisfies the invariant. -/
theorem abs_eq_and_inv {s : Memory.State} {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    (hlim : L.limit ≤ s.frontier) (hC : Fits w L.capacity) (hk : k ≤ L.capacity)
    (hsize : s.mem L.size.base = k) (hmat : ∀ i j : Fin k, L.mat s.mem i j = W i j)
    (hdeg : ∀ i : Fin k, s.mem (L.degree.base + i) = rowDeg W i)
    (htotal : s.mem L.total.base = totalDoubledWeight W) (hfit : Fits w (totalDoubledWeight W)) :
    abs L s = ⟨k, W⟩ ∧ Inv L w s := by
  have habs : abs L s = ⟨k, W⟩ := by
    rw [abs, hsize]
    exact congrArg (Graph.mk k) (funext₂ hmat)
  exact ⟨habs, hlim, hC, hsize ▸ hk, by rw [habs]; exact hW, by rw [habs]; exact hdeg,
    by rw [habs]; exact htotal, by rw [htotal]; exact hfit⟩

/-- The cells of a state satisfying the invariant hold its abstraction. -/
theorem Inv.cells {s : Memory.State} (hs : Inv L w s) {k : ℕ} {W : Fin k → Fin k → ℕ}
    (habs : abs L s = ⟨k, W⟩) :
    s.mem L.size.base = k ∧ (∀ i j : Fin k, L.mat s.mem i j = W i j) ∧ IsMultigraph W ∧
      (∀ i : Fin k, s.mem (L.degree.base + i) = rowDeg W i) ∧
      s.mem L.total.base = totalDoubledWeight W := by
  obtain ⟨hk, hW⟩ := Graph.mk.inj habs
  subst hk
  obtain rfl := eq_of_heq hW
  exact ⟨rfl, fun _ _ => rfl, hs.multigraph, hs.degree_eq, hs.total_eq⟩

/-- Matrix entries within the capacity belong to the region. -/
theorem Layout.row_base_add_mem_footprint {i j : ℕ} (hi : i < L.capacity) (hj : j < L.capacity) :
    (L.row i).base + j ∈ L.footprint :=
  Finset.mem_Ico.mpr ⟨by simp only [Layout.row, Layout.weight]; omega,
    (Layout.row_base_add_lt hi hj).trans_le (by simp only [Layout.weight, Layout.limit]; omega)⟩

/-- Degree cells within the capacity belong to the region. -/
theorem Layout.degree_mem_footprint {i : ℕ} (hi : i < L.capacity) :
    L.degree.base + i ∈ L.footprint :=
  Finset.mem_Ico.mpr ⟨by simp only [Layout.degree]; omega, by
    simp only [Layout.degree, Layout.limit]; nlinarith⟩

/-- The size cell belongs to the region. -/
theorem Layout.size_mem_footprint : L.size.base ∈ L.footprint :=
  Finset.mem_Ico.mpr ⟨le_rfl, by simp only [Layout.size, Layout.limit]; omega⟩

/-- The total cell belongs to the region. -/
theorem Layout.total_mem_footprint : L.total.base ∈ L.footprint :=
  Finset.mem_Ico.mpr ⟨by simp only [Layout.total]; omega,
    by simp only [Layout.total, Layout.limit]; omega⟩

/-- The size, total and degree cells lie outside the weight field. -/
theorem Layout.not_owns_size : ¬L.weight.Owns L.size.base := by
  simp only [Block.Owns, Layout.weight, Layout.size]; omega

theorem Layout.not_owns_total : ¬L.weight.Owns L.total.base := by
  simp only [Block.Owns, Layout.weight, Layout.total]; omega

theorem Layout.not_owns_degree {i : ℕ} (hi : i < L.capacity) :
    ¬L.weight.Owns (L.degree.base + i) := by
  simp only [Block.Owns, Layout.weight, Layout.degree]; omega

/-- The size, total and degree cells are distinct. -/
theorem Layout.size_ne_total : L.size.base ≠ L.total.base := by
  simp only [Layout.size, Layout.total]; omega

theorem Layout.size_ne_degree (i : ℕ) : L.size.base ≠ L.degree.base + i := by
  simp only [Layout.size, Layout.degree]; omega

theorem Layout.total_ne_degree (i : ℕ) : L.total.base ≠ L.degree.base + i := by
  simp only [Layout.total, Layout.degree]; omega

/-- A cell outside the region belongs to no field. -/
theorem Layout.not_owns_of_not_mem {a : ℕ} (ha : a ∉ L.footprint) :
    ¬L.weight.Owns a ∧ a ≠ L.size.base ∧ a ≠ L.total.base ∧
      ∀ i < L.capacity, a ≠ L.degree.base + i := by
  simp only [Layout.footprint, Finset.mem_Ico, not_and_or, not_le, not_lt] at ha
  simp only [Block.Owns, Layout.weight, Layout.size, Layout.total, Layout.degree,
    Layout.limit] at ha ⊢
  refine ⟨?_, ?_, ?_, fun i hi => ?_⟩ <;> omega

/-- The weight field is allocated. -/
theorem Inv.weight_le {s : Memory.State} (hs : Inv L w s) :
    L.weight.base + L.weight.length ≤ s.frontier := by
  have := hs.allocated
  simp only [Layout.weight, Layout.limit] at this ⊢
  omega

/-- The abstraction reads only the region. -/
theorem abs_congr {s s' : Memory.State} (hs : Inv L w s)
    (h : ∀ a ∈ L.footprint, s'.mem a = s.mem a) : abs L s' = abs L s := by
  have hsize : s'.mem L.size.base = s.mem L.size.base := h _ L.size_mem_footprint
  have hk := hs.size_le
  rw [abs, abs, hsize]
  exact Layout.graph_congr fun i j hi hj =>
    h _ (L.row_base_add_mem_footprint (by omega) (by omega))

/-- The invariant reads only the region, and survives a growing frontier. -/
theorem Inv.congr {s s' : Memory.State} (hs : Inv L w s)
    (h : ∀ a ∈ L.footprint, s'.mem a = s.mem a) (hf : s.frontier ≤ s'.frontier) :
    Inv L w s' := by
  have habs := abs_congr hs h
  have hsize : s'.mem L.size.base = s.mem L.size.base := h _ L.size_mem_footprint
  have htot : s'.mem L.total.base = s.mem L.total.base := h _ L.total_mem_footprint
  have hk := hs.size_le
  refine ⟨hs.allocated.trans hf, hs.capacity_fits, hsize ▸ hk, habs ▸ hs.multigraph, ?_,
    by rw [habs, htot]; exact hs.total_eq, htot ▸ hs.total_fits⟩
  rw [habs]
  intro i
  rw [h _ (L.degree_mem_footprint (by have := i.isLt; simp only [abs_size] at this; omega)),
    hs.degree_eq i]

/-! ## Prefix sums -/

/-- The degrees before `u` as a sum over a range. -/
theorem degBefore_eq_sum_range {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k) (g : ℕ → ℕ)
    (hg : ∀ j (hj : j < k), g j = rowDeg W ⟨j, hj⟩) :
    degBefore W u = ∑ j ∈ range u, g j := by
  rw [degBefore, filter_gt_eq_Iio, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, sum_map]
  exact sum_congr rfl fun a _ => (hg a a.isLt).symm

/-- The weights of row `u` before column `v` as a sum over a range. -/
theorem weightBefore_eq_sum_range {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) (g : ℕ → ℕ)
    (hg : ∀ j (hj : j < k), g j = W u ⟨j, hj⟩) :
    weightBefore W u v = ∑ j ∈ range v, g j := by
  rw [weightBefore, filter_gt_eq_Iio, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, sum_map]
  exact sum_congr rfl fun a _ => (hg a a.isLt).symm

/-- The weighted degree as a sum over a range. -/
theorem rowDeg_eq_sum_range {k : ℕ} (W : Fin k → Fin k → ℕ) (u : Fin k) (g : ℕ → ℕ)
    (hg : ∀ j (hj : j < k), g j = W u ⟨j, hj⟩) : rowDeg W u = ∑ j ∈ range k, g j := by
  rw [rowDeg, ← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun a _ => (hg a a.isLt).symm

/-- The total doubled weight as a sum of degrees over a range. -/
theorem totalDoubledWeight_eq_sum_range {k : ℕ} (W : Fin k → Fin k → ℕ) (g : ℕ → ℕ)
    (hg : ∀ j (hj : j < k), g j = rowDeg W ⟨j, hj⟩) :
    totalDoubledWeight W = ∑ j ∈ range k, g j := by
  rw [totalDoubledWeight, ← Fin.sum_univ_eq_sum_range]
  exact sum_congr rfl fun a _ => (hg a a.isLt).symm

/-! ## Queries -/

variable (L)

/-- Read the number of supervertices. -/
def size : Prog ℕ := L.size.get 0

/-- Read the total doubled weight. -/
def total : Prog ℕ := L.total.get 0

/-- **Prefix-sum scan.** Read the entries `i, i + 1, …` of the field `b`, at most `n` of them,
subtracting each from the offset `r` until an entry exceeds what remains. Answer that entry's
index and the remaining offset. -/
def scan (b : Block) : ℕ → ℕ → ℕ → Prog (ℕ × ℕ)
  | 0, i, r => pure (i, r)
  | n + 1, i, r => do
    let x ← b.get i
    if r < x then pure (i, r) else scan b n (i + 1) (r - x)

/-- The pair sampled at offset `r`: scan the degree array for the row, then that row for the
column. -/
def pairAt (r : ℕ) : Prog (ℕ × ℕ) := do
  let k ← L.size.get 0
  let (u, r') ← scan L.degree k 0 r
  let (v, _) ← scan (L.row u) k 0 r'
  pure (u, v)

variable {L}

/-- **The scan finds the sampled entry.** If the offset `r` is below the sum of the `n` entries
from `i`, the scan reads the entries `i, …, u` and answers the first index `u` whose prefix sum
exceeds `r`, together with what remains of `r` after the entries before `u`. -/
theorem wp_scan {b : Block} {s : Memory.State} :
    ∀ (n i r : ℕ) (Q : ℕ × ℕ → Memory.State → ℕ → Prop),
      (∀ j < i + n, b.base + j < s.frontier) →
      r < ∑ j ∈ Ico i (i + n), s.mem (b.base + j) →
      (∀ u, i ≤ u → u < i + n → ∑ j ∈ Ico i u, s.mem (b.base + j) ≤ r →
        r < ∑ j ∈ Ico i (u + 1), s.mem (b.base + j) →
          Q (u, r - ∑ j ∈ Ico i u, s.mem (b.base + j)) s (u + 1 - i)) →
      (Memory.spec w).wp charge (scan b n i r) Q s
  | 0, i, r, Q, _, hr, _ => by simp at hr
  | n + 1, i, r, Q, hf, hr, hQ => by
    rw [scan, wp_lift_bind]
    refine ⟨hf i (by omega), ?_⟩
    change (Memory.spec w).wp charge (if r < s.mem (b.base + i) then pure (i, r) else
      scan b n (i + 1) (r - s.mem (b.base + i))) (fun a s' t => Q a s' (t + 1)) s
    have hsplit := sum_eq_sum_Ico_succ_bot (show i < i + (n + 1) by omega)
      fun j => s.mem (b.base + j)
    by_cases hx : r < s.mem (b.base + i)
    · rw [ite_eq_left hx]
      have h := hQ i le_rfl (by omega) (by simp) (by simpa using hx)
      simp only [Ico_self, sum_empty, Nat.sub_zero, Nat.add_sub_cancel_left] at h
      simpa using h
    · rw [ite_eq_right hx]
      refine wp_scan n (i + 1) (r - s.mem (b.base + i)) _ (fun j hj => hf j (by omega))
        (by rw [show i + 1 + n = i + (n + 1) by omega]; omega) fun u hu₁ hu₂ hle hlt => ?_
      have h₁ := sum_eq_sum_Ico_succ_bot (show i < u by omega) fun j => s.mem (b.base + j)
      have h₂ := sum_eq_sum_Ico_succ_bot (show i < u + 1 by omega) fun j => s.mem (b.base + j)
      have hQu := hQ u (by omega) (by omega) (by omega) (by omega)
      rw [h₁, ← Nat.sub_sub,
        show u + 1 - i = u + 1 - (i + 1) + 1 by omega] at hQu
      exact hQu


/-- The degree array as a sum over a range is the total doubled weight. -/
theorem Inv.sum_degree {s : Memory.State} (hs : Inv L w s) :
    ∑ j ∈ range (abs L s).size, s.mem (L.degree.base + j) =
      totalDoubledWeight (abs L s).weight :=
  (totalDoubledWeight_eq_sum_range _ _ fun j hj => hs.degree_eq ⟨j, hj⟩).symm

/-- **The sampling query.** At an offset below the total weight, `pairAt r` answers the pair
sampled at `r`, leaves memory unchanged, and reads at most `2 k + 1` cells. -/
theorem wp_pairAt {s : Memory.State} (hs : Inv L w s) {r : ℕ}
    (hr : r < totalDoubledWeight (abs L s).weight) :
    (Memory.spec w).wp charge (pairAt L r)
      (fun a s' t => a = sampledPair (abs L s).weight r ∧ s' = s ∧
        t ≤ 2 * (abs L s).size + 1) s := by
  have hk : s.mem L.size.base ≤ L.capacity := hs.size_le
  have hwl := hs.weight_le
  rw [pairAt, wp_lift_bind]
  refine ⟨hs.lt_frontier L.size_mem_footprint, ?_⟩
  dsimp only [StateTransitionSpec.stepFn, step_read, charge_read, Nat.add_zero]
  rw [wp_bind]
  refine wp_scan _ 0 r _ (fun j hj => hs.lt_frontier (L.degree_mem_footprint (by omega)))
    (by rw [Nat.zero_add, ← range_eq_Ico, ← abs_size, hs.sum_degree]; exact hr)
    fun u _ hu hle hlt => ?_
  simp only [Nat.zero_add, ← range_eq_Ico, sum_range_succ] at hu hle hlt
  rw [hs.degree_eq ⟨u, hu⟩] at hlt
  dsimp only
  rw [wp_bind]
  have hrd : rowDeg (abs L s).weight ⟨u, hu⟩ =
      ∑ j ∈ Ico 0 (0 + s.mem L.size.base), s.mem ((L.row u).base + j) := by
    rw [Nat.zero_add, ← range_eq_Ico]
    exact rowDeg_eq_sum_range _ _ _ fun j hj => rfl
  have hsu : ∑ j ∈ Ico 0 u, s.mem (L.degree.base + j) =
      ∑ j ∈ range u, s.mem (L.degree.base + j) := by rw [range_eq_Ico]
  refine wp_scan _ 0 _ _ (fun j hj => (Layout.row_base_add_lt (hu.trans_le hk)
      (show j < L.capacity by omega)).trans_le hwl)
    (by rw [← hrd, hsu]; omega) fun v _ hv hle' hlt' => ?_
  simp only [Nat.zero_add, ← range_eq_Ico, sum_range_succ] at hv hle' hlt'
  dsimp only
  have hdb : degBefore (abs L s).weight ⟨u, hu⟩ = ∑ j ∈ range u, s.mem (L.degree.base + j) :=
    degBefore_eq_sum_range _ _ _ fun j hj => hs.degree_eq ⟨j, hj⟩
  have hwb : weightBefore (abs L s).weight ⟨u, hu⟩ ⟨v, hv⟩ =
      ∑ j ∈ range v, s.mem ((L.row u).base + j) :=
    weightBefore_eq_sum_range _ _ _ _ fun j hj => rfl
  have hsamp : IsSampledPair (abs L s).weight r ⟨u, hu⟩ ⟨v, hv⟩ := by
    have hw : (abs L s).weight ⟨u, hu⟩ ⟨v, hv⟩ = s.mem ((L.row u).base + v) := rfl
    unfold IsSampledPair edgeOffset
    omega
  refine ⟨(sampledPair_eq hsamp).symm, rfl, ?_⟩
  simp only [abs_size] at hu hv ⊢
  omega

end Cslib.Algorithms.Lean.Karger.Memory
