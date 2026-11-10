/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.CellProbe.Defs
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Foundations.Data.Code.HammingBound

/-!
# Chronogram bookkeeping for cell-probe schemes

The chronogram method of Fredman and Saks [FredmanSaks1989] proves dynamic cell-probe lower bounds
by splitting an update sequence into consecutive *epochs* and asking which epoch last wrote the
cells that a later query probes (see [PatrascuDemaine2006], §3.1, p. 5, for the history of the
method). Here the epoch that last *probed* a cell stands in for the epoch that last wrote it: a cell
that no later epoch probes keeps its contents, and the cells probed later are exactly the ones whose
final contents an encoder records.

This file supplies the epoch-independent bookkeeping for a deterministic step-indexed
scheme `D : IndexedScheme Op Result cells w` that runs consecutive operation segments
`seg 0, seg 1, …` from step `t₀` and memory `m₀`.

For a run of `L` segments and a segment `j < L`, `laterCells` is the set of cells probed by segments
`j + 1, …, L - 1`, and `lastCells` is the set of cells probed by segment `j` and by no later
segment. `overlayMem` is the memory that a decoder can reconstruct from the memory before segment
`j` together with the final contents of the cells probed afterwards. The main facts are:

* the overlay agrees with the true final memory outside `lastCells`, and it differs from the
  memory before segment `j` on at most `#laterCells` cells, which is at most `d * Σ |seg k|` when
  every step has depth at most `d`;
* the sets `lastCells L j`, `j < L`, are pairwise disjoint, so a set of `p` probed cells meets at
  most `p` of them;
* a query whose probed cells avoid `lastCells L j` gives the same answer on the overlay as on the
  true memory.

At most `(cells * (2 ^ w - 1) + 1) ^ r` memories lie within Hamming distance `r` of a fixed memory,
which bounds the number of overlays in an encoding argument.

## Main definitions

* `Cslib.CellProbe.IndexedScheme.segStart`, `Cslib.CellProbe.IndexedScheme.segMem`: the step index
  and memory at which segment `j` starts.
* `Cslib.CellProbe.IndexedScheme.segCells`, `Cslib.CellProbe.IndexedScheme.laterCells`,
  `Cslib.CellProbe.IndexedScheme.lastCells`: cells probed by segment `j`, by segments after `j`,
  and by segment `j` but no later segment.
* `Cslib.CellProbe.IndexedScheme.overlayMem`: the final contents of `laterCells` over the memory
  before segment `j`.

## Main results

* `Cslib.CellProbe.IndexedScheme.runInterval_flatMap_range`,
  `Cslib.CellProbe.IndexedScheme.runInterval_flatMap_range_append`: running the concatenated
  segments reaches `segStart L` and `segMem L`.
* `Cslib.CellProbe.IndexedScheme.segMem_eq_of_notMem_laterCells`: cells untouched after segment
  `j` keep their contents from the end of segment `j`.
* `Cslib.CellProbe.IndexedScheme.overlayMem_eq_of_notMem_lastCells`,
  `Cslib.CellProbe.IndexedScheme.hammingDist_overlayMem_le`: the overlay agrees with the final
  memory outside `lastCells` and is close to the memory before segment `j`.
* `Cslib.CellProbe.IndexedScheme.pairwiseDisjoint_lastCells`,
  `Cslib.CellProbe.IndexedScheme.card_filter_lastCells_le`: disjointness of the last-touched sets
  and the resulting bound on the number of epochs a probe set meets.
* `Cslib.CellProbe.IndexedScheme.card_laterCells_le`,
  `Cslib.CellProbe.IndexedScheme.probesInterval_le_mul_length`: probe-count bounds under a
  uniform depth bound.
* `Cslib.CellProbe.IndexedScheme.run_overlayMem_eq`: a query avoiding `lastCells` answers the same
  on the overlay.
* `Cslib.CellProbe.card_filter_hammingDist_le_le_pow`: at most `(cells * (2 ^ w - 1) + 1) ^ r`
  memories within Hamming distance `r` of a memory, from
  `Cslib.Code.card_filter_hammingDist_le_le_pow`.

## References

* [M. L. Fredman and M. E. Saks, *The cell probe complexity of dynamic data
  structures*][FredmanSaks1989]
* [M. Pătraşcu and E. D. Demaine, *Logarithmic Lower Bounds in the Cell-Probe
  Model*][PatrascuDemaine2006]
-/

public section

namespace Cslib.CellProbe

open Finset

/-- At most `(cells * (2 ^ w - 1) + 1) ^ r` memories of `cells` cells of `w` bits lie within
Hamming distance `r` of a fixed memory `m`: the number of overlays in an encoding argument. -/
theorem card_filter_hammingDist_le_le_pow {cells w : ℕ} (m : Mem cells w) (r : ℕ) :
    #{m' : Mem cells w | hammingDist m m' ≤ r} ≤ (cells * (2 ^ w - 1) + 1) ^ r := by
  simpa using Code.card_filter_hammingDist_le_le_pow (q := 2 ^ w) (fun _ => by simp) m r

namespace IndexedScheme

variable {Op : Type*} {Result : Op → Type} {cells w : ℕ}

/-! ### Segments, their start points and their probed cells -/

/-- The step index at which segment `j` starts when the segments `seg 0, seg 1, …` run
consecutively from step `t₀`. -/
@[expose] def segStart (seg : ℕ → List Op) (t₀ : ℕ) (j : ℕ) : ℕ :=
  t₀ + ∑ k ∈ range j, (seg k).length

/-- The memory before segment `j` when `D` runs the segments `seg 0, seg 1, …` consecutively from
step `t₀` and memory `m₀`. -/
@[expose] def segMem (D : IndexedScheme Op Result cells w) (seg : ℕ → List Op) (t₀ : ℕ)
    (m₀ : Mem cells w) : ℕ → Mem cells w
  | 0 => m₀
  | j + 1 => (D.runInterval (segStart seg t₀ j) (D.segMem seg t₀ m₀ j) (seg j)).2

/-- The cells probed while `D` runs segment `j`. -/
@[expose] def segCells (D : IndexedScheme Op Result cells w)
    (seg : ℕ → List Op) (t₀ : ℕ) (m₀ : Mem cells w) (j : ℕ) : Finset (Fin cells) :=
  D.probedCellsInterval (segStart seg t₀ j) (D.segMem seg t₀ m₀ j) (seg j)

/-- The cells probed by the segments strictly between `j` and `L`. -/
@[expose] def laterCells (D : IndexedScheme Op Result cells w)
    (seg : ℕ → List Op) (t₀ : ℕ) (m₀ : Mem cells w) (L j : ℕ) : Finset (Fin cells) :=
  (Ioo j L).biUnion (D.segCells seg t₀ m₀)

/-- The cells probed by segment `j` and by no segment between `j` and `L`: the cells whose last
probe before step `segStart seg t₀ L` happened during segment `j`. -/
@[expose] def lastCells (D : IndexedScheme Op Result cells w)
    (seg : ℕ → List Op) (t₀ : ℕ) (m₀ : Mem cells w) (L j : ℕ) : Finset (Fin cells) :=
  D.segCells seg t₀ m₀ j \ D.laterCells seg t₀ m₀ L j

/-- The final contents of the cells probed after segment `j`, laid over the memory before segment
`j`. -/
@[expose] def overlayMem (D : IndexedScheme Op Result cells w)
    (seg : ℕ → List Op) (t₀ : ℕ) (m₀ : Mem cells w) (L j : ℕ) : Mem cells w :=
  fun c => if c ∈ D.laterCells seg t₀ m₀ L j then D.segMem seg t₀ m₀ L c
    else D.segMem seg t₀ m₀ j c

variable (D : IndexedScheme Op Result cells w) (seg : ℕ → List Op) (t₀ : ℕ) (m₀ : Mem cells w)

@[simp]
theorem segStart_zero : segStart seg t₀ 0 = t₀ := by
  simp [segStart]

theorem segStart_succ (j : ℕ) : segStart seg t₀ (j + 1) = segStart seg t₀ j + (seg j).length := by
  simp [segStart, sum_range_succ, Nat.add_assoc]

@[simp]
theorem segMem_zero : D.segMem seg t₀ m₀ 0 = m₀ :=
  rfl

theorem segMem_succ (j : ℕ) :
    D.segMem seg t₀ m₀ (j + 1) =
      (D.runInterval (segStart seg t₀ j) (D.segMem seg t₀ m₀ j) (seg j)).2 :=
  rfl

/-- The start of segment `j` depends only on the lengths of the segments before it. -/
theorem segStart_congr {seg seg' : ℕ → List Op} {j : ℕ} (h : ∀ k < j, seg k = seg' k) :
    segStart seg t₀ j = segStart seg' t₀ j := by
  unfold segStart
  rw [sum_congr rfl fun k hk => by rw [h k (mem_range.mp hk)]]

/-- The memory before segment `j` depends only on the segments before it. -/
theorem segMem_congr {seg seg' : ℕ → List Op} {j : ℕ} (h : ∀ k < j, seg k = seg' k) :
    D.segMem seg t₀ m₀ j = D.segMem seg' t₀ m₀ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h' : ∀ k < j, seg k = seg' k := fun k hk => h k (by omega)
    rw [segMem_succ, segMem_succ, ih h', segStart_congr t₀ h', h j (by omega)]

/-- Running the concatenation of the first `L` segments reaches step `segStart seg t₀ L` and memory
`segMem L`. -/
theorem runInterval_flatMap_range (L : ℕ) :
    (D.runInterval t₀ m₀ ((List.range L).flatMap seg)).2 = D.segMem seg t₀ m₀ L ∧
      t₀ + ((List.range L).flatMap seg).length = segStart seg t₀ L := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, runInterval_append,
      List.length_append, ← Nat.add_assoc, ih.2, ih.1, segMem_succ, segStart_succ]
    exact ⟨rfl, rfl⟩

/-- Running the first `L` segments followed by `ops` runs `ops` from step `segStart seg t₀ L` and
memory `segMem L`. -/
theorem runInterval_flatMap_range_append (L : ℕ) (ops : List Op) :
    D.runInterval t₀ m₀ ((List.range L).flatMap seg ++ ops) =
      ((D.runInterval t₀ m₀ ((List.range L).flatMap seg)).1 ++
        (D.runInterval (segStart seg t₀ L) (D.segMem seg t₀ m₀ L) ops).1,
       (D.runInterval (segStart seg t₀ L) (D.segMem seg t₀ m₀ L) ops).2) := by
  obtain ⟨hmem, hlen⟩ := D.runInterval_flatMap_range seg t₀ m₀ L
  rw [runInterval_append, hmem, hlen]

/-! ### Later and last-touched cells -/

/-- A cell lies in `laterCells L j` iff some segment strictly between `j` and `L` probes it. -/
theorem mem_laterCells {L j : ℕ} {c : Fin cells} :
    c ∈ D.laterCells seg t₀ m₀ L j ↔ ∃ k, j < k ∧ k < L ∧ c ∈ D.segCells seg t₀ m₀ k := by
  simp [laterCells, and_assoc]

/-- Every segment strictly between `j` and `L` probes only cells of `laterCells L j`. -/
theorem segCells_subset_laterCells {L j k : ℕ} (hjk : j < k) (hkL : k < L) :
    D.segCells seg t₀ m₀ k ⊆ D.laterCells seg t₀ m₀ L j :=
  subset_biUnion_of_mem (D.segCells seg t₀ m₀) (mem_Ioo.mpr ⟨hjk, hkL⟩)

/-- The cells last touched by segment `j` are probed by segment `j`. -/
theorem lastCells_subset_segCells (L j : ℕ) :
    D.lastCells seg t₀ m₀ L j ⊆ D.segCells seg t₀ m₀ j :=
  sdiff_subset

/-- **Frame across segments**: a cell probed by no segment strictly between `j` and `L` keeps the
contents it had at the end of segment `j`. -/
theorem segMem_eq_of_notMem_laterCells {L j : ℕ} (hjL : j < L) {c : Fin cells}
    (hc : c ∉ D.laterCells seg t₀ m₀ L j) :
    D.segMem seg t₀ m₀ L c = D.segMem seg t₀ m₀ (j + 1) c := by
  obtain ⟨n, rfl⟩ : ∃ n, L = j + 1 + n := ⟨L - (j + 1), by omega⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    have hc' : c ∉ D.laterCells seg t₀ m₀ (j + 1 + n) j := fun h =>
      hc ((biUnion_subset_biUnion_of_subset_left _ (Ioo_subset_Ioo_right (by omega))) h)
    have hcn : c ∉ D.segCells seg t₀ m₀ (j + 1 + n) := fun h =>
      hc (D.segCells_subset_laterCells seg t₀ m₀ (by omega) (by omega) h)
    rw [← Nat.add_assoc, segMem_succ,
      D.nextMem_runInterval_eq_of_notMem_probedCellsInterval _ _ _ hcn, ih (by omega) hc']

/-- The overlay agrees with the memory before segment `j` outside `laterCells`. -/
theorem overlayMem_eq_segMem_of_notMem_laterCells {L j : ℕ} {c : Fin cells}
    (hc : c ∉ D.laterCells seg t₀ m₀ L j) :
    D.overlayMem seg t₀ m₀ L j c = D.segMem seg t₀ m₀ j c := by
  simp [overlayMem, hc]

/-- **Overlay agreement**: the overlay agrees with the memory after all `L` segments outside the
cells last touched by segment `j`. -/
theorem overlayMem_eq_of_notMem_lastCells {L j : ℕ} (hjL : j < L) {c : Fin cells}
    (hc : c ∉ D.lastCells seg t₀ m₀ L j) :
    D.overlayMem seg t₀ m₀ L j c = D.segMem seg t₀ m₀ L c := by
  by_cases hlater : c ∈ D.laterCells seg t₀ m₀ L j
  · simp [overlayMem, hlater]
  · have hseg : c ∉ D.segCells seg t₀ m₀ j := fun h => hc (mem_sdiff.mpr ⟨h, hlater⟩)
    rw [D.overlayMem_eq_segMem_of_notMem_laterCells seg t₀ m₀ hlater,
      D.segMem_eq_of_notMem_laterCells seg t₀ m₀ hjL hlater, segMem_succ,
      D.nextMem_runInterval_eq_of_notMem_probedCellsInterval _ _ _ hseg]

/-- The overlay differs from the memory before segment `j` on at most `#laterCells` cells. -/
theorem hammingDist_overlayMem_le (L j : ℕ) :
    hammingDist (D.segMem seg t₀ m₀ j) (D.overlayMem seg t₀ m₀ L j) ≤
      #(D.laterCells seg t₀ m₀ L j) := by
  refine card_le_card fun c hc => ?_
  by_contra hlater
  exact (mem_filter.mp hc).2 (D.overlayMem_eq_segMem_of_notMem_laterCells seg t₀ m₀ hlater).symm

/-- The cells last touched by different segments `j, k < L` are disjoint. -/
theorem disjoint_lastCells {L j k : ℕ} (hj : j < L) (hk : k < L) (hjk : j ≠ k) :
    Disjoint (D.lastCells seg t₀ m₀ L j) (D.lastCells seg t₀ m₀ L k) := by
  rcases lt_or_gt_of_ne hjk with h | h
  · exact disjoint_of_subset_right
      ((D.lastCells_subset_segCells seg t₀ m₀ L k).trans
        (D.segCells_subset_laterCells seg t₀ m₀ h hk)) sdiff_disjoint
  · exact (disjoint_of_subset_right
      ((D.lastCells_subset_segCells seg t₀ m₀ L j).trans
        (D.segCells_subset_laterCells seg t₀ m₀ h hj)) sdiff_disjoint).symm

/-- The cells last touched by the segments `j < L` form a pairwise disjoint family. -/
theorem pairwiseDisjoint_lastCells (L : ℕ) :
    ((range L : Finset ℕ) : Set ℕ).PairwiseDisjoint (D.lastCells seg t₀ m₀ L) :=
  fun _ hj _ hk hjk =>
    D.disjoint_lastCells seg t₀ m₀ (mem_range.mp hj) (mem_range.mp hk) hjk

/-- **Epoch counting**: a set `P` of cells meets the last-touched sets of at most `#P` segments. -/
theorem card_filter_lastCells_le (L : ℕ) (P : Finset (Fin cells)) :
    #{j ∈ range L | (P ∩ D.lastCells seg t₀ m₀ L j).Nonempty} ≤ #P := by
  calc #{j ∈ range L | (P ∩ D.lastCells seg t₀ m₀ L j).Nonempty}
      ≤ ∑ j ∈ range L, #(P ∩ D.lastCells seg t₀ m₀ L j) := by
        rw [card_filter]
        refine sum_le_sum fun j _ => ?_
        split_ifs with h
        · exact card_pos.mpr h
        · exact Nat.zero_le _
    _ = #((range L).biUnion fun j => P ∩ D.lastCells seg t₀ m₀ L j) :=
        (card_biUnion fun j hj k hk hjk =>
          (D.pairwiseDisjoint_lastCells seg t₀ m₀ L hj hk hjk).mono inter_subset_right
            inter_subset_right).symm
    _ ≤ #P := card_le_card (biUnion_subset.mpr fun _ _ => inter_subset_left)

/-! ### Probe counts under a uniform depth bound -/

/-- If every step on the operations of `ops` has depth at most `d`, running `ops` makes at most
`d * ops.length` probes. -/
theorem probesInterval_le_mul_length {d : ℕ} (t : ℕ) (m : Mem cells w) (ops : List Op)
    (hd : ∀ t, ∀ o ∈ ops, (D.step t o).depth ≤ d) :
    D.probesInterval t m ops ≤ d * ops.length := by
  induction ops generalizing t m with
  | nil => simp
  | cons o rest ih =>
    rw [probesInterval_cons, List.length_cons, Nat.mul_succ]
    have h₁ := ((D.step t o).probes_le_depth m).trans (hd t o List.mem_cons_self)
    have h₂ := ih (t + 1) ((D.step t o).run m).2 fun t o' ho' =>
      hd t o' (List.mem_cons_of_mem _ ho')
    omega

/-- If every step on the operations of the segments between `j` and `L` has depth at most `d`,
those segments probe at most `d * Σ |seg k|` cells. -/
theorem card_laterCells_le {d L j : ℕ}
    (hd : ∀ k ∈ Ioo j L, ∀ t, ∀ o ∈ seg k, (D.step t o).depth ≤ d) :
    #(D.laterCells seg t₀ m₀ L j) ≤ d * ∑ k ∈ Ioo j L, (seg k).length := by
  rw [mul_sum]
  exact card_biUnion_le.trans <| sum_le_sum fun k hk =>
    (D.card_probedCellsInterval_le_probesInterval _ _ _).trans
      (D.probesInterval_le_mul_length _ _ _ (hd k hk))

/-! ### Replaying a query on the overlay -/

/-- **Query replay**: a tree whose probed cells on the final memory avoid the cells last touched by
segment `j` answers identically, with the same probes, on the overlay. -/
theorem run_overlayMem_eq {α : Type} {L j : ℕ} (hjL : j < L) (t : ProbeTree cells w α)
    (h : Disjoint (t.probedCells (D.segMem seg t₀ m₀ L)) (D.lastCells seg t₀ m₀ L j)) :
    (t.run (D.overlayMem seg t₀ m₀ L j)).1 = (t.run (D.segMem seg t₀ m₀ L)).1 ∧
      t.probes (D.overlayMem seg t₀ m₀ L j) = t.probes (D.segMem seg t₀ m₀ L) := by
  obtain ⟨hout, hpr, -⟩ := t.run_eq_of_eq_on_probedCells fun c hc =>
    D.overlayMem_eq_of_notMem_lastCells seg t₀ m₀ hjL (disjoint_left.mp h hc)
  exact ⟨hout, hpr⟩

end IndexedScheme

end Cslib.CellProbe
