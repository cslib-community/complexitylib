/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.CellProbe.Chronogram

/-!
# Chronogram bookkeeping tests

Kernel-checked instances for `Cslib.CellProbe.IndexedScheme` segment bookkeeping on an adaptive
3-cell, 1-bit scheme whose `copy` operation reads one cell and writes its value to another.

The three segments are `[write 0 1, write 1 1]`, `[copy 0 2]` and `[write 1 0]`. Segment `1` only
*reads* cell `0`, yet that read removes cell `0` from the cells last touched by segment `0`: the
last-touched sets record the last probe, not the last write. The checks cover

1. the segment start points and memories, and the two run-the-concatenation lemmas;
2. `laterCells` / `lastCells`, their disjointness and the epoch-counting bound;
3. the overlay, which agrees with the final memory exactly outside `lastCells`, and the Hamming
   bound against the memory before the segment (tight here);
4. query replay on the overlay, together with a query that probes a last-touched cell and answers
   differently, so the disjointness hypothesis of `run_overlayMem_eq` cannot be dropped;
5. the probe-count bound `card_laterCells_le` and the Hamming-ball count
   `card_filter_hammingDist_le_le_pow`, including a case where the latter is attained.
-/

public section

namespace ComplexityTests.CellProbeChronogram

open Cslib Cslib.CellProbe Finset

/-- Operations on three 1-bit cells: write a bit, or copy one cell into another. -/
inductive TOp : Type where
  | write (i : Fin 3) (v : Fin 2)
  | copy (src dst : Fin 3)
  deriving DecidableEq

/-- Every operation returns no answer. -/
abbrev TResult : TOp → Type := fun _ => PUnit

/-- `write i v` writes `v` to cell `i` (depth `1`); `copy src dst` reads cell `src` and writes the
value read to cell `dst` (depth `2`). -/
def copier : IndexedScheme TOp TResult 3 1 where
  init := zeroMem 3 1
  step _
    | .write i v => ProbeTree.write i v
    | .copy src dst => do
        let v ← ProbeTree.read src
        ProbeTree.write dst v

/-- Segment `0` sets cells `0` and `1`, segment `1` copies cell `0` into cell `2`, segment `2`
clears cell `1`. -/
def segs : ℕ → List TOp
  | 0 => [.write 0 1, .write 1 1]
  | 1 => [.copy 0 2]
  | 2 => [.write 1 0]
  | _ => []

/-- The initial memory, all cells `0`. -/
abbrev m₀ : Mem 3 1 := zeroMem 3 1

/-! ### 1. Segment start points and memories -/

example :
    IndexedScheme.segStart segs 0 1 = 2 ∧ IndexedScheme.segStart segs 0 2 = 3 ∧
      IndexedScheme.segStart segs 0 3 = 4 := by
  decide

example :
    copier.segMem segs 0 m₀ 1 = ![1, 1, 0] ∧ copier.segMem segs 0 m₀ 2 = ![1, 1, 1] ∧
      copier.segMem segs 0 m₀ 3 = ![1, 0, 1] := by
  decide

-- Running the concatenated segments reaches `segMem 3` at step `segStart 3`.
example :
    (copier.runInterval 0 m₀ ((List.range 3).flatMap segs)).2 = ![1, 0, 1] := by
  rw [(copier.runInterval_flatMap_range segs 0 m₀ 3).1]
  decide

/-! ### 2. Later and last-touched cells -/

example :
    copier.segCells segs 0 m₀ 0 = {0, 1} ∧ copier.segCells segs 0 m₀ 1 = {0, 2} ∧
      copier.segCells segs 0 m₀ 2 = {1} := by
  decide

-- Cell `0` is only read after segment `0`, but that read already removes it from `lastCells 3 0`.
example :
    copier.laterCells segs 0 m₀ 3 0 = {0, 1, 2} ∧ copier.lastCells segs 0 m₀ 3 0 = ∅ ∧
      copier.laterCells segs 0 m₀ 3 1 = {1} ∧ copier.lastCells segs 0 m₀ 3 1 = {0, 2} ∧
      copier.laterCells segs 0 m₀ 3 2 = ∅ ∧ copier.lastCells segs 0 m₀ 3 2 = {1} := by
  decide

example : Disjoint (copier.lastCells segs 0 m₀ 3 1) (copier.lastCells segs 0 m₀ 3 2) :=
  copier.disjoint_lastCells segs 0 m₀ (by decide) (by decide) (by decide)

-- The full cell set meets `lastCells 3 1` and `lastCells 3 2` but not the empty `lastCells 3 0`.
example :
    #{j ∈ range 3 | ((univ : Finset (Fin 3)) ∩ copier.lastCells segs 0 m₀ 3 j).Nonempty} = 2 ∧
      #{j ∈ range 3 | ((univ : Finset (Fin 3)) ∩ copier.lastCells segs 0 m₀ 3 j).Nonempty} ≤
        #(univ : Finset (Fin 3)) :=
  ⟨by decide, copier.card_filter_lastCells_le segs 0 m₀ 3 univ⟩

/-! ### 3. The overlay -/

-- For `j = 1` the overlay keeps cell `2` from before segment `1`; it differs from the final memory
-- `![1, 0, 1]` only at cell `2 ∈ lastCells 3 1`.
example : copier.overlayMem segs 0 m₀ 3 1 = ![1, 0, 0] := by
  decide

example :
    (∀ c ∉ copier.lastCells segs 0 m₀ 3 1,
        copier.overlayMem segs 0 m₀ 3 1 c = copier.segMem segs 0 m₀ 3 c) ∧
      copier.overlayMem segs 0 m₀ 3 1 2 ≠ copier.segMem segs 0 m₀ 3 2 :=
  ⟨fun _ hc => copier.overlayMem_eq_of_notMem_lastCells segs 0 m₀ (by decide) hc, by decide⟩

-- For `j = 0` every cell is probed later, so the overlay is the final memory.
example : copier.overlayMem segs 0 m₀ 3 0 = copier.segMem segs 0 m₀ 3 := by
  decide

-- The Hamming bound is tight for `j = 1`: the overlay differs from `segMem 1` at cell `1` only.
example :
    hammingDist (copier.segMem segs 0 m₀ 1) (copier.overlayMem segs 0 m₀ 3 1) = 1 ∧
      #(copier.laterCells segs 0 m₀ 3 1) = 1 :=
  ⟨by decide, by decide⟩

example :
    hammingDist (copier.segMem segs 0 m₀ 1) (copier.overlayMem segs 0 m₀ 3 1) ≤
      #(copier.laterCells segs 0 m₀ 3 1) :=
  copier.hammingDist_overlayMem_le segs 0 m₀ 3 1

/-! ### 4. Query replay on the overlay -/

-- Reading cell `1` avoids `lastCells 3 1 = {0, 2}` and answers identically on the overlay.
example :
    ((ProbeTree.read 1 : ProbeTree 3 1 _).run (copier.overlayMem segs 0 m₀ 3 1)).1 =
        ((ProbeTree.read 1 : ProbeTree 3 1 _).run (copier.segMem segs 0 m₀ 3)).1 ∧
      ((ProbeTree.read 1 : ProbeTree 3 1 _).run (copier.segMem segs 0 m₀ 3)).1 = 0 := by
  refine ⟨(copier.run_overlayMem_eq segs 0 m₀ (by decide) _ ?_).1, by decide⟩
  decide

-- Reading cell `2 ∈ lastCells 3 1` answers `0` on the overlay but `1` on the final memory.
example :
    ¬ Disjoint ((ProbeTree.read 2 : ProbeTree 3 1 _).probedCells (copier.segMem segs 0 m₀ 3))
        (copier.lastCells segs 0 m₀ 3 1) ∧
      ((ProbeTree.read 2 : ProbeTree 3 1 _).run (copier.overlayMem segs 0 m₀ 3 1)).1 = 0 ∧
      ((ProbeTree.read 2 : ProbeTree 3 1 _).run (copier.segMem segs 0 m₀ 3)).1 = 1 := by
  decide

/-! ### 5. Probe counts and Hamming balls -/

theorem copier_depth_le (t : ℕ) (o : TOp) : (copier.step t o).depth ≤ 2 := by
  change (copier.step 0 o).depth ≤ 2
  cases o with
  | write i v => revert i v; decide
  | copy src dst => revert src dst; decide

-- Segments `1` and `2` contain two operations of depth at most `2` and probe three distinct cells,
-- within the bound `2 * 2 = 4`; it is not attained because `write 1 0` has depth `1`.
example :
    #(copier.laterCells segs 0 m₀ 3 0) = 3 ∧
      #(copier.laterCells segs 0 m₀ 3 0) ≤ 2 * ∑ k ∈ Ioo 0 3, (segs k).length :=
  ⟨by decide, copier.card_laterCells_le segs 0 m₀ fun _ _ t o _ => copier_depth_le t o⟩

-- Two 1-bit cells: the radius-`1` ball around `0` has `3` memories, attaining the bound
-- `(2 * (2 ^ 1 - 1) + 1) ^ 1 = 3`; the radius-`0` ball is the centre alone.
example :
    #{m' : Mem 2 1 | hammingDist (zeroMem 2 1) m' ≤ 1} = 3 ∧
      #{m' : Mem 2 1 | hammingDist (zeroMem 2 1) m' ≤ 0} = 1 :=
  ⟨by decide, by decide⟩

example :
    #{m' : Mem 2 1 | hammingDist (zeroMem 2 1) m' ≤ 1} ≤ (2 * (2 ^ 1 - 1) + 1) ^ 1 :=
  card_filter_hammingDist_le_le_pow _ 1

end ComplexityTests.CellProbeChronogram
