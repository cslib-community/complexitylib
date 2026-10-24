/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Node.Header
public import Complexity.Algorithms.WordRAM.FusionTree.Node.Neighbors

/-!
# First fusion-node query and full-key selection

The first sketch query obtains a cut. Two full-key loads then select a neighboring key by
exclusive or. The original query and record address remain available for correction.

## Main definitions

* `NodeProgram.saveNeighbor`, `NodeProgram.initial`: neighbor-saving and initial query code.

## Main results

* `NodeProgram.exec_initial`: 149 charged instructions produce the selected neighbor.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.NodeProgram

open Cslib.WordRAM Lean.FusionTree

/-- Copy the selected full key and exclusive or, and initialize the branch's zero register. -/
def saveNeighbor : Code .standard registers :=
  .seq (.op (.copy chosen (neighborBank 14)))
    (.seq (.op (.copy divergence (neighborBank 15))) (.op (.const zero 0)))

/-- Initial compression, inclusive sketch cut, and the two full-key neighbor loads. -/
def initial : Code .standard registers :=
  .seq (.op (.copy argument query))
    (.seq (sketchQuery false)
      (.seq (.op (.copy cut (rankBank 9))) (.seq neighbors saveNeighbor)))

/-- A concrete first query produces a genuine minimum-exclusive-or sketch neighbor.
All setup and copies are charged; memory and original inputs are preserved. -/
theorem exec_initial {w n q a : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (hw : 2 ≤ w) (hn : 0 < n) (hs : StrictMono keys) (hk : ∀ i, keys i < 2 ^ w)
    (hnB : n ≤ branching w) (hlarge : 9 ≤ Nat.log 2 w)
    (x : Data registers) (hx : Ready p q a x) (hq : Fits w q)
    (ha : Fits w (a + 18 + (n - 1) * 2)) :
    ∃ y, ExecWithin w initial x y 149 ∧ Ready p q a y ∧ y.mem = x.mem ∧
      y.regs cut = sketchRank w keys q ∧ y.regs zero = 0 ∧
      ∃ j : Fin n, y.regs chosen = keys j ∧ y.regs divergence = keys j ^^^ q ∧
        IsSketchNeighbor w keys q j ∧
        ∀ i, IsSketchNeighbor w keys q i → keys j ^^^ q ≤ keys i ^^^ q := by
  let u := x.set argument q
  have heu : Exec (B := .standard) w (.op (.copy argument query)) x u 1 := by
    simpa only [hx.query_eq] using
      (Exec.copy (B := .standard) (w := w) (d := argument) (s := query) (x := x))
  have hru : Ready p q a u := hx.set_scratch argument q (by decide) (by decide)
  obtain ⟨v, hev, hv, hfv⟩ := exec_sketchQuery p false hw hn hs hk hnB hlarge u hru.prepared
    hq (by simp [u])
  have hrv := hru.frame hfv
  let t := v.set cut (sketchRank w keys q)
  have het : Exec (B := .standard) w (.op (.copy cut (rankBank 9))) v t 1 := by
    simpa only [sketchCut, Bool.false_eq_true, ↓reduceIte, hv] using
      (Exec.copy (B := .standard) (w := w) (d := cut) (s := rankBank 9) (x := v))
  have hrt : Ready p q a t := hrv.set_scratch cut _ (by decide) (by decide)
  obtain ⟨z, hez, hfz, j, hj, hd, hnear, hbest⟩ := exec_neighbors p hn hs hk hnB hlarge t
    hrt.prepared hq hrt.query_eq hrt.pointer_eq (by simp [t]) ha hrt.keys_eq
  have hrz := hrt.frame hfz
  let y := ((z.set chosen (keys j)).set divergence (keys j ^^^ q)).set zero 0
  have hey : Exec w saveNeighbor z y 3 := by
    ram_eval [saveNeighbor, y, hj, hd]
  have hry : Ready p q a y :=
    ((hrz.set_scratch chosen _ (by decide) (by decide)).set_scratch divergence _
      (by decide) (by decide)).set_scratch zero _ (by decide) (by decide)
  refine ⟨y, heu.within.seq (hev.within.seq (het.within.seq (hez.seq hey.within))), hry,
    hfz.1.trans hfv.1, ?_, ?_, j, ?_, ?_, hnear, hbest⟩
  · simpa +decide [y, t, cut, chosen, divergence, zero] using hfz.2 cut (by decide)
  · simp [y]
  · simp +decide [y, chosen, divergence, zero]
  · simp +decide [y, divergence, zero]

end Cslib.Algorithms.WordRAM.FusionTree.NodeProgram
