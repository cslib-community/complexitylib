/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Node.Sketch

/-!
# Actual full-key neighbor loads

The key table begins eighteen words after the record base and has stride two. Its second
word in each entry is a child pointer; this subroutine reads the full-key minima only.
All constants, address calculations, copies and both loads are charged.

## Main definitions

* `NodeProgram.neighborInputs`, `NodeProgram.neighborAddress`, `NodeProgram.neighbors`: register
  copies, table-address calculation, and full-key neighbor-loading code.

## Main results

* `NodeProgram.exec_neighbors`: select a minimum-exclusive-or sketch neighbor in 25 instructions.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.NodeProgram

open Cslib.WordRAM Lean.FusionTree

/-- Registers copied before the two actual full-key loads. -/
def neighborInputs : List (Fin registers × Fin registers) :=
  [(neighborBank 0, query), (neighborBank 1, cut), (neighborBank 2, count)]

/-- Load the table offset and stride, charging address addition as well. -/
def neighborAddress : Code .standard registers := ram[
  ⟪Code.op (.const (neighborBank 3) 18)⟫;
  ⟪Code.op (.bin .add (neighborBank 3) pointer (neighborBank 3))⟫;
  ⟪Code.op (.const (neighborBank 4) 2)⟫ ]

/-- Caller setup followed by the checked two-neighbor program. -/
def neighbors : Code .standard registers :=
  .seq (moves neighborInputs)
    (.seq neighborAddress (NeighborProgram.code.rename neighborBank))

/-- The output key and its exclusive or are selected from actual stride-two memory loads.
The only representation premise is the literal full-key table, with explicit address bounds. -/
theorem exec_neighbors {w n q a : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (hn : 0 < n) (hs : StrictMono keys) (hk : ∀ i, keys i < 2 ^ w)
    (hnB : n ≤ branching w) (hlarge : 9 ≤ Nat.log 2 w)
    (x : Data registers) (hx : Prepared p x) (hq : Fits w q)
    (hxq : x.regs query = q) (hxa : x.regs pointer = a)
    (hxt : x.regs cut = sketchRank w keys q)
    (ha : Fits w (a + 18 + (n - 1) * 2))
    (hkeys : ∀ i : Fin n, x.mem (a + 18 + i.val * 2) = keys i) :
    ∃ y, ExecWithin w neighbors x y 25 ∧ Frame x y ∧
      ∃ j : Fin n, y.regs (neighborBank 14) = keys j ∧
        y.regs (neighborBank 15) = keys j ^^^ q ∧ IsSketchNeighbor w keys q j ∧
        ∀ i, IsSketchNeighbor w keys q i → keys j ^^^ q ≤ keys i ^^^ q := by
  let u := moved neighborInputs x
  have hfu : Frame x u := frame_moved _ _ (by simp [neighborInputs, neighborBank, bank])
  let v := ((u.set (neighborBank 3) 18).set (neighborBank 3) (a + 18)).set (neighborBank 4) 2
  have h18 : Fits w 18 := ha.of_le (by omega)
  have h2 : Fits w 2 := ha.of_le (by omega)
  have ha18 : Fits w (a + 18) := ha.of_le (Nat.le_add_right _ _)
  have huv : Exec w neighborAddress u v 3 := by
    have hua := hfu.2 pointer (by decide)
    ram_eval [neighborAddress, v, hua, hxa, h18, h2, ha18]
  have hfv : Frame u v :=
    (frame_set u _ _ (by decide)).trans
      ((frame_set _ _ _ (by decide)).trans (frame_set _ _ _ (by decide)))
  have hinputs :
      (v.comap neighborBank).regs 0 = q ∧
      (v.comap neighborBank).regs 1 = sketchRank w keys q ∧
      (v.comap neighborBank).regs 2 = n ∧
      (v.comap neighborBank).regs 3 = a + 18 ∧
      (v.comap neighborBank).regs 4 = 2 :=
    ⟨hxq, hxt, hx.count_eq, rfl, rfl⟩
  have htable (i : Fin n) : (v.comap neighborBank).mem (a + 18 + i.val * 2) = keys i :=
    (congrFun (hfv.1.trans hfu.1) _).trans (hkeys i)
  obtain ⟨he, hm⟩ := NeighborProgram.exec (v.comap neighborBank) hn (upperRank_le _ _)
    hq (p.count_fit hn hs hk hnB hlarge) ha
    (fun i hi => (htable ⟨i, hi⟩) ▸ hk ⟨i, hi⟩)
    hinputs.1 hinputs.2.1 hinputs.2.2.1 hinputs.2.2.2.1 hinputs.2.2.2.2
  let z := NeighborProgram.result (v.comap neighborBank) q n (sketchRank w keys q) (a + 18) 2
  obtain ⟨j, _, hj, hd, hnear, hbest⟩ :=
    NeighborProgram.result_sketchNeighbor (v.comap neighborBank) keys hn htable
  refine ⟨z.extend neighborBank v,
    (exec_moves w _ x).within.seq (huv.within.seq (he.rename (bank_injective _))),
    hfu.trans (hfv.trans (frame_extend _ (by decide) v z hm)), j, ?_, ?_, hnear, hbest⟩
  · exact ((bank_injective _).extend_apply _ _ _).trans hj
  · exact ((bank_injective _).extend_apply _ _ _).trans hd

end Cslib.Algorithms.WordRAM.FusionTree.NodeProgram
