/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.FusionTree.Node.Header
public import Complexity.Algorithms.WordRAM.FusionTree.Node.Sketch
public import Complexity.Algorithms.WordRAM.FusionTree.MSBProgram

/-!
# Executable correction subroutines

The highest-bit call accepts an ordinary physical register and initializes its own bank.
The boundary and second-rank calls charge all register transfers. No call changes memory.

## Main definitions

* `NodeProgram.msbBank`, `NodeProgram.highest`: register bank and code for the highest-bit call.
* `NodeProgram.boundaryInputs`, `NodeProgram.boundaries`: register transfers and boundary code.
* `NodeProgram.secondQuery`: second sketch query with charged register transfers.

## Main results

* `NodeProgram.exec_highest`: the concrete highest-bit code on the selected exclusive or.
* `NodeProgram.exec_boundaries`: both correction endpoints and the query bit.
* `NodeProgram.exec_secondQuery`: a full second sketch query with charged transfers.

## References

* [FredmanWillard1993]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.NodeProgram

open Cslib.WordRAM Cslib.WordRAM.Multiword Cslib.BitString Lean.FusionTree

/-- Disjoint workspace for the complete multiword highest-bit program. -/
abbrev msbBank : Fin (Bank.capacity 44 + 4) → Fin registers := bank 130 (by decide)

/-- Copy the physical input, run the actual highest-bit program, and copy its scalar result. -/
def highest (w : ℕ) : Code .standard registers :=
  .seq (.op (.copy (msbBank Bank.inputReg) divergence))
    (.seq ((MSB.Program.scalarCode w).rename msbBank)
      (.op (.copy position (msbBank MSB.Program.output))))

/-- The 200000-instruction MSB bound plus its two actual caller copies. -/
theorem exec_highest {w d : ℕ} (hw : 3 ≤ w) (x : Data registers)
    (hd : Fits w d) (hxd : x.regs divergence = d) :
    ∃ y, ExecWithin w (highest w) x y 200002 ∧ y.regs position = d.log2 ∧
      y.mem = x.mem ∧
      ∀ i : Fin registers, i.val < 40 → i ≠ position → y.regs i = x.regs i := by
  let u := x.set (msbBank Bank.inputReg) d
  have hexu : Exec (B := .standard) w (.op (.copy (msbBank Bank.inputReg) divergence)) x u 1 := by
    simpa only [hxd] using (Exec.copy (B := .standard) (w := w)
      (d := msbBank Bank.inputReg) (s := divergence) (x := x))
  have hu : (u.comap msbBank).regs Bank.inputReg = d := by simp [u]
  obtain ⟨v, hev, hv, hm⟩ := MSB.Program.exec_scalarCode hw (u.comap msbBank) (hu ▸ hd)
  let z := v.extend msbBank u
  have hz : z.regs (msbBank MSB.Program.output) = d.log2 := by
    exact ((bank_injective _).extend_apply _ _ _).trans (hv.trans (congrArg Nat.log2 hu))
  let y := z.set position (d.log2)
  have hezy : Exec (B := .standard) w
      (.op (.copy position (msbBank MSB.Program.output))) z y 1 := by
    simpa only [hz] using (Exec.copy (B := .standard) (w := w)
      (d := position) (s := msbBank MSB.Program.output) (x := z))
  have hf : Frame x z := (frame_set x _ _ (by decide)).trans
    (frame_extend _ (by decide) u v hm)
  refine ⟨y, hexu.within.seq ((hev.rename (bank_injective _)).seq hezy.within),
    by simp [y], hf.1, ?_⟩
  intro i hi hn
  exact (Function.update_of_ne hn _ _).trans (hf.2 i hi)

/-- The two transfers into the boundary workspace. -/
def boundaryInputs : List (Fin registers × Fin registers) :=
  [(boundaryBank 0, query), (boundaryBank 1, position)]

/-- Prepare two inputs and compute both correction boundaries. -/
def boundaries : Code .standard registers :=
  .seq (moves boundaryInputs) (BoundaryProgram.code.rename boundaryBank)

/-- The boundary call includes three transfer instructions and ten arithmetic instructions. -/
theorem exec_boundaries {w q d : ℕ} (x : Data registers) (hq : Fits w q) (hd : d < w)
    (hxq : x.regs query = q) (hxd : x.regs position = d) :
    ∃ y, Exec w boundaries x y 13 ∧ Frame x y ∧
      y.regs (boundaryBank 7) = lowerBoundary q d ∧
      y.regs (boundaryBank 8) = upperBoundary q d ∧
      y.regs (boundaryBank 9) = ((q >>> d) &&& 1) := by
  let u := moved boundaryInputs x
  have hf : Frame x u := frame_moved _ _ (by simp [boundaryInputs, boundaryBank, bank])
  have huq : (u.comap boundaryBank).regs BoundaryProgram.query = q := hxq
  have hud : (u.comap boundaryBank).regs BoundaryProgram.position = d := hxd
  obtain ⟨he, hl, hu, hb, hm⟩ := BoundaryProgram.exec (u.comap boundaryBank) hq hd huq hud
  let v := BoundaryProgram.result (u.comap boundaryBank) q d
  refine ⟨v.extend boundaryBank u, (exec_moves w _ x).seq (he.rename (bank_injective _)),
    hf.trans (frame_extend _ (by decide) u v hm), ?_, ?_, ?_⟩
  · exact ((bank_injective _).extend_apply _ _ _).trans hl
  · exact ((bank_injective _).extend_apply _ _ _).trans hu
  · exact ((bank_injective _).extend_apply _ _ _).trans hb

/-- Transfer a full word to the compressor, make a sketch query and return the rank. -/
def secondQuery (strict : Bool) (src : Fin registers) : Code .standard registers :=
  .seq (.op (.copy argument src))
    (.seq (sketchQuery strict) (.op (.copy out (rankBank 9))))

/-- Both caller copies and all 119 sketch-query instructions are charged. -/
theorem exec_secondQuery {w n q a z : ℕ} {keys : Fin n → ℕ} (p : NodeParameters w keys)
    (strict : Bool) (src : Fin registers) (hw : 2 ≤ w) (hn : 0 < n)
    (hs : StrictMono keys) (hk : ∀ i, keys i < 2 ^ w)
    (hnB : n ≤ branching w) (hlarge : 9 ≤ Nat.log 2 w)
    (x : Data registers) (hx : Ready p q a x) (hz : Fits w z) (hxz : x.regs src = z) :
    ∃ y, Exec w (secondQuery strict src) x y 121 ∧
      y.regs out = sketchCut strict w keys z ∧ Ready p q a y ∧ y.mem = x.mem := by
  let u := x.set argument z
  have heu : Exec (B := .standard) w (.op (.copy argument src)) x u 1 := by
    simpa only [hxz] using (Exec.copy (B := .standard) (w := w)
      (d := argument) (s := src) (x := x))
  have hru : Ready p q a u := hx.set_scratch argument z (by decide) (by decide)
  obtain ⟨v, hev, hv, hfv⟩ := exec_sketchQuery p strict hw hn hs hk hnB hlarge u hru.prepared
    hz (by simp [u])
  let y := v.set out (sketchCut strict w keys z)
  have hey : Exec (B := .standard) w (.op (.copy out (rankBank 9))) v y 1 := by
    simpa only [hv] using (Exec.copy (B := .standard) (w := w)
      (d := out) (s := rankBank 9) (x := v))
  exact ⟨y, heu.seq (hev.seq hey), by simp [y],
    (hru.frame hfv).set_scratch out _ (by decide) (by decide), hfv.1⟩

/-- The numeric bit tested by RAM is zero precisely when the Boolean query bit is false. -/
theorem bit_eq_zero_iff (q d : ℕ) : ((q >>> d) &&& 1) = 0 ↔ q.testBit d = false := by
  simp [Nat.testBit, Nat.and_comm]

/-- Both boundary words are physical words, including a differing bit at `w - 1`. -/
theorem boundary_fits {w q d : ℕ} (hq : Fits w q) (hd : d < w) :
    Fits w (lowerBoundary q d) ∧ Fits w (upperBoundary q d) := by
  have hstem : Fits w ((q >>> (d + 1)) <<< (d + 1)) := hq.of_le (by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    exact Nat.div_mul_le_self _ _)
  have hpower : Fits w (2 ^ d) := Nat.pow_lt_pow_right (by decide) hd
  exact ⟨Nat.or_lt_two_pow hstem (hpower.of_le (Nat.sub_le _ _)),
    Nat.or_lt_two_pow hstem hpower⟩

end Cslib.Algorithms.WordRAM.FusionTree.NodeProgram
