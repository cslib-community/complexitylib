/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.NodeSetup
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.NodeMemory

/-!
# Complete native initialization of a Chan–He node

## Main results

* `NodePacking.exec_initialize`: exact runtime layout, encoded constants and all `4N` padding
  writes, charged within `12N+33` native instructions.

## References

This native composition proof is original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking

open Cslib.WordRAM

private theorem paddingRegisters_injective : Function.Injective paddingRegisters := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun k : Fin 64 => k.val) he

private theorem padding_extend_frame (a : Data 10) (x : Data 64) :
    Frame x (a.extend paddingRegisters x) := by
  intro i hi hne
  change Function.extend paddingRegisters a.regs x.regs i = x.regs i
  apply Function.extend_apply'
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  dsimp only [paddingRegisters] at this
  omega

/-- All setup and padding are real instructions, starting from arbitrary old output memory. -/
theorem exec_initialize {w : ℕ} (x : Data 64) (hfit : Fits w (layout x).budget) :
    ∃ y, ExecWithin w initializeCode x y (12 * (layout x).N + 33) ∧ Parameters x y ∧
      Prepared (layout x) y ∧ y.mem = paddingMemory (layout x) x.mem := by
  let L := layout x
  have hfit' : Fits w L.budget := hfit
  obtain ⟨a, ha, har, ham, hap, hak, hah, ha1, ha4, ha3⟩ := exec_layout x hfit
  have haU : a.regs magnitude = L.U := har magnitude (by decide)
  have haN : a.regs groups = L.N := har groups (by decide)
  obtain ⟨b, hb, hbr, hbm, hready, hpad⟩ := exec_constants L a hfit' haU haN hak hah hap ha1 ha4 ha3
  have hargs : Parameters x b := fun i hi => (hbr i hi).trans (har i hi)
  obtain ⟨hbd, hbn, hbp₀, hbp₁, hbp₂, hbp₃⟩ := hpad
  have hpd : (b.comap paddingRegisters).regs Padding.dst = L.packed := hbd
  have hpn : (b.comap paddingRegisters).regs Padding.len = L.N := hbn
  have hf4 : Fits w 4 := hfit'.of_le (by have := L.bounds.2.2; omega)
  have hpend : Fits w ((b.comap paddingRegisters).regs Padding.dst +
      4 * (b.comap paddingRegisters).regs Padding.len) := by
    rw [hpd, hpn]
    exact (hfit'.of_le L.bounds.1).of_le (by
      dsimp only [Layout.endpoint, Layout.hist, Layout.scratch]
      omega)
  obtain ⟨c, hc, hcm, _⟩ := Padding.exec (b.comap paddingRegisters) hf4 hpend
  let y := c.extend paddingRegisters b
  have hy : ExecWithin w (Padding.program.rename paddingRegisters) b y (12 * L.N + 5) :=
    by simpa only [hpn] using hc.rename paddingRegisters_injective
  have hframe : Frame b y := padding_extend_frame c b
  refine ⟨y, (ha.seq (hb.seq hy)).mono (by dsimp only [L] at *; omega), hargs.of_frame hframe,
    hready.of_frame hframe, ?_⟩
  change c.mem = _
  rw [hcm, Data.comap_mem, hbm, ham, hpd, hpn]
  change Padding.memory x.mem L.packed (b.regs pad0) (b.regs pad1)
    (b.regs pad2) (b.regs pad3) L.N = _
  rw [hbp₀, hbp₁, hbp₂, hbp₃]
  rfl

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.NodePacking
