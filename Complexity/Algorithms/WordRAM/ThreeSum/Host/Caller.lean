/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Loop
import Complexity.Computability.WordRAM.SymbolicExec.CanonicalCall

/-!
# Caller-owned Convolution-3SUM input and workspace

The caller supplies raw length, magnitude, input pointer and matrix-workspace pointer in the
existing host registers. Initialization reuses the existing square-root and layout code without
reading header zero. The input pointer is restored before the unchanged instance loop runs.

## Main definitions

* `prepareAt`: prepare the actual caller-owned source and matrix blocks.

## Main results

* `exec_prepare_at`: charged setup with exact parameters and a complete memory frame.

These native ABI composition proofs are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Host

open Cslib.WordRAM

/-- Saved caller input pointer; the existing layout and square-root banks do not change it. -/
abbrev savedSource : Fin 64 := 50

/-- Adapt the existing adjacent-block layout to the caller's chosen matrix start. -/
def callerSetup : Code .standard 64 := ram[
  savedSource ← base; base ← matAB - len; one ← #1; sqrtArg ← len ]

/-- Restore the actual source pointer after computing the caller's matrix layout. -/
def restoreSource : Code .standard 64 := ram[ base ← savedSource ]

/-- Initialize from actual register arguments, without touching any memory cell. -/
def prepareAt : Code .standard 64 :=
  .seq callerSetup (.seq (NatSqrt.program.rename sqrtRegisters) (.seq layout restoreSource))

/-- Every source/layout operation is charged. The source and all other caller memory are kept. -/
theorem exec_prepare_at {w N U src workspace : ℕ} (x : Data 64)
    (hN : x.regs len = N) (hU : x.regs upper = U)
    (hb : x.regs base = src) (hab : x.regs matAB = workspace)
    (hbelow : src + N ≤ workspace)
    (hsize : Fits w (workspace + 3 * (sideLength N * sideLength N)))
    (hfill : Fits w (4 * U + 2)) (hsqrt : Fits w (4 * N + 4)) :
    ∃ y, ExecWithin w prepareAt x y (5 * Nat.sqrt N + 24) ∧
      ParametersAt N U src workspace y ∧ y.regs inst = 0 ∧ y.regs found = 0 ∧
      y.mem = x.mem := by
  have h1 : Fits w 1 := hfill.of_le (by omega)
  have hd : Fits w (workspace - N) := hsize.of_le (by omega)
  let a := x.set savedSource src |>.set base (workspace - N) |>.set one 1 |>.set sqrtArg N
  have ha : ExecWithin w callerSetup x a 4 := by
    ram_eval [callerSetup, a, hb, hab, hN, h1, hd,
      savedSource, base, matAB, len, one, sqrtArg, Fin.mk.injEq]
  have han : a.regs sqrtArg = N := by simp [a]
  have hsi : sqrtRegisters.Injective := by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp only [sqrtRegisters] at this
    omega
  obtain ⟨small, he, hr, _, hm, _⟩ := NatSqrt.exec (a.comap sqrtRegisters)
    (by change Fits w (4 * a.regs sqrtArg + 4); rw [han]; exact hsqrt)
  let b := small.extend sqrtRegisters a
  have hcall : ExecWithin w (NatSqrt.program.rename sqrtRegisters) a b
      (5 * Nat.sqrt N + 7) := by
    have hcall := he.rename hsi
    change ExecWithin w _ a b (5 * Nat.sqrt (a.regs sqrtArg) + 7) at hcall
    simpa only [han] using hcall
  change small.regs NatSqrt.root = Nat.sqrt (a.regs sqrtArg) at hr
  rw [han] at hr
  have hr' : b.regs sqrtRoot = Nat.sqrt N := by
    wram_simp [b, NatSqrt.root, hr]
  have hw : N + (workspace - N) = workspace := by omega
  obtain ⟨c, hc, hp, hi, hf, hmem⟩ :=
    exec_layout_at (N := N) (U := U) (src := workspace - N) b
      (by wram_simp [b, a, hN]) (by wram_simp [b, a, hU])
      (by wram_simp [b, a]) (by wram_simp [b, a]) hr'
      (by simpa only [hw] using hsize) hfill
  rw [hw] at hp
  have hsaved : c.regs savedSource = src := by
    rw [hc.regs_eq (by decide)]
    wram_simp [b, a]
  let y := c.set base src
  have hy : ExecWithin w restoreSource c y 1 := by
    simpa only [restoreSource, hsaved] using
      (ExecWithin.copy (x := c) (d := base) (s := savedSource))
  refine ⟨y, (ha.seq (hcall.seq (hc.seq hy))).mono ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · constructor <;> simp +decide [y, Data.set_regs,
      len, upper, base, matAB, matBC, matAC, free, side, stop, filler, encodedFiller, one,
      hp.len, hp.upper, hp.ab, hp.bc, hp.ac, hp.free, hp.side, hp.stop,
      hp.filler, hp.encodedFiller, hp.one]
  · simpa +decide [y, inst, base] using hi
  · simpa +decide [y, found, base] using hf
  · exact hmem.trans hm

end Cslib.Algorithms.WordRAM.ThreeSum.Host
