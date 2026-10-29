/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Host.Loop

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
  obtain ⟨b, he, hr, _, hm, _⟩ := NatSqrt.exec_rename sqrtRegisters hsi a
    (by change Fits w (4 * a.regs sqrtArg + 4); rw [han]; exact hsqrt)
  change ExecWithin w _ a b (5 * Nat.sqrt (a.regs sqrtArg) + 7) at he
  rw [han] at he
  have hbr (i : Fin 64) (hi : 34 ≤ i.val) : b.regs i = a.regs i := by
    apply he.regs_eq
    apply Code.preserves_rename_of_forall_ne
    intro j hj
    have := congrArg Fin.val hj
    dsimp only [sqrtRegisters] at this
    have := j.isLt
    omega
  have hr' : b.regs sqrtRoot = Nat.sqrt N := by
    change b.regs sqrtRoot = Nat.sqrt (a.regs sqrtArg) at hr
    simpa only [han] using hr
  have hw : N + (workspace - N) = workspace := by omega
  obtain ⟨c, hc, hp, hi, hf, hmem⟩ :=
    exec_layout_at (N := N) (U := U) (src := workspace - N) b
    ((hbr len (by decide)).trans (by simp +decide [a, hN, len, sqrtArg, one, base, savedSource]))
    ((hbr upper (by decide)).trans
      (by simp +decide [a, hU, upper, sqrtArg, one, base, savedSource]))
    ((hbr base (by decide)).trans (by simp +decide [a, base, sqrtArg, one]))
    ((hbr one (by decide)).trans (by simp +decide [a, one, sqrtArg])) hr'
    (by simpa only [hw] using hsize) hfill
  rw [hw] at hp
  have hsaved : c.regs savedSource = src :=
    (hc.regs_eq (by decide)).trans ((hbr savedSource (by decide)).trans
      (by simp +decide [a, savedSource, base, one, sqrtArg]))
  let y := c.set base src
  have hy : ExecWithin w restoreSource c y 1 := by
    simpa only [restoreSource, hsaved] using
      (ExecWithin.copy (x := c) (d := base) (s := savedSource))
  refine ⟨y, (ha.seq (he.seq (hc.seq hy))).mono ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · constructor <;> simp +decide [y, Data.set_regs,
      len, upper, base, matAB, matBC, matAC, free, side, stop, filler, encodedFiller, one,
      hp.len, hp.upper, hp.ab, hp.bc, hp.ac, hp.free, hp.side, hp.stop,
      hp.filler, hp.encodedFiller, hp.one]
  · simpa +decide [y, inst, base] using hi
  · simpa +decide [y, found, base] using hf
  · exact hmem.trans hm

end Cslib.Algorithms.WordRAM.ThreeSum.Host
