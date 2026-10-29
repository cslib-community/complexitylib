/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Parameters
public import Complexity.Algorithms.WordRAM.ThreeSum.Fill
public import Complexity.Computability.WordRAM.RegisterFrame

/-!
# Preparing the native Convolution-3SUM host

The host reads the standard length header and computes a polynomial magnitude bound using the
existing native parameter program. It then computes the matrix side and consecutive matrix
addresses. The parameter program's additional computations are included in the instruction count.

This directly adapts the setup of Anthropic's pinned
[`c3Body`](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem21a/Convolution/Host.lean).
The complete reduction must also fill every instance and invoke a concrete certified solver.

## Main definitions

* `Host.Parameters`: the prepared register interface.
* `Host.prepare`: native header, magnitude, square-root and layout computation.

## Main results

* `Host.exec_prepare`: exact prepared parameters and a charged setup bound.

## References

* [V. Vassilevska Williams and R. Williams, *Finding, minimizing, and counting weighted
  subgraphs*][VassilevskaWilliamsWilliams2013]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Host

open Cslib.WordRAM

/-- Input length. -/
abbrev len : Fin 64 := 34
/-- Polynomial magnitude bound. -/
abbrev upper : Fin 64 := 35
/-- Input base address. -/
abbrev base : Fin 64 := 36
/-- AB matrix base address. -/
abbrev matAB : Fin 64 := 37
/-- BC matrix base address. -/
abbrev matBC : Fin 64 := 38
/-- AC matrix base address. -/
abbrev matAC : Fin 64 := 39
/-- Solver workspace starts after the three matrices. -/
abbrev free : Fin 64 := 40
/-- Number of vertices per part. -/
abbrev side : Fin 64 := 41
/-- Current instance number. -/
abbrev inst : Fin 64 := 42
/-- Number of instances. -/
abbrev stop : Fin 64 := 43
/-- Accumulated Boolean verdict. -/
abbrev found : Fin 64 := 44
/-- Constant one. -/
abbrev one : Fin 64 := 45
/-- Unsigned filler magnitude. -/
abbrev filler : Fin 64 := 47
/-- Signed-encoded positive filler. -/
abbrev encodedFiller : Fin 64 := 48
/-- Number of entries per matrix. -/
abbrev area : Fin 64 := 49
/-- Square-root argument. -/
abbrev sqrtArg : Fin 64 := 28
/-- Square-root output. -/
abbrev sqrtRoot : Fin 64 := 29

/-- Register embedding for the existing parameter routine. -/
def parameterRegisters (i : Fin 24) : Fin 64 := ⟨i.val, by omega⟩

/-- Register embedding for successive squares. -/
def sqrtRegisters (i : Fin 6) : Fin 64 := ⟨28 + i.val, by omega⟩

private theorem parameter_injective : parameterRegisters.Injective := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 64 => k.val) h)

private theorem sqrt_injective : sqrtRegisters.Injective := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp only [sqrtRegisters] at this
  omega

/-- The mathematical side length used by the reduction. -/
abbrev sideLength (N : ℕ) : ℕ := Nat.sqrt N + 1

/-- Parameters retained throughout the instance loop. -/
structure Parameters (N U : ℕ) (x : Data 64) : Prop where
  /-- Input length. -/
  len : x.regs len = N
  /-- Magnitude bound. -/
  upper : x.regs upper = U
  /-- Input starts after the length header. -/
  base : x.regs base = 1
  /-- AB follows the input. -/
  ab : x.regs matAB = N + 1
  /-- BC follows AB. -/
  bc : x.regs matBC = N + 1 + sideLength N * sideLength N
  /-- AC follows BC. -/
  ac : x.regs matAC = N + 1 + 2 * (sideLength N * sideLength N)
  /-- Solver scratch follows AC. -/
  free : x.regs free = N + 1 + 3 * (sideLength N * sideLength N)
  /-- Side length. -/
  side : x.regs side = sideLength N
  /-- Two instances per possible low-index sum. -/
  stop : x.regs stop = 2 * sideLength N
  /-- Positive invalid-index filler. -/
  filler : x.regs filler = 2 * U + 1
  /-- Sign-and-magnitude representation of that filler. -/
  encodedFiller : x.regs encodedFiller = 4 * U + 2
  /-- Loop increment. -/
  one : x.regs one = 1

/-- Input-length output of the parameter bank. -/
abbrev parameterLen : Fin 64 := 0
/-- Magnitude output of the parameter bank. -/
abbrev parameterUpper : Fin 64 := 1

/-- Copy the two needed parameter outputs and initialize constants. -/
def setup : Code .standard 64 := ram[
  len ← parameterLen; upper ← parameterUpper;
  base ← #1; one ← #1; sqrtArg ← len ]

/-- Consecutive output blocks and the two loop counters. -/
def layout : Code .standard 64 := ram[
  side ← sqrtRoot + one; area ← side * side; stop ← side + side;
  matAB ← base + len; matBC ← matAB + area; matAC ← matBC + area; free ← matAC + area;
  filler ← upper + upper; filler ← filler + one; encodedFiller ← filler + filler;
  inst ← #0; found ← #0 ]

/-- All initialization consists of actual native subprograms and charged register operations. -/
def prepare (κ : ℕ) : Code .standard 64 :=
  .seq ((ChanHe.Parameters.program κ).rename parameterRegisters)
    (.seq setup (.seq (NatSqrt.program.rename sqrtRegisters) layout))

private theorem exec_layout {w N U : ℕ} (x : Data 64)
    (hN : x.regs len = N) (hU : x.regs upper = U) (hb : x.regs base = 1)
    (ho : x.regs one = 1)
    (hr : x.regs sqrtRoot = Nat.sqrt N)
    (hsize : Fits w (N + 1 + 3 * (sideLength N * sideLength N)))
    (hfill : Fits w (4 * U + 2)) :
    ∃ y, ExecWithin w layout x y 12 ∧ Parameters N U y ∧
      y.regs inst = 0 ∧ y.regs found = 0 ∧ y.mem = x.mem := by
  let t := sideLength N
  have ht : Fits w t := hsize.of_le (by have := Nat.le_mul_self t; dsimp [t] at *; omega)
  have ha : Fits w (t * t) := hsize.of_le (by dsimp [t] at *; omega)
  have hs : Fits w (t + t) := hsize.of_le (by have := Nat.le_mul_self t; dsimp [t] at *; omega)
  have hab : Fits w (1 + N) := hsize.of_le (by omega)
  have hbc : Fits w (1 + N + t * t) := hsize.of_le (by dsimp [t] at *; omega)
  have hac : Fits w (1 + N + t * t + t * t) := hsize.of_le (by dsimp [t] at *; omega)
  have hfree : Fits w (1 + N + t * t + t * t + t * t) :=
    hsize.of_le (by dsimp [t] at *; omega)
  have hu2 : Fits w (U + U) := hfill.of_le (by omega)
  have hu1 : Fits w (U + U + 1) := hfill.of_le (by omega)
  have hu4 : Fits w (U + U + 1 + (U + U + 1)) := hfill.of_le (by omega)
  refine ⟨?y, ?run, ?parameters, ?counter, ?found, ?memory⟩
  case run =>
    ram_eval [layout, hr, ho, hN, hU, hb, ht, ha, hs, hab, hbc, hac, hfree,
      hu2, hu1, hu4, t, sideLength, len, upper, base, matAB, matBC, matAC,
      free, side, inst, stop, found, one, filler, encodedFiller, area, sqrtRoot, Fin.mk.injEq]
  case parameters =>
    constructor <;>
      simp +decide [Data.set_regs, len, upper, base, matAB,
        matBC, matAC, free, side, stop, filler, encodedFiller, one,
        hN, hU, hb, ho, sideLength] <;> omega
  case counter => simp [inst]
  case found => simp
  case memory => rfl

/-- Exact initialization from the ordinary length header. The existing parameter program
computes `U = (N+2)^κ`; its entire execution is charged, including the unused extra parameters.
The additional fit premises cover matrix addresses and the encoded filler, and are independent
of any solver execution contract. -/
theorem exec_prepare {w : ℕ} (κ : ℕ) (x : Data 64)
    (hbudget : Fits w (ChanHe.Parameters.Math.budget (x.mem 0) ((x.mem 0 + 2) ^ κ)))
    (hsize : Fits w (x.mem 0 + 1 + 3 * (sideLength (x.mem 0) * sideLength (x.mem 0))))
    (hfill : Fits w (4 * ((x.mem 0 + 2) ^ κ) + 2)) :
    ∃ y, ExecWithin w (prepare κ) x y
        (ChanHe.Parameters.time κ (x.mem 0) ((x.mem 0 + 2) ^ κ) +
          5 * Nat.sqrt (x.mem 0) + 24) ∧
      Parameters (x.mem 0) ((x.mem 0 + 2) ^ κ) y ∧
      y.regs inst = 0 ∧ y.regs found = 0 ∧ y.mem = x.mem := by
  let N := x.mem 0
  let U := (N + 2) ^ κ
  obtain ⟨p, hp, hout, hm⟩ := ChanHe.Parameters.exec κ (x.comap parameterRegisters) hbudget
  let a := p.extend parameterRegisters x
  have ha := hp.rename parameter_injective
  have han : a.regs parameterLen = N :=
    (parameter_injective.extend_apply _ _ ChanHe.Parameters.len).trans hout.len
  have hau : a.regs parameterUpper = U :=
    (parameter_injective.extend_apply _ _ ChanHe.Parameters.magnitude).trans hout.magnitude
  have ham : a.mem = x.mem := hm
  have h1 : Fits w 1 := hfill.of_le (by omega)
  let b := a.set len N |>.set upper U |>.set base 1 |>.set one 1
    |>.set sqrtArg N
  have hb : ExecWithin w setup a b 5 := by
    ram_eval [setup, b, han, hau, h1, parameterLen, parameterUpper, len, upper, base,
      one, sqrtArg, Fin.mk.injEq]
  have hbn : b.regs sqrtArg = N := by simp [b]
  have hsqrt : Fits w (4 * b.regs sqrtArg + 4) := hbudget.of_le (by
    rw [hbn]
    change 4 * N + 4 ≤ ChanHe.Parameters.Math.budget N U
    dsimp [ChanHe.Parameters.Math.budget]
    omega)
  obtain ⟨c, hc, hcr, -, hcm, -⟩ := NatSqrt.exec_rename sqrtRegisters sqrt_injective b hsqrt
  have hpres (i : Fin 64) (hi : 34 ≤ i.val) : c.regs i = b.regs i := by
    apply hc.regs_eq
    apply Code.preserves_rename_of_forall_ne
    intro j he
    have hv := congrArg Fin.val he
    dsimp only [sqrtRegisters] at hv
    have := j.isLt
    omega
  have hcr' : c.regs sqrtRoot = Nat.sqrt N := by
    change c.regs sqrtRoot = Nat.sqrt (b.regs sqrtArg) at hcr
    simpa only [hbn] using hcr
  have hc' : ExecWithin w (NatSqrt.program.rename sqrtRegisters) b c
      (5 * Nat.sqrt N + 7) := by
    change ExecWithin w _ b c (5 * Nat.sqrt (b.regs sqrtArg) + 7) at hc
    simpa only [hbn] using hc
  obtain ⟨y, hy, hparams, hi, hf, hym⟩ := exec_layout (N := N) (U := U) c
    ((hpres len (by decide)).trans (by
      simp +decide [b, N, U, len, sqrtArg, one, base, upper]))
    ((hpres upper (by decide)).trans (by
      simp +decide [b, N, U, upper, sqrtArg, one, base]))
    ((hpres base (by decide)).trans (by simp +decide [b, base, sqrtArg, one]))
    ((hpres one (by decide)).trans (by simp +decide [b, one, sqrtArg]))
    hcr' hsize hfill
  refine ⟨y, ?_, hparams, hi, hf, hym.trans (hcm.trans ham)⟩
  convert ha.seq (hb.seq (hc'.seq hy)) using 1
  · rfl
  · simp only [Data.comap_mem, N]
    omega

end Cslib.Algorithms.WordRAM.ThreeSum.Host
