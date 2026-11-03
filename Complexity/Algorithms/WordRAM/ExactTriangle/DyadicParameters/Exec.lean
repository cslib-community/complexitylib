/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.DyadicParameters.Program
import Complexity.Computability.WordRAM.RegisterFrame

/-!
# Actual native parameter computation from the original dimension

The original scalar n derives every logarithm, power and arithmetic fit. The actual calls
and all setup/copy/branch instructions are charged. No exponent, logarithm, power, parameter
table or execution certificate is an input to the public rule.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters

open Cslib.WordRAM
open Cslib.Algorithms.ExactTriangle

/-- Original-scalar word envelope, including all fixed constants and both power calls. -/
@[expose] def wordBudget (n : ℕ) : ℕ := 1296 + 32 * (n + 1)

/-- Charged complete caller computation, before the final halt. -/
@[expose] def timeBound (n : ℕ) : ℕ :=
  4 * Nat.log 2 n + 4 * ParameterChoice.blocks n + 4 * ParameterChoice.level n + 33

private def Ready (n : ℕ) (x : Data 16) : Prop := x.regs Reg.side = n ∧
  x.regs Reg.blocks = ParameterChoice.blocks n ∧ x.regs Reg.level = ParameterChoice.level n ∧
  x.regs Reg.tensorDepth = ParameterChoice.tensorDepth n ∧ x.regs Reg.four = 4

private theorem power_preserves : ∀ i : Fin 16, i.val < 7 ∨ 12 ≤ i.val →
    (Power.program.rename powerRegisters).Preserves i := by decide +kernel

private theorem Ready.after_power {w n : ℕ} {x y : Data 16} {t : ℕ}
    (hx : Ready n x) (he : ExecWithin w (Power.program.rename powerRegisters) x y t) :
    Ready n y :=
  ⟨(he.regs_eq (power_preserves Reg.side (by decide))).trans hx.1,
    (he.regs_eq (power_preserves Reg.blocks (by decide))).trans hx.2.1,
    (he.regs_eq (power_preserves Reg.level (by decide))).trans hx.2.2.1,
    (he.regs_eq (power_preserves Reg.tensorDepth (by decide))).trans hx.2.2.2.1,
    (he.regs_eq (power_preserves Reg.four (by decide))).trans hx.2.2.2.2⟩

private theorem exec_finish {w n : ℕ} (x : Data 16)
    (hb : x.regs Reg.blocks = ParameterChoice.blocks n)
    (hv : x.regs Reg.workValue = ParameterChoice.window n)
    (hf : Fits w (wordBudget n)) :
    ∃ y, ExecWithin w finish x y 5 ∧ y.regs Reg.window = ParameterChoice.window n ∧
      y.regs Reg.fast = (if 0 < ParameterChoice.blocks n then 1 else 0) ∧ y.mem = x.mem ∧
      ∀ i, i ≠ Reg.window → i ≠ Reg.fast → y.regs i = x.regs i := by
  let y := (x.set Reg.window (ParameterChoice.window n)).set Reg.fast
    (if 0 < ParameterChoice.blocks n then 1 else 0)
  have h0 : Fits w 0 := hf.of_le (Nat.zero_le _)
  have h1 : Fits w 1 := hf.of_le (by unfold wordBudget; omega)
  let start := (x.set Reg.window (ParameterChoice.window n)).set Reg.fast 0
  have pre : ExecWithin (B := .standard) w
      (ram[ Reg.window ← Reg.workValue; Reg.fast ← #0 ]) x start 2 := by
    ram_eval [start, hv, h0, Reg.window, Reg.workValue, Reg.fast, Fin.mk.injEq]
  have he : ExecWithin w finish x y 5 := by
    by_cases hp : 0 < ParameterChoice.blocks n
    · have hc : ExecWithin (B := .standard) w (ram[ Reg.fast ← #1 ]) start y 1 := by
        ram_eval [y, start, hp, h1, Data.set, Function.update_idem,
          Reg.window, Reg.fast, Fin.mk.injEq]
      have cond : (Cond.lt Reg.fast Reg.blocks).Holds start := by
        simpa +decide [start, hb, Reg.window, Reg.fast, Reg.blocks] using hp
      exact (pre.seq (ExecWithin.branch_pos cond hc)).mono (by omega)
    · have hc : ExecWithin (B := .standard) w (ram[ Reg.fast ← Reg.fast ]) start y 1 := by
        ram_eval [y, start, hp, Data.set, Function.update_idem,
          Reg.window, Reg.fast, Fin.mk.injEq]
      have cond : ¬(Cond.lt Reg.fast Reg.blocks).Holds start := by
        simpa +decide [start, hb, Reg.window, Reg.fast, Reg.blocks] using hp
      exact pre.seq (ExecWithin.branch_neg cond hc)
  refine ⟨y, he, ?_, ?_, rfl, ?_⟩
  · simp +decide [y, Reg.window, Reg.fast]
  · simp only [y, Data.set_regs, Function.update_self]
  · intro i hw hf
    simp only [y, Data.set_regs, Function.update_of_ne hf, Function.update_of_ne hw]

/-- Execute the logarithm, rounded exponent arithmetic, two real powers and regime flag.
Memory and the original n are preserved. All fits follow from one original-scalar envelope. -/
theorem exec {w n : ℕ} (x : Data 16) (hn : x.regs Reg.side = n)
    (hfit : Fits w (wordBudget n)) :
    ∃ y, ExecWithin w program x y (timeBound n) ∧
      y.regs Reg.side = n ∧ y.regs Reg.blocks = ParameterChoice.blocks n ∧
      y.regs Reg.level = ParameterChoice.level n ∧ y.regs Reg.window = ParameterChoice.window n ∧
      y.regs Reg.groups = ParameterChoice.groups n ∧
      y.regs Reg.tensorDepth = ParameterChoice.tensorDepth n ∧
      y.regs Reg.fast = (if 0 < ParameterChoice.blocks n then 1 else 0) ∧ y.mem = x.mem := by
  have ht : ParameterChoice.blocks n ≤ n :=
    (ParameterChoice.blocks_le_log n).trans (Nat.log_le_self 2 n)
  have hm : ParameterChoice.level n ≤ n :=
    (ParameterChoice.level_le_log n).trans (Nat.log_le_self 2 n)
  have hL : ParameterChoice.tensorDepth n ≤ 19 * n := Nat.mul_le_mul_left 19 hm
  have hg := (ParameterChoice.powers_le n).1
  have hD := (ParameterChoice.powers_le n).2
  have hlog := Nat.log_le_self 2 n
  have h1296 : Fits w 1296 := hfit.of_le (by unfold wordBudget; omega)
  have h36 : Fits w 36 := hfit.of_le (by unfold wordBudget; omega)
  have h19 : Fits w 19 := hfit.of_le (by unfold wordBudget; omega)
  have h4 : Fits w 4 := hfit.of_le (by unfold wordBudget; omega)
  have hblocks : Fits w (ParameterChoice.blocks n) := hfit.of_le (by unfold wordBudget; omega)
  have hlevel : Fits w (ParameterChoice.level n) := hfit.of_le (by unfold wordBudget; omega)
  have hlength : Fits w (ParameterChoice.tensorDepth n) := hfit.of_le (by unfold wordBudget; omega)
  have htFit : Fits w (Nat.log 2 n / 1296) := hblocks
  have hmFit : Fits w (36 * (Nat.log 2 n / 1296)) := hlevel
  have hLFit : Fits w (19 * (36 * (Nat.log 2 n / 1296))) := hlength
  have hpg : Fits w (4 ^ ParameterChoice.blocks n + ParameterChoice.blocks n + 2) := hfit.of_le (by
    change ParameterChoice.groups n + ParameterChoice.blocks n + 2 ≤ _
    unfold wordBudget
    omega)
  have hpD : Fits w (4 ^ ParameterChoice.level n + ParameterChoice.level n + 2) := hfit.of_le (by
    change ParameterChoice.window n + ParameterChoice.level n + 2 ≤ _
    unfold wordBudget
    omega)
  have log_inj : Function.Injective logRegisters := by
    intro i j h
    apply Fin.ext
    have hv := congrArg (fun i : Fin 16 => i.val) h
    dsimp [logRegisters] at hv
    omega
  have pow_inj : Function.Injective powerRegisters := by
    intro i j h
    apply Fin.ext
    have hv := congrArg (fun i : Fin 16 => i.val) h
    dsimp [powerRegisters] at hv
    omega
  let a := x.set Reg.workValue n
  have copy : ExecWithin (B := .standard) w (ram[ Reg.workValue ← Reg.side ]) x a 1 := by
    simpa only [hn] using ExecWithin.copy (w := w) (x := x) (d := Reg.workValue) (s := Reg.side)
  obtain ⟨b, hb, blog, bmem, _, _⟩ := NatLog.exec_rename logRegisters log_inj a
    (hfit.of_le (by unfold wordBudget; omega))
    (hfit.of_le (by change n ≤ _; unfold wordBudget; omega))
    (hfit.of_le (by change Nat.log 2 n + 1 ≤ _; unfold wordBudget; omega))
  have bside : b.regs Reg.side = n := by
    have frame := hb.regs_eq (Code.preserves_rename_of_forall_ne NatLog.program logRegisters
      Reg.side (by
        intro i h
        have hv := congrArg (fun i : Fin 16 => i.val) h
        dsimp [logRegisters, Reg.side] at hv
        omega))
    exact frame.trans (by simpa +decide [a, Reg.side, Reg.workValue] using hn)
  have blog' : b.regs Reg.workCount = Nat.log 2 n := blog
  let c := ((((((((b.set Reg.divisor 1296).set Reg.blocks (ParameterChoice.blocks n)).set
    Reg.thirtySix 36).set Reg.level (ParameterChoice.level n)).set Reg.nineteen 19).set
    Reg.tensorDepth (ParameterChoice.tensorDepth n)).set Reg.four 4).set Reg.workBase 4).set
    Reg.workExponent (ParameterChoice.blocks n)
  have prep : ExecWithin w prepare b c 9 := by
    ram_eval [prepare, c, blog', ParameterChoice.blocks, ParameterChoice.level,
      ParameterChoice.tensorDepth,
      h1296, h36, h19, h4, htFit, hmFit, hLFit, Reg.divisor, Reg.blocks,
      Reg.thirtySix, Reg.level, Reg.nineteen, Reg.tensorDepth, Reg.four, Reg.workBase,
      Reg.workExponent, Reg.workCount, Fin.mk.injEq]
  have cReady : Ready n c := by
    refine ⟨?_, rfl, rfl, rfl, rfl⟩
    simpa +decide [c, Reg.side, Reg.divisor, Reg.blocks, Reg.thirtySix, Reg.level,
      Reg.nineteen, Reg.tensorDepth, Reg.four, Reg.workBase, Reg.workExponent] using bside
  obtain ⟨d, hd, dg, _, _, dmem, _, _, _⟩ := Power.exec_rename powerRegisters pow_inj
    4 (ParameterChoice.blocks n) (by decide) c (by rfl) (by rfl) hpg
  have dReady := cReady.after_power hd
  have dg' : d.regs Reg.workValue = ParameterChoice.groups n := dg
  let e := ((d.set Reg.groups (ParameterChoice.groups n)).set Reg.workBase 4).set
    Reg.workExponent (ParameterChoice.level n)
  have next : ExecWithin w nextPower d e 3 := by
    ram_eval [nextPower, e, dg', dReady.2.2.1, dReady.2.2.2.2,
      Reg.groups, Reg.workValue, Reg.workBase, Reg.workExponent, Reg.level, Reg.four,
      Fin.mk.injEq]
  have eReady : Ready n e := by
    simpa +decide [Ready, e, Reg.side, Reg.blocks, Reg.level, Reg.tensorDepth, Reg.four,
      Reg.groups, Reg.workBase, Reg.workExponent] using dReady
  obtain ⟨f, hf, fD, _, _, fmem, _, _, _⟩ := Power.exec_rename powerRegisters pow_inj
    4 (ParameterChoice.level n) (by decide) e (by rfl) (by rfl) hpD
  have fReady := eReady.after_power hf
  have fg : f.regs Reg.groups = ParameterChoice.groups n :=
    (hf.regs_eq (power_preserves Reg.groups (by decide))).trans (by rfl)
  obtain ⟨y, hy, yD, yflag, ymem, yr⟩ := exec_finish f fReady.2.1 fD hfit
  have full := copy.seq (hb.seq (prep.seq (hd.seq (next.seq (hf.seq hy)))))
  refine ⟨y, full.mono ?_, ?_, ?_, ?_, yD, ?_, ?_, yflag, ?_⟩
  · change 1 + (4 * Nat.log 2 n + 5 + (9 + (4 * ParameterChoice.blocks n + 5 +
      (3 + (4 * ParameterChoice.level n + 5 + 5))))) ≤ timeBound n
    unfold timeBound
    omega
  · exact (yr Reg.side (by decide) (by decide)).trans fReady.1
  · exact (yr Reg.blocks (by decide) (by decide)).trans fReady.2.1
  · exact (yr Reg.level (by decide) (by decide)).trans fReady.2.2.1
  · exact (yr Reg.groups (by decide) (by decide)).trans fg
  · exact (yr Reg.tensorDepth (by decide) (by decide)).trans fReady.2.2.2.1
  · exact ymem.trans (fmem.trans (dmem.trans bmem))

/-- Actual execution is logarithmic, even using conservative bounds for both power calls. -/
theorem timeBound_le (n : ℕ) : timeBound n ≤ 12 * Nat.log 2 n + 33 := by
  have ht := ParameterChoice.blocks_le_log n
  have hm := ParameterChoice.level_le_log n
  unfold timeBound
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.DyadicParameters
