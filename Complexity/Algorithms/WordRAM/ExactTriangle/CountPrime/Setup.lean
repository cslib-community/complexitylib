/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Layout
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Logarithm

/-!
# Computed counter metadata and native setup

The actual logarithm and power routines determine the padding and every pointer. The internal
register predicate records that execution's resulting words; it is not an algorithm argument
or a supplied layout. Later native stages preserve these metadata registers.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Original scalar/pointer envelope for actual address, index, length and count arithmetic.
The signed arithmetic magnitude envelope is accounted for separately. -/
@[expose] def addressBudget (n p k scratch a b c : ℕ) : ℕ :=
  32 * (a + b + c + scratch + n * n * n + n * n + 4 ^ k * p + 4 ^ k +
    2 ^ k + k + p + n + 4)

/-- Exactly the persistent counter metadata, excluding its mutable raw result. -/
@[expose] def MetadataRegister (j : Fin 128) : Prop :=
  64 ≤ j.val ∧ (j.val ≤ 86 ∨ j.val = 98 ∨ j.val = 101) ∧ j ≠ Reg.result

instance (j : Fin 128) : Decidable (MetadataRegister j) :=
  inferInstanceAs
    (Decidable (64 ≤ j.val ∧ (j.val ≤ 86 ∨ j.val = 98 ∨ j.val = 101) ∧ j ≠ Reg.result))

/-- The actual computed layout, protected original pointers and initialized constants. -/
structure CounterRegisters (n p k scratch a b c : ℕ) (x : Data 128) : Prop where
  /-- Computed powers, matrix lengths and all workspace pointers. -/
  layout : LayoutRegisters n p k scratch x
  /-- Original AB pointer. -/
  inputAB : x.regs Reg.inputAB = a
  /-- Original BC pointer. -/
  inputBC : x.regs Reg.inputBC = b
  /-- Original AC pointer. -/
  inputAC : x.regs Reg.inputAC = c
  /-- Actual constant zero. -/
  zero : x.regs Reg.zero = 0
  /-- Actual constant one. -/
  one : x.regs Reg.one = 1
  /-- Raw two, also the canonical signed word for one. -/
  two : x.regs Reg.two = 2
  /-- Actual constant four. -/
  four : x.regs Reg.four = 4

/-- Native stages that leave the persistent metadata unchanged retain its computed meaning. -/
theorem CounterRegisters.congr {n p k scratch a b c : ℕ} {x y : Data 128}
    (h : CounterRegisters n p k scratch a b c x)
    (keep : ∀ j, MetadataRegister j → y.regs j = x.regs j) :
    CounterRegisters n p k scratch a b c y := by
  rcases h with ⟨L, ha, hb, hc, h0, h1, h2, h4⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases L
    constructor <;> rwa [keep _ (by decide)]
  all_goals rwa [keep _ (by decide)]

/-- Execute the actual depth calculation and layout, with every argument, constant, power and
pointer instruction charged. The input contains no padding-depth or layout certificate. -/
theorem exec_setup {W n p scratch a b c : ℕ} (x : Data 128) (hp0 : 0 < p)
    (hn : x.regs Reg.side = n) (hp : x.regs Reg.modulus = p)
    (ha : x.regs Reg.inputAB = a) (hb : x.regs Reg.inputBC = b)
    (hc : x.regs Reg.inputAC = c) (hs : x.regs Reg.scratch = scratch)
    (hw : Fits W (layoutWordBound n p (Nat.clog 2 n) scratch + n + Nat.clog 2 n + 8)) :
    ∃ y, ExecWithin W setup x y (9 * Nat.clog 2 n + 31) ∧
      CounterRegisters n p (Nat.clog 2 n) scratch a b c y ∧ y.mem = x.mem := by
  let k := Nat.clog 2 n
  obtain ⟨s, logRun, depth, h0, h1, h2, h4, memory, keep⟩ := exec_logarithm x
    (by rw [hn]; exact hw.of_le (by omega))
  have sreg (j : Fin 128) (hj : MetadataRegister j) (hd : j ≠ Reg.depth)
      (hz : j ≠ Reg.zero) (ho : j ≠ Reg.one) (ht : j ≠ Reg.two)
      (hf : j ≠ Reg.four) : s.regs j = x.regs j :=
    keep j (by unfold MetadataRegister at hj; omega) hd hz ho ht hf
  have sk : s.regs Reg.depth = k := by simpa only [hn] using depth
  obtain ⟨y, layoutRun, L, ym, yr⟩ := exec_layout s hp0
    ((sreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn)
    ((sreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hp)
    sk
    ((sreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs)
    h2 (hw.of_le (by dsimp only [k]; omega))
  have preserved (j : Fin 128) (hj : ¬LayoutLocal j) : y.regs j = s.regs j := yr j hj
  refine ⟨y, ?_, ⟨L, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ym.trans memory⟩
  · exact (logRun.seq layoutRun).mono (by rw [hn]; dsimp only [k]; omega)
  · exact (preserved _ (by decide)).trans
      ((sreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ha)
  · exact (preserved _ (by decide)).trans
      ((sreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb)
  · exact (preserved _ (by decide)).trans
      ((sreg _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc)
  · exact (preserved _ (by decide)).trans h0
  · exact (preserved _ (by decide)).trans h1
  · exact (preserved _ (by decide)).trans h2
  · exact (preserved _ (by decide)).trans h4

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
