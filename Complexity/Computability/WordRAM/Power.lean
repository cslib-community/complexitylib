/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
import Complexity.Computability.WordRAM.CountingLoop
import Complexity.Tactic.Fits

/-!
# Native natural powers

## Main definitions

* `Power.program`: repeated native multiplication, with base and exponent in registers.

## Main results

* `Power.exec`: `b^n` within `4n+5` instructions, with input-derived intermediate fits.
-/

@[expose] public section

namespace Cslib.WordRAM.Power

/-- Result accumulator, initially one. -/
abbrev value : Fin 5 := 0
/-- Number of completed multiplications. -/
abbrev counter : Fin 5 := 1
/-- Input base. -/
abbrev base : Fin 5 := 2
/-- Input exponent. -/
abbrev exponent : Fin 5 := 3
/-- Constant one, initialized by the routine. -/
abbrev one : Fin 5 := 4

/-- One multiplication and one counter increment. -/
def body : Code .standard 5 := ram[ value ← value * base; counter ← counter + one ]

/-- A fixed program for natural exponentiation by repeated multiplication. -/
def program : Code .standard 5 :=
  .seq (ram[ value ← #1; counter ← #0; one ← #1 ]) (.loop (.lt counter exponent) body)

/-- Output value, loop counters, input readback and memory after exponentiation. -/
def Post (b n : ℕ) (x y : Data 5) : Prop :=
  y.regs value = b ^ n ∧
  y.regs counter = n ∧ y.regs one = 1 ∧ y.mem = x.mem ∧
  y.regs base = b ∧ y.regs exponent = n

/-- The routine is uniform in its arguments and preserves memory and both input registers.
Every multiplication fit follows from the final power and exponent bound. -/
theorem exec {w : ℕ} (b n : ℕ) (hb : 1 ≤ b) (x : Data 5)
    (hx : x.regs base = b) (hn : x.regs exponent = n) (hfit : Fits w (b ^ n + n + 2)) :
    ∃ y, ExecWithin w program x y (4 * n + 5) ∧ Post b n x y := by
  unfold Post
  have h0 : Fits w 0 := by fits
  have h1 : Fits w 1 := by fits
  let start := ((x.set value 1).set counter 0).set one 1
  have hs : ExecWithin (B := .standard) w
      (ram[ value ← #1; counter ← #0; one ← #1 ]) x start 3 := by
    ram_eval [start, h0, h1, value, counter, one, Fin.mk.injEq]
  let P (j : ℕ) (y : Data 5) : Prop :=
    y.regs base = b ∧ y.regs exponent = n ∧ y.regs one = 1 ∧
      y.regs value = b ^ j ∧ y.mem = x.mem
  have hi : P (start.regs counter) start := by
    simp [P, start, hx, hn, base, exponent, one, counter, value]
  have hbody (y : Data 5) (hy : P (y.regs counter) y) (hc_lt : y.regs counter < n) :
      ∃ z, ExecWithin w body y z 2 ∧ P (y.regs counter + 1) z ∧
        z.regs counter = y.regs counter + 1 := by
    obtain ⟨hbv, hnv, ho, hv, hm⟩ := hy
    have hpn : b ^ (y.regs counter + 1) ≤ b ^ n := Nat.pow_le_pow_right hb (by omega)
    have hp : Fits w (b ^ (y.regs counter + 1)) := by fits
    have hj : Fits w (y.regs counter + 1) := by fits
    let z := (y.set value (b ^ (y.regs counter + 1))).set counter (y.regs counter + 1)
    have he : ExecWithin w body y z 2 := by
      ram_eval [body, z, hbv, ho, hv, ← pow_succ, hp, hj,
        value, counter, base, one, Fin.mk.injEq]
    refine ⟨z, he, ?_, by simp [z]⟩
    simpa +decide [P, z, base, exponent, one, counter, value, Function.update_apply] using
      (show y.regs base = b ∧ y.regs exponent = n ∧ y.regs one = 1 ∧ y.mem = x.mem from
        ⟨hbv, hnv, ho, hm⟩)
  obtain ⟨y, he, ⟨hyb, hyn, hy1, hyv, hym⟩, hj⟩ := ExecWithin.loop_count P
    (fun y hy => hy.2.1) hbody (by simp [start, counter, one]) hi
  refine ⟨y, ?_, hyv, hj, hy1, hym, hyb, hyn⟩
  · apply (hs.seq he).mono
    have hs0 : start.regs counter = 0 := by simp [start, counter, one]
    rw [hs0, Nat.sub_zero]
    omega

end Cslib.WordRAM.Power
