/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

/-!
# A charged native integer square root

## Main definitions

* `NatSqrt.program`: successive squares.

## Main results

* `NatSqrt.exec`: integer square root in a square-root number of native instructions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.NatSqrt

open Cslib.WordRAM

/-- Input integer, preserved. -/
abbrev arg : Fin 6 := 0
/-- Current root and output. -/
abbrev root : Fin 6 := 1
/-- Successor of the current root. -/
abbrev next : Fin 6 := 2
/-- Square of the successor. -/
abbrev square : Fin 6 := 3
/-- Constant one. -/
abbrev one : Fin 6 := 4
/-- Input plus one. -/
abbrev bound : Fin 6 := 5

/-- Advance the root and compute the next square. -/
def body : Code .standard 6 := ram[
  root ← next; next ← next + one; square ← next * next ]

/-- A fixed program for the integer square root, with all square computations charged. -/
def program : Code .standard 6 :=
  .seq (ram[ root ← #0; next ← #1; square ← #1; one ← #1; bound ← arg + one ])
    (.loop (.lt square bound) body)

/-- Compute `Nat.sqrt n` in at most `5 sqrt(n) + 7` instructions, preserving input and memory.
The linear bound `4n + 4` covers the final unsuccessful square as well as all counters. -/
theorem exec {w : ℕ} (x : Data 6) (hfit : Fits w (4 * x.regs arg + 4)) :
    ∃ y, ExecWithin w program x y (5 * Nat.sqrt (x.regs arg) + 7) ∧
      y.regs root = Nat.sqrt (x.regs arg) ∧ y.regs arg = x.regs arg ∧ y.mem = x.mem ∧
      y.regs one = 1 := by
  let n := x.regs arg
  let I (y : Data 6) : Prop := y.regs arg = n ∧ y.regs one = 1 ∧
    y.regs bound = n + 1 ∧ y.regs next = y.regs root + 1 ∧
    y.regs square = y.regs next * y.regs next ∧
    y.regs root ≤ Nat.sqrt n ∧ y.mem = x.mem
  have hbody (y : Data 6) (hy : I y) (hc : (Cond.lt square bound).Holds y) :
      ∃ z, ExecWithin w body y z 3 ∧ I z ∧
        Nat.sqrt n - z.regs root < Nat.sqrt n - y.regs root := by
    obtain ⟨ha, ho, hb, hn, hsq, hr, hm⟩ := hy
    have hsmall : y.regs next * y.regs next ≤ n := by
      simp only [Cond.holds_lt, hsq, hb] at hc
      omega
    have hnext : y.regs next ≤ Nat.sqrt n := Nat.le_sqrt.mpr hsmall
    have hsl := Nat.sqrt_le n
    have hsle := Nat.sqrt_le_self n
    have hstep : Fits w (y.regs next + 1) := hfit.of_le (by dsimp [n] at *; omega)
    have hsquare : Fits w ((y.regs next + 1) * (y.regs next + 1)) := hfit.of_le (by
      change (y.regs next + 1) * (y.regs next + 1) ≤ 4 * n + 4
      have hnn : y.regs next ≤ n := hnext.trans hsle
      nlinarith)
    refine ⟨?z, ?run, ?inv, ?decrease⟩
    case run => ram_eval [body, ho, hstep, hsquare, root, next, square, one, Fin.mk.injEq]
    case inv =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa +decide [Function.update_apply] using ha
      · simpa +decide [Function.update_apply] using ho
      · simpa +decide [Function.update_apply] using hb
      · rfl
      · rfl
      · exact hnext
      · exact hm
    case decrease =>
      change Nat.sqrt n - y.regs next < Nat.sqrt n - y.regs root
      omega
  let x₀ := ((((x.set root 0).set next 1).set square 1).set one 1).set bound (n + 1)
  have hx₀ : I x₀ := by simp +decide [I, x₀, n, root, next, square, one, bound, arg]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => Nat.sqrt n - y.regs root) hbody hx₀
  obtain ⟨ha, ho, hb, hn, hsq, hr, hm⟩ := hy
  have hlarge : n < (y.regs root + 1) * (y.regs root + 1) := by
    simp only [Cond.holds_lt, hsq, hn, hb] at hc
    omega
  have hout : y.regs root = Nat.sqrt n := by
    have h := Nat.sqrt_lt.mpr hlarge
    omega
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have hbfit : Fits w (x.regs arg + 1) := hfit.of_le (by omega)
  have hinit : ExecWithin (B := .standard) w
      (ram[ root ← #0; next ← #1; square ← #1; one ← #1; bound ← arg + one ]) x x₀ 5 := by
    ram_eval [x₀, n, h1, hbfit, root, next, square, one, bound, arg, Fin.mk.injEq]
  refine ⟨y, ?_, hout, ha, hm, ho⟩
  convert hinit.seq he using 1
  · rfl
  · simp +decide only [x₀, Data.set_regs, Function.update_apply, root, next, square, one,
      bound, arg, n, ↓reduceIte, Nat.sub_zero]
    omega

/-- Run successive squares on any injectively chosen registers. -/
theorem exec_rename {r w : ℕ} (f : Fin 6 → Fin r) (hf : f.Injective) (x : Data r)
    (hfit : Fits w (4 * x.regs (f arg) + 4)) :
    ∃ y, ExecWithin w (program.rename f) x y (5 * Nat.sqrt (x.regs (f arg)) + 7) ∧
      y.regs (f root) = Nat.sqrt (x.regs (f arg)) ∧
      y.regs (f arg) = x.regs (f arg) ∧ y.mem = x.mem ∧ y.regs (f one) = 1 := by
  obtain ⟨a, ha, hr, hn, hm, ho⟩ := exec (x.comap f) hfit
  refine ⟨a.extend f x, ha.rename hf, ?_, ?_, hm, ?_⟩
  · exact (hf.extend_apply _ _ root).trans hr
  · exact (hf.extend_apply _ _ arg).trans hn
  · exact (hf.extend_apply _ _ one).trans ho

end Cslib.Algorithms.WordRAM.NatSqrt
