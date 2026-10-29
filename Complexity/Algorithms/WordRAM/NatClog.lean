/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Mathlib.Data.Nat.Log

/-!
# A charged native ceiling binary logarithm

## Main definitions

* `NatClog.program`: successive ceiling division by two.

## Main results

* `NatClog.exec`: the ceiling logarithm with a logarithmic charged instruction bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.NatClog

open Cslib.WordRAM

/-- Quotient, initially the input. -/
abbrev arg : Fin 4 := 0
/-- Ceiling logarithm output. -/
abbrev result : Fin 4 := 1
/-- Constant one. -/
abbrev one : Fin 4 := 2
/-- Constant two. -/
abbrev two : Fin 4 := 3

/-- Divide the quotient by two and increment the answer. -/
def body : Code .standard 4 := ram[ arg ← arg + one; arg ← arg / two; result ← result + one ]

/-- Fixed code for `Nat.clog 2`, including its value zero at input zero. -/
def program : Code .standard 4 :=
  .seq (ram[ result ← #0; one ← #1; two ← #2 ]) (.loop (.lt one arg) body)

/-- Compute the ceiling binary logarithm in at most `5 ⌈log₂ n⌉ + 5` instructions.
Memory is untouched and the input quotient is consumed. -/
theorem exec {w : ℕ} (x : Data 4) (h2 : Fits w 2) (hn : Fits w (x.regs arg + 1))
    (hout : Fits w (Nat.clog 2 (x.regs arg) + 1)) :
    ∃ y, ExecWithin w program x y (5 * Nat.clog 2 (x.regs arg) + 5) ∧
      y.regs result = Nat.clog 2 (x.regs arg) ∧ y.mem = x.mem ∧
      y.regs one = 1 ∧ y.regs two = 2 := by
  let I (y : Data 4) : Prop := y.regs one = 1 ∧ y.regs two = 2 ∧
    y.regs arg ≤ x.regs arg ∧
    y.regs result + Nat.clog 2 (y.regs arg) = Nat.clog 2 (x.regs arg) ∧ y.mem = x.mem
  have hbody (y : Data 4) (hy : I y) (hc : (Cond.lt one arg).Holds y) :
      ∃ z, ExecWithin w body y z 3 ∧ I z ∧
        Nat.clog 2 (z.regs arg) < Nat.clog 2 (y.regs arg) := by
    obtain ⟨ho, ht, harg, hsum, hm⟩ := hy
    have hgt : 1 < y.regs arg := by simpa only [Cond.holds_lt, ho] using hc
    have hpos : 0 < Nat.clog 2 (y.regs arg) := Nat.clog_pos (by decide) (by omega)
    have hadd : Fits w (y.regs arg + 1) := hn.of_le (by omega)
    have hdiv : Fits w ((y.regs arg + 1) / 2) :=
      hn.of_le ((Nat.div_le_self _ _).trans (by omega))
    have hinc : Fits w (y.regs result + 1) := hout.of_le (by omega)
    refine ⟨?z, ?run, ?inv, ?decrease⟩
    case run => ram_eval [body, ho, ht, hadd, hdiv, hinc, arg, result, one, two, Fin.mk.injEq]
    case inv =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa +decide [Function.update_apply] using ho
      · simpa +decide [Function.update_apply] using ht
      · simpa +decide [Function.update_apply] using
          (show (y.regs arg + 1) / 2 ≤ x.regs arg from by omega)
      · change y.regs result + 1 + Nat.clog 2 ((y.regs arg + 1) / 2) = Nat.clog 2 (x.regs arg)
        have h := Nat.clog_of_two_le (b := 2) (by decide) (by omega : 2 ≤ y.regs arg)
        simp only [show y.regs arg + 2 - 1 = y.regs arg + 1 by omega] at h
        omega
      · exact hm
    case decrease =>
      change Nat.clog 2 ((y.regs arg + 1) / 2) < Nat.clog 2 (y.regs arg)
      have h := Nat.clog_of_two_le (b := 2) (by decide) (by omega : 2 ≤ y.regs arg)
      simp only [show y.regs arg + 2 - 1 = y.regs arg + 1 by omega] at h
      omega
  let x₀ := ((x.set result 0).set one 1).set two 2
  have hx₀ : I x₀ := by simp +decide [I, x₀, arg, result, one, two]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => Nat.clog 2 (y.regs arg)) hbody hx₀
  obtain ⟨ho, ht, harg, hsum, hm⟩ := hy
  have hzero : Nat.clog 2 (y.regs arg) = 0 := by
    have hle : y.regs arg ≤ 1 := by simpa only [Cond.holds_lt, ho, not_lt] using hc
    exact Nat.clog_of_right_le_one hle 2
  refine ⟨y, ?_, by omega, hm, ho, ht⟩
  have h1 : Fits w 1 := h2.of_le (by decide)
  have hinit : ExecWithin (B := .standard) w (ram[ result ← #0; one ← #1; two ← #2 ]) x x₀ 3 := by
    ram_eval [x₀, h1, h2]
  convert hinit.seq he using 1
  · rfl
  · simp +decide only [x₀, Data.set_regs, Function.update_apply, arg, result, one, two,
      ↓reduceIte]
    omega

/-- Run the routine on any injectively chosen registers. -/
theorem exec_rename {r w : ℕ} (f : Fin 4 → Fin r) (hf : f.Injective) (x : Data r)
    (h2 : Fits w 2) (hn : Fits w (x.regs (f arg) + 1))
    (hout : Fits w (Nat.clog 2 (x.regs (f arg)) + 1)) :
    ∃ y, ExecWithin w (program.rename f) x y (5 * Nat.clog 2 (x.regs (f arg)) + 5) ∧
      y.regs (f result) = Nat.clog 2 (x.regs (f arg)) ∧ y.mem = x.mem ∧
      y.regs (f one) = 1 ∧ y.regs (f two) = 2 := by
  obtain ⟨a, ha, hr, hm, ho, ht⟩ := exec (x.comap f) h2 hn hout
  refine ⟨a.extend f x, ha.rename hf, ?_, hm, ?_, ?_⟩
  · exact (hf.extend_apply _ _ result).trans hr
  · exact (hf.extend_apply _ _ one).trans ho
  · exact (hf.extend_apply _ _ two).trans ht

end Cslib.Algorithms.WordRAM.NatClog
