/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
import Mathlib.Tactic.NormNum

/-!
# Initializing the four columns of a Chan–He node

## Main definitions

* `Padding.program`: a fixed loop writing a four-word pattern to every group.

## Main results

* `Padding.exec`: exact memory and a charged `12N+5` instruction bound.

## References

This native program and its execution proof are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Padding

open Cslib.WordRAM

/-- Packed output base. -/
abbrev dst : Fin 10 := 0
/-- Number of four-cell groups. -/
abbrev len : Fin 10 := 1
/-- Padding word for column zero. -/
abbrev pad0 : Fin 10 := 2
/-- Padding word for column one. -/
abbrev pad1 : Fin 10 := 3
/-- Padding word for column two. -/
abbrev pad2 : Fin 10 := 4
/-- Padding word for column three. -/
abbrev pad3 : Fin 10 := 5
/-- Group cursor. -/
abbrev idx : Fin 10 := 6
/-- Temporary address. -/
abbrev addr : Fin 10 := 7
/-- Constant one. -/
abbrev one : Fin 10 := 8
/-- Constant four. -/
abbrev four : Fin 10 := 9

/-- A concrete four-word pattern, addressed by its residue modulo four. -/
def pattern (p₀ p₁ p₂ p₃ u : ℕ) : ℕ :=
  if u % 4 = 0 then p₀ else if u % 4 = 1 then p₁ else if u % 4 = 2 then p₂ else p₃

/-- Initial memory with the first `k` groups overwritten, including all padding. -/
def memory (mem : ℕ → ℕ) (dst p₀ p₁ p₂ p₃ k : ℕ) : ℕ → ℕ := fun a =>
  if dst ≤ a ∧ a < dst + 4 * k then pattern p₀ p₁ p₂ p₃ (a - dst) else mem a

@[simp] theorem memory_zero (mem : ℕ → ℕ) (dst p₀ p₁ p₂ p₃ : ℕ) :
    memory mem dst p₀ p₁ p₂ p₃ 0 = mem := by
  funext a
  simp [memory]

/-- Four distinct stores make one complete group. -/
theorem memory_succ (mem : ℕ → ℕ) (dst p₀ p₁ p₂ p₃ k : ℕ) :
    memory mem dst p₀ p₁ p₂ p₃ (k + 1) =
      Function.update (Function.update (Function.update (Function.update
        (memory mem dst p₀ p₁ p₂ p₃ k) (dst + 4 * k) p₀)
          (dst + 4 * k + 1) p₁) (dst + 4 * k + 2) p₂) (dst + 4 * k + 3) p₃ := by
  funext a
  by_cases h₀ : a = dst + 4 * k
  · subst a; simp [memory, pattern]
  by_cases h₁ : a = dst + 4 * k + 1
  · subst a
    simp [memory, pattern, show dst + 4 * k + 1 - dst = 4 * k + 1 by omega,
      show dst ≤ dst + 4 * k + 1 by omega,
      show dst + 4 * k + 1 < dst + 4 * (k + 1) by omega]
  by_cases h₂ : a = dst + 4 * k + 2
  · subst a
    simp [memory, pattern, show dst + 4 * k + 2 - dst = 4 * k + 2 by omega,
      show dst ≤ dst + 4 * k + 2 by omega,
      show dst + 4 * k + 2 < dst + 4 * (k + 1) by omega]
  by_cases h₃ : a = dst + 4 * k + 3
  · subst a
    simp [memory, pattern, show dst + 4 * k + 3 - dst = 4 * k + 3 by omega,
      show dst ≤ dst + 4 * k + 3 by omega,
      show dst + 4 * k + 3 < dst + 4 * (k + 1) by omega]
  simp only [Function.update_of_ne h₃, Function.update_of_ne h₂,
    Function.update_of_ne h₁, Function.update_of_ne h₀, memory]
  have he : (dst ≤ a ∧ a < dst + 4 * (k + 1)) ↔ (dst ≤ a ∧ a < dst + 4 * k) := by omega
  simp only [he]

/-- Every address, store and increment of a four-word group is charged. -/
def body : Code .standard 10 := ram[
  addr ← four * idx; addr ← dst + addr; *addr ← pad0;
  addr ← addr + one; *addr ← pad1; addr ← addr + one; *addr ← pad2;
  addr ← addr + one; *addr ← pad3; idx ← idx + one ]

/-- Runtime pattern values and length, with fixed code and registers. -/
def program : Code .standard 10 :=
  .seq (ram[ idx ← #0; one ← #1; four ← #4 ]) (.loop (.lt idx len) body)

/-- Initialize exactly `4N` cells from arbitrary old memory. -/
theorem exec {w : ℕ} (x : Data 10) (h4 : Fits w 4)
    (hfit : Fits w (x.regs dst + 4 * x.regs len)) :
    ∃ y, ExecWithin w program x y (12 * x.regs len + 5) ∧
      y.mem = memory x.mem (x.regs dst) (x.regs pad0) (x.regs pad1)
        (x.regs pad2) (x.regs pad3) (x.regs len) ∧
      ∀ i, i.val < 6 → y.regs i = x.regs i := by
  let I (y : Data 10) : Prop :=
    (∀ i, i.val < 6 → y.regs i = x.regs i) ∧ y.regs one = 1 ∧ y.regs four = 4 ∧
      y.regs idx ≤ x.regs len ∧ y.mem = memory x.mem (x.regs dst)
        (x.regs pad0) (x.regs pad1) (x.regs pad2) (x.regs pad3) (y.regs idx)
  have hbody (y : Data 10) (hy : I y) (hcond : (Cond.lt idx len).Holds y) :
      ∃ z, ExecWithin w body y z 10 ∧ I z ∧
        x.regs len - z.regs idx < x.regs len - y.regs idx := by
    obtain ⟨hr, h1, hfour, hi, hm⟩ := hy
    have hd := hr dst (by decide)
    have hl := hr len (by decide)
    have hp₀ := hr pad0 (by decide)
    have hp₁ := hr pad1 (by decide)
    have hp₂ := hr pad2 (by decide)
    have hp₃ := hr pad3 (by decide)
    have hlt : y.regs idx < x.regs len := by simpa only [Cond.holds_lt, hl] using hcond
    have fa : Fits w (4 * y.regs idx) := hfit.of_le (by omega)
    have fb : Fits w (x.regs dst + 4 * y.regs idx) := hfit.of_le (by omega)
    have fc : Fits w (x.regs dst + 4 * y.regs idx + 1) := hfit.of_le (by omega)
    have fd : Fits w (x.regs dst + 4 * y.regs idx + 1 + 1) := hfit.of_le (by omega)
    have fe : Fits w (x.regs dst + 4 * y.regs idx + 1 + 1 + 1) := hfit.of_le (by omega)
    have fi : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine ⟨?z, ?run, ?inv, ?decrease⟩
    case run => ram_eval [body, h1, hfour, hd, hp₀, hp₁, hp₂, hp₃, fa, fb, fc, fd, fe, fi]
    case inv =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro i hi
        have ha : i ≠ addr := by intro h; subst i; norm_num [addr] at hi
        have hn : i ≠ idx := by intro h; subst i; norm_num [idx] at hi
        simpa only [Data.set_regs, Data.write_regs, Function.update_of_ne ha,
          Function.update_of_ne hn] using hr i hi
      · simpa +decide [one, addr, idx] using h1
      · simpa +decide [four, addr, idx] using hfour
      · simpa only [Data.set_regs, Function.update_self, h1] using Nat.succ_le_of_lt hlt
      · simp only [Data.set_mem, Data.write_mem]
        rw [hm, ← memory_succ]
        rfl
    case decrease => simp only [Data.set_regs, Function.update_self]; omega
  let x₀ := ((x.set idx 0).set one 1).set four 4
  have hx₀ : I x₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      have hi₁ : i ≠ one := by intro h; subst i; norm_num [one] at hi
      have hi₄ : i ≠ four := by intro h; subst i; norm_num [four] at hi
      have hin : i ≠ idx := by intro h; subst i; norm_num [idx] at hi
      simp only [x₀, Data.set_regs, Function.update_of_ne hi₁,
        Function.update_of_ne hi₄, Function.update_of_ne hin]
    all_goals simp +decide [x₀, one, four, idx]
  obtain ⟨y, he, hy, hstop⟩ := ExecWithin.loop_invariant I
    (fun y => x.regs len - y.regs idx) hbody hx₀
  obtain ⟨hr, h1, hfour, hi, hm⟩ := hy
  have hl := hr len (by decide)
  have hend : y.regs idx = x.regs len := by
    simp only [Cond.holds_lt, hl] at hstop
    omega
  have hinit : ExecWithin (B := .standard) w (ram[ idx ← #0; one ← #1; four ← #4 ]) x x₀ 3 := by
    ram_eval [x₀, h4, h4.of_le (by decide : 1 ≤ 4)]
  refine ⟨y, ?_, by simpa only [hend] using hm, hr⟩
  convert hinit.seq he using 1
  · rfl
  · simp +decide only [x₀, idx, one, four, Data.set_regs, Function.update_apply,
      ↓reduceIte, Nat.sub_zero]
    omega

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Padding
