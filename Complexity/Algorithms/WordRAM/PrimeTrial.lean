/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Charged native trial division

This is a finite instruction program, not an invocation of Lean's primality decision procedure.
The Chan–He prime table will call it only on candidates at least two.

## Main definitions

* `PrimeTrial.program`: trial divisors from two up to the candidate.

## Main results

* `PrimeTrial.exec`: native trial division with an explicit linear instruction bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PrimeTrial

open Cslib.WordRAM

/-- Candidate, preserved. -/
abbrev arg : Fin 6 := 0
/-- Current trial divisor. -/
abbrev divisor : Fin 6 := 1
/-- Primality flag. -/
abbrev flag : Fin 6 := 2
/-- Remainder scratch. -/
abbrev remainder : Fin 6 := 3
/-- Constant one. -/
abbrev one : Fin 6 := 4
/-- Constant zero. -/
abbrev zero : Fin 6 := 5

/-- Test one trial divisor and advance. The conditional also charges its control instructions. -/
def body : Code .standard 6 := ram[
  remainder ← arg % divisor;
  if remainder = zero then [ flag ← zero ] else [ flag ← flag ];
  divisor ← divisor + one ]

/-- Initialize and test every divisor strictly between one and the candidate. -/
def program : Code .standard 6 :=
  .seq (ram[ divisor ← #2; flag ← #1; one ← #1; zero ← #0 ])
    (.loop (.lt divisor arg) body)

private def Good (p k : ℕ) : Prop := ∀ d, 2 ≤ d → d < k → p % d ≠ 0

private theorem good_succ (p k : ℕ) (hk : 2 ≤ k) :
    Good p (k + 1) ↔ Good p k ∧ p % k ≠ 0 := by
  constructor
  · intro h
    exact ⟨fun d hd hdk => h d hd (by omega), h k hk (by omega)⟩
  · rintro ⟨h, hmod⟩ d hd hdk
    by_cases hdk' : d = k
    · simpa only [hdk'] using hmod
    · exact h d hd (by omega)

/-- Test a candidate at least two in at most `7(p-2)+6` native instructions.
All divisors are actual register values; the native remainder instruction is charged. -/
theorem exec {w : ℕ} (x : Data 6) (hp : 2 ≤ x.regs arg)
    (hfit : Fits w (x.regs arg + 2)) :
    ∃ y, ExecWithin w program x y (7 * (x.regs arg - 2) + 6) ∧
      y.regs flag = (if (x.regs arg).Prime then 1 else 0) ∧
      y.regs arg = x.regs arg ∧ y.mem = x.mem := by
  classical
  let p := x.regs arg
  let I (y : Data 6) : Prop := y.regs arg = p ∧ y.regs one = 1 ∧ y.regs zero = 0 ∧
    2 ≤ y.regs divisor ∧ y.regs divisor ≤ p ∧
    y.regs flag = (if Good p (y.regs divisor) then 1 else 0) ∧ y.mem = x.mem
  have hbody (y : Data 6) (hy : I y) (hc : (Cond.lt divisor arg).Holds y) :
      ∃ z, ExecWithin w body y z 5 ∧ I z ∧ p - z.regs divisor < p - y.regs divisor := by
    obtain ⟨ha, ho, hz, hd, hdp, hf, hm⟩ := hy
    have hlt : y.regs divisor < p := by simpa only [Cond.holds_lt, ha] using hc
    have hmod : Fits w (p % y.regs divisor) := hfit.of_le (by
      have := Nat.mod_le p (y.regs divisor)
      change p % y.regs divisor ≤ p + 2
      omega)
    have hinc : Fits w (y.regs divisor + 1) := hfit.of_le (by change _ ≤ p + 2; omega)
    let z := ((y.set remainder (p % y.regs divisor)).set flag
      (if p % y.regs divisor = 0 then 0 else y.regs flag)).set divisor (y.regs divisor + 1)
    have he : ExecWithin w body y z 5 := by
      by_cases hrem : p % y.regs divisor = 0 <;>
        ram_eval [body, z, ha, ho, hz, hmod, hinc, hrem, arg, divisor, flag,
          remainder, one, zero, Fin.mk.injEq]
    have hflag : (if p % y.regs divisor = 0 then 0 else y.regs flag) =
        if Good p (y.regs divisor + 1) then 1 else 0 := by
      rw [hf]
      have hg := good_succ p (y.regs divisor) hd
      by_cases hrem : p % y.regs divisor = 0
      · have hg' : ¬Good p (y.regs divisor + 1) := fun h => (hg.mp h).2 hrem
        simp only [hrem, hg', ↓reduceIte]
      · have hg' : Good p (y.regs divisor + 1) ↔ Good p (y.regs divisor) := by tauto
        simp only [hrem, hg', ↓reduceIte]
    refine ⟨z, he, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa +decide [z, Function.update_apply, arg, divisor, flag, remainder] using ha
      · simpa +decide [z, Function.update_apply, one, divisor, flag, remainder] using ho
      · simpa +decide [z, Function.update_apply, zero, divisor, flag, remainder] using hz
      · simpa +decide [z, Function.update_apply, divisor] using
          (show 2 ≤ y.regs divisor + 1 by omega)
      · simpa +decide [z, Function.update_apply, divisor] using Nat.succ_le_of_lt hlt
      · simpa +decide [z, Function.update_apply, divisor, flag, remainder] using hflag
      · exact hm
    · change p - (y.regs divisor + 1) < p - y.regs divisor
      omega
  let x₀ := (((x.set divisor 2).set flag 1).set one 1).set zero 0
  have hx₀ : I x₀ := by
    have hgood : Good p 2 := by intro d hd hlt; omega
    simp +decide [I, x₀, p, arg, divisor, flag, one, zero, hgood, hp]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I (fun y => p - y.regs divisor) hbody hx₀
  obtain ⟨ha, ho, hz, hd, hdp, hf, hm⟩ := hy
  have hend : y.regs divisor = p := by simp only [Cond.holds_lt, ha] at hc; omega
  have hprime : Good p p ↔ p.Prime := by
    rw [Nat.prime_def_lt']
    constructor
    · intro h
      refine ⟨hp, fun d hd hdp hdiv => ?_⟩
      exact h d hd hdp (Nat.mod_eq_zero_of_dvd hdiv)
    · rintro ⟨_, h⟩ d hd hdp hzero
      exact h d hd hdp (Nat.dvd_of_mod_eq_zero hzero)
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have h2 : Fits w 2 := hfit.of_le (by omega)
  have hinit : ExecWithin (B := .standard) w
      (ram[ divisor ← #2; flag ← #1; one ← #1; zero ← #0 ]) x x₀ 4 := by
    ram_eval [x₀, h1, h2]
  refine ⟨y, ?_, by simpa only [hend, hprime] using hf, ha, hm⟩
  have hd₀ : x₀.regs divisor = 2 := rfl
  exact (hinit.seq he).mono (by rw [hd₀]; dsimp only [p]; omega)

end Cslib.Algorithms.WordRAM.PrimeTrial
