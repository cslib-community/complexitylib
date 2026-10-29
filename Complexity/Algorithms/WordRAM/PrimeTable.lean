/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.PrimeTrial
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Native prime tables

This fixed program tests every candidate through the supplied bound, writes its primality
bit, and counts the primes. Trial division, table addresses, writes and loops are charged.
There is no primality oracle or assumed sieve.

## Main definitions

* `PrimeTable.program`: the complete native table builder.
* `PrimeTable.memory`: its output bitmap and memory frame.

## Main results

* `PrimeTable.exec`: exact bitmap and prime count in an explicit quadratic instruction bound.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PrimeTable

open Cslib.WordRAM
open Finset

/-- Registers of the trial-division subroutine. -/
def trialRegisters (i : Fin 6) : Fin 15 := ⟨i.val, by omega⟩

private theorem trial_injective : Function.Injective trialRegisters := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 15 => i.val) h

/-- Current trial-division candidate. -/
abbrev arg : Fin 15 := 0
/-- Current candidate's primality bit. -/
abbrev flag : Fin 15 := 2
/-- Largest candidate. -/
abbrev limit : Fin 15 := 6
/-- Output bitmap base. -/
abbrev base : Fin 15 := 7
/-- First candidate not yet written. -/
abbrev cursor : Fin 15 := 8
/-- Address scratch. -/
abbrev addr : Fin 15 := 9
/-- Number of primes written. -/
abbrev count : Fin 15 := 10
/-- One past the largest candidate. -/
abbrev stop : Fin 15 := 11
/-- Constant one. -/
abbrev one : Fin 15 := 12
/-- Constant zero. -/
abbrev zero : Fin 15 := 13
/-- Constant two. -/
abbrev two : Fin 15 := 14

/-- Handle zero and one directly; test all larger candidates by charged native trial division. -/
def test : Code .standard 15 :=
  .branch (.lt cursor two) (ram[ flag ← #0 ])
    (.seq (ram[ arg ← cursor ]) (PrimeTrial.program.rename trialRegisters))

/-- Test, write the bit, update the count, and advance the candidate. -/
def body : Code .standard 15 :=
  .seq test (ram[ addr ← base + cursor; *addr ← flag;
    count ← count + flag; cursor ← cursor + one ])

/-- A finite native prime-table program with its bound and base supplied in registers. -/
def program : Code .standard 15 :=
  .seq (ram[ one ← #1; zero ← #0; two ← #2; cursor ← #0; count ← #0;
    stop ← limit + one ]) (.loop (.lt cursor stop) body)

/-- The first `k` primality bits, preserving all other memory cells. -/
def memory (mem : ℕ → ℕ) (base k : ℕ) : ℕ → ℕ :=
  fun a => if base ≤ a ∧ a < base + k then if (a - base).Prime then 1 else 0 else mem a

private theorem memory_zero (mem : ℕ → ℕ) (base : ℕ) : memory mem base 0 = mem := by
  funext a
  simp [memory]

private theorem memory_succ (mem : ℕ → ℕ) (base k : ℕ) :
    memory mem base (k + 1) = Function.update (memory mem base k)
      (base + k) (if k.Prime then 1 else 0) := by
  funext a
  by_cases ha : a = base + k
  · subst a
    simp [memory]
  · rw [Function.update_of_ne ha]
    have h : (base ≤ a ∧ a < base + (k + 1)) ↔ (base ≤ a ∧ a < base + k) := by omega
    simp only [memory, h]

private theorem exec_test {w m : ℕ} (x : Data 15) (htwo : x.regs two = 2)
    (hbound : x.regs cursor ≤ m) (hfit : Fits w (m + 3)) :
    ∃ y, ExecWithin w test x y (7 * m + 9) ∧
      y.regs flag = (if (x.regs cursor).Prime then 1 else 0) ∧ y.mem = x.mem ∧
      ∀ i, 6 ≤ i.val → y.regs i = x.regs i := by
  by_cases hp : x.regs cursor < 2
  · have hnp : ¬(x.regs cursor).Prime := fun h => by have := h.two_le; omega
    refine ⟨x.set flag 0, ?_, by simp [hnp], rfl, ?_⟩
    · exact (ExecWithin.branch_pos (by simpa only [Cond.holds_lt, htwo] using hp)
        (ExecWithin.const (fits_zero w))).mono (by omega)
    · intro i hi
      have hne : i ≠ flag := by intro h; subst i; change 6 ≤ 2 at hi; omega
      simp only [Data.set_regs, Function.update_of_ne hne]
  · let p := x.set arg (x.regs cursor)
    have hcopy : ExecWithin (B := .standard) w (ram[ arg ← cursor ]) x p 1 :=
      ExecWithin.copy
    obtain ⟨a, ha, haf, haa, ham⟩ := PrimeTrial.exec (p.comap trialRegisters)
      (by change 2 ≤ x.regs cursor; omega)
      (hfit.of_le (by change x.regs cursor + 2 ≤ m + 3; omega))
    let y := a.extend trialRegisters p
    have hf : y.regs flag = a.regs PrimeTrial.flag := by
      change Function.extend trialRegisters a.regs p.regs (trialRegisters PrimeTrial.flag) = _
      exact trial_injective.extend_apply _ _ _
    refine ⟨y, ?_, hf.trans haf, ham, ?_⟩
    · exact (ExecWithin.branch_neg (by simpa only [Cond.holds_lt, htwo] using hp)
        (hcopy.seq (ha.rename trial_injective))).mono (by
          change 1 + (7 * (x.regs cursor - 2) + 6) + 2 ≤ 7 * m + 9
          omega)
    · intro i hi
      change Function.extend trialRegisters a.regs p.regs i = x.regs i
      rw [Function.extend_apply']
      · have hne : i ≠ arg := by intro h; subst i; change 6 ≤ 0 at hi; omega
        exact Function.update_of_ne hne _ _
      · rintro ⟨j, hj⟩
        have := congrArg Fin.val hj
        dsimp [trialRegisters] at this
        omega


/-- Write every primality bit through `m`, count exactly `Nat.primesLE m`, and preserve
all cells outside the bitmap. Trial division gives the explicit quadratic bound
`(m+1)(7m+15)+8`; the final halt is excluded. -/
theorem exec {w : ℕ} (x : Data 15)
    (hfit : Fits w (x.regs limit + 3))
    (haddr : Fits w (x.regs base + (x.regs limit + 1))) :
    ∃ y, ExecWithin w program x y ((x.regs limit + 1) * (7 * x.regs limit + 15) + 8) ∧
      y.mem = memory x.mem (x.regs base) (x.regs limit + 1) ∧
      y.regs count = #(Nat.primesLE (x.regs limit)) ∧
      y.regs limit = x.regs limit ∧ y.regs base = x.regs base := by
  let m := x.regs limit
  let I (y : Data 15) : Prop := y.regs limit = m ∧ y.regs base = x.regs base ∧
    y.regs stop = m + 1 ∧ y.regs one = 1 ∧ y.regs zero = 0 ∧ y.regs two = 2 ∧
    y.regs cursor ≤ m + 1 ∧ y.regs count = Nat.primeCounting' (y.regs cursor) ∧
    y.mem = memory x.mem (x.regs base) (y.regs cursor)
  have hbody (y : Data 15) (hy : I y) (hc : (Cond.lt cursor stop).Holds y) :
      ∃ q, ExecWithin w body y q (7 * m + 13) ∧ I q ∧
        m + 1 - q.regs cursor < m + 1 - y.regs cursor := by
    obtain ⟨hl, hb, hs, ho, hz, ht, hi, hcount, hm⟩ := hy
    have hlt : y.regs cursor < m + 1 := by simpa only [Cond.holds_lt, hs] using hc
    obtain ⟨z, he, hzf, hzm, hzr⟩ := exec_test y ht (show y.regs cursor ≤ m by omega) hfit
    have hzb : z.regs base = x.regs base := (hzr base (by decide)).trans hb
    have hzi : z.regs cursor = y.regs cursor := hzr cursor (by decide)
    have hzc : z.regs count = Nat.primeCounting' (y.regs cursor) :=
      (hzr count (by decide)).trans hcount
    have hzo : z.regs one = 1 := (hzr one (by decide)).trans ho
    have hzf_le : z.regs flag ≤ 1 := by rw [hzf]; split_ifs <;> omega
    have ha : Fits w (z.regs base + z.regs cursor) := haddr.of_le (by rw [hzb, hzi]; omega)
    have hn : Fits w (z.regs cursor + 1) := hfit.of_le (by rw [hzi]; change _ ≤ m + 3; omega)
    have hct : Fits w (z.regs count + z.regs flag) := hfit.of_le (by
      rw [hzc]
      have hle : Nat.primeCounting' (y.regs cursor) ≤ y.regs cursor :=
        Nat.count_le Nat.Prime
      change _ ≤ m + 3
      omega)
    refine ⟨?q, ?run, ?inv, ?decrease⟩
    case run =>
      have htail : ExecWithin w (ram[ addr ← base + cursor; *addr ← flag;
          count ← count + flag; cursor ← cursor + one ]) z ?q 4 := by
        ram_eval [ha, hn, hct, hzo]
      exact (he.seq htail).mono (by omega)
    case inv =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa +decide [Function.update_apply] using (hzr limit (by decide)).trans hl
      · simpa +decide [Function.update_apply] using hzb
      · simpa +decide [Function.update_apply] using (hzr stop (by decide)).trans hs
      · simpa +decide [Function.update_apply] using hzo
      · simpa +decide [Function.update_apply] using (hzr zero (by decide)).trans hz
      · simpa +decide [Function.update_apply] using (hzr two (by decide)).trans ht
      · simpa +decide [Function.update_apply, hzi] using Nat.succ_le_of_lt hlt
      · change z.regs count + z.regs flag = Nat.primeCounting' (z.regs cursor + 1)
        rw [hzc, hzf, hzi]
        simp only [Nat.primeCounting', Nat.count_succ]
      · change Function.update z.mem (z.regs base + z.regs cursor) (z.regs flag) =
          memory x.mem (x.regs base) (z.regs cursor + 1)
        rw [hzm, hm, hzb, hzi, hzf, ← memory_succ]
    case decrease =>
      change m + 1 - (z.regs cursor + 1) < m + 1 - y.regs cursor
      rw [hzi]
      omega
  let x₀ := (((((x.set one 1).set zero 0).set two 2).set cursor 0).set count 0).set stop (m + 1)
  have hx₀ : I x₀ := by
    simp +decide [I, x₀, m, limit, base, stop, one, zero, two, cursor, count,
      Nat.primeCounting', Nat.count_zero, memory_zero]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => m + 1 - y.regs cursor) hbody hx₀
  obtain ⟨hl, hb, hs, ho, hz, ht, hi, hcount, hm⟩ := hy
  have hend : y.regs cursor = m + 1 := by
    simp only [Cond.holds_lt, hs] at hc
    omega
  have h1 : Fits w 1 := hfit.of_le (by omega)
  have h2 : Fits w 2 := hfit.of_le (by omega)
  have hstop : Fits w (x.regs limit + 1) := hfit.of_le (by omega)
  have hinit : ExecWithin (B := .standard) w
      (ram[ one ← #1; zero ← #0; two ← #2; cursor ← #0; count ← #0;
        stop ← limit + one ]) x x₀ 6 := by
    ram_eval [x₀, m, h1, h2, hstop, limit, base, stop, one, zero, two, cursor, count, Fin.mk.injEq]
  refine ⟨y, ?_, by simpa only [hend] using hm, ?_, hl, hb⟩
  · have hi₀ : x₀.regs cursor = 0 := rfl
    have hcost : 7 * m + 13 + 2 = 7 * m + 15 := by omega
    exact (hinit.seq he).mono (by rw [hi₀, Nat.sub_zero, hcost]; dsimp only [m]; omega)
  · rw [hcount, hend, Nat.primesLE_card_eq_primeCounting, Nat.primeCounting]

end Cslib.Algorithms.WordRAM.PrimeTable
