/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Allocation

/-!
# Copying disjoint arrays on the word RAM

The seven-register copy routine charges every address calculation, load, store, increment,
and loop test. Its source precedes its destination, as in a bump-allocated growing array.
It is a fixed program: neither the length nor either address is baked into the code.

## Main definitions

* `Cslib.WordRAM.ArrayCopy.program`: copying between addresses supplied in registers.
* `Cslib.WordRAM.ArrayCopy.copyPrefix`: mathematical specification of the writes.

## Main results

* `Cslib.WordRAM.ArrayCopy.exec`: copying `n` words within `7 * n + 4` instructions,
  preserving the source and all cells outside the destination.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.ArrayCopy

/-- The memory after copying a prefix into a disjoint destination block. -/
def copyPrefix (mem : ℕ → ℕ) (src dst k : ℕ) : ℕ → ℕ :=
  fun a => if dst ≤ a ∧ a < dst + k then mem (src + (a - dst)) else mem a

@[simp]
theorem copyPrefix_zero (mem : ℕ → ℕ) (src dst : ℕ) : copyPrefix mem src dst 0 = mem := by
  funext a
  simp [copyPrefix]

theorem copyPrefix_read {mem : ℕ → ℕ} {src dst k j : ℕ} (hj : j < k) :
    copyPrefix mem src dst k (dst + j) = mem (src + j) := by
  simp [copyPrefix, hj]

theorem copyPrefix_outside {mem : ℕ → ℕ} {src dst k a : ℕ}
    (ha : ¬(dst ≤ a ∧ a < dst + k)) : copyPrefix mem src dst k a = mem a := by
  simp [copyPrefix, ha]

private theorem copyPrefix_succ (mem : ℕ → ℕ) (src dst k : ℕ) :
    copyPrefix mem src dst (k + 1) =
      Function.update (copyPrefix mem src dst k) (dst + k) (mem (src + k)) := by
  funext a
  by_cases ha : a = dst + k
  · subst a; simp [copyPrefix]
  · simp only [copyPrefix, Function.update_of_ne ha]
    have hiff : (dst ≤ a ∧ a < dst + (k + 1)) ↔ (dst ≤ a ∧ a < dst + k) := by omega
    simp only [hiff]

/-- Source base, destination base, length, index, temporary address, value, and one. -/
abbrev src : Fin 7 := 0
/-- Destination base. -/
abbrev dst : Fin 7 := 1
/-- Number of words. -/
abbrev len : Fin 7 := 2
/-- Loop index. -/
abbrev idx : Fin 7 := 3
/-- Temporary address. -/
abbrev addr : Fin 7 := 4
/-- Temporary value. -/
abbrev value : Fin 7 := 5
/-- Constant one. -/
abbrev one : Fin 7 := 6

/-- Five data instructions per copied word. -/
def body : Code .standard 7 := ram[
  addr ← src + idx; value ← *addr; addr ← dst + idx; *addr ← value; idx ← idx + one ]

/-- A fixed copying program with all three parameters in registers. -/
def program : Code .standard 7 := ram[ idx ← #0; one ← #1; while idx < len do [ ⟪body⟫ ] ]

/-- Low-level structured copying charges register setup and all loop instructions, excluding
the final halt. The one-past-end addresses must fit a word. Boundedness of the input memory and
registers is a separate premise when using `ExecWithin.bounded` to obtain bounded-word execution. -/
theorem exec {w : ℕ} (x : Data 7) (h1 : Fits w 1)
    (hs : Fits w (x.regs src + x.regs len))
    (hd : Fits w (x.regs dst + x.regs len))
    (hdisj : x.regs src + x.regs len ≤ x.regs dst) :
    ∃ y, ExecWithin w program x y (7 * x.regs len + 4) ∧
      y.mem = copyPrefix x.mem (x.regs src) (x.regs dst) (x.regs len) ∧
      y.regs src = x.regs src ∧ y.regs dst = x.regs dst ∧ y.regs len = x.regs len := by
  let I (y : Data 7) : Prop :=
    y.regs src = x.regs src ∧ y.regs dst = x.regs dst ∧ y.regs len = x.regs len ∧
    y.regs one = 1 ∧ y.regs idx ≤ x.regs len ∧
    y.mem = copyPrefix x.mem (x.regs src) (x.regs dst) (y.regs idx)
  have hbody (y : Data 7) (hy : I y) (hc : (Cond.lt idx len).Holds y) :
      ∃ z, ExecWithin w body y z 5 ∧ I z ∧
        x.regs len - z.regs idx < x.regs len - y.regs idx := by
    obtain ⟨hys, hyd, hyl, hyo, hyi, hym⟩ := hy
    have hi : y.regs idx < x.regs len := by simpa [hyl] using hc
    have hsrc : Fits w (y.regs src + y.regs idx) := by
      rw [hys]; exact hs.of_le (by omega)
    have hdst : Fits w (y.regs dst + y.regs idx) := by
      rw [hyd]; exact hd.of_le (by omega)
    have hinc : Fits w (y.regs idx + 1) := hs.of_le (by omega)
    have hread : y.mem (y.regs src + y.regs idx) = x.mem (x.regs src + y.regs idx) := by
      rw [hym, hys]
      apply copyPrefix_outside
      omega
    refine ⟨?z, ?run, ?inv, ?decrease⟩
    case run => ram_eval [body, hsrc, hdst, hinc, hyo]
    case inv =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa +decide [Function.update_apply] using hys
      · simpa +decide [Function.update_apply] using hyd
      · simpa +decide [Function.update_apply] using hyl
      · simpa +decide [Function.update_apply] using hyo
      · simpa [hyo] using (Nat.succ_le_of_lt hi)
      · simp only [Data.set_mem, Data.write_mem, Data.set_regs, Function.update_apply]
        rw [hread, hym, hyd, ← copyPrefix_succ]
        rfl
    case decrease => simp only [Data.set_regs, Function.update_self]; omega
  let x₀ := (x.set idx 0).set one 1
  have hx₀ : I x₀ := by simp +decide [I, x₀]
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun y => x.regs len - y.regs idx) hbody hx₀
  obtain ⟨hys, hyd, hyl, hyo, hyi, hym⟩ := hy
  have hend : y.regs idx = x.regs len := by
    simp only [Cond.holds_lt, hyl] at hc
    omega
  refine ⟨y, ?_, ?_, hys, hyd, hyl⟩
  · have hinit := (ExecWithin.const (d := idx) (x := x) (fits_zero w)).seq
      ((ExecWithin.const (d := one) h1).seq he)
    convert hinit using 1
    · rfl
    · simp +decide only [x₀, Data.set_regs, Function.update_apply, ↓reduceIte,
        Nat.sub_zero]
      omega
  · simpa [hend] using hym

end Cslib.WordRAM.ArrayCopy

end
