/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Copy
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

import CslibFrontier.Computability.WordRAM.CountingLoop

/-!
# Copying an array while accumulating its original words

The fixed eight-register program performs the same forward stores as `ArrayCopy.program`,
with one additional addition per word. The running sum can carry across successive arrays.
Its sum is computed by the program, rather than supplied as an input magnitude certificate.
All memory outside the destination remains unchanged, including dirty caller memory.
-/

public section

namespace Cslib.WordRAM.ArrayCopySum

namespace Reg

/-- Source pointer. -/
abbrev src : Fin 8 := 0
/-- Destination pointer. -/
abbrev dst : Fin 8 := 1
/-- Number of words. -/
abbrev len : Fin 8 := 2
/-- Current offset. -/
abbrev idx : Fin 8 := 3
/-- Address temporary. -/
abbrev addr : Fin 8 := 4
/-- Loaded original word. -/
abbrev value : Fin 8 := 5
/-- Constant one. -/
abbrev one : Fin 8 := 6
/-- Accumulator, supplied and returned in the same register. -/
abbrev total : Fin 8 := 7

end Reg

open Reg

/-- The mathematical sum of the original source span. -/
@[expose] def wordSum (mem : ℕ → ℕ) (base length : ℕ) : ℕ :=
  ∑ j ∈ Finset.range length, mem (base + j)

/-- One actual copy and accumulation, including both address computations. -/
@[expose] def body : Code .standard 8 := ram[
  addr ← src + idx; value ← *addr; addr ← dst + idx; *addr ← value;
  total ← total + value; idx ← idx + one ]

/-- Copy and sum a runtime span, retaining the old accumulator for zero-length spans. -/
@[expose] def program : Code .standard 8 :=
  ram[ idx ← #0; one ← #1; while idx < len do [ ⟪body⟫ ] ]

/-- Copied destination, retained span arguments and the accumulated sum of the original source. -/
structure Post {r : ℕ} (f : Fin 8 → Fin r) (x y : Data r) : Prop where
  /-- The destination contains the original source prefix. -/
  memory : y.mem = ArrayCopy.copyPrefix x.mem (x.regs (f Reg.src))
    (x.regs (f Reg.dst)) (x.regs (f Reg.len))
  /-- The source pointer survives the loop. -/
  src : y.regs (f Reg.src) = x.regs (f Reg.src)
  /-- The destination pointer survives the loop. -/
  dst : y.regs (f Reg.dst) = x.regs (f Reg.dst)
  /-- The original span length survives the loop. -/
  len : y.regs (f Reg.len) = x.regs (f Reg.len)
  /-- The accumulator adds precisely the original source words. -/
  total : y.regs (f Reg.total) = x.regs (f Reg.total) +
    wordSum x.mem (x.regs (f Reg.src)) (x.regs (f Reg.len))

/-- Read a native postcondition through the caller's selected registers. -/
theorem Post.of_comap {r : ℕ} {f : Fin 8 → Fin r} {x y : Data r}
    (post : Post id (x.comap f) (y.comap f)) : Post f x y :=
  ⟨post.memory, post.src, post.dst, post.len, post.total⟩

/-- Copy a separated source span and accumulate its original words. Every loop test, load,
store and sum is charged; only actual source/destination and total-sum numerical fits are
premises. This does not require a clean destination. -/
theorem exec {w : ℕ} (x : Data 8) (h1 : Fits w 1)
    (hs : Fits w (x.regs src + x.regs len))
    (hd : Fits w (x.regs dst + x.regs len))
    (ht : Fits w (x.regs total + wordSum x.mem (x.regs src) (x.regs len)))
    (hsep : x.regs src + x.regs len ≤ x.regs dst) :
    ∃ y, ExecWithin w program x y (8 * x.regs len + 4) ∧ Post id x y := by
  let P (j : ℕ) (y : Data 8) : Prop :=
    y.regs src = x.regs src ∧ y.regs dst = x.regs dst ∧ y.regs len = x.regs len ∧
    y.regs one = 1 ∧
    y.mem = ArrayCopy.copyPrefix x.mem (x.regs src) (x.regs dst) j ∧
    y.regs total = x.regs total + wordSum x.mem (x.regs src) j
  have hbody (y : Data 8) (hy : P (y.regs idx) y) (hi : y.regs idx < x.regs len) :
      ∃ z, ExecWithin w body y z 6 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hys, hyd, hyl, hyo, hym, hyt⟩ := hy
    have hsrc : Fits w (y.regs src + y.regs idx) := by
      rw [hys]; exact hs.of_le (by omega)
    have hdst : Fits w (y.regs dst + y.regs idx) := by
      rw [hyd]; exact hd.of_le (by omega)
    have hinc : Fits w (y.regs idx + 1) := hs.of_le (by omega)
    have hread : y.mem (y.regs src + y.regs idx) = x.mem (x.regs src + y.regs idx) := by
      rw [hym, hys]
      exact ArrayCopy.copyPrefix_outside (by omega)
    have hsum : Fits w (y.regs total + y.mem (y.regs src + y.regs idx)) := by
      rw [hyt, hread]
      have hle : wordSum x.mem (x.regs src) (y.regs idx + 1) ≤
          wordSum x.mem (x.regs src) (x.regs len) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun _ _ _ => Nat.zero_le _)
      apply ht.of_le
      simpa only [wordSum, Finset.sum_range_succ, Nat.add_assoc] using
        Nat.add_le_add_left hle (x.regs total)
    refine ⟨?z, ?run, ?inv, ?increment⟩
    case run => ram_eval [body, hsrc, hdst, hinc, hsum, hyo]
    case inv =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa +decide [Function.update_apply] using hys
      · simpa +decide [Function.update_apply] using hyd
      · simpa +decide [Function.update_apply] using hyl
      · simpa +decide [Function.update_apply] using hyo
      · simp only [Data.set_mem, Data.write_mem]
        rw [hread, hym, hyd, ← ArrayCopy.copyPrefix_succ]
      · simp only [Data.set_regs, Function.update_apply]
        simp only [show (total : Fin 8) ≠ idx by decide, ↓reduceIte]
        rw [hyt, hread]
        simp only [wordSum, Finset.sum_range_succ, Nat.add_assoc]
    case increment => rfl
  let x₀ := (x.set idx 0).set one 1
  have hx₀ : P (x₀.regs idx) x₀ := by simp +decide [P, x₀, wordSum]
  obtain ⟨y, he, ⟨hys, hyd, hyl, hyo, hym, hyt⟩, _⟩ := ExecWithin.loop_count P
    (fun y hy => hy.2.2.1) hbody (by simp +decide [x₀, idx, one]) hx₀
  refine ⟨y, ?_, by simpa only [id] using hym, hys, hyd, hyl,
    by simpa only [id] using hyt⟩
  have hinit := (ExecWithin.const (d := idx) (x := x) (fits_zero w)).seq
    ((ExecWithin.const (d := one) h1).seq he)
  convert hinit using 1
  · rfl
  · simp +decide only [x₀, Data.set_regs, Function.update_apply, ↓reduceIte, Nat.sub_zero]
    omega

end Cslib.WordRAM.ArrayCopySum
