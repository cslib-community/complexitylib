/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.Setup

/-!
# One native tile-prefix update

## Main results

* `Wanted.exec_prefixStep`: load the actual bucket count, store its immutable start and
  mutable cursor, and advance the running sum with every instruction charged.

This stage lemma is an internal implementation API for the complete grouping execution.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- One actual prefix update; the two stored cells are the only possible memory changes. -/
theorem exec_prefixStep {w L m N Q t : ℕ} (key : ℕ → ℕ)
    (ht : t < numBands L m N ^ 2) (x : Data 96) (hx : Parameters L m N Q x)
    (hi : x.regs index = t) (hs : x.regs total = Nat.count (fun k => key k < t) Q)
    (hc : x.mem (countAddress L Q + t) = Nat.count (fun k => key k = t) Q)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w prefixStep x y 8 ∧ Parameters L m N Q y ∧
      y.regs index = t + 1 ∧ y.regs total = Nat.count (fun k => key k < (t + 1)) Q ∧
      y.mem (offsetAddress L m N Q + t) = Nat.count (fun k => key k < t) Q ∧
      y.mem (cursorAddressBase L m N Q + t) = Nat.count (fun k => key k < t) Q ∧
      (∀ a, a ≠ offsetAddress L m N Q + t → a ≠ cursorAddressBase L m N Q + t →
        y.mem a = x.mem a) := by
  have hl := local_fits hfit
  have hend := memoryLimit_eq L m N Q
  have h10 := Nat.zero_le (10 ^ L)
  have hf (v : ℕ) (hv : v ≤ memoryLimit L m N Q) : Fits w v := hl.of_le (by omega)
  have hcount : Fits w (countAddress L Q + t) := hf _ (by
    unfold countAddress tableAddress inputLimit
    omega)
  have hoff : Fits w (offsetAddress L m N Q + t) := hf _ (by
    unfold offsetAddress countAddress tableAddress inputLimit
    omega)
  have hcursor : Fits w (cursorAddressBase L m N Q + t) := hf _ (by
    unfold cursorAddressBase offsetAddress countAddress tableAddress inputLimit
    omega)
  have hadd : Fits w (Nat.count (fun k => key k < t) Q + Nat.count (fun k => key k = t) Q) :=
    hf _ (by
    rw [← CountingSort.count_lt_succ]
    have := Nat.count_le (fun i => key i < t + 1) (n := Q)
    omega)
  have hnext : Fits w (t + 1) := hf _ (by omega)
  let s := Nat.count (fun k => key k < t) Q
  let c := Nat.count (fun k => key k = t) Q
  let y := ((((((((x.set pointer (countAddress L Q + t)).set count c).set
    pointer (offsetAddress L m N Q + t)).write (offsetAddress L m N Q + t) s).set
    pointer (cursorAddressBase L m N Q + t)).write (cursorAddressBase L m N Q + t) s).set
    total (s + c)).set index (t + 1))
  have he : ExecWithin w prefixStep x y 8 := by
    ram_eval [prefixStep, y, hx.counts, hx.offsets, hx.cursors, hx.tables.one,
      hi, hs, hc, hcount, hoff, hcursor, hadd, hnext, s, c,
      pointer, count, counts, offsets, cursors, total, index, BandPreparation.one,
      Fin.mk.injEq]
  have hp : Parameters L m N Q y := hx.reframe (by
    intro i hi
    apply he.regs_eq
    have h : ∀ i ∈ parameterRegisters, prefixStep.Preserves i := by decide +kernel
    exact h i hi)
  have hsep : offsetAddress L m N Q + t ≠ cursorAddressBase L m N Q + t := by
    unfold cursorAddressBase
    omega
  refine ⟨y, he, hp, by simp [y, index], ?_, ?_, ?_, ?_⟩
  · simpa only [y, Data.set_regs, Data.write_regs, total, index,
      Function.update_of_ne (by decide : (30 : Fin 96) ≠ 23), Function.update_self,
      s, c] using (CountingSort.count_lt_succ key Q t).symm
  · change Function.update (Function.update x.mem (offsetAddress L m N Q + t) s)
      (cursorAddressBase L m N Q + t) s (offsetAddress L m N Q + t) = s
    rw [Function.update_of_ne hsep, Function.update_self]
  · exact Function.update_self _ _ _
  · intro a ho hc
    change Function.update (Function.update x.mem (offsetAddress L m N Q + t) s)
      (cursorAddressBase L m N Q + t) s a = x.mem a
    rw [Function.update_of_ne hc, Function.update_of_ne ho]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
