/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Transfer

import Complexity.Computability.WordRAM.CountingLoop

/-!
# One charged timestamp initialization for all product tiles

## Main results

* `QueriedProduct.exec_initializeDirectory`: clear the actual shared directory once and set
  the initial epoch and tile index, with a complete outside frame.

Subsequent kernel calls propagate their returned epoch. This initialization is not repeated
per tile or request.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM

/-- Actual directory stores and loop control, followed by the epoch/index setup. -/
public theorem exec_initializeDirectory {w L m N Q : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x) (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w initializeDirectory x y (5 * 10 ^ L + 5) ∧
      Parameters L m N Q y ∧ y.regs Reg.epoch = 0 ∧ y.regs Reg.index = 0 ∧
      (∀ j < 10 ^ L, y.mem (stampBase L m N Q + j) = 0) ∧
      (∀ a, a < stampBase L m N Q ∨ memoryEnd L m N Q ≤ a → y.mem a = x.mem a) := by
  let H := 10 ^ L
  let body : Code .standard 160 := ram[
    Reg.address ← Reg.stamps + Reg.index; *Reg.address ← Reg.zero; Reg.index ← Reg.index + Reg.one ]
  let P (k : ℕ) (z : Data 160) : Prop := Parameters L m N Q z ∧
    (∀ j < k, z.mem (stampBase L m N Q + j) = 0) ∧
    (∀ a, a < stampBase L m N Q ∨ memoryEnd L m N Q ≤ a → z.mem a = x.mem a)
  let start := x.set Reg.index 0
  have hs : ExecWithin (B := .standard) w (ram[Reg.index ← #0]) x start 1 := by
    ram_eval [start]
  have sp : Parameters L m N Q start := hp.set_work Reg.index (by decide) _
  have hstart : P (start.regs Reg.index) start := ⟨sp, by simp [start], by simp [start]⟩
  have hbody (z : Data 160) (hz : P (z.regs Reg.index) z) (hi : z.regs Reg.index < H) :
      ∃ u, ExecWithin w body z u 3 ∧ P (z.regs Reg.index + 1) u ∧
        u.regs Reg.index = z.regs Reg.index + 1 := by
    have ha : Fits w (stampBase L m N Q + z.regs Reg.index) := allocated_fits hfit (by
      unfold memoryEnd
      dsimp only [H] at hi
      omega)
    have hn : Fits w (z.regs Reg.index + 1) := allocated_fits hfit (by
      unfold memoryEnd
      dsimp only [H] at hi
      omega)
    let u := ((z.set Reg.address (stampBase L m N Q + z.regs Reg.index)).write
      (stampBase L m N Q + z.regs Reg.index) 0).set Reg.index (z.regs Reg.index + 1)
    have he : ExecWithin w body z u 3 := by
      ram_eval [body, u, hz.1.stamps, hz.1.zero, hz.1.one, ha, hn,
        Reg.address, Reg.stamps, Reg.index, Reg.zero, Reg.one]
    have up : Parameters L m N Q u :=
      ((hz.1.set_work Reg.address (by decide) _).write _ _).set_work Reg.index (by decide) _
    have hnext : u.regs Reg.index = z.regs Reg.index + 1 := by simp [u]
    refine ⟨u, he, ⟨up, ?_, ?_⟩, hnext⟩
    · intro j hj
      change Function.update z.mem (stampBase L m N Q + z.regs Reg.index) 0
        (stampBase L m N Q + j) = 0
      by_cases h : j = z.regs Reg.index
      · subst j
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne (by omega)]
        exact hz.2.1 j (by omega)
    · intro a ha
      change Function.update z.mem (stampBase L m N Q + z.regs Reg.index) 0 a = _
      rw [Function.update_of_ne (by
        unfold memoryEnd at ha
        dsimp only [H] at hi
        rcases ha with ha | ha <;> omega)]
      exact hz.2.2 a ha
  obtain ⟨y, he, hy, _⟩ := ExecWithin.loop_count P (fun _ hy => hy.1.leaves)
    hbody (by simp [start]) hstart
  let z := (y.set Reg.epoch 0).set Reg.index 0
  have hz : ExecWithin (B := .standard) w (ram[Reg.epoch ← #0; Reg.index ← #0]) y z 2 := by
    ram_eval [z]
  refine ⟨z, ?_, (hy.1.set_work Reg.epoch (by decide) _).set_work Reg.index (by decide) _,
    by simp [z, Reg.epoch, Reg.index], by simp [z], ?_, ?_⟩
  · apply (hs.seq (he.seq hz)).mono
    have hzero : start.regs Reg.index = 0 := by simp [start]
    rw [hzero, Nat.sub_zero]
    omega
  · simpa only [z, Data.set_mem, H] using hy.2.1
  · simpa only [z, Data.set_mem] using hy.2.2

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
