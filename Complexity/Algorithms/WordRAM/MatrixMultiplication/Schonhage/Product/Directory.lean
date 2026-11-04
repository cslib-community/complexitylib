/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Transfer

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
  let I (z : Data 160) : Prop := Parameters L m N Q z ∧ z.regs Reg.index ≤ H ∧
    (∀ j < z.regs Reg.index, z.mem (stampBase L m N Q + j) = 0) ∧
    (∀ a, a < stampBase L m N Q ∨ memoryEnd L m N Q ≤ a → z.mem a = x.mem a)
  let start := x.set Reg.index 0
  have hs : ExecWithin (B := .standard) w (ram[Reg.index ← #0]) x start 1 := by
    ram_eval [start]
  have sp : Parameters L m N Q start := hp.set_work Reg.index (by decide) _
  have hstart : I start := ⟨sp, by simp [start], by simp [start], by simp [start]⟩
  have hbody (z : Data 160) (hz : I z) (hc : (Cond.lt Reg.index Reg.leaves).Holds z) :
      ∃ u, ExecWithin w body z u 3 ∧ I u ∧ H - u.regs Reg.index < H - z.regs Reg.index := by
    have hi : z.regs Reg.index < H := by simpa only [Cond.holds_lt, hz.1.leaves, H] using hc
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
    refine ⟨u, he, ⟨up, by rw [hnext]; omega, ?_, ?_⟩, by rw [hnext]; omega⟩
    · intro j hj
      rw [hnext] at hj
      change Function.update z.mem (stampBase L m N Q + z.regs Reg.index) 0
        (stampBase L m N Q + j) = 0
      by_cases h : j = z.regs Reg.index
      · subst j
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne (by omega)]
        exact hz.2.2.1 j (by omega)
    · intro a ha
      change Function.update z.mem (stampBase L m N Q + z.regs Reg.index) 0 a = _
      rw [Function.update_of_ne (by
        unfold memoryEnd at ha
        dsimp only [H] at hi
        rcases ha with ha | ha <;> omega)]
      exact hz.2.2.2 a ha
  obtain ⟨y, he, hy, hc⟩ :=
    ExecWithin.loop_invariant I (fun z => H - z.regs Reg.index) hbody hstart
  have hn : y.regs Reg.index = H := by
    have hi := hy.2.1
    simp only [Cond.holds_lt, hy.1.leaves] at hc
    dsimp only [H] at hi ⊢
    omega
  let z := (y.set Reg.epoch 0).set Reg.index 0
  have hz : ExecWithin (B := .standard) w (ram[Reg.epoch ← #0; Reg.index ← #0]) y z 2 := by
    ram_eval [z]
  refine ⟨z, ?_, (hy.1.set_work Reg.epoch (by decide) _).set_work Reg.index (by decide) _,
    by simp [z, Reg.epoch, Reg.index], by simp [z], ?_, ?_⟩
  · apply (hs.seq (he.seq hz)).mono
    have hzero : start.regs Reg.index = 0 := by simp [start]
    rw [hzero, Nat.sub_zero]
    dsimp only [H]
    omega
  · simpa only [z, Data.set_mem, hn, H] using hy.2.2.1
  · simpa only [z, Data.set_mem] using hy.2.2.2

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
