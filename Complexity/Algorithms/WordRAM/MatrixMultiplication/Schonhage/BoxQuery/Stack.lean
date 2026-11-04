/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Program

/-!
# Actual five-word query-stack operations

Every pushed task writes all five words before a pop can read them. The caller may
start with dirty stack memory. These execution lemmas charge the address arithmetic,
stores, loads and top update, and preserve all other memory and registers.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM

/-- The five actual stores performed when appending one native task. -/
@[expose] def writeTask (F n k c u e p : ℕ) (μ : ℕ → ℕ) : ℕ → ℕ :=
  let a := F + n * 5
  Function.update (Function.update (Function.update (Function.update
    (Function.update μ a k) (a + 1) c) (a + 2) u) (a + 3) e) (a + 4) p

/-- The new task's descriptor is exactly the five words supplied by the computed child. -/
theorem writeTask_read (F n k c u e p : ℕ) (μ : ℕ → ℕ) :
    writeTask F n k c u e p μ (F + n * 5) = k ∧
    writeTask F n k c u e p μ (F + n * 5 + 1) = c ∧
    writeTask F n k c u e p μ (F + n * 5 + 2) = u ∧
    writeTask F n k c u e p μ (F + n * 5 + 3) = e ∧
    writeTask F n k c u e p μ (F + n * 5 + 4) = p := by
  simp [writeTask]

/-- All words outside the newly appended five-word record retain their old contents. -/
theorem writeTask_frame (F n k c u e p : ℕ) (μ : ℕ → ℕ) (q : ℕ)
    (hq : ¬(F + n * 5 ≤ q ∧ q < F + n * 5 + 5)) :
    writeTask F n k c u e p μ q = μ q := by
  simp only [writeTask]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega)]

/-- Registers modified by one real task push. -/
@[expose] def PushLocal (i : Fin registers) : Prop := i = Reg.cursor ∨ i = Reg.top

instance (i : Fin registers) : Decidable (PushLocal i) :=
  inferInstanceAs (Decidable (i = Reg.cursor ∨ i = Reg.top))

private theorem push_preserves (i : Fin registers) : ¬PushLocal i → push.Preserves i :=
  by decide +revert

/-- Store and append one complete task within twelve native instructions. -/
theorem exec_push {w F n k c u e p : ℕ} (x : Data registers)
    (hF : x.regs Reg.stack = F) (hn : x.regs Reg.top = n)
    (hk : x.regs Reg.depth = k) (hc : x.regs Reg.childCode = c)
    (hu : x.regs Reg.childUsed = u) (he : x.regs Reg.childStars = e)
    (hp : x.regs Reg.childPower = p) (h5 : x.regs Reg.five = 5)
    (h1 : x.regs BoxTable.Reg.one = 1) (hfit : Fits w (F + 5 * (n + 1) + 8)) :
    ∃ y, ExecWithin w push x y 12 ∧ y.regs Reg.top = n + 1 ∧
      y.mem = writeTask F n k c u e p x.mem ∧
      (∀ i, ¬PushLocal i → y.regs i = x.regs i) := by
  let a := F + n * 5
  have hfn : Fits w (n * 5) := hfit.of_le (by omega)
  have hfa : Fits w a := hfit.of_le (by dsimp only [a]; omega)
  have hf1 : Fits w (a + 1) := hfit.of_le (by dsimp only [a]; omega)
  have hf2 : Fits w (a + 1 + 1) := hfit.of_le (by dsimp only [a]; omega)
  have hf3 : Fits w (a + 1 + 1 + 1) := hfit.of_le (by dsimp only [a]; omega)
  have hf4 : Fits w (a + 1 + 1 + 1 + 1) := hfit.of_le (by dsimp only [a]; omega)
  have hfnext : Fits w (n + 1) := hfit.of_le (by omega)
  let z0 := (x.set Reg.cursor (n * 5)).set Reg.cursor a
  let z1 := (z0.write a k).set Reg.cursor (a + 1)
  let z2 := (z1.write (a + 1) c).set Reg.cursor (a + 1 + 1)
  let z3 := (z2.write (a + 1 + 1) u).set Reg.cursor (a + 1 + 1 + 1)
  let z4 := (z3.write (a + 1 + 1 + 1) e).set Reg.cursor (a + 1 + 1 + 1 + 1)
  let y := (z4.write (a + 1 + 1 + 1 + 1) p).set Reg.top (n + 1)
  have hy : ExecWithin w push x y 12 := by
    ram_eval [push, y, z4, z3, z2, z1, z0, a, hF, hn, hk, hc, hu, he, hp,
      h5, h1, hfn, hfa, hf1, hf2, hf3, hf4, hfnext,
      Reg.cursor, Reg.top, Reg.stack, Reg.depth, Reg.childCode, Reg.childUsed,
      Reg.childStars, Reg.childPower, Reg.five, BoxTable.Reg.one, Fin.mk.injEq]
  refine ⟨y, hy, by simp [y], ?_, fun i hi => hy.regs_eq (push_preserves i hi)⟩
  simp only [y, z4, z3, z2, z1, z0, Data.set_mem, Data.write_mem, writeTask, a,
    Nat.add_assoc, Nat.reduceAdd]

/-- Registers modified while popping a complete five-word task. -/
@[expose] def PopLocal (i : Fin registers) : Prop :=
  i = Reg.top ∨ i = Reg.cursor ∨ i = Reg.depth ∨ i = Reg.code ∨
    i = Reg.used ∨ i = Reg.stars ∨ i = Reg.power

instance (i : Fin registers) : Decidable (PopLocal i) :=
  inferInstanceAs (Decidable (i = Reg.top ∨ i = Reg.cursor ∨ i = Reg.depth ∨
    i = Reg.code ∨ i = Reg.used ∨ i = Reg.stars ∨ i = Reg.power))

private theorem pop_preserves (i : Fin registers) : ¬PopLocal i → pop.Preserves i :=
  by decide +revert

/-- Pop the occupied top record, reading every real task word in twelve instructions. -/
theorem exec_pop {w F n k c u e p : ℕ} (x : Data registers)
    (hF : x.regs Reg.stack = F) (hn : x.regs Reg.top = n + 1)
    (h5 : x.regs Reg.five = 5) (h1 : x.regs BoxTable.Reg.one = 1)
    (hk : x.mem (F + n * 5) = k) (hc : x.mem (F + n * 5 + 1) = c)
    (hu : x.mem (F + n * 5 + 2) = u) (he : x.mem (F + n * 5 + 3) = e)
    (hp : x.mem (F + n * 5 + 4) = p) (hfit : Fits w (F + 5 * (n + 1) + 8)) :
    ∃ y, ExecWithin w pop x y 12 ∧ y.regs Reg.top = n ∧
      y.regs Reg.depth = k ∧ y.regs Reg.code = c ∧ y.regs Reg.used = u ∧
      y.regs Reg.stars = e ∧ y.regs Reg.power = p ∧ y.mem = x.mem ∧
      (∀ i, ¬PopLocal i → y.regs i = x.regs i) := by
  let a := F + n * 5
  have hfn : Fits w n := hfit.of_le (by omega)
  have hfm : Fits w (n * 5) := hfit.of_le (by omega)
  have hfa : Fits w a := hfit.of_le (by dsimp only [a]; omega)
  have hf1 : Fits w (a + 1) := hfit.of_le (by dsimp only [a]; omega)
  have hf2 : Fits w (a + 1 + 1) := hfit.of_le (by dsimp only [a]; omega)
  have hf3 : Fits w (a + 1 + 1 + 1) := hfit.of_le (by dsimp only [a]; omega)
  have hf4 : Fits w (a + 1 + 1 + 1 + 1) := hfit.of_le (by dsimp only [a]; omega)
  have hu' : x.mem (a + 1 + 1) = u := by simpa [a, Nat.add_assoc] using hu
  have he' : x.mem (a + 1 + 1 + 1) = e := by simpa [a, Nat.add_assoc] using he
  have hp' : x.mem (a + 1 + 1 + 1 + 1) = p := by simpa [a, Nat.add_assoc] using hp
  let z0 := ((x.set Reg.top n).set Reg.cursor (n * 5)).set Reg.cursor a
  let z1 := (z0.set Reg.depth k).set Reg.cursor (a + 1)
  let z2 := (z1.set Reg.code c).set Reg.cursor (a + 1 + 1)
  let z3 := (z2.set Reg.used u).set Reg.cursor (a + 1 + 1 + 1)
  let z4 := (z3.set Reg.stars e).set Reg.cursor (a + 1 + 1 + 1 + 1)
  let y := z4.set Reg.power p
  have hy : ExecWithin w pop x y 12 := by
    ram_eval [pop, y, z4, z3, z2, z1, z0, a, hF, hn, h5, h1, hk, hc, hu', he', hp',
      hfn, hfm, hfa, hf1, hf2, hf3, hf4, Reg.top, Reg.cursor, Reg.stack,
      Reg.depth, Reg.code, Reg.used, Reg.stars, Reg.power, Reg.five,
      BoxTable.Reg.one, Fin.mk.injEq, Nat.add_sub_cancel]
  refine ⟨y, hy, ?_, ?_, ?_, ?_, ?_, ?_, rfl,
    fun i hi => hy.regs_eq (pop_preserves i hi)⟩
  all_goals simp [y, z4, z3, z2, z1, z0, Reg.top, Reg.cursor, Reg.depth, Reg.code,
    Reg.used, Reg.stars, Reg.power]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
