/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.SavedGroups

/-!
# Actual reconstruction in original request order

## Main results

* `QueriedProduct.exec_reconstruct`: read the stored original indices and grouped answers,
  then scatter every answer to its original request position, charging every instruction.

The existing stable-position bijection proves that no earlier answer is overwritten.
Neither an inverse permutation nor a scatter execution is supplied to the program.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual reconstruction retains repeated input occurrences, input words and outside memory.
Only the designated original-order answer block is written. -/
public theorem exec_reconstruct {w L m N : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (old : ℕ → ℕ) (x : Data 160)
    (hp : Parameters L m N qs.length x) (hg : SavedGroups L m N qs.length old x.mem)
    (horiginals : ∀ i : Fin qs.length,
      old (Wanted.originalAddress L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) = i.val)
    (hanswers : ∀ i : Fin qs.length,
      x.mem (groupedBase L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2))
    (hfit : Fits w (wordBudget L m N qs.length)) :
    ∃ y, ExecWithin w reconstruct x y (9 * qs.length + 3) ∧
      Parameters L m N qs.length y ∧
      (∀ i : Fin qs.length, y.mem (outputBase L m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < outputBase L m N qs.length ∨ scratchBase L m N qs.length ≤ a →
        y.mem a = x.mem a) := by
  let key := Wanted.tileKey L m N ∘ Wanted.inputPairs qs
  let pos := CountingSort.position key qs.length
  let I (z : Data 160) : Prop := Parameters L m N qs.length z ∧ z.regs Reg.index ≤ qs.length ∧
    (∀ i : Fin qs.length, pos i.val < z.regs Reg.index →
      z.mem (outputBase L m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
    (∀ a, a < outputBase L m N qs.length ∨ scratchBase L m N qs.length ≤ a → z.mem a = x.mem a)
  have hout : outputBase L m N qs.length + qs.length = scratchBase L m N qs.length := rfl
  have hgroup : groupedBase L m N qs.length + qs.length = outputBase L m N qs.length := rfl
  have horig : originalBase L m N qs.length + qs.length = groupedBase L m N qs.length := rfl
  have hfree : scratchBase L m N qs.length ≤ memoryEnd L m N qs.length := by
    unfold memoryEnd stampBase
    have h10 := Nat.zero_le (10 ^ L)
    omega
  let start := x.set Reg.index 0
  have hs : ExecWithin (B := .standard) w (ram[Reg.index ← #0]) x start 1 := by ram_eval [start]
  have sp : Parameters L m N qs.length start := hp.set_work Reg.index (by decide) _
  have hstart : I start := ⟨sp, by simp [start], by simp [start, pos], by simp [start]⟩
  have hbody (z : Data 160) (hz : I z) (hc : (Cond.lt Reg.index Reg.queryCount).Holds z) :
      ∃ u, ExecWithin w reconstructStep z u 7 ∧ I u ∧
        qs.length - u.regs Reg.index < qs.length - z.regs Reg.index := by
    have hi : z.regs Reg.index < qs.length := by
      simpa only [Cond.holds_lt, hz.1.queryCount] using hc
    obtain ⟨i, hip⟩ :=
      (CountingSort.position_bijective key qs.length).surjective ⟨z.regs Reg.index, hi⟩
    have hpos := congrArg (fun j : Fin qs.length => j.val) hip
    change pos i.val = z.regs Reg.index at hpos
    have hreadIndex : z.mem (originalBase L m N qs.length + z.regs Reg.index) = i.val := by
      rw [hz.2.2.2 _ (Or.inl (by omega)), hg.originals _ hi, ← hpos]
      exact horiginals i
    have hreadValue : z.mem (groupedBase L m N qs.length + z.regs Reg.index) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2) := by
      rw [hz.2.2.2 _ (Or.inl (by omega)), ← hpos]
      exact hanswers i
    have fo : Fits w (originalBase L m N qs.length + z.regs Reg.index) :=
      allocated_fits hfit (by omega)
    have fg : Fits w (groupedBase L m N qs.length + z.regs Reg.index) :=
      allocated_fits hfit (by omega)
    have fy : Fits w (outputBase L m N qs.length + i.val) := allocated_fits hfit (by
      have h := i.isLt
      omega)
    have fn : Fits w (z.regs Reg.index + 1) := allocated_fits hfit (by omega)
    let answer := Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)
    let u := ((((((z.set Reg.address (originalBase L m N qs.length + z.regs Reg.index)).set
      Reg.temporary i.val).set Reg.address (groupedBase L m N qs.length + z.regs Reg.index)).set
      Reg.value answer).set Reg.address (outputBase L m N qs.length + i.val)).write
      (outputBase L m N qs.length + i.val) answer).set Reg.index (z.regs Reg.index + 1)
    have he : ExecWithin w reconstructStep z u 7 := by
      ram_eval [reconstructStep, u, answer, hz.1.originals, hz.1.grouped, hz.1.output,
        hz.1.one, hreadIndex, hreadValue, fo, fg, fy, fn, Reg.address, Reg.originals, Reg.index,
        Reg.temporary, Reg.grouped, Reg.value, Reg.output, Reg.one]
    have up : Parameters L m N qs.length u :=
      ((((((hz.1.set_work Reg.address (by decide) _).set_work Reg.temporary (by decide) _).set_work
        Reg.address (by decide) _).set_work Reg.value (by decide) _).set_work Reg.address
        (by decide) _).write _ _).set_work Reg.index (by decide) _
    have un : u.regs Reg.index = z.regs Reg.index + 1 := by simp [u]
    refine ⟨u, he, ⟨up, by rw [un]; omega, ?_, ?_⟩, by rw [un]; omega⟩
    · intro j hj
      rw [un] at hj
      change Function.update z.mem (outputBase L m N qs.length + i.val) answer
        (outputBase L m N qs.length + j.val) = _
      by_cases hij : j = i
      · subst j
        exact Function.update_self _ _ _
      · have hne : j.val ≠ i.val := fun heq => hij (Fin.ext heq)
        rw [Function.update_of_ne (by omega)]
        have hpne : pos j.val ≠ pos i.val := fun heq => hij
          (CountingSort.position_injective key qs.length heq)
        exact hz.2.2.1 j (by omega)
    · intro a ha
      change Function.update z.mem (outputBase L m N qs.length + i.val) answer a = _
      rw [Function.update_of_ne (by have h := i.isLt; rcases ha with ha | ha <;> omega)]
      exact hz.2.2.2 a ha
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I (fun z => qs.length - z.regs Reg.index)
    hbody hstart
  have hn : y.regs Reg.index = qs.length := by
    have h := hy.2.1
    simp only [Cond.holds_lt, hy.1.queryCount] at hc
    omega
  refine ⟨y, ?_, hy.1, ?_, hy.2.2.2⟩
  · apply (hs.seq he).mono
    have hzero : start.regs Reg.index = 0 := by simp [start]
    rw [hzero, Nat.sub_zero]
    omega
  · intro i
    apply hy.2.2.1 i
    rw [hn]
    exact CountingSort.position_lt key i.isLt

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
