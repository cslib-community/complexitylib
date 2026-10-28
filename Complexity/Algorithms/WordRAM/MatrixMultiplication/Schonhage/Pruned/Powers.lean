/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory

/-!
# Charged initialization and encoding-array size

## Main results

* `PrunedQuery.exec_powers`: compute `10^L` using the actual native multiplication loop,
  preserving all caller parameters and memory.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- The scalar registers initialized or advanced by the power loop. -/
def PowersLocal (i : Fin registers) : Prop :=
  i = nil ∨ i = one ∨ i = two ∨ i = ten ∨ i = nine ∨ i = frameWidth ∨ i = span ∨ i = index

instance (i : Fin registers) : Decidable (PowersLocal i) :=
  inferInstanceAs (Decidable
    (i = nil ∨ i = one ∨ i = two ∨ i = ten ∨ i = nine ∨ i = frameWidth ∨ i = span ∨ i = index))

private theorem powers_preserves (i : Fin registers) : ¬PowersLocal i → powers.Preserves i := by
  decide +kernel +revert

/-- The power loop charges its eight initializations, both body instructions, loop tests and
jumps. The only width premise is a bound on ordinary input-derived natural numbers. -/
theorem exec_powers {w L Q : ℕ} (x : Data registers) (hL : x.regs inputDepth = L)
    (hbound : Fits w (addressBound L Q)) :
    ∃ y, ExecWithin w powers x y (4 * L + 10) ∧ y.mem = x.mem ∧
      y.regs inputDepth = L ∧ y.regs span = 10 ^ L ∧ y.regs index = L ∧
      y.regs nil = 0 ∧ y.regs one = 1 ∧ y.regs two = 2 ∧ y.regs ten = 10 ∧
      y.regs nine = 9 ∧ y.regs frameWidth = 4 ∧
      (∀ i, ¬PowersLocal i → y.regs i = x.regs i) := by
  have hspan : 1 ≤ (10 : ℕ) ^ L := by
    have hp : 0 < (10 : ℕ) ^ L := by positivity
    omega
  have hscalar : L + 128 + 128 * 10 ^ L ≤ addressBound L Q := by
    have hm := Nat.mul_le_mul_left L hspan
    unfold addressBound
    nlinarith
  have hbase := hbound.of_le hscalar
  have h0 : Fits w 0 := fits_zero w
  have h1 : Fits w 1 := hbase.of_le (by omega)
  have h2 : Fits w 2 := hbase.of_le (by omega)
  have h4 : Fits w 4 := hbase.of_le (by omega)
  have h9 : Fits w 9 := hbase.of_le (by omega)
  have h10 : Fits w 10 := hbase.of_le (by omega)
  have hpow (j : ℕ) (hj : j ≤ L) : Fits w (10 ^ j) := by
    have hle := Nat.pow_le_pow_right (by decide : 1 ≤ (10 : ℕ)) hj
    exact hbase.of_le (by omega)
  let I (y : Data registers) : Prop :=
    y.mem = x.mem ∧ y.regs inputDepth = L ∧ y.regs span = 10 ^ y.regs index ∧
      y.regs index ≤ L ∧ y.regs one = 1 ∧ y.regs ten = 10
  have hstep (y : Data registers) (hy : I y) (hc : (Cond.lt index inputDepth).Holds y) :
      ∃ z, ExecWithin w powerStep y z 2 ∧ I z ∧
        L - z.regs index < L - y.regs index := by
    obtain ⟨hm, hd, hp, hj, ho, ht⟩ := hy
    have hlt : y.regs index < L := by simpa only [Cond.holds_lt, hd] using hc
    have hmul : Fits w (y.regs span * 10) := by
      rw [hp, ← pow_succ]
      exact hpow _ (by omega)
    have hinc : Fits w (y.regs index + 1) := hbase.of_le (by omega)
    let z := (y.set span (y.regs span * 10)).set index (y.regs index + 1)
    have he : ExecWithin w powerStep y z 2 := by
      ram_eval [powerStep, z, ho, ht, hmul, hinc, span, index, ten, one, Fin.mk.injEq]
    refine ⟨z, he, ?_, ?_⟩
    · refine ⟨hm, ?_, ?_, ?_, ?_, ?_⟩
      · simpa +decide [z, inputDepth, span, index, Function.update_apply] using hd
      · simp +decide [z, span, index, hp, pow_succ]
      · simpa [z] using Nat.succ_le_of_lt hlt
      · simpa +decide [z, one, span, index, Function.update_apply] using ho
      · simpa +decide [z, ten, span, index, Function.update_apply] using ht
    · simp only [z, Data.set_regs, Function.update_self]
      omega
  let x0 := ((((((((x.set nil 0).set one 1).set two 2).set ten 10).set nine 9).set
    frameWidth 4).set span 1).set index 0)
  have hsetup : ExecWithin w powerSetup x x0 8 := by
    ram_eval [powerSetup, x0, h0, h1, h2, h4, h9, h10]
  have hI : I x0 := by
    simp +decide [I, x0, hL, inputDepth, nil, one, two, ten, nine, frameWidth, span, index]
  obtain ⟨y, hy, hIy, hstop⟩ := ExecWithin.loop_invariant I (fun y => L - y.regs index)
    hstep hI
  have he : ExecWithin w powers x y (4 * L + 10) := by
    exact (hsetup.seq hy).mono (by simp [x0]; omega)
  obtain ⟨hm, hd, hp, hj, ho, ht⟩ := hIy
  have hidx : y.regs index = L := by
    simp only [Cond.holds_lt, hd, not_lt] at hstop
    omega
  refine ⟨y, he, hm, hd, hp.trans (congrArg (fun n => 10 ^ n) hidx), hidx,
    ?_, ho, ?_, ht, ?_, ?_, fun i hi => he.regs_eq (powers_preserves i hi)⟩
  · simpa +decide [x0, nil, one, two, ten, nine, frameWidth, span, index] using
      hy.regs_eq (by decide :
      (Code.loop (.lt index inputDepth) powerStep).Preserves nil)
  · simpa +decide [x0, nil, one, two, ten, nine, frameWidth, span, index] using
      hy.regs_eq (by decide :
      (Code.loop (.lt index inputDepth) powerStep).Preserves two)
  · simpa +decide [x0, nil, one, two, ten, nine, frameWidth, span, index] using
      hy.regs_eq (by decide :
      (Code.loop (.lt index inputDepth) powerStep).Preserves nine)
  · simpa +decide [x0, nil, one, two, ten, nine, frameWidth, span, index] using
      hy.regs_eq (by decide :
      (Code.loop (.lt index inputDepth) powerStep).Preserves frameWidth)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
