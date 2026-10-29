/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.PackProgram
import Mathlib.Tactic.Linarith

/-!
# Execution of the native wanted-output digit loop

## Main results

* `Wanted.exec_pack`: actual unsigned packing with an explicit linear instruction bound
  and unchanged memory, for arbitrary initial scratch-register contents.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage.QueryDigits

/-- Scalar contents retained throughout packing. These are only register equalities. -/
structure PackParameters (L : ℕ) (x : Data 16) : Prop where
  /-- Original depth. -/
  depth : x.regs depth = L
  /-- Initialized unit. -/
  one : x.regs one = 1
  /-- Binary radix. -/
  two : x.regs two = 2
  /-- Compressed offset radix. -/
  three : x.regs three = 3
  /-- Output radix. -/
  ten : x.regs ten = 10
  /-- Inner output digit. -/
  nine : x.regs nine = 9

/-- A consumed prefix and the remaining arithmetic recurrence give the original output. -/
structure PackProgress (L M R C : ℕ) (x : Data 16) : Prop where
  /-- Persistent constants and depth. -/
  fixed : PackParameters L x
  /-- A coordinate is visited at most once. -/
  level_le : x.regs level ≤ L
  /-- Binary division decreases the mask. -/
  mask_le : x.regs mask ≤ M
  /-- Ternary division decreases the row offset. -/
  row_le : x.regs row ≤ R
  /-- Ternary division decreases the column offset. -/
  col_le : x.regs col ≤ C
  /-- Actual next output place. -/
  power_eq : x.regs power = 10 ^ x.regs level
  /-- Already emitted digits fit below the next place. -/
  code_lt : x.regs code < x.regs power
  /-- Prefix and residual recurrence have the desired complete value. -/
  value : x.regs code + x.regs power *
    pack (L - x.regs level) (x.regs mask) (x.regs row) (x.regs col) = pack L M R C

private theorem parameters_after_body {L : ℕ} {x y : Data 16}
    (hx : PackParameters L x) {w c : ℕ} (he : ExecWithin w packBody x y c) :
    PackParameters L y := by
  have hf (i : Fin 16) (hi : i ∈ ({depth, one, two, three, ten, nine} : Finset _)) :
      y.regs i = x.regs i := by
    apply he.regs_eq
    have h : ∀ i ∈ ({depth, one, two, three, ten, nine} : Finset (Fin 16)),
        packBody.Preserves i := by
      simp only [packBody, Code.Preserves, Op.dest, Op.bin]
      decide
    exact h i hi
  exact ⟨(hf _ (by decide)).trans hx.depth, (hf _ (by decide)).trans hx.one,
    (hf _ (by decide)).trans hx.two, (hf _ (by decide)).trans hx.three,
    (hf _ (by decide)).trans hx.ten, (hf _ (by decide)).trans hx.nine⟩

/-- One coordinate's actual test, arithmetic and register updates. The numeric budget is
derived from original inputs, rather than an assumed bound on intermediate states. -/
theorem exec_packBody {w L M R C : ℕ} (x : Data 16) (hx : PackProgress L M R C x)
    (hc : (Cond.lt level depth).Holds x)
    (hfit : Fits w (M + R + C + L + 32 * 10 ^ L + 32)) :
    ∃ y, ExecWithin w packBody x y 13 ∧ PackProgress L M R C y ∧ y.mem = x.mem ∧
      L - y.regs level < L - x.regs level := by
  have hj : x.regs level < L := by simpa only [Cond.holds_lt, hx.fixed.depth] using hc
  have hr := Nat.mod_lt (x.regs row) (by decide : 0 < 3)
  have hcol := Nat.mod_lt (x.regs col) (by decide : 0 < 3)
  have hp : x.regs power ≤ 10 ^ L := by
    rw [hx.power_eq]
    exact Nat.pow_le_pow_right (by decide) hx.level_le
  have hmfit : Fits w (x.regs mask / 2) := hfit.of_le
    ((Nat.div_le_self _ _).trans (by have := hx.mask_le; omega))
  have hbit : Fits w (x.regs mask % 2) := hfit.of_le (by
    have := Nat.mod_lt (x.regs mask) (by decide : 0 < 2)
    omega)
  have hpfit : Fits w (x.regs power * 10) := hfit.of_le (by omega)
  have hjfit : Fits w (x.regs level + 1) := hfit.of_le (by omega)
  have hrest : L - x.regs level = L - (x.regs level + 1) + 1 := by omega
  by_cases hb : x.regs mask % 2 = 0
  · let d := (x.regs row % 3) * 3 + x.regs col % 3
    have hd : d < 9 := by dsimp [d]; omega
    have hrd : Fits w (x.regs row % 3) := hfit.of_le (by omega)
    have hr3 : Fits w (x.regs row % 3 * 3) := hfit.of_le (by omega)
    have hcd : Fits w (x.regs col % 3) := hfit.of_le (by omega)
    have hdf : Fits w d := hfit.of_le (by omega)
    have hrq : Fits w (x.regs row / 3) := hfit.of_le
      ((Nat.div_le_self _ _).trans (by have := hx.row_le; omega))
    have hcq : Fits w (x.regs col / 3) := hfit.of_le
      ((Nat.div_le_self _ _).trans (by have := hx.col_le; omega))
    have hmul : Fits w (d * x.regs power) := hfit.of_le (by nlinarith)
    have hadd : Fits w (x.regs code + d * x.regs power) := hfit.of_le (by
      have := hx.code_lt
      nlinarith)
    let y := ((((((((((((x.set bit 0).set mask (x.regs mask / 2)).set digit
      (x.regs row % 3)).set digit (x.regs row % 3 * 3)).set temporary
      (x.regs col % 3)).set digit d).set row (x.regs row / 3)).set
      col (x.regs col / 3)).set temporary (d * x.regs power)).set code
      (x.regs code + d * x.regs power)).set power (x.regs power * 10)).set
      level (x.regs level + 1))
    have he : ExecWithin w packBody x y 13 := by
      ram_eval [packBody, y, d, hx.fixed.two, hx.fixed.three, hx.fixed.one,
        hx.fixed.ten, hb, hmfit, hbit, hpfit, hjfit, hrd, hr3, hcd, hdf,
        hrq, hcq, hmul, hadd, Nat.lt_one_iff,
        mask, bit, row, col, digit, temporary, code, power, level, two, three, one, ten,
        Fin.mk.injEq]
    refine ⟨y, he, ⟨parameters_after_body hx.fixed he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      rfl, ?_⟩
    · simp only [y, Data.set_regs, Function.update_self]; omega
    · simpa [y, mask, bit, digit, row, col, temporary, code, power, level] using
        (Nat.div_le_self (x.regs mask) 2).trans hx.mask_le
    · simpa [y, mask, bit, digit, row, col, temporary, code, power, level] using
        (Nat.div_le_self (x.regs row) 3).trans hx.row_le
    · simpa [y, mask, bit, digit, row, col, temporary, code, power, level] using
        (Nat.div_le_self (x.regs col) 3).trans hx.col_le
    · simp [y, power, level, hx.power_eq, pow_succ]
    · have := hx.code_lt
      simp only [y, Data.set_regs, Function.update_self, code, power, level,
        Function.update_of_ne (by decide : (4 : Fin 16) ≠ 5),
        Function.update_of_ne (by decide : (4 : Fin 16) ≠ 6),
        Function.update_of_ne (by decide : (6 : Fin 16) ≠ 5)]
      nlinarith
    · have hv := hx.value
      rw [hrest, pack, ite_eq_left hb] at hv
      simp only [y, Data.set_regs, Function.update_apply]
      simp only [mask, row, col, code, power, level, digit, temporary,
        Fin.isValue, ↓reduceIte]
      dsimp [d] at *
      nlinarith only [hv]
    · change L - (x.regs level + 1) < L - x.regs level
      omega
  · have h9 : Fits w 9 := hfit.of_le (by omega)
    have hmul : Fits w (9 * x.regs power) := hfit.of_le (by omega)
    have hadd : Fits w (x.regs code + 9 * x.regs power) := hfit.of_le (by
      have := hx.code_lt
      omega)
    let y := (((((((x.set bit (x.regs mask % 2)).set mask (x.regs mask / 2)).set
      digit 9).set temporary (9 * x.regs power)).set code
      (x.regs code + 9 * x.regs power)).set power (x.regs power * 10)).set
      level (x.regs level + 1))
    have he : ExecWithin w packBody x y 13 := by
      ram_eval [packBody, y, hx.fixed.two, hx.fixed.nine, hx.fixed.one, hx.fixed.ten,
        hb, hmfit, hbit, hpfit, hjfit, h9, hmul, hadd, Nat.lt_one_iff,
        mask, bit, row, col, digit, temporary, code, power, level, two, three, one, ten, nine,
        Fin.mk.injEq]
    refine ⟨y, he, ⟨parameters_after_body hx.fixed he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      rfl, ?_⟩
    · simp only [y, Data.set_regs, Function.update_self]; omega
    · simpa [y, mask, bit, digit, row, col, temporary, code, power, level] using
        (Nat.div_le_self (x.regs mask) 2).trans hx.mask_le
    · simpa [y, mask, bit, digit, row, col, temporary, code, power, level] using hx.row_le
    · simpa [y, mask, bit, digit, row, col, temporary, code, power, level] using hx.col_le
    · simp [y, power, level, hx.power_eq, pow_succ]
    · have := hx.code_lt
      change x.regs code + 9 * x.regs power < x.regs power * 10
      omega
    · have hv := hx.value
      rw [hrest, pack, ite_eq_right hb] at hv
      simp only [bit, Fin.isValue, mask, digit, temporary, power, code, level, Data.set_regs,
        ne_eq, Fin.reduceEq, not_false_eq_true, Function.update_of_ne, Function.update_self,
        row, col, y]
      nlinarith only [hv]
    · change L - (x.regs level + 1) < L - x.regs level
      omega

/-- Execute the entire fixed packer from ordinary register inputs. Every branch, division,
remainder, index update and loop control is charged; memory and the depth are preserved. -/
theorem exec_pack {w : ℕ} (L M R C : ℕ) (x : Data 16)
    (hL : x.regs depth = L) (hM : x.regs mask = M) (hR : x.regs row = R)
    (hC : x.regs col = C) (hfit : Fits w (M + R + C + L + 32 * 10 ^ L + 32)) :
    ∃ y, ExecWithin w packCode x y (15 * L + 10) ∧
      y.regs code = pack L M R C ∧ y.regs depth = L ∧ y.mem = x.mem := by
  have hf (v : ℕ) (hv : v ≤ 10) : Fits w v := hfit.of_le (by omega)
  let start := ((((((((x.set one 1).set two 2).set three 3).set ten 10).set nine 9).set
    code 0).set level 0).set power 1)
  have hs : ExecWithin w packHead x start 8 := by
    ram_eval [packHead, start, hf 0 (by decide), hf 1 (by decide), hf 2 (by decide),
      hf 3 (by decide), hf 9 (by decide), hf 10 (by decide),
      one, two, three, ten, nine, code, level, power, Fin.mk.injEq]
  have hi : PackProgress L M R C start := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · constructor <;> simp [start, depth, one, two, three, ten, nine, code, level, power, hL]
    all_goals simp [start, one, two, three, ten, nine, code, level, power,
      mask, row, col, hM, hR, hC]
  let I (z : Data 16) : Prop := PackProgress L M R C z ∧ z.mem = x.mem
  have hb (z : Data 16) (hz : I z) (hc : (Cond.lt level depth).Holds z) :
      ∃ u, ExecWithin w packBody z u 13 ∧ I u ∧
        L - u.regs level < L - z.regs level := by
    obtain ⟨u, he, hu, hm, ht⟩ := exec_packBody z hz.1 hc hfit
    exact ⟨u, he, ⟨hu, hm.trans hz.2⟩, ht⟩
  obtain ⟨y, he, hy, hc⟩ := ExecWithin.loop_invariant I
    (fun z => L - z.regs level) hb ⟨hi, rfl⟩
  have hend : y.regs level = L := by
    simp only [Cond.holds_lt, hy.1.fixed.depth] at hc
    have := hy.1.level_le
    omega
  refine ⟨y, ?_, ?_, hy.1.fixed.depth, hy.2⟩
  · apply (hs.seq he).mono
    have hstart : start.regs level = 0 := by simp [start, level, power]
    rw [hstart, Nat.sub_zero]
    omega
  · simpa only [hend, Nat.sub_self, pack, Nat.mul_zero, Nat.add_zero] using hy.1.value

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
