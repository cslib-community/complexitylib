/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Kernel

/-!
# Actual record selection and depth recovery

These internal lemmas account for the actual original-header and six descriptor loads, every
stride/address calculation, and the existing floor-logarithm loop. The final producer client
derives each loaded word from its actual readback theorem.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM

/-- The actual binary logarithm recovers twice the power-of-four exponent. -/
theorem log_two_four_pow (m : ℕ) : Nat.log 2 (4 ^ m) = 2 * m := by
  rw [show 4 ^ m = 2 ^ (2 * m) by rw [Nat.pow_mul], Nat.log_pow (by decide)]

private theorem logBank_injective : Function.Injective logBank := by
  intro i j h
  apply Fin.ext
  simpa only [logBank, Nat.add_left_cancel_iff] using congrArg Fin.val h

-- This closed preservation test enumerates the finite relocated register bank.
set_option maxRecDepth 4096 in
private theorem log_preserves : ∀ i : Fin 320,
    i.val < 96 ∨ 100 ≤ i.val → logarithm.Preserves i := by decide

/-- The computed logarithm is read from the actual existing loop, with no logarithm input
certificate. Its charge is `8m+5` at a power of four. -/
theorem exec_logarithm {W m : ℕ} (x : Data 320)
    (hD : x.regs Reg.source = 4 ^ m) (hfit : Fits W (4 ^ m + 2 * m + 3)) :
    ∃ y, ExecWithin W logarithm x y (8 * m + 5) ∧
      y.regs Reg.destination = 2 * m ∧ y.mem = x.mem ∧
      ∀ i : Fin 320, i.val < 96 ∨ 100 ≤ i.val → y.regs i = x.regs i := by
  have harg : x.regs (logBank NatLog.arg) = 4 ^ m := hD
  obtain ⟨y, hy, hr, hm, -, -⟩ := NatLog.exec_rename logBank logBank_injective x
    (hfit.of_le (by omega)) (by rw [harg]; exact hfit.of_le (by omega))
    (by rw [harg, log_two_four_pow]; exact hfit.of_le (by omega))
  refine ⟨y, ?_, ?_, hm, fun i hi => hy.regs_eq (log_preserves i hi)⟩
  · have he : 4 * Nat.log 2 (x.regs (logBank NatLog.arg)) + 5 = 8 * m + 5 := by
      rw [harg, log_two_four_pow]; omega
    simpa only [logarithm, he] using hy
  · rw [harg, log_two_four_pow] at hr
    exact hr

/-- Read an actual six-word producer record at its computed ordinal. The input memory is
unchanged; arbitrary source words are loaded, rather than supplied as predecoded registers. -/
theorem exec_readRecord {W n D i out b : ℕ} (x : Data 320) (v : Fin 6 → ℕ)
    (hD : x.mem 1 = D) (hn : x.mem 3 = n)
    (hi : x.regs Reg.ordinal = i) (hout : x.regs 39 = out) (hb : x.regs 42 = b)
    (hrec : out + i * (6 + 2 * (n * D)) + 6 ≤ b)
    (hv : ∀ k : Fin 6, x.mem (out + i * (6 + 2 * (n * D)) + k.val) = v k)
    (hfit : Fits W (b + 2 * (n * D) + D + n + 128)) :
    ∃ y, ExecWithin W readRecord x y 28 ∧ y.mem = x.mem ∧
      y.regs Reg.dimension = D ∧ y.regs Reg.size = n ∧
      y.regs Reg.area = n * D ∧ y.regs Reg.twiceArea = 2 * (n * D) ∧
      y.regs Reg.base = b ∧ y.regs Reg.record = out + i * (6 + 2 * (n * D)) ∧
      y.regs Reg.rho = v 0 ∧ y.regs Reg.piece = v 1 ∧ y.regs Reg.queries = v 2 ∧
      y.regs Reg.count = v 3 ∧ y.regs Reg.left = v 4 ∧ y.regs Reg.right = v 5 ∧
      y.regs Reg.source = D ∧ y.regs Reg.one = 1 ∧ y.regs Reg.two = 2 ∧
      y.regs Reg.nineteen = 19 ∧ y.regs Reg.four = 4 := by
  let r := out + i * (n * D + n * D + 6)
  have hmul : n * D + n * D + 6 = 6 + 2 * (n * D) := by omega
  have hrec' : r + 6 ≤ b := by simpa only [r, hmul] using hrec
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have h2 : Fits W 2 := hfit.of_le (by omega)
  have h3 : Fits W 3 := hfit.of_le (by omega)
  have h4 : Fits W 4 := hfit.of_le (by omega)
  have h6 : Fits W 6 := hfit.of_le (by omega)
  have h19 : Fits W 19 := hfit.of_le (by omega)
  have hA : Fits W (n * D) := hfit.of_le (by omega)
  have hAA : Fits W (n * D + n * D) := hfit.of_le (by omega)
  have hstride : Fits W (n * D + n * D + 6) := hfit.of_le (by omega)
  have his : Fits W (i * (n * D + n * D + 6)) := by
    rw [hmul]; exact hfit.of_le (by omega)
  have hr : Fits W r := hfit.of_le (by dsimp only [r]; omega)
  have hr1 : Fits W (r + 1) := hfit.of_le (by dsimp only [r]; omega)
  have hr2 : Fits W (r + 1 + 1) := hfit.of_le (by dsimp only [r]; omega)
  have hr3 : Fits W (r + 1 + 1 + 1) := hfit.of_le (by dsimp only [r]; omega)
  have hr4 : Fits W (r + 1 + 1 + 1 + 1) := hfit.of_le (by dsimp only [r]; omega)
  have hr5 : Fits W (r + 1 + 1 + 1 + 1 + 1) := hfit.of_le (by dsimp only [r]; omega)
  have hv0 : x.mem r = v 0 := by simpa only [r, hmul, Fin.val_zero, Nat.add_zero] using hv 0
  have hv1 : x.mem (r + 1) = v 1 := by simpa +decide [r, hmul] using hv ⟨1, by decide⟩
  have hv2 : x.mem (r + 1 + 1) = v 2 := by
    change x.mem (r + 2) = v 2
    simpa +decide [r, hmul] using hv ⟨2, by decide⟩
  have hv3 : x.mem (r + 1 + 1 + 1) = v 3 := by
    change x.mem (r + 3) = v 3
    simpa +decide [r, hmul] using hv ⟨3, by decide⟩
  have hv4 : x.mem (r + 1 + 1 + 1 + 1) = v 4 := by
    change x.mem (r + 4) = v 4
    simpa +decide [r, hmul] using hv ⟨4, by decide⟩
  have hv5 : x.mem (r + 1 + 1 + 1 + 1 + 1) = v 5 := by
    change x.mem (r + 5) = v 5
    simpa +decide [r, hmul] using hv ⟨5, by decide⟩
  let y := x.set Reg.one 1 |>.set Reg.two 2 |>.set Reg.six 6 |>.set Reg.nineteen 19
    |>.set Reg.four 4 |>.set Reg.address 1 |>.set Reg.dimension D |>.set Reg.address 3
    |>.set Reg.size n |>.set Reg.area (n * D) |>.set Reg.twiceArea (n * D + n * D)
    |>.set Reg.address (n * D + n * D + 6)
    |>.set Reg.address (i * (n * D + n * D + 6)) |>.set Reg.record r |>.set Reg.base b
    |>.set Reg.address r |>.set Reg.rho (v 0) |>.set Reg.address (r + 1)
    |>.set Reg.piece (v 1) |>.set Reg.address (r + 1 + 1) |>.set Reg.queries (v 2)
    |>.set Reg.address (r + 1 + 1 + 1) |>.set Reg.count (v 3)
    |>.set Reg.address (r + 1 + 1 + 1 + 1) |>.set Reg.left (v 4)
    |>.set Reg.address (r + 1 + 1 + 1 + 1 + 1) |>.set Reg.right (v 5) |>.set Reg.source D
  refine ⟨y, ?run, ?post⟩
  case run =>
    ram_eval [readRecord, y, hi, hout, hb, hD, hn, h1, h2, h3, h4, h6, h19, hA, hAA,
      hstride, his, hr, hr1, hr2, hr3, hr4, hr5, r, hv0, hv1, hv2, hv3, hv4, hv5,
      Reg.one, Reg.two, Reg.six, Reg.nineteen, Reg.four, Reg.address, Reg.dimension,
      Reg.size, Reg.area, Reg.twiceArea, Reg.ordinal, Reg.record, Reg.base, Reg.rho,
      Reg.piece, Reg.queries, Reg.count, Reg.left, Reg.right, Reg.source]
  case post =>
    simp +decide [y, r, two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
