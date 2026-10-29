/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Decode

/-!
# Original callee header stores

The native stores place the payload length, computed tensor level and recovered inner depth,
outer dimension and actual occurrence count above the producer's heap. No encoded matrix or
query table is supplied by this header.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM

/-- Fifteen actual arithmetic/copy/store instructions write the five original header words.
All metadata below register 78, including the complete producer bank, is preserved. -/
theorem exec_writeHeader {W b m n A Q : ℕ} (x : Data 320)
    (hb : x.regs Reg.base = b) (hm : x.regs Reg.destination = 2 * m)
    (hA : x.regs Reg.twiceArea = 2 * A) (hQ : x.regs Reg.count = Q)
    (hn : x.regs Reg.size = n) (h1 : x.regs Reg.one = 1) (h2 : x.regs Reg.two = 2)
    (h19 : x.regs Reg.nineteen = 19) (h4 : x.regs Reg.four = 4)
    (hfit : Fits W (b + 19 * m + 2 * A + 2 * Q + 64)) :
    ∃ y, ExecWithin W writeHeader x y 15 ∧
      (Block.mk b 5).Realizes y.mem ![4 + 2 * A + 2 * Q, 19 * m, m, n, Q] ∧
      (∀ a, a < b ∨ b + 5 ≤ a → y.mem a = x.mem a) ∧
      ∀ i : Fin 320, i.val < 78 → y.regs i = x.regs i := by
  have hdepth : Fits W m := hfit.of_le (by omega)
  have hlevel : Fits W (m * 19) := hfit.of_le (by omega)
  have hAQ : Fits W (2 * A + Q) := hfit.of_le (by omega)
  have hAQQ : Fits W (2 * A + Q + Q) := hfit.of_le (by omega)
  have hlen : Fits W (2 * A + Q + Q + 4) := hfit.of_le (by omega)
  have hb1 : Fits W (b + 1) := hfit.of_le (by omega)
  have hb2 : Fits W (b + 1 + 1) := hfit.of_le (by omega)
  have hb3 : Fits W (b + 1 + 1 + 1) := hfit.of_le (by omega)
  have hb4 : Fits W (b + 1 + 1 + 1 + 1) := hfit.of_le (by omega)
  have hquot : 2 * m / 2 = m := by omega
  let y := x.set Reg.depth m |>.set Reg.level (m * 19)
    |>.set Reg.payloadLength (2 * A + Q) |>.set Reg.payloadLength (2 * A + Q + Q)
    |>.set Reg.payloadLength (2 * A + Q + Q + 4) |>.set Reg.address b
    |>.write b (2 * A + Q + Q + 4) |>.set Reg.address (b + 1) |>.write (b + 1) (m * 19)
    |>.set Reg.address (b + 1 + 1) |>.write (b + 1 + 1) m
    |>.set Reg.address (b + 1 + 1 + 1) |>.write (b + 1 + 1 + 1) n
    |>.set Reg.address (b + 1 + 1 + 1 + 1) |>.write (b + 1 + 1 + 1 + 1) Q
  have he : ExecWithin W writeHeader x y 15 := by
    ram_eval [writeHeader, y, hb, hm, hA, hQ, hn, h1, h2, h19, h4, hquot, hdepth, hlevel,
      hAQ, hAQQ, hlen, hb1, hb2, hb3, hb4, Reg.depth, Reg.destination, Reg.two,
      Reg.level, Reg.nineteen, Reg.payloadLength, Reg.twiceArea, Reg.count, Reg.four,
      Reg.address, Reg.base, Reg.one, Reg.size]
  refine ⟨y, he, ?_, ?_, ?_⟩
  · intro j
    change y.mem (b + j.val) = _
    fin_cases j <;> simp +decide [y, two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      Nat.mul_comm]
  · intro a ha
    have h0 : a ≠ b := by omega
    have h1 : a ≠ b + 1 := by omega
    have h2 : a ≠ b + 1 + 1 := by omega
    have h3 : a ≠ b + 1 + 1 + 1 := by omega
    have h4 : a ≠ b + 1 + 1 + 1 + 1 := by omega
    simp only [y, Data.write_mem, Data.set_mem, Function.update_of_ne h0,
      Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
      Function.update_of_ne h4]
  · intro i hi
    have hdepth : i ≠ Reg.depth := by intro h; subst i; simp [Reg.depth] at hi
    have hlevel : i ≠ Reg.level := by intro h; subst i; simp [Reg.level] at hi
    have hlen : i ≠ Reg.payloadLength := by
      intro h; subst i; simp [Reg.payloadLength] at hi
    have haddr : i ≠ Reg.address := by intro h; subst i; simp [Reg.address] at hi
    simp only [y, Data.write_regs, Data.set_regs, Function.update_of_ne hdepth,
      Function.update_of_ne hlevel, Function.update_of_ne hlen, Function.update_of_ne haddr]

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
