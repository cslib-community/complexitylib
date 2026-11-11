/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORNativeProjection
import all CslibFrontier.Cryptanalysis.AddXNORNativeProjection

/-!
# Native projection from an arbitrary original operand array

`projectFrom_exec` reuses the existing projection loop with a configurable
source base. This lets dissection project separate original quarters without
first installing them at the fixed encoded-input address. Every read, remainder,
store and control instruction is charged; no projected array is a premise.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.Native.Counters

open Cslib.WordRAM

/-- The existing projection loop, with its source address transferred natively. -/
@[expose] def projectFrom (a : ℕ) (back : Bool) : Code .standard 18 :=
  .seq (ram[ cursor ← #0; one ← #1; negative ← #a ])
    (.loop (.lt cursor limit) (projectBody back))

/-- Construct projected operands from a disjoint original array at `a`.
The observed target list is related to raw source cells only by remainders. -/
theorem projectFrom_exec {W p a b : ℕ} (back : Bool) (as : List (BitVec p))
    (x : Data 18) (hn : x.regs modulus = 2 ^ p)
    (hb : x.regs destination = b) (hq : x.regs limit = as.length)
    (hsep : a + as.length ≤ b)
    (hinput : ∀ j (hj : j < as.length),
      x.mem (a + if back then as.length - 1 - j else j) % 2 ^ p = as[j].toNat)
    (hfit : Fits W (b + as.length + 2 ^ p + 6)) :
    ∃ y, ExecWithin W (projectFrom a back) x y (10 * as.length + 5) ∧
      y.mem = projectedPrefix x.mem b as as.length ∧
      y.regs modulus = 2 ^ p ∧ y.regs destination = b ∧
      y.regs limit = as.length ∧ y.regs cursor = as.length ∧
      y.regs initial = x.regs initial ∧ y.regs one = 1 := by
  have hN := Nat.two_pow_pos p
  have h0 : Fits W 0 := fits_zero _
  have h1 : Fits W 1 := hfit.of_le (by omega)
  have h5 : Fits W a := hfit.of_le (by omega)
  let start := ((x.set cursor 0).set one 1).set negative a
  have hs : ExecWithin (B := .standard) W
      (ram[ cursor ← #0; one ← #1; negative ← #a ]) x start 3 := by
    ram_eval [start, h0, h1, h5, cursor, one, negative, Fin.mk.injEq]
  let I (y : Data 18) : Prop :=
    y.regs modulus = 2 ^ p ∧ y.regs destination = b ∧
    y.regs limit = as.length ∧ y.regs one = 1 ∧ y.regs negative = a ∧
    y.regs cursor ≤ as.length ∧
    y.mem = projectedPrefix x.mem b as (y.regs cursor) ∧
    y.regs initial = x.regs initial
  have hi : I start := by
    simp [I, start, projectedPrefix_zero, hn, hb, hq,
      modulus, destination, limit, one, negative, cursor, initial]
  have step (y : Data 18) (hy : I y) (ht : (Cond.lt cursor limit).Holds y) :
      ∃ z, ExecWithin W (projectBody back) y z 8 ∧ I z ∧
        as.length - z.regs cursor < as.length - y.regs cursor := by
    obtain ⟨yn, yb, yq, yo, yg, yj, ym, yi⟩ := hy
    have hj : y.regs cursor < as.length := by simpa only [Cond.holds_lt, yq] using ht
    let j := y.regs cursor
    let r := if back then as.length - 1 - j else j
    have hr : r < as.length := by dsimp [r]; split <;> omega
    have hread : y.mem (a + r) % 2 ^ p = as[j]!.toNat := by
      rw [ym]
      have hout : ¬(b ≤ a + r ∧ a + r < b + y.regs cursor) := by omega
      simp only [projectedPrefix, hout, ↓reduceIte]
      simpa only [r, j, getElem!_pos as j hj] using hinput j hj
    have haddr : Fits W (a + r) := hfit.of_le (by omega)
    have hdest : Fits W (b + j) := hfit.of_le (by omega)
    have hnext : Fits W (j + 1) := hfit.of_le (by omega)
    have hvalue : Fits W as[j]!.toNat := hfit.of_le (by have := as[j]!.isLt; omega)
    let loaded := y.set address (a + r)
    have heRead : ExecWithin (B := .standard) W
        (if back then ram[ address ← limit - cursor; address ← address - one;
          address ← address + negative ] else ram[ address ← cursor + negative ])
        y loaded 3 := by
      cases back
      · have he : a + r = y.regs cursor + a := by simp [r, j, Nat.add_comm]
        have hf : Fits W (y.regs cursor + a) := he ▸ haddr
        have hrun : ExecWithin (B := .standard) W
            (ram[ address ← cursor + negative ]) y loaded 1 := by
          ram_eval [loaded, yo, yg, hf, he, address, cursor, negative, Fin.mk.injEq]
        exact hrun.mono (by omega)
      · have hr' : r = as.length - y.regs cursor - 1 := by dsimp [r, j]; omega
        have hf : Fits W (as.length - y.regs cursor) := hfit.of_le (by omega)
        have hf' : Fits W (as.length - y.regs cursor - 1) := hfit.of_le (by omega)
        have hf'' : Fits W (as.length - y.regs cursor - 1 + a) := by
          simpa only [hr', Nat.add_comm] using haddr
        have hrun : ExecWithin (B := .standard) W
            (ram[ address ← limit - cursor; address ← address - one;
              address ← address + negative ]) y
            (y.set address (as.length - y.regs cursor)
              |>.set address (as.length - y.regs cursor - 1)
              |>.set address (as.length - y.regs cursor - 1 + a)) 3 := by
          ram_eval [yq, yo, yg, hf, hf', hf'', address, limit, cursor, one,
            negative, Fin.mk.injEq]
        simpa [loaded, hr', Nat.add_comm, Data.set] using hrun
    let z := loaded.set operand (y.mem (a + r))
      |>.set operand as[j]!.toNat |>.set address (b + j)
      |>.write (b + j) as[j]!.toNat |>.set cursor (j + 1)
    have heWrite : ExecWithin (B := .standard) W
        (ram[ operand ← *address; operand ← operand % modulus;
          address ← destination + cursor; *address ← operand; cursor ← cursor + one ])
        loaded z 5 := by
      ram_eval [z, loaded, hread, yn, yb, yo, hvalue, hdest, hnext,
        address, operand, modulus, destination, cursor, one, j, Fin.mk.injEq]
    refine ⟨z, heRead.seq heWrite, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals simp +decide only [z, loaded, Data.set_regs, Data.set_mem,
        Data.write_regs, Data.write_mem, Function.update_apply,
        modulus, destination, limit, one, negative, cursor, initial, address, operand,
        ↓reduceIte]
      · exact yn
      · exact yb
      · exact yq
      · exact yo
      · exact yg
      · exact Nat.succ_le_iff.mpr hj
      · simpa only [j, ym] using (projectedPrefix_succ x.mem b as (y.regs cursor)).symm
      · exact yi
    · simp only [z, Data.set_regs, Function.update_self, j]
      omega
  obtain ⟨y, he, hy, ht⟩ := ExecWithin.loop_invariant I
    (fun y => as.length - y.regs cursor) step hi
  have hj : y.regs cursor = as.length := by
    have := hy.2.2.2.2.2.1
    simp only [Cond.holds_lt, hy.2.2.1] at ht
    omega
  refine ⟨y, ?_, ?_, hy.1, hy.2.1, hy.2.2.1, hj, hy.2.2.2.2.2.2.2, hy.2.2.2.1⟩
  · apply (hs.seq he).mono
    have hz : start.regs cursor = 0 := by simp [start, cursor, one, negative]
    rw [hz]
    omega
  · simpa only [hj] using hy.2.2.2.2.2.2.1

end Cslib.Cryptanalysis.AddXNOR.Native.Counters
