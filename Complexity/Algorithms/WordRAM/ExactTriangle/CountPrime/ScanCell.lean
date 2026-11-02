/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Access
public import Complexity.Computability.WordRAM.Signed.Encoding

/-!
# Actual selected-coefficient read and accumulation

This internal stage reads the computed AB residue, computes its additive inverse modulo p,
loads the actual cyclic-product coefficient and decodes its nonnegative canonical word.
The complete counter derives this readback from its real residue and Strassen executions.
No instruction performs a free coefficient lookup, signed decoding or summation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- The scan modifies only its result and the shared coordinate/address temporaries. -/
@[expose] def ScanLocal (j : Fin 128) : Prop := j = Reg.result ∨ 87 ≤ j.val ∧ j.val ≤ 97

instance (j : Fin 128) : Decidable (ScanLocal j) :=
  inferInstanceAs (Decidable (j = Reg.result ∨ 87 ≤ j.val ∧ j.val ≤ 97))

private theorem countStep_preserves (j : Fin 128) (hj : ¬ScanLocal j) :
    countStep.Preserves j := by decide +kernel +revert

/-- One actual selected coefficient, including the real zero/nonzero residue branch and
signed-to-unsigned division. The sum and all addresses fit by the displayed numerical bound. -/
theorem exec_countStep {w n p k i r value total : ℕ} (x : Data 128)
    (hn : x.regs Reg.side = n) (hp : x.regs Reg.modulus = p)
    (hi : x.regs Reg.index = i) (hlt : i < n * n) (hpadding : n ≤ 2 ^ k)
    (hr : x.mem (x.regs Reg.residueAB + i) = r) (hrlt : r < p)
    (hvalue : x.mem (x.regs Reg.matrixR + Nat.Morton.index (i / n) (i % n) * p +
      (if r = 0 then 0 else p - r)) = encode (value : ℤ))
    (hbound : value ≤ n) (hresult : x.regs Reg.result = total) (htotal : total ≤ i * n)
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1) (h2 : x.regs Reg.two = 2)
    (htable : ∀ j < 2 ^ k, x.mem (x.regs Reg.spread + j) = Nat.Morton.spread j)
    (hw : Fits w (x.regs Reg.spread + x.regs Reg.residueAB + x.regs Reg.matrixR +
      4 ^ k * p + 4 ^ k + 2 ^ k + n * n * n + n * n + p + 16)) :
    ∃ y, ExecWithin w countStep x y 20 ∧ y.mem = x.mem ∧
      y.regs Reg.index = i + 1 ∧ y.regs Reg.result = total + value ∧
      ∀ j, ¬ScanLocal j → y.regs j = x.regs j := by
  have hnpos : 0 < n := by nlinarith
  have hrow : i / n < n := (Nat.div_lt_iff_lt_mul hnpos).mpr hlt
  have hcol : i % n < n := Nat.mod_lt _ hnpos
  have hposition := Nat.Morton.index_lt (hrow.trans_le hpadding) (hcol.trans_le hpadding)
  have hprod := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hposition)
  rw [Nat.succ_mul] at hprod
  let key := if r = 0 then 0 else p - r
  have hkey : key < p := by dsimp only [key]; split_ifs <;> omega
  have hsum : total + value ≤ n * n * n := by
    have he := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at he
    omega
  have fit (a : ℕ) (ha : a ≤ x.regs Reg.spread + x.regs Reg.residueAB +
      x.regs Reg.matrixR + 4 ^ k * p + 4 ^ k + 2 ^ k + n * n * n + n * n + p + 16) :
      Fits w a := hw.of_le ha
  let z := (x.set Reg.row (i / n)).set Reg.column (i % n)
  have coordinates : ExecWithin (B := .standard) w
      (ram[ Reg.row ← Reg.index / Reg.side; Reg.column ← Reg.index % Reg.side ]) x z 2 := by
    ram_eval [z, hi, hn, fit (i / n) (by omega), fit (i % n) (by omega),
      Reg.row, Reg.column, Reg.index, Reg.side]
  have zregs (j : Fin 128) (hj : j ≠ Reg.row) (hc : j ≠ Reg.column) :
      z.regs j = x.regs j := by simp only [z, Data.set, Function.update_of_ne hj,
        Function.update_of_ne hc]
  obtain ⟨s, hm, sm, sp, sr⟩ := exec_morton (k := k) z
    ((zregs _ (by decide) (by decide)).trans h2)
    (by simpa +decide [z, Reg.row, Reg.column] using hrow.trans_le hpadding)
    (by simpa +decide [z, Reg.column] using hcol.trans_le hpadding)
    (by simpa only [show z.mem = x.mem from rfl, zregs Reg.spread (by decide) (by decide)]
      using htable)
    (by rw [zregs Reg.spread (by decide) (by decide)]; exact fit _ (by omega))
  have keep (j : Fin 128) (ha : j ≠ Reg.address) (hb : j ≠ Reg.rowSpread)
      (hc : j ≠ Reg.columnSpread) (hd : j ≠ Reg.position)
      (he : j ≠ Reg.row) (hf : j ≠ Reg.column) : s.regs j = x.regs j :=
    (sr j ha hb hc hd).trans (zregs j he hf)
  have spos : s.regs Reg.position = Nat.Morton.index (i / n) (i % n) := by
    simpa +decide [z, Reg.row, Reg.column] using sp
  have si := (keep Reg.index (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).trans hi
  have sa := keep Reg.residueAB (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  let t := ((s.set Reg.address (x.regs Reg.residueAB + i)).set Reg.residue r).set Reg.residue key
  have read : ExecWithin (B := .standard) w
      (ram[ Reg.address ← Reg.residueAB + Reg.index; Reg.residue ← *Reg.address;
        if Reg.residue = Reg.zero then [ Reg.residue ← #0 ]
        else [ Reg.residue ← Reg.modulus - Reg.residue ] ]) s t 5 := by
    have smod := (keep Reg.modulus (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans hp
    have szero := (keep Reg.zero (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h0
    by_cases hz : r = 0
    · ram_eval [t, z, key, hz, si, sa, sm, hr, szero, smod,
        fit (x.regs Reg.residueAB + i) (by omega), fits_zero w,
        Reg.residueAB, Reg.index, Reg.address, Reg.residue, Reg.zero, Reg.modulus]
    · ram_eval [t, z, key, hz, si, sa, sm, hr, szero, smod,
        fit (x.regs Reg.residueAB + i) (by omega), fit (p - r) (by omega),
        Reg.residueAB, Reg.index, Reg.address, Reg.residue, Reg.zero, Reg.modulus]
  let position := Nat.Morton.index (i / n) (i % n)
  let addr := x.regs Reg.matrixR + position * p + key
  let y := (((((((t.set Reg.block (position * p)).set Reg.address
    (x.regs Reg.matrixR + position * p)).set Reg.address addr).set Reg.temporary
    (encode (value : ℤ))).set Reg.temporary value).set Reg.result (total + value)).set
    Reg.index (i + 1))
  have suffix : ExecWithin (B := .standard) w
      (ram[ Reg.block ← Reg.position * Reg.modulus;
        Reg.address ← Reg.matrixR + Reg.block; Reg.address ← Reg.address + Reg.residue;
        Reg.temporary ← *Reg.address; Reg.temporary ← Reg.temporary / Reg.two;
        Reg.result ← Reg.result + Reg.temporary; Reg.index ← Reg.index + Reg.one ]) t y 7 := by
    have kv : encode (value : ℤ) / 2 = value := by simp [encode_div_two]
    ram_eval [t, y, z, key, position, addr, spos, sm, hvalue, kv, si,
      keep Reg.modulus (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hp,
      keep Reg.matrixR (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      keep Reg.two (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h2,
      keep Reg.one (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h1,
      keep Reg.result (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide), hresult,
      fit (position * p) (by dsimp [position]; omega),
      fit (x.regs Reg.matrixR + position * p) (by dsimp [position]; omega),
      fit addr (by dsimp [addr, position]; omega), fit value (by omega),
      fit (total + value) (by omega), fit (i + 1) (by omega),
      Reg.block, Reg.position, Reg.modulus, Reg.matrixR, Reg.address, Reg.residue,
      Reg.temporary, Reg.two, Reg.result, Reg.index, Reg.one]
  have he : ExecWithin w countStep x y 20 := coordinates.seq (hm.seq (read.seq suffix))
  exact ⟨y, he, sm, rfl, rfl, fun j hj => he.regs_eq (countStep_preserves j hj)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
