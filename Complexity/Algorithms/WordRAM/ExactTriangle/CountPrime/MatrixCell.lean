/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.MatrixResidue
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Monomial

/-!
# Actual native padded coefficient-matrix cell

One cell executes its runtime division/remainder, actual spread-table reads and Morton
address arithmetic, both padding guards, real residue read when admitted, every coefficient
write and index increment. The table is constructed by the preceding native spread stage;
this internal execution theorem describes its current-state meaning for composition.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime

open Cslib.WordRAM

/-- Exactly the row/column/scan/coefficient/address temporaries used by a matrix cell. -/
@[expose] def MatrixLocal (i : Fin 128) : Prop := 87 ≤ i.val ∧ i.val ≤ 97

instance (i : Fin 128) : Decidable (MatrixLocal i) :=
  inferInstanceAs (Decidable (87 ≤ i.val ∧ i.val ≤ 97))

private theorem matrixStep_preserves (transpose : Bool) (i : Fin 128) (hi : ¬MatrixLocal i) :
    (matrixStep transpose).Preserves i := by
  cases transpose <;> decide +kernel +revert

/-- Construct one complete padded p-coefficient cell from actual current source/table words.
All address, division, comparison, coefficient and control fits follow from a numerical
envelope; no matrix cell, residue answer, table lookup or running time is supplied by an oracle. -/
theorem exec_matrixStep {w n p k source destination table i : ℕ}
    (transpose : Bool) (x : Data 128)
    (hn : x.regs Reg.side = n) (hp : x.regs Reg.modulus = p)
    (hN : x.regs Reg.paddedSide = 2 ^ k) (hindex : x.regs Reg.index = i) (hi : i < 4 ^ k)
    (hsrc : x.regs Reg.residueSource = source) (hdst : x.regs Reg.destination = destination)
    (ht : x.regs Reg.spread = table)
    (h0 : x.regs Reg.zero = 0) (h1 : x.regs Reg.one = 1) (h2 : x.regs Reg.two = 2)
    (htable : ∀ j < 2 ^ k, x.mem (table + j) = Nat.Morton.spread j)
    (hw : Fits w (destination + 4 ^ k * p + table + 4 ^ k + 2 ^ k +
      source + n * n + p + 16)) :
    ∃ y, ExecWithin w (matrixStep transpose) x y (7 * p + 22) ∧
      y.regs Reg.index = i + 1 ∧
      (∀ j < p, y.mem (destination + Nat.Morton.index (i / 2 ^ k) (i % 2 ^ k) * p + j) =
        if j = (if i / 2 ^ k < n ∧ i % 2 ^ k < n then x.mem (source +
          if transpose then i % 2 ^ k * n + i / 2 ^ k else i / 2 ^ k * n + i % 2 ^ k)
        else p) then 2 else 0) ∧
      (∀ d, (d < destination + Nat.Morton.index (i / 2 ^ k) (i % 2 ^ k) * p ∨
        destination + Nat.Morton.index (i / 2 ^ k) (i % 2 ^ k) * p + p ≤ d) →
        y.mem d = x.mem d) ∧
      ∀ r, ¬MatrixLocal r → y.regs r = x.regs r := by
  let N := 2 ^ k
  let row := i / N
  let col := i % N
  let position := Nat.Morton.index row col
  have hpos : 0 < N := by positivity
  have hsquare : N * N = 4 ^ k := by dsimp only [N]; rw [← mul_pow]; rfl
  have hrlt : row < N := (Nat.div_lt_iff_lt_mul hpos).mpr (by simpa only [hsquare] using hi)
  have hclt : col < N := Nat.mod_lt i hpos
  have hzlt : position < 4 ^ k := Nat.Morton.index_lt hrlt hclt
  have hmul := Nat.mul_le_mul_right p (Nat.succ_le_of_lt hzlt)
  rw [Nat.succ_mul] at hmul
  have fit (a : ℕ) (ha : a ≤ destination + 4 ^ k * p + table + 4 ^ k + N +
      source + n * n + p + 16) : Fits w a := hw.of_le ha
  let z := (x.set Reg.row row).set Reg.column col
  have coordinates : ExecWithin (B := .standard) w
      (ram[ Reg.row ← Reg.index / Reg.paddedSide; Reg.column ← Reg.index % Reg.paddedSide ])
      x z 2 := by
    ram_eval [z, row, col, hindex, hN, N, fit row (by omega), fit col (by omega),
      Reg.row, Reg.column, Reg.index, Reg.paddedSide]
  have zmeta (r : Fin 128) (hr : ¬MatrixLocal r) : z.regs r = x.regs r := by
    simp only [z, Data.set,
      Function.update_of_ne (show r ≠ Reg.row by intro he; subst r; exact hr (by decide)),
      Function.update_of_ne (show r ≠ Reg.column by intro he; subst r; exact hr (by decide))]
  obtain ⟨s, mortonRun, sm, spos, sr⟩ := exec_morton (k := k) z
    ((zmeta Reg.two (by decide)).trans h2)
    (by simpa +decide [z, Reg.row, Reg.column] using hrlt)
    (by simpa +decide [z, Reg.column] using hclt)
    (by simpa only [show z.mem = x.mem from rfl, zmeta Reg.spread (by decide), ht] using htable)
    (by rw [zmeta Reg.spread (by decide), ht]; exact hw.of_le (by omega))
  have smeta (r : Fin 128) (hr : ¬MatrixLocal r) : s.regs r = x.regs r :=
    (sr r (by intro he; subst r; exact hr (by decide))
      (by intro he; subst r; exact hr (by decide))
      (by intro he; subst r; exact hr (by decide))
      (by intro he; subst r; exact hr (by decide))).trans (zmeta r hr)
  have sposition : s.regs Reg.position = position := by
    simpa +decide [z, Reg.row, Reg.column] using spos
  have srow : s.regs Reg.row = row :=
    (sr Reg.row (by decide) (by decide) (by decide) (by decide)).trans (by
      simp +decide [z, Reg.row, Reg.column])
  have scol : s.regs Reg.column = col :=
    (sr Reg.column (by decide) (by decide) (by decide) (by decide)).trans (by
      simp +decide [z, Reg.column])
  have sindex : s.regs Reg.index = i :=
    (sr Reg.index (by decide) (by decide) (by decide) (by decide)).trans (by
      simpa +decide [z, Reg.index, Reg.row, Reg.column] using hindex)
  let block := destination + position * p
  let t := (s.set Reg.block (position * p)).set Reg.block block
  have blockRun : ExecWithin (B := .standard) w
      (ram[ Reg.block ← Reg.position * Reg.modulus;
        Reg.block ← Reg.destination + Reg.block ]) s t 2 := by
    ram_eval [t, block, sposition, (smeta Reg.modulus (by decide)).trans hp,
      (smeta Reg.destination (by decide)).trans hdst,
      fit (position * p) (by omega), fit block (by dsimp [block]; omega),
      Reg.block, Reg.position, Reg.modulus, Reg.destination]
  have tmeta (r : Fin 128) (hr : ¬MatrixLocal r) : t.regs r = x.regs r := by
    simpa only [t, Data.set,
      Function.update_of_ne (show r ≠ Reg.block by intro he; subst r; exact hr (by decide))]
      using smeta r hr
  have trow : t.regs Reg.row = row := by simpa +decide [t, Reg.row, Reg.block] using srow
  have tcol : t.regs Reg.column = col := by simpa +decide [t, Reg.column, Reg.block] using scol
  have tindex : t.regs Reg.index = i := by simpa +decide [t, Reg.index, Reg.block] using sindex
  have tm : t.mem = x.mem := sm
  obtain ⟨r, selectRun, rm, key, rr⟩ := exec_matrixResidue transpose t (by
    rw [tmeta Reg.residueSource (by decide), hsrc, tmeta Reg.side (by decide), hn,
      tmeta Reg.modulus (by decide), hp]
    exact hw.of_le (by omega))
  have rmeta (j : Fin 128) (hj : ¬MatrixLocal j) : r.regs j = x.regs j :=
    (rr j (by intro he; subst j; exact hj (by decide))
      (by intro he; subst j; exact hj (by decide))
      (by intro he; subst j; exact hj (by decide))).trans (tmeta j hj)
  have rblock : r.regs Reg.block = block :=
    (rr Reg.block (by decide) (by decide) (by decide)).trans (by simp [t])
  have rindex : r.regs Reg.index = i :=
    (rr Reg.index (by decide) (by decide) (by decide)).trans tindex
  have rmod : r.regs Reg.modulus = p := (rmeta Reg.modulus (by decide)).trans hp
  obtain ⟨s', writeRun, values, memory, regs⟩ := exec_writeCoefficients r
    ((rmeta Reg.zero (by decide)).trans h0) ((rmeta Reg.one (by decide)).trans h1)
    ((rmeta Reg.two (by decide)).trans h2)
    (by rw [rblock, rmod]; exact fit _ (by dsimp [block]; omega))
  have s'index : s'.regs Reg.index = i :=
    (regs Reg.index (by decide) (by decide)).trans rindex
  have s'one : s'.regs Reg.one = 1 :=
    (regs Reg.one (by decide) (by decide)).trans ((rmeta Reg.one (by decide)).trans h1)
  let y := s'.set Reg.index (i + 1)
  have increment : ExecWithin (B := .standard) w
      (ram[ Reg.index ← Reg.index + Reg.one ]) s' y 1 := by
    ram_eval [y, s'index, s'one, fit (i + 1) (by omega)]
  have he : ExecWithin w (matrixStep transpose) x y (7 * p + 22) :=
    (coordinates.seq (mortonRun.seq (blockRun.seq (selectRun.seq (writeRun.seq increment))))).mono
      (by rw [rmod]; omega)
  refine ⟨y, he, ?_, ?_, ?_, fun j hj => he.regs_eq (matrixStep_preserves transpose j hj)⟩
  · rfl
  · intro j hj
    have hv := values j (by simpa only [rmod] using hj)
    simpa only [y, Data.set_mem, rblock, block, key, trow, tcol,
      tmeta Reg.side (by decide), hn, tmeta Reg.residueSource (by decide), hsrc,
      tmeta Reg.modulus (by decide), hp, tm, rm] using hv
  · intro d hd
    exact (memory d (by simpa only [rblock, rmod, block] using hd)).trans (by rw [rm, tm])

end Cslib.Algorithms.WordRAM.ExactTriangle.CountPrime
