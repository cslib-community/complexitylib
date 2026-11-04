/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Program

/-!
# Native compact-table reads and signed arithmetic

The descriptor loads, leaf multiplication and child accumulation execute the actual
fixed-register program. The bounds include address arithmetic and operand loads as
well as the existing signed kernels. None of these routines changes memory.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

/-- Registers written while loading one three-word descriptor. -/
@[expose] def RecordLocal (i : Fin registers) : Prop :=
  i = Reg.address ∨ i = Reg.completion ∨ i = Reg.stars ∨ i = Reg.starPower

instance (i : Fin registers) : Decidable (RecordLocal i) :=
  inferInstanceAs (Decidable (i = Reg.address ∨ i = Reg.completion ∨
    i = Reg.stars ∨ i = Reg.starPower))

private theorem loadRecord_preserves (i : Fin registers) :
    ¬RecordLocal i → loadRecord.Preserves i := by decide +revert

/-- Read the three actual descriptor cells within seven native instructions. -/
theorem exec_loadRecord {w R j c e p : ℕ} (x : Data registers)
    (hR : x.regs Reg.records = R) (hj : x.regs Reg.current = j)
    (h1 : x.regs Reg.one = 1) (h3 : x.regs Reg.three = 3)
    (hc : x.mem (R + j * 3) = c) (he : x.mem (R + j * 3 + 1) = e)
    (hp : x.mem (R + j * 3 + 2) = p) (hfit : Fits w (R + j * 3 + 2)) :
    ∃ y, ExecWithin w loadRecord x y 7 ∧ y.regs Reg.completion = c ∧
      y.regs Reg.stars = e ∧ y.regs Reg.starPower = p ∧ y.mem = x.mem ∧
      (∀ i, ¬RecordLocal i → y.regs i = x.regs i) := by
  have hf0 : Fits w (j * 3) := hfit.of_le (by omega)
  have hf1 : Fits w (R + j * 3) := hfit.of_le (by omega)
  have hf2 : Fits w (R + j * 3 + 1) := hfit.of_le (by omega)
  have hf3 : Fits w (R + j * 3 + 1 + 1) := by simpa only [Nat.add_assoc] using hfit
  have hp' : x.mem (R + j * 3 + 1 + 1) = p := by simpa only [Nat.add_assoc] using hp
  let y := (((((((x.set Reg.address (j * 3)).set Reg.address (R + j * 3)).set
    Reg.completion c).set Reg.address (R + j * 3 + 1)).set Reg.stars e).set
    Reg.address (R + j * 3 + 1 + 1)).set Reg.starPower p)
  have hy : ExecWithin w loadRecord x y 7 := by
    ram_eval [loadRecord, y, hR, hj, h1, h3, hc, he, hp', hf0, hf1, hf2, hf3,
      Reg.address, Reg.records, Reg.current, Reg.one, Reg.three, Reg.completion,
      Reg.stars, Reg.starPower, Fin.mk.injEq]
  exact ⟨y, hy, by simp [y, Reg.completion, Reg.starPower, Reg.stars, Reg.address],
    by simp [y, Reg.stars, Reg.starPower, Reg.address], by simp [y], rfl,
    fun i hi => hy.regs_eq (loadRecord_preserves i hi)⟩

/-- The signed workspace, indexed address and returned accumulator. -/
@[expose] def ProductLocal (i : Fin registers) : Prop :=
  i.val < 9 ∨ i = Reg.address ∨ i = Reg.accumulator

instance (i : Fin registers) : Decidable (ProductLocal i) :=
  inferInstanceAs (Decidable (i.val < 9 ∨ i = Reg.address ∨ i = Reg.accumulator))

private theorem leafProduct_preserves (i : Fin registers) :
    ¬ProductLocal i → leafProduct.Preserves i := by decide +revert

/-- Actual encoded leaf loads, signed multiplication and result delivery cost nineteen. -/
theorem exec_leafProduct {w : ℕ} {a b : ℤ} (ha : GenericRAM.Signed.Fits w a)
    (hb : GenericRAM.Signed.Fits w b) (hab : GenericRAM.Signed.Fits w (a * b))
    (x : Data registers)
    (hleft : x.mem (x.regs Reg.arrayA + x.regs Reg.completion) = Signed.encode a)
    (hright : x.mem (x.regs Reg.arrayB + x.regs Reg.completion) = Signed.encode b)
    (hp : Fits (w + 2) (x.regs Reg.arrayA + x.regs Reg.completion))
    (hq : Fits (w + 2) (x.regs Reg.arrayB + x.regs Reg.completion)) :
    ∃ y, ExecWithin (w + 2) leafProduct x y 19 ∧
      y.regs Reg.accumulator = Signed.encode (a * b) ∧ y.mem = x.mem ∧
      (∀ i, ¬ProductLocal i → y.regs i = x.regs i) := by
  let z := ((((x.set Reg.address (x.regs Reg.arrayA + x.regs Reg.completion)).set
    Signed.left (Signed.encode a)).set Reg.address
    (x.regs Reg.arrayB + x.regs Reg.completion)).set Signed.right (Signed.encode b))
  have hload : ExecWithin (w + 2) leafLoad x z 4 := by
    ram_eval [leafLoad, z, hleft, hright, hp, hq, Reg.address, Reg.arrayA,
      Reg.arrayB, Reg.completion, Signed.left, Signed.right, Fin.mk.injEq]
  obtain ⟨u, hu, hproduct, hframe⟩ := Signed.exec_multiply (r := 55) ha hb hab z
    (by simp +decide [z, Signed.left, Signed.right, Reg.address]) (by simp [z])
  have hproduct' : u.regs Signed.result = Signed.encode (a * b) := hproduct
  let y := u.set Reg.accumulator (Signed.encode (a * b))
  have hfinish : ExecWithin (w + 2) leafFinish u y 1 := by
    ram_eval [leafFinish, y, hproduct']
  have hy : ExecWithin (w + 2) leafProduct x y 19 := hload.seq (hu.seq hfinish)
  exact ⟨y, hy, by simp [y], hframe.1,
    fun i hi => hy.regs_eq (leafProduct_preserves i hi)⟩

/-- The signed workspace and native directory/value-address temporaries of one child. -/
@[expose] def ChildLocal (i : Fin registers) : Prop :=
  i.val < 9 ∨ i = Reg.temporary ∨ i = Reg.childCode ∨ i = Reg.childSlot ∨
    i = Reg.address ∨ i = Reg.childRank ∨ i = Reg.accumulator ∨ i = Reg.term

instance (i : Fin registers) : Decidable (ChildLocal i) :=
  inferInstanceAs (Decidable (i.val < 9 ∨ i = Reg.temporary ∨ i = Reg.childCode ∨
    i = Reg.childSlot ∨ i = Reg.address ∨ i = Reg.childRank ∨
    i = Reg.accumulator ∨ i = Reg.term))

private theorem addChild_preserves (i : Fin registers) :
    ¬ChildLocal i → addChild.Preserves i := by decide +revert

/-- Read the actual offset-one directory rank and child value, add it, and advance the term.
The caller supplies mathematical readback equalities, not an execution or time contract. -/
theorem exec_addChild {w D V c e T p d r : ℕ} {a b : ℤ}
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (x : Data registers)
    (hD : x.regs Reg.directory = D) (hV : x.regs Reg.values = V)
    (hc : x.regs Reg.completion = c) (he : x.regs Reg.stars = e)
    (hT : x.regs Reg.span = T) (hTpos : 0 < T) (hp : x.regs Reg.starPower = p)
    (hd : x.regs Reg.term = d) (hacc : x.regs Reg.accumulator = Signed.encode a)
    (h9 : x.regs Reg.nine = 9) (h1 : x.regs Reg.one = 1)
    (hrank : x.mem (D + ((e - 1) * T + (c - (9 - d) * p))) = r + 1)
    (hvalue : x.mem (V + r) = Signed.encode b)
    (hfit : Fits (w + 2) (D + V + c + e * T + 10 * p + r + d + 20)) :
    ∃ y, ExecWithin (w + 2) addChild x y 29 ∧
      y.regs Reg.accumulator = Signed.encode (a + b) ∧ y.regs Reg.term = d + 1 ∧
      y.mem = x.mem ∧ (∀ i, ¬ChildLocal i → y.regs i = x.regs i) := by
  let cc := c - (9 - d) * p
  let cs := (e - 1) * T + cc
  have hmp : (9 - d) * p ≤ 10 * p := Nat.mul_le_mul_right p (by omega)
  have hmt : (e - 1) * T ≤ e * T := Nat.mul_le_mul_right T (Nat.sub_le ..)
  have heT : e ≤ e * T := by simpa only [Nat.mul_one] using
    (Nat.mul_le_mul_left e hTpos)
  have hcc : cc ≤ c := Nat.sub_le ..
  have hcs : cs ≤ e * T + c := Nat.add_le_add hmt hcc
  have hf9 : Fits (w + 2) (9 - d) := hfit.of_le (by omega)
  have hfmp : Fits (w + 2) ((9 - d) * p) := hfit.of_le (by omega)
  have hfcc : Fits (w + 2) cc := hfit.of_le (by omega)
  have hfe : Fits (w + 2) (e - 1) := hfit.of_le (by omega)
  have hfmt : Fits (w + 2) ((e - 1) * T) := hfit.of_le (by omega)
  have hfcs : Fits (w + 2) cs := hfit.of_le (by omega)
  have hfD : Fits (w + 2) (D + cs) := hfit.of_le (by omega)
  have hfr : Fits (w + 2) r := hfit.of_le (by omega)
  have hfV : Fits (w + 2) (V + r) := hfit.of_le (by omega)
  have hfd : Fits (w + 2) (d + 1) := hfit.of_le (by omega)
  let z := ((((((((((((x.set Reg.temporary (9 - d)).set Reg.temporary ((9 - d) * p)).set
    Reg.childCode cc).set Reg.childSlot (e - 1)).set Reg.childSlot ((e - 1) * T)).set
    Reg.childSlot cs).set Reg.address (D + cs)).set Reg.childRank (r + 1)).set
    Reg.childRank r).set Reg.address (V + r)).set Signed.right (Signed.encode b)).set
    Signed.left (Signed.encode a))
  have hload : ExecWithin (w + 2) childLoad x z 12 := by
    ram_eval [childLoad, z, cc, cs, hD, hV, hc, he, hT, hp, hd, hacc, h9, h1,
      hrank, hvalue, hf9, hfmp, hfcc, hfe, hfmt, hfcs, hfD, hfr, hfV,
      Reg.temporary, Reg.childCode, Reg.childSlot, Reg.address, Reg.childRank,
      Reg.completion, Reg.stars, Reg.span, Reg.starPower, Reg.directory, Reg.values,
      Reg.term, Reg.accumulator, Reg.nine, Reg.one, Signed.left, Signed.right,
      Fin.mk.injEq, Nat.add_sub_cancel]
  obtain ⟨u, hu, hsum, hframe⟩ := Signed.exec_add (r := 55) ha hb z
    (by simp [z]) (by simp +decide [z, Signed.left, Signed.right])
  have hsum' : u.regs Signed.result = Signed.encode (a + b) := hsum
  have hud : u.regs Reg.term = d := by
    rw [hframe.2 _ (Or.inr (by decide))]
    simpa +decide [z, Reg.term, Reg.temporary, Reg.childCode, Reg.childSlot,
      Reg.address, Reg.childRank, Signed.left, Signed.right] using hd
  have hu1 : u.regs Reg.one = 1 := by
    rw [hframe.2 _ (Or.inr (by decide))]
    simpa +decide [z, Reg.one, Reg.temporary, Reg.childCode, Reg.childSlot,
      Reg.address, Reg.childRank, Signed.left, Signed.right] using h1
  let y := (u.set Reg.accumulator (Signed.encode (a + b))).set Reg.term (d + 1)
  have hfinish : ExecWithin (w + 2) childFinish u y 2 := by
    ram_eval [childFinish, y, hud, hu1, hsum', hfd, Reg.term, Reg.accumulator,
      Reg.one, Fin.mk.injEq]
  have hy : ExecWithin (w + 2) addChild x y 29 := hload.seq (hu.seq hfinish)
  exact ⟨y, hy, by simp [y, Reg.accumulator, Reg.term], by simp [y], hframe.1,
    fun i hi => hy.regs_eq (addChild_preserves i hi)⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
