/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.CyclicConvolution.Program
public import Complexity.Foundations.RingTheory.CyclicIntRing.Coefficients

/-!
# Charged native cyclic-coefficient multiplication and accumulation

These are internal execution APIs for the coefficient loop. Each term computes its cyclic
index, loads the actual operands, calls the native signed multiply and add blocks, and advances
the summation counter. Source-width premises for the operands and partial sum will be derived
from coefficient magnitude bounds by the enclosing loop; no arithmetic result is supplied
as an input to the program.
-/

public section

namespace Cslib.Algorithms.WordRAM.CyclicConvolution

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.CyclicIntRing (subIndex)

/-- The actual wrap comparison and both unsigned subtractions take at most three instructions. -/
theorem exec_selectPartner {w : ℕ} (x : Data 32)
    (hfit : Fits w (x.regs Reg.coefficient + x.regs Reg.length)) :
    ExecWithin w selectPartner x
      (x.set Reg.partner (subIndex (x.regs Reg.length)
        (x.regs Reg.coefficient) (x.regs Reg.index))) 3 := by
  by_cases h : x.regs Reg.coefficient < x.regs Reg.index
  · have hs : Fits w (x.regs Reg.coefficient + x.regs Reg.length -
        x.regs Reg.index) := hfit.of_le (Nat.sub_le ..)
    have he : ExecWithin w
        (ram[ Reg.partner ← Reg.coefficient + Reg.length;
          Reg.partner ← Reg.partner - Reg.index ]) x
        (x.set Reg.partner (x.regs Reg.coefficient + x.regs Reg.length -
          x.regs Reg.index)) 2 := by
      refine ⟨2, le_rfl, ?_⟩
      ram_eval [hfit, hs, Reg.partner, Reg.coefficient, Reg.length, Reg.index, Fin.mk.injEq,
        Data.set, Function.update_idem]
    simpa only [selectPartner, subIndex, show ¬x.regs Reg.index ≤
      x.regs Reg.coefficient from by omega, ↓reduceIte] using
        ExecWithin.branch_pos (cond := .lt Reg.coefficient Reg.index)
          (by simpa only [Cond.holds_lt] using h) he
  · have hs : Fits w (x.regs Reg.coefficient - x.regs Reg.index) :=
      hfit.of_le (by omega)
    have he : ExecWithin w
        (ram[ Reg.partner ← Reg.coefficient - Reg.index ]) x
        (x.set Reg.partner (x.regs Reg.coefficient - x.regs Reg.index)) 1 := by
      ram_eval [hs]
    simpa only [selectPartner, subIndex, show x.regs Reg.index ≤
      x.regs Reg.coefficient from by omega, ↓reduceIte] using
        ExecWithin.branch_neg (cond := .lt Reg.coefficient Reg.index)
          (by simpa only [Cond.holds_lt] using h) he

/-- Exactly the arithmetic scratch, cyclic partner, partial sum, address and inner counter. -/
def TermLocal (i : Fin 32) : Prop :=
  i.val < 9 ∨ i = Reg.partner ∨ i = Reg.accumulator ∨ i = Reg.address ∨ i = Reg.index

instance (i : Fin 32) : Decidable (TermLocal i) :=
  inferInstanceAs (Decidable
    (i.val < 9 ∨ i = Reg.partner ∨ i = Reg.accumulator ∨ i = Reg.address ∨ i = Reg.index))

private theorem term_preserves (i : Fin 32) :
    ¬TermLocal i → term.Preserves i := by decide +kernel +revert

/-- All index work, two loads, signed multiply/add and counter work take forty native
instructions. The memory is unchanged and every parameter register is preserved. -/
theorem exec_term {w : ℕ} (x : Data 32) (a b s : ℤ)
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (hp : GenericRAM.Signed.Fits w (a * b)) (hs : GenericRAM.Signed.Fits w s)
    (hwrap : Fits (w + 2) (x.regs Reg.coefficient + x.regs Reg.length))
    (haddrA : Fits (w + 2) (x.regs Reg.inputA + x.regs Reg.index))
    (haddrB : Fits (w + 2) (x.regs Reg.inputB +
      subIndex (x.regs Reg.length) (x.regs Reg.coefficient) (x.regs Reg.index)))
    (hnext : Fits (w + 2) (x.regs Reg.index + 1))
    (hreadA : x.mem (x.regs Reg.inputA + x.regs Reg.index) = encode a)
    (hreadB : x.mem (x.regs Reg.inputB +
      subIndex (x.regs Reg.length) (x.regs Reg.coefficient) (x.regs Reg.index)) = encode b)
    (hacc : x.regs Reg.accumulator = encode s) (hone : x.regs Reg.one = 1) :
    ∃ y, ExecWithin (w + 2) term x y 40 ∧
      y.regs Reg.accumulator = encode (s + a * b) ∧
      y.regs Reg.index = x.regs Reg.index + 1 ∧ y.mem = x.mem ∧
      ∀ i, ¬TermLocal i → y.regs i = x.regs i := by
  let j := subIndex (x.regs Reg.length) (x.regs Reg.coefficient) (x.regs Reg.index)
  let z := x.set Reg.partner j
  have hz : ExecWithin (w + 2) selectPartner x z 3 := exec_selectPartner x hwrap
  let u := (((z.set Reg.address (x.regs Reg.inputA + x.regs Reg.index)).set left
    (encode a)).set Reg.address (x.regs Reg.inputB + j)).set right (encode b)
  have hu : ExecWithin (w + 2) loadOperands z u 4 := by
    ram_eval [loadOperands, u, z, j, haddrA, haddrB, hreadA, hreadB,
      Reg.inputA, Reg.inputB, Reg.partner, Reg.address, Reg.index, left, right, Fin.mk.injEq]
  obtain ⟨v, hv, hvresult, hvframe⟩ := Signed.exec_multiply (r := 23) ha hb hp u
    (by simp +decide [u, left, right, Reg.address]) (by simp [u])
  have hprod : ExecWithin (w + 2) productTerm x v 21 := hz.seq (hu.seq hv)
  have hvs : v.regs Reg.accumulator = encode s :=
    (hprod.regs_eq (by decide : productTerm.Preserves Reg.accumulator)).trans hacc
  change v.regs result = encode (a * b) at hvresult
  let q := (v.set right (encode (a * b))).set left (encode s)
  have hq : ExecWithin (w + 2) addArguments v q 2 := by
    ram_eval [addArguments, q, hvresult, hvs, left, right, result, Reg.accumulator,
      Fin.mk.injEq]
  obtain ⟨t, ht, htresult, htframe⟩ := Signed.exec_add (r := 23) hs hp q
    (by simp [q]) (by simp +decide [q, left, right])
  have he : ExecWithin (w + 2) (.seq productTerm (.seq addArguments Signed.add)) x t 38 :=
    hprod.seq (hq.seq ht)
  have hti : t.regs Reg.index = x.regs Reg.index :=
    he.regs_eq (by decide)
  have hto : t.regs Reg.one = 1 := (he.regs_eq (by decide)).trans hone
  change t.regs result = encode (s + a * b) at htresult
  let y := (t.set Reg.accumulator (encode (s + a * b))).set Reg.index
    (x.regs Reg.index + 1)
  have hy : ExecWithin (w + 2) finishTerm t y 2 := by
    ram_eval [finishTerm, y, htresult, hti, hto, hnext, Reg.accumulator, Reg.index,
      Reg.one, result, Fin.mk.injEq]
  have hall : ExecWithin (w + 2) term x y 40 := hprod.seq (hq.seq (ht.seq hy))
  refine ⟨y, hall, ?_, ?_, ?_, fun i hi => hall.regs_eq (term_preserves i hi)⟩
  · simp +decide [y, Reg.accumulator, Reg.index]
  · simp [y]
  · exact htframe.1.trans hvframe.1

end Cslib.Algorithms.WordRAM.CyclicConvolution
