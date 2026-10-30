/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Signed.ArrayArithmetic.Program

/-!
# Charged native pointwise signed array operations

Both operands are read before the output store, so exact input/output aliases are valid.
The enclosing array loop is responsible for proving that earlier stores preserve unread
input cells. The numerical premises here concern only the two original values and addresses.
-/

public section

namespace Cslib.WordRAM.Signed.ArrayArithmetic

open Cslib.WordRAM Cslib.WordRAM.Signed

private theorem exec_arithmetic {w : ℕ} (subtract : Bool) (x : Data 16) (a b : ℤ)
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (hla : x.regs left = encode a) (hlb : x.regs right = encode b) :
    ∃ y, ExecWithin (w + 2) (arithmetic subtract) x y 17 ∧
      y.regs result = encode (if subtract then a - b else a + b) ∧ Frame x y := by
  cases subtract with
  | false =>
    obtain ⟨y, he, hr, hf⟩ := Signed.exec_add ha hb x hla hlb
    exact ⟨y, he.mono (by decide), hr, hf⟩
  | true =>
    obtain ⟨y, he, hr, hf⟩ := Signed.exec_subtract ha hb x hla hlb
    exact ⟨y, he, hr, hf⟩

/-- The arithmetic workspace, index and address are the only body modifications. -/
@[expose] def BodyLocal (i : Fin 16) : Prop :=
  i.val < 9 ∨ i = Reg.index ∨ i = Reg.address

instance (i : Fin 16) : Decidable (BodyLocal i) :=
  inferInstanceAs (Decidable (i.val < 9 ∨ i = Reg.index ∨ i = Reg.address))

private theorem body_preserves (subtract : Bool) (i : Fin 16) :
    ¬BodyLocal i → (body subtract).Preserves i := by
  cases subtract <;> decide +kernel +revert

/-- One complete pointwise operation costs at most twenty-four native instructions. -/
theorem exec_body {w : ℕ} (subtract : Bool) (x : Data 16) (a b : ℤ)
    (ha : GenericRAM.Signed.Fits w a) (hb : GenericRAM.Signed.Fits w b)
    (hA : x.mem (x.regs Reg.inputA + x.regs Reg.index) = encode a)
    (hB : x.mem (x.regs Reg.inputB + x.regs Reg.index) = encode b)
    (haddrA : Fits (w + 2) (x.regs Reg.inputA + x.regs Reg.index))
    (haddrB : Fits (w + 2) (x.regs Reg.inputB + x.regs Reg.index))
    (haddrOut : Fits (w + 2) (x.regs Reg.output + x.regs Reg.index))
    (hnext : Fits (w + 2) (x.regs Reg.index + 1)) (hone : x.regs Reg.one = 1) :
    ∃ y, ExecWithin (w + 2) (body subtract) x y 24 ∧
      y.regs Reg.index = x.regs Reg.index + 1 ∧
      y.mem = Function.update x.mem (x.regs Reg.output + x.regs Reg.index)
        (encode (if subtract then a - b else a + b)) ∧
      ∀ i, ¬BodyLocal i → y.regs i = x.regs i := by
  let z := (((x.set Reg.address (x.regs Reg.inputA + x.regs Reg.index)).set left
    (encode a)).set Reg.address (x.regs Reg.inputB + x.regs Reg.index)).set right (encode b)
  have hz : ExecWithin (w + 2) load x z 4 := by
    ram_eval [load, z, hA, hB, haddrA, haddrB, Reg.inputA, Reg.inputB, Reg.index,
      Reg.address, left, right, Fin.mk.injEq]
  obtain ⟨t, ht, htresult, htframe⟩ := exec_arithmetic subtract z a b ha hb
    (by simp +decide [z, left, right, Reg.address]) (by simp [z])
  have hprefix : ExecWithin (w + 2) (.seq load (arithmetic subtract)) x t 21 := hz.seq ht
  have hri : t.regs Reg.index = x.regs Reg.index :=
    hprefix.regs_eq (by cases subtract <;> decide)
  have hro : t.regs Reg.output = x.regs Reg.output :=
    hprefix.regs_eq (by cases subtract <;> decide)
  have hr1 : t.regs Reg.one = 1 :=
    (hprefix.regs_eq (by cases subtract <;> decide)).trans hone
  let y := ((t.set Reg.address (x.regs Reg.output + x.regs Reg.index)).write
    (x.regs Reg.output + x.regs Reg.index)
    (encode (if subtract then a - b else a + b))).set Reg.index (x.regs Reg.index + 1)
  have hfinish : ExecWithin (w + 2) finish t y 3 := by
    ram_eval [finish, y, hri, hro, hr1, htresult, haddrOut, hnext, Reg.address,
      Reg.index, Reg.output, Reg.one, result, Fin.mk.injEq]
  have he : ExecWithin (w + 2) (body subtract) x y 24 := hz.seq (ht.seq hfinish)
  refine ⟨y, he, by simp [y], ?_, fun i hi => he.regs_eq (body_preserves subtract i hi)⟩
  simpa only [y, Data.set_mem, Data.write_mem, z] using
    congrArg (fun mem => Function.update mem (x.regs Reg.output + x.regs Reg.index)
      (encode (if subtract then a - b else a + b))) htframe.1

end Cslib.WordRAM.Signed.ArrayArithmetic
