/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Multiword.Bank
public import Complexity.Computability.WordRAM.Multiword.Transfer
public import Complexity.Computability.WordRAM.Multiword.Shift

/-!
# Scalar operations and variable shifts on multiword banks

Scalar operations assemble both operands before writing the destination, so the destination
may coincide with either source. Their inputs and result must fit the physical word width.
Variable right shifts assemble only the shift amount; the shifted input remains multiword.

## Main definitions

* `Bank.scalarLeft`, `Bank.scalarRight`, `Bank.scalarResult`: physical registers four, five, and
  six used for assembled scalar operands and results.
* `Bank.scalar`: a checked physical binary operation between bank entries.
* `Bank.shift`: a variable right shift into a distinct bank entry.

## Main results

* `Bank.exec_scalar`: exact execution in 133 instructions, preserving other entries and memory.
* `Bank.exec_shift`: execution within 123 instructions, preserving other entries and memory.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Bank

open Workspace

variable {n : ℕ}

/-- Physical register four stores the assembled left operand or shift amount. -/
abbrev scalarLeft : Fin (capacity n + 4) := ⟨4, by dsimp [capacity]; omega⟩
/-- Physical register five stores the assembled right operand. -/
abbrev scalarRight : Fin (capacity n + 4) := ⟨5, by dsimp [capacity]; omega⟩
/-- Physical register six stores the checked scalar result. -/
abbrev scalarResult : Fin (capacity n + 4) := ⟨6, by dsimp [capacity]; omega⟩

private theorem value_preserved {w : ℕ} {x y : Data (capacity n + 4)} (j : Fin n)
    (hp : ∀ i, 44 ≤ i.val → y.regs i = x.regs i) :
    value (radix w) y (regs j) = value (radix w) x (regs j) := by
  unfold value
  congr 1
  exact List.map_congr_left fun i hi => hp i (by have := mem_regs hi; omega)

/-- Assemble into physical registers four and five, compute in register six, and split the
checked result into the destination. Both inputs are read before any bank entry is written. -/
def scalar (f : BinOp) (a b d : Fin n) : Code .standard (capacity n + 4) :=
  .seq (Transfer.assemble (regs a) scalarLeft)
    (.seq (Transfer.assemble (regs b) scalarRight)
      (.seq (.op (.bin f scalarResult scalarLeft scalarRight))
        (Transfer.split scalarResult (regs d))))

/-- Scalar operations compile to exactly 133 instructions, independently of word width. -/
theorem size_scalar (f : BinOp) (a b d : Fin n) : (scalar f a b d).size = 133 := by
  simp [scalar, Transfer.size_assemble, Transfer.size_split, length_regs]

/-- Checked scalar arithmetic permits either source to coincide with the destination. -/
theorem exec_scalar {w : ℕ} (hw : 2 ≤ w) (f : BinOp) (a b d : Fin n)
    (x : Data (capacity n + 4)) {v : Fin n → ℕ} (hx : Encodes w x v)
    (hfa : Fits w (v a)) (hfb : Fits w (v b))
    (hresult : Fits w (f.eval (v a) (v b))) :
    ∃ y, Exec w (scalar f a b d) x y 133 ∧
      Encodes w y (Function.update v d (f.eval (v a) (v b))) ∧ y.mem = x.mem := by
  obtain ⟨u, heu, hua, huf, hup⟩ := Transfer.exec_assemble hw (regs a) scalarLeft
    (digit_regs a) x (by rwa [(hx a).2])
  have hup' (i : Fin (capacity n + 4)) (hi : 44 ≤ i.val) : u.regs i = x.regs i :=
    hup i (by dsimp [IsDigit]; omega) (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
  have hub : value (radix w) u (regs b) = v b :=
    (value_preserved b hup').trans (hx b).2
  obtain ⟨t, het, htb, htf, htp⟩ := Transfer.exec_assemble hw (regs b) scalarRight
    (digit_regs b) u (by rwa [hub])
  have hta : t.regs scalarLeft = v a := by
    rw [htp scalarLeft (by simp [IsDigit]) (by simp [Fin.ext_iff]), hua, (hx a).2]
  have htb' : t.regs scalarRight = v b := htb.trans hub
  let z := t.set scalarResult (f.eval (t.regs scalarLeft) (t.regs scalarRight))
  have hzv : z.regs scalarResult = f.eval (v a) (v b) := by
    simp only [z, Data.set_regs, Function.update_self, hta, htb']
  have hez : Exec w (.op (.bin f scalarResult scalarLeft scalarRight)) t z 1 :=
    Exec.bin (by rwa [hta, htb'])
  obtain ⟨y, hey, hyb, hyv, hyf, hyp⟩ := Transfer.exec_split_eighteen hw scalarResult
    (regs d) (length_regs d) (by simp [IsDigit]) (digit_regs d) (nodup_regs d) z
    (by rwa [hzv])
  refine ⟨y, ?_, encodes_update hx d _ hyb (hyv.trans hzv) ?_, ?_⟩
  · simpa only [scalar, length_regs] using heu.seq (het.seq (hez.seq hey))
  · intro i hi hid
    have hd : IsDigit i := by dsimp [IsDigit]; omega
    have hl : i ≠ scalarLeft := by intro h; have := congrArg Fin.val h; dsimp at this; omega
    have hr : i ≠ scalarRight := by intro h; have := congrArg Fin.val h; dsimp at this; omega
    have hs : i ≠ scalarResult := by intro h; have := congrArg Fin.val h; dsimp at this; omega
    rw [hyp i hd hid, show z.regs i = t.regs i from Function.update_of_ne hs _ _,
      htp i hd hr, hup i hd hl]
  · exact hyf.1.trans (htf.1.trans huf.1)

/-- Assemble the scalar shift amount in physical register four, then shift the multiword input.
The destination must be distinct from the input, but may contain the original shift amount. -/
def shift (w : ℕ) (a b d : Fin n) : Code .standard (capacity n + 4) :=
  .seq (Transfer.assemble (regs b) scalarLeft) (Shift.program w (regs a) (regs d) scalarLeft)

/-- The compiled size is independent of physical word width. -/
theorem size_shift (w : ℕ) (a b d : Fin n) : (shift w a b d).size = 1014 := by
  simp only [shift, Code.size, Transfer.size_assemble, length_regs,
    Shift.size_program_eighteen w (regs a) (regs d) scalarLeft (length_regs a) (length_regs d)]

/-- Multiword right shifts require only the shift amount to fit a physical word. -/
theorem exec_shift {w : ℕ} (hw : 2 ≤ w) (a b d : Fin n) (hda : d ≠ a)
    (x : Data (capacity n + 4)) {v : Fin n → ℕ} (hx : Encodes w x v)
    (hfb : Fits w (v b)) :
    ∃ y, ExecWithin w (shift w a b d) x y 123 ∧
      Encodes w y (Function.update v d (v a >>> v b)) ∧ y.mem = x.mem := by
  obtain ⟨u, heu, hub, huf, hup⟩ := Transfer.exec_assemble hw (regs b) scalarLeft
    (digit_regs b) x (by rwa [(hx b).2])
  have hup' (i : Fin (capacity n + 4)) (hi : 44 ≤ i.val) : u.regs i = x.regs i :=
    hup i (by dsimp [IsDigit]; omega) (by intro h; have := congrArg Fin.val h; dsimp at this; omega)
  have hua : Bounded (radix w) u (regs a) := by
    intro i hi
    rw [hup' i (by have := mem_regs hi; omega)]
    exact (hx a).1 i hi
  have hnot : scalarLeft ∉ regs d := by
    intro h
    have := mem_regs h
    dsimp at this
    omega
  obtain ⟨y, hey, hyb, hyv, hyf, hyp⟩ := Shift.exec_eighteen hw (regs a) (regs d)
    scalarLeft (length_regs a) (length_regs d) (digit_regs a) (digit_regs d)
    (by simp [IsDigit]) (nodup_regs d) (disjoint_regs hda) hnot u hua
    (by rwa [hub, (hx b).2])
  rw [value_preserved a hup', (hx a).2, hub, (hx b).2] at hyv
  refine ⟨y, ?_, encodes_update hx d _ hyb hyv ?_, hyf.1.trans huf.1⟩
  · simpa only [shift, length_regs] using heu.within.seq hey
  · intro i hi hid
    rw [hyp i (by dsimp [IsDigit]; omega) hid, hup' i hi]

end Cslib.WordRAM.Multiword.Bank

end
