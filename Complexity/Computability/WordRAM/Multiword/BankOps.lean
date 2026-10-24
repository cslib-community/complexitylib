/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Multiword.Bank
public import Complexity.Computability.WordRAM.Multiword.Bitwise
public import Complexity.Computability.WordRAM.Multiword.Transfer

/-!
# Checked operations on multiword register banks

The constants are installed as explicit half-word digits. Boolean operations execute one
standard instruction per digit. Scalar arithmetic is provided separately in `BankScalar`.

## Main definitions

* `Bank.constant`: installation of a width-dependent constant.
* `Bank.boolean`: limbwise Boolean operations.

## Main results

* `Bank.exec_constant`, `Bank.exec_boolean`: execution and preservation of the other bank entries.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Bank

open Workspace
open Schoolbook (registers)

variable {n : ℕ}

/-- Canonical fixed-length digits; no computation depending on the run-time input is
performed by the constant installer. -/
def constantDigits (w z : ℕ) : List ℕ :=
  List.ofFn fun i : Fin 18 => z / radix w ^ i.val % radix w

private theorem constantDigits_bounded {w : ℕ} (hw : 2 ≤ w) (z : ℕ) :
    ∀ c ∈ constantDigits w z, c < radix w := by
  intro c hc
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
  exact Nat.mod_lt _ (by have := one_lt_radix hw; omega)

private theorem value_constantDigits {w z : ℕ} (hz : z < radix w ^ 18) :
    Nat.ofDigits (radix w) (constantDigits w z) = z := by
  obtain ⟨cs, hcs, hval⟩ := Nat.exists_ofDigits_ofFn hz
  have he : (fun i : Fin 18 => z / radix w ^ i.val % radix w) = cs := by
    funext i
    rw [← hval]
    exact Nat.ofDigits_ofFn_div_mod cs hcs i
  rw [constantDigits, he, hval]

/-- Install an eighteen-digit constant, charging all eighteen constants and the final copy. -/
def constant (w z : ℕ) (d : Fin n) : Code .standard (capacity n + 4) :=
  Transfer.constants (regs d) (constantDigits w z)

theorem size_constant (w z : ℕ) (d : Fin n) : (constant w z d).size = 19 := by
  simpa only [constant, length_regs] using Transfer.size_constants (regs d)
    (constantDigits w z) (by simp [length_regs, constantDigits])

theorem exec_constant {w : ℕ} (hw : 2 ≤ w) (d : Fin n) (z : ℕ)
    (hz : z < 2 ^ (6 * w)) (x : Data (capacity n + 4))
    {v : Fin n → ℕ} (hx : Encodes w x v) :
    ∃ y, Exec w (constant w z d) x y 19 ∧
      Encodes w y (Function.update v d z) ∧ y.mem = x.mem ∧
      ∀ i ∉ regs d, y.regs i = x.regs i := by
  obtain ⟨y, he, hyb, hyv, hyf, hyp⟩ := Transfer.exec_digits hw (regs d)
    (constantDigits w z) (by simp [length_regs, constantDigits]) (nodup_regs d)
    (constantDigits_bounded hw z) x
  have hv := value_constantDigits (hz.trans_le (six_word_capacity hw))
  refine ⟨y, by simpa only [constant, length_regs] using he,
    encodes_update hx d z hyb (hyv.trans hv) (fun i _ hi => hyp i hi), hyf.1, hyp⟩

/-- A Boolean operation on two bank entries with a fresh destination. -/
def boolean (f : BinOp) (a b d : Fin n) : Code .standard (capacity n + 4) :=
  Bitwise.program f (regs a) (regs b) (regs d)

theorem size_boolean (f : BinOp) (a b d : Fin n) : (boolean f a b d).size = 19 := by
  simpa only [boolean, length_regs] using Bitwise.size_program f (regs a) (regs b)
    (regs d) (by rw [length_regs, length_regs]) (by rw [length_regs, length_regs])

theorem exec_boolean {w : ℕ} (hw : 2 ≤ w) {f : BinOp} (hf : Bitwise.Supported f)
    (a b d : Fin n) (hda : d ≠ a) (hdb : d ≠ b) (x : Data (capacity n + 4))
    {v : Fin n → ℕ} (hx : Encodes w x v) :
    ∃ y, Exec w (boolean f a b d) x y 19 ∧
      Encodes w y (Function.update v d (f.eval (v a) (v b))) ∧ y.mem = x.mem := by
  have hdis : List.Disjoint (regs d) (regs a ++ regs b) :=
    List.disjoint_append_right.mpr ⟨disjoint_regs hda, disjoint_regs hdb⟩
  obtain ⟨y, he, hyb, hyv, hyf, hyp⟩ := Bitwise.exec hw hf (regs a) (regs b) (regs d)
    (by rw [length_regs, length_regs]) (by rw [length_regs, length_regs])
    (fun i hi => by
      rcases List.mem_append.mp hi with hi | hi
      · exact digit_regs a i hi
      · exact digit_regs b i hi)
    (digit_regs d) (nodup_regs d) hdis x (hx a).1 (hx b).1
  rw [(hx a).2, (hx b).2] at hyv
  exact ⟨y, by simpa only [boolean, length_regs] using he,
    encodes_update hx d _ hyb hyv (fun i _ hi => hyp i hi), hyf.1⟩

/-- Physical register receiving the ordinary one-word input. -/
abbrev inputReg : Fin (capacity n + 4) := ⟨4, by dsimp [capacity]; omega⟩

/-- All bank digits, excluding the forty-four physical workspace registers. -/
def allRegs (n : ℕ) : List (Fin (capacity n + 4)) :=
  registers 40 (18 * n) (by dsimp [capacity]; omega)

private theorem mem_allRegs (j : Fin n) {i : Fin (capacity n + 4)} (hi : i ∈ regs j) :
    i ∈ allRegs n := by
  have hh := mem_regs hi
  apply List.mem_ofFn.mpr
  refine ⟨⟨i.val - 44, by dsimp [capacity]; omega⟩, ?_⟩
  apply Fin.ext
  dsimp
  omega

/-- Initialize every bank digit, charging one constant instruction per digit. -/
def clear (n : ℕ) : Code .standard (capacity n + 4) :=
  Transfer.constants (allRegs n) (List.replicate (18 * n) 0)

theorem size_clear (n : ℕ) : (clear n).size = 18 * n + 1 := by
  simpa only [clear, allRegs, registers, List.length_ofFn] using
    Transfer.size_constants (allRegs n) (List.replicate (18 * n) 0) (by
      simp only [allRegs, registers, List.length_ofFn, List.length_replicate])

/-- Clearing starts from arbitrary registers and memory, and preserves the physical input. -/
theorem exec_clear {w : ℕ} (hw : 2 ≤ w) (x : Data (capacity n + 4)) :
    ∃ y, Exec w (clear n) x y (18 * n + 1) ∧ Encodes w y (fun _ => 0) ∧
      y.mem = x.mem ∧ y.regs inputReg = x.regs inputReg := by
  have hnd : (allRegs n).Nodup := by
    apply List.nodup_ofFn_ofInjective
    intro a b hab
    apply Fin.ext
    have := congrArg Fin.val hab
    dsimp at this
    omega
  obtain ⟨y, he, hm, hf, hp⟩ := Transfer.exec_constants (w := w) (allRegs n)
    (List.replicate (18 * n) 0)
    (by simp only [allRegs, registers, List.length_ofFn, List.length_replicate]) hnd
    (by intro c hc; have := (List.mem_replicate.mp hc).2; subst c; exact fits_zero w) x
  have hzero (j : Fin n) (i : Fin (capacity n + 4)) (hi : i ∈ regs j) : y.regs i = 0 := by
    have hh : y.regs i ∈ (allRegs n).map y.regs :=
      List.mem_map.mpr ⟨i, mem_allRegs j hi, rfl⟩
    rw [hm] at hh
    exact (List.mem_replicate.mp hh).2
  refine ⟨y, by simpa only [clear, allRegs, registers, List.length_ofFn] using he,
    ?_, hf.1, hp inputReg ?_⟩
  · intro j
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [hzero j i hi]
      have := one_lt_radix hw
      omega
    · have hh := List.map_congr_left (g := fun _ => 0) (hzero j)
      have hmap : (regs j).map y.regs = List.replicate 18 0 := by
        simpa only [List.map_const', length_regs] using hh
      simp only [value, hmap, Nat.ofDigits_replicate_zero]
  · intro hi
    obtain ⟨i, heq⟩ := List.mem_ofFn.mp hi
    have hh := congrArg Fin.val heq
    dsimp only [inputReg] at hh
    dsimp at hh
    omega

/-- Load the sole input from the usual RAM input memory, then split it into a bank entry.
The input memory contains its length at address zero and its value at address one. -/
def input (d : Fin n) : Code .standard (capacity n + 4) :=
  .seq (ram[inputReg ← #1; inputReg ← *inputReg]) (Transfer.split inputReg (regs d))

theorem size_input (d : Fin n) : (input d).size = 46 := by
  simp only [input, Code.size, Transfer.size_split, length_regs]

/-- Input delivery and conversion are charged: two input instructions and forty-four
digit-conversion instructions. All remaining bank entries start at zero. -/
theorem exec_input {w z : ℕ} (hw : 2 ≤ w) (hz : Fits w z) (d : Fin n) :
    ∃ y, Exec w (input d) (Data.init [z]) y 46 ∧
      Encodes w y (Function.update (fun _ => 0) d z) ∧
      y.mem = (Data.init [z] : Data (capacity n + 4)).mem ∧ y.regs inputReg = z := by
  let u : Data (capacity n + 4) := ((Data.init [z]).set inputReg 1).set inputReg z
  have he : Exec (B := .standard) w (ram[inputReg ← #1; inputReg ← *inputReg])
      (Data.init [z]) u 2 := by
    ram_eval [u, fits_one (by omega : w ≠ 0), Data.init, inputReg]
  have hzero (i : Fin (capacity n + 4)) (hi : 44 ≤ i.val) : u.regs i = 0 := by
    have hine : i ≠ inputReg := by
      intro h
      have := congrArg Fin.val h
      dsimp only [inputReg] at this
      omega
    simp only [u, Data.set_regs, Function.update_of_ne hine, Data.init_regs]
  have hu : Encodes w u (fun _ => 0) := by
    intro j
    have hm : (regs j).map u.regs = List.replicate 18 0 := by
      have hh := List.map_congr_left (l := regs j)
        (g := fun _ => 0) (fun i hi => hzero i (by have := mem_regs hi; omega))
      simpa only [List.map_const', length_regs] using hh
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [hzero i (by have := mem_regs hi; omega)]
      have := one_lt_radix hw
      omega
    · simp only [value, hm, Nat.ofDigits_replicate_zero]
  have huz : u.regs inputReg = z := by simp [u]
  obtain ⟨y, hey, hyb, hyv, hyf, hyp⟩ := Transfer.exec_split_eighteen hw inputReg
    (regs d) (length_regs d) (by dsimp [IsDigit, inputReg]; omega)
    (digit_regs d) (nodup_regs d) u
    (by rwa [huz])
  rw [huz] at hyv
  have hnot : inputReg ∉ regs d := by
    intro hi
    have hh := mem_regs hi
    dsimp only [inputReg] at hh
    omega
  refine ⟨y, ?_, encodes_update hu d z hyb hyv ?_, hyf.1, ?_⟩
  · exact he.seq hey
  · intro i hi hid
    exact hyp i (by dsimp [IsDigit]; omega) hid
  · exact (hyp inputReg (by dsimp [IsDigit, inputReg]; omega) hnot).trans huz

end Cslib.WordRAM.Multiword.Bank

end
