/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Turing.ListOutput
import Complexity.Computability.WordRAM.Copy

/-!
# Word-RAM list outputs and their Turing-machine simulation

The length-prefixed output convention and halt parking on concrete programs, then two list-valued
programs transferred to Turing-machine polynomial time. The one-instruction program returning
address `0` outputs its input array, through the headline theorem. A copying program writes the
input to a fresh block after it, with its length in front, and returns that block's address,
through an explicit width schedule.
-/

namespace ComplexityTests.WordRAMListOutput

open Cslib.WordRAM Turing.MultiTapeTM

/-! ## The convention -/

/-- The array at address `0` of a memory `[3, 7, 9, 0, …]`: three words, the last one never
written. -/
example : outputList (fun a => [3, 7, 9].getD a 0) 0 = [7, 9, 0] := by decide

/-- The initial memory holds the input as the array at address `0`. -/
example : outputList (Data.init [5, 7] : Data 1).mem 0 = [5, 7] := outputList_init _

/-- Parking: each `halt i` jumps to a self-loop at `p.length + i`; the halt of register `1` is
parked at label `2 + 1`. -/
example : Program.parkHalts ([.op (.const 0 3), .halt 1] : Program .standard 2) =
    [.op (.const 0 3), .jump 3, .jump 2, .jump 3] := rfl

/-! ## The identity: return address `0` -/

/-- Return address `0`, where the input array is stored. -/
def idProgram : Program .standard 1 := [.halt 0]

theorem idProgram_executesList (w : ℕ) (l : List ℕ) : ExecutesList w idProgram (.init l) l 1 :=
  ⟨_, 0, 0, .refl _, rfl, outputList_init l, rfl⟩

/-- A parked run of the identity reaches the self-loop and keeps the input array. -/
example (w : ℕ) (l : List ℕ) :
    ∃ (i : Fin 1) (x : Data 1), Runs w idProgram.parkHalts (.init l) ⟨1 + i, x⟩ 5 ∧
      outputList x.mem (x.regs i) = l :=
  (idProgram_executesList w l).runs_parkHalts (by omega)

/-- The identity on framed lists of binary words is polynomial-time, through the headline
theorem. -/
example : Turing.MultiTapeTM.ComputableInPolyTime (fun l : List ℕ => l) (encList encNat)
    (encList encNat) :=
  UniformComputableListInPolyTime.turingComputableInPolyTime checkedOp_polyTime
    (size := List.length)
    ⟨fun _ => 1, .const 1, 1, one_pos, 1, idProgram,
      fun l w _ _ => ⟨1, idProgram_executesList w l, le_rfl⟩⟩
    (PolyBounded.self.mono fun l => length_le_length_encList encNat l) (.id' (encIn := _))
    (PolyBounded.self.mono fun l => length_le_length_encList encNat l)

/-! ## Copying to a fresh block -/

section Copy

open ArrayCopy

/-- Copy the input array `1, …, n` to `n + 2, …, 2n + 1`, store `n` at `n + 1`, and leave the
address `n + 1` in register `addr`. -/
def copyCode : Code .standard 7 :=
  .seq ram[ addr ← #0; len ← *addr; src ← #1; one ← #1; dst ← src + len; dst ← dst + one ]
    (.seq ArrayCopy.program ram[ addr ← src + len; *addr ← len ])

/-- The copying program returns the address of the copy. -/
def copyProgram : Program .standard 7 := copyCode.program addr

/-- The copy of the input is the array at the returned address, within `7 n + 12` instructions,
whenever `2 n + 2` fits a word. -/
theorem copyCode_exec {w : ℕ} (l : List ℕ) (hw : 2 * l.length + 2 < 2 ^ w) :
    ∃ y, ExecWithin w copyCode (Data.init l) y (7 * l.length + 12) ∧
      outputList y.mem (y.regs addr) = l := by
  let x : Data 7 := Data.init l
  have h1 : Fits w 1 := fits_iff.mpr (by omega)
  have hn1 : Fits w (1 + l.length) := fits_iff.mpr (by omega)
  have hn2 : Fits w (1 + l.length + 1) := fits_iff.mpr (by omega)
  have hnn : Fits w (1 + l.length + 1 + l.length) := fits_iff.mpr (by omega)
  let u := (((((x.set addr 0).set len l.length).set src 1).set one 1).set dst
    (1 + l.length)).set dst (1 + l.length + 1)
  have hi : ExecWithin w
      (ram[ addr ← #0; len ← *addr; src ← #1; one ← #1; dst ← src + len; dst ← dst + one ])
      x u 6 := by
    ram_eval [u, x, Data.init_mem_zero, h1, hn1, hn2]
  have hus : u.regs src = 1 := by simp +decide [u]
  have hud : u.regs dst = 1 + l.length + 1 := by simp +decide [u]
  have hul : u.regs len = l.length := by simp +decide [u]
  have hum : u.mem = x.mem := by simp [u]
  obtain ⟨y, hy, hym, hys, -, hyl⟩ := ArrayCopy.exec u h1 (by rw [hus, hul]; exact hn1)
    (by rw [hud, hul]; exact hnn) (by rw [hus, hul, hud]; omega)
  let z := (y.set addr (1 + l.length)).write (1 + l.length) l.length
  have ht : ExecWithin w ram[ addr ← src + len; *addr ← len ] y z 2 := by
    ram_eval [z, hys, hyl, hus, hul, hn1]
  refine ⟨z, (hi.seq (hy.seq ht)).mono (by rw [hul]; omega), ?_⟩
  have hza : z.regs addr = 1 + l.length := by simp [z]
  rw [hza, outputList_eq_iff]
  refine ⟨by simp [z], fun i => ?_⟩
  have hi' : i.val < l.length := i.isLt
  change z.mem (1 + l.length + 1 + i.val) = l[i.val]
  simp only [z, Data.write_mem, Data.set_mem, Function.update_of_ne
    (show 1 + l.length + 1 + i.val ≠ 1 + l.length by omega), hym, hus, hud, hul]
  rw [ArrayCopy.copyPrefix_read hi', hum]
  change (Data.init l : Data 7).mem (1 + i.val) = l[i.val]
  rw [Nat.add_comm, Data.init_mem_succ]
  simp [List.getD_eq_getElem?_getD, hi']

/-- The copying program computes the identity on word lists, within `7 n + 13` instructions at
every width where `2 n + 2` fits. -/
theorem copyProgram_computesListInTime :
    copyProgram.ComputesListInTime (fun _ l => l) (fun l _ => 7 * l.length + 13)
      (fun l w => 2 * l.length + 2 < 2 ^ w) id :=
  copyCode.computesListInTime_program addr fun l _ hw _ => copyCode_exec l hw

/-- The copying program transfers to a polynomial-time Turing machine at the width schedule
`|encList encNat l| + 2`, which admits every input. -/
example : Turing.MultiTapeTM.ComputableInPolyTime (fun l : List ℕ => l) (encList encNat)
    (encList encNat) :=
  copyProgram_computesListInTime.turingComputableInPolyTime_of_width checkedOp_polyTime
    (width := fun l => (encList encNat l).length + 2)
    (Turing.MultiTapeTM.ComputableInPolyTime.unary_add'
      (Turing.MultiTapeTM.ComputableInPolyTime.encoding_length _) (.const 2))
    (fun l => by
      have h1 := length_le_length_encList encNat l
      have h2 := Nat.lt_two_pow_self (n := (encList encNat l).length)
      rw [Nat.pow_add]
      omega)
    (fun l => (inputFits_of_length_encList_le le_rfl).mono (by omega)) (.id' (encIn := _))
    (((PolyBounded.const 7).mul
      (PolyBounded.self.mono fun l => length_le_length_encList encNat l)).add (.const 13))
    (PolyBounded.self.mono fun l => length_le_length_encList encNat l)

end Copy

end ComplexityTests.WordRAMListOutput
