/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
import Mathlib.Tactic.FinCases

/-!
# Reading a fusion-node header

All eighteen words of an internal-node header are loaded by a fixed straight-line program.
The constant offsets and their address additions are charged. Query-dependent array accesses
are separate from this header load.

## Main definitions

* `ReadHeaderProgram.pointer`, `ReadHeaderProgram.offset`, `ReadHeaderProgram.address`: register
  assignments for the header reader.
* `ReadHeaderProgram.word`: three-instruction block loading a single header word.
* `ReadHeaderProgram.code`: the 54-instruction header reader.
* `ReadHeaderProgram.result`: output state after loading all eighteen header words.

## Main results

* `ReadHeaderProgram.exec`: checked execution with an explicit header-address bound.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.ReadHeaderProgram

open Cslib.WordRAM

/-- Base address of the record, preserved. -/
abbrev pointer : Fin 21 := 0
/-- Constant-offset scratch. -/
abbrev offset : Fin 21 := 19
/-- Address scratch. -/
abbrev address : Fin 21 := 20

/-- Load header word `i` into register `i+1`. -/
def word (i : Fin 18) : Code .standard 21 :=
  let dst : Fin 21 := ⟨i.val + 1, by omega⟩
  ram[ offset ← #i.val; address ← pointer + offset; dst ← *address ]

/-- All eighteen header loads, with their constant offsets and address additions. -/
def code : Code .standard 21 := ram[
  ⟪word ⟨0, by decide⟩⟫;
  ⟪word ⟨1, by decide⟩⟫;
  ⟪word ⟨2, by decide⟩⟫;
  ⟪word ⟨3, by decide⟩⟫;
  ⟪word ⟨4, by decide⟩⟫;
  ⟪word ⟨5, by decide⟩⟫;
  ⟪word ⟨6, by decide⟩⟫;
  ⟪word ⟨7, by decide⟩⟫;
  ⟪word ⟨8, by decide⟩⟫;
  ⟪word ⟨9, by decide⟩⟫;
  ⟪word ⟨10, by decide⟩⟫;
  ⟪word ⟨11, by decide⟩⟫;
  ⟪word ⟨12, by decide⟩⟫;
  ⟪word ⟨13, by decide⟩⟫;
  ⟪word ⟨14, by decide⟩⟫;
  ⟪word ⟨15, by decide⟩⟫;
  ⟪word ⟨16, by decide⟩⟫;
  ⟪word ⟨17, by decide⟩⟫ ]

/-- Output state after the eighteen loaded words. -/
def result (x : Data 21) : Data 21 :=
  (List.ofFn (fun i : Fin 18 => i)).foldl (fun z i =>
    ((z.set offset i.val).set address (x.regs pointer + i.val)).set
      ⟨i.val + 1, by omega⟩ (x.mem (x.regs pointer + i.val))) x

/-- All header words are read in 54 checked standard instructions, counting constants and
address additions. The address bound implies that all constant offsets fit as well. -/
theorem exec {w : ℕ} (x : Data 21) (ha : Fits w (x.regs pointer + 17)) :
    Exec w code x (result x) 54 := by
  have haddr (i : ℕ) (hi : i < 18) : Fits w (x.regs pointer + i) := ha.of_le (by omega)
  have hoff (i : ℕ) (hi : i < 18) : Fits w i := ha.of_le (by omega)
  ram_eval [code, word, result, List.ofFn_succ, List.ofFn_zero, List.foldl,
    Fin.val_zero, Fin.val_succ, Fin.val_mk, haddr, hoff]

/-- The record base and memory are preserved, and each output register contains its header word. -/
theorem result_spec (x : Data 21) :
    (result x).regs pointer = x.regs pointer ∧ (result x).mem = x.mem ∧
      ∀ i : Fin 18, (result x).regs ⟨i.val + 1, by omega⟩ = x.mem (x.regs pointer + i.val) := by
  constructor
  · simp +decide [result, pointer, offset, address, List.ofFn_succ, List.foldl]
  constructor
  · rfl
  intro i
  fin_cases i <;> simp +decide [result, pointer, offset, address, List.ofFn_succ, List.foldl]

end Cslib.Algorithms.WordRAM.FusionTree.ReadHeaderProgram
