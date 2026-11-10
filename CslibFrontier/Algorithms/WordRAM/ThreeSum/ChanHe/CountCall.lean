/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.Count
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import Mathlib.Tactic.FinCases

/-!
# Charged calls to Chan–He collision counting

The prime searches keep their parameters outside the counting workspace. Each of the three
set arrays has a fixed pair of base/length registers and its own result register. This module
charges argument setup and result delivery as well as the complete native counting routine.

## Main definitions

* `CountCall.program`: a counting call on one of the three input arrays.

## Main results

* `CountCall.exec`: exact collision count, memory frame and preserved caller registers.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CountCall

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Counting workspace in a larger, fixed register file. -/
def registers (i : Fin 28) : Fin 64 := i.castAdd 36

private theorem registers_injective : Function.Injective registers :=
  Fin.castAdd_injective _ _

/-- Length register for the selected set. -/
def length (j : Fin 3) : Fin 64 := ⟨28 + 2 * j.val, by omega⟩
/-- Base register for the selected set. -/
def source (j : Fin 3) : Fin 64 := ⟨29 + 2 * j.val, by omega⟩
/-- Residue scratch base. -/
abbrev scratch : Fin 64 := 34
/-- Histogram base. -/
abbrev histogram : Fin 64 := 35
/-- Encoded positive modulus. -/
abbrev modulus : Fin 64 := 36
/-- Collision-count output register for the selected set. -/
def result (j : Fin 3) : Fin 64 := ⟨37 + j.val, by omega⟩

/-- Counting input base register. -/
abbrev countSource : Fin 64 := registers Count.src
/-- Counting scratch base register. -/
abbrev countScratch : Fin 64 := registers Count.scratch
/-- Counting input length register. -/
abbrev countLength : Fin 64 := registers Count.len
/-- Counting encoded-modulus register. -/
abbrev countModulus : Fin 64 := registers Count.modulus
/-- Counting histogram base register. -/
abbrev countHistogram : Fin 64 := registers Count.dst
/-- Counting result register. -/
abbrev countTotal : Fin 64 := registers Count.total

/-- Five runtime register copies deliver the counting arguments. -/
def prepare (j : Fin 3) : Code .standard 64 :=
  let input := source j
  let n := length j
  ram[ countSource ← input; countScratch ← scratch; countLength ← n;
    countModulus ← modulus; countHistogram ← histogram ]

/-- A complete native count call, including argument and result copies. -/
def program (j : Fin 3) : Code .standard 64 :=
  .seq (prepare j) (.seq (Count.program.rename registers) (.op (.copy (result j) countTotal)))

/-- A native count call costs `34n+5M+24`, including five argument copies and one result copy.
The mathematical input is an injective array enumeration, as required by the existing set-based
Chan–He collision count. All registers outside the workspace, except its chosen result, survive. -/
theorem exec {w M : ℕ} (j : Fin 3) (x : Data 64) (values : ℕ → ℤ) (hM : 0 < M)
    (hmod : GenericRAM.Signed.Fits w (M : ℤ))
    (hmodreg : x.regs modulus = encode (M : ℤ))
    (hfit : ∀ i < x.regs (length j), GenericRAM.Signed.Fits w (values i))
    (hs : Fits (w + 2) (x.regs (source j) + x.regs (length j)))
    (hk : Fits (w + 2) (x.regs scratch + x.regs (length j)))
    (hd : Fits (w + 2) (x.regs histogram + M))
    (ht : Fits (w + 2) (x.regs (length j) * x.regs (length j) + x.regs (length j) + 1))
    (hsk : x.regs (source j) + x.regs (length j) ≤ x.regs scratch)
    (hkd : x.regs scratch + x.regs (length j) ≤ x.regs histogram)
    (hinput : ∀ i < x.regs (length j),
      x.mem (x.regs (source j) + i) = encode (values i))
    (hinj : Set.InjOn values (↑(Finset.range (x.regs (length j))) : Set ℕ)) :
    ∃ y, ExecWithin (w + 2) (program j) x y (34 * x.regs (length j) + 5 * M + 24) ∧
      y.mem = Count.memory x.mem values (x.regs (length j)) M
        (x.regs scratch) (x.regs histogram) ∧
      y.regs (result j) = Cslib.Algorithms.ThreeSum.ChanHe.coll
        ((Finset.range (x.regs (length j))).image values) M ∧
      ∀ i, 28 ≤ i.val → i ≠ result j → y.regs i = x.regs i := by
  let q := ((((x.set countSource (x.regs (source j))).set countScratch (x.regs scratch)).set
    countLength (x.regs (length j))).set countModulus (x.regs modulus)).set
    countHistogram (x.regs histogram)
  have hprep : ExecWithin (w + 2) (prepare j) x q 5 := by
    fin_cases j <;>
      ram_eval [prepare, q, source, length, registers, countSource, countScratch,
        countLength, countModulus, countHistogram, scratch, histogram, modulus,
        Count.src, Count.scratch, Count.len, Count.modulus, Count.dst, Fin.mk.injEq]
  unfold program
  refine WP.exists_execWithin (WP.seq (WP.of_execWithin hprep (WP.seq ?_)))
  wram_call (Count.exec_coll _ values hM hmod
    (by wram_simp [q, Data.comap_regs, hmodreg])
    (by wram_simp [q, Data.comap_regs]; exact hfit)
    (by wram_simp [q, Data.comap_regs]; exact hs)
    (by wram_simp [q, Data.comap_regs]; exact hk)
    (by wram_simp [q, Data.comap_regs]; exact hd)
    (by wram_simp [q, Data.comap_regs]; exact ht)
    (by wram_simp [q, Data.comap_regs]; exact hsk)
    (by wram_simp [q, Data.comap_regs]; exact hkd)
    (by wram_simp [q, Data.comap_regs, Data.comap_mem]; exact hinput)
    (by wram_simp [q, Data.comap_regs]; exact hinj)) renamed registers_injective
    with y ⟨⟨ham, hav, _⟩, hframe⟩
  wram_exec
  wram_simp [q, Data.comap_regs, Data.comap_mem] at ham hav ⊢
  refine ⟨by omega, ham, hav, fun i hi hres => ?_⟩
  have hbank (k : Fin 28) : registers k ≠ i :=
    Fin.ne_of_val_ne (by simp only [registers, Fin.val_castAdd]; omega)
  wram_simp [hres]
  rw [hframe i hbank]
  wram_simp [q, hbank]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CountCall
