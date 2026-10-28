/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.CountFrame
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
def registers (i : Fin 28) : Fin 64 := ⟨i.val, by omega⟩

private theorem registers_injective : Function.Injective registers := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 64 => i.val) h

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

private theorem extend_outside (a : Data 28) (x : Data 64) (i : Fin 64) (hi : 28 ≤ i.val) :
    (a.extend registers x).regs i = x.regs i := by
  change Function.extend registers a.regs x.regs i = x.regs i
  apply Function.extend_apply'
  rintro ⟨j, hj⟩
  have := congrArg Fin.val hj
  dsimp [registers] at this
  omega

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
  have hq (i : Fin 64) (hi : 28 ≤ i.val) : q.regs i = x.regs i := by
    have hne (k : Fin 64) (hk : k.val < 28) : i ≠ k := by
      intro h
      have := congrArg Fin.val h
      omega
    simp only [q, Data.set_regs, Function.update_of_ne (hne countSource (by decide)),
      Function.update_of_ne (hne countScratch (by decide)),
      Function.update_of_ne (hne countLength (by decide)),
      Function.update_of_ne (hne countModulus (by decide)),
      Function.update_of_ne (hne countHistogram (by decide))]
  have hqs : (q.comap registers).regs Count.src = x.regs (source j) := by
    simp +decide [q, registers, countSource, countScratch, countLength, countModulus,
      countHistogram, Count.src, Count.scratch, Count.len, Count.modulus, Count.dst]
  have hqn : (q.comap registers).regs Count.len = x.regs (length j) := by
    simp +decide [q, registers, countSource, countScratch, countLength, countModulus,
      countHistogram, Count.src, Count.scratch, Count.len, Count.modulus, Count.dst]
  have hqk : (q.comap registers).regs Count.scratch = x.regs scratch := by
    simp +decide [q, registers, countSource, countScratch, countLength, countModulus,
      countHistogram, Count.src, Count.scratch, Count.len, Count.modulus, Count.dst]
  have hqd : (q.comap registers).regs Count.dst = x.regs histogram := by
    simp +decide [q, registers, countSource, countScratch, countLength, countModulus,
      countHistogram, Count.src, Count.scratch, Count.len, Count.modulus, Count.dst]
  have hqm : (q.comap registers).regs Count.modulus = x.regs modulus := by
    simp +decide [q, registers, countSource, countScratch, countLength, countModulus,
      countHistogram, Count.src, Count.scratch, Count.len, Count.modulus, Count.dst]
  obtain ⟨a, ha, ham, hav, _⟩ := Count.exec_coll (q.comap registers) values hM hmod
    (hqm.trans hmodreg) (by simpa only [hqn] using hfit)
    (by simpa only [hqs, hqn] using hs) (by simpa only [hqk, hqn] using hk)
    (by simpa only [hqd] using hd) (by simpa only [hqn] using ht)
    (by simpa only [hqs, hqn, hqk] using hsk)
    (by simpa only [hqk, hqn, hqd] using hkd)
    (by
      change ∀ i < (q.comap registers).regs Count.len,
        x.mem ((q.comap registers).regs Count.src + i) = encode (values i)
      simpa only [hqn, hqs] using hinput)
    (by simpa only [hqn] using hinj)
  let y := a.extend registers q
  have hy : ExecWithin (w + 2) (Count.program.rename registers) q y
      (34 * x.regs (length j) + 5 * M + 18) := by
    simpa only [hqn] using ha.rename registers_injective
  have hyt : y.regs countTotal = a.regs Count.total := by
    change Function.extend registers a.regs q.regs (registers Count.total) = _
    exact registers_injective.extend_apply _ _ _
  refine ⟨y.set (result j) (y.regs countTotal), ?_, ?_, ?_, ?_⟩
  · exact (hprep.seq (hy.seq ExecWithin.copy)).mono (by omega)
  · change a.mem = _
    have hqmem : q.mem = x.mem := rfl
    simpa only [Data.comap_mem, hqmem, hqn, hqk, hqd] using ham
  · simp only [Data.set_regs, Function.update_self, hyt]
    simpa only [hqn] using hav
  · intro i hi hne
    rw [Data.set_regs, Function.update_of_ne hne, extend_outside a q i hi, hq i hi]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.CountCall
