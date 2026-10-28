/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.Frontend.Model
public import Complexity.Computability.WordRAM.Notation

/-!
# Native selection of canonical signed keys

All arithmetic is unsigned. The sign bit and magnitude are decoded explicitly, the label
is formed by addition or subtraction, and its two digits are computed with native shifts and
remainders. The repeated-value case doubles the key and subtracts its original sign bit.

## Main definitions

* `Select.program`: concrete selection and transformation instructions.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Frontend

open Cslib.WordRAM

namespace Select

/-- Magnitude bound, followed by two bit positions, selected digit and scan mode. -/
abbrev magnitude : Fin 48 := 0
@[inherit_doc magnitude] abbrev beta : Fin 48 := 1
@[inherit_doc magnitude] abbrev beta' : Fin 48 := 2
@[inherit_doc magnitude] abbrev digit : Fin 48 := 3
@[inherit_doc magnitude] abbrev mode : Fin 48 := 4
/-- Input key; replaced by its selected output value. -/
abbrev key : Fin 48 := 5
/-- Full input multiplicity, read without truncation. -/
abbrev count : Fin 48 := 6
/-- Small constants installed by the scan. -/
abbrev zero : Fin 48 := 7
@[inherit_doc zero] abbrev one : Fin 48 := 8
@[inherit_doc zero] abbrev two : Fin 48 := 9
@[inherit_doc zero] abbrev three : Fin 48 := 10
@[inherit_doc zero] abbrev four : Fin 48 := 11
@[inherit_doc zero] abbrev five : Fin 48 := 12
/-- Scratch registers for decoding and label digits. -/
abbrev sign : Fin 48 := 13
@[inherit_doc sign] abbrev label : Fin 48 := 14
@[inherit_doc sign] abbrev bitA : Fin 48 := 15
@[inherit_doc sign] abbrev bitB : Fin 48 := 16
/-- Selection flag, either zero or one. -/
abbrev take : Fin 48 := 17
/-- Magnitude temporary. -/
abbrev absolute : Fin 48 := 18

/-- Explicit native sign/magnitude decoding, shifted label and binary digit computation. -/
def labels : Code .standard 48 := ram[
  sign ← key % two; absolute ← key / two; label ← magnitude + magnitude;
  if sign = zero then [ label ← label + absolute ] else [ label ← label - absolute ];
  bitA ← label >>> beta; bitA ← bitA % two;
  bitB ← label >>> beta'; bitB ← bitB % two ]

/-- A no-op used by unsuccessful selections. -/
def skip : Code .standard 48 := ram[ take ← take ]

/-- Select one of the six finite scan modes and perform the repeated-value transformation. -/
def choose : Code .standard 48 := ram[
  take ← #0;
  if mode = zero then [
    if bitA = digit then [ take ← one ] else [ ⟪skip⟫ ]
  ] else [ if mode = one then [
    if bitA = digit then [ ⟪skip⟫ ] else [
      if bitB = zero then [ take ← one ] else [ ⟪skip⟫ ] ]
  ] else [ if mode = two then [
    if bitA = digit then [ ⟪skip⟫ ] else [
      if bitB = one then [ take ← one ] else [ ⟪skip⟫ ] ]
  ] else [ if mode = three then [
    if key = zero then [ ⟪skip⟫ ] else [
      if count < two then [ ⟪skip⟫ ] else [ take ← one ] ];
    key ← key + key; key ← key - sign
  ] else [ if mode = four then [
    if key = zero then [
      if count < three then [ ⟪skip⟫ ] else [ take ← one ]
    ] else [ ⟪skip⟫ ]
  ] else [ if mode = five then [ take ← one ] else [ ⟪skip⟫ ] ] ] ] ] ] ]

/-- Every decoding, arithmetic, branch and selection instruction is part of this code. -/
def program : Code .standard 48 := .seq labels choose

/-- This scalar program never reads the physical word width. -/
theorem not_readsWidth : ¬program.ReadsWidth := by decide

/-- Registers below the decoding scratch are preserved by label calculation. -/
theorem labels_preserves (j : Fin 48) (hj : j.val ≤ 12) : labels.Preserves j := by
  have hne (k : Fin 48) (hk : 13 ≤ k.val) : (some k : Option (Fin 48)) ≠ some j := by
    intro h
    have := congrArg Fin.val (Option.some.inj h)
    omega
  simp only [labels, Code.Preserves, Op.dest]
  exact ⟨hne sign (by decide), hne absolute (by decide), hne label (by decide),
    ⟨hne label (by decide), hne label (by decide)⟩, hne bitA (by decide),
    hne bitA (by decide), hne bitB (by decide), hne bitB (by decide)⟩

/-- Selection preserves all caller parameters, constants and scan registers. -/
theorem preserves (j : Fin 48) (hj : (j.val ≤ 12 ∧ j.val ≠ 5) ∨ 19 ≤ j.val) :
    program.Preserves j := by
  have hne (k : Fin 48) (hk : k.val = 5 ∨ 13 ≤ k.val ∧ k.val ≤ 18) :
      (some k : Option (Fin 48)) ≠ some j := by
    intro h
    have := congrArg Fin.val (Option.some.inj h)
    omega
  simp only [program, labels, choose, skip, Code.Preserves, Op.bin, Op.dest]
  repeat' constructor
  all_goals exact hne _ (by decide)

/-- Decoding and both binary digits cost at most eleven native instructions. -/
theorem labels_exec {w : ℕ} (x : Data 48)
    (hz : x.regs zero = 0) (h2 : x.regs two = 2)
    (hkey : Fits w (x.regs key))
    (habs : x.regs key / 2 ≤ 2 * x.regs magnitude)
    (hfit : Fits w (4 * x.regs magnitude + 2)) :
    ∃ y, ExecWithin w labels x y 11 ∧
      y.regs sign = x.regs key % 2 ∧
      y.regs label = Math.label (x.regs magnitude) (x.regs key) ∧
      y.regs bitA = (Math.label (x.regs magnitude) (x.regs key) >>> x.regs beta) % 2 ∧
      y.regs bitB = (Math.label (x.regs magnitude) (x.regs key) >>> x.regs beta') % 2 ∧
      y.mem = x.mem := by
  have fm := hkey.of_le (Nat.div_le_self _ 2)
  have fs := hfit.of_le (show x.regs key % 2 ≤ 4 * x.regs magnitude + 2 by omega)
  have fd := hfit.of_le (show x.regs magnitude + x.regs magnitude ≤
    4 * x.regs magnitude + 2 by omega)
  have fa := hfit.of_le (show x.regs magnitude + x.regs magnitude + x.regs key / 2 ≤
    4 * x.regs magnitude + 2 by omega)
  have fb := hfit.of_le (show x.regs magnitude + x.regs magnitude - x.regs key / 2 ≤
    4 * x.regs magnitude + 2 by omega)
  by_cases he : x.regs key % 2 = 0
  · have fsa := fa.of_le (Nat.shiftRight_le _ (x.regs beta))
    have fsb := fa.of_le (Nat.shiftRight_le _ (x.regs beta'))
    have fra := fsa.of_le (Nat.mod_le _ 2)
    have frb := fsb.of_le (Nat.mod_le _ 2)
    refine ⟨?_, ?run, ?_, ?_, ?_, ?_, ?_⟩
    case run => ram_eval [labels, hz, h2, hkey, fm, fs, fd, fa, fsa, fsb, fra, frb, he]
    all_goals simp +decide [Data.set_regs, Math.label, he, two_mul]
  · have fsa := fb.of_le (Nat.shiftRight_le _ (x.regs beta))
    have fsb := fb.of_le (Nat.shiftRight_le _ (x.regs beta'))
    have fra := fsa.of_le (Nat.mod_le _ 2)
    have frb := fsb.of_le (Nat.mod_le _ 2)
    refine ⟨?_, ?run, ?_, ?_, ?_, ?_, ?_⟩
    case run => ram_eval [labels, hz, h2, hkey, fm, fs, fd, fb, fsa, fsb, fra, frb, he]
    all_goals simp +decide [Data.set_regs, Math.label, he, two_mul]

/-- Selection from already computed digits, with the full repeated-value count. -/
theorem choose_exec {w : ℕ} (x : Data 48)
    (hz : x.regs zero = 0) (h1 : x.regs one = 1) (h2 : x.regs two = 2)
    (h3 : x.regs three = 3) (h4 : x.regs four = 4) (h5 : x.regs five = 5)
    (hs : x.regs sign = x.regs key % 2)
    (hfit : Fits w (2 * x.regs key)) (hsmall : Fits w 5) :
    ∃ y, ExecWithin w choose x y 20 ∧
      y.regs take = (Math.flag (x.regs bitA) (x.regs bitB) (x.regs digit)
        (x.regs mode) (x.regs key, x.regs count)).toNat ∧
      y.regs key = Math.value (x.regs mode) (x.regs key) ∧ y.mem = x.mem := by
  have f1 := hsmall.of_le (show 1 ≤ 5 by decide)
  have fd : Fits w (x.regs key + x.regs key) := by simpa only [two_mul] using hfit
  have fs : Fits w (x.regs key + x.regs key - x.regs key % 2) := fd.of_le (Nat.sub_le _ _)
  rcases (show x.regs mode = 0 ∨ x.regs mode = 1 ∨ x.regs mode = 2 ∨
      x.regs mode = 3 ∨ x.regs mode = 4 ∨ x.regs mode = 5 ∨ 6 ≤ x.regs mode by omega) with
    hm | hm | hm | hm | hm | hm | hm
  · by_cases ha : x.regs bitA = x.regs digit
    all_goals refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try ram_eval [choose, skip, hz, h1, h2, h3, h4, h5, hm, ha, f1]
    all_goals simp +decide [Data.set_regs, hm, ha, Math.value, Math.flag]
  · by_cases ha : x.regs bitA = x.regs digit
    · refine ⟨?_, ?run, ?_, ?_, ?_⟩
      case run => ram_eval [choose, skip, hz, h1, h2, h3, h4, h5, hm, ha, f1]
      all_goals simp +decide [Data.set_regs, hm, ha, Math.value, Math.flag]
    · by_cases hb : x.regs bitB = 0
      all_goals refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals try ram_eval [choose, skip, hz, h1, h2, h3, h4, h5, hm, ha, hb, f1]
      all_goals simp +decide [Data.set_regs, hm, ha, hb, Math.value, Math.flag]
  · by_cases ha : x.regs bitA = x.regs digit
    · refine ⟨?_, ?run, ?_, ?_, ?_⟩
      case run => ram_eval [choose, skip, hz, h1, h2, h3, h4, h5, hm, ha, f1]
      all_goals simp +decide [Data.set_regs, hm, ha, Math.value, Math.flag]
    · by_cases hb : x.regs bitB = 1
      all_goals refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals try ram_eval [choose, skip, hz, h1, h2, h3, h4, h5, hm, ha, hb, f1]
      all_goals simp +decide [Data.set_regs, hm, ha, hb, Math.value, Math.flag]
  · by_cases hk : x.regs key = 0
    · refine ⟨?_, ?run, ?_, ?_, ?_⟩
      case run => ram_eval [choose, skip, hz, h1, h2, h3, h4, h5, hm, hk, hs, fd, fs]
      all_goals simp +decide [Data.set_regs, hm, hk, Math.value, Math.flag, Math.twice]
    · by_cases hc : x.regs count < 2
      all_goals refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals try ram_eval [choose, skip, hz, h1, h2, h3, h4, h5, hm, hk, hc, hs,
        fd, fs, f1]
      all_goals simp +decide [Data.set_regs, hm, hk, Math.value, Math.flag, Math.twice, hc,
        show (2 ≤ x.regs count) ↔ ¬x.regs count < 2 from by omega, two_mul]
  · by_cases hk : x.regs key = 0
    · by_cases hc : x.regs count < 3
      all_goals refine ⟨?_, ?_, ?_, ?_, ?_⟩
      all_goals try ram_eval [choose, skip, hz, h1, h2, h3, h4, h5, hm, hk, hc, f1]
      all_goals simp +decide [Data.set_regs, hm, hk, Math.value, Math.flag, hc,
        show (3 ≤ x.regs count) ↔ ¬x.regs count < 3 from by omega]
    · refine ⟨?_, ?run, ?_, ?_, ?_⟩
      case run => ram_eval [choose, skip, hz, h1, h2, h3, h4, h5, hm, hk, f1]
      all_goals simp +decide [Data.set_regs, hm, hk, Math.value, Math.flag]
  · refine ⟨?_, ?run, ?_, ?_, ?_⟩
    case run => ram_eval [choose, skip, hz, h1, h2, h3, h4, h5, hm, f1]
    all_goals simp +decide [Data.set_regs, hm, Math.value, Math.flag]
  · have hn0 : x.regs mode ≠ 0 := by omega
    have hn1 : x.regs mode ≠ 1 := by omega
    have hn2 : x.regs mode ≠ 2 := by omega
    have hn3 : x.regs mode ≠ 3 := by omega
    have hn4 : x.regs mode ≠ 4 := by omega
    have hn5 : x.regs mode ≠ 5 := by omega
    refine ⟨?_, ?run, ?_, ?_, ?_⟩
    case run => ram_eval [choose, skip, hz, h1, h2, h3, h4, h5, hn0, hn1, hn2, hn3, hn4, hn5]
    all_goals simp +decide [Data.set_regs, Math.value, Math.flag, hn3]

/-- Complete native scalar selection. Its cost includes decoding, both label bits and doubling. -/
theorem exec {w : ℕ} (x : Data 48)
    (hz : x.regs zero = 0) (h1 : x.regs one = 1) (h2 : x.regs two = 2)
    (h3 : x.regs three = 3) (h4 : x.regs four = 4) (h5 : x.regs five = 5)
    (hkey : Fits w (x.regs key)) (habs : x.regs key / 2 ≤ 2 * x.regs magnitude)
    (hfit : Fits w (4 * x.regs magnitude + 2))
    (hdouble : Fits w (2 * x.regs key)) (hsmall : Fits w 5) :
    ∃ y, ExecWithin w program x y 31 ∧
      y.regs take = (Math.keep (x.regs magnitude) (x.regs beta) (x.regs beta')
        (x.regs digit) (x.regs mode) (x.regs key, x.regs count)).toNat ∧
      y.regs key = Math.value (x.regs mode) (x.regs key) ∧ y.mem = x.mem := by
  obtain ⟨u, hu, hus, _, hua, hub, hum⟩ := labels_exec x hz h2 hkey habs hfit
  have hr (j : Fin 48) (hj : j.val ≤ 12) : u.regs j = x.regs j :=
    hu.regs_eq (labels_preserves j hj)
  obtain ⟨y, hy, hyt, hyk, hym⟩ := choose_exec u
    ((hr zero (by decide)).trans hz) ((hr one (by decide)).trans h1)
    ((hr two (by decide)).trans h2) ((hr three (by decide)).trans h3)
    ((hr four (by decide)).trans h4) ((hr five (by decide)).trans h5)
    (by simpa only [hr key (by decide)] using hus)
    (by simpa only [hr key (by decide)] using hdouble) hsmall
  refine ⟨y, hu.seq hy, ?_, ?_, hym.trans hum⟩
  · simpa only [Math.keep, hr mode (by decide), hr digit (by decide), hr key (by decide),
      hr count (by decide), hua, hub] using hyt
  · simpa only [hr mode (by decide), hr key (by decide)] using hyk

end Select
end Cslib.Algorithms.WordRAM.ThreeSum.Frontend
