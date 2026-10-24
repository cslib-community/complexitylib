/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Multiword.Mul
public import Complexity.Algorithms.Lean.FusionTree.Multiplier
import Mathlib.Tactic.FinCases

/-!
# Checked mask-and-multiply compression

The multiplier is supplied as three precomputed half-word digits. The query arrives as
one physical word: masking and conversion to digits are part of the charged execution.
The retained window fits inside the third product digit, including at odd physical widths.

## Main definitions

* `CompressProgram.code`: a fixed standard-basis compression program.

## Main results

* `CompressProgram.exec`: checked execution of mask-and-multiply compression.
* `CompressProgram.exec_approximateSketch`: execution of the arithmetic fusion sketch.

Node preprocessing and loading the constants are separate from query execution.

## References

* [Fredman and Willard, *Surpassing the information theoretic bound
  with fusion trees*][FredmanWillard1993].
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.FusionTree.CompressProgram

open Cslib.WordRAM Cslib.WordRAM.Multiword

/-- Embed the multiplication workspace in the first sixteen registers. -/
def embed (i : Fin 16) : Fin 21 := ⟨i.val, by omega⟩

private theorem embed_injective : Function.Injective embed := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 21 => i.val) h)

/-- Query word, preserved. -/
abbrev query : Fin 21 := 16
/-- Input position mask, preserved. -/
abbrev positions : Fin 21 := 17
/-- Retained output mask, preserved. -/
abbrev retained : Fin 21 := 18
/-- Offset `w - 2 * (w / 2)`, supplied by the caller and preserved. -/
abbrev offset : Fin 21 := 19
/-- Conversion scratch and final compressed result. -/
abbrev out : Fin 21 := 20

/-- Half-word radix workspace. -/
abbrev base : Fin 21 := 2
/-- Lowest query digit. -/
abbrev a₀ : Fin 21 := 4
/-- Middle query digit. -/
abbrev a₁ : Fin 21 := 5
/-- Highest query digit. -/
abbrev a₂ : Fin 21 := 6
/-- Third product digit, containing the retained window. -/
abbrev productDigit : Fin 21 := 12

/-- Mask the query and split it using division and remainder by the half-word radix.
No squared radix is ever installed in a physical register. -/
def split : Code .standard 21 := ram[
  out ← query &&& positions;
  a₀ ← out % base;
  out ← out / base;
  a₁ ← out % base;
  out ← out / base;
  a₂ ← out % base ]

/-- The exact data after query conversion, with an already initialized radix. -/
private def splitResult (w : ℕ) (x : Data 21) : Data 21 :=
  let a := x.regs query &&& x.regs positions
  let β := radix w
  (((((x.set out a).set 4 (a % β)).set out (a / β)).set 5
    (a / β % β)).set out (a / β / β)).set 6 (a / β / β % β)

private theorem exec_split {w : ℕ} (x : Data 21)
    (hx : Fits w (x.regs query)) (hbase : x.regs 2 = radix w) :
    Exec w split x (splitResult w x) 6 := by
  have ha : Fits w (x.regs query &&& x.regs positions) := hx.of_le Nat.and_le_left
  have hq := ha.of_le (Nat.div_le_self _ (radix w))
  have hqq := hq.of_le (Nat.div_le_self _ (radix w))
  have hm := ha.of_le (Nat.mod_le _ (radix w))
  have hqm := hq.of_le (Nat.mod_le _ (radix w))
  have hqqm := hqq.of_le (Nat.mod_le _ (radix w))
  ram_eval [split, splitResult, hbase, ha, hq, hqq, hm, hqm, hqqm]

/-- A masked window inside the third half-word digit depends only on that digit. -/
private theorem window_eq {w L p D : ℕ} (hL : L + (w - 2 * (w / 2)) ≤ w / 2)
    (hD : D < 2 ^ L) :
    ((p / radix w ^ 2 % radix w) >>> (w - 2 * (w / 2))) &&& D =
      (p >>> w) &&& D := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < L
  · have hsmall : w - 2 * (w / 2) + i < w / 2 := by omega
    have he : w - 2 * (w / 2) + i + w / 2 * 2 = w + i := by omega
    simp only [Nat.testBit_land, Nat.testBit_shiftRight, radix,
      Nat.testBit_mod_two_pow, decide_eq_true hsmall, Bool.true_and, ← pow_mul,
      Nat.testBit_div_two_pow, he]
  · have hfalse : D.testBit i = false := Nat.testBit_eq_false_of_lt
      (hD.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    simp only [Nat.testBit_land, hfalse, Bool.and_false]

/-- A multiplier of at most `w + L` bits has three bounded half-word digits whenever the
retained window fits. This is a preprocessing representation theorem; loading is separate. -/
theorem exists_multiplier_digits {w L M : ℕ}
    (hL : L + (w - 2 * (w / 2)) ≤ w / 2) (hM : M < 2 ^ (w + L)) :
    ∃ digits : Fin 3 → ℕ, (∀ i, digits i < radix w) ∧
      Nat.ofDigits (radix w) (List.ofFn digits) = M := by
  apply Nat.exists_ofDigits_ofFn
  rw [radix, ← pow_mul]
  exact hM.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

/-- Initialize the radix, convert the query, multiply three digits by three digits, and
extract the retained window. Registers 7--9 contain the precomputed multiplier digits. -/
def code : Code .standard 21 :=
  .seq Workspace.setup (.seq split
    (.seq ((Schoolbook.fixedProgram 3 3).rename embed) (ram[
      out ← productDigit >>> offset;
      out ← out &&& retained ])))

theorem size_code : code.size = 94 := by
  simp only [code, Code.size, Code.size_rename, Schoolbook.size_fixedProgram_eq]
  rfl

private theorem three_digits_value {β a : ℕ} (hβ : 0 < β) (ha : a < β ^ 3) :
    Nat.ofDigits β [a % β, a / β % β, a / β / β % β] = a := by
  have hq : a / β / β < β := by
    rw [Nat.div_div_eq_div_mul]
    apply (Nat.div_lt_iff_lt_mul (Nat.mul_pos hβ hβ)).mpr
    nlinarith [ha]
  simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero,
    Nat.mod_eq_of_lt hq]
  nlinarith [Nat.mod_add_div a β, Nat.mod_add_div (a / β) β]

private theorem split_left {w : ℕ} (hw : 2 ≤ w) (x : Data 21)
    (hx : Fits w (x.regs query)) :
    Multiword.Bounded (radix w) ((splitResult w x).comap embed)
      (Schoolbook.leftRegs 3 3) ∧
    Multiword.value (radix w) ((splitResult w x).comap embed)
      (Schoolbook.leftRegs 3 3) = x.regs query &&& x.regs positions := by
  have hβ : 0 < radix w := lt_trans Nat.zero_lt_one (one_lt_radix hw)
  have ha : x.regs query &&& x.regs positions < radix w ^ 3 := by
    apply (hx.of_le Nat.and_le_left).trans_le
    rw [radix, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  constructor
  · intro i hi
    simp only [Schoolbook.leftRegs, Schoolbook.registers, List.mem_ofFn] at hi
    obtain ⟨j, rfl⟩ := hi
    fin_cases j <;> simp +decide [Data.comap, embed, splitResult, Nat.mod_lt _ hβ]
  · simpa +decide [Multiword.value, Schoolbook.leftRegs, Schoolbook.registers,
      List.ofFn_succ, Data.comap, embed, splitResult] using three_digits_value hβ ha

private theorem third_digit {w : ℕ} (y : Data 16)
    (hy : Multiword.Bounded (radix w) y (Schoolbook.outputRegs 3 3)) :
    Multiword.value (radix w) y (Schoolbook.outputRegs 3 3) /
      radix w ^ 2 % radix w = y.regs 12 := by
  let digits : Fin 6 → ℕ := fun i => y.regs ⟨10 + i.val, by omega⟩
  have hb (i : Fin 6) : digits i < radix w := by
    apply hy
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  exact Nat.ofDigits_ofFn_div_mod digits hb (2 : Fin 6)

/-- In 94 checked standard instructions, compute the masked product window. The query and
all node parameters are preserved, as is memory. Only registers 0--6, 10--15 and 20 may
change. Multiplier digits in registers 7--9 must be preloaded; conversion of the physical
query word is charged. The retained mask occupies `L` bits and satisfies the stated
half-word window condition. -/
theorem exec {w L M : ℕ} (hw : 2 ≤ w) (x : Data 21)
    (hx : Fits w (x.regs query))
    (hb : Multiword.Bounded (radix w) (x.comap embed) (Schoolbook.rightRegs 3 3))
    (hM : Multiword.value (radix w) (x.comap embed) (Schoolbook.rightRegs 3 3) = M)
    (ho : x.regs offset = w - 2 * (w / 2))
    (hD : x.regs retained < 2 ^ L)
    (hL : L + (w - 2 * (w / 2)) ≤ w / 2) :
    ∃ y, Exec w code x y 94 ∧
      y.regs out = (((x.regs query &&& x.regs positions) * M) >>> w) &&&
        x.regs retained ∧
      y.mem = x.mem ∧
      ∀ i : Fin 21, (7 ≤ i.val ∧ i.val < 10) ∨ (16 ≤ i.val ∧ i.val < 20) →
        y.regs i = x.regs i := by
  let z := Workspace.setupResult w x
  let u := splitResult w z
  have hzq : z.regs query = x.regs query := by
    simp +decide [z, Workspace.setupResult, Workspace.base, Workspace.zero]
  have hzp : z.regs positions = x.regs positions := by
    simp +decide [z, Workspace.setupResult, Workspace.base, Workspace.zero]
  have hzbase : z.regs 2 = radix w := by simp [z, Workspace.setupResult,
    Workspace.base, Workspace.zero]
  have hez : Exec w Workspace.setup x z 6 := Workspace.exec_setup hw x
  have heu : Exec w split z u 6 := exec_split z (by rwa [hzq]) hzbase
  obtain ⟨hua, huav⟩ := split_left hw z (by rwa [hzq])
  have hur (i : Fin 16) (hi : i ∈ Schoolbook.rightRegs 3 3) :
      (u.comap embed).regs i = (x.comap embed).regs i := by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hi
    fin_cases j <;> simp +decide [u, z, Data.comap, embed, splitResult,
      Workspace.setupResult, Workspace.base, Workspace.zero]
  have hub : Multiword.Bounded (radix w) (u.comap embed) (Schoolbook.rightRegs 3 3) := by
    intro i hi
    rw [hur i hi]
    exact hb i hi
  have hum : Multiword.value (radix w) (u.comap embed) (Schoolbook.rightRegs 3 3) = M := by
    rw [Multiword.value, List.map_congr_left hur]
    exact hM
  obtain ⟨v, hev, hvb, hv, hvm, _⟩ := Schoolbook.exec_fixedProgram hw 3 3 (u.comap embed)
    hua hub
  rw [huav, hzq, hzp, hum] at hv
  let t := v.extend embed u
  have het : Exec w ((Schoolbook.fixedProgram 3 3).rename embed) u t 80 :=
    hev.rename embed_injective
  have htd : t.regs productDigit =
      ((x.regs query &&& x.regs positions) * M) / radix w ^ 2 % radix w := by
    have ht : t.regs (embed (12 : Fin 16)) = v.regs 12 :=
      embed_injective.extend_apply _ _ _
    rw [show productDigit = embed (12 : Fin 16) from rfl, ht,
      ← third_digit v hvb, hv]
  have htcaller (i : Fin 21) (hi : 16 ≤ i.val ∧ i.val < 20) :
      t.regs i = x.regs i := by
    apply (hez.seq (heu.seq het)).regs_eq
    have hp : ∀ i : Fin 21, 16 ≤ i.val ∧ i.val < 20 →
        (Code.seq (B := .standard) Workspace.setup
          (.seq split ((Schoolbook.fixedProgram 3 3).rename embed))).Preserves i := by decide
    exact hp i hi
  let d := t.regs productDigit >>> t.regs offset
  let y := (t.set out d).set out (d &&& t.regs retained)
  have hdigit : Fits w (t.regs productDigit) := by
    rw [htd]
    exact (Nat.mod_lt _ (lt_trans Nat.zero_lt_one (one_lt_radix hw))).trans (radix_fits hw)
  have hd : Fits w d := hdigit.of_le (by
    dsimp [d]
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_self _ _)
  have hmask : Fits w (d &&& t.regs retained) := hd.of_le Nat.and_le_left
  have hey : Exec w (ram[out ← productDigit >>> offset; out ← out &&& retained]) t y 2 := by
    ram_eval [y, d, hd, hmask]
  refine ⟨y, ?_, ?_, ?_, ?_⟩
  · exact hez.seq (heu.seq (het.seq hey))
  · change d &&& t.regs retained = _
    dsimp only [d]
    rw [htd, htcaller offset (by decide), htcaller retained (by decide), ho]
    exact window_eq hL hD
  · exact hvm
  · intro i hi
    apply (hez.seq (heu.seq (het.seq hey))).regs_eq
    have hp : ∀ i : Fin 21, (7 ≤ i.val ∧ i.val < 10) ∨ (16 ≤ i.val ∧ i.val < 20) →
        code.Preserves i := by decide
    exact hp i hi

/-- Specialize the actual execution to the arithmetic approximate sketch. The collision-free
parameter construction and comparison theorem are independent of this execution theorem.
The caller supplies the position and retained masks and three multiplier digits. -/
theorem exec_approximateSketch {w L r : ℕ} (hw : 2 ≤ w) (b m : Fin r → ℕ)
    (x : Data 21) (hx : Fits w (x.regs query))
    (hb : Multiword.Bounded (radix w) (x.comap embed) (Schoolbook.rightRegs 3 3))
    (hM : Multiword.value (radix w) (x.comap embed) (Schoolbook.rightRegs 3 3) =
      Lean.FusionTree.positionMask m)
    (hC : x.regs positions = Lean.FusionTree.positionMask b)
    (hD : x.regs retained = Lean.FusionTree.positionMask (fun i => b i + m i - w))
    (ho : x.regs offset = w - 2 * (w / 2))
    (hwidth : Lean.FusionTree.positionMask (fun i => b i + m i - w) < 2 ^ L)
    (hL : L + (w - 2 * (w / 2)) ≤ w / 2) :
    ∃ y, Exec w code x y 94 ∧
      y.regs out = Lean.FusionTree.approximateSketch w b m (x.regs query) ∧
      y.mem = x.mem ∧
      ∀ i : Fin 21, (7 ≤ i.val ∧ i.val < 10) ∨ (16 ≤ i.val ∧ i.val < 20) →
        y.regs i = x.regs i := by
  simpa only [hC, hD, Lean.FusionTree.approximateSketch] using
    exec hw x hx hb hM ho (hD ▸ hwidth) hL

end Cslib.Algorithms.WordRAM.FusionTree.CompressProgram
