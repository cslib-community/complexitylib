/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Notation
public import Complexity.Foundations.Data.Nat.Radix
import Mathlib.Tactic.Linarith

/-!
# Multiword arithmetic on the checked word RAM

An elementary schoolbook multiplication update uses half-word digits. For radix
`β = 2 ^ (w / 2)`, four digits `a, b, d, c < β` satisfy
`a * b + d + c < β ^ 2 ≤ 2 ^ w`. Thus the product and both partial sums fit the
physical word, and division and remainder recover an exact digit and carry.

## Main definitions

* `Cslib.WordRAM.Multiword.radix`: the half-word radix.
* `Cslib.WordRAM.Multiword.LimbUpdate.program`: five standard RAM instructions implementing
  one schoolbook multiply-add update.
* `Cslib.WordRAM.Multiword.LimbUpdate.initializedProgram`: compute the half-word radix and
  perform the update in ten instructions, with no preloaded radix.

## Main results

* `Cslib.WordRAM.Multiword.LimbUpdate.exec`: checked execution, exact reconstruction, and
  bounded output digit and carry in five instructions, independently of the word size.

This module supplies the elementary update. `WordRAM.Multiword.Mul` assembles the full
schoolbook routine for arbitrary fixed operand lengths.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword

/-- Radix for digits whose multiply-add updates fit a single physical word. -/
def radix (w : ℕ) : ℕ := 2 ^ (w / 2)

/-- Widths below two have a degenerate floor-half radix, so nonzero inputs require
a different representation and routine. The schoolbook routines explicitly assume `2 ≤ w`. -/
theorem radix_eq_one_of_lt_two {w : ℕ} (hw : w < 2) : radix w = 1 := by
  simp [radix, Nat.div_eq_of_lt hw]

theorem one_lt_radix {w : ℕ} (hw : 2 ≤ w) : 1 < radix w :=
  Nat.one_lt_two_pow (by omega)

theorem radix_sq_le (w : ℕ) : radix w ^ 2 ≤ 2 ^ w := by
  rw [radix, ← pow_mul]
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem radix_fits {w : ℕ} (hw : 2 ≤ w) : Fits w (radix w) := by
  have h := one_lt_radix hw
  have hs := radix_sq_le w
  unfold Fits
  nlinarith

/-- Eighteen half-word digits suffice for a value occupying at most six physical words,
including odd word sizes. This is a representation bound, not a multiplication algorithm. -/
theorem exists_six_word_digits {w v : ℕ} (hw : 2 ≤ w) (hv : v < 2 ^ (6 * w)) :
    ∃ x : Fin 18 → ℕ, (∀ i, x i < radix w) ∧
      Nat.ofDigits (radix w) (List.ofFn x) = v := by
  apply Nat.exists_ofDigits_ofFn
  rw [radix, ← pow_mul]
  exact hv.trans_le (Nat.pow_le_pow_right (by decide) (by omega))

/-- The sharp bound for a schoolbook multiply-add: the maximum is `β ^ 2 - 1`. -/
theorem limb_update_lt_sq {β a b d c : ℕ} (ha : a < β) (hb : b < β)
    (hd : d < β) (hc : c < β) : a * b + d + c < β ^ 2 := by
  have hp := Nat.mul_le_mul (show a ≤ β - 1 by omega) (show b ≤ β - 1 by omega)
  have hβ : β - 1 + 1 = β := by omega
  nlinarith

/-- Every intermediate arithmetic result of the update fits the physical word. -/
theorem limb_update_fits {w a b d c : ℕ} (ha : a < radix w) (hb : b < radix w)
    (hd : d < radix w) (hc : c < radix w) : Fits w (a * b + d + c) :=
  (limb_update_lt_sq ha hb hd hc).trans_le (radix_sq_le w)

namespace LimbUpdate

/-- First multiplicand digit (preserved). -/
abbrev left : Fin 7 := 0
/-- Second multiplicand digit (preserved). -/
abbrev right : Fin 7 := 1
/-- Previous destination digit (preserved). -/
abbrev addend : Fin 7 := 2
/-- Input carry, replaced by the output carry. -/
abbrev carry : Fin 7 := 3
/-- Radix (preserved). -/
abbrev base : Fin 7 := 4
/-- Product and partial-sum workspace. -/
abbrev total : Fin 7 := 5
/-- Output digit. -/
abbrev digit : Fin 7 := 6

/-- One schoolbook update, using only checked single-word arithmetic. -/
def program : Code .standard 7 := ram[
  total ← left * right;
  total ← total + addend;
  total ← total + carry;
  digit ← total % base;
  carry ← total / base ]

theorem size_program : program.size = 5 := rfl

/-- Compute the radix from the physical word size, using only the two output registers as
workspace. The four input digits are preserved. -/
def setup : Code .standard 7 := ram[
  total ← width%;
  digit ← #2;
  base ← total / digit;
  digit ← #1;
  base ← digit <<< base ]

/-- The result of radix setup. -/
private def setupResult (w : ℕ) (x : Data 7) : Data 7 :=
  ((((x.set total w).set digit 2).set base (w / 2)).set digit 1).set base (radix w)

/-- Radix setup costs five instructions for every physical word size at least two. -/
private theorem exec_setup {w : ℕ} (x : Data 7) (hw : 2 ≤ w) :
    Exec w setup x (setupResult w x) 5 := by
  have h2 : Fits w 2 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hw
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2) this
  have hhalf : Fits w (w / 2) := (fits_self w).of_le (Nat.div_le_self _ _)
  have h1 := fits_one (w := w) (by omega)
  have hβ := radix_fits hw
  have hshift : 1 <<< (w / 2) = radix w := by rw [Nat.shiftLeft_eq, one_mul]; rfl
  ram_eval [setup, setupResult, h2, hhalf, h1, hβ, hshift]

/-- Fixed code computing the radix and then executing a schoolbook update. -/
def initializedProgram : Code .standard 7 := .seq setup program

theorem size_initializedProgram : initializedProgram.size = 10 := rfl

/-- The mathematical result of the five instructions, including the workspace. -/
private def result (x : Data 7) : Data 7 :=
  let s := x.regs left * x.regs right + x.regs addend + x.regs carry
  ((x.set total s).set digit (s % x.regs base)).set carry (s / x.regs base)

/-- Checked execution of the elementary update. All three intermediate results are justified
from the digit bounds; no high-product primitive or enlarged physical word is assumed. -/
private theorem exec_exact {w : ℕ} (x : Data 7)
    (ha : x.regs left < radix w) (hb : x.regs right < radix w)
    (hd : x.regs addend < radix w) (hc : x.regs carry < radix w) :
    Exec w program x (result x) 5 := by
  have hs := limb_update_fits ha hb hd hc
  have hp : Fits w (x.regs left * x.regs right) := hs.of_le (by omega)
  have hpd : Fits w (x.regs left * x.regs right + x.regs addend) :=
    hs.of_le (by omega)
  have hm : Fits w ((x.regs left * x.regs right + x.regs addend + x.regs carry) %
      x.regs base) := hs.of_le (Nat.mod_le _ _)
  have hq : Fits w ((x.regs left * x.regs right + x.regs addend + x.regs carry) /
      x.regs base) := hs.of_le (Nat.div_le_self _ _)
  ram_eval [program, result, hp, hpd, hs, hm, hq]
  simp only [Data.set, Function.update_idem]

/-- In five instructions the elementary update returns an exact low digit and carry, both
strictly below the radix. Memory and the two operands, addend, and radix are preserved.
For globally bounded input data, `ExecWithin.bounded` also gives globally bounded output data. -/
theorem exec {w : ℕ} (x : Data 7) (hw : 2 ≤ w) (hbase : x.regs base = radix w)
    (ha : x.regs left < radix w) (hb : x.regs right < radix w)
    (hd : x.regs addend < radix w) (hc : x.regs carry < radix w) :
    ∃ y, ExecWithin w program x y 5 ∧
      y.regs digit < radix w ∧ y.regs carry < radix w ∧
      x.regs left * x.regs right + x.regs addend + x.regs carry =
        y.regs digit + radix w * y.regs carry ∧
      y.mem = x.mem ∧ y.regs left = x.regs left ∧ y.regs right = x.regs right ∧
      y.regs addend = x.regs addend ∧ y.regs base = x.regs base := by
  have hβ : 0 < radix w := by have := one_lt_radix hw; omega
  have hs := limb_update_lt_sq ha hb hd hc
  have hq : (x.regs left * x.regs right + x.regs addend + x.regs carry) /
      radix w < radix w := by
    apply (Nat.div_lt_iff_lt_mul hβ).mpr
    simpa only [pow_two] using hs
  refine ⟨result x, (exec_exact x ha hb hd hc).within, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa +decide [result, Function.update_apply, hbase] using Nat.mod_lt
      (x.regs left * x.regs right + x.regs addend + x.regs carry) hβ
  · simpa +decide [result, Function.update_apply, hbase] using hq
  · simpa +decide [result, Function.update_apply, hbase] using (Nat.mod_add_div
      (x.regs left * x.regs right + x.regs addend + x.regs carry) (radix w)).symm
  all_goals simp +decide [result]

/-- The update with charged radix setup, in ten instructions at any word size at least two.
The initial radix and workspace registers may contain arbitrary words. -/
theorem exec_initialized {w : ℕ} (x : Data 7) (hw : 2 ≤ w)
    (ha : x.regs left < radix w) (hb : x.regs right < radix w)
    (hd : x.regs addend < radix w) (hc : x.regs carry < radix w) :
    ∃ y, ExecWithin w initializedProgram x y 10 ∧
      y.regs digit < radix w ∧ y.regs carry < radix w ∧
      x.regs left * x.regs right + x.regs addend + x.regs carry =
        y.regs digit + radix w * y.regs carry ∧
      y.mem = x.mem ∧ y.regs left = x.regs left ∧ y.regs right = x.regs right ∧
      y.regs addend = x.regs addend ∧ y.regs base = radix w := by
  have ha' : (setupResult w x).regs left < radix w := by
    simpa +decide [setupResult] using ha
  have hb' : (setupResult w x).regs right < radix w := by
    simpa +decide [setupResult] using hb
  have hd' : (setupResult w x).regs addend < radix w := by
    simpa +decide [setupResult] using hd
  have hc' : (setupResult w x).regs carry < radix w := by
    simpa +decide [setupResult] using hc
  obtain ⟨y, he, hy⟩ := exec (setupResult w x) hw (by simp [setupResult]) ha' hb' hd' hc'
  refine ⟨y, (exec_setup x hw).within.seq he, ?_⟩
  simpa +decide [setupResult] using hy

end LimbUpdate

end Cslib.WordRAM.Multiword

end
