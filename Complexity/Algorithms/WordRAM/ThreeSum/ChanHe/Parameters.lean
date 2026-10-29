/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.ChanHe.Defs
public import Complexity.Algorithms.WordRAM.NatLog
public import Complexity.Algorithms.WordRAM.NatClog
public import Complexity.Algorithms.WordRAM.NatSqrt
public import Complexity.Computability.WordRAM.Compile
public import Complexity.Computability.WordRAM.Signed.Encoding
import Mathlib.Tactic.Linarith

/-!
# Native parameters for Chan–He preprocessing

Original native programs and proofs. The parameter meanings are the existing finite mathematical
Chan–He definitions, with magnitude bound `2U` after the distinct-position frontend.
All loops and arithmetic are instructions; the program is fixed for each exponent `κ`.

## Main definitions

* `Parameters.program`: read the input header and compute the exact parameters.
* `Parameters.Output`: identify the unsigned output registers.

## Main results

* `Parameters.runs_input`: native execution from signed-encoded input with derived fits.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Parameters

open Cslib.WordRAM

namespace Math
open Cslib.Algorithms.ThreeSum

/-- A bound covering arithmetic, unsuccessful loop tests, and all output words. -/
def budget (n U : ℕ) : ℕ := 8 * (ChanHe.mPar n (2 * U) + 1) ^ 2 + 8 * U + 4 * n + 64

private theorem want_le (n U : ℕ) : ChanHe.wPar n (2 * U) + 1 ≤ ChanHe.mPar n (2 * U) :=
  Nat.le_mul_of_pos_right _ (by omega)

private theorem digits_le (n U : ℕ) : 5 * labelBits (2 * U) ≤ ChanHe.wPar n (2 * U) :=
  Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

private theorem factor_le (n U : ℕ) :
    2 * Nat.log 2 (ChanHe.wPar n (2 * U) + 1) + 4 ≤ ChanHe.mPar n (2 * U) :=
  Nat.le_mul_of_pos_left _ (Nat.succ_pos _)

private theorem height_le (n : ℕ) : ChanHe.height n ≤ Nat.log 2 n + 2 :=
  Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

end Math

/-- Unsigned input length. -/
abbrev len : Fin 24 := 0
/-- Original magnitude bound U. -/
abbrev magnitude : Fin 24 := 1
/-- Label bits for magnitude bound 2U. -/
abbrev digits : Fin 24 := 2
/-- Recursion height. -/
abbrev height : Fin 24 := 3
/-- Recursion fuel. -/
abbrev fuel : Fin 24 := 4
/-- Number of desired primes. -/
abbrev want : Fin 24 := 5
/-- Upper bound on candidate primes. -/
abbrev primeBound : Fin 24 := 6
/-- Common packed convolution length, 8m². -/
abbrev packedLen : Fin 24 := 7
/-- Magnitude of the padding for the doubled frontend bound, 4U+1. -/
abbrev padding : Fin 24 := 8
/-- Constant one. -/
abbrev one : Fin 24 := 9
/-- Constant two. -/
abbrev two : Fin 24 := 10
/-- Constant three. -/
abbrev three : Fin 24 := 11
/-- Constant four. -/
abbrev four : Fin 24 := 12
/-- Constant five. -/
abbrev five : Fin 24 := 13
/-- Constant eight. -/
abbrev eight : Fin 24 := 14
/-- Input length plus two. -/
abbrev base : Fin 24 := 15
/-- Consumed logarithm argument. -/
abbrev quotient : Fin 24 := 16
/-- Floor logarithm of input length. -/
abbrev logLen : Fin 24 := 17
/-- Integer square root of input length. -/
abbrev root : Fin 24 := 18
/-- Number of desired primes plus one. -/
abbrev wantSucc : Fin 24 := 19
/-- Arithmetic scratch. -/
abbrev temp : Fin 24 := 20
/-- Successor square-root counter. -/
abbrev nextRoot : Fin 24 := 21
/-- Square of that counter. -/
abbrev square : Fin 24 := 22
/-- Square-root test bound. -/
abbrev rootBound : Fin 24 := 23

/-- Exact mathematical outputs; every output is an ordinary unsigned word. -/
structure Output (n U : ℕ) (x : Data 24) : Prop where
  len : x.regs len = n
  magnitude : x.regs magnitude = U
  digits : x.regs digits = Cslib.Algorithms.ThreeSum.labelBits (2 * U)
  height : x.regs height = Cslib.Algorithms.ThreeSum.ChanHe.height n
  fuel : x.regs fuel = Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  want : x.regs want = Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U)
  primeBound : x.regs primeBound = Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  packedLen : x.regs packedLen = 8 * Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U) ^ 2
  padding : x.regs padding = 4 * U + 1

/-- One header load, constants, and the polynomial base. -/
def setup : Code .standard 24 := ram[
  quotient ← #0; len ← *quotient; one ← #1; two ← #2; three ← #3;
  four ← #4; five ← #5; eight ← #8; base ← len + two ]

/-- Unroll only the fixed exponent, never the input length or word width. -/
def power : ℕ → Code .standard 24
  | 0 => ram[ magnitude ← #1 ]
  | κ + 1 => .seq (power κ) (ram[ magnitude ← magnitude * base ])

/-- Register selection for a floor/ceiling logarithm with output `dst`. -/
def logRegisters (dst : Fin 24) : Fin 4 → Fin 24 := ![quotient, dst, one, two]

/-- Register selection for successive squares. -/
def sqrtRegisters : Fin 6 → Fin 24 := ![len, root, nextRoot, square, one, rootBound]

private theorem sqrt_injective : sqrtRegisters.Injective := by decide

/-- The instruction sequence after the power computation. -/
def calculate : Code .standard 24 :=
  .seq (ram[ quotient ← four * magnitude; padding ← quotient + one ])
    (.seq (NatLog.program.rename (logRegisters digits))
    (.seq (ram[ digits ← digits + one ])
    (.seq (NatSqrt.program.rename sqrtRegisters)
    (.seq (ram[ temp ← root + one; want ← five * digits; want ← want * temp;
      wantSucc ← want + one; quotient ← wantSucc ])
    (.seq (NatLog.program.rename (logRegisters temp))
    (.seq (ram[ temp ← two * temp; temp ← temp + four; primeBound ← wantSucc * temp ])
    (.seq (ram[ quotient ← len ])
    (.seq (NatLog.program.rename (logRegisters logLen))
    (.seq (ram[ quotient ← logLen + two ])
    (.seq (NatClog.program.rename (logRegisters height))
    (ram[ fuel ← three * height; fuel ← fuel - two; packedLen ← primeBound * primeBound;
      packedLen ← eight * packedLen ])))))))))))

/-- Fixed 24-register native code for each fixed polynomial magnitude exponent. -/
def program (κ : ℕ) : Code .standard 24 := .seq setup (.seq (power κ) calculate)

private theorem exec_power {w : ℕ} (κ : ℕ) (x : Data 24) (hb : 1 ≤ x.regs base)
    (hfit : Fits w (x.regs base ^ κ)) :
    ExecWithin w (power κ) x (x.set magnitude (x.regs base ^ κ)) (κ + 1) := by
  induction κ with
  | zero => simpa only [power, pow_zero] using ExecWithin.const hfit
  | succ κ ih =>
    have hprev : Fits w (x.regs base ^ κ) :=
      hfit.of_le (Nat.pow_le_pow_right hb (by omega))
    have he := ih hprev
    have hm : ExecWithin w (ram[ magnitude ← magnitude * base ])
        (x.set magnitude (x.regs base ^ κ))
        (x.set magnitude (x.regs base ^ (κ + 1))) 1 := by
      have hp : Fits w (x.regs base ^ κ * x.regs base) := by
        simpa only [pow_succ] using hfit
      apply ExecWithin.of_eval (fuel := 0) (n := 1) ?_ (by decide)
      simp +decide [Code.eval, Op.eval_bin, Data.put,
        BinOp.eval, hp, magnitude, base, pow_succ, Data.set, Function.update_idem]
    exact (he.seq hm).mono (by omega)

/-- An explicit charged bound, including all header reads, copies and setup. Halt adds one. -/
def time (κ n U : ℕ) : ℕ := κ + 64 + 5 * Nat.sqrt n + 4 * Nat.log 2 (4 * U) +
  4 * Nat.log 2 (Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U) + 1) +
  4 * Nat.log 2 n + 5 * Cslib.Algorithms.ThreeSum.ChanHe.height n

private theorem time_zero (n U : ℕ) : time 0 n U - 20 = 44 + 5 * Nat.sqrt n +
    4 * Nat.log 2 (4 * U) +
    4 * Nat.log 2 (Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U) + 1) +
    4 * Nat.log 2 n + 5 * Cslib.Algorithms.ThreeSum.ChanHe.height n := by
  dsimp [time]
  omega

set_option maxHeartbeats 300000 in
-- Measured 256376 heartbeats for the twelve native segments and explicit register frames.
private theorem exec_calculate {w n U : ℕ} (x : Data 24)
    (hlen : x.regs len = n) (hU : x.regs magnitude = U)
    (h1 : x.regs one = 1) (h2 : x.regs two = 2) (h3 : x.regs three = 3)
    (h4 : x.regs four = 4) (h5 : x.regs five = 5) (h8 : x.regs eight = 8)
    (hfit : Fits w (Math.budget n U)) :
    ∃ y, ExecWithin w calculate x y (time 0 n U - 20) ∧ Output n U y ∧ y.mem = x.mem := by
  let Λ := Cslib.Algorithms.ThreeSum.labelBits (2 * U)
  let h := Cslib.Algorithms.ThreeSum.ChanHe.height n
  let wp := Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U)
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  have eΛ : Λ = Nat.log 2 (4 * U) + 1 := by
    dsimp [Λ, Cslib.Algorithms.ThreeSum.labelBits]
    congr 2
    omega
  have ew : wp = 5 * Λ * (Nat.sqrt n + 1) := rfl
  have em : m = (wp + 1) * (2 * Nat.log 2 (wp + 1) + 4) := rfl
  have eh : Cslib.Algorithms.ThreeSum.ChanHe.fuel n = 3 * h - 2 := rfl
  have hd : 5 * Λ ≤ wp := Math.digits_le n U
  have hw : wp + 1 ≤ m := Math.want_le n U
  have hf : 2 * Nat.log 2 (wp + 1) + 4 ≤ m := Math.factor_le n U
  have hh : h ≤ Nat.log 2 n + 2 := Math.height_le n
  have hl := Nat.log_le_self 2 n
  have hroot := Nat.sqrt_le_self n
  have hml : Fits w m := hfit.of_le (by dsimp [Math.budget]; nlinarith)
  have fitm (v : ℕ) (hv : v ≤ m) : Fits w v := hml.of_le hv
  have fitu (v : ℕ) (hv : v ≤ 8 * U + 64) : Fits w v :=
    hfit.of_le (by dsimp [Math.budget]; omega)
  have fitn (v : ℕ) (hv : v ≤ 4 * n + 64) : Fits w v :=
    hfit.of_le (by dsimp [Math.budget]; omega)
  have f1 : Fits w 1 := fitu _ (by omega)
  have f2 : Fits w 2 := fitu _ (by omega)
  have f4U : Fits w (4 * U) := fitu _ (by omega)
  have fpad : Fits w (4 * U + 1) := fitu _ (by omega)
  have fΛ : Fits w Λ := fitm _ (by omega)
  have flogU : Fits w (Nat.log 2 (4 * U) + 1) :=
    fitu _ (by have := Nat.log_le_self 2 (4 * U); omega)
  have fsqrt : Fits w (4 * n + 4) := fitn _ (by omega)
  have fr : Fits w (Nat.sqrt n + 1) := fitn _ (by omega)
  have f5Λ : Fits w (5 * Λ) := fitm _ (by omega)
  have fwp : Fits w wp := fitm _ (by omega)
  have fwps : Fits w (wp + 1) := fitm _ hw
  have flogwp : Fits w (Nat.log 2 (wp + 1) + 1) := fitm _ (by omega)
  have f2log : Fits w (2 * Nat.log 2 (wp + 1)) := fitm _ (by omega)
  have ff : Fits w (2 * Nat.log 2 (wp + 1) + 4) := fitm _ hf
  have fn : Fits w n := fitn _ (by omega)
  have flogn : Fits w (Nat.log 2 n + 1) := fitn _ (by omega)
  have flog2 : Fits w (Nat.log 2 n + 2) := fitn _ (by omega)
  have flog3 : Fits w (Nat.log 2 n + 2 + 1) := fitn _ (by omega)
  have fh : Fits w (h + 1) := fitn _ (by omega)
  have f3h : Fits w (3 * h) := fitn _ (by omega)
  have ffuel : Fits w (Cslib.Algorithms.ThreeSum.ChanHe.fuel n) :=
    fitn _ (by dsimp [Cslib.Algorithms.ThreeSum.ChanHe.fuel]; omega)
  have fm2 : Fits w (m * m) := hfit.of_le (by dsimp [Math.budget]; nlinarith)
  have fN : Fits w (8 * m ^ 2) := hfit.of_le (by dsimp [Math.budget]; nlinarith)
  have fNm : Fits w (8 * (m * m)) := by simpa only [pow_two] using fN
  let a := ((x.set quotient (4 * U)).set padding (4 * U + 1))
  have ea : ExecWithin w (ram[ quotient ← four * magnitude; padding ← quotient + one ]) x a 2 := by
    ram_eval [a, h4, hU, h1, f4U, fpad, four, magnitude, one, quotient, padding,
      Fin.mk.injEq]
  have a_len : a.regs len = n := by
    simpa +decide [a, quotient, padding, len] using hlen
  have a_magnitude : a.regs magnitude = U := by
    simpa +decide [a, quotient, padding, magnitude] using hU
  have a_one : a.regs one = 1 := by
    simpa +decide [a, quotient, padding, one] using h1
  have a_two : a.regs two = 2 := by
    simpa +decide [a, quotient, padding, two] using h2
  have a_three : a.regs three = 3 := by
    simpa +decide [a, quotient, padding, three] using h3
  have a_four : a.regs four = 4 := by
    simpa +decide [a, quotient, padding, four] using h4
  have a_five : a.regs five = 5 := by
    simpa +decide [a, quotient, padding, five] using h5
  have a_eight : a.regs eight = 8 := by
    simpa +decide [a, quotient, padding, eight] using h8
  have a_quotient : a.regs quotient = 4 * U := by
    simp +decide [a, quotient, padding]
  have a_padding : a.regs padding = 4 * U + 1 := by
    simp +decide [a, quotient, padding]
  have a_mem : a.mem = x.mem := rfl
  obtain ⟨b, eb, b_digits, b_mem, b_one, b_two⟩ :=
    NatLog.exec_rename (logRegisters digits) (by decide) a f2
      (by simpa only [logRegisters, NatLog.arg, Matrix.cons_val_zero, a_quotient] using f4U)
      (by simpa only [logRegisters, NatLog.arg, Matrix.cons_val_zero, a_quotient, h] using flogU)
  simp only [logRegisters, NatLog.arg, NatLog.result, NatLog.one, NatLog.two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      a_quotient] at eb b_digits b_one b_two
  have b_len : b.regs len = n := (eb.regs_eq (by decide)).trans a_len
  have b_magnitude : b.regs magnitude = U := (eb.regs_eq (by decide)).trans a_magnitude
  have b_three : b.regs three = 3 := (eb.regs_eq (by decide)).trans a_three
  have b_four : b.regs four = 4 := (eb.regs_eq (by decide)).trans a_four
  have b_five : b.regs five = 5 := (eb.regs_eq (by decide)).trans a_five
  have b_eight : b.regs eight = 8 := (eb.regs_eq (by decide)).trans a_eight
  have b_padding : b.regs padding = 4 * U + 1 := (eb.regs_eq (by decide)).trans a_padding
  have b_memory : b.mem = x.mem := b_mem.trans a_mem
  let c := (b.set digits (Λ))
  have ec : ExecWithin w (ram[ digits ← digits + one ]) b c 1 := by
    ram_eval [c, b_digits, b_one, ← eΛ, fΛ, digits, one, Fin.mk.injEq]
  have c_len : c.regs len = n := by
    simpa +decide [c, digits, len] using b_len
  have c_magnitude : c.regs magnitude = U := by
    simpa +decide [c, digits, magnitude] using b_magnitude
  have c_three : c.regs three = 3 := by
    simpa +decide [c, digits, three] using b_three
  have c_four : c.regs four = 4 := by
    simpa +decide [c, digits, four] using b_four
  have c_five : c.regs five = 5 := by
    simpa +decide [c, digits, five] using b_five
  have c_eight : c.regs eight = 8 := by
    simpa +decide [c, digits, eight] using b_eight
  have c_padding : c.regs padding = 4 * U + 1 := by
    simpa +decide [c, digits, padding] using b_padding
  have c_digits : c.regs digits = Λ := by
    simp +decide [c, digits]
  have c_one : c.regs one = 1 := by
    simpa +decide [c, digits, one] using b_one
  have c_two : c.regs two = 2 := by
    simpa +decide [c, digits, two] using b_two
  have c_mem : c.mem = x.mem := b_memory
  obtain ⟨d, ed, d_root, d_len, d_mem, d_one⟩ := NatSqrt.exec_rename
    sqrtRegisters sqrt_injective c (by simpa [sqrtRegisters, NatSqrt.arg, c_len] using fsqrt)
  simp only [sqrtRegisters, NatSqrt.arg, NatSqrt.root, NatSqrt.one,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, c_len] at ed d_root d_len d_one
  have d_magnitude : d.regs magnitude = U := (ed.regs_eq (by decide)).trans c_magnitude
  have d_three : d.regs three = 3 := (ed.regs_eq (by decide)).trans c_three
  have d_four : d.regs four = 4 := (ed.regs_eq (by decide)).trans c_four
  have d_five : d.regs five = 5 := (ed.regs_eq (by decide)).trans c_five
  have d_eight : d.regs eight = 8 := (ed.regs_eq (by decide)).trans c_eight
  have d_padding : d.regs padding = 4 * U + 1 := (ed.regs_eq (by decide)).trans c_padding
  have d_digits : d.regs digits = Λ := (ed.regs_eq (by decide)).trans c_digits
  have d_two : d.regs two = 2 := (ed.regs_eq (by decide)).trans c_two
  have d_memory : d.mem = x.mem := d_mem.trans c_mem
  let e := (((((d.set temp (Nat.sqrt n + 1)).set want (5 * Λ)).set want (wp)).set wantSucc
    (wp + 1)).set quotient (wp + 1))
  have ee : ExecWithin w (ram[ temp ← root + one; want ← five * digits; want ← want * temp;
    wantSucc ← want + one; quotient ← wantSucc ]) d e 5 := by
    ram_eval [e, d_root, d_one, d_five, d_digits, ← ew, fr, f5Λ, fwp, fwps, temp, root, one,
      want, five, digits, wantSucc, quotient, Fin.mk.injEq, Data.set, Function.update_idem]
  have e_magnitude : e.regs magnitude = U := by
    simpa +decide [e, temp, want, wantSucc, quotient, magnitude] using d_magnitude
  have e_three : e.regs three = 3 := by
    simpa +decide [e, temp, want, wantSucc, quotient, three] using d_three
  have e_four : e.regs four = 4 := by
    simpa +decide [e, temp, want, wantSucc, quotient, four] using d_four
  have e_five : e.regs five = 5 := by
    simpa +decide [e, temp, want, wantSucc, quotient, five] using d_five
  have e_eight : e.regs eight = 8 := by
    simpa +decide [e, temp, want, wantSucc, quotient, eight] using d_eight
  have e_padding : e.regs padding = 4 * U + 1 := by
    simpa +decide [e, temp, want, wantSucc, quotient, padding] using d_padding
  have e_digits : e.regs digits = Λ := by
    simpa +decide [e, temp, want, wantSucc, quotient, digits] using d_digits
  have e_two : e.regs two = 2 := by
    simpa +decide [e, temp, want, wantSucc, quotient, two] using d_two
  have e_root : e.regs root = Nat.sqrt n := by
    simpa +decide [e, temp, want, wantSucc, quotient, root] using d_root
  have e_one : e.regs one = 1 := by
    simpa +decide [e, temp, want, wantSucc, quotient, one] using d_one
  have e_len : e.regs len = n := by
    simpa +decide [e, temp, want, wantSucc, quotient, len] using d_len
  have e_temp : e.regs temp = Nat.sqrt n + 1 := by
    simp +decide [e, temp, want, wantSucc, quotient]
  have e_want : e.regs want = wp := by
    simp +decide [e, temp, want, wantSucc, quotient]
  have e_wantSucc : e.regs wantSucc = wp + 1 := by
    simp +decide [e, temp, want, wantSucc, quotient]
  have e_quotient : e.regs quotient = wp + 1 := by
    simp +decide [e, temp, want, wantSucc, quotient]
  have e_mem : e.mem = x.mem := d_memory
  obtain ⟨f, ef, f_temp, f_mem, f_one, f_two⟩ :=
    NatLog.exec_rename (logRegisters temp) (by decide) e f2
      (by simpa only [logRegisters, NatLog.arg, Matrix.cons_val_zero, e_quotient] using fwps)
      (by simpa only [logRegisters, NatLog.arg, Matrix.cons_val_zero, e_quotient, h] using flogwp)
  simp only [logRegisters, NatLog.arg, NatLog.result, NatLog.one, NatLog.two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, e_quotient] at ef f_temp f_one f_two
  have f_magnitude : f.regs magnitude = U := (ef.regs_eq (by decide)).trans e_magnitude
  have f_three : f.regs three = 3 := (ef.regs_eq (by decide)).trans e_three
  have f_four : f.regs four = 4 := (ef.regs_eq (by decide)).trans e_four
  have f_five : f.regs five = 5 := (ef.regs_eq (by decide)).trans e_five
  have f_eight : f.regs eight = 8 := (ef.regs_eq (by decide)).trans e_eight
  have f_padding : f.regs padding = 4 * U + 1 := (ef.regs_eq (by decide)).trans e_padding
  have f_digits : f.regs digits = Λ := (ef.regs_eq (by decide)).trans e_digits
  have f_root : f.regs root = Nat.sqrt n := (ef.regs_eq (by decide)).trans e_root
  have f_len : f.regs len = n := (ef.regs_eq (by decide)).trans e_len
  have f_want : f.regs want = wp := (ef.regs_eq (by decide)).trans e_want
  have f_wantSucc : f.regs wantSucc = wp + 1 := (ef.regs_eq (by decide)).trans e_wantSucc
  have f_memory : f.mem = x.mem := f_mem.trans e_mem
  let g := (((f.set temp (2 * Nat.log 2 (wp + 1))).set temp
    (2 * Nat.log 2 (wp + 1) + 4)).set primeBound m)
  have eg : ExecWithin w (ram[ temp ← two * temp; temp ← temp + four;
    primeBound ← wantSucc * temp ]) f g 3 := by
    ram_eval [g, f_two, f_temp, f_four, f_wantSucc, ← em, f2log, ff, hml, temp, two, four,
      primeBound, wantSucc, Fin.mk.injEq, Data.set, Function.update_idem]
  have g_magnitude : g.regs magnitude = U := by
    simpa +decide [g, temp, primeBound, magnitude] using f_magnitude
  have g_three : g.regs three = 3 := by
    simpa +decide [g, temp, primeBound, three] using f_three
  have g_four : g.regs four = 4 := by
    simpa +decide [g, temp, primeBound, four] using f_four
  have g_five : g.regs five = 5 := by
    simpa +decide [g, temp, primeBound, five] using f_five
  have g_eight : g.regs eight = 8 := by
    simpa +decide [g, temp, primeBound, eight] using f_eight
  have g_padding : g.regs padding = 4 * U + 1 := by
    simpa +decide [g, temp, primeBound, padding] using f_padding
  have g_digits : g.regs digits = Λ := by
    simpa +decide [g, temp, primeBound, digits] using f_digits
  have g_root : g.regs root = Nat.sqrt n := by
    simpa +decide [g, temp, primeBound, root] using f_root
  have g_len : g.regs len = n := by
    simpa +decide [g, temp, primeBound, len] using f_len
  have g_want : g.regs want = wp := by
    simpa +decide [g, temp, primeBound, want] using f_want
  have g_wantSucc : g.regs wantSucc = wp + 1 := by
    simpa +decide [g, temp, primeBound, wantSucc] using f_wantSucc
  have g_temp : g.regs temp = 2 * Nat.log 2 (wp + 1) + 4 := by
    simp +decide [g, temp, primeBound]
  have g_one : g.regs one = 1 := by
    simpa +decide [g, temp, primeBound, one] using f_one
  have g_two : g.regs two = 2 := by
    simpa +decide [g, temp, primeBound, two] using f_two
  have g_primeBound : g.regs primeBound = m := by
    simp +decide [g, temp, primeBound]
  have g_mem : g.mem = x.mem := f_memory
  let j := (g.set quotient (n))
  have ej : ExecWithin (B := .standard) w (ram[ quotient ← len ]) g j 1 := by
    ram_eval [j, g_len]
  have j_magnitude : j.regs magnitude = U := by
    simpa +decide [j, quotient, magnitude] using g_magnitude
  have j_three : j.regs three = 3 := by
    simpa +decide [j, quotient, three] using g_three
  have j_four : j.regs four = 4 := by
    simpa +decide [j, quotient, four] using g_four
  have j_five : j.regs five = 5 := by
    simpa +decide [j, quotient, five] using g_five
  have j_eight : j.regs eight = 8 := by
    simpa +decide [j, quotient, eight] using g_eight
  have j_padding : j.regs padding = 4 * U + 1 := by
    simpa +decide [j, quotient, padding] using g_padding
  have j_digits : j.regs digits = Λ := by
    simpa +decide [j, quotient, digits] using g_digits
  have j_root : j.regs root = Nat.sqrt n := by
    simpa +decide [j, quotient, root] using g_root
  have j_len : j.regs len = n := by
    simpa +decide [j, quotient, len] using g_len
  have j_want : j.regs want = wp := by
    simpa +decide [j, quotient, want] using g_want
  have j_wantSucc : j.regs wantSucc = wp + 1 := by
    simpa +decide [j, quotient, wantSucc] using g_wantSucc
  have j_temp : j.regs temp = 2 * Nat.log 2 (wp + 1) + 4 := by
    simpa +decide [j, quotient, temp] using g_temp
  have j_one : j.regs one = 1 := by
    simpa +decide [j, quotient, one] using g_one
  have j_two : j.regs two = 2 := by
    simpa +decide [j, quotient, two] using g_two
  have j_primeBound : j.regs primeBound = m := by
    simpa +decide [j, quotient, primeBound] using g_primeBound
  have j_quotient : j.regs quotient = n := by
    simp +decide [j, quotient]
  have j_mem : j.mem = x.mem := g_mem
  obtain ⟨k, ek, k_logLen, k_mem, k_one, k_two⟩ :=
    NatLog.exec_rename (logRegisters logLen) (by decide) j f2
      (by simpa only [logRegisters, NatLog.arg, Matrix.cons_val_zero, j_quotient] using fn)
      (by simpa only [logRegisters, NatLog.arg, Matrix.cons_val_zero, j_quotient, h] using flogn)
  simp only [logRegisters, NatLog.arg, NatLog.result, NatLog.one, NatLog.two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      j_quotient] at ek k_logLen k_one k_two
  have k_magnitude : k.regs magnitude = U := (ek.regs_eq (by decide)).trans j_magnitude
  have k_three : k.regs three = 3 := (ek.regs_eq (by decide)).trans j_three
  have k_four : k.regs four = 4 := (ek.regs_eq (by decide)).trans j_four
  have k_five : k.regs five = 5 := (ek.regs_eq (by decide)).trans j_five
  have k_eight : k.regs eight = 8 := (ek.regs_eq (by decide)).trans j_eight
  have k_padding : k.regs padding = 4 * U + 1 := (ek.regs_eq (by decide)).trans j_padding
  have k_digits : k.regs digits = Λ := (ek.regs_eq (by decide)).trans j_digits
  have k_root : k.regs root = Nat.sqrt n := (ek.regs_eq (by decide)).trans j_root
  have k_len : k.regs len = n := (ek.regs_eq (by decide)).trans j_len
  have k_want : k.regs want = wp := (ek.regs_eq (by decide)).trans j_want
  have k_wantSucc : k.regs wantSucc = wp + 1 := (ek.regs_eq (by decide)).trans j_wantSucc
  have k_temp : k.regs temp = 2 * Nat.log 2 (wp + 1) + 4 := (ek.regs_eq (by decide)).trans j_temp
  have k_primeBound : k.regs primeBound = m := (ek.regs_eq (by decide)).trans j_primeBound
  have k_memory : k.mem = x.mem := k_mem.trans j_mem
  let l := (k.set quotient (Nat.log 2 n + 2))
  have el : ExecWithin w (ram[ quotient ← logLen + two ]) k l 1 := by
    ram_eval [l, k_logLen, k_two, flog2, quotient, logLen, two, Fin.mk.injEq]
  have l_magnitude : l.regs magnitude = U := by
    simpa +decide [l, quotient, magnitude] using k_magnitude
  have l_three : l.regs three = 3 := by
    simpa +decide [l, quotient, three] using k_three
  have l_four : l.regs four = 4 := by
    simpa +decide [l, quotient, four] using k_four
  have l_five : l.regs five = 5 := by
    simpa +decide [l, quotient, five] using k_five
  have l_eight : l.regs eight = 8 := by
    simpa +decide [l, quotient, eight] using k_eight
  have l_padding : l.regs padding = 4 * U + 1 := by
    simpa +decide [l, quotient, padding] using k_padding
  have l_digits : l.regs digits = Λ := by
    simpa +decide [l, quotient, digits] using k_digits
  have l_root : l.regs root = Nat.sqrt n := by
    simpa +decide [l, quotient, root] using k_root
  have l_len : l.regs len = n := by
    simpa +decide [l, quotient, len] using k_len
  have l_want : l.regs want = wp := by
    simpa +decide [l, quotient, want] using k_want
  have l_wantSucc : l.regs wantSucc = wp + 1 := by
    simpa +decide [l, quotient, wantSucc] using k_wantSucc
  have l_temp : l.regs temp = 2 * Nat.log 2 (wp + 1) + 4 := by
    simpa +decide [l, quotient, temp] using k_temp
  have l_primeBound : l.regs primeBound = m := by
    simpa +decide [l, quotient, primeBound] using k_primeBound
  have l_logLen : l.regs logLen = Nat.log 2 n := by
    simpa +decide [l, quotient, logLen] using k_logLen
  have l_one : l.regs one = 1 := by
    simpa +decide [l, quotient, one] using k_one
  have l_two : l.regs two = 2 := by
    simpa +decide [l, quotient, two] using k_two
  have l_quotient : l.regs quotient = Nat.log 2 n + 2 := by
    simp +decide [l, quotient]
  have l_mem : l.mem = x.mem := k_memory
  obtain ⟨o, eo, o_height, o_mem, o_one, o_two⟩ :=
    NatClog.exec_rename (logRegisters height) (by decide) l f2
      (by simpa only [logRegisters, NatClog.arg, Matrix.cons_val_zero, l_quotient] using flog3)
      (by simpa only [logRegisters, NatClog.arg, Matrix.cons_val_zero, l_quotient, h,
        Cslib.Algorithms.ThreeSum.ChanHe.height] using fh)
  simp only [logRegisters, NatClog.arg, NatClog.result, NatClog.one, NatClog.two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      l_quotient] at eo o_height o_one o_two
  change o.regs height = h at o_height
  change ExecWithin w _ l o (5 * h + 5) at eo
  have o_magnitude : o.regs magnitude = U := (eo.regs_eq (by decide)).trans l_magnitude
  have o_three : o.regs three = 3 := (eo.regs_eq (by decide)).trans l_three
  have o_four : o.regs four = 4 := (eo.regs_eq (by decide)).trans l_four
  have o_five : o.regs five = 5 := (eo.regs_eq (by decide)).trans l_five
  have o_eight : o.regs eight = 8 := (eo.regs_eq (by decide)).trans l_eight
  have o_padding : o.regs padding = 4 * U + 1 := (eo.regs_eq (by decide)).trans l_padding
  have o_digits : o.regs digits = Λ := (eo.regs_eq (by decide)).trans l_digits
  have o_root : o.regs root = Nat.sqrt n := (eo.regs_eq (by decide)).trans l_root
  have o_len : o.regs len = n := (eo.regs_eq (by decide)).trans l_len
  have o_want : o.regs want = wp := (eo.regs_eq (by decide)).trans l_want
  have o_wantSucc : o.regs wantSucc = wp + 1 := (eo.regs_eq (by decide)).trans l_wantSucc
  have o_temp : o.regs temp = 2 * Nat.log 2 (wp + 1) + 4 := (eo.regs_eq (by decide)).trans l_temp
  have o_primeBound : o.regs primeBound = m := (eo.regs_eq (by decide)).trans l_primeBound
  have o_logLen : o.regs logLen = Nat.log 2 n := (eo.regs_eq (by decide)).trans l_logLen
  have o_memory : o.mem = x.mem := o_mem.trans l_mem
  let p := ((((o.set fuel (3 * h)).set fuel (Cslib.Algorithms.ThreeSum.ChanHe.fuel n)).set packedLen
    (m * m)).set packedLen (8 * m ^ 2))
  have ep : ExecWithin w (ram[ fuel ← three * height; fuel ← fuel - two;
    packedLen ← primeBound * primeBound; packedLen ← eight * packedLen ]) o p 4 := by
    ram_eval [p, o_three, o_height, o_two, o_primeBound, o_eight, ← eh, f3h, ffuel, fm2, fNm,
      fuel, three, height, two, packedLen, primeBound, eight, Fin.mk.injEq, pow_two, Data.set,
      Function.update_idem]
  have p_magnitude : p.regs magnitude = U := by
    simpa +decide [p, fuel, packedLen, magnitude] using o_magnitude
  have p_three : p.regs three = 3 := by
    simpa +decide [p, fuel, packedLen, three] using o_three
  have p_four : p.regs four = 4 := by
    simpa +decide [p, fuel, packedLen, four] using o_four
  have p_five : p.regs five = 5 := by
    simpa +decide [p, fuel, packedLen, five] using o_five
  have p_eight : p.regs eight = 8 := by
    simpa +decide [p, fuel, packedLen, eight] using o_eight
  have p_padding : p.regs padding = 4 * U + 1 := by
    simpa +decide [p, fuel, packedLen, padding] using o_padding
  have p_digits : p.regs digits = Λ := by
    simpa +decide [p, fuel, packedLen, digits] using o_digits
  have p_root : p.regs root = Nat.sqrt n := by
    simpa +decide [p, fuel, packedLen, root] using o_root
  have p_len : p.regs len = n := by
    simpa +decide [p, fuel, packedLen, len] using o_len
  have p_want : p.regs want = wp := by
    simpa +decide [p, fuel, packedLen, want] using o_want
  have p_wantSucc : p.regs wantSucc = wp + 1 := by
    simpa +decide [p, fuel, packedLen, wantSucc] using o_wantSucc
  have p_temp : p.regs temp = 2 * Nat.log 2 (wp + 1) + 4 := by
    simpa +decide [p, fuel, packedLen, temp] using o_temp
  have p_primeBound : p.regs primeBound = m := by
    simpa +decide [p, fuel, packedLen, primeBound] using o_primeBound
  have p_logLen : p.regs logLen = Nat.log 2 n := by
    simpa +decide [p, fuel, packedLen, logLen] using o_logLen
  have p_height : p.regs height = h := by
    simpa +decide [p, fuel, packedLen, height] using o_height
  have p_one : p.regs one = 1 := by
    simpa +decide [p, fuel, packedLen, one] using o_one
  have p_two : p.regs two = 2 := by
    simpa +decide [p, fuel, packedLen, two] using o_two
  have p_fuel : p.regs fuel = Cslib.Algorithms.ThreeSum.ChanHe.fuel n := by
    simp +decide [p, fuel, packedLen]
  have p_packedLen : p.regs packedLen = 8 * m ^ 2 := by
    simp +decide [p, fuel, packedLen]
  have p_mem : p.mem = x.mem := o_memory
  refine ⟨p, ?_, ?_, p_mem⟩
  · exact (ea.seq
      (eb.seq
      (ec.seq
      (ed.seq
      (ee.seq
      (ef.seq
      (eg.seq
      (ej.seq
      (ek.seq
      (el.seq
      (eo.seq
      (ep)))))))))))).mono (by
      rw [time_zero]
      dsimp only [wp, h]
      exact le_of_eq (by ring))
  · exact ⟨p_len, p_magnitude, p_digits, p_height, p_fuel, p_want, p_primeBound, p_packedLen,
    p_padding⟩

/-- Read the native unsigned header and compute all parameters, preserving every memory cell.
This local theorem is discharged from a logarithmic width in `runs_input`. -/
theorem exec {w : ℕ} (κ : ℕ) (x : Data 24)
    (hfit : Fits w (Math.budget (x.mem 0) ((x.mem 0 + 2) ^ κ))) :
    ∃ y, ExecWithin w (program κ) x y (time κ (x.mem 0) ((x.mem 0 + 2) ^ κ)) ∧
      Output (x.mem 0) ((x.mem 0 + 2) ^ κ) y ∧ y.mem = x.mem := by
  let n := x.mem 0
  let U := (n + 2) ^ κ
  have fit (v : ℕ) (hv : v ≤ 8 * U + 4 * n + 64) : Fits w v :=
    hfit.of_le (by change v ≤ Math.budget n U; dsimp [Math.budget]; omega)
  have f1 : Fits w 1 := fit _ (by omega)
  have f2 : Fits w 2 := fit _ (by omega)
  have f3 : Fits w 3 := fit _ (by omega)
  have f4 : Fits w 4 := fit _ (by omega)
  have f5 : Fits w 5 := fit _ (by omega)
  have f8 : Fits w 8 := fit _ (by omega)
  have fb : Fits w (n + 2) := fit _ (by omega)
  have fU : Fits w U := fit _ (by omega)
  let a := (((((((((x.set quotient 0).set len n).set one 1).set two 2).set three 3).set
    four 4).set five 5).set eight 8).set base (n + 2))
  have ha : ExecWithin w setup x a 9 := by
    ram_eval [setup, a, n, f1, f2, f3, f4, f5, f8, fb,
      quotient, len, one, two, three, four, five, eight, base, Fin.mk.injEq]
  have hab : a.regs base = n + 2 := by simp [a]
  have hp := exec_power κ a (by rw [hab]; omega) (by simpa only [hab] using fU)
  let b := a.set magnitude U
  have hpb : ExecWithin w (power κ) a b (κ + 1) := by simpa only [hab] using hp
  obtain ⟨y, hy, hout, hm⟩ := exec_calculate b
    (by simp +decide [b, a, n, magnitude, len, base, one, two, three, four, five, eight, quotient])
    (by simp [b, U, n])
    (by simp +decide [b, a, magnitude, one, base, two, three, four, five, eight])
    (by simp +decide [b, a, magnitude, two, base, three, four, five, eight])
    (by simp +decide [b, a, magnitude, three, base, four, five, eight])
    (by simp +decide [b, a, magnitude, four, base, five, eight])
    (by simp +decide [b, a, magnitude, five, base, eight])
    (by simp +decide [b, a, magnitude, eight, base]) hfit
  refine ⟨y, (ha.seq (hpb.seq hy)).mono ?_, hout, hm⟩
  dsimp only [time]
  omega

namespace Math

open Cslib.Algorithms.ThreeSum

/-- A polynomial scale for bounding every parameter intermediate. -/
def scale (n U : ℕ) : ℕ := 16 * (n + 2) * (U + 1)

private theorem scale_bounds (n U : ℕ) :
    16 ≤ scale n U ∧ n + 2 ≤ scale n U ∧ 4 * U + 2 ≤ scale n U := by
  have h := Nat.mul_le_mul_left 16 (Nat.mul_le_mul
    (show 1 ≤ n + 2 by omega) (show 1 ≤ U + 1 by omega))
  have hn := Nat.le_mul_of_pos_right (n + 2) (show 0 < 16 * (U + 1) by positivity)
  have hU := Nat.le_mul_of_pos_right (U + 1) (show 0 < n + 2 by omega)
  dsimp [scale]
  have hnu := Nat.zero_le (n * U)
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

private theorem scale_pow_mono {b : ℕ} (hb : 1 ≤ b) {i j : ℕ} (hij : i ≤ j) :
    b ^ i ≤ b ^ j := Nat.pow_le_pow_right hb hij

/-- A coarse polynomial bound; it also covers final unsuccessful root/log iterations. -/
theorem budget_le_scale (n U : ℕ) : budget n U ≤ scale n U ^ 20 := by
  let b := scale n U
  obtain ⟨hb, hn, hU⟩ := scale_bounds n U
  change 16 ≤ b at hb
  change n + 2 ≤ b at hn
  change 4 * U + 2 ≤ b at hU
  have hb1 : 1 ≤ b := by omega
  have hΛ : labelBits (2 * U) ≤ b := by
    have hl := Nat.log_le_self 2 (4 * U)
    dsimp [labelBits]
    have he : 2 * (2 * U) = 4 * U := by omega
    rw [he]
    omega
  have hr : Nat.sqrt n + 1 ≤ b := by have := Nat.sqrt_le_self n; omega
  have hw : ChanHe.wPar n (2 * U) ≤ b ^ 3 := by
    calc
      _ ≤ b * b * b := by
        dsimp [ChanHe.wPar]
        exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) hΛ) hr
      _ = b ^ 3 := by ring
  have hws : ChanHe.wPar n (2 * U) + 1 ≤ b ^ 4 := by
    have hp : 1 ≤ b ^ 3 := Nat.one_le_pow _ _ hb1
    calc
      _ ≤ 2 * b ^ 3 := by omega
      _ ≤ b * b ^ 3 := Nat.mul_le_mul_right _ (by omega)
      _ = b ^ 4 := by ring
  have hfac : 2 * Nat.log 2 (ChanHe.wPar n (2 * U) + 1) + 4 ≤ b ^ 5 := by
    have hl := Nat.log_le_self 2 (ChanHe.wPar n (2 * U) + 1)
    have hp : 1 ≤ b ^ 4 := Nat.one_le_pow _ _ hb1
    calc
      _ ≤ 6 * b ^ 4 := by omega
      _ ≤ b * b ^ 4 := Nat.mul_le_mul_right _ (by omega)
      _ = b ^ 5 := by ring
  have hm : ChanHe.mPar n (2 * U) ≤ b ^ 9 := by
    calc
      _ ≤ b ^ 4 * b ^ 5 := Nat.mul_le_mul hws hfac
      _ = b ^ 9 := by ring
  have hms : ChanHe.mPar n (2 * U) + 1 ≤ 2 * b ^ 9 := by
    have hp : 1 ≤ b ^ 9 := Nat.one_le_pow _ _ hb1
    omega
  have hsq : (ChanHe.mPar n (2 * U) + 1) ^ 2 ≤ (2 * b ^ 9) ^ 2 :=
    Nat.pow_le_pow_left hms 2
  have hsmall : 8 * U + 4 * n + 64 ≤ 16 * b := by omega
  have hp18 : b ≤ b ^ 18 := by
    simpa only [pow_one] using scale_pow_mono hb1 (show 1 ≤ 18 by decide)
  have hbudget : budget n U ≤ 48 * b ^ 18 := by
    dsimp only [budget]
    nlinarith
  calc
    _ ≤ 48 * b ^ 18 := hbudget
    _ ≤ b ^ 2 * b ^ 18 := Nat.mul_le_mul_right _ (by nlinarith)
    _ = b ^ 20 := by ring

/-- A single polynomial bound, with exponent affine in the fixed magnitude exponent. -/
theorem budget_polynomial (κ n : ℕ) : budget n ((n + 2) ^ κ) ≤ (n + 2) ^ (20 * κ + 120) := by
  let a := n + 2
  have ha : 2 ≤ a := by dsimp [a]; omega
  have hpow : 1 ≤ a ^ κ := Nat.one_le_pow _ _ (by omega)
  have hs : scale n (a ^ κ) ≤ a ^ (κ + 6) := by
    calc
      _ = 16 * a * (a ^ κ + 1) := rfl
      _ ≤ 32 * a * a ^ κ := by nlinarith
      _ ≤ a ^ 5 * a * a ^ κ := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by
          have := Nat.pow_le_pow_left ha 5
          norm_num at this ⊢
          omega))
      _ = a ^ (κ + 6) := by ring
  calc
    _ ≤ scale n (a ^ κ) ^ 20 := budget_le_scale n (a ^ κ)
    _ ≤ (a ^ (κ + 6)) ^ 20 := Nat.pow_le_pow_left hs 20
    _ = a ^ (20 * κ + 120) := by ring

end Math
/-- Positive logarithmic word-width threshold for the complete parameter computation. -/
def width (κ n : ℕ) : ℕ := (20 * κ + 121) * Nat.clog 2 (n + 2)

/-- The width requirement is satisfiable even at empty input and exponent zero. -/
theorem width_pos (κ n : ℕ) : 0 < width κ n := by
  have := Nat.clog_pos (b := 2) (by decide) (show 1 < n + 2 by omega)
  dsimp [width]
  positivity

private theorem budget_le_two_pow (κ n : ℕ) :
    Math.budget n ((n + 2) ^ κ) ≤ 2 ^ ((20 * κ + 120) * Nat.clog 2 (n + 2)) := by
  calc
    _ ≤ (n + 2) ^ (20 * κ + 120) := Math.budget_polynomial κ n
    _ ≤ (2 ^ Nat.clog 2 (n + 2)) ^ (20 * κ + 120) :=
      Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
    _ = _ := by rw [← pow_mul]; congr 1; ring

/-- Every local fit premise follows from the positive logarithmic width. -/
theorem budget_fits {κ n w : ℕ} (hw : width κ n ≤ w) :
    Fits w (Math.budget n ((n + 2) ^ κ)) := by
  have hl := Nat.clog_pos (b := 2) (by decide) (show 1 < n + 2 by omega)
  apply Fits.mono (w := width κ n) _ hw
  apply (budget_le_two_pow κ n).trans_lt
  apply Nat.pow_lt_pow_right (by decide)
  dsimp [width]
  nlinarith

/-- Signed-encoded inputs and the unsigned length header fit at the same width. -/
theorem inputFits {κ w : ℕ} (input : List ℤ) (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    InputFits w (input.map Signed.encode) := by
  have hf := budget_fits hw
  refine ⟨?_, ?_⟩
  · simp only [List.length_map]
    apply hf.of_le
    dsimp [Math.budget]
    omega
  · intro v hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    have habs : z.natAbs ≤ (input.length + 2) ^ κ := by
      have hc : (z.natAbs : ℤ) ≤ ((input.length + 2) ^ κ : ℕ) := by
        simpa only [Int.natCast_natAbs] using hvalues z hz
      exact_mod_cast hc
    apply hf.of_le
    dsimp [Math.budget, Signed.encode]
    split_ifs <;> omega

/-- Explicit `Oκ(√n + log(n+2))` instruction bound, valid also at `n = 0,1,2`. -/
theorem time_bound (κ n : ℕ) :
    time κ n ((n + 2) ^ κ) ≤
      5 * Nat.sqrt n + (400 * κ + 3000) * Nat.clog 2 (n + 2) := by
  let U := (n + 2) ^ κ
  let L := Nat.clog 2 (n + 2)
  let E := 20 * κ + 120
  have hL : 1 ≤ L := Nat.clog_pos (by decide) (show 1 < n + 2 by omega)
  have hB : Nat.log 2 (Math.budget n U) ≤ E * L := by
    calc
      _ ≤ Nat.log 2 (2 ^ (E * L)) := Nat.log_mono_right (budget_le_two_pow κ n)
      _ = _ := Nat.log_pow (by decide) _
  have hlogU : Nat.log 2 (4 * U) ≤ E * L :=
    (Nat.log_mono_right (show 4 * U ≤ Math.budget n U by dsimp [Math.budget]; omega)).trans hB
  have hw := Math.want_le n U
  have hlogw : Nat.log 2 (Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U) + 1) ≤ E * L := by
    apply (Nat.log_mono_right ?_).trans hB
    dsimp [Math.budget]
    nlinarith
  have hlogn : Nat.log 2 n ≤ E * L :=
    (Nat.log_mono_right (show n ≤ Math.budget n U by dsimp [Math.budget]; omega)).trans hB
  have hh := Math.height_le n
  change time κ n U ≤ _
  dsimp only [time]
  dsimp only [E, L] at *
  nlinarith

/-- Native run from actual signed input initialization. No parameters or arithmetic routines
are supplied as advice. The returned state identifies all outputs and keeps *all* input memory.
The flat program has 24 registers and depends only on `κ`; halting adds one instruction. -/
theorem runs_input {κ w : ℕ} (input : List ℤ) (hw : width κ input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ)) :
    ∃ y t, t ≤ 5 * Nat.sqrt input.length +
        (400 * κ + 3000) * Nat.clog 2 (input.length + 2) ∧
      Runs w ((program κ).program packedLen) (State.init (input.map Signed.encode))
        ⟨(program κ).size, y⟩ t ∧
      Output input.length ((input.length + 2) ^ κ) y ∧
      y.mem = (Data.init (input.map Signed.encode) : Data 24).mem ∧ y.Bounded w := by
  have hi := inputFits input hw hvalues
  obtain ⟨y, hy, ho, hm⟩ := exec κ (Data.init (input.map Signed.encode))
    (by simpa only [Data.init_mem_zero, List.length_map] using budget_fits hw)
  simp only [Data.init_mem_zero, List.length_map] at hy ho
  obtain ⟨t, ht, he⟩ := hy
  have hr := he.runs (pc := 0) (p := (program κ).program packedLen)
    (Program.Contains.self _).append_left
  simp only [Nat.zero_add] at hr
  refine ⟨y, t, ht.trans (time_bound κ input.length), hr, ho, hm, ?_⟩
  exact hr.bounded_init hi

/-- The number of native instructions in the finite structured code is affine in `κ`. -/
theorem size_program (κ : ℕ) : (program κ).size = κ + 71 := by
  have hp : (power κ).size = κ + 1 := by
    induction κ with
    | zero => rfl
    | succ κ ih => simp [power, ih]
  simp only [program, setup, calculate, NatLog.program, NatLog.body, NatSqrt.program,
    NatSqrt.body, NatClog.program, NatClog.body, Code.size.eq_2, Code.size, Nat.reduceAdd, hp,
    Code.size_rename]
  omega

/-- The code is the same at every word width. -/
theorem not_readsWidth (κ : ℕ) : ¬(program κ).ReadsWidth := by
  have hs : ¬setup.ReadsWidth := by decide
  have hc : ¬calculate.ReadsWidth := by decide
  have hp : ¬(power κ).ReadsWidth := by
    induction κ with
    | zero => decide
    | succ κ ih =>
      change ¬((power κ).ReadsWidth ∨
        (Code.op (Op.bin BinOp.mul magnitude magnitude base) : Code .standard 24).ReadsWidth)
      exact not_or.mpr ⟨ih, by decide⟩
  simpa only [program, Code.ReadsWidth, not_or] using And.intro hs (And.intro hp hc)

/-- Canonical-width executions use only polynomially bounded integers, including memory
addresses, loop counters, and final unsuccessful tests. -/
theorem intermediates_polynomial {κ : ℕ} (input : List ℤ)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ))
    {s : State 24} {t : ℕ}
    (hr : Runs (width κ input.length) ((program κ).program packedLen)
      (State.init (input.map Signed.encode)) s t) :
    (∀ i, s.data.regs i < (input.length + 2) ^ (40 * κ + 242)) ∧
      ∀ a, s.data.mem a < (input.length + 2) ^ (40 * κ + 242) := by
  let n := input.length
  let L := Nat.clog 2 (n + 2)
  have hL : 0 < L := Nat.clog_pos (by decide) (by omega)
  have hpred : 2 ^ (L - 1) < n + 2 :=
    Nat.pow_pred_clog_lt_self (b := 2) (x := n + 2) (by decide) (by omega)
  have he : 2 ^ L = 2 * 2 ^ (L - 1) := by
    conv_lhs => rw [show L = (L - 1) + 1 by omega]
    rw [pow_succ, Nat.mul_comm]
  have hceil : 2 ^ L ≤ (n + 2) ^ 2 := by rw [he]; nlinarith
  have hpoly : 2 ^ width κ n ≤ (n + 2) ^ (40 * κ + 242) := by
    calc
      _ = (2 ^ L) ^ (20 * κ + 121) := by
        dsimp only [width, L]
        rw [← pow_mul]
        congr 1
        ring
      _ ≤ ((n + 2) ^ 2) ^ (20 * κ + 121) := Nat.pow_le_pow_left hceil _
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hb := hr.bounded_init (inputFits input le_rfl hvalues)
  exact ⟨fun i => (hb.1 i).trans_le hpoly, fun a => (hb.2 a).trans_le hpoly⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Parameters
