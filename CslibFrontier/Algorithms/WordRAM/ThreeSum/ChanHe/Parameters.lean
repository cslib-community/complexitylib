/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.ThreeSum.ChanHe.Defs
public import CslibFrontier.Algorithms.WordRAM.NatLog
public import CslibFrontier.Algorithms.WordRAM.NatClog
public import CslibFrontier.Algorithms.WordRAM.NatSqrt
public import CslibFrontier.Computability.WordRAM.Compile
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Foundations.Data.Nat.Log
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
* `Parameters.two_pow_width_le`: words at the canonical width have polynomial magnitude.

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

/-- Unroll only the compile-time fixed exponent `κ`, never the input length or word width.
Unlike `WordRAM.Power.program`, which loops over a runtime exponent register using counter and
constant-one scratch registers, `power κ` emits `κ + 1` straight-line instructions over `magnitude`
and `base` alone and requires no `Fits w (κ + 1)` budget premise at empty input (`n = 0`). -/
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

private theorem exec_calculate_tail {w n U : ℕ} (k : Data 24)
    (k_len : k.regs len = n) (k_magnitude : k.regs magnitude = U)
    (k_digits : k.regs digits = Cslib.Algorithms.ThreeSum.labelBits (2 * U))
    (k_padding : k.regs padding = 4 * U + 1)
    (k_want : k.regs want = Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U))
    (k_primeBound : k.regs primeBound = Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U))
    (k_logLen : k.regs logLen = Nat.log 2 n)
    (k_two : k.regs two = 2) (k_three : k.regs three = 3)
    (k_eight : k.regs eight = 8)
    (hfit : Fits w (Math.budget n U)) :
    ∃ p, ExecWithin w
      (.seq (ram[ quotient ← logLen + two ])
      (.seq (NatClog.program.rename (logRegisters height))
      (ram[ fuel ← three * height; fuel ← fuel - two; packedLen ← primeBound * primeBound;
        packedLen ← eight * packedLen ])))
      k p (10 + 5 * Cslib.Algorithms.ThreeSum.ChanHe.height n) ∧
      Output n U p ∧ p.mem = k.mem := by
  let Λ := Cslib.Algorithms.ThreeSum.labelBits (2 * U)
  let h := Cslib.Algorithms.ThreeSum.ChanHe.height n
  let wp := Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U)
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  change k.regs digits = Λ at k_digits
  change k.regs want = wp at k_want
  change k.regs primeBound = m at k_primeBound
  have eh : Cslib.Algorithms.ThreeSum.ChanHe.fuel n = 3 * h - 2 := rfl
  have hh : h ≤ Nat.log 2 n + 2 := Math.height_le n
  have hl := Nat.log_le_self 2 n
  have fitn (v : ℕ) (hv : v ≤ 4 * n + 64) : Fits w v :=
    hfit.of_le (by dsimp [Math.budget]; omega)
  have f2 : Fits w 2 := fitn _ (by omega)
  have flog2 : Fits w (Nat.log 2 n + 2) := fitn _ (by omega)
  have flog3 : Fits w (Nat.log 2 n + 2 + 1) := fitn _ (by omega)
  have fh : Fits w (h + 1) := fitn _ (by omega)
  have f3h : Fits w (3 * h) := fitn _ (by omega)
  have ffuel : Fits w (Cslib.Algorithms.ThreeSum.ChanHe.fuel n) :=
    fitn _ (by dsimp [Cslib.Algorithms.ThreeSum.ChanHe.fuel]; omega)
  have fm2 : Fits w (m * m) := hfit.of_le (by dsimp [Math.budget]; nlinarith)
  have fN : Fits w (8 * m ^ 2) := hfit.of_le (by dsimp [Math.budget]; nlinarith)
  have fNm : Fits w (8 * (m * m)) := by simpa only [pow_two] using fN
  wram_exec [k_logLen, k_two, flog2]
  wram_call (NatClog.exec _ f2
    (by wram_simp [NatClog.arg, logRegisters, flog3])
    (by wram_simp [NatClog.arg, logRegisters, h,
      Cslib.Algorithms.ThreeSum.ChanHe.height]; exact fh)) canonical
    (by decide : (logRegisters height).Injective) with o ⟨oh, om, oo, ot⟩
  wram_exec [logRegisters, NatClog.result, NatClog.one, NatClog.two, oh, oo, ot,
    k_three, k_primeBound, k_eight, ← eh, f3h, ffuel, fm2, fNm,
    show Nat.clog 2 (Nat.log 2 n + 2) = h from rfl]
  refine ⟨?_, ?_⟩
  · constructor <;> wram_simp [logRegisters, NatClog.result, oh, k_len, k_magnitude,
      k_digits, k_want, k_primeBound, k_padding, ← eh, pow_two, Λ, wp, m, h,
      Cslib.Algorithms.ThreeSum.ChanHe.height, Cslib.Algorithms.ThreeSum.ChanHe.fuel]
  · wram_simp [om]

private theorem exec_calculate_suffix {w n U : ℕ} (f : Data 24)
    (f_len : f.regs len = n) (f_magnitude : f.regs magnitude = U)
    (f_digits : f.regs digits = Cslib.Algorithms.ThreeSum.labelBits (2 * U))
    (f_padding : f.regs padding = 4 * U + 1)
    (f_want : f.regs want = Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U))
    (f_wantSucc : f.regs wantSucc = Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U) + 1)
    (f_temp : f.regs temp = Nat.log 2 (Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U) + 1))
    (f_two : f.regs two = 2) (f_three : f.regs three = 3)
    (f_four : f.regs four = 4) (f_eight : f.regs eight = 8)
    (hfit : Fits w (Math.budget n U)) :
    ∃ p, ExecWithin w
      (.seq (ram[ temp ← two * temp; temp ← temp + four; primeBound ← wantSucc * temp ])
      (.seq (ram[ quotient ← len ])
      (.seq (NatLog.program.rename (logRegisters logLen))
      (.seq (ram[ quotient ← logLen + two ])
      (.seq (NatClog.program.rename (logRegisters height))
      (ram[ fuel ← three * height; fuel ← fuel - two; packedLen ← primeBound * primeBound;
        packedLen ← eight * packedLen ]))))))
      f p (19 + 4 * Nat.log 2 n + 5 * Cslib.Algorithms.ThreeSum.ChanHe.height n) ∧
      Output n U p ∧ p.mem = f.mem := by
  let Λ := Cslib.Algorithms.ThreeSum.labelBits (2 * U)
  let h := Cslib.Algorithms.ThreeSum.ChanHe.height n
  let wp := Cslib.Algorithms.ThreeSum.ChanHe.wPar n (2 * U)
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * U)
  change f.regs digits = Λ at f_digits
  change f.regs want = wp at f_want
  change f.regs wantSucc = wp + 1 at f_wantSucc
  change f.regs temp = Nat.log 2 (wp + 1) at f_temp
  have em : m = (wp + 1) * (2 * Nat.log 2 (wp + 1) + 4) := rfl
  have hf : 2 * Nat.log 2 (wp + 1) + 4 ≤ m := Math.factor_le n U
  have hl := Nat.log_le_self 2 n
  have hml : Fits w m := hfit.of_le (by dsimp [Math.budget]; nlinarith)
  have fitm (v : ℕ) (hv : v ≤ m) : Fits w v := hml.of_le hv
  have fitn (v : ℕ) (hv : v ≤ 4 * n + 64) : Fits w v :=
    hfit.of_le (by dsimp [Math.budget]; omega)
  have f2 : Fits w 2 := fitn _ (by omega)
  have f2log : Fits w (2 * Nat.log 2 (wp + 1)) := fitm _ (by omega)
  have ff : Fits w (2 * Nat.log 2 (wp + 1) + 4) := fitm _ hf
  have fn : Fits w n := fitn _ (by omega)
  have flogn : Fits w (Nat.log 2 n + 1) := fitn _ (by omega)
  wram_exec [f_two, f_temp, f_four, f_wantSucc, ← em, f2log, ff, hml, f_len]
  wram_call (NatLog.exec _ f2
    (by wram_simp [NatLog.arg, logRegisters, f_len, fn])
    (by wram_simp [NatLog.arg, logRegisters, f_len, flogn])) canonical
    (by decide : (logRegisters logLen).Injective) with k ⟨kl, km, _, kt⟩
  wram_call (exec_calculate_tail _
    (by wram_simp [f_len]) (by wram_simp [f_magnitude])
    (by wram_simp [f_digits, Λ]) (by wram_simp [f_padding])
    (by wram_simp [f_want, wp]) (by wram_simp [m])
    (by wram_simp [logRegisters, NatLog.result, kl, f_len])
    (by wram_simp [logRegisters, NatLog.two, kt])
    (by wram_simp [f_three]) (by wram_simp [f_eight]) hfit) with p ⟨hp, hm⟩
  refine ⟨?_, hp, ?_⟩
  · wram_simp [logRegisters, NatLog.arg, f_len]
    omega
  · wram_simp [hm, km]

private theorem exec_calculate {w n U : ℕ} (x : Data 24)
    (hlen : x.regs len = n) (hU : x.regs magnitude = U)
    (h1 : x.regs one = 1) (h3 : x.regs three = 3)
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
  have hd : 5 * Λ ≤ wp := Math.digits_le n U
  have hw : wp + 1 ≤ m := Math.want_le n U
  have hf : 2 * Nat.log 2 (wp + 1) + 4 ≤ m := Math.factor_le n U
  have hroot := Nat.sqrt_le_self n
  have hml : Fits w m := hfit.of_le (by dsimp [Math.budget]; nlinarith)
  have fitm (v : ℕ) (hv : v ≤ m) : Fits w v := hml.of_le hv
  have fitu (v : ℕ) (hv : v ≤ 8 * U + 64) : Fits w v :=
    hfit.of_le (by dsimp [Math.budget]; omega)
  have fitn (v : ℕ) (hv : v ≤ 4 * n + 64) : Fits w v :=
    hfit.of_le (by dsimp [Math.budget]; omega)
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
  unfold calculate
  wram_exec [h4, hU, h1, f4U, fpad]
  wram_call (NatLog.exec _ f2
    (by wram_simp [NatLog.arg, logRegisters, f4U])
    (by wram_simp [NatLog.arg, logRegisters, flogU])) canonical
    (by decide : (logRegisters digits).Injective) with b ⟨bd, bm, bo, bt⟩
  wram_exec [logRegisters, NatLog.result, NatLog.one, bd, bo, ← eΛ, fΛ]
  wram_call (NatSqrt.exec _
    (by wram_simp [sqrtRegisters, NatSqrt.arg, hlen, fsqrt])) canonical
    sqrt_injective with d ⟨dr, dl, dm, done⟩
  wram_exec [sqrtRegisters, NatSqrt.root, NatSqrt.one, dr, done, hlen,
    logRegisters, h5, ← ew, fr, f5Λ, fwp, fwps, ← eΛ]
  wram_call (NatLog.exec _ f2
    (by wram_simp [NatLog.arg, logRegisters, fwps])
    (by wram_simp [NatLog.arg, logRegisters, flogwp])) canonical
    (by decide : (logRegisters temp).Injective) with f ⟨ft, fm, _, ftt⟩
  wram_call (exec_calculate_suffix _
    (by wram_simp [sqrtRegisters, NatSqrt.arg, dl, hlen])
    (by wram_simp [hU]) (by wram_simp [← eΛ, Λ]) (by wram_simp)
    (by wram_simp [wp]) (by wram_simp [wp])
    (by wram_simp [logRegisters, NatLog.result, ft, wp])
    (by wram_simp [logRegisters, NatLog.two, ftt])
    (by wram_simp [h3]) (by wram_simp [h4]) (by wram_simp [h8]) hfit) with p ⟨hp, hm⟩
  refine ⟨?_, hp, ?_⟩
  · wram_simp [time_zero, logRegisters, NatLog.arg, sqrtRegisters, NatSqrt.arg,
      hlen, wp, h]
    omega
  · wram_simp [hm, fm, dm, bm]

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

/-- A word at the canonical width has polynomial magnitude. -/
theorem two_pow_width_le (κ n : ℕ) : 2 ^ width κ n ≤ (n + 2) ^ (40 * κ + 242) := by
  have hpow := Nat.pow_clog_le_mul (by decide : 1 < 2) (by omega : n + 2 ≠ 0)
  have hsq : 2 * (n + 2) ≤ (n + 2) ^ 2 := by nlinarith
  calc
    2 ^ width κ n = (2 ^ Nat.clog 2 (n + 2)) ^ (20 * κ + 121) := by
      rw [width, ← pow_mul, Nat.mul_comm]
    _ ≤ ((n + 2) ^ 2) ^ (20 * κ + 121) := Nat.pow_le_pow_left (hpow.trans hsq) _
    _ = _ := by rw [← pow_mul]; congr 1; omega

/-- Canonical-width executions use only polynomially bounded integers, including memory
addresses, loop counters, and final unsuccessful tests. -/
theorem intermediates_polynomial {κ : ℕ} (input : List ℤ)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ))
    {s : State 24} {t : ℕ}
    (hr : Runs (width κ input.length) ((program κ).program packedLen)
      (State.init (input.map Signed.encode)) s t) :
    (∀ i, s.data.regs i < (input.length + 2) ^ (40 * κ + 242)) ∧
      ∀ a, s.data.mem a < (input.length + 2) ^ (40 * κ + 242) := by
  have hpoly := two_pow_width_le κ input.length
  have hb := hr.bounded_init (inputFits input le_rfl hvalues)
  exact ⟨fun i => (hb.1 i).trans_le hpoly, fun a => (hb.2 a).trans_le hpoly⟩

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Parameters
