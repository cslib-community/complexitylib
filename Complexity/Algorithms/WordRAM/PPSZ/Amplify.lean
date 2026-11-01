/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.PPSZ.Round
public import Complexity.Algorithms.WordRAM.PPZ.Amplify
public import Complexity.Computability.Complexity.FineGrained.PPSZ.General

/-!
# The PPSZ algorithm on the randomized word RAM

`Cslib.Algorithms.WordRAM.PPSZ.ampProgram` is the PPSZ k-SAT algorithm
[Paturi, Pudlák, Saks, Zane][PaturiPudlakSaksZane2005] with w-implication [Hertli][Hertli2011]
and confidence `c`, as a program of the randomized word RAM. On the input
`s :: a :: b :: c :: encode φ` it computes the number of rounds
`R = ppszRounds a b n c = 2 ^ ⌈a n / b⌉ c` in a multiword counter, then runs up to `R` independent
rounds of PPSZ with the bound `s` (`Cslib.Algorithms.WordRAM.PPSZ.roundProgram`), stopping at the
first round whose assignment satisfies the formula. It halts with output `1`, leaving a satisfying
assignment in memory, or with output `0` when every round failed.

The rational `a / b` is an upper bound on the exponent of the success probability of one round,
supplied with the input. The bound proved for satisfiable formulas with clauses of at most `k ≥ 3`
literals and `s ≥ ∑ i < h, (k - 1) ^ i` is `2 ^ (-(1 - qbar k h) n)`
(`Cslib.Complexity.PPSZ.round_success_of_satisfiable`), and `qbar k h` is the value of an integral.
The program does not compute it: the failure bound
`Cslib.Algorithms.WordRAM.PPSZ.ampProgram_failure_le_exp` assumes `1 - qbar k h ≤ a / b`. For
3-SAT, `qbar 3 2 = 31 / 70` gives the choice `(s, a, b) = (3, 39, 70)`
(`Cslib.Algorithms.WordRAM.PPSZ.ampProgram_failure_le_exp_three`). With `(a, b) = (k - 1, k)`, the
number of rounds is that of PPZ (`Cslib.Algorithms.WordRAM.PPZ.ppzRounds`).

The program reuses the amplified loop of PPZ (`Cslib.Algorithms.WordRAM.PPZ.ampLoopWith`) with the
round body of PPSZ (`Cslib.Algorithms.WordRAM.PPSZ.roundCore_isRoundCore`). The words that the
oracle reads after the order array, `s` and `2 s` zero words, come before the counter.

`Cslib.Algorithms.WordRAM.PPSZ.ampProgram_spec` proves, at every word size `w` with
`L + 2 n + 2 s + a n + b + 2 c + ppszCounterLen a b n c + 3 < 2 ^ w`, where `L` is the input length
and `ppszCounterLen a b n c = ⌈a n / b⌉ + 1 + (number of binary digits of c)` bounds the number of
digits of `R`:

* the program halts on every path within `ampTime s a b c n L` instructions, which is
  `R (n (impliedTime s L + 25) + 12 L + 41)` plus a setup cost linear in the counter length;
* it makes at most `2 n R` `rand` calls;
* an output `1` always comes with a satisfying assignment, so the program never errs on
  unsatisfiable formulas;
* the output is `1` with exactly the law of `R` independent rounds of PPSZ, so it is `0` with
  probability exactly `(1 - p) ^ R`, where `p` is the probability that one round finds a
  satisfying assignment.

The running time is `O((s + 1)² (n + L) ^ (2 s + 1) 2 ^ ((a / b) n) (c + 1))`
(`Cslib.Algorithms.WordRAM.PPSZ.ampTime_le`).

## Main definitions

* `Cslib.Algorithms.WordRAM.PPSZ.ppszExp`, `Cslib.Algorithms.WordRAM.PPSZ.ppszRounds`: the number of
  rounds.
* `Cslib.Algorithms.WordRAM.PPSZ.ampCode`, `Cslib.Algorithms.WordRAM.PPSZ.ampProgram`: the amplified
  algorithm, structured and compiled.
* `Cslib.Algorithms.WordRAM.PPSZ.ampTime`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.PPSZ.roundCore_isRoundCore`: the round body of PPSZ in the amplified
  loop.
* `Cslib.Algorithms.WordRAM.PPSZ.ampProgram_spec`: halting, time and `rand` bounds, no false
  positives, and the exact law of the output.
* `Cslib.Algorithms.WordRAM.PPSZ.ampProgram_failure_le_exp`: on a satisfiable k-CNF the program
  fails with probability at most `e ^ (-c)`.
* `Cslib.Algorithms.WordRAM.PPSZ.ampProgram_failure_le_exp_three`: the same for 3-CNF with
  `(s, a, b) = (3, 39, 70)`.
* `Cslib.Algorithms.WordRAM.PPSZ.ampProgram_failure_le_exp_limit`: the `ε`-form, for every
  `a / b ≥ 1 - μ_k / (k - 1) + ε` with a bound `s` depending on `k` and `ε`.
* `Cslib.Algorithms.WordRAM.PPSZ.ampTime_le`: the time bound.

## References

* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
* [T. Hertli, *3-SAT faster and simpler*][Hertli2011]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PPSZ

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.PPSZ
open Cslib.Algorithms.WordRAM.Schoening (encodeClauses encode assignmentAt length_encode)
open Cslib.Algorithms.WordRAM.PPZ (RoundFrame IsRoundCore AmpState AmpPost roundCoreWith
  ampLoopWith ampLoopWith_law countSetup countSetup_spec countSetupTime countDigits
  repeatRoundWith roundSuccessProbWith)
open Cslib.Algorithms.WordRAM.PPZ.Reg

variable {n : ℕ}

/-! ### Registers -/

namespace Reg

/-- The numerator `a` of the bound on the exponent, during the setup; shares register `6` with
`sReg`. -/
abbrev numReg : Fin 32 := 6
/-- The denominator `b` of the bound on the exponent, during the setup; shares register `9` with
`jR`. -/
abbrev denReg : Fin 32 := 9

end Reg

open Reg

/-! ### The round body -/

/-- **The body of a round of PPSZ is a round body** for `Cslib.Complexity.PPSZ.implied φ s`, on
rounds whose memory holds `s` and `2 s` zero words just after the order array. -/
theorem roundCore_isRoundCore {φ : CNF (Fin n)} {C Tb s w : ℕ}
    (hw : Fits w (Tb + 2 * n + 2 * s + 2)) :
    IsRoundCore w φ C Tb (s :: List.replicate (2 * s) 0) (implied φ s) (roundCoreWith impliedCode)
      (n * (impliedTime s (encodeClauses φ).length + 25) + 6) where
  preserves_bBase := by decide
  preserves_bLen := by decide
  preserves_flag := by decide
  law M x hx hS := roundCore_law (by simpa using hS.get 0 (by simp))
    (fun i hi => by
      have h := hS.get (i + 1) (by simp; omega)
      rw [show Tb + 2 * n + (i + 1) = Tb + 2 * n + 1 + i by omega] at h
      simpa [List.getElem_replicate] using h)
    hw hx

/-! ### The number of rounds -/

/-- The exponent `⌈a n / b⌉` of the number of rounds. -/
def ppszExp (a b n : ℕ) : ℕ := (a * n + b - 1) / b

/-- **The number of rounds** of PPSZ with confidence `c` on `n` variables, for the bound `a / b` on
the exponent: `2 ^ ⌈a n / b⌉ c`. -/
def ppszRounds (a b n c : ℕ) : ℕ := 2 ^ ppszExp a b n * c

/-- The binary digits of the number of rounds, as the setup computes them. -/
def ppszDigits (a b n c : ℕ) : List ℕ := countDigits (ppszExp a b n) c

/-- A bound on the number of digits of the number of rounds. -/
def ppszCounterLen (a b n c : ℕ) : ℕ := ppszExp a b n + 1 + (Nat.digits 2 c).length

theorem ofDigits_ppszDigits (a b n c : ℕ) :
    Nat.ofDigits 2 (ppszDigits a b n c) = ppszRounds a b n c :=
  PPZ.ofDigits_countDigits _ _

/-- The exponent is at least `(a / b) n`. -/
theorem le_ppszExp {a b : ℕ} (hb : 0 < b) (n : ℕ) : (a : ℝ) / b * n ≤ ppszExp a b n := by
  have hkn : a * n ≤ b * ppszExp a b n := by
    have h := Nat.div_add_mod (a * n + b - 1) b
    have h' := Nat.mod_lt (a * n + b - 1) hb
    simp only [ppszExp]
    omega
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hr : (a : ℝ) * n ≤ b * ppszExp a b n := by exact_mod_cast hkn
  rw [div_mul_eq_mul_div, div_le_iff₀ hb0]
  linarith

/-- The exponent is at most `(a / b) n + 1`. -/
theorem ppszExp_le_add_one {a b : ℕ} (hb : 0 < b) (n : ℕ) :
    (ppszExp a b n : ℝ) ≤ (a : ℝ) / b * n + 1 := by
  have hkn : b * ppszExp a b n ≤ a * n + b := by
    have := Nat.div_mul_le_self (a * n + b - 1) b
    simp only [ppszExp]
    rw [Nat.mul_comm]
    omega
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hr : (b : ℝ) * ppszExp a b n ≤ a * n + b := by exact_mod_cast hkn
  rw [show (a : ℝ) / b * n + 1 = (a * n + b) / b by field_simp, le_div_iff₀ hb0]
  linarith

/-! ### The setup -/

/-- Set up the registers on the input `s :: a :: b :: c :: encode φ`: the clauses start at address
`6`, the partial assignment is stored just after the input, then the order array; `s` is copied to
the word after the order array, the counter starts after the `2 s` words that follow it, and
`eReg = ⌈a n / b⌉`. -/
def ampSetup : Code .standard 32 := ram[
  one ← #1; two ← #2; val ← *zero; tBase ← val + one; cEnd ← tBase;
  val ← one + one; numReg ← *val; val ← val + one; denReg ← *val; val ← val + one; cReg ← *val;
  val ← val + one; nReg ← *val; cBeg ← val + one; pBase ← tBase + nReg;
  addr ← pBase + nReg; val ← *one; *addr ← val; bBase ← addr + one; bBase ← bBase + val;
  bBase ← bBase + val;
  eReg ← numReg * nReg; eReg ← eReg + denReg; eReg ← eReg - one; eReg ← eReg / denReg ]

/-- The data after the setup on the input `s :: a :: b :: c :: encode φ`. -/
def ampSetupData (s a b c : ℕ) (φ : CNF (Fin n)) : Data 32 :=
  ((((((((((((((((((((((((((Data.init (s :: a :: b :: c :: encode φ)).set one 1).set two
    2).set val (s :: a :: b :: c :: encode φ).length).set tBase
    ((s :: a :: b :: c :: encode φ).length + 1)).set cEnd
    ((s :: a :: b :: c :: encode φ).length + 1)).set val 2).set numReg a).set val 3).set denReg
    b).set val 4).set cReg c).set val 5).set nReg n).set cBeg 6).set pBase
    ((s :: a :: b :: c :: encode φ).length + 1 + n)).set addr
    ((s :: a :: b :: c :: encode φ).length + 1 + n + n)).set val s).write
    ((s :: a :: b :: c :: encode φ).length + 1 + n + n) s).set bBase
    ((s :: a :: b :: c :: encode φ).length + 1 + n + n + 1)).set bBase
    ((s :: a :: b :: c :: encode φ).length + 1 + n + n + 1 + s)).set bBase
    ((s :: a :: b :: c :: encode φ).length + 1 + n + n + 1 + s + s)).set eReg (a * n)).set eReg
    (a * n + b)).set eReg (a * n + b - 1)).set eReg (ppszExp a b n))

/-- The memory after the setup: the input, then `s` at `L + 1 + 2 n`, and zero after it. -/
theorem ampSetupData_mem (s a b c : ℕ) (φ : CNF (Fin n)) (x : ℕ) :
    (ampSetupData s a b c φ).mem x =
      if x = (s :: a :: b :: c :: encode φ).length + 1 + n + n then s
      else (Data.init (s :: a :: b :: c :: encode φ) : Data 32).mem x := by
  simp only [ampSetupData, Data.write_mem, Data.set_mem, Function.update_apply]

/-- The setup establishes the frame of the rounds on the input `s :: a :: b :: c :: encode φ`. -/
theorem ampSetup_exec (s a b c : ℕ) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((s :: a :: b :: c :: encode φ).length + 2 * n + 2 * s + a * n + b + 2)) :
    ExecWithin w ampSetup (Data.init (s :: a :: b :: c :: encode φ)) (ampSetupData s a b c φ) 25 ∧
      RoundFrame φ 6 ((s :: a :: b :: c :: encode φ).length + 1) (ampSetupData s a b c φ).mem
        (ampSetupData s a b c φ) := by
  have hL : 5 ≤ (s :: a :: b :: c :: encode φ).length := by simp [encode]
  have hf1 : Fits w 1 := hw.of_le (by omega)
  have hf2 : Fits w 2 := hw.of_le (by omega)
  have hf3 : Fits w 3 := hw.of_le (by omega)
  have hf4 : Fits w 4 := hw.of_le (by omega)
  have hf5 : Fits w 5 := hw.of_le (by omega)
  have hf6 : Fits w 6 := hw.of_le (by omega)
  have hf7 : Fits w ((s :: a :: b :: c :: encode φ).length + 1) := hw.of_le (by omega)
  have hf8 : Fits w ((s :: a :: b :: c :: encode φ).length + 1 + n) := hw.of_le (by omega)
  have hf9 : Fits w ((s :: a :: b :: c :: encode φ).length + 1 + n + n) := hw.of_le (by omega)
  have hf10 : Fits w ((s :: a :: b :: c :: encode φ).length + 1 + n + n + 1) :=
    hw.of_le (by omega)
  have hf11 : Fits w ((s :: a :: b :: c :: encode φ).length + 1 + n + n + 1 + s) :=
    hw.of_le (by omega)
  have hf12 : Fits w ((s :: a :: b :: c :: encode φ).length + 1 + n + n + 1 + s + s) :=
    hw.of_le (by omega)
  have hf13 : Fits w (a * n) := hw.of_le (by omega)
  have hf14 : Fits w (a * n + b) := hw.of_le (by omega)
  have hf15 : Fits w (a * n + b - 1) := hw.of_le (by omega)
  have hf16 : Fits w ((a * n + b - 1) / b) := hw.of_le (by
    have := Nat.div_le_self (a * n + b - 1) b; omega)
  have hm0 : (Data.init (s :: a :: b :: c :: encode φ) : Data 32).mem 0 =
      (s :: a :: b :: c :: encode φ).length := rfl
  have hm1 : (Data.init (s :: a :: b :: c :: encode φ) : Data 32).mem 1 = s := rfl
  have hm2 : (Data.init (s :: a :: b :: c :: encode φ) : Data 32).mem 2 = a := rfl
  have hm3 : (Data.init (s :: a :: b :: c :: encode φ) : Data 32).mem 3 = b := rfl
  have hm4 : (Data.init (s :: a :: b :: c :: encode φ) : Data 32).mem 4 = c := rfl
  have hm5 : (Data.init (s :: a :: b :: c :: encode φ) : Data 32).mem 5 = n := rfl
  refine ⟨?run, ?frame⟩
  case run =>
    ram_eval [ampSetup, ampSetupData, ppszExp, Data.init_regs, hm0, hm1, hm2, hm3, hm4, hm5, hf1,
      hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16]
  case frame =>
    refine ⟨by simp +decide [ampSetupData], by simp +decide [ampSetupData],
      by simp +decide [ampSetupData], by simp +decide [ampSetupData],
      by simp +decide [ampSetupData], by simp +decide [ampSetupData],
      by simp +decide [ampSetupData], by simp +decide [ampSetupData], ?_, ?_, fun _ _ => rfl⟩
    · intro i
      have hi : i.val < (encodeClauses φ).length := i.isLt
      change (ampSetupData s a b c φ).mem (6 + i.val) = (encodeClauses φ)[i.val]
      rw [ampSetupData_mem, ite_eq_right_iff.mpr (fun h => by simp [length_encode] at h; omega),
        show 6 + i.val = (5 + i.val) + 1 by omega, Data.init_mem_succ]
      simp [encode, show 5 + i.val = (i.val + 1) + 1 + 1 + 1 + 1 by omega]
    · simp [length_encode]; omega

/-! ### The algorithm -/

/-- **The PPSZ algorithm** on the input `s :: a :: b :: c :: encode φ`. -/
def ampCode : Code .standard 32 :=
  ram[ ⟪ampSetup⟫; ⟪countSetup⟫; flag ← one; ⟪ampLoopWith (roundCoreWith impliedCode)⟫ ]

/-- **The PPSZ algorithm** on the input `s :: a :: b :: c :: encode φ`, halting with `out`. -/
def ampProgram : Program .standard 32 := ampCode.program out

/-- The instruction bound of the PPSZ algorithm with the bound `s`, the bound `a / b` on the
exponent and confidence `c`, on `n` variables and an input of length `L`. -/
def ampTime (s a b c n L : ℕ) : ℕ :=
  ppszRounds a b n c * (n * (impliedTime s L + 25) + 12 * L + 41) + 5 * ppszExp a b n +
    19 * ppszCounterLen a b n c + 70

/-- **The PPSZ algorithm on the randomized word RAM.** On the input `s :: a :: b :: c :: encode φ`
of length `L`, at any word size `w` with
`L + 2 n + 2 s + a n + b + 2 c + ppszCounterLen a b n c + 3 < 2 ^ w`, the program

* halts on every path within `ampTime s a b c n L` instructions;
* makes at most `R (2 n)` `rand` calls, where `R = ppszRounds a b n c`;
* outputs `0` or `1`, and outputs `1` only with a satisfying assignment of `φ` stored at address
  `L + 1`;
* outputs `1` with exactly the law `repeatRoundWith (implied φ s) φ R` of up to `R` independent
  rounds of PPSZ with the bound `s`. -/
theorem ampProgram_spec (s a b c : ℕ) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((s :: a :: b :: c :: encode φ).length + 2 * n + 2 * s + a * n + b + 2 * c +
      ppszCounterLen a b n c + 3)) :
    RandHaltsWithin w ampProgram (.init (s :: a :: b :: c :: encode φ))
      (ampTime s a b c n (s :: a :: b :: c :: encode φ).length) ∧
    RandCallsBounded w ampProgram (.init (s :: a :: b :: c :: encode φ))
      (ampTime s a b c n (s :: a :: b :: c :: encode φ).length) (ppszRounds a b n c * (2 * n)) ∧
    (∀ cfg ∈ (runRand w ampProgram (ampTime s a b c n (s :: a :: b :: c :: encode φ).length)
        (.running (.init (s :: a :: b :: c :: encode φ)))).support,
      ∃ v d, cfg = .halted v d ∧
        (v = 0 ∨ (v = 1 ∧
          φ.eval (assignmentAt d.mem ((s :: a :: b :: c :: encode φ).length + 1) n) = true))) ∧
    (evalRand w ampProgram (ampTime s a b c n (s :: a :: b :: c :: encode φ).length)
      (.init (s :: a :: b :: c :: encode φ))).map Schoening.cfgSuccess =
        repeatRoundWith (implied φ s) φ (ppszRounds a b n c) := by
  set L := (s :: a :: b :: c :: encode φ).length with hL
  have hE : (encodeClauses φ).length + 5 = L := by
    simp only [hL, List.length_cons, length_encode]
  set e := ppszExp a b n with he
  have hlen := PPZ.length_countDigits_le e c
  -- the setup
  obtain ⟨h₀, hfr₀⟩ := ampSetup_exec s a b c φ (hw.of_le (by omega))
  have hDb : (ampSetupData s a b c φ).regs bBase = L + 1 + 2 * n + 1 + 2 * s := by
    simp +decide [ampSetupData, hL]; omega
  have hDe : (ampSetupData s a b c φ).regs eReg = e := by simp +decide [ampSetupData, he]
  have hDc : (ampSetupData s a b c φ).regs cReg = c := by simp +decide [ampSetupData]
  have hDo : (ampSetupData s a b c φ).regs out = 0 := by simp +decide [ampSetupData]
  -- the counter
  obtain ⟨y₁, hy₁, hl₁, hh₁, hm₁⟩ := countSetup_spec (ampSetupData s a b c φ) hfr₀.zero_eq
    hfr₀.one_eq hDb hDe hDc (hw.of_le (by simp only [ppszCounterLen, ← he]; omega))
  have hfr₁ : RoundFrame φ 6 (L + 1) y₁.mem y₁ :=
    hfr₀.of_exec_mem_lt (by decide) hy₁ fun x hx => hm₁ x (by omega)
  have hfl : ExecWithin w (ram[ flag ← one ] : Code .standard 32) y₁ (y₁.set flag 1) 1 := by
    ram_eval [hfr₁.one_eq]
  have hpar : HoldsList (L + 1 + 2 * n) (s :: List.replicate (2 * s) 0) y₁.mem := by
    rintro ⟨i, hi⟩
    simp only [List.length_cons, List.length_replicate] at hi
    change y₁.mem (L + 1 + 2 * n + i) = (s :: List.replicate (2 * s) 0)[i]
    rw [hm₁ _ (by omega), ampSetupData_mem]
    rcases i with _ | j
    · rw [ite_eq_left (by omega)]
      rfl
    · rw [ite_eq_right (by omega), show L + 1 + 2 * n + (j + 1) = (L + 2 * n + j + 1) + 1 by omega,
        Data.init_mem_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      simp [List.getElem_replicate]
  have hb₁ : y₁.regs bBase = L + 1 + 2 * n + 1 + 2 * s :=
    (hy₁.regs_eq (i := bBase) (by decide)).trans hDb
  have ho₁ : y₁.regs out = 0 := (hy₁.regs_eq (i := out) (by decide)).trans hDo
  have hstate : AmpState φ 6 (L + 1) (s :: List.replicate (2 * s) 0) (ppszDigits a b n c)
      (y₁.set flag 1) :=
    { frame := hfr₁.set (by decide) 1
      params := hpar
      bBase_eq := by simp +decide [hb₁]; omega
      bLen_eq := by simp +decide [hl₁, ppszDigits, he]
      digits := by
        simpa [ppszDigits, ← he, show L + 1 + 2 * n + 1 + 2 * s =
          L + 1 + 2 * n + (2 * s + 1) by omega] using hh₁
      binary := PPZ.countDigits_binary _ _
      flag_eq := by simp
      out_eq := by simp +decide [ho₁] }
  -- the rounds
  have hloop := ampLoopWith_law (roundCore_isRoundCore (φ := φ) (C := 6) (Tb := L + 1) (s := s)
    (hw.of_le (by omega))) (hw.of_le (by omega)) (by omega) (ppszRounds a b n c)
    (ppszDigits a b n c) (y₁.set flag 1) hstate (ofDigits_ppszDigits a b n c)
    (hw.of_le (by simp only [List.length_cons, List.length_replicate, ppszDigits, ← he,
      ppszCounterLen] at hlen ⊢; omega))
  have hall := ExecRandLaw.seq_det h₀ (ExecRandLaw.seq_det hy₁ (ExecRandLaw.seq_det hfl hloop))
  have hcount := List.count_le_length (a := 0) (l := ppszDigits a b n c)
  obtain ⟨hhalt, hcalls, hpost, hlaw⟩ := hall.program out (T' := ampTime s a b c n L)
    (by
      have h1 := Nat.mul_le_mul_left n (Nat.add_le_add_right
        (impliedTime_mono s (show (encodeClauses φ).length ≤ L by omega)) 25)
      have h2 := Nat.mul_le_mul_left (ppszRounds a b n c)
        (show n * (impliedTime s (encodeClauses φ).length + 25) + 6 +
          12 * (encodeClauses φ).length + 35 ≤ n * (impliedTime s L + 25) + 12 * L + 41 by omega)
      simp only [ampTime, countSetupTime, ppszCounterLen, ppszDigits, ← he] at hlen hcount ⊢
      omega)
    Schoening.cfgSuccess fun _ _ => rfl
  refine ⟨hhalt, hcalls, fun cfg hcfg => ?_, hlaw⟩
  obtain ⟨d, rfl, -, hd⟩ := hpost cfg hcfg
  exact ⟨_, d, rfl, hd⟩

/-- **The PPSZ bound for one round** [Hertli][Hertli2011]: on a satisfiable formula with clauses
of at most `k ≥ 3` literals, one round of PPSZ with `s ≥ ∑ i < h, (k - 1) ^ i` succeeds with
probability at least `2 ^ (-(1 - qbar k h) n)`
(`Cslib.Complexity.PPSZ.round_success_of_satisfiable`). -/
theorem roundSuccessProb_ge {k h s : ℕ} (hk : 3 ≤ k) {φ : CNF (Fin n)} (hsat : φ.Satisfiable)
    (hlen : ∀ c ∈ φ, c.length ≤ k) (hs : ∑ i ∈ Finset.range h, (k - 1) ^ i ≤ s) :
    (2 : ℝ) ^ (-((1 - qbar k h) * n)) ≤ roundSuccessProbWith (implied φ s) φ :=
  (round_success_of_satisfiable hk hsat hlen hs).trans (PPZ.sum_le_roundSuccessProbWith _ φ)

/-- With `R = ppszRounds a b n c` rounds, `R 2 ^ (-(a / b) n)` is at least `c`. -/
theorem le_ppszRounds_mul {a b : ℕ} (hb : 0 < b) (n c : ℕ) :
    (c : ℝ) ≤ ppszRounds a b n c * (2 : ℝ) ^ (-((a : ℝ) / b * n)) := by
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ppszExp a b n * (2 : ℝ) ^ (-((a : ℝ) / b * n)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add two_pos]
    exact Real.one_le_rpow one_le_two (by linarith [le_ppszExp (a := a) hb n])
  calc (c : ℝ) ≤ c * ((2 : ℝ) ^ ppszExp a b n * (2 : ℝ) ^ (-((a : ℝ) / b * n))) :=
        le_mul_of_one_le_right (Nat.cast_nonneg c) h2
    _ = (ppszRounds a b n c : ℝ) * (2 : ℝ) ^ (-((a : ℝ) / b * n)) := by
        simp only [ppszRounds]; push_cast; ring

/-- **Amplification from a bound on one round**: if one round of PPSZ with the bound `s` succeeds
with probability at least `2 ^ (-(a / b) n)`, the program fails with probability at most
`e ^ (-c)`. -/
theorem ampProgram_failure_le_exp_of_le {s a b c : ℕ} (hb : 0 < b) {φ : CNF (Fin n)}
    (hq : (2 : ℝ) ^ (-((a : ℝ) / b * n)) ≤ roundSuccessProbWith (implied φ s) φ) {w : ℕ}
    (hw : Fits w ((s :: a :: b :: c :: encode φ).length + 2 * n + 2 * s + a * n + b + 2 * c +
      ppszCounterLen a b n c + 3)) :
    ((evalRand w ampProgram (ampTime s a b c n (s :: a :: b :: c :: encode φ).length)
      (.init (s :: a :: b :: c :: encode φ))).map Schoening.cfgSuccess false).toReal ≤
      Real.exp (-c) := by
  rw [(ampProgram_spec s a b c φ hw).2.2.2]
  exact PPZ.repeatRoundWith_false_le_exp hq (le_ppszRounds_mul hb n c)

/-- **The PPSZ algorithm succeeds with high probability**
[Paturi, Pudlák, Saks, Zane][PaturiPudlakSaksZane2005], [Hertli][Hertli2011]. On a satisfiable
formula whose clauses have at most `k ≥ 3` literals, with `s ≥ ∑ i < h, (k - 1) ^ i` and
`1 - qbar k h ≤ a / b`, the program outputs `1` except with probability at most `e ^ (-c)`. -/
theorem ampProgram_failure_le_exp {k h s a b c : ℕ} (hk : 3 ≤ k) (hb : 0 < b)
    {φ : CNF (Fin n)} (hφ : φ.Satisfiable) (hlen : ∀ cl ∈ φ, cl.length ≤ k)
    (hs : ∑ i ∈ Finset.range h, (k - 1) ^ i ≤ s) (hab : 1 - qbar k h ≤ (a : ℝ) / b) {w : ℕ}
    (hw : Fits w ((s :: a :: b :: c :: encode φ).length + 2 * n + 2 * s + a * n + b + 2 * c +
      ppszCounterLen a b n c + 3)) :
    ((evalRand w ampProgram (ampTime s a b c n (s :: a :: b :: c :: encode φ).length)
      (.init (s :: a :: b :: c :: encode φ))).map Schoening.cfgSuccess false).toReal ≤
      Real.exp (-c) :=
  ampProgram_failure_le_exp_of_le hb (le_trans (Real.rpow_le_rpow_of_exponent_le one_le_two
    (neg_le_neg (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n))))
    (roundSuccessProb_ge hk hφ hlen hs)) hw

/-- **PPSZ for k-SAT on the randomized word RAM, `ε`-form**
[Paturi, Pudlák, Saks, Zane][PaturiPudlakSaksZane2005], [Hertli][Hertli2011]. Let `k ≥ 3` and
`ε > 0`. There is a bound `s` such that for every rational `a / b ≥ 1 - μ_k / (k - 1) + ε`, the
program with the bound `s` fails on any satisfiable formula whose clauses have at most `k` literals
with probability at most `e ^ (-c)`, in time `O((n + L) ^ (2 s + 1) 2 ^ ((a / b) n) (c + 1))`
(`ampTime_le`). This uses `Cslib.Complexity.PPSZ.round_success_limit`, the `ε`-form of the bound
`2 ^ (-(1 - μ_k / (k - 1)) n - o(n))` of the sources. -/
theorem ampProgram_failure_le_exp_limit {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℕ, ∀ {a b c : ℕ}, 0 < b → 1 - mu k / ((k : ℝ) - 1) + ε ≤ (a : ℝ) / b →
      ∀ {n : ℕ} {φ : CNF (Fin n)}, φ.Satisfiable → (∀ cl ∈ φ, cl.length ≤ k) → ∀ {w : ℕ},
        Fits w ((s :: a :: b :: c :: encode φ).length + 2 * n + 2 * s + a * n + b + 2 * c +
          ppszCounterLen a b n c + 3) →
        ((evalRand w ampProgram (ampTime s a b c n (s :: a :: b :: c :: encode φ).length)
          (.init (s :: a :: b :: c :: encode φ))).map Schoening.cfgSuccess false).toReal ≤
          Real.exp (-c) := by
  obtain ⟨s, hs⟩ := round_success_limit hk ε hε
  refine ⟨s, fun hb hab n φ hφ hlen w hw => ampProgram_failure_le_exp_of_le hb ?_ hw⟩
  exact le_trans (Real.rpow_le_rpow_of_exponent_le one_le_two
    (neg_le_neg (mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n))))
    ((hs n φ hφ hlen).trans (PPZ.sum_le_roundSuccessProbWith _ φ))

/-- **PPSZ for 3-SAT on the randomized word RAM.** With `s = 3` and the bound `39 / 70` on the
exponent, which is `1 - qbar 3 2`, the program fails on a satisfiable 3-CNF with probability at
most `e ^ (-c)`. It runs `2 ^ ⌈39 n / 70⌉ c` rounds, about `1.471 ^ n c`. -/
theorem ampProgram_failure_le_exp_three {c : ℕ} {φ : CNF (Fin n)} (hφ : φ.Satisfiable)
    (hlen : ∀ cl ∈ φ, cl.length ≤ 3) {w : ℕ}
    (hw : Fits w ((3 :: 39 :: 70 :: c :: encode φ).length + 2 * n + 2 * 3 + 39 * n + 70 + 2 * c +
      ppszCounterLen 39 70 n c + 3)) :
    ((evalRand w ampProgram (ampTime 3 39 70 c n (3 :: 39 :: 70 :: c :: encode φ).length)
      (.init (3 :: 39 :: 70 :: c :: encode φ))).map Schoening.cfgSuccess false).toReal ≤
      Real.exp (-c) :=
  ampProgram_failure_le_exp (k := 3) (h := 2) le_rfl (by norm_num) hφ hlen
    (by simp [Finset.sum_range_succ]) (by rw [qbar_three_two]; norm_num) hw

/-- **The running time** of the PPSZ algorithm is
`O((s + 1)² (n + L) ^ (2 s + 1) 2 ^ ((a / b) n) (c + 1))`: explicitly, at most
`600 (s + 1)² (n + L + 1) ^ (2 s + 1) 2 ^ ((a / b) n) (c + 1)` instructions. -/
theorem ampTime_le {s a b : ℕ} (hb : 0 < b) (c n L : ℕ) :
    (ampTime s a b c n L : ℝ) ≤
      600 * ((s + 1) ^ 2 : ℕ) * ((n + L + 1 : ℕ) : ℝ) ^ (2 * s + 1) *
        (2 : ℝ) ^ ((a : ℝ) / b * n) * (c + 1) := by
  set X := (2 : ℝ) ^ ((a : ℝ) / b * n) with hX
  set e := ppszExp a b n with he
  obtain ⟨N, hN⟩ : ∃ N, n + L + 1 = N := ⟨_, rfl⟩
  rw [hN]
  have hX1 : 1 ≤ X := Real.one_le_rpow one_le_two (by positivity)
  -- the number of rounds
  have h2e : (2 : ℝ) ^ e ≤ 2 * X := by
    rw [← Real.rpow_natCast, hX, show 2 * (2 : ℝ) ^ ((a : ℝ) / b * n) =
      (2 : ℝ) ^ ((a : ℝ) / b * n + 1) by rw [Real.rpow_add two_pos, Real.rpow_one]; ring]
    exact Real.rpow_le_rpow_of_exponent_le one_le_two (ppszExp_le_add_one hb n)
  -- one round
  set K := (s + 1) ^ 2 * N ^ (2 * s + 1) with hK
  have hP : n * (impliedTime s L + 25) + 12 * L + 41 ≤ 181 * K := by
    have hI := impliedTime_le s L
    have hn : n ≤ N := by omega
    have hL1 : (L + 1) ^ (2 * s) ≤ N ^ (2 * s) := Nat.pow_le_pow_left (by omega) _
    have hNs : N ≤ N ^ (2 * s + 1) := Nat.le_self_pow (by omega) N
    have hs1 : 1 ≤ (s + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h1 : n * (140 * (s + 1) ^ 2 * (L + 1) ^ (2 * s)) ≤ 140 * K := by
      calc n * (140 * (s + 1) ^ 2 * (L + 1) ^ (2 * s))
          ≤ N * (140 * (s + 1) ^ 2 * N ^ (2 * s)) := by gcongr
        _ = 140 * K := by rw [hK, pow_succ]; ring
    have h2 : 41 * N ≤ 41 * K := by
      rw [hK]; nlinarith [Nat.mul_le_mul hs1 hNs]
    have h3 : n * (impliedTime s L + 25) ≤ n * (140 * (s + 1) ^ 2 * (L + 1) ^ (2 * s)) + 25 * n :=
      by rw [Nat.mul_add, Nat.mul_comm n 25]; gcongr
    omega
  -- the setup
  have hS : 5 * e + 19 * ppszCounterLen a b n c + 70 ≤ 89 * 2 ^ e * (c + 1) := by
    have hd : (Nat.digits 2 c).length ≤ c :=
      (Nat.digits_length_le_iff (by decide) _).mpr Nat.lt_two_pow_self
    have he2 : e + 1 ≤ 2 ^ e := Nat.lt_two_pow_self
    simp only [ppszCounterLen, ← he]
    nlinarith [Nat.mul_le_mul_right (c + 1) he2]
  have hK1 : (1 : ℝ) ≤ K := by
    have : 0 < K := by rw [hK]; exact Nat.mul_pos (by positivity) (pow_pos (by omega) _)
    exact_mod_cast this
  have hexp : (ampTime s a b c n L : ℝ) =
      (2 : ℝ) ^ e * c * ((n * (impliedTime s L + 25) + 12 * L + 41 : ℕ) : ℝ) +
        ((5 * e + 19 * ppszCounterLen a b n c + 70 : ℕ) : ℝ) := by
    simp only [ampTime, ppszRounds, ← he]; push_cast; ring
  have hPr : ((n * (impliedTime s L + 25) + 12 * L + 41 : ℕ) : ℝ) ≤ 181 * (K : ℝ) := by
    exact_mod_cast hP
  have hSr : ((5 * e + 19 * ppszCounterLen a b n c + 70 : ℕ) : ℝ) ≤
      89 * (2 : ℝ) ^ e * (c + 1) := by
    exact_mod_cast hS
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hKc : ((s + 1) ^ 2 : ℕ) * ((N : ℕ) : ℝ) ^ (2 * s + 1) = (K : ℝ) := by
    rw [hK]; push_cast; ring
  rw [hexp, mul_assoc 600, hKc]
  have h2e0 : (0 : ℝ) ≤ (2 : ℝ) ^ e := by positivity
  calc (2 : ℝ) ^ e * c * ((n * (impliedTime s L + 25) + 12 * L + 41 : ℕ) : ℝ) +
        ((5 * e + 19 * ppszCounterLen a b n c + 70 : ℕ) : ℝ)
      ≤ (2 * X) * c * (181 * K) + 89 * (2 * X) * (c + 1) :=
        add_le_add (by gcongr) (hSr.trans (by gcongr))
    _ ≤ 600 * K * X * (c + 1) := by
        nlinarith [mul_le_mul_of_nonneg_left hK1 (mul_nonneg (by linarith : (0 : ℝ) ≤ X)
          (by linarith : (0 : ℝ) ≤ c + 1)), mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ K)
          (by linarith : (0 : ℝ) ≤ X)) hc0]

end Cslib.Algorithms.WordRAM.PPSZ
