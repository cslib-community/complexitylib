/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.PPSZ.Implied
public import Complexity.Algorithms.WordRAM.PPZ.Round

/-!
# One round of PPSZ on the randomized word RAM

`Cslib.Algorithms.WordRAM.PPSZ.roundProgram` is one round of the PPSZ algorithm
[Paturi, Pudlák, Saks, Zane][PaturiPudlakSaksZane2005] with w-implication
[Hertli][Hertli2011], as a program of the randomized word RAM (`Cslib.WordRAM.runRand`). On the
input `s :: encode φ`, the bound `s` on the number of clauses of an implication followed by the
number `n` of variables and the clauses of `φ : CNF (Fin n)`, it

1. stores the empty partial assignment, the array `P = [0, 1, …, n - 1]` and the bound `s` just
   after the input; the `2 s` words after `s` are the scratch memory of the oracle and start out
   zero;
2. for `i = 0, …, n - 1`: draws `j` uniformly from `[i, n)`, swaps `P[i]` and `P[j]`, and sets the
   variable `x = P[i]` to its w-implied value (`Cslib.Complexity.PPSZ.implied φ s`, computed by
   `Cslib.Algorithms.WordRAM.PPSZ.impliedCode`), or to a uniform bit if it has none;
3. halts with output `1` if the assignment it built satisfies `φ`, and `0` otherwise.

Steps 2 and 3 are the round of PPZ (`Cslib.Algorithms.WordRAM.PPZ.roundCoreWith`,
`Cslib.Algorithms.WordRAM.PPZ.roundCheck`) with `impliedCode` as its oracle code
(`Cslib.Algorithms.WordRAM.PPSZ.impliedCode_isOracleCode`). Since
`Cslib.Complexity.PPSZ.round φ s` is by definition the round of PPZ with the oracle
`implied φ s`, the law of the loop is a round of PPSZ.

`Cslib.Algorithms.WordRAM.PPSZ.roundProgram_spec` proves that the program halts on every path
within `roundTime s n L = n (impliedTime s L + 25) + 12 L + 23` instructions, where `L` is the input
length, makes at most `2 n` `rand` calls, reports correctly whether the assignment it leaves
satisfies `φ`, and that the law of that assignment is exactly `Cslib.Complexity.PPSZ.round φ s`.
The PPSZ success bounds, such as `Cslib.Complexity.PPSZ.round_success_of_satisfiable`, therefore
apply to the program. By `Cslib.Algorithms.WordRAM.PPSZ.impliedTime_le`, the time is
`O(n (s + 1)² (L + 1) ^ (2 s) + L)`. Time is the instruction count of the word RAM with unit-cost
`rand` (`Cslib.WordRAM.stepRand`).

## Main definitions

* `Cslib.Algorithms.WordRAM.PPSZ.roundSetup`, `Cslib.Algorithms.WordRAM.PPSZ.roundCode`,
  `Cslib.Algorithms.WordRAM.PPSZ.roundProgram`: a round on the input `s :: encode φ`, structured
  and compiled.
* `Cslib.Algorithms.WordRAM.PPSZ.roundTime`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.PPSZ.impliedTime_mono`: the oracle's bound is monotone in the length
  of the clauses.
* `Cslib.Algorithms.WordRAM.PPSZ.impliedCode_isOracleCode`: `impliedCode` is an oracle code for
  `implied φ s` on rounds whose memory after the order array holds `s` and `2 s` zero words.
* `Cslib.Algorithms.WordRAM.PPSZ.roundCore_law`: the round body has the law of
  `Cslib.Complexity.PPSZ.round φ s`.
* `Cslib.Algorithms.WordRAM.PPSZ.roundProgram_spec`: halting, time and `rand` bounds, a correct
  output, and the exact law of a round for the compiled program.

## References

* [R. Paturi, P. Pudlák, M. Saks, F. Zane, *An improved exponential-time algorithm for
  k-SAT*][PaturiPudlakSaksZane2005]
* [T. Hertli, *3-SAT faster and simpler*][Hertli2011]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PPSZ

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.PPSZ
open Cslib.Algorithms.WordRAM.Schoening (encodeClauses encode assignmentAt length_encode)
open Cslib.Algorithms.WordRAM.PPZ (RoundFrame IsOracleCode roundCoreWith roundCheck roundCheck_exec
  roundCoreWith_law cfgPartial)
open Cslib.Algorithms.WordRAM.PPZ.Reg

variable {n : ℕ}

/-! ### The oracle code -/

/-- **The oracle's bound is monotone** in the length of the clauses. -/
theorem impliedTime_mono (s : ℕ) {E E' : ℕ} (h : E ≤ E') : impliedTime s E ≤ impliedTime s E' := by
  have hp : E ^ s ≤ E' ^ s := Nat.pow_le_pow_left h s
  simp only [impliedTime, impScanTime, outerTime, outerIter, innerTime]
  gcongr

/-- **w-implication is an oracle code** for `Cslib.Complexity.PPSZ.implied φ s`, within
`impliedTime s E` instructions, on rounds whose memory after the order array, from `Tb + 2 n`,
holds `s` followed by `2 s` zero words (`Cslib.Algorithms.WordRAM.PPSZ.impliedCode_spec`). -/
theorem impliedCode_isOracleCode {φ : CNF (Fin n)} {C Tb s w : ℕ} {M : ℕ → ℕ}
    (hs : M (Tb + 2 * n) = s) (hzero : ∀ i < 2 * s, M (Tb + 2 * n + 1 + i) = 0)
    (hw : Fits w (Tb + 2 * n + 2 * s + 2)) :
    IsOracleCode w φ C Tb M (implied φ s) impliedCode (impliedTime s (encodeClauses φ).length) where
  preserves := by decide
  preserves_x := by decide
  preserves_i := by decide
  preserves_j := by decide
  exec τ v y hf hv hτ := by
    obtain ⟨z, hz, hzm, hzr⟩ := impliedCode_spec φ τ v s y hf.zero_eq hf.one_eq hf.two_eq hv
      hf.cBeg_eq (by rw [hf.cEnd_eq, hf.span]) hf.tBase_eq hf.nReg_eq hf.clauses hτ
      hf.span.le (by rw [hf.rest _ le_rfl, hs])
      (fun i hi => by rw [hf.rest _ (by omega), hzero i hi]) hw
    exact ⟨z, hz, hzm, hzr⟩

/-- **The body of a round of PPSZ** (`Cslib.Algorithms.WordRAM.PPZ.roundCoreWith impliedCode`) has
the law of `Cslib.Complexity.PPSZ.round φ s`, keeps the frame, and leaves every variable set. -/
theorem roundCore_law {φ : CNF (Fin n)} {C Tb s w : ℕ} {M : ℕ → ℕ}
    (hs : M (Tb + 2 * n) = s) (hzero : ∀ i < 2 * s, M (Tb + 2 * n + 1 + i) = 0)
    (hw : Fits w (Tb + 2 * n + 2 * s + 2)) {x : Data 32} (hx : RoundFrame φ C Tb M x) :
    ExecRandLaw w (roundCoreWith impliedCode) x
      (fun y => RoundFrame φ C Tb M y ∧ ∀ v < n, y.mem (Tb + v) ≤ 1)
      (n * (impliedTime s (encodeClauses φ).length + 25) + 6) (2 * n)
      (fun y => PPZ.partialAssignmentAt y.mem Tb n) (round φ s) :=
  roundCoreWith_law (impliedCode_isOracleCode hs hzero hw) (hw.of_le (by omega)) hx

/-! ### The program -/

/-- Set up the registers of a round on the input `s :: encode φ`: the clauses start at address
`3`, the partial assignment is stored just after the input, the order array just after it, and
the bound `s` is copied to the word after the order array. -/
def roundSetup : Code .standard 32 := ram[
  one ← #1; two ← #2; val ← *zero; tBase ← val + one; cEnd ← tBase; val ← one + one;
  nReg ← *val; cBeg ← val + one; pBase ← tBase + nReg; addr ← pBase + nReg; val ← *one;
  *addr ← val ]

/-- **One round of PPSZ** on the input `s :: encode φ`, as a structured program. -/
def roundCode : Code .standard 32 := ram[ ⟪roundSetup⟫; ⟪roundCoreWith impliedCode⟫; ⟪roundCheck⟫ ]

/-- **One round of PPSZ** on the input `s :: encode φ`, halting with `out`. -/
def roundProgram : Program .standard 32 := roundCode.program out

/-- The instruction bound of a round with the bound `s`, on `n` variables and an input of length
`L`. -/
def roundTime (s n L : ℕ) : ℕ := n * (impliedTime s L + 25) + 12 * L + 23

/-- The data after the setup of a round on the input `s :: encode φ`. -/
def roundSetupData (s : ℕ) (φ : CNF (Fin n)) : Data 32 :=
  ((((((((((((Data.init (s :: encode φ)).set one 1).set two 2).set val
    (s :: encode φ).length).set tBase ((s :: encode φ).length + 1)).set cEnd
    ((s :: encode φ).length + 1)).set val 2).set nReg n).set cBeg 3).set pBase
    ((s :: encode φ).length + 1 + n)).set addr ((s :: encode φ).length + 1 + n + n)).set val
    s).write ((s :: encode φ).length + 1 + n + n) s

/-- The memory after the setup: the input, then `s` at `L + 1 + 2 n`, and zero after it. -/
theorem roundSetupData_mem (s : ℕ) (φ : CNF (Fin n)) (a : ℕ) :
    (roundSetupData s φ).mem a =
      if a = (s :: encode φ).length + 1 + n + n then s
      else (Data.init (s :: encode φ) : Data 32).mem a := by
  simp only [roundSetupData, Data.write_mem, Data.set_mem, Function.update_apply]

/-- The setup establishes the frame of a round on the input `s :: encode φ`, with `s` stored after
the order array and zero memory after it. -/
theorem roundSetup_exec (s : ℕ) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((s :: encode φ).length + 2 * n + 1)) :
    ExecWithin w roundSetup (Data.init (s :: encode φ)) (roundSetupData s φ) 12 ∧
      RoundFrame φ 3 ((s :: encode φ).length + 1) (roundSetupData s φ).mem
        (roundSetupData s φ) := by
  have hf1 : Fits w 1 := hw.of_le (by omega)
  have hf2 : Fits w 2 := hw.of_le (by simp [encode]; omega)
  have hf3 : Fits w 3 := hw.of_le (by simp [encode]; omega)
  have hf4 : Fits w ((s :: encode φ).length + 1) := hw.of_le (by omega)
  have hf5 : Fits w ((s :: encode φ).length + 1 + n) := hw.of_le (by omega)
  have hf6 : Fits w ((s :: encode φ).length + 1 + n + n) := hw.of_le (by omega)
  have hm0 : (Data.init (s :: encode φ) : Data 32).mem 0 = (s :: encode φ).length := rfl
  have hm1 : (Data.init (s :: encode φ) : Data 32).mem 1 = s := rfl
  have hm2 : (Data.init (s :: encode φ) : Data 32).mem 2 = n := rfl
  refine ⟨?run, ?frame⟩
  case run =>
    ram_eval [roundSetup, roundSetupData, Data.init_regs, hm0, hm1, hm2, hf1, hf2, hf3, hf4, hf5,
      hf6]
  case frame =>
    refine ⟨by simp +decide [roundSetupData], by simp +decide [roundSetupData],
      by simp +decide [roundSetupData], by simp +decide [roundSetupData],
      by simp +decide [roundSetupData], by simp +decide [roundSetupData],
      by simp +decide [roundSetupData], by simp +decide [roundSetupData], ?_, ?_, fun _ _ => rfl⟩
    · intro i
      have hi : i.val < (encodeClauses φ).length := i.isLt
      change (roundSetupData s φ).mem (3 + i.val) = (encodeClauses φ)[i.val]
      rw [roundSetupData_mem, ite_eq_right_iff.mpr (fun h => by simp [length_encode] at h; omega),
        show 3 + i.val = (2 + i.val) + 1 by omega, Data.init_mem_succ]
      simp [encode, show 2 + i.val = (i.val + 1) + 1 by omega]
    · simp [length_encode]; omega

/-- **One round of PPSZ on the randomized word RAM.** On the input `s :: encode φ` of length `L`,
at any word size `w` with `L + 2 n + 2 s + 3 < 2 ^ w`, the program

* halts on every path within `roundTime s n L = n (impliedTime s L + 25) + 12 L + 23`
  instructions;
* makes at most `2 n` `rand` calls;
* outputs `1` exactly when the assignment it leaves at address `L + 1` satisfies `φ`, and that
  assignment is total: every word is `0` or `1`;
* leaves a partial assignment whose law is exactly `Cslib.Complexity.PPSZ.round φ s`. -/
theorem roundProgram_spec (s : ℕ) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((s :: encode φ).length + 2 * n + 2 * s + 3)) :
    RandHaltsWithin w roundProgram (.init (s :: encode φ))
      (roundTime s n (s :: encode φ).length) ∧
    RandCallsBounded w roundProgram (.init (s :: encode φ))
      (roundTime s n (s :: encode φ).length) (2 * n) ∧
    (∀ cfg ∈ (runRand w roundProgram (roundTime s n (s :: encode φ).length)
        (.running (.init (s :: encode φ)))).support,
      ∃ d : Data 32, cfg = .halted
        (if φ.eval (assignmentAt d.mem ((s :: encode φ).length + 1) n) then 1 else 0) d ∧
        ∀ v < n, d.mem ((s :: encode φ).length + 1 + v) ≤ 1) ∧
    (evalRand w roundProgram (roundTime s n (s :: encode φ).length)
        (.init (s :: encode φ))).map
      (cfgPartial ((s :: encode φ).length + 1) n) = round φ s := by
  set Tb := (s :: encode φ).length + 1
  obtain ⟨hy, hfr⟩ := roundSetup_exec s φ (hw.of_le (by omega))
  have hT : 1 ≤ Tb := by omega
  have hw' : Fits w (Tb + 2 * n) := hw.of_le (by omega)
  have hs : (roundSetupData s φ).mem (Tb + 2 * n) = s := by
    rw [roundSetupData_mem, ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
  have hzero : ∀ i < 2 * s, (roundSetupData s φ).mem (Tb + 2 * n + 1 + i) = 0 := fun i _ => by
    rw [roundSetupData_mem, ite_eq_right_iff.mpr (fun h => by omega), show Tb + 2 * n + 1 + i =
      ((s :: encode φ).length + 2 * n + 1 + i) + 1 by omega, Data.init_mem_succ,
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  have hcore := ExecRandLaw.seq_det hy (ExecRandLaw.seq_det_right
    (roundCore_law hs hzero (hw.of_le (by omega)) hfr)
    (Q := fun y => (RoundFrame φ 3 Tb (roundSetupData s φ).mem y ∧ ∀ v < n, y.mem (Tb + v) ≤ 1) ∧
      y.regs out = if φ.eval (assignmentAt y.mem Tb n) then 1 else 0)
    fun y ⟨hfy, hby⟩ => by
      obtain ⟨z, hz, hzm, hfz, hzo⟩ := roundCheck_exec hw' hT hfy hby
      exact ⟨z, hz, ⟨⟨hfz, by rw [hzm]; exact hby⟩, by rw [hzm]; exact hzo⟩, by simp [hzm]⟩)
  obtain ⟨hhalt, hcalls, hpost, hlaw⟩ := hcore.program out
    (T' := roundTime s n (s :: encode φ).length)
    (by
      have hL : (s :: encode φ).length = (encodeClauses φ).length + 2 := by
        simp [length_encode]
      have := Nat.mul_le_mul_left n (Nat.add_le_add_right
        (impliedTime_mono s (show (encodeClauses φ).length ≤ (s :: encode φ).length by omega)) 25)
      simp only [roundTime]
      omega)
    (cfgPartial Tb n) fun _ _ => rfl
  refine ⟨hhalt, hcalls, fun cfg hcfg => ?_, hlaw⟩
  obtain ⟨d, rfl, ⟨-, hb⟩, hd⟩ := hpost cfg hcfg
  exact ⟨d, by rw [hd], hb⟩

end Cslib.Algorithms.WordRAM.PPSZ
