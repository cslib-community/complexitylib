/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Schoening.Trial
public import Mathlib.Analysis.Complex.Exponential
import Complexity.Probability.PMF.Event

/-!
# Schöning's algorithm on the randomized word RAM

`Cslib.Algorithms.WordRAM.Schoening.ampProgram` runs up to `R` independent trials of Schöning's
k-SAT algorithm [Schöning][Schoening1999] on the input `R :: encode φ`, stopping at the first
trial that finds a satisfying assignment. It halts with output `1`, leaving a satisfying assignment
in memory, or with output `0` when every trial failed.

`Cslib.Algorithms.WordRAM.Schoening.ampProgram_spec` proves that the program halts on every path
within `ampTime R n L = R (36 n L + 66 n + 12 L + 18) + 10` instructions, where `L` is the input
length, and makes at most `4 n R` `rand` calls; an output `1` always comes with a satisfying
assignment, so the program never errs on unsatisfiable formulas; and the output is `1` with
exactly the law of `R` independent trials (`Cslib.Algorithms.WordRAM.Schoening.repeatTrial`), so it
is `0` with probability exactly `(1 - p) ^ R`, where `p` is the success probability of one trial
(`Cslib.Algorithms.WordRAM.Schoening.ampProgram_failure_eq`).

Combined with Schöning's bound for one trial
(`Cslib.Complexity.Schoening.trial_success_of_length_le`), the trial count
`R = schoeningTrials k n c = ⌈(3 n + 1) (2 (k - 1) / k) ^ n (k / (k - 1)) ^ (k - 3)⌉ c` makes
the program fail on a satisfiable formula with clauses of at most `k ≥ 3` literals with
probability at most `e ^ (-c)` (`Cslib.Algorithms.WordRAM.Schoening.ampProgram_failure_le_exp`).
For `k = 3` this is `⌈(3 n + 1) (4 / 3) ^ n⌉ c` trials, and the time bound is
`O(n ^ 2 L (4 / 3) ^ n c)`: Schöning's `O*((2 - 2 / k) ^ n)` running time, with the polynomial
factor explicit.

The trial count is part of the input and must fit in a word, so the statements need a word size
`w` with `R < 2 ^ w`, that is, about `0.415 n` bits for `k = 3`. Computing `R` on the machine and
counting trials with several words, which would remove this assumption, is not formalized.

## Main definitions

* `Cslib.Algorithms.WordRAM.Schoening.repeatTrial`: the law of the output of up to `R`
  independent trials.
* `Cslib.Algorithms.WordRAM.Schoening.ampCode`, `Cslib.Algorithms.WordRAM.Schoening.ampProgram`:
  the amplified algorithm, structured and compiled.
* `Cslib.Algorithms.WordRAM.Schoening.ampTime`: its instruction bound.
* `Cslib.Algorithms.WordRAM.Schoening.cfgSuccess`: whether a halting run output `1`.
* `Cslib.Algorithms.WordRAM.Schoening.schoeningTrials`: the trial count for confidence `c`.

## Main results

* `Cslib.Algorithms.WordRAM.Schoening.repeatTrial_false_toReal`: `R` trials all fail with
  probability `(1 - p) ^ R`.
* `Cslib.Algorithms.WordRAM.Schoening.ampProgram_spec`: halting, time and `rand` bounds, no false
  positives, and the exact law of the output.
* `Cslib.Algorithms.WordRAM.Schoening.ampProgram_failure_eq`: the program fails with probability
  `(1 - p) ^ R`.
* `Cslib.Algorithms.WordRAM.Schoening.ampProgram_failure_le_exp`: with `schoeningTrials k n c`
  trials it fails on a satisfiable k-CNF with probability at most `e ^ (-c)`.

## References

* [U. Schöning, *A probabilistic algorithm for k-SAT and constraint satisfaction
  problems*][Schoening1999]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Schoening

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.Schoening
open Reg

variable {n : ℕ}

/-! ### Repeated trials -/

/-- The output of up to `R` independent trials of Schöning's algorithm, stopping at the first
success: `true` if some trial found a satisfying assignment. -/
noncomputable def repeatTrial (φ : CNF (Fin n)) : ℕ → PMF Bool
  | 0 => PMF.pure false
  | R + 1 => (trial φ).bind fun σ => if φ.eval σ then PMF.pure true else repeatTrial φ R

/-- **All `R` trials fail** with probability `(1 - p) ^ R`, where `p` is the success probability of
one trial. -/
theorem repeatTrial_false_toReal (φ : CNF (Fin n)) (R : ℕ) :
    (repeatTrial φ R false).toReal = (1 - succeedProb φ (trial φ)) ^ R := by
  induction R with
  | zero => simp [repeatTrial]
  | succ R ih =>
    have h := Probability.PMF.toOuterMeasure_bind_toReal (trial φ)
      (fun σ => if φ.eval σ then PMF.pure true else repeatTrial φ R) {false}
    simp only [PMF.toOuterMeasure_apply_singleton] at h
    have hsum : ∑ σ, ((trial φ) σ).toReal * (if φ.eval σ = true then 0 else 1) =
        1 - succeedProb φ (trial φ) := by
      have hfail := Probability.PMF.toOuterMeasure_toReal_add_compl (trial φ)
        {σ | φ.eval σ = true}
      have hcongr : ∑ σ, ((trial φ) σ).toReal * (if φ.eval σ = true then 0 else 1) =
          ((trial φ).toOuterMeasure {σ | φ.eval σ = true}ᶜ).toReal := by
        rw [Probability.PMF.toOuterMeasure_apply_toReal]
        exact Finset.sum_congr rfl fun σ _ => by by_cases hσ : φ.eval σ = true <;> simp [hσ]
      rw [hcongr, succeedProb]
      linarith
    rw [repeatTrial, h, pow_succ]
    calc ∑ σ, ((trial φ) σ).toReal *
          ((if φ.eval σ = true then PMF.pure true else repeatTrial φ R) false).toReal
        = ∑ σ, ((trial φ) σ).toReal * (if φ.eval σ = true then 0 else 1) *
            (1 - succeedProb φ (trial φ)) ^ R := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          by_cases hσ : φ.eval σ = true
          · simp only [hσ, ↓reduceIte, PMF.pure_apply, Bool.false_eq_true, ENNReal.toReal_zero,
              mul_zero, zero_mul]
          · simp only [hσ, Bool.false_eq_true, ↓reduceIte, ih, mul_one]
      _ = (1 - succeedProb φ (trial φ)) ^ R * (1 - succeedProb φ (trial φ)) := by
          rw [← Finset.sum_mul, hsum, mul_comm]

/-- `(1 - p) ^ R ≤ e ^ (-c)` once `c ≤ R p`. -/
theorem one_sub_pow_le_exp {p c : ℝ} {R : ℕ} (hp1 : p ≤ 1) (hc : c ≤ R * p) :
    (1 - p) ^ R ≤ Real.exp (-c) := by
  calc (1 - p) ^ R ≤ Real.exp (-p) ^ R :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-p)]) R
    _ = Real.exp (-(R * p)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-c) := Real.exp_le_exp.mpr (by linarith)

/-! ### The program -/

/-- Set up the registers on the input `R :: encode φ`: the clauses start at address `3`, the
assignment is stored just after the input, and `rem = R`. -/
def ampSetup : Code .standard 24 := ram[
  one ← #1; val ← *zero; aBase ← val + one; rem ← *one; val ← one + one; nReg ← *val;
  cBeg ← val + one ]

/-- One trial, then stop after a success or count the trial. -/
def ampBody : Code .standard 24 := ram[
  ⟪trialCore⟫; if out = one then [ rem ← zero ] else [ rem ← rem - one ] ]

/-- Run trials while `rem > 0`. -/
def ampLoop : Code .standard 24 := .loop (.lt zero rem) ampBody

/-- **Schöning's algorithm** on the input `R :: encode φ`: up to `R` trials. -/
def ampCode : Code .standard 24 := ram[ ⟪ampSetup⟫; ⟪ampLoop⟫ ]

/-- **Schöning's algorithm** on the input `R :: encode φ`, halting with `out`. -/
def ampProgram : Program .standard 24 := ampCode.program out

/-- The instruction bound of `R` trials on `n` variables and an input of length `L`. -/
def ampTime (R n L : ℕ) : ℕ := R * (36 * n * L + 66 * n + 12 * L + 18) + 10

/-- Whether a halting run output `1`. -/
def cfgSuccess {r : ℕ} : RandCfg r → Bool
  | .halted v _ => decide (v = 1)
  | _ => false

/-- The loop of trials from `j` remaining trials has the law `repeatTrial φ j`. -/
private theorem ampLoop_law {φ : CNF (Fin n)} {C A w : ℕ} (hw : Fits w (A + 3 * n)) (hA : 1 ≤ A) :
    ∀ (j : ℕ) (x : Data 24), Frame φ C A x → x.regs rem = j → x.regs out = 0 → Fits w j →
      ExecRandLaw w (.loop (.lt zero rem) ampBody) x
        (fun y => Frame φ C A y ∧
          (y.regs out = 0 ∨ (y.regs out = 1 ∧ φ.eval (assignmentAt y.mem A n) = true)))
        (j * (trialCoreTime n (encodeClauses φ).length + 5) + 2) (j * (4 * n))
        (fun y => decide (y.regs out = 1)) (repeatTrial φ j)
  | 0, x, hx, hr, ho, _ => by
    have hc : ¬(Cond.lt zero rem).Holds x := by simp [Cond.holds_lt, hr, hx.zero_eq]
    have h := ExecRandLaw.loop_exit (w := w) (body := ampBody)
      (f := fun y => decide (y.regs out = 1)) hc (P := fun y => Frame φ C A y ∧
          (y.regs out = 0 ∨ (y.regs out = 1 ∧ φ.eval (assignmentAt y.mem A n) = true)))
      ⟨hx, Or.inl ho⟩
    simpa [ho, repeatTrial] using h
  | j + 1, x, hx, hr, ho, hfj => by
    have hc : (Cond.lt zero rem).Holds x := by simp [Cond.holds_lt, hr, hx.zero_eq]
    have hcore := (trialCore_law (φ := φ) hw hA hx).withPreserves (i := rem) (by decide)
    have hbody := ExecRandLaw.seq_det_right (T₂ := 3)
      (c₂ := ram[ if out = one then [ rem ← zero ] else [ rem ← rem - one ] ])
      (Q := fun y => Frame φ C A y ∧
        y.regs out = (if φ.eval (assignmentAt y.mem A n) then 1 else 0) ∧
        y.regs rem = (if φ.eval (assignmentAt y.mem A n) then 0 else j)) hcore
      fun y ⟨⟨⟨hy, _⟩, hyo⟩, hyr⟩ => by
        rw [hr] at hyr
        by_cases he : φ.eval (assignmentAt y.mem A n) = true
        · simp only [he, ↓reduceIte] at hyo
          refine ⟨_, (ExecWithin.branch_pos (by simp [Cond.holds_eq, hyo, hy.one_eq])
            (ExecWithin.copy (B := .standard) (w := w) (d := rem) (s := zero) (x := y))).mono
            (by omega), ⟨hy.congr (by simp +decide) (by simp +decide) (by simp +decide)
              (by simp +decide) (by simp +decide) fun _ _ => rfl, ?_, ?_⟩, rfl⟩
          · simpa +decide [he] using hyo
          · simp +decide [he, hy.zero_eq]
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at hyo
          have hsub := ExecWithin.bin (w := w) (f := .sub) (d := rem) (i := rem) (j := one)
            (x := y) (by
              simp only [BinOp.eval, hyr, hy.one_eq, Nat.add_sub_cancel]
              exact hfj.of_le (by omega))
          refine ⟨_, (ExecWithin.branch_neg (by simp [Cond.holds_eq, hyo, hy.one_eq]) hsub).mono
            le_rfl, ⟨hy.congr (by simp +decide) (by simp +decide) (by simp +decide)
              (by simp +decide) (by simp +decide) fun _ _ => rfl, ?_, ?_⟩, rfl⟩
          · simpa +decide [he] using hyo
          · simp [he, hyr, hy.one_eq]
    have h := ExecRandLaw.loop_iter
      (κ := fun σ => if φ.eval σ then PMF.pure true else repeatTrial φ j)
      (T₂ := j * (trialCoreTime n (encodeClauses φ).length + 5) + 2) (R₂ := j * (4 * n))
      hc hbody fun y ⟨hy, hyo, hyr⟩ => by
        by_cases he : φ.eval (assignmentAt y.mem A n) = true
        · simp only [he, ↓reduceIte] at hyo hyr
          have hcy : ¬(Cond.lt zero rem).Holds y := by simp [Cond.holds_lt, hyr, hy.zero_eq]
          have h := ExecRandLaw.loop_exit (w := w) (body := ampBody)
            (f := fun y => decide (y.regs out = 1)) hcy (P := fun y => Frame φ C A y ∧
              (y.regs out = 0 ∨ (y.regs out = 1 ∧ φ.eval (assignmentAt y.mem A n) = true)))
            ⟨hy, Or.inr ⟨hyo, he⟩⟩
          have h2 : ExecRandLaw w (.loop (.lt zero rem) ampBody) y
              (fun y => Frame φ C A y ∧
                (y.regs out = 0 ∨ (y.regs out = 1 ∧ φ.eval (assignmentAt y.mem A n) = true)))
              (j * (trialCoreTime n (encodeClauses φ).length + 5) + 2) (j * (4 * n))
              (fun y => decide (y.regs out = 1)) (PMF.pure true) := by
            have h3 := h.mono (fun _ h => h)
              (show 2 ≤ j * (trialCoreTime n (encodeClauses φ).length + 5) + 2 by omega)
              (Nat.zero_le (j * (4 * n)))
            simpa only [hyo, decide_true] using h3
          simp only [he, ↓reduceIte]
          exact h2
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at hyo hyr
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          exact ampLoop_law hw hA j y hy hyr hyo (hfj.of_le (by omega))
    refine (h.congr_law rfl).mono (fun _ h => h) ?_ ?_
    · simp only [Nat.add_mul, Nat.one_mul]; omega
    · simp only [Nat.add_mul, Nat.one_mul]; omega

/-- The data after the setup on the input `R :: encode φ`. -/
def ampSetupData (R : ℕ) (φ : CNF (Fin n)) : Data 24 :=
  ((((((((Data.init (R :: encode φ)).set one 1).set val (R :: encode φ).length).set aBase
    ((R :: encode φ).length + 1)).set rem R).set val 2).set nReg n).set cBeg 3)

/-- The setup establishes the frame of the trials on the input `R :: encode φ`. -/
theorem ampSetup_exec (R : ℕ) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((R :: encode φ).length + 3 * n + 1)) :
    ExecWithin w ampSetup (Data.init (R :: encode φ)) (ampSetupData R φ) 7 ∧
      Frame φ 3 ((R :: encode φ).length + 1) (ampSetupData R φ) ∧
      (ampSetupData R φ).regs rem = R ∧ (ampSetupData R φ).regs out = 0 := by
  have hf1 : Fits w 1 := hw.of_le (by omega)
  have hf2 : Fits w ((R :: encode φ).length + 1) := hw.of_le (by omega)
  have hf3 : Fits w 2 := hw.of_le (by simp [encode]; omega)
  have hf4 : Fits w 3 := hw.of_le (by simp [encode]; omega)
  have hm0 : (Data.init (R :: encode φ) : Data 24).mem 0 = (R :: encode φ).length := rfl
  have hm1 : (Data.init (R :: encode φ) : Data 24).mem 1 = R := rfl
  have hm2 : (Data.init (R :: encode φ) : Data 24).mem 2 = n := rfl
  refine ⟨?run, ?frame, by simp +decide [ampSetupData], by simp +decide [ampSetupData]⟩
  case run => ram_eval [ampSetup, ampSetupData, Data.init_regs, hm0, hm1, hm2, hf1, hf2, hf3, hf4]
  case frame =>
    refine ⟨by simp +decide [ampSetupData], by simp +decide [ampSetupData],
      by simp +decide [ampSetupData], by simp +decide [ampSetupData],
      by simp +decide [ampSetupData], ?_, ?_⟩
    · intro i
      change (Data.init (R :: encode φ) : Data 24).mem (3 + i.val) = (encodeClauses φ)[i.val]
      rw [show 3 + i.val = (2 + i.val) + 1 by omega, Data.init_mem_succ]
      simp [encode, show 2 + i.val = (i.val + 1) + 1 by omega]
    · simp [length_encode]; omega

/-- **Schöning's algorithm on the randomized word RAM.** On the input `R :: encode φ` of length
`L`, at any word size `w` with `L + 3 n + 1 < 2 ^ w` and `R < 2 ^ w`, the program

* halts on every path within `ampTime R n L = R (36 n L + 66 n + 12 L + 18) + 10` instructions;
* makes at most `R (4 n)` `rand` calls;
* outputs `0` or `1`, and outputs `1` only with a satisfying assignment of `φ` stored at address
  `L + 1`;
* outputs `1` with exactly the law `repeatTrial φ R` of up to `R` independent trials. -/
theorem ampProgram_spec (R : ℕ) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((R :: encode φ).length + 3 * n + 1)) (hR : Fits w R) :
    RandHaltsWithin w ampProgram (.init (R :: encode φ)) (ampTime R n (R :: encode φ).length) ∧
    RandCallsBounded w ampProgram (.init (R :: encode φ)) (ampTime R n (R :: encode φ).length)
      (R * (4 * n)) ∧
    (∀ cfg ∈ (runRand w ampProgram (ampTime R n (R :: encode φ).length)
        (.running (.init (R :: encode φ)))).support,
      ∃ v d, cfg = .halted v d ∧
        (v = 0 ∨ (v = 1 ∧ φ.eval (assignmentAt d.mem ((R :: encode φ).length + 1) n) = true))) ∧
    (evalRand w ampProgram (ampTime R n (R :: encode φ).length) (.init (R :: encode φ))).map
      cfgSuccess = repeatTrial φ R := by
  set A := (R :: encode φ).length + 1
  obtain ⟨hy, hfr, hrem, hout⟩ := ampSetup_exec R φ hw
  have hA : 1 ≤ A := by omega
  have hw' : Fits w (A + 3 * n) := hw.of_le (by omega)
  have hloop := ExecRandLaw.seq_det hy (ampLoop_law (φ := φ) hw' hA R _ hfr hrem hout hR)
  have hE : (encodeClauses φ).length ≤ (R :: encode φ).length := by
    simp only [List.length_cons, length_encode]; omega
  obtain ⟨hhalt, hcalls, hpost, hlaw⟩ := hloop.program out
    (T' := ampTime R n (R :: encode φ).length)
    (by
      simp only [trialCoreTime, ampTime]
      have := Nat.mul_le_mul_left R (show 36 * n * (encodeClauses φ).length + 66 * n +
        12 * (encodeClauses φ).length + 13 + 5 ≤
          36 * n * (R :: encode φ).length + 66 * n + 12 * (R :: encode φ).length + 18 by
        have := Nat.mul_le_mul_left (36 * n) hE
        omega)
      omega)
    cfgSuccess fun _ _ => rfl
  refine ⟨hhalt, hcalls, fun cfg hcfg => ?_, hlaw⟩
  obtain ⟨d, rfl, -, hd⟩ := hpost cfg hcfg
  exact ⟨_, d, rfl, hd⟩

/-- **Failure probability.** The program outputs something other than `1` with probability exactly
`(1 - p) ^ R`, where `p = succeedProb φ (trial φ)` is the success probability of one trial. -/
theorem ampProgram_failure_eq (R : ℕ) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((R :: encode φ).length + 3 * n + 1)) (hR : Fits w R) :
    ((evalRand w ampProgram (ampTime R n (R :: encode φ).length) (.init (R :: encode φ))).map
      cfgSuccess false).toReal = (1 - succeedProb φ (trial φ)) ^ R := by
  rw [(ampProgram_spec R φ hw hR).2.2.2, repeatTrial_false_toReal]

/-- The number of trials for confidence `c`:
`⌈(3 n + 1) (2 (k - 1) / k) ^ n (k / (k - 1)) ^ (k - 3)⌉ c`, the inverse of Schöning's bound
for one trial, rounded up, times `c`. For `k = 3` it is `⌈(3 n + 1) (4 / 3) ^ n⌉ c`. -/
noncomputable def schoeningTrials (k n c : ℕ) : ℕ :=
  ⌈(3 * n + 1 : ℝ) * (2 * ((k : ℝ) - 1) / k) ^ n * ((k : ℝ) / ((k : ℝ) - 1)) ^ (k - 3)⌉₊ * c

/-- **Schöning's algorithm succeeds with high probability.** On a satisfiable formula whose
clauses have at most `k ≥ 3` literals, `schoeningTrials k n c` trials output `1` except with
probability at most `e ^ (-c)`. -/
theorem ampProgram_failure_le_exp {k c : ℕ} (hk : 3 ≤ k) {φ : CNF (Fin n)} (hφ : φ.Satisfiable)
    (hlen : ∀ cl ∈ φ, cl.length ≤ k) {w : ℕ}
    (hw : Fits w ((schoeningTrials k n c :: encode φ).length + 3 * n + 1))
    (hR : Fits w (schoeningTrials k n c)) :
    ((evalRand w ampProgram (ampTime (schoeningTrials k n c) n
        (schoeningTrials k n c :: encode φ).length)
      (.init (schoeningTrials k n c :: encode φ))).map cfgSuccess false).toReal ≤
      Real.exp (-c) := by
  rw [ampProgram_failure_eq _ φ hw hR]
  have hp := trial_success_of_length_le hk hφ hlen
  simp only [Fintype.card_fin] at hp
  have hk1 : (1 : ℝ) < (k : ℝ) - 1 := by
    have : (3 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  set P₀ := (((k : ℝ) - 1) / k) ^ (k - 3) * ((k : ℝ) / (2 * ((k : ℝ) - 1))) ^ n / (3 * n + 1)
    with hP₀
  have hP₀pos : 0 < P₀ := by
    rw [hP₀]
    have : (0 : ℝ) < k := by linarith
    positivity
  have hinv : (3 * n + 1 : ℝ) * (2 * ((k : ℝ) - 1) / k) ^ n *
      ((k : ℝ) / ((k : ℝ) - 1)) ^ (k - 3) = P₀⁻¹ := by
    rw [hP₀]
    have hk0 : (k : ℝ) ≠ 0 := by linarith
    have hk10 : (k : ℝ) - 1 ≠ 0 := by linarith
    have h1 : (2 * ((k : ℝ) - 1) / k) * ((k : ℝ) / (2 * ((k : ℝ) - 1))) = 1 := by field_simp
    have h2 : ((k : ℝ) / ((k : ℝ) - 1)) * (((k : ℝ) - 1) / k) = 1 := by field_simp
    field_simp
    calc _ = ((2 * ((k : ℝ) - 1) / k) * ((k : ℝ) / (2 * ((k : ℝ) - 1)))) ^ n *
          (((k : ℝ) / ((k : ℝ) - 1)) * (((k : ℝ) - 1) / k)) ^ (k - 3) := by
          rw [mul_pow, mul_pow]; ring
      _ = 1 := by rw [h1, h2, one_pow, one_pow, one_mul]
  have hp1 : succeedProb φ (trial φ) ≤ 1 := by
    rw [succeedProb]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact Probability.PMF.toOuterMeasure_le_one _ _)
  refine one_sub_pow_le_exp hp1 ?_
  rw [schoeningTrials, hinv]
  push_cast
  calc (c : ℝ) = (P₀⁻¹ * c) * P₀ := by field_simp
    _ ≤ (⌈P₀⁻¹⌉₊ * c) * P₀ := by gcongr; exact Nat.le_ceil _
    _ ≤ (⌈P₀⁻¹⌉₊ * c) * succeedProb φ (trial φ) := by gcongr

end Cslib.Algorithms.WordRAM.Schoening

end
