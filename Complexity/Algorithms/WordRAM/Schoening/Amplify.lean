/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.Schoening.Trial
public import Complexity.Algorithms.WordRAM.Schoening.TrialCount
public import Mathlib.Analysis.Complex.Exponential
import Complexity.Probability.PMF.Event

/-!
# Schöning's algorithm on the randomized word RAM

`Cslib.Algorithms.WordRAM.Schoening.ampProgram` is Schöning's k-SAT algorithm
[Schöning][Schoening1999] with confidence `c`, as a program of the randomized word RAM. On the
input `k :: c :: encode φ` it computes the trial count
`R = schoeningTrials k n c = ⌈(3 n + 1) (2 (k - 1) / k) ^ n (k / (k - 1)) ^ (k - 3)⌉ c` in a
multiword counter (`Cslib.Algorithms.WordRAM.Schoening.counterDigits`), then runs up to `R`
independent trials, stopping at the first trial that finds a satisfying assignment. It halts with
output `1`, leaving a satisfying assignment in memory, or with output `0` when every trial failed.

`Cslib.Algorithms.WordRAM.Schoening.ampProgram_spec` proves, at every word size `w` with
`L + 6 n + 4 k + 2 c + counterLen k n c + 2 < 2 ^ w`, where `L` is the input length and
`counterLen k n c = O((n + k) log (n + k) + log c)` bounds the number of digits of `R`:

* the program halts on every path within `ampTime k n c L` instructions, which is
  `R (36 n L + 66 n + 12 L + 43)` plus a setup cost polynomial in `n`, `k` and `log c`;
* it makes at most `4 n R` `rand` calls;
* an output `1` always comes with a satisfying assignment, so the program never errs on
  unsatisfiable formulas;
* the output is `1` with exactly the law of `R` independent trials
  (`Cslib.Algorithms.WordRAM.Schoening.repeatTrial`), so it is `0` with probability exactly
  `(1 - p) ^ R`, where `p` is the success probability of one trial
  (`Cslib.Algorithms.WordRAM.Schoening.ampProgram_failure_eq`).

Combined with Schöning's bound for one trial
(`Cslib.Complexity.Schoening.trial_success_of_length_le`), the program fails on a satisfiable
formula with clauses of at most `k ≥ 3` literals with probability at most `e ^ (-c)`
(`Cslib.Algorithms.WordRAM.Schoening.ampProgram_failure_le_exp`). For `k = 3` there are
`⌈(3 n + 1) (4 / 3) ^ n⌉ c` trials, so the time is `O(n ^ 2 L (4 / 3) ^ n c)` plus the
polynomial setup: Schöning's `O*((2 - 2 / k) ^ n)` running time, with the polynomial factor
explicit. The word size needs only `O(log (n + k + L + c))` bits, which is `O(log (L + c))` when
`k` is fixed and `n = O(L)`; `n` and `k` count separately because the input length `L` does not
bound them (a formula without clauses has `L = 3` for every `n`). The trial count, of about
`0.415 n` bits for `k = 3`, is kept in memory, one binary digit per word. A decrement reads the
digits up to the lowest nonzero one, which costs a constant amortized number of instructions per
trial.

## Main definitions

* `Cslib.Algorithms.WordRAM.Schoening.repeatTrial`: the law of the output of up to `R`
  independent trials.
* `Cslib.Algorithms.WordRAM.Schoening.countSetup`: the computation of the trial count.
* `Cslib.Algorithms.WordRAM.Schoening.ampCode`, `Cslib.Algorithms.WordRAM.Schoening.ampProgram`:
  the amplified algorithm, structured and compiled.
* `Cslib.Algorithms.WordRAM.Schoening.ampTime`: its instruction bound.
* `Cslib.Algorithms.WordRAM.Schoening.cfgSuccess`: whether a halting run output `1`.

## Main results

* `Cslib.Algorithms.WordRAM.Schoening.repeatTrial_false_toReal`: `R` trials all fail with
  probability `(1 - p) ^ R`.
* `Cslib.Algorithms.WordRAM.Schoening.ampTime_le`: the time bound is
  `O((n + k + L) ^ 3 (2 - 2 / k) ^ n (c + 1))`.
* `Cslib.Algorithms.WordRAM.Schoening.ampProgram_spec`: halting, time and `rand` bounds, no false
  positives, and the exact law of the output.
* `Cslib.Algorithms.WordRAM.Schoening.ampProgram_failure_eq`: the program fails with probability
  `(1 - p) ^ R`.
* `Cslib.Algorithms.WordRAM.Schoening.ampProgram_failure_le_exp`: on a satisfiable k-CNF the
  program fails with probability at most `e ^ (-c)`.

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

namespace Reg

/-- `k`, during the setup; shares register `5` with `ptr`. -/
abbrev kReg : Fin 24 := 5
/-- `c`, during the setup; shares register `6` with `len`. -/
abbrev cReg : Fin 24 := 6
/-- `k - 3`, during the setup; shares register `7` with `lptr`. -/
abbrev kSub : Fin 24 := 7
/-- Loop counter of the setup; shares register `18` with `steps`. -/
abbrev outer : Fin 24 := 18

end Reg

/-- Set up the registers on the input `k :: c :: encode φ`: the clauses start at address `4`, the
assignment is stored just after the input, the counter just after the assignment, and it is
empty. -/
def ampSetup : Code .standard 24 := ram[
  one ← #1; val ← *zero; aBase ← val + one; kReg ← *one; val ← one + one; cReg ← *val;
  val ← val + one; nReg ← *val; cBeg ← val + one; bBase ← aBase + nReg; bLen ← zero;
  val ← #3; kSub ← kReg - val ]

/-- Set the counter to `3 n + 1`. -/
def countInit : Code .standard 24 := ram[
  ⟪ram[ mulr ← zero; carry ← nReg + nReg; carry ← carry + nReg; carry ← carry + one ]⟫;
  ⟪mulAdd⟫ ]

/-- Multiply the counter by `2 (k - 1)`. -/
def numStep₁ : Code .standard 24 := ram[
  ⟪ram[ mulr ← kReg - one; mulr ← mulr + mulr; carry ← zero ]⟫; ⟪mulAdd⟫ ]

/-- Multiply the counter by `k`. -/
def numStep₂ : Code .standard 24 := ram[ ⟪ram[ mulr ← kReg; carry ← zero ]⟫; ⟪mulAdd⟫ ]

/-- Divide the counter by `k`, rounding up. -/
def denStep₁ : Code .standard 24 := ram[
  ⟪ram[ mulr ← one; carry ← kReg - one ]⟫; ⟪mulAdd⟫; dvs ← kReg; ⟪divFloor⟫ ]

/-- Divide the counter by `k - 1`, rounding up. -/
def denStep₂ : Code .standard 24 := ram[
  ⟪ram[ mulr ← one; carry ← kReg - one; carry ← carry - one ]⟫; ⟪mulAdd⟫; dvs ← kReg - one;
  ⟪divFloor⟫ ]

/-- Multiply the counter by `c`. -/
def confStep : Code .standard 24 := ram[ ⟪ram[ mulr ← cReg; carry ← zero ]⟫; ⟪mulAdd⟫ ]

/-- Run `body` as many times as register `lim` says. -/
def repeatCode (lim : Fin 24) (body : Code .standard 24) : Code .standard 24 :=
  ram[ outer ← zero; while outer < lim do [ ⟪body⟫; outer ← outer + one ] ]

/-- **The trial count**: compute `schoeningTrials k n c` in the counter. -/
def countSetup : Code .standard 24 := ram[
  ⟪countInit⟫; ⟪repeatCode nReg numStep₁⟫; ⟪repeatCode kSub numStep₂⟫;
  ⟪repeatCode nReg denStep₁⟫; ⟪repeatCode kSub denStep₂⟫; ⟪confStep⟫ ]

/-- Decrement the counter; stop if it was zero, and otherwise run one trial and stop after a
success. -/
def ampBody : Code .standard 24 := ram[
  ⟪decCounter⟫;
  if found = zero then [ flag ← zero ]
  else [ ⟪trialCore⟫; if out = one then [ flag ← zero ] else [ flag ← one ] ] ]

/-- Run trials while `flag > 0`. -/
def ampLoop : Code .standard 24 := .loop (.lt zero flag) ampBody

/-- **Schöning's algorithm** on the input `k :: c :: encode φ`. -/
def ampCode : Code .standard 24 := ram[ ⟪ampSetup⟫; ⟪countSetup⟫; flag ← one; ⟪ampLoop⟫ ]

/-- **Schöning's algorithm** on the input `k :: c :: encode φ`, halting with `out`. -/
def ampProgram : Program .standard 24 := ampCode.program out

/-- The instruction bound of the setup. -/
def setupTime (k n c : ℕ) : ℕ :=
  (n + k) * (30 * counterLen k n c + 30) + 20 * counterLen k n c + 50

/-- The instruction bound of Schöning's algorithm with confidence `c`, on `n` variables, clauses
of at most `k` literals and an input of length `L`. -/
noncomputable def ampTime (k n c L : ℕ) : ℕ :=
  schoeningTrials k n c * (36 * n * L + 66 * n + 12 * L + 43) + setupTime k n c +
    9 * counterLen k n c + 45

/-- Whether a halting run output `1`. -/
def cfgSuccess {r : ℕ} : RandCfg r → Bool
  | .halted v _ => decide (v = 1)
  | _ => false

/-- **The running time** of Schöning's algorithm is `O((n + k + L) ^ 3 (2 - 2 / k) ^ n (c + 1))`:
explicitly, at most `900 (n + k + L + 1) ^ 3 (2 (k - 1) / k) ^ n (c + 1)` instructions. For
`k = 3` this is `O((n + L) ^ 3 (4 / 3) ^ n (c + 1))`. -/
theorem ampTime_le {k : ℕ} (hk : 3 ≤ k) (n c L : ℕ) :
    (ampTime k n c L : ℝ) ≤
      900 * ((n + k + L + 1 : ℕ) : ℝ) ^ 3 * (2 * ((k : ℝ) - 1) / k) ^ n * (c + 1) := by
  set r := (2 * ((k : ℝ) - 1) / k) ^ n with hr
  obtain ⟨N, hN⟩ : ∃ N, n + k + L + 1 = N := ⟨_, rfl⟩
  rw [hN]
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hr1 : 1 ≤ r := one_le_pow₀ (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hR := schoeningTrials_le hk n c
  rw [← hr] at hR
  -- the setup
  have hS : setupTime k n c + 9 * counterLen k n c + 45 ≤ 305 * N ^ 3 * (c + 1) := by
    obtain ⟨m, hm⟩ : ∃ m, n + k = m := ⟨_, rfl⟩
    have hℓ : counterLen k n c ≤ 6 * m ^ 2 + c := hm ▸ counterLen_le k n c
    have h1 : setupTime k n c + 9 * counterLen k n c + 45 ≤
        (m + 1) * (30 * counterLen k n c + 95) := by
      simp only [setupTime, hm]; ring_nf; omega
    have h2 : (m + 1) * (30 * counterLen k n c + 95) ≤ (m + 1) * (180 * m ^ 2 + 30 * c + 95) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : (m + 1) * (180 * m ^ 2 + 30 * c + 95) ≤ 305 * (m + 1) ^ 3 * (c + 1) := by
      ring_nf; omega
    have h4 : (m + 1) ^ 3 ≤ N ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have h5 := Nat.mul_le_mul_right (c + 1) (Nat.mul_le_mul_left 305 h4)
    omega
  -- the trials
  have hP : 9 * n + 4 ≤ 9 * (n + 1) ∧ 36 * n * L + 66 * n + 12 * L + 43 ≤ 66 * (n + 1) * (L + 1) :=
    ⟨by omega, by ring_nf; omega⟩
  have hPN : 9 * (n + 1) * (66 * (n + 1) * (L + 1)) ≤ 594 * N ^ 3 := by
    have h1 : n + 1 ≤ N := by omega
    have h2 : L + 1 ≤ N := by omega
    have h3 : (n + 1) * (n + 1) * (L + 1) ≤ N * N * N :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h1) h2
    calc 9 * (n + 1) * (66 * (n + 1) * (L + 1)) = 594 * ((n + 1) * (n + 1) * (L + 1)) := by ring
      _ ≤ 594 * (N * N * N) := Nat.mul_le_mul_left _ h3
      _ = 594 * N ^ 3 := by ring
  have hPr : ((36 * n * L + 66 * n + 12 * L + 43 : ℕ) : ℝ) ≤ 66 * (n + 1) * (L + 1) := by
    exact_mod_cast hP.2
  have hPN' : (9 * n + 4 : ℝ) * (66 * (n + 1) * (L + 1)) ≤ 594 * (N : ℝ) ^ 3 := by
    have : ((9 * n + 4) * (66 * (n + 1) * (L + 1)) : ℕ) ≤ 594 * N ^ 3 :=
      (Nat.mul_le_mul_right _ hP.1).trans hPN
    exact_mod_cast this
  have hSr : ((setupTime k n c + 9 * counterLen k n c + 45 : ℕ) : ℝ) ≤
      305 * (N : ℝ) ^ 3 * (c + 1) := by
    exact_mod_cast hS
  have hexp : (ampTime k n c L : ℝ) =
      (schoeningTrials k n c : ℝ) * ((36 * n * L + 66 * n + 12 * L + 43 : ℕ) : ℝ) +
        ((setupTime k n c + 9 * counterLen k n c + 45 : ℕ) : ℝ) := by
    simp only [ampTime]; push_cast; ring
  have hT : (schoeningTrials k n c : ℝ) * ((36 * n * L + 66 * n + 12 * L + 43 : ℕ) : ℝ) ≤
      (9 * n + 4) * r * c * (66 * (n + 1) * (L + 1)) :=
    mul_le_mul hR hPr (Nat.cast_nonneg _) (by positivity)
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_right hPN' (mul_nonneg (by linarith : (0 : ℝ) ≤ r) hc0),
    mul_le_mul_of_nonneg_left hr1 (mul_nonneg hN0 (by linarith : (0 : ℝ) ≤ c + 1))]

/-! ### The setup -/

/-- The setup registers: those of the frame, `kReg`, `cReg`, `kSub`, `bBase` and `out`. -/
private def PreservesSetup (c : Code .standard 24) : Prop :=
  PreservesFrame c ∧ c.Preserves kReg ∧ c.Preserves cReg ∧ c.Preserves kSub ∧
    c.Preserves bBase ∧ c.Preserves out

private instance (c : Code .standard 24) : Decidable (PreservesSetup c) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The state during the setup: the frame of the trials, the setup registers, and the counter
digits `ds` at `A + n`. -/
structure SetupState (φ : CNF (Fin n)) (k c A : ℕ) (ds : List ℕ) (x : Data 24) : Prop where
  frame : Frame φ 4 A x.mem x
  kReg_eq : x.regs kReg = k
  cReg_eq : x.regs cReg = c
  kSub_eq : x.regs kSub = k - 3
  bBase_eq : x.regs bBase = A + n
  bLen_eq : x.regs bLen = ds.length
  digits : HoldsList (A + n) ds x.mem
  binary : ∀ d ∈ ds, d ≤ 1
  out_eq : x.regs out = 0

/-- Setup code that keeps the setup registers and the memory below the counter keeps the setup
state, with the new counter digits. -/
private theorem SetupState.of_exec {φ : CNF (Fin n)} {k c A w T : ℕ} {ds ds' : List ℕ}
    {code : Code .standard 24} {x y : Data 24} (h : SetupState φ k c A ds x)
    (hc : PreservesSetup code) (he : ExecWithin w code x y T)
    (hmem : ∀ a < A + n, y.mem a = x.mem a) (hl : y.regs bLen = ds'.length)
    (hh : HoldsList (A + n) ds' y.mem) (hb : ∀ d ∈ ds', d ≤ 1) : SetupState φ k c A ds' y where
  frame := h.frame.of_mem_lt (he.regs_eq hc.1.1) (he.regs_eq hc.1.2.1) (he.regs_eq hc.1.2.2.1)
    (he.regs_eq hc.1.2.2.2.1) (he.regs_eq hc.1.2.2.2.2) fun a ha => hmem a (by omega)
  kReg_eq := (he.regs_eq hc.2.1).trans h.kReg_eq
  cReg_eq := (he.regs_eq hc.2.2.1).trans h.cReg_eq
  kSub_eq := (he.regs_eq hc.2.2.2.1).trans h.kSub_eq
  bBase_eq := (he.regs_eq hc.2.2.2.2.1).trans h.bBase_eq
  bLen_eq := hl
  digits := hh
  binary := hb
  out_eq := (he.regs_eq hc.2.2.2.2.2).trans h.out_eq

/-- The setup state does not depend on the registers outside the setup registers and `bLen`. -/
private theorem SetupState.set {φ : CNF (Fin n)} {k c A : ℕ} {ds : List ℕ} {x : Data 24}
    (h : SetupState φ k c A ds x) {i : Fin 24}
    (hi : i ∉ ({zero, one, cBeg, aBase, nReg, kReg, cReg, kSub, bBase, bLen, out} :
      Finset (Fin 24)))
    (v : ℕ) : SetupState φ k c A ds (x.set i v) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hi
  exact
    { frame := h.frame.of_mem_lt (by simp [Function.update_of_ne (Ne.symm h0)])
        (by simp [Function.update_of_ne (Ne.symm h1)])
        (by simp [Function.update_of_ne (Ne.symm h2)])
        (by simp [Function.update_of_ne (Ne.symm h3)])
        (by simp [Function.update_of_ne (Ne.symm h4)])
        fun _ _ => rfl
      kReg_eq := by simp [Function.update_of_ne (Ne.symm h5), h.kReg_eq]
      cReg_eq := by simp [Function.update_of_ne (Ne.symm h6), h.cReg_eq]
      kSub_eq := by simp [Function.update_of_ne (Ne.symm h7), h.kSub_eq]
      bBase_eq := by simp [Function.update_of_ne (Ne.symm h8), h.bBase_eq]
      bLen_eq := by simp [Function.update_of_ne (Ne.symm h9), h.bLen_eq]
      digits := by simpa using h.digits
      binary := h.binary
      out_eq := by simp [Function.update_of_ne (Ne.symm h10), h.out_eq] }

/-- A multiply-add during the setup. -/
private theorem SetupState.mulAdd {φ : CNF (Fin n)} {k c A w a cy Bd : ℕ} {ds : List ℕ}
    {x : Data 24} (h : SetupState φ k c A ds x) (ha : x.regs mulr = a) (hcy : x.regs carry = cy)
    (haB : a ≤ Bd)
    (hcB : cy ≤ Bd) (hf : Fits w (2 * Bd)) (hfit : Fits w (A + n + (mulAddDigits a cy ds).length)) :
    ∃ y, ExecWithin w mulAdd x y (10 * (mulAddDigits a cy ds).length + 5) ∧
      SetupState φ k c A (mulAddDigits a cy ds) y ∧ y.regs outer = x.regs outer := by
  obtain ⟨y, hy, hh, hl, hm⟩ := mulAdd_spec h.frame.zero_eq h.frame.one_eq ha hcy h.bLen_eq
    (by rw [h.bBase_eq]; exact h.digits) h.binary haB hcB hf (by rw [h.bBase_eq]; exact hfit)
  rw [h.bBase_eq] at hh hm
  exact ⟨y, hy, h.of_exec (by decide) hy hm hl hh (mulAddDigits_digit_le a cy ds),
    hy.regs_eq (by decide)⟩

/-- A division during the setup. -/
private theorem SetupState.divFloor {φ : CNF (Fin n)} {k c A w d : ℕ} {ds : List ℕ} {x : Data 24}
    (h : SetupState φ k c A ds x) (hd : 0 < d) (hdv : x.regs dvs = d) (hfd : Fits w (2 * d))
    (hfit : Fits w (A + n + ds.length)) :
    ∃ y, ExecWithin w divFloor x y (10 * ds.length + 4) ∧
      SetupState φ k c A (divDigits d 0 ds).1 y ∧ y.regs outer = x.regs outer := by
  obtain ⟨y, hy, hh, hm⟩ := divFloor_spec hd hfd h.frame.zero_eq h.frame.one_eq hdv h.bLen_eq
    (by rw [h.bBase_eq]; exact h.digits) h.binary (by rw [h.bBase_eq]; exact hfit)
  rw [h.bBase_eq] at hh hm
  refine ⟨y, hy, h.of_exec (by decide) hy hm ?_ hh (divDigits_digit_le hd hd h.binary),
    hy.regs_eq (by decide)⟩
  rw [hy.regs_eq (by decide), h.bLen_eq, length_divDigits]

/-- **A counted loop** of the setup: `j` runs of a body taking the counter digits `ds` to
`F ds`. -/
private theorem SetupState.repeatCode {φ : CNF (Fin n)} {k c A w Tb j : ℕ} {lim : Fin 24}
    {body : Code .standard 24} (hlim : lim ≠ outer) (hbl : body.Preserves lim)
    (hbo : body.Preserves outer) (F : List ℕ → List ℕ) {ds : List ℕ}
    (hbody : ∀ i < j, ∀ x, SetupState φ k c A (F^[i] ds) x →
      ∃ y, ExecWithin w body x y Tb ∧ SetupState φ k c A (F^[i + 1] ds) y)
    (hfit : Fits w j) {x : Data 24} (hx : SetupState φ k c A ds x) (hl : x.regs lim = j) :
    ∃ y, ExecWithin w (repeatCode lim body) x y (j * (Tb + 3) + 3) ∧
      SetupState φ k c A (F^[j] ds) y := by
  have hz := hx.frame.zero_eq
  have h₀ : ExecWithin w (ram[ outer ← zero ] : Code .standard 24) x (x.set outer 0) 1 := by
    ram_eval [hz]
  obtain ⟨y, hy, ⟨i, hij, hyo, hyl, hyI⟩, hc⟩ := ExecWithin.loop_invariant (w := w)
    (x := x.set outer 0)
    (cond := .lt outer lim) (body := ram[ ⟪body⟫; outer ← outer + one ]) (T := Tb + 1)
    (fun x => ∃ i ≤ j, x.regs outer = i ∧ x.regs lim = j ∧ SetupState φ k c A (F^[i] ds) x)
    (fun x => j - x.regs outer)
    (fun x ⟨i, hij, hxo, hxl, hxI⟩ hcx => by
      have hi : i < j := by simpa [Cond.holds_lt, hxo, hxl] using hcx
      obtain ⟨y, hy, hyI⟩ := hbody i hi x hxI
      have hyo : y.regs outer = i := (hy.regs_eq hbo).trans hxo
      have hyl : y.regs lim = j := (hy.regs_eq hbl).trans hxl
      have hinc : ExecWithin w (ram[ outer ← outer + one ] : Code .standard 24) y
          (y.set outer (i + 1)) 1 := by
        ram_eval [hyo, hyI.frame.one_eq, hfit.of_le (show i + 1 ≤ j by omega)]
      refine ⟨_, hy.seq hinc, ⟨i + 1, hi, by simp, ?_, hyI.set (by decide) _⟩, ?_⟩
      · rw [Data.set_regs, Function.update_of_ne hlim, hyl]
      · simp only [Data.set_regs, Function.update_self, hxo]
        omega)
    ⟨0, Nat.zero_le _, by simp, by simp [Function.update_of_ne hlim, hl], by
      simpa using hx.set (by decide) 0⟩
  have hij' : i = j := by
    simp only [Cond.holds_lt, not_lt, hyo, hyl] at hc
    omega
  subst hij'
  refine ⟨y, (h₀.seq hy).mono ?_, hyI⟩
  simp only [Data.set_regs, Function.update_self, Nat.sub_zero,
    show Tb + 1 + 2 = Tb + 3 by omega]
  omega

/-- Multiplication by `2 (k - 1)` during the setup. -/
private theorem SetupState.numStep₁ {φ : CNF (Fin n)} {k c A w : ℕ} {ds : List ℕ} {x : Data 24}
    (h : SetupState φ k c A ds x) (hk : 3 ≤ k) (hf : Fits w (4 * k))
    (hfit : Fits w (A + n + (mulStep (2 * (k - 1)) ds).length)) :
    ∃ y, ExecWithin w numStep₁ x y (10 * (mulStep (2 * (k - 1)) ds).length + 8) ∧
      SetupState φ k c A (mulStep (2 * (k - 1)) ds) y := by
  unfold mulStep at hfit ⊢
  have hf1 : Fits w (k - 1) := hf.of_le (by omega)
  have hf2 : Fits w (k - 1 + (k - 1)) := hf.of_le (by omega)
  let x₃ := ((x.set mulr (k - 1)).set mulr (k - 1 + (k - 1))).set carry 0
  have hpre : ExecWithin w (ram[ mulr ← kReg - one; mulr ← mulr + mulr; carry ← zero ] :
      Code .standard 24) x x₃ 3 := by
    ram_eval [x₃, h.kReg_eq, h.frame.one_eq, h.frame.zero_eq, hf1, hf2]
  have h₃ : SetupState φ k c A ds x₃ :=
    ((h.set (by decide) _).set (by decide) _).set (by decide) _
  obtain ⟨y, hy, hyS, -⟩ := h₃.mulAdd (a := 2 * (k - 1)) (cy := 0) (Bd := 2 * (k - 1))
    (by simp +decide [x₃]; omega) (by simp +decide [x₃]) le_rfl (Nat.zero_le _)
    (hf.of_le (by omega)) hfit
  exact ⟨y, (hpre.seq hy).mono (by omega), hyS⟩

/-- Multiplication by `k` during the setup. -/
private theorem SetupState.numStep₂ {φ : CNF (Fin n)} {k c A w : ℕ} {ds : List ℕ} {x : Data 24}
    (h : SetupState φ k c A ds x) (hf : Fits w (2 * k))
    (hfit : Fits w (A + n + (mulStep k ds).length)) :
    ∃ y, ExecWithin w numStep₂ x y (10 * (mulStep k ds).length + 8) ∧
      SetupState φ k c A (mulStep k ds) y := by
  unfold mulStep at hfit ⊢
  let x₂ := (x.set mulr k).set carry 0
  have hpre : ExecWithin w (ram[ mulr ← kReg; carry ← zero ] : Code .standard 24) x x₂ 2 := by
    ram_eval [x₂, h.kReg_eq, h.frame.zero_eq]
  have h₂ : SetupState φ k c A ds x₂ := (h.set (by decide) _).set (by decide) _
  obtain ⟨y, hy, hyS, -⟩ := h₂.mulAdd (a := k) (cy := 0) (Bd := k) (by simp +decide [x₂])
    (by simp +decide [x₂]) le_rfl (Nat.zero_le _) hf hfit
  exact ⟨y, (hpre.seq hy).mono (by omega), hyS⟩

/-- Division by `k`, rounding up, during the setup. -/
private theorem SetupState.denStep₁ {φ : CNF (Fin n)} {k c A w : ℕ} {ds : List ℕ} {x : Data 24}
    (h : SetupState φ k c A ds x) (hk : 3 ≤ k) (hf : Fits w (2 * k))
    (hfit : Fits w (A + n + (ceilStep k ds).length)) :
    ∃ y, ExecWithin w denStep₁ x y (20 * (ceilStep k ds).length + 13) ∧
      SetupState φ k c A (ceilStep k ds) y := by
  have hlen : (ceilStep k ds).length = (mulAddDigits 1 (k - 1) ds).length := by
    rw [ceilStep, length_divDigits]
  rw [hlen] at hfit ⊢
  have hf1 : Fits w (k - 1) := hf.of_le (by omega)
  let x₂ := (x.set mulr 1).set carry (k - 1)
  have hpre : ExecWithin w (ram[ mulr ← one; carry ← kReg - one ] : Code .standard 24) x x₂ 2 := by
    ram_eval [x₂, h.kReg_eq, h.frame.one_eq, hf1]
  have h₂ : SetupState φ k c A ds x₂ := (h.set (by decide) _).set (by decide) _
  obtain ⟨y, hy, hyS, -⟩ := h₂.mulAdd (a := 1) (cy := k - 1) (Bd := k) (by simp +decide [x₂])
    (by simp +decide [x₂]) (by omega) (by omega) hf hfit
  have hdv : ExecWithin w (ram[ dvs ← kReg ] : Code .standard 24) y (y.set dvs k) 1 := by
    ram_eval [hyS.kReg_eq]
  obtain ⟨z, hz, hzS, -⟩ := (hyS.set (i := dvs) (by decide) k).divFloor (d := k) (by omega)
    (by simp +decide) hf hfit
  exact ⟨z, (hpre.seq (hy.seq (hdv.seq hz))).mono (by omega), hzS⟩

/-- Division by `k - 1`, rounding up, during the setup. -/
private theorem SetupState.denStep₂ {φ : CNF (Fin n)} {k c A w : ℕ} {ds : List ℕ} {x : Data 24}
    (h : SetupState φ k c A ds x) (hk : 3 ≤ k) (hf : Fits w (2 * k))
    (hfit : Fits w (A + n + (ceilStep (k - 1) ds).length)) :
    ∃ y, ExecWithin w denStep₂ x y (20 * (ceilStep (k - 1) ds).length + 13) ∧
      SetupState φ k c A (ceilStep (k - 1) ds) y := by
  have hlen : (ceilStep (k - 1) ds).length = (mulAddDigits 1 (k - 1 - 1) ds).length := by
    rw [ceilStep, length_divDigits]
  rw [hlen] at hfit ⊢
  have hf1 : Fits w (k - 1) := hf.of_le (by omega)
  have hf2 : Fits w (k - 1 - 1) := hf.of_le (by omega)
  let x₃ := ((x.set mulr 1).set carry (k - 1)).set carry (k - 1 - 1)
  have hpre : ExecWithin w (ram[ mulr ← one; carry ← kReg - one; carry ← carry - one ] :
      Code .standard 24) x x₃ 3 := by
    ram_eval [x₃, h.kReg_eq, h.frame.one_eq, hf1, hf2]
  have h₃ : SetupState φ k c A ds x₃ :=
    ((h.set (by decide) _).set (by decide) _).set (by decide) _
  obtain ⟨y, hy, hyS, -⟩ := h₃.mulAdd (a := 1) (cy := k - 1 - 1) (Bd := k)
    (by simp +decide [x₃]) (by simp +decide [x₃]) (by omega) (by omega) hf hfit
  have hdv : ExecWithin w (ram[ dvs ← kReg - one ] : Code .standard 24) y (y.set dvs (k - 1))
      1 := by
    ram_eval [hyS.kReg_eq, hyS.frame.one_eq, hf1]
  obtain ⟨z, hz, hzS, -⟩ := (hyS.set (i := dvs) (by decide) (k - 1)).divFloor (d := k - 1)
    (by omega)
    (by simp +decide) (hf.of_le (by omega)) hfit
  exact ⟨z, (hpre.seq (hy.seq (hdv.seq hz))).mono (by omega), hzS⟩

/-- **Computing the trial count.** From an empty counter, the setup leaves the digits
`counterDigits k n c` of `schoeningTrials k n c` within `setupTime k n c` instructions. -/
theorem countSetup_exec {φ : CNF (Fin n)} {k c A w : ℕ} {x : Data 24} (hk : 3 ≤ k)
    (h : SetupState φ k c A [] x) (hfm : Fits w (6 * n + 4 * k + 2 * c + 2))
    (hfa : Fits w (A + n + counterLen k n c)) :
    ∃ y, ExecWithin w countSetup x y (setupTime k n c) ∧
      SetupState φ k c A (counterDigits k n c) y := by
  set ℓ := counterLen k n c with hℓ
  have hlast := length_counterDigits_le hk n c
  obtain ⟨hs1, hs2, hs3, hs4⟩ := length_stages_le k n c
  have hfl {m : ℕ} (hm : m ≤ ℓ) : Fits w (A + n + m) := hfa.of_le (by omega)
  -- the counter starts at `3 n + 1`
  have hL₀ : (mulAddDigits 0 (3 * n + 1) []).length ≤ ℓ := (hs1 0 (Nat.zero_le _)).trans hlast
  have hf3 : Fits w (n + n) := hfm.of_le (by omega)
  have hf4 : Fits w (n + n + n) := hfm.of_le (by omega)
  have hf5 : Fits w (n + n + n + 1) := hfm.of_le (by omega)
  let x₄ := (((x.set mulr 0).set carry (n + n)).set carry (n + n + n)).set carry (n + n + n + 1)
  have hpre : ExecWithin w (ram[ mulr ← zero; carry ← nReg + nReg; carry ← carry + nReg;
      carry ← carry + one ] : Code .standard 24) x x₄ 4 := by
    ram_eval [x₄, h.frame.zero_eq, h.frame.one_eq, h.frame.nReg_eq, hf3, hf4, hf5]
  have h₄ : SetupState φ k c A [] x₄ :=
    (((h.set (by decide) _).set (by decide) _).set (by decide) _).set (by decide) _
  obtain ⟨y₀, hy₀, hS₀, -⟩ := h₄.mulAdd (a := 0) (cy := 3 * n + 1) (Bd := 3 * n + 1)
    (by simp +decide [x₄]) (by simp +decide [x₄]; omega) (Nat.zero_le _) le_rfl
    (hfm.of_le (by omega)) (hfl hL₀)
  have h0 : ExecWithin w countInit x y₀ (10 * ℓ + 9) := (hpre.seq hy₀).mono (by omega)
  -- multiply by `2 (k - 1)`, `n` times
  obtain ⟨y₁, hy₁, hS₁⟩ := hS₀.repeatCode (lim := nReg) (body := numStep₁) (j := n)
    (Tb := 10 * ℓ + 8) (by decide) (by decide)
    (by decide) (mulStep (2 * (k - 1))) (fun i hi z hz => by
      have hb := (hs1 (i + 1) hi).trans hlast
      rw [Function.iterate_succ_apply'] at hb ⊢
      obtain ⟨y, hy, hyS⟩ := hz.numStep₁ hk (hfm.of_le (by omega)) (hfl hb)
      exact ⟨y, hy.mono (by omega), hyS⟩)
    (hfm.of_le (by omega)) hS₀.frame.nReg_eq
  -- multiply by `k`, `k - 3` times
  obtain ⟨y₂, hy₂, hS₂⟩ := hS₁.repeatCode (lim := kSub) (body := numStep₂) (j := k - 3)
    (Tb := 10 * ℓ + 8) (by decide)
    (by decide) (by decide) (mulStep k) (fun i hi z hz => by
      have hb := (hs2 (i + 1) hi).trans hlast
      rw [Function.iterate_succ_apply'] at hb ⊢
      obtain ⟨y, hy, hyS⟩ := hz.numStep₂ (hfm.of_le (by omega)) (hfl hb)
      exact ⟨y, hy.mono (by omega), hyS⟩)
    (hfm.of_le (by omega)) hS₁.kSub_eq
  change SetupState φ k c A (numeratorDigits k n) y₂ at hS₂
  -- divide by `k`, `n` times
  obtain ⟨y₃, hy₃, hS₃⟩ := hS₂.repeatCode (lim := nReg) (body := denStep₁) (j := n)
    (Tb := 20 * ℓ + 13) (by decide) (by decide)
    (by decide) (ceilStep k) (fun i hi z hz => by
      have hb := (hs3 (i + 1) hi).trans hlast
      rw [Function.iterate_succ_apply'] at hb ⊢
      obtain ⟨y, hy, hyS⟩ := hz.denStep₁ hk (hfm.of_le (by omega)) (hfl hb)
      exact ⟨y, hy.mono (by omega), hyS⟩)
    (hfm.of_le (by omega)) hS₂.frame.nReg_eq
  -- divide by `k - 1`, `k - 3` times
  obtain ⟨y₄, hy₄, hS₄⟩ := hS₃.repeatCode (lim := kSub) (body := denStep₂) (j := k - 3)
    (Tb := 20 * ℓ + 13) (by decide)
    (by decide) (by decide) (ceilStep (k - 1)) (fun i hi z hz => by
      have hb := (hs4 (i + 1) hi).trans hlast
      rw [Function.iterate_succ_apply'] at hb ⊢
      obtain ⟨y, hy, hyS⟩ := hz.denStep₂ hk (hfm.of_le (by omega)) (hfl hb)
      exact ⟨y, hy.mono (by omega), hyS⟩)
    (hfm.of_le (by omega)) hS₃.kSub_eq
  -- multiply by `c`
  have hlast' : (mulAddDigits c 0 ((ceilStep (k - 1))^[k - 3] ((ceilStep k)^[n]
      (numeratorDigits k n)))).length ≤ ℓ := hlast
  let x₂ := (y₄.set mulr c).set carry 0
  have hpre₅ : ExecWithin w (ram[ mulr ← cReg; carry ← zero ] : Code .standard 24) y₄ x₂ 2 := by
    ram_eval [x₂, hS₄.cReg_eq, hS₄.frame.zero_eq]
  have h₂ : SetupState φ k c A _ x₂ := (hS₄.set (by decide) _).set (by decide) _
  obtain ⟨y₅, hy₅, hS₅, -⟩ := h₂.mulAdd (a := c) (cy := 0) (Bd := c) (by simp +decide [x₂])
    (by simp +decide [x₂]) le_rfl (Nat.zero_le _) (hfm.of_le (by omega)) (hfl hlast')
  have h5 : ExecWithin w confStep y₄ y₅ (10 * ℓ + 7) := (hpre₅.seq hy₅).mono (by omega)
  refine ⟨y₅, (h0.seq (hy₁.seq (hy₂.seq (hy₃.seq (hy₄.seq h5))))).mono ?_, hS₅⟩
  simp only [setupTime, ← hℓ]
  have hkn : k - 3 ≤ k := Nat.sub_le k 3
  nlinarith

/-- The data after the setup on the input `k :: c :: encode φ`. -/
def ampSetupData (k c : ℕ) (φ : CNF (Fin n)) : Data 24 :=
  ((((((((((((((Data.init (k :: c :: encode φ)).set one 1).set val
    (k :: c :: encode φ).length).set aBase ((k :: c :: encode φ).length + 1)).set kReg k).set
    val 2).set cReg c).set val 3).set nReg n).set cBeg 4).set bBase
    ((k :: c :: encode φ).length + 1 + n)).set bLen 0).set val 3).set kSub (k - 3))

/-- The setup establishes the setup state with an empty counter on the input
`k :: c :: encode φ`. -/
theorem ampSetup_exec (k c : ℕ) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((k :: c :: encode φ).length + n + k + 4)) :
    ExecWithin w ampSetup (Data.init (k :: c :: encode φ)) (ampSetupData k c φ) 13 ∧
      SetupState φ k c ((k :: c :: encode φ).length + 1) [] (ampSetupData k c φ) := by
  have hf1 : Fits w 1 := hw.of_le (by omega)
  have hf2 : Fits w ((k :: c :: encode φ).length + 1) := hw.of_le (by omega)
  have hf3 : Fits w 2 := hw.of_le (by omega)
  have hf4 : Fits w 3 := hw.of_le (by omega)
  have hf5 : Fits w 4 := hw.of_le (by omega)
  have hf6 : Fits w ((k :: c :: encode φ).length + 1 + n) := hw.of_le (by omega)
  have hf7 : Fits w (k - 3) := hw.of_le (by omega)
  have hm0 : (Data.init (k :: c :: encode φ) : Data 24).mem 0 = (k :: c :: encode φ).length :=
    rfl
  have hm1 : (Data.init (k :: c :: encode φ) : Data 24).mem 1 = k := rfl
  have hm2 : (Data.init (k :: c :: encode φ) : Data 24).mem 2 = c := rfl
  have hm3 : (Data.init (k :: c :: encode φ) : Data 24).mem 3 = n := rfl
  refine ⟨?run, ?state⟩
  case run =>
    ram_eval [ampSetup, ampSetupData, Data.init_regs, hm0, hm1, hm2, hm3, hf1, hf2, hf3, hf4, hf5,
      hf6, hf7]
  case state =>
    refine ⟨⟨by simp +decide [ampSetupData], by simp +decide [ampSetupData],
      by simp +decide [ampSetupData], by simp +decide [ampSetupData],
      by simp +decide [ampSetupData], ?_, ?_, fun _ _ => rfl⟩, by simp +decide [ampSetupData],
      by simp +decide [ampSetupData], by simp +decide [ampSetupData],
      by simp +decide [ampSetupData], by simp +decide [ampSetupData], holdsList_nil _ _,
      by simp, by simp +decide [ampSetupData]⟩
    · intro i
      change (Data.init (k :: c :: encode φ) : Data 24).mem (4 + i.val) = (encodeClauses φ)[i.val]
      rw [show 4 + i.val = (3 + i.val) + 1 by omega, Data.init_mem_succ]
      simp [encode, show 3 + i.val = (i.val + 1) + 1 + 1 by omega]
    · simp [length_encode]; omega

/-! ### The trials -/

/-- The state at the head of the trial loop: the frame of the trials, the counter digits `ds` at
`A + n`, `flag = 1` and `out = 0`. -/
private structure LoopState (φ : CNF (Fin n)) (C A : ℕ) (ds : List ℕ) (x : Data 24) : Prop where
  frame : Frame φ C A x.mem x
  bBase_eq : x.regs bBase = A + n
  bLen_eq : x.regs bLen = ds.length
  digits : HoldsList (A + n) ds x.mem
  binary : ∀ d ∈ ds, d ≤ 1
  flag_eq : x.regs flag = 1
  out_eq : x.regs out = 0

/-- The postcondition of the trial loop: the frame, and an output `0`, or `1` with a satisfying
assignment at `A`. -/
private def LoopPost (φ : CNF (Fin n)) (C A : ℕ) (y : Data 24) : Prop :=
  Frame φ C A y.mem y ∧ (y.regs out = 0 ∨ (y.regs out = 1 ∧ φ.eval (assignmentAt y.mem A n) = true))

/-- The trial loop from a counter of value `j` has the law `repeatTrial φ j`. Each trial costs
`trialCoreTime n E + 30` instructions, amortized: the decrements are paid for by the zero digits
of the counter. -/
private theorem ampLoop_law {φ : CNF (Fin n)} {C A w : ℕ} (hw : Fits w (A + 3 * n)) (hA : 1 ≤ A) :
    ∀ (j : ℕ) (ds : List ℕ) (x : Data 24), LoopState φ C A ds x → Nat.ofDigits 2 ds = j →
      Fits w (A + n + ds.length) →
      ExecRandLaw w ampLoop x (LoopPost φ C A)
        (j * (trialCoreTime n (encodeClauses φ).length + 30) + 9 * ds.count 0 + 30) (j * (4 * n))
        (fun y => decide (y.regs out = 1)) (repeatTrial φ j)
  | 0, ds, x, hx, hv, hfit => by
    have hz : ∀ d ∈ ds, d = 0 := (ofDigits_two_eq_zero_iff ds).mp hv
    have hc : (Cond.lt zero flag).Holds x := by
      simp [Cond.holds_lt, hx.frame.zero_eq, hx.flag_eq]
    obtain ⟨y₁, hy₁, -, hf₁, hm₁⟩ := decCounter_spec hx.frame.zero_eq hx.frame.one_eq hx.bLen_eq
      (by rw [hx.bBase_eq]; exact hx.digits) (by rw [hx.bBase_eq]; exact hfit)
    replace hf₁ : y₁.regs found = 0 := by rw [hf₁]; split_ifs; rfl
    have hz₁ : y₁.regs zero = 0 := (hy₁.regs_eq (by decide)).trans hx.frame.zero_eq
    have hbody : ExecWithin w ampBody x (y₁.set flag (y₁.regs zero)) (9 * decSteps ds + 4 + 2) :=
      hy₁.seq (ExecWithin.branch_pos (by simp [Cond.holds_eq, hf₁, hz₁]) ExecWithin.copy)
    have hcy : ¬(Cond.lt zero flag).Holds (y₁.set flag (y₁.regs zero)) := by
      simp +decide [Cond.holds_lt, hz₁]
    have hout : (y₁.set flag (y₁.regs zero)).regs out = 0 := by
      simp +decide [(hy₁.regs_eq (by decide)).trans hx.out_eq]
    have hpost : LoopPost φ C A (y₁.set flag (y₁.regs zero)) := by
      refine ⟨hx.frame.of_mem_lt ?_ ?_ ?_ ?_ ?_ ?_, Or.inl hout⟩
      · simp +decide [hy₁.regs_eq (i := zero) (by decide)]
      · simp +decide [hy₁.regs_eq (i := one) (by decide)]
      · simp +decide [hy₁.regs_eq (i := cBeg) (by decide)]
      · simp +decide [hy₁.regs_eq (i := aBase) (by decide)]
      · simp +decide [hy₁.regs_eq (i := nReg) (by decide)]
      · intro a ha; rw [Data.set_mem, hm₁ a (by rw [hx.bBase_eq]; omega)]
    have h := ExecRandLaw.of_execWithin (f := fun y => decide (y.regs out = 1))
      (ExecWithin.loop_iter hc hbody (ExecWithin.loop_exit hcy)) hpost
    have hsteps := decSteps_add_count_le ds
    refine (h.congr_law (by simp [hout, repeatTrial])).mono (fun _ h => h) (by omega) (by simp)
  | j + 1, ds, x, hx, hv, hfit => by
    have hnz : ¬∀ d ∈ ds, d = 0 := fun h => by
      rw [(ofDigits_two_eq_zero_iff ds).mpr h] at hv; omega
    have hc : (Cond.lt zero flag).Holds x := by
      simp [Cond.holds_lt, hx.frame.zero_eq, hx.flag_eq]
    obtain ⟨y₁, hy₁, hh₁, hf₁, hm₁⟩ := decCounter_spec hx.frame.zero_eq hx.frame.one_eq hx.bLen_eq
      (by rw [hx.bBase_eq]; exact hx.digits) (by rw [hx.bBase_eq]; exact hfit)
    replace hf₁ : y₁.regs found = 1 := by rw [hf₁]; split_ifs; rfl
    rw [hx.bBase_eq] at hh₁ hm₁
    have hv₁ : Nat.ofDigits 2 (decDigits ds) = j := by
      have := ofDigits_decDigits hx.binary (by omega)
      omega
    have hz₁ : y₁.regs zero = 0 := (hy₁.regs_eq (by decide)).trans hx.frame.zero_eq
    have hfr₁ : Frame φ C A y₁.mem y₁ := hx.frame.of_mem_lt (hy₁.regs_eq (by decide))
      (hy₁.regs_eq (by decide)) (hy₁.regs_eq (by decide)) (hy₁.regs_eq (by decide))
      (hy₁.regs_eq (by decide)) fun a ha => hm₁ a (by omega)
    have hb₁ : y₁.regs bBase = A + n := (hy₁.regs_eq (by decide)).trans hx.bBase_eq
    have hl₁ : y₁.regs bLen = ds.length := (hy₁.regs_eq (by decide)).trans hx.bLen_eq
    have hfl₁ : y₁.regs flag = 1 := (hy₁.regs_eq (by decide)).trans hx.flag_eq
    have hcf : ¬(Cond.eq found zero).Holds y₁ := by simp [Cond.holds_eq, hf₁, hz₁]
    -- one trial
    have hcore := (((trialCore_law (φ := φ) hw hA hfr₁).withPreserves (i := bBase)
      (by decide)).withPreserves (i := bLen) (by decide)).withPreserves (i := flag) (by decide)
    let Q : Data 24 → Prop := fun y => Frame φ C A y₁.mem y ∧ y.regs bBase = A + n ∧
      y.regs bLen = ds.length ∧
      y.regs out = (if φ.eval (assignmentAt y.mem A n) then 1 else 0) ∧
      y.regs flag = (if φ.eval (assignmentAt y.mem A n) then 0 else 1)
    have hrest := ExecRandLaw.seq_det_right (T₂ := 3)
      (c₂ := ram[ if out = one then [ flag ← zero ] else [ flag ← one ] ]) (Q := Q) hcore
      fun y ⟨⟨⟨⟨⟨hy, _⟩, hyo⟩, hyb⟩, hyl⟩, hyf⟩ => by
        by_cases he : φ.eval (assignmentAt y.mem A n) = true
        · simp only [he, ↓reduceIte] at hyo
          refine ⟨_, (ExecWithin.branch_pos (by simp [Cond.holds_eq, hyo, hy.one_eq])
            (ExecWithin.copy (B := .standard) (w := w) (d := flag) (s := zero) (x := y))).mono
            (by omega), ⟨hy.congr (by simp +decide) (by simp +decide) (by simp +decide)
              (by simp +decide) (by simp +decide) fun _ _ => rfl, ?_, ?_, ?_, ?_⟩, rfl⟩
          · simp +decide [hyb, hb₁]
          · simp +decide [hyl, hl₁]
          · simpa +decide [he] using hyo
          · simp +decide [he, hy.zero_eq]
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at hyo
          refine ⟨_, (ExecWithin.branch_neg (by simp [Cond.holds_eq, hyo, hy.one_eq])
            (ExecWithin.copy (B := .standard) (w := w) (d := flag) (s := one) (x := y))).mono
            le_rfl, ⟨hy.congr (by simp +decide) (by simp +decide) (by simp +decide)
              (by simp +decide) (by simp +decide) fun _ _ => rfl, ?_, ?_, ?_, ?_⟩, rfl⟩
          · simp +decide [hyb, hb₁]
          · simp +decide [hyl, hl₁]
          · simpa +decide [he] using hyo
          · simp +decide [he, hy.one_eq]
    have hbody : ExecRandLaw w ampBody x Q
        (9 * decSteps ds + 4 + (trialCoreTime n (encodeClauses φ).length + 3 + 2)) (4 * n)
        (fun y => assignmentAt y.mem A n) (trial φ) :=
      ExecRandLaw.seq_det hy₁ (ExecRandLaw.branch_neg hcf hrest)
    have h := ExecRandLaw.loop_iter
      (κ := fun σ => if φ.eval σ then PMF.pure true else repeatTrial φ j)
      (T₂ := j * (trialCoreTime n (encodeClauses φ).length + 30) +
        9 * (decDigits ds).count 0 + 30) (R₂ := j * (4 * n))
      hc hbody fun y ⟨hy, hyb, hyl, hyo, hyf⟩ => by
        have hmy : ∀ a, A + n ≤ a → y.mem a = y₁.mem a := hy.rest
        have hdy : HoldsList (A + n) (decDigits ds) y.mem :=
          hh₁.frame fun a ha _ => hmy a ha
        by_cases he : φ.eval (assignmentAt y.mem A n) = true
        · simp only [he, ↓reduceIte] at hyo hyf
          have hcy : ¬(Cond.lt zero flag).Holds y := by simp [Cond.holds_lt, hyf]
          have h := ExecRandLaw.loop_exit (w := w) (body := ampBody)
            (f := fun y => decide (y.regs out = 1)) hcy (P := LoopPost φ C A)
            ⟨hy.self, Or.inr ⟨hyo, he⟩⟩
          simp only [he, ↓reduceIte]
          refine (h.congr_law (by simp [hyo])).mono (fun _ h => h) (by omega) (Nat.zero_le _)
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at hyo hyf
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          exact ampLoop_law hw hA j (decDigits ds) y
            ⟨hy.self, hyb, by rw [hyl, length_decDigits], hdy, decDigits_digit_le hx.binary, hyf,
              hyo⟩ hv₁ (by rw [length_decDigits]; exact hfit)
    have hsteps := decSteps_add_count_le ds
    refine (h.congr_law rfl).mono (fun _ h => h) ?_ ?_
    · simp only [Nat.add_mul, Nat.one_mul]; omega
    · simp only [Nat.add_mul, Nat.one_mul]; omega

/-! ### The algorithm -/

/-- **Schöning's algorithm on the randomized word RAM.** On the input `k :: c :: encode φ` of
length `L`, with `3 ≤ k` and at any word size `w` with
`L + 6 n + 4 k + 2 c + counterLen k n c + 2 < 2 ^ w`, the program

* halts on every path within `ampTime k n c L` instructions;
* makes at most `R (4 n)` `rand` calls, where `R = schoeningTrials k n c`;
* outputs `0` or `1`, and outputs `1` only with a satisfying assignment of `φ` stored at address
  `L + 1`;
* outputs `1` with exactly the law `repeatTrial φ R` of up to `R` independent trials. -/
theorem ampProgram_spec (k c : ℕ) (hk : 3 ≤ k) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((k :: c :: encode φ).length + 6 * n + 4 * k + 2 * c + counterLen k n c + 2)) :
    RandHaltsWithin w ampProgram (.init (k :: c :: encode φ))
      (ampTime k n c (k :: c :: encode φ).length) ∧
    RandCallsBounded w ampProgram (.init (k :: c :: encode φ))
      (ampTime k n c (k :: c :: encode φ).length) (schoeningTrials k n c * (4 * n)) ∧
    (∀ cfg ∈ (runRand w ampProgram (ampTime k n c (k :: c :: encode φ).length)
        (.running (.init (k :: c :: encode φ)))).support,
      ∃ v d, cfg = .halted v d ∧
        (v = 0 ∨ (v = 1 ∧
          φ.eval (assignmentAt d.mem ((k :: c :: encode φ).length + 1) n) = true))) ∧
    (evalRand w ampProgram (ampTime k n c (k :: c :: encode φ).length)
      (.init (k :: c :: encode φ))).map cfgSuccess = repeatTrial φ (schoeningTrials k n c) := by
  set L := (k :: c :: encode φ).length with hL
  have hE : (encodeClauses φ).length ≤ L := by
    simp only [hL, List.length_cons, length_encode]; omega
  obtain ⟨h₀, hS₀⟩ := ampSetup_exec k c φ (hw.of_le (by omega))
  rw [← hL] at hS₀
  obtain ⟨y₁, hy₁, hS₁⟩ := countSetup_exec hk hS₀ (hw.of_le (by omega)) (hw.of_le (by omega))
  have hfl : ExecWithin w (ram[ flag ← one ] : Code .standard 24) y₁ (y₁.set flag 1) 1 := by
    ram_eval [hS₁.frame.one_eq]
  have hlen := length_counterDigits_le hk n c
  have hstate : LoopState φ 4 (L + 1) (counterDigits k n c) (y₁.set flag 1) :=
    { frame := hS₁.frame.of_mem_lt (by simp +decide) (by simp +decide) (by simp +decide)
        (by simp +decide) (by simp +decide) fun _ _ => rfl
      bBase_eq := by simp +decide [hS₁.bBase_eq]
      bLen_eq := by simp +decide [hS₁.bLen_eq]
      digits := hS₁.digits
      binary := hS₁.binary
      flag_eq := by simp
      out_eq := by simp +decide [hS₁.out_eq] }
  have hloop := ampLoop_law (φ := φ) (C := 4) (A := L + 1) (hw.of_le (by omega)) (by omega)
    (schoeningTrials k n c) (counterDigits k n c) (y₁.set flag 1) hstate
    (ofDigits_counterDigits hk n c) (hw.of_le (by omega))
  have hall := ExecRandLaw.seq_det h₀ (ExecRandLaw.seq_det hy₁ (ExecRandLaw.seq_det hfl hloop))
  have hcount := List.count_le_length (a := 0) (l := counterDigits k n c)
  obtain ⟨hhalt, hcalls, hpost, hlaw⟩ := hall.program out (T' := ampTime k n c L)
    (by
      simp only [ampTime, trialCoreTime]
      have := Nat.mul_le_mul_left (schoeningTrials k n c)
        (show 36 * n * (encodeClauses φ).length + 66 * n + 12 * (encodeClauses φ).length + 13 + 30
          ≤ 36 * n * L + 66 * n + 12 * L + 43 by
          have := Nat.mul_le_mul_left (36 * n) hE
          omega)
      omega)
    cfgSuccess fun _ _ => rfl
  refine ⟨hhalt, hcalls, fun cfg hcfg => ?_, hlaw⟩
  obtain ⟨d, rfl, -, hd⟩ := hpost cfg hcfg
  exact ⟨_, d, rfl, hd⟩

/-- **Failure probability.** The program outputs something other than `1` with probability exactly
`(1 - p) ^ R`, where `R = schoeningTrials k n c` and `p = succeedProb φ (trial φ)` is the success
probability of one trial. -/
theorem ampProgram_failure_eq (k c : ℕ) (hk : 3 ≤ k) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((k :: c :: encode φ).length + 6 * n + 4 * k + 2 * c + counterLen k n c + 2)) :
    ((evalRand w ampProgram (ampTime k n c (k :: c :: encode φ).length)
      (.init (k :: c :: encode φ))).map cfgSuccess false).toReal =
      (1 - succeedProb φ (trial φ)) ^ schoeningTrials k n c := by
  rw [(ampProgram_spec k c hk φ hw).2.2.2, repeatTrial_false_toReal]

/-- **Schöning's algorithm succeeds with high probability.** On a satisfiable formula whose
clauses have at most `k ≥ 3` literals, the program outputs `1` except with probability at most
`e ^ (-c)`. -/
theorem ampProgram_failure_le_exp {k c : ℕ} (hk : 3 ≤ k) {φ : CNF (Fin n)} (hφ : φ.Satisfiable)
    (hlen : ∀ cl ∈ φ, cl.length ≤ k) {w : ℕ}
    (hw : Fits w ((k :: c :: encode φ).length + 6 * n + 4 * k + 2 * c + counterLen k n c + 2)) :
    ((evalRand w ampProgram (ampTime k n c (k :: c :: encode φ).length)
      (.init (k :: c :: encode φ))).map cfgSuccess false).toReal ≤ Real.exp (-c) := by
  rw [ampProgram_failure_eq k c hk φ hw]
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
