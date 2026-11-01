/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.WordRAM.PPZ.Round
public import Complexity.Algorithms.WordRAM.Schoening.Amplify
import Complexity.Probability.PMF.Event

/-!
# The PPZ algorithm on the randomized word RAM

`Cslib.Algorithms.WordRAM.PPZ.ampProgram` is the PPZ k-SAT algorithm [Paturi, Pudlák, Zane][PPZ1997]
with confidence `c`, as a program of the randomized word RAM. On the input `k :: c :: encode φ` it
computes the number of rounds `R = ppzRounds k n c = 2 ^ ⌈(k - 1) n / k⌉ c` in a multiword counter
(`Cslib.Algorithms.WordRAM.Schoening.mulAdd`), then runs up to `R` independent rounds
(`Cslib.Algorithms.WordRAM.PPZ.roundCore`), stopping at the first round whose assignment satisfies
the formula. It halts with output `1`, leaving a satisfying assignment in memory, or with output
`0` when every round failed.

`Cslib.Algorithms.WordRAM.PPZ.ampProgram_spec` proves, at every word size `w` with
`L + 2 n + k n + k + 2 c + ppzCounterLen k n c + 2 < 2 ^ w`, where `L` is the input length and
`ppzCounterLen k n c`, which is `⌈(k - 1) n / k⌉ + 1` plus the number of binary digits of `c`,
bounds the number of digits of `R`:

* the program halts on every path within `ampTime k n c L` instructions, which is
  `R (n (28 L + 40) + 12 L + 41)` plus a setup cost linear in the counter length;
* it makes at most `2 n R` `rand` calls;
* an output `1` always comes with a satisfying assignment, so the program never errs on
  unsatisfiable formulas;
* the output is `1` with exactly the law of `R` independent rounds
  (`Cslib.Algorithms.WordRAM.PPZ.repeatRound`), so it is `0` with probability exactly `(1 - p) ^ R`,
  where `p` is the probability that one round finds a satisfying assignment
  (`Cslib.Algorithms.WordRAM.PPZ.ampProgram_failure_eq`).

With the PPZ bound `p ≥ 2 ^ (-(1 - 1 / k) n)` for one round
(`Cslib.Complexity.PPZ.round_success_of_satisfiable`), the program fails on a satisfiable formula
with clauses of at most `k ≥ 1` literals with probability at most `e ^ (-c)`
(`Cslib.Algorithms.WordRAM.PPZ.ampProgram_failure_le_exp`), and it runs in time
`O((n + L) ^ 2 2 ^ ((1 - 1 / k) n) (c + 1))` (`Cslib.Algorithms.WordRAM.PPZ.ampTime_le`). Rounding
the exponent `(1 - 1 / k) n` up to an integer costs at most a factor `2` in the number of rounds,
and makes the counter's setup a run of zero digits, a single one digit, and one multiply-add by `c`.

The loop of rounds and the counter's setup take their round body and exponent as parameters:
`Cslib.Algorithms.WordRAM.PPZ.ampLoopWith core` runs rounds with any round body `core` for an
oracle `O` (`Cslib.Algorithms.WordRAM.PPZ.IsRoundCore`), with the law of
`Cslib.Algorithms.WordRAM.PPZ.repeatRoundWith O` (`Cslib.Algorithms.WordRAM.PPZ.ampLoopWith_law`),
and `Cslib.Algorithms.WordRAM.PPZ.countSetup_spec` computes the digits of any `2 ^ e c`. The PPSZ
algorithm (`Cslib.Algorithms.WordRAM.PPSZ.ampProgram`) uses both.

## Main definitions

* `Cslib.Algorithms.WordRAM.PPZ.succeeds`: whether a round's assignment satisfies the formula.
* `Cslib.Algorithms.WordRAM.PPZ.repeatRoundWith`, `Cslib.Algorithms.WordRAM.PPZ.repeatRound`: the
  law of the output of up to `R` independent rounds.
* `Cslib.Algorithms.WordRAM.PPZ.IsRoundCore`: the contract of a round body in the loop.
* `Cslib.Algorithms.WordRAM.PPZ.ampLoopWith`: the loop of rounds with a round body.
* `Cslib.Algorithms.WordRAM.PPZ.countDigits`: the digits of `2 ^ e c` as the setup computes them.
* `Cslib.Algorithms.WordRAM.PPZ.ppzRounds`: the number of rounds.
* `Cslib.Algorithms.WordRAM.PPZ.ampCode`, `Cslib.Algorithms.WordRAM.PPZ.ampProgram`: the amplified
  algorithm, structured and compiled.
* `Cslib.Algorithms.WordRAM.PPZ.ampTime`: its instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.PPZ.repeatRoundWith_false_toReal`: `R` rounds all fail with
  probability `(1 - p) ^ R`.
* `Cslib.Algorithms.WordRAM.PPZ.repeatRoundWith_false_le_exp`: amplification, from a lower bound
  on `p`.
* `Cslib.Algorithms.WordRAM.PPZ.sum_le_roundSuccessProbWith`: `p` is at least the probability of
  outputting a satisfying assignment.
* `Cslib.Algorithms.WordRAM.PPZ.roundSuccessProb_ge`: the PPZ bound on `p`.
* `Cslib.Algorithms.WordRAM.PPZ.ampLoopWith_law`: the law of the loop of rounds.
* `Cslib.Algorithms.WordRAM.PPZ.countSetup_spec`: computing the number of rounds.
* `Cslib.Algorithms.WordRAM.PPZ.ampProgram_spec`: halting, time and `rand` bounds, no false
  positives, and the exact law of the output.
* `Cslib.Algorithms.WordRAM.PPZ.ampProgram_failure_le_exp`: on a satisfiable k-CNF the program fails
  with probability at most `e ^ (-c)`.
* `Cslib.Algorithms.WordRAM.PPZ.ampTime_le`: the time bound.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability Coding Lemma*][PPZ1997]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.PPZ

open Cslib.WordRAM Cslib.WordRAM.Block Cslib.Logic.PL Cslib.Complexity.PPZ
open Cslib.Algorithms.WordRAM.Schoening (encodeClauses encode assignmentAt length_encode
  decDigits decSteps mulAddDigits)
open Reg

variable {n : ℕ}

/-! ### Repeated rounds -/

/-- Whether the partial assignment `τ` satisfies `φ`, reading unset variables as false. A round
leaves a total assignment, on which this is satisfaction. -/
def succeeds (φ : CNF (Fin n)) (τ : Fin n → Option Bool) : Bool :=
  φ.eval fun v => τ v == some true

/-- The probability that one round with the oracle `O` finds a satisfying assignment of `φ`. -/
noncomputable def roundSuccessProbWith (O : (Fin n → Option Bool) → Fin n → Option Bool)
    (φ : CNF (Fin n)) : ℝ :=
  ((roundWith O).toOuterMeasure {τ | succeeds φ τ = true}).toReal

/-- The probability that one round of PPZ finds a satisfying assignment. -/
noncomputable def roundSuccessProb (φ : CNF (Fin n)) : ℝ := roundSuccessProbWith (forced φ) φ

/-- The output of up to `R` independent rounds with the oracle `O`, stopping at the first that
finds a satisfying assignment of `φ`: `true` if some round found one. -/
noncomputable def repeatRoundWith (O : (Fin n → Option Bool) → Fin n → Option Bool)
    (φ : CNF (Fin n)) : ℕ → PMF Bool
  | 0 => PMF.pure false
  | R + 1 => (roundWith O).bind fun τ =>
    if succeeds φ τ then PMF.pure true else repeatRoundWith O φ R

/-- The output of up to `R` independent rounds of PPZ, stopping at the first success: `true` if
some round found a satisfying assignment. -/
noncomputable def repeatRound (φ : CNF (Fin n)) : ℕ → PMF Bool := repeatRoundWith (forced φ) φ

/-- **All `R` rounds with the oracle `O` fail** with probability `(1 - p) ^ R`, where `p` is the
success probability of one round. -/
theorem repeatRoundWith_false_toReal (O : (Fin n → Option Bool) → Fin n → Option Bool)
    (φ : CNF (Fin n)) (R : ℕ) :
    (repeatRoundWith O φ R false).toReal = (1 - roundSuccessProbWith O φ) ^ R := by
  induction R with
  | zero => simp [repeatRoundWith]
  | succ R ih =>
    have h := Probability.PMF.toOuterMeasure_bind_toReal (roundWith O)
      (fun τ => if succeeds φ τ then PMF.pure true else repeatRoundWith O φ R) {false}
    simp only [PMF.toOuterMeasure_apply_singleton] at h
    have hsum : ∑ τ, ((roundWith O) τ).toReal * (if succeeds φ τ = true then 0 else 1) =
        1 - roundSuccessProbWith O φ := by
      have hfail := Probability.PMF.toOuterMeasure_toReal_add_compl (roundWith O)
        {τ | succeeds φ τ = true}
      have hcongr : ∑ τ, ((roundWith O) τ).toReal * (if succeeds φ τ = true then 0 else 1) =
          ((roundWith O).toOuterMeasure {τ | succeeds φ τ = true}ᶜ).toReal := by
        rw [Probability.PMF.toOuterMeasure_apply_toReal]
        exact Finset.sum_congr rfl fun τ _ => by by_cases hτ : succeeds φ τ = true <;> simp [hτ]
      rw [hcongr, roundSuccessProbWith]
      linarith
    rw [repeatRoundWith, h, pow_succ]
    calc ∑ τ, ((roundWith O) τ).toReal *
          ((if succeeds φ τ = true then PMF.pure true else repeatRoundWith O φ R) false).toReal
        = ∑ τ, ((roundWith O) τ).toReal * (if succeeds φ τ = true then 0 else 1) *
            (1 - roundSuccessProbWith O φ) ^ R := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          by_cases hτ : succeeds φ τ = true
          · simp only [hτ, ↓reduceIte, PMF.pure_apply, Bool.false_eq_true, ENNReal.toReal_zero,
              mul_zero, zero_mul]
          · simp only [hτ, Bool.false_eq_true, ↓reduceIte, ih, mul_one]
      _ = (1 - roundSuccessProbWith O φ) ^ R * (1 - roundSuccessProbWith O φ) := by
          rw [← Finset.sum_mul, hsum, mul_comm]

/-- **All `R` rounds fail** with probability `(1 - p) ^ R`, where `p` is the success probability of
one round. -/
theorem repeatRound_false_toReal (φ : CNF (Fin n)) (R : ℕ) :
    (repeatRound φ R false).toReal = (1 - roundSuccessProb φ) ^ R :=
  repeatRoundWith_false_toReal (forced φ) φ R

/-- The success probability of a round is at most `1`. -/
theorem roundSuccessProbWith_le_one (O : (Fin n → Option Bool) → Fin n → Option Bool)
    (φ : CNF (Fin n)) : roundSuccessProbWith O φ ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact Probability.PMF.toOuterMeasure_le_one _ _)

/-- A round's success test on a total assignment is satisfaction. -/
theorem succeeds_some (φ : CNF (Fin n)) (σ : Fin n → Bool) :
    succeeds φ (fun x => some (σ x)) = φ.eval σ := by
  unfold succeeds
  congr 1

/-- The success probability of a round is at least the probability that it outputs a satisfying
assignment, summed over the satisfying assignments. -/
theorem sum_le_roundSuccessProbWith (O : (Fin n → Option Bool) → Fin n → Option Bool)
    (φ : CNF (Fin n)) :
    ∑ σ ∈ Finset.univ.filter (fun σ : Fin n → Bool => φ.eval σ = true),
      ((roundWith O) fun x => some (σ x)).toReal ≤ roundSuccessProbWith O φ := by
  classical
  rw [roundSuccessProbWith, Probability.PMF.toOuterMeasure_apply_toReal]
  have hinj : Set.InjOn (fun σ : Fin n → Bool => fun x => some (σ x))
      ↑(Finset.univ.filter fun σ : Fin n → Bool => φ.eval σ = true) :=
    fun σ _ σ' _ h => funext fun x => Option.some_injective _ (congrFun h x)
  rw [← Finset.sum_image (f := fun τ => ((roundWith O) τ).toReal) hinj]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun τ hτ => ?_))
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun τ _ _ => ?_)
  · obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hτ
    rw [Finset.mem_filter] at hσ
    rw [ite_eq_left (by rw [Set.mem_ofPred_eq, succeeds_some]; exact hσ.2)]
  · split_ifs
    · exact ENNReal.toReal_nonneg
    · exact le_rfl

/-- **Amplification**: if one round succeeds with probability at least `q > 0` and `c ≤ R q`,
then `R` rounds all fail with probability at most `e ^ (-c)`. -/
theorem repeatRoundWith_false_le_exp {O : (Fin n → Option Bool) → Fin n → Option Bool}
    {φ : CNF (Fin n)} {q c : ℝ} {R : ℕ} (hq : q ≤ roundSuccessProbWith O φ) (hR : c ≤ R * q) :
    (repeatRoundWith O φ R false).toReal ≤ Real.exp (-c) := by
  rw [repeatRoundWith_false_toReal]
  exact Schoening.one_sub_pow_le_exp (roundSuccessProbWith_le_one O φ)
    (hR.trans (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg R)))

/-- **The PPZ bound for one round** [Paturi, Pudlák, Zane][PPZ1997]: on a satisfiable formula with
clauses of at most `k ≥ 1` literals, one round succeeds with probability at least
`2 ^ (-(1 - 1 / k) n)` (`Cslib.Complexity.PPZ.round_success_of_satisfiable`). -/
theorem roundSuccessProb_ge {k : ℕ} (hk : 1 ≤ k) {φ : CNF (Fin n)} (hsat : φ.Satisfiable)
    (hlen : ∀ c ∈ φ, c.length ≤ k) :
    (2 : ℝ) ^ (-((1 - 1 / (k : ℝ)) * n)) ≤ roundSuccessProb φ := by
  refine (round_success_of_satisfiable hk hsat hlen).trans
    (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _) (PMF.toOuterMeasure_mono _ ?_))
  rintro τ ⟨⟨σ, hσ, rfl⟩, -⟩
  change φ.eval (fun v => some (σ v) == some true) = true
  convert hσ using 2
  funext v
  cases σ v <;> rfl

/-- The success test of a stored assignment is the satisfaction test of the stored words. -/
theorem succeeds_partialAssignmentAt (φ : CNF (Fin n)) (mem : ℕ → ℕ) (base : ℕ) :
    succeeds φ (partialAssignmentAt mem base n) = φ.eval (assignmentAt mem base n) := by
  unfold succeeds
  congr 1
  funext v
  simp only [partialAssignmentAt, assignmentAt]
  rcases h : mem (base + v) with _ | _ | m <;> rfl

/-! ### Registers -/

namespace Reg

/-- Base address of the counter digits (`embed Cslib.Algorithms.WordRAM.Schoening.Reg.bBase`). -/
abbrev bBase : Fin 32 := 29
/-- Number of counter digits (`embed Cslib.Algorithms.WordRAM.Schoening.Reg.bLen`). -/
abbrev bLen : Fin 32 := 30
/-- Whether the amplified algorithm runs another round. -/
abbrev flag : Fin 32 := 31
/-- Multiplier of a multiply-add (`embed Cslib.Algorithms.WordRAM.Schoening.Reg.mulr`); shares
register `9` with `lend`. -/
abbrev mulr : Fin 32 := 9
/-- Carry of a multiply-add (`embed Cslib.Algorithms.WordRAM.Schoening.Reg.carry`); shares
register `10` with `lit`. -/
abbrev carry : Fin 32 := 10
/-- `k`, during the setup; shares register `6` with `ptr`. -/
abbrev kReg : Fin 32 := 6
/-- `c`, during the setup; shares register `7` with `len`. -/
abbrev cReg : Fin 32 := 7
/-- The exponent `⌈(k - 1) n / k⌉`, during the setup; shares register `8` with `lptr`. -/
abbrev eReg : Fin 32 := 8

end Reg

/-! ### The counter routines in the register file of PPZ -/

/-- **Decrement**, renamed: Schöning's `Cslib.Algorithms.WordRAM.Schoening.decCounter_spec`. -/
theorem decCounter_rename_spec {w : ℕ} {ds : List ℕ} {x : Data 32} (hz : x.regs zero = 0)
    (hone : x.regs one = 1) (hl : x.regs bLen = ds.length)
    (hh : HoldsList (x.regs bBase) ds x.mem) (hfit : Fits w (x.regs bBase + ds.length)) :
    ∃ y, ExecWithin w (Schoening.decCounter.rename embed) x y (9 * decSteps ds + 4) ∧
      HoldsList (x.regs bBase) (decDigits ds) y.mem ∧
      y.regs sFound = (if ∀ d ∈ ds, d = 0 then 0 else 1) ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  obtain ⟨y, hy, hh', hf, hm⟩ := Schoening.decCounter_spec (w := w) (x := x.comap embed) hz hone
    hl hh hfit
  refine ⟨y.extend embed x, ExecWithin.rename embed_injective hy, hh', ?_, hm⟩
  rw [← hf]
  exact embed_injective.extend_apply y.regs x.regs Schoening.Reg.found

/-- **Multiply-add**, renamed: Schöning's `Cslib.Algorithms.WordRAM.Schoening.mulAdd_spec`. -/
theorem mulAdd_rename_spec {w a cy Bd : ℕ} {ds : List ℕ} {x : Data 32} (hz : x.regs zero = 0)
    (hone : x.regs one = 1) (ha : x.regs mulr = a) (hc : x.regs carry = cy)
    (hl : x.regs bLen = ds.length) (hh : HoldsList (x.regs bBase) ds x.mem)
    (hds : ∀ d ∈ ds, d ≤ 1) (haB : a ≤ Bd) (hcB : cy ≤ Bd) (hf : Fits w (2 * Bd))
    (hfit : Fits w (x.regs bBase + (mulAddDigits a cy ds).length)) :
    ∃ y, ExecWithin w (Schoening.mulAdd.rename embed) x y
        (10 * (mulAddDigits a cy ds).length + 5) ∧
      HoldsList (x.regs bBase) (mulAddDigits a cy ds) y.mem ∧
      y.regs bLen = (mulAddDigits a cy ds).length ∧
      ∀ b, b < x.regs bBase → y.mem b = x.mem b := by
  obtain ⟨y, hy, hh', hl', hm⟩ := Schoening.mulAdd_spec (w := w) (x := x.comap embed) hz hone ha
    hc hl hh hds haB hcB hf hfit
  refine ⟨y.extend embed x, ExecWithin.rename embed_injective hy, hh', ?_, hm⟩
  rw [← hl']
  exact embed_injective.extend_apply y.regs x.regs Schoening.Reg.bLen

/-- A deterministic run of frame-preserving code keeps the frame if it keeps the memory below
`Tb`, with the memory after the arrays taken as it is. -/
theorem RoundFrame.of_exec_mem_lt {φ : CNF (Fin n)} {C Tb : ℕ} {M : ℕ → ℕ} {c : Code .standard 32}
    {x y : Data 32} {w T : ℕ} (h : RoundFrame φ C Tb M x) (hc : PreservesRound c)
    (he : ExecWithin w c x y T) (hmem : ∀ a < Tb, y.mem a = x.mem a) :
    RoundFrame φ C Tb y.mem y where
  zero_eq := (he.regs_eq hc.1).trans h.zero_eq
  one_eq := (he.regs_eq hc.2.1).trans h.one_eq
  two_eq := (he.regs_eq hc.2.2.1).trans h.two_eq
  cBeg_eq := (he.regs_eq hc.2.2.2.1).trans h.cBeg_eq
  cEnd_eq := (he.regs_eq hc.2.2.2.2.1).trans h.cEnd_eq
  tBase_eq := (he.regs_eq hc.2.2.2.2.2.1).trans h.tBase_eq
  nReg_eq := (he.regs_eq hc.2.2.2.2.2.2.1).trans h.nReg_eq
  pBase_eq := (he.regs_eq hc.2.2.2.2.2.2.2).trans h.pBase_eq
  clauses := h.clauses.frame fun a _ ha' => hmem a (h.span ▸ ha')
  span := h.span
  rest _ _ := rfl

/-! ### The rounds -/

/-- **A round body for the oracle `O`** within `Tc` instructions, on rounds whose memory holds the
words `S` just after the order array: from any frame of a round whose memory `M` holds `S` at
`Tb + 2 n`, `core` has the law of `Cslib.Complexity.PPZ.roundWith O` within `Tc` instructions and
`2 n` `rand` calls, keeps the frame and leaves every variable set. It writes none of the counter
registers. -/
structure IsRoundCore (w : ℕ) (φ : CNF (Fin n)) (C Tb : ℕ) (S : List ℕ)
    (O : (Fin n → Option Bool) → Fin n → Option Bool) (core : Code .standard 32) (Tc : ℕ) :
    Prop where
  preserves_bBase : core.Preserves bBase
  preserves_bLen : core.Preserves bLen
  preserves_flag : core.Preserves flag
  law : ∀ (M : ℕ → ℕ) (x : Data 32), RoundFrame φ C Tb M x → HoldsList (Tb + 2 * n) S M →
    ExecRandLaw w core x (fun y => RoundFrame φ C Tb M y ∧ ∀ v < n, y.mem (Tb + v) ≤ 1) Tc
      (2 * n) (fun y => partialAssignmentAt y.mem Tb n) (roundWith O)

/-- **The body of a round of PPZ is a round body** for `Cslib.Complexity.PPZ.forced φ`, with no
words after the order array. -/
theorem roundCore_isRoundCore {φ : CNF (Fin n)} {C Tb w : ℕ} (hw : Fits w (Tb + 2 * n))
    (hT : 1 ≤ Tb) :
    IsRoundCore w φ C Tb [] (forced φ) roundCore (roundCoreTime n (encodeClauses φ).length) where
  preserves_bBase := by decide
  preserves_bLen := by decide
  preserves_flag := by decide
  law _ _ hx _ := roundCore_law hw hT hx

/-- Decrement the counter; stop if it was zero, and otherwise run one round with the round body
`core` and stop after a success. -/
def ampBodyWith (core : Code .standard 32) : Code .standard 32 := ram[
  ⟪Schoening.decCounter.rename embed⟫;
  if sFound = zero then [ flag ← zero ]
  else [ ⟪core⟫; ⟪roundCheck⟫; if out = one then [ flag ← zero ] else [ flag ← one ] ] ]

/-- Run rounds with the round body `core` while `flag > 0`. -/
def ampLoopWith (core : Code .standard 32) : Code .standard 32 :=
  .loop (.lt zero flag) (ampBodyWith core)

/-- Decrement the counter; stop if it was zero, and otherwise run one round of PPZ and stop after a
success. -/
def ampBody : Code .standard 32 := ampBodyWith roundCore

/-- Run rounds of PPZ while `flag > 0`. -/
def ampLoop : Code .standard 32 := ampLoopWith roundCore

/-- The instruction bound of one round of the amplified algorithm, amortizing the decrements. -/
def ampRoundTime (n E : ℕ) : ℕ := roundCoreTime n E + 12 * E + 35

/-- The state at the head of the round loop: the frame of the rounds, the words `S` the rounds read
at `Tb + 2 n`, the counter digits `ds` just after them, `flag = 1` and `out = 0`. -/
structure AmpState (φ : CNF (Fin n)) (C Tb : ℕ) (S ds : List ℕ) (x : Data 32) : Prop where
  frame : RoundFrame φ C Tb x.mem x
  params : HoldsList (Tb + 2 * n) S x.mem
  bBase_eq : x.regs bBase = Tb + 2 * n + S.length
  bLen_eq : x.regs bLen = ds.length
  digits : HoldsList (Tb + 2 * n + S.length) ds x.mem
  binary : ∀ d ∈ ds, d ≤ 1
  flag_eq : x.regs flag = 1
  out_eq : x.regs out = 0

/-- The postcondition of the round loop: the frame, and an output `0`, or `1` with a satisfying
assignment at `Tb`. -/
def AmpPost (φ : CNF (Fin n)) (C Tb : ℕ) (y : Data 32) : Prop :=
  RoundFrame φ C Tb y.mem y ∧
    (y.regs out = 0 ∨ (y.regs out = 1 ∧ φ.eval (assignmentAt y.mem Tb n) = true))

/-- **The round loop with a round body** for the oracle `O`, from a counter of value `j`, has the
law `repeatRoundWith O φ j`. Each round costs `Tc + 12 E + 35` instructions, amortized: the
decrements are paid for by the zero digits of the counter. -/
theorem ampLoopWith_law {φ : CNF (Fin n)} {C Tb w Tc : ℕ} {S : List ℕ}
    {O : (Fin n → Option Bool) → Fin n → Option Bool} {core : Code .standard 32}
    (hcore : IsRoundCore w φ C Tb S O core Tc) (hw : Fits w (Tb + 2 * n)) (hT : 1 ≤ Tb) :
    ∀ (j : ℕ) (ds : List ℕ) (x : Data 32), AmpState φ C Tb S ds x → Nat.ofDigits 2 ds = j →
      Fits w (Tb + 2 * n + S.length + ds.length) →
      ExecRandLaw w (ampLoopWith core) x (AmpPost φ C Tb)
        (j * (Tc + 12 * (encodeClauses φ).length + 35) + 9 * ds.count 0 + 30) (j * (2 * n))
        (fun y => decide (y.regs out = 1)) (repeatRoundWith O φ j)
  | 0, ds, x, hx, hv, hfit => by
    have hz : ∀ d ∈ ds, d = 0 := (Schoening.ofDigits_two_eq_zero_iff ds).mp hv
    have hc : (Cond.lt zero flag).Holds x := by
      simp [Cond.holds_lt, hx.frame.zero_eq, hx.flag_eq]
    obtain ⟨y₁, hy₁, -, hf₁, hm₁⟩ := decCounter_rename_spec hx.frame.zero_eq hx.frame.one_eq
      hx.bLen_eq (by rw [hx.bBase_eq]; exact hx.digits) (by rw [hx.bBase_eq]; exact hfit)
    replace hf₁ : y₁.regs sFound = 0 := by rw [hf₁]; split_ifs; rfl
    have hz₁ : y₁.regs zero = 0 := (hy₁.regs_eq (by decide)).trans hx.frame.zero_eq
    have hcp := ExecWithin.copy (B := .standard) (w := w) (d := flag) (s := zero) (x := y₁)
    have hbody : ExecWithin w (ampBodyWith core) x (y₁.set flag (y₁.regs zero))
        (9 * decSteps ds + 4 + 2) :=
      hy₁.seq (ExecWithin.branch_pos (by simp [Cond.holds_eq, hf₁, hz₁]) hcp)
    have hcy : ¬(Cond.lt zero flag).Holds (y₁.set flag (y₁.regs zero)) := by
      simp +decide [Cond.holds_lt, hz₁]
    have hout : (y₁.set flag (y₁.regs zero)).regs out = 0 := by
      simp +decide [(hy₁.regs_eq (by decide)).trans hx.out_eq]
    have hpost : AmpPost φ C Tb (y₁.set flag (y₁.regs zero)) :=
      ⟨hx.frame.of_exec_mem_lt (c := ram[ ⟪Schoening.decCounter.rename embed⟫; flag ← zero ])
        (by decide) (hy₁.seq hcp) fun a ha => by
          rw [Data.set_mem, hm₁ a (by rw [hx.bBase_eq]; omega)], Or.inl hout⟩
    have h := ExecRandLaw.of_execWithin (f := fun y => decide (y.regs out = 1))
      (ExecWithin.loop_iter hc hbody (ExecWithin.loop_exit hcy)) hpost
    have hsteps := Schoening.decSteps_add_count_le ds
    refine (h.congr_law (by simp [hout, repeatRoundWith])).mono (fun _ h => h) (by omega)
      (by simp)
  | j + 1, ds, x, hx, hv, hfit => by
    have hnz : ¬∀ d ∈ ds, d = 0 := fun h => by
      rw [(Schoening.ofDigits_two_eq_zero_iff ds).mpr h] at hv; omega
    have hc : (Cond.lt zero flag).Holds x := by
      simp [Cond.holds_lt, hx.frame.zero_eq, hx.flag_eq]
    obtain ⟨y₁, hy₁, hh₁, hf₁, hm₁⟩ := decCounter_rename_spec hx.frame.zero_eq hx.frame.one_eq
      hx.bLen_eq (by rw [hx.bBase_eq]; exact hx.digits) (by rw [hx.bBase_eq]; exact hfit)
    replace hf₁ : y₁.regs sFound = 1 := by rw [hf₁]; split_ifs; rfl
    rw [hx.bBase_eq] at hh₁ hm₁
    have hv₁ : Nat.ofDigits 2 (decDigits ds) = j := by
      have := Schoening.ofDigits_decDigits hx.binary (by omega)
      omega
    have hz₁ : y₁.regs zero = 0 := (hy₁.regs_eq (by decide)).trans hx.frame.zero_eq
    have hfr₁ : RoundFrame φ C Tb y₁.mem y₁ :=
      hx.frame.of_exec_mem_lt (by decide) hy₁ fun a ha => hm₁ a (by omega)
    have hpar₁ : HoldsList (Tb + 2 * n) S y₁.mem :=
      hx.params.frame fun a _ ha => hm₁ a ha
    have hb₁ : y₁.regs bBase = Tb + 2 * n + S.length :=
      (hy₁.regs_eq (by decide)).trans hx.bBase_eq
    have hl₁ : y₁.regs bLen = ds.length := (hy₁.regs_eq (by decide)).trans hx.bLen_eq
    have hcf : ¬(Cond.eq sFound zero).Holds y₁ := by simp [Cond.holds_eq, hf₁, hz₁]
    -- one round
    have hcore' := (((hcore.law y₁.mem y₁ hfr₁ hpar₁).withPreserves hcore.preserves_bBase)
      |>.withPreserves hcore.preserves_bLen).withPreserves hcore.preserves_flag
    let Q : Data 32 → Prop := fun y => RoundFrame φ C Tb y₁.mem y ∧
      y.regs bBase = Tb + 2 * n + S.length ∧ y.regs bLen = ds.length ∧
      y.regs out = (if φ.eval (assignmentAt y.mem Tb n) then 1 else 0) ∧
      y.regs flag = (if φ.eval (assignmentAt y.mem Tb n) then 0 else 1)
    have hrest := ExecRandLaw.seq_det_right (T₂ := 12 * (encodeClauses φ).length + 5 + 3)
      (c₂ := ram[ ⟪roundCheck⟫; if out = one then [ flag ← zero ] else [ flag ← one ] ])
      (Q := Q) hcore' fun y ⟨⟨⟨⟨hy, hyb⟩, hyB⟩, hyL⟩, hyF⟩ => by
        obtain ⟨z, hz, hzm, hfz, hzo⟩ := roundCheck_exec hw hT hy hyb
        have hzB : z.regs bBase = Tb + 2 * n + S.length := by
          rw [hz.regs_eq (by decide), hyB, hb₁]
        have hzL : z.regs bLen = ds.length := by rw [hz.regs_eq (by decide), hyL, hl₁]
        by_cases he : φ.eval (assignmentAt y.mem Tb n) = true
        · simp only [he, ↓reduceIte] at hzo
          have hcp := ExecWithin.copy (B := .standard) (w := w) (d := flag) (s := zero) (x := z)
          refine ⟨_, hz.seq ((ExecWithin.branch_pos (by simp [Cond.holds_eq, hzo, hfz.one_eq])
            hcp).mono (by omega)), ⟨hfz.set (by decide) _, ?_, ?_, ?_, ?_⟩, ?_⟩
          · simp +decide [hzB]
          · simp +decide [hzL]
          · simpa +decide [he, hzm] using hzo
          · simp +decide [he, hzm, hfz.zero_eq]
          · simp [hzm]
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at hzo
          have hcp := ExecWithin.copy (B := .standard) (w := w) (d := flag) (s := one) (x := z)
          refine ⟨_, hz.seq ((ExecWithin.branch_neg (by simp [Cond.holds_eq, hzo, hfz.one_eq])
            hcp).mono le_rfl), ⟨hfz.set (by decide) _, ?_, ?_, ?_, ?_⟩, ?_⟩
          · simp +decide [hzB]
          · simp +decide [hzL]
          · simpa +decide [he, hzm] using hzo
          · simp +decide [he, hzm, hfz.one_eq]
          · simp [hzm]
    have hbody : ExecRandLaw w (ampBodyWith core) x Q
        (9 * decSteps ds + 4 + (Tc + (12 * (encodeClauses φ).length + 5 + 3) + 2)) (2 * n)
        (fun y => partialAssignmentAt y.mem Tb n) (roundWith O) :=
      ExecRandLaw.seq_det hy₁ (ExecRandLaw.branch_neg hcf hrest)
    have h := ExecRandLaw.loop_iter
      (κ := fun τ => if succeeds φ τ then PMF.pure true else repeatRoundWith O φ j)
      (T₂ := j * (Tc + 12 * (encodeClauses φ).length + 35) + 9 * (decDigits ds).count 0 + 30)
      (R₂ := j * (2 * n))
      hc hbody fun y ⟨hy, hyb, hyl, hyo, hyf⟩ => by
        have hmy : ∀ a, Tb + 2 * n ≤ a → y.mem a = y₁.mem a := hy.rest
        have hdy : HoldsList (Tb + 2 * n + S.length) (decDigits ds) y.mem :=
          hh₁.frame fun a ha _ => hmy a (by omega)
        have hpy : HoldsList (Tb + 2 * n) S y.mem := hpar₁.frame fun a ha _ => hmy a ha
        rw [succeeds_partialAssignmentAt]
        by_cases he : φ.eval (assignmentAt y.mem Tb n) = true
        · simp only [he, ↓reduceIte] at hyo hyf
          have hcy : ¬(Cond.lt zero flag).Holds y := by simp [Cond.holds_lt, hyf]
          have h := ExecRandLaw.loop_exit (w := w) (body := ampBodyWith core)
            (f := fun y => decide (y.regs out = 1)) hcy (P := AmpPost φ C Tb)
            ⟨hy.self, Or.inr ⟨hyo, he⟩⟩
          simp only [he, ↓reduceIte]
          refine (h.congr_law (by simp [hyo])).mono (fun _ h => h) (by omega) (Nat.zero_le _)
        · simp only [he, Bool.false_eq_true, ↓reduceIte] at hyo hyf
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          exact ampLoopWith_law hcore hw hT j (decDigits ds) y
            ⟨hy.self, hpy, hyb, by rw [hyl, Schoening.length_decDigits], hdy,
              Schoening.decDigits_digit_le hx.binary, hyf, hyo⟩ hv₁
            (by rw [Schoening.length_decDigits]; exact hfit)
    have hsteps := Schoening.decSteps_add_count_le ds
    refine (h.congr_law rfl).mono (fun _ h => h) ?_ ?_
    · simp only [Nat.add_mul, Nat.one_mul]; omega
    · simp only [Nat.add_mul, Nat.one_mul]; omega

/-- **The round loop of PPZ** from a counter of value `j` has the law `repeatRound φ j`. Each round
costs `ampRoundTime n E` instructions, amortized: the decrements are paid for by the zero digits of
the counter. -/
theorem ampLoop_law {φ : CNF (Fin n)} {C Tb w : ℕ} (hw : Fits w (Tb + 2 * n)) (hT : 1 ≤ Tb)
    (j : ℕ) (ds : List ℕ) (x : Data 32) (hx : AmpState φ C Tb [] ds x)
    (hv : Nat.ofDigits 2 ds = j) (hfit : Fits w (Tb + 2 * n + ds.length)) :
    ExecRandLaw w ampLoop x (AmpPost φ C Tb)
      (j * ampRoundTime n (encodeClauses φ).length + 9 * ds.count 0 + 30) (j * (2 * n))
      (fun y => decide (y.regs out = 1)) (repeatRound φ j) :=
  ampLoopWith_law (roundCore_isRoundCore hw hT) hw hT j ds x hx hv (by simpa using hfit)

/-! ### The number of rounds -/

/-- The exponent `⌈(k - 1) n / k⌉` of the number of rounds. -/
def ppzExp (k n : ℕ) : ℕ := ((k - 1) * n + k - 1) / k

/-- **The number of rounds** of PPZ with confidence `c` on `n` variables and clauses of at most `k`
literals: `2 ^ ⌈(k - 1) n / k⌉ c`. -/
def ppzRounds (k n c : ℕ) : ℕ := 2 ^ ppzExp k n * c

/-- The binary digits of `2 ^ e c`, low digit first, as the counter's setup computes them: the
digits of `2 ^ e`, multiplied by `c`. -/
def countDigits (e c : ℕ) : List ℕ := mulAddDigits c 0 (List.replicate e 0 ++ [1])

theorem ofDigits_countDigits (e c : ℕ) : Nat.ofDigits 2 (countDigits e c) = 2 ^ e * c := by
  simp [countDigits, Schoening.ofDigits_mulAddDigits, Nat.ofDigits_append,
    Nat.ofDigits_replicate_zero]

theorem countDigits_binary (e c : ℕ) : ∀ d ∈ countDigits e c, d ≤ 1 :=
  Schoening.mulAddDigits_digit_le _ _ _

theorem length_countDigits_le (e c : ℕ) :
    (countDigits e c).length ≤ e + 1 + (Nat.digits 2 c).length := by
  have h := Schoening.length_mulAddDigits_le (a := c) (cy := 0) (B := c)
    (ds := List.replicate e 0 ++ [1])
    (fun d hd => by
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hd
      omega)
    le_rfl (Nat.zero_le _)
  simpa [countDigits] using h

/-- The binary digits of the number of rounds, as the setup computes them: the digits of
`2 ^ ⌈(k - 1) n / k⌉`, multiplied by `c`. -/
def ppzDigits (k n c : ℕ) : List ℕ := countDigits (ppzExp k n) c

/-- A bound on the number of digits of the number of rounds. -/
def ppzCounterLen (k n c : ℕ) : ℕ := ppzExp k n + 1 + (Nat.digits 2 c).length

theorem ofDigits_ppzDigits (k n c : ℕ) : Nat.ofDigits 2 (ppzDigits k n c) = ppzRounds k n c :=
  ofDigits_countDigits _ _

theorem ppzDigits_binary (k n c : ℕ) : ∀ d ∈ ppzDigits k n c, d ≤ 1 :=
  countDigits_binary _ _

theorem length_ppzDigits_le (k n c : ℕ) : (ppzDigits k n c).length ≤ ppzCounterLen k n c :=
  length_countDigits_le _ _

/-- The exponent is at least `(1 - 1 / k) n`. -/
theorem le_ppzExp {k : ℕ} (hk : 1 ≤ k) (n : ℕ) : (1 - 1 / (k : ℝ)) * n ≤ ppzExp k n := by
  have hkn : (k - 1) * n ≤ k * ppzExp k n := by
    have h := Nat.div_add_mod ((k - 1) * n + k - 1) k
    have h' := Nat.mod_lt ((k - 1) * n + k - 1) (show 0 < k by omega)
    simp only [ppzExp]
    omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hr : ((k : ℝ) - 1) * n ≤ k * ppzExp k n := by
    have := (Nat.cast_le (α := ℝ)).mpr hkn
    push_cast [Nat.cast_sub hk] at this
    exact this
  rw [show (1 - 1 / (k : ℝ)) * n = ((k : ℝ) - 1) * n / k by field_simp]
  rw [div_le_iff₀ hk0]
  linarith

/-- The exponent is at most `n`. -/
theorem ppzExp_le (k n : ℕ) : ppzExp k n ≤ n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [ppzExp]
  · simp only [ppzExp]
    rw [Nat.div_le_iff_le_mul_add_pred hk]
    have h1 : (k - 1) * n ≤ k * n := Nat.mul_le_mul_right n (Nat.sub_le k 1)
    have h2 : k * n = n * k := Nat.mul_comm k n
    omega

/-! ### The setup -/

/-- Set up the registers on the input `k :: c :: encode φ`: the clauses start at address `4`, the
partial assignment is stored just after the input, then the order array, then the counter; and
`eReg = ⌈(k - 1) n / k⌉`. -/
def ampSetup : Code .standard 32 := ram[
  one ← #1; two ← #2; val ← *zero; tBase ← val + one; cEnd ← tBase;
  kReg ← *one; val ← one + one; cReg ← *val; val ← val + one; nReg ← *val; cBeg ← val + one;
  pBase ← tBase + nReg; bBase ← pBase + nReg;
  eReg ← kReg - one; eReg ← eReg * nReg; eReg ← eReg + kReg; eReg ← eReg - one; eReg ← eReg / kReg ]

/-- Write a zero digit. -/
def fillBody : Code .standard 32 := ram[ addr ← bBase + iReg; *addr ← zero; iReg ← iReg + one ]

/-- Write the zero digits `iReg, …, eReg - 1`. -/
def fillLoop : Code .standard 32 := .loop (.lt iReg eReg) fillBody

/-- Write the top digit `1`, and prepare the multiplication by `c`. -/
def countTop : Code .standard 32 := ram[
  addr ← bBase + eReg; *addr ← one; bLen ← eReg + one; mulr ← cReg; carry ← zero ]

/-- **The number of rounds**: write the digits of `2 ^ eReg`, then multiply by `c`. -/
def countSetup : Code .standard 32 := ram[
  iReg ← zero; ⟪fillLoop⟫; ⟪countTop⟫; ⟪Schoening.mulAdd.rename embed⟫ ]

/-- The zero digits from `iReg` on. -/
theorem fillLoop_spec {w B e : ℕ} (hfit : Fits w (B + e)) :
    ∀ (d : ℕ) (x : Data 32), x.regs bBase = B → x.regs eReg = e → x.regs zero = 0 →
      x.regs one = 1 → x.regs iReg + d = e →
      ∃ y, ExecWithin w fillLoop x y (5 * d + 2) ∧
        y.mem = fun a => if B + x.regs iReg ≤ a ∧ a < B + e then 0 else x.mem a
  | 0, x, hb, he, hz, ho, hd => by
    have hc : ¬(Cond.lt iReg eReg).Holds x := by simp [Cond.holds_lt, he]; omega
    refine ⟨x, (ExecWithin.loop_exit hc).mono (by omega), funext fun a => ?_⟩
    simp only [show ¬(B + x.regs iReg ≤ a ∧ a < B + e) by omega, ↓reduceIte]
  | d + 1, x, hb, he, hz, ho, hd => by
    obtain ⟨i, hi⟩ : ∃ i, x.regs iReg = i := ⟨_, rfl⟩
    rw [hi] at hd ⊢
    have hc : (Cond.lt iReg eReg).Holds x := by simp [Cond.holds_lt, he, hi]; omega
    have hf1 : Fits w (B + i) := hfit.of_le (by omega)
    have hf2 : Fits w (i + 1) := hfit.of_le (by omega)
    let y := ((x.set addr (B + i)).write (B + i) 0).set iReg (i + 1)
    have hrun : ExecWithin w fillBody x y 3 := by
      ram_eval [y, fillBody, hb, hz, ho, hi, hf1, hf2]
    obtain ⟨z, hz', hzm⟩ := fillLoop_spec hfit d y (by simp +decide [y, hb])
      (by simp +decide [y, he]) (by simp +decide [y, hz]) (by simp +decide [y, ho])
      (by simp [y]; omega)
    refine ⟨z, (ExecWithin.loop_iter hc hrun hz').mono (by omega), ?_⟩
    rw [hzm]
    funext a
    simp only [y, Data.set_regs, Function.update_self, Data.set_mem, Data.write_mem,
      Function.update_apply]
    by_cases h1 : B + (i + 1) ≤ a ∧ a < B + e
    · simp [h1, show B + i ≤ a ∧ a < B + e by omega]
    · by_cases h2 : a = B + i
      · simp [h2, show B + i < B + e by omega]
      · simp [h1, h2, show ¬(B + i ≤ a ∧ a < B + e) by omega]

/-- The data after the setup on the input `k :: c :: encode φ`. -/
def ampSetupData (k c : ℕ) (φ : CNF (Fin n)) : Data 32 :=
  (((((((((((((((((((Data.init (k :: c :: encode φ)).set one 1).set two 2).set val
    (k :: c :: encode φ).length).set tBase ((k :: c :: encode φ).length + 1)).set cEnd
    ((k :: c :: encode φ).length + 1)).set kReg k).set val 2).set cReg c).set val 3).set nReg
    n).set cBeg 4).set pBase ((k :: c :: encode φ).length + 1 + n)).set bBase
    ((k :: c :: encode φ).length + 1 + n + n)).set eReg (k - 1)).set eReg ((k - 1) * n)).set eReg
    ((k - 1) * n + k)).set eReg ((k - 1) * n + k - 1)).set eReg (ppzExp k n))

/-- The setup establishes the frame of the rounds on the input `k :: c :: encode φ`. -/
theorem ampSetup_exec (k c : ℕ) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((k :: c :: encode φ).length + 2 * n + k * n + k + 1)) :
    ExecWithin w ampSetup (Data.init (k :: c :: encode φ)) (ampSetupData k c φ) 18 ∧
      RoundFrame φ 4 ((k :: c :: encode φ).length + 1) (ampSetupData k c φ).mem
        (ampSetupData k c φ) := by
  have hf1 : Fits w 1 := hw.of_le (by omega)
  have hf2 : Fits w 2 := hw.of_le (by simp [encode]; omega)
  have hf3 : Fits w 3 := hw.of_le (by simp [encode]; omega)
  have hf4 : Fits w 4 := hw.of_le (by simp [encode]; omega)
  have hf5 : Fits w ((k :: c :: encode φ).length + 1) := hw.of_le (by omega)
  have hf6 : Fits w ((k :: c :: encode φ).length + 1 + n) := hw.of_le (by omega)
  have hf7 : Fits w ((k :: c :: encode φ).length + 1 + n + n) := hw.of_le (by omega)
  have hkn : (k - 1) * n ≤ k * n := Nat.mul_le_mul_right n (Nat.sub_le k 1)
  have hf8 : Fits w (k - 1) := hw.of_le (by omega)
  have hf9 : Fits w ((k - 1) * n) := hw.of_le (by omega)
  have hf10 : Fits w ((k - 1) * n + k) := hw.of_le (by omega)
  have hf11 : Fits w ((k - 1) * n + k - 1) := hw.of_le (by omega)
  have hf12 : Fits w (((k - 1) * n + k - 1) / k) := hw.of_le (by
    have := Nat.div_le_self ((k - 1) * n + k - 1) k; omega)
  have hm0 : (Data.init (k :: c :: encode φ) : Data 32).mem 0 = (k :: c :: encode φ).length :=
    rfl
  have hm1 : (Data.init (k :: c :: encode φ) : Data 32).mem 1 = k := rfl
  have hm2 : (Data.init (k :: c :: encode φ) : Data 32).mem 2 = c := rfl
  have hm3 : (Data.init (k :: c :: encode φ) : Data 32).mem 3 = n := rfl
  refine ⟨?run, ?frame⟩
  case run =>
    ram_eval [ampSetup, ampSetupData, ppzExp, Data.init_regs, hm0, hm1, hm2, hm3, hf1, hf2, hf3,
      hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12]
  case frame =>
    refine ⟨by simp +decide [ampSetupData], by simp +decide [ampSetupData],
      by simp +decide [ampSetupData], by simp +decide [ampSetupData],
      by simp +decide [ampSetupData], by simp +decide [ampSetupData],
      by simp +decide [ampSetupData], by simp +decide [ampSetupData], ?_, ?_, fun _ _ => rfl⟩
    · intro i
      change (Data.init (k :: c :: encode φ) : Data 32).mem (4 + i.val) =
        (encodeClauses φ)[i.val]
      rw [show 4 + i.val = (3 + i.val) + 1 by omega, Data.init_mem_succ]
      simp [encode, show 3 + i.val = (i.val + 1) + 1 + 1 by omega]
    · simp [length_encode]; omega

/-- The instruction bound of the counter's setup for `2 ^ e c`. -/
def countSetupTime (e c : ℕ) : ℕ := 5 * e + 10 * (e + 1 + (Nat.digits 2 c).length) + 13

/-- **Computing the number of rounds `2 ^ e c`.** From `bBase = B`, `eReg = e` and `cReg = c`, the
setup stores the digits `countDigits e c` from `B`, sets `bLen` to their number and leaves the
memory below `B` unchanged. -/
theorem countSetup_spec {w B e c : ℕ} (x : Data 32) (hz : x.regs zero = 0) (ho : x.regs one = 1)
    (hB : x.regs bBase = B) (he : x.regs eReg = e) (hc : x.regs cReg = c)
    (hw : Fits w (B + e + 1 + (Nat.digits 2 c).length + 2 * c)) :
    ∃ y, ExecWithin w countSetup x y (countSetupTime e c) ∧
      y.regs bLen = (countDigits e c).length ∧ HoldsList B (countDigits e c) y.mem ∧
      ∀ a < B, y.mem a = x.mem a := by
  have hlen := length_countDigits_le e c
  -- the zero digits
  have h₀ := ExecWithin.copy (B := .standard) (w := w) (d := iReg) (s := zero) (x := x)
  rw [hz] at h₀
  obtain ⟨y₁, hy₁, hm₁⟩ := fillLoop_spec (w := w) (B := B) (e := e)
    (hw.of_le (by omega)) e (x.set iReg 0) (by simp +decide [hB])
    (by simp +decide [he]) (by simp +decide [hz]) (by simp +decide [ho]) (by simp)
  simp only [Data.set_regs, Function.update_self, Nat.add_zero, Data.set_mem] at hm₁
  have hm₁' : ∀ a, y₁.mem a = if B ≤ a ∧ a < B + e then 0 else x.mem a := fun a => by rw [hm₁]
  have hr₁ {i : Fin 32} (hi : fillLoop.Preserves i) (hi' : i ≠ iReg) : y₁.regs i = x.regs i := by
    rw [hy₁.regs_eq hi, Data.set_regs, Function.update_of_ne hi']
  -- the top digit
  have hf1 : Fits w (B + e) := hw.of_le (by omega)
  have hf2 : Fits w (e + 1) := hw.of_le (by omega)
  have hy₂ : ExecWithin w countTop y₁ (((((y₁.set addr (B + e)).write
      (B + e) 1).set bLen (e + 1)).set mulr c).set carry 0) 5 := by
    ram_eval [countTop, hr₁ (i := bBase) (by decide) (by decide), hB,
      hr₁ (i := eReg) (by decide) (by decide), he, hr₁ (i := one) (by decide) (by decide), ho,
      hr₁ (i := cReg) (by decide) (by decide), hc, hr₁ (i := zero) (by decide) (by decide), hz,
      hf1, hf2]
  obtain ⟨y₂, hy₂e⟩ : ∃ y₂, (((((y₁.set addr (B + e)).write
      (B + e) 1).set bLen (e + 1)).set mulr c).set carry 0) = y₂ := ⟨_, rfl⟩
  rw [hy₂e] at hy₂
  have hy₂m : ∀ a, y₂.mem a = if a = B + e then 1 else y₁.mem a := fun a => by
    rw [← hy₂e]
    simp only [Data.set_mem, Data.write_mem, Function.update_apply]
  have hy₂b : y₂.regs bBase = B := by
    rw [← hy₂e]; simp +decide [hr₁ (i := bBase) (by decide) (by decide), hB]
  have hds : HoldsList (y₂.regs bBase) (List.replicate e 0 ++ [1]) y₂.mem := by
    rw [hy₂b]
    intro t
    change y₂.mem (B + t.val) = (List.replicate e 0 ++ [1])[t.val]
    have ht := t.isLt
    simp only [List.length_append, List.length_replicate, List.length_singleton] at ht
    rw [hy₂m]
    by_cases hte : t.val = e
    · simp [hte]
    · rw [ite_eq_right (by omega), hm₁', ite_eq_left (by omega),
        List.getElem_append_left (by simp; omega), List.getElem_replicate]
  -- the multiplication by `c`
  have hfit₃ : Fits w (y₂.regs bBase + (mulAddDigits c 0 (List.replicate e 0 ++ [1])).length) := by
    rw [hy₂b]; exact hw.of_le (by simp only [countDigits] at hlen; omega)
  obtain ⟨y₃, hy₃, hh₃, hl₃, hm₃⟩ := mulAdd_rename_spec (w := w) (a := c) (cy := 0) (Bd := c)
    (ds := List.replicate e 0 ++ [1]) (x := y₂)
    (by rw [← hy₂e]; simp +decide [hr₁ (i := zero) (by decide) (by decide), hz])
    (by rw [← hy₂e]; simp +decide [hr₁ (i := one) (by decide) (by decide), ho])
    (by rw [← hy₂e]; simp +decide) (by rw [← hy₂e]; simp +decide)
    (by rw [← hy₂e]; simp +decide) hds
    (fun d hd => by
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hd
      omega)
    le_rfl (Nat.zero_le _) (hw.of_le (by omega)) hfit₃
  rw [hy₂b] at hh₃ hm₃
  have hrun : ExecWithin w countSetup x y₃
      (1 + (5 * e + 2 + (5 + (10 * (mulAddDigits c 0 (List.replicate e 0 ++ [1])).length +
      5)))) := h₀.seq (hy₁.seq (hy₂.seq hy₃))
  refine ⟨y₃, hrun.mono (by simp only [countSetupTime, countDigits] at hlen ⊢; omega), hl₃, hh₃,
    fun a ha => ?_⟩
  rw [hm₃ a ha, hy₂m, ite_eq_right (by omega), hm₁', ite_eq_right (by omega)]

/-- The instruction bound of the counter's setup. -/
def countTime (k n c : ℕ) : ℕ := 5 * ppzExp k n + 10 * ppzCounterLen k n c + 13

/-- **Computing the number of rounds.** After the setup, the counter holds the digits
`ppzDigits k n c` of `ppzRounds k n c`, and the frame of the rounds holds. -/
theorem countSetup_exec (k c : ℕ) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((k :: c :: encode φ).length + 2 * n + k * n + k + 2 * c +
      ppzCounterLen k n c + 2)) :
    ∃ y, ExecWithin w countSetup (ampSetupData k c φ) y (countTime k n c) ∧
      RoundFrame φ 4 ((k :: c :: encode φ).length + 1) y.mem y ∧
      y.regs bBase = (k :: c :: encode φ).length + 1 + 2 * n ∧
      y.regs bLen = (ppzDigits k n c).length ∧
      HoldsList ((k :: c :: encode φ).length + 1 + 2 * n) (ppzDigits k n c) y.mem ∧
      y.regs out = 0 := by
  obtain ⟨L, hL⟩ : ∃ L, (k :: c :: encode φ).length = L := ⟨_, rfl⟩
  rw [hL] at hw ⊢
  have hfr : RoundFrame φ 4 (L + 1) (ampSetupData k c φ).mem (ampSetupData k c φ) := by
    have := (ampSetup_exec k c φ (hw.of_le (by rw [hL]; omega))).2
    rwa [hL] at this
  have hDb : (ampSetupData k c φ).regs bBase = L + 1 + 2 * n := by
    simp +decide [ampSetupData, hL]; omega
  have hDe : (ampSetupData k c φ).regs eReg = ppzExp k n := by simp +decide [ampSetupData]
  have hDc : (ampSetupData k c φ).regs cReg = c := by simp +decide [ampSetupData]
  have hDo : (ampSetupData k c φ).regs out = 0 := by simp +decide [ampSetupData]
  obtain ⟨y, hy, hyl, hyh, hym⟩ := countSetup_spec (ampSetupData k c φ) hfr.zero_eq hfr.one_eq
    hDb hDe hDc (hw.of_le (by simp only [ppzCounterLen]; omega))
  exact ⟨y, hy, hfr.of_exec_mem_lt (by decide) hy fun a ha => hym a (by omega),
    by rw [hy.regs_eq (by decide), hDb], hyl, hyh, by rw [hy.regs_eq (by decide), hDo]⟩

/-! ### The algorithm -/

/-- **The PPZ algorithm** on the input `k :: c :: encode φ`. -/
def ampCode : Code .standard 32 := ram[ ⟪ampSetup⟫; ⟪countSetup⟫; flag ← one; ⟪ampLoop⟫ ]

/-- **The PPZ algorithm** on the input `k :: c :: encode φ`, halting with `out`. -/
def ampProgram : Program .standard 32 := ampCode.program out

/-- The instruction bound of the PPZ algorithm with confidence `c`, on `n` variables, clauses of
at most `k` literals and an input of length `L`. -/
def ampTime (k n c L : ℕ) : ℕ :=
  ppzRounds k n c * (n * (28 * L + 40) + 12 * L + 41) + 5 * ppzExp k n +
    19 * ppzCounterLen k n c + 63

/-- **The PPZ algorithm on the randomized word RAM.** On the input `k :: c :: encode φ` of length
`L`, with `1 ≤ k` and at any word size `w` with
`L + 2 n + k n + k + 2 c + ppzCounterLen k n c + 2 < 2 ^ w`, the program

* halts on every path within `ampTime k n c L` instructions;
* makes at most `R (2 n)` `rand` calls, where `R = ppzRounds k n c`;
* outputs `0` or `1`, and outputs `1` only with a satisfying assignment of `φ` stored at address
  `L + 1`;
* outputs `1` with exactly the law `repeatRound φ R` of up to `R` independent rounds. -/
theorem ampProgram_spec (k c : ℕ) (hk : 1 ≤ k) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((k :: c :: encode φ).length + 2 * n + k * n + k + 2 * c +
      ppzCounterLen k n c + 2)) :
    RandHaltsWithin w ampProgram (.init (k :: c :: encode φ))
      (ampTime k n c (k :: c :: encode φ).length) ∧
    RandCallsBounded w ampProgram (.init (k :: c :: encode φ))
      (ampTime k n c (k :: c :: encode φ).length) (ppzRounds k n c * (2 * n)) ∧
    (∀ cfg ∈ (runRand w ampProgram (ampTime k n c (k :: c :: encode φ).length)
        (.running (.init (k :: c :: encode φ)))).support,
      ∃ v d, cfg = .halted v d ∧
        (v = 0 ∨ (v = 1 ∧
          φ.eval (assignmentAt d.mem ((k :: c :: encode φ).length + 1) n) = true))) ∧
    (evalRand w ampProgram (ampTime k n c (k :: c :: encode φ).length)
      (.init (k :: c :: encode φ))).map Schoening.cfgSuccess =
        repeatRound φ (ppzRounds k n c) := by
  set L := (k :: c :: encode φ).length with hL
  have hE : (encodeClauses φ).length ≤ L := by
    simp only [hL, List.length_cons, length_encode]; omega
  have h₀ := (ampSetup_exec k c φ (hw.of_le (by omega))).1
  obtain ⟨y₁, hy₁, hfr₁, hb₁, hl₁, hh₁, ho₁⟩ := countSetup_exec k c φ hw
  have hfl : ExecWithin w (ram[ flag ← one ] : Code .standard 32) y₁ (y₁.set flag 1) 1 := by
    ram_eval [hfr₁.one_eq]
  have hlen := length_ppzDigits_le k n c
  have hstate : AmpState φ 4 (L + 1) [] (ppzDigits k n c) (y₁.set flag 1) :=
    { frame := hfr₁.set (by decide) 1
      params := holdsList_nil _ _
      bBase_eq := by simp +decide [hb₁, hL]
      bLen_eq := by simp +decide [hl₁]
      digits := hh₁
      binary := ppzDigits_binary k n c
      flag_eq := by simp
      out_eq := by simp +decide [ho₁] }
  have hloop := ampLoop_law (φ := φ) (C := 4) (Tb := L + 1) (hw.of_le (by omega)) (by omega)
    (ppzRounds k n c) (ppzDigits k n c) (y₁.set flag 1) hstate (ofDigits_ppzDigits k n c)
    (hw.of_le (by omega))
  have hall := ExecRandLaw.seq_det h₀ (ExecRandLaw.seq_det hy₁ (ExecRandLaw.seq_det hfl hloop))
  have hcount := List.count_le_length (a := 0) (l := ppzDigits k n c)
  obtain ⟨hhalt, hcalls, hpost, hlaw⟩ := hall.program out (T' := ampTime k n c L)
    (by
      simp only [ampTime, ampRoundTime, roundCoreTime, countTime]
      have h1 := Nat.mul_le_mul_left n (show 28 * (encodeClauses φ).length + 40 ≤ 28 * L + 40 by
        omega)
      have h2 := Nat.mul_le_mul_left (ppzRounds k n c)
        (show n * (28 * (encodeClauses φ).length + 40) + 6 + 12 * (encodeClauses φ).length + 35 ≤
          n * (28 * L + 40) + 12 * L + 41 by omega)
      omega)
    Schoening.cfgSuccess fun _ _ => rfl
  refine ⟨hhalt, hcalls, fun cfg hcfg => ?_, hlaw⟩
  obtain ⟨d, rfl, -, hd⟩ := hpost cfg hcfg
  exact ⟨_, d, rfl, hd⟩

/-- **Failure probability.** The program outputs something other than `1` with probability exactly
`(1 - p) ^ R`, where `R = ppzRounds k n c` and `p = roundSuccessProb φ` is the probability that one
round finds a satisfying assignment. -/
theorem ampProgram_failure_eq (k c : ℕ) (hk : 1 ≤ k) (φ : CNF (Fin n)) {w : ℕ}
    (hw : Fits w ((k :: c :: encode φ).length + 2 * n + k * n + k + 2 * c +
      ppzCounterLen k n c + 2)) :
    ((evalRand w ampProgram (ampTime k n c (k :: c :: encode φ).length)
      (.init (k :: c :: encode φ))).map Schoening.cfgSuccess false).toReal =
      (1 - roundSuccessProb φ) ^ ppzRounds k n c := by
  rw [(ampProgram_spec k c hk φ hw).2.2.2, repeatRound_false_toReal]

/-- **The PPZ algorithm succeeds with high probability** [Paturi, Pudlák, Zane][PPZ1997]. On a
satisfiable formula whose clauses have at most `k ≥ 1` literals, the program outputs `1` except
with probability at most `e ^ (-c)`. -/
theorem ampProgram_failure_le_exp {k c : ℕ} (hk : 1 ≤ k) {φ : CNF (Fin n)} (hφ : φ.Satisfiable)
    (hlen : ∀ cl ∈ φ, cl.length ≤ k) {w : ℕ}
    (hw : Fits w ((k :: c :: encode φ).length + 2 * n + k * n + k + 2 * c +
      ppzCounterLen k n c + 2)) :
    ((evalRand w ampProgram (ampTime k n c (k :: c :: encode φ).length)
      (.init (k :: c :: encode φ))).map Schoening.cfgSuccess false).toReal ≤ Real.exp (-c) := by
  rw [ampProgram_failure_eq k c hk φ hw]
  have hp := roundSuccessProb_ge hk hφ hlen
  have hp1 : roundSuccessProb φ ≤ 1 := roundSuccessProbWith_le_one _ _
  refine Schoening.one_sub_pow_le_exp hp1 ?_
  have he := le_ppzExp hk n
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ppzExp k n * (2 : ℝ) ^ (-((1 - 1 / (k : ℝ)) * n)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add two_pos]
    exact Real.one_le_rpow one_le_two (by linarith)
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  calc (c : ℝ) ≤ c * ((2 : ℝ) ^ ppzExp k n * (2 : ℝ) ^ (-((1 - 1 / (k : ℝ)) * n))) :=
        le_mul_of_one_le_right hc0 h2
    _ = ((2 : ℝ) ^ ppzExp k n * c) * (2 : ℝ) ^ (-((1 - 1 / (k : ℝ)) * n)) := by ring
    _ ≤ ((2 : ℝ) ^ ppzExp k n * c) * roundSuccessProb φ := by gcongr
    _ = (ppzRounds k n c : ℝ) * roundSuccessProb φ := by simp [ppzRounds]

/-- The exponent is at most `(1 - 1 / k) n + 1`. -/
theorem ppzExp_le_add_one {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (ppzExp k n : ℝ) ≤ (1 - 1 / (k : ℝ)) * n + 1 := by
  have hkn : k * ppzExp k n ≤ (k - 1) * n + k := by
    have := Nat.div_mul_le_self ((k - 1) * n + k - 1) k
    simp only [ppzExp]
    rw [Nat.mul_comm]
    omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hr : (k : ℝ) * ppzExp k n ≤ ((k : ℝ) - 1) * n + k := by
    have := (Nat.cast_le (α := ℝ)).mpr hkn
    push_cast [Nat.cast_sub hk] at this
    exact this
  rw [show (1 - 1 / (k : ℝ)) * n + 1 = (((k : ℝ) - 1) * n + k) / k by field_simp, le_div_iff₀ hk0]
  linarith

/-- **The running time** of the PPZ algorithm is `O((n + L) ^ 2 2 ^ ((1 - 1 / k) n) (c + 1))`:
explicitly, at most `200 (n + L + 1) ^ 2 2 ^ ((1 - 1 / k) n) (c + 1)` instructions. For `k = 3`
this is `O((n + L) ^ 2 2 ^ (2 n / 3) (c + 1))`, about `1.588 ^ n`. -/
theorem ampTime_le {k : ℕ} (hk : 1 ≤ k) (n c L : ℕ) :
    (ampTime k n c L : ℝ) ≤
      200 * ((n + L + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ ((1 - 1 / (k : ℝ)) * n) * (c + 1) := by
  set X := (2 : ℝ) ^ ((1 - 1 / (k : ℝ)) * n) with hX
  obtain ⟨N, hN⟩ : ∃ N, n + L + 1 = N := ⟨_, rfl⟩
  rw [hN]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hX1 : 1 ≤ X := by
    refine Real.one_le_rpow one_le_two (mul_nonneg ?_ (Nat.cast_nonneg n))
    rw [sub_nonneg, div_le_one (by linarith)]
    exact hk1
  -- the number of rounds
  have hR : (ppzRounds k n c : ℝ) ≤ 2 * X * c := by
    simp only [ppzRounds]
    push_cast
    have h : (2 : ℝ) ^ ppzExp k n ≤ 2 * X := by
      rw [← Real.rpow_natCast, hX, show 2 * (2 : ℝ) ^ ((1 - 1 / (k : ℝ)) * n) =
        (2 : ℝ) ^ ((1 - 1 / (k : ℝ)) * n + 1) by rw [Real.rpow_add two_pos, Real.rpow_one]; ring]
      exact Real.rpow_le_rpow_of_exponent_le one_le_two (ppzExp_le_add_one hk n)
    exact mul_le_mul_of_nonneg_right h (Nat.cast_nonneg c)
  -- one round
  have hP : n * (28 * L + 40) + 12 * L + 41 ≤ 41 * N ^ 2 := by
    have h1 : n + 1 ≤ N := by omega
    have h2 : L + 1 ≤ N := by omega
    have h3 : (n + 1) * (L + 1) ≤ N * N := Nat.mul_le_mul h1 h2
    nlinarith
  -- the setup
  have hS : 5 * ppzExp k n + 19 * ppzCounterLen k n c + 63 ≤ 82 * N ^ 2 * (c + 1) := by
    have he := ppzExp_le k n
    have hd : (Nat.digits 2 c).length ≤ c :=
      (Nat.digits_length_le_iff (by decide) _).mpr Nat.lt_two_pow_self
    have h1 : n + 1 ≤ N ^ 2 := by nlinarith
    have h3 : 5 * ppzExp k n + 19 * ppzCounterLen k n c + 63 ≤ 82 * (n + 1) * (c + 1) := by
      simp only [ppzCounterLen]
      nlinarith [Nat.zero_le (n * c)]
    have h4 : 82 * (n + 1) * (c + 1) ≤ 82 * N ^ 2 * (c + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)
    omega
  have hexp : (ampTime k n c L : ℝ) =
      (ppzRounds k n c : ℝ) * ((n * (28 * L + 40) + 12 * L + 41 : ℕ) : ℝ) +
        ((5 * ppzExp k n + 19 * ppzCounterLen k n c + 63 : ℕ) : ℝ) := by
    simp only [ampTime]; push_cast; ring
  have hPr : ((n * (28 * L + 40) + 12 * L + 41 : ℕ) : ℝ) ≤ 41 * (N : ℝ) ^ 2 := by
    exact_mod_cast hP
  have hSr : ((5 * ppzExp k n + 19 * ppzCounterLen k n c + 63 : ℕ) : ℝ) ≤
      82 * (N : ℝ) ^ 2 * (c + 1) := by
    exact_mod_cast hS
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hN0 : (0 : ℝ) ≤ (N : ℝ) ^ 2 := by positivity
  have hT : (ppzRounds k n c : ℝ) * ((n * (28 * L + 40) + 12 * L + 41 : ℕ) : ℝ) ≤
      (2 * X * c) * (41 * (N : ℝ) ^ 2) :=
    mul_le_mul hR hPr (Nat.cast_nonneg _) (by positivity)
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_left hX1 (mul_nonneg hN0 (by linarith : (0 : ℝ) ≤ c + 1)),
    mul_nonneg (mul_nonneg hN0 (by linarith : (0 : ℝ) ≤ X)) hc0]

end Cslib.Algorithms.WordRAM.PPZ
