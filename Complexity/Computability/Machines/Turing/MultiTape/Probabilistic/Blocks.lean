/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Locality
public import Complexity.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Sign.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Sign.Basic
import Mathlib.Tactic.Linarith

/-!
# Time intervals and tape blocks of a choice-string run

The blocking idea of Hopcroft, Paul and Valiant [HopcroftPaulValiant1977], in the form of
Lemma 2.1 of the note *Deterministic simulations of nondeterministic and randomized time*
(30 October 2026) formalized in issue #1833. It uses three neighbouring tape blocks instead of
making the machine block-respecting (compare [Williams2025], Lemma 2.1 and §3.2). The
statements here are the run-level facts of that lemma, for the replay
`Turing.MultiTapePTM.stepCoins` of a fair-coin table on a list of choice bits.

Time is cut into intervals of `b` steps: interval `i` starts at
`Turing.MultiTapePTM.intervalStart b coins c i`, after the first `i * b` bits. Each tape is cut
into blocks `B_j = [b j, b (j + 1))`, so a head at coordinate `p` (`Turing.Cfg.headPos`) is in
block `p / b` at offset `p % b`. The blocked heads are the input head and the `k` work heads;
the write-only output tape is never read and is not blocked.

* **Three blocks.** Within `b` steps a head moves at most `b` cells, so it stays in the blocks
  `B_{j-1}, B_j, B_{j+1}` around its starting block `B_j`
  (`Turing.MultiTapePTM.headPos_stepCoins_mem_Ico`), and its block index changes by at most one
  (`Turing.MultiTapePTM.abs_blockIndex_stepCoins_sub_le`).
* **Schedules.** The *movement schedule* of a run (`Turing.MultiTapePTM.schedule`) records this
  change in `{-1, 0, 1}` for every interval and head. There are `3 ^ ((k + 1) * q)` schedules of
  `q` intervals (`Turing.MultiTapePTM.card_schedule`), every run has exactly one, and it
  determines all block indices from the starting ones
  (`Turing.MultiTapePTM.blockIndex_intervalStart`).
* **Locality.** An interval only reads and writes the window `Turing.Cfg.blockWindow` of three
  blocks around each work head. Two configurations agreeing on their control, heads and window
  contents still agree after `b` steps on the same bits, and emit the same output
  (`Turing.MultiTapePTM.agreeOn_blockWindow_stepCoins`). So the interval is determined by its
  bits, its entering state and head positions and the contents of its windows. Cells outside the
  window are unchanged (`Turing.MultiTapePTM.workTapes_stepCoins_eq_of_notMem_blockWindow`), and
  a cell lying outside the windows of a range of intervals is untouched throughout that range
  (`Turing.MultiTapePTM.workTapes_intervalStart_eq_of_notMem_blockWindow`).

All statements hold for every block length `b > 0` and number `q` of intervals; the choice
`q = ⌈t / b⌉` and the bound `2 ≤ b ≤ t` of the note only matter for counting.

## Main definitions

* `Turing.Cfg.blockWindow`: the three blocks around each work head.
* `Turing.MultiTapePTM.intervalStart`: the configuration at the start of a time interval.
* `Turing.MultiTapePTM.Schedule`, `Turing.MultiTapePTM.schedule`: movement schedules.

## Main results

* `Turing.MultiTapePTM.abs_headPos_stepCoins_sub_le`: a head moves at most one cell per bit.
* `Turing.MultiTapePTM.headPos_stepCoins_mem_Ico`: within `b` steps, three blocks.
* `Turing.MultiTapePTM.abs_blockIndex_stepCoins_sub_le`: block indices change by at most one.
* `Turing.MultiTapePTM.card_schedule`: there are `3 ^ ((k + 1) * q)` schedules.
* `Turing.MultiTapePTM.coe_schedule`: a schedule entry is the change of block index.
* `Turing.MultiTapePTM.blockIndex_intervalStart`: schedules determine block indices.
* `Turing.MultiTapePTM.agreeOn_stepCoins`: locality of a run on cells containing its heads.
* `Turing.MultiTapePTM.agreeOn_blockWindow_stepCoins`: an interval is determined by its window.
* `Turing.MultiTapePTM.workTapes_stepCoins_eq_of_notMem_blockWindow`: cells outside the window
  are unchanged.
* `Turing.MultiTapePTM.workTapes_intervalStart_eq_of_notMem_blockWindow`: blocks outside the
  windows of a range of intervals are untouched.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On Time Versus Space*][HopcroftPaulValiant1977]
* [R. Williams, *Simulating Time With Square-Root Space*][Williams2025]
-/

public section

namespace Turing

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-! ### Block arithmetic -/

/-- Within distance `b` of a point of block `p / b`, the three blocks around it. -/
private theorem mem_Ico_of_abs_sub_le {b p p' : ℤ} (hb : 0 < b) (h : |p' - p| ≤ b) :
    b * (p / b - 1) ≤ p' ∧ p' < b * (p / b + 2) := by
  have hdiv := Int.mul_ediv_add_emod p b
  have hlo := Int.emod_nonneg p hb.ne'
  have hhi := Int.emod_lt_of_pos p hb
  have := abs_le.mp h
  constructor <;> nlinarith

/-- Within distance `b`, block indices differ by at most one. -/
private theorem abs_ediv_sub_ediv_le_one {b p p' : ℤ} (hb : 0 < b) (h : |p' - p| ≤ b) :
    |p' / b - p / b| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := mem_Ico_of_abs_sub_le hb h
  have hdiv := Int.mul_ediv_add_emod p' b
  have hlo' := Int.emod_nonneg p' hb.ne'
  have hhi' := Int.emod_lt_of_pos p' hb
  have h₁ : p' / b < p / b + 2 := lt_of_mul_lt_mul_left (by linarith) hb.le
  have h₂ : p / b - 1 < p' / b + 1 := lt_of_mul_lt_mul_left (by linarith) hb.le
  rw [abs_le]
  constructor <;> omega

/-- The three blocks of length `b` around the block of each work head: the cells a work head can
visit within `b` steps. -/
@[expose] def Cfg.blockWindow (b : ℕ) (c : Cfg k Symbol State input) (i : Fin k) : Set ℤ :=
  Set.Ico (b * (c.workTapePos i / b - 1)) (b * (c.workTapePos i / b + 2))

namespace MultiTapePTM

variable (machine : MultiTapePTM k Symbol State)

/-! ### Head movement -/

/-- A replayed bit is a step of the table with that coin fixed. -/
private theorem step_withCoin (bit : Bool) (c : Cfg k Symbol State input) :
    (machine.withCoin bit).toTM.Step c ((machine.withCoin bit).toTM.step c) :=
  MultiTapeTM.step_iff.mpr rfl

/-- A head moves at most one cell per replayed bit. -/
theorem abs_headPos_stepCoins_sub_le (coins : List Bool) (c : Cfg k Symbol State input)
    (head : Option (Fin k)) :
    |(machine.stepCoins coins c).headPos head - c.headPos head| ≤ coins.length := by
  induction coins generalizing c with
  | nil => simp
  | cons bit coins ih =>
    rw [stepCoins_cons]
    have h₁ := abs_le.mp (ih ((machine.withCoin bit).toTM.step c))
    have h₂ := abs_le.mp ((machine.step_withCoin bit c).abs_headPos_sub_le head)
    rw [abs_le, List.length_cons]
    push_cast
    constructor <;> linarith

/-- **Three blocks.** Within `b` replayed bits, a head stays in the three blocks of length `b`
around its starting block. -/
theorem headPos_stepCoins_mem_Ico {b : ℕ} (hb : 0 < b) {coins : List Bool}
    (hlen : coins.length ≤ b) (c : Cfg k Symbol State input) (head : Option (Fin k)) :
    (machine.stepCoins coins c).headPos head ∈
      Set.Ico ((b : ℤ) * (c.headPos head / b - 1)) (b * (c.headPos head / b + 2)) :=
  mem_Ico_of_abs_sub_le (by exact_mod_cast hb)
    ((machine.abs_headPos_stepCoins_sub_le coins c head).trans (by exact_mod_cast hlen))

/-- Within `b` replayed bits, the block index of a head changes by at most one. -/
theorem abs_blockIndex_stepCoins_sub_le {b : ℕ} (hb : 0 < b) {coins : List Bool}
    (hlen : coins.length ≤ b) (c : Cfg k Symbol State input) (head : Option (Fin k)) :
    |(machine.stepCoins coins c).headPos head / b - c.headPos head / b| ≤ 1 :=
  abs_ediv_sub_ediv_le_one (by exact_mod_cast hb)
    ((machine.abs_headPos_stepCoins_sub_le coins c head).trans (by exact_mod_cast hlen))

/-- A work-tape cell farther from the head than the number of replayed bits is unchanged. -/
theorem workTapes_stepCoins_eq_of_lt_abs (coins : List Bool) (c : Cfg k Symbol State input)
    {i : Fin k} {z : ℤ} (hz : (coins.length : ℤ) < |z - c.workTapePos i|) :
    (machine.stepCoins coins c).workTapes i z = c.workTapes i z := by
  induction coins generalizing c with
  | nil => rfl
  | cons bit coins ih =>
    have hstep := machine.step_withCoin bit c
    have hmove := abs_le.mp (hstep.abs_headPos_sub_le (some i))
    simp only [Cfg.headPos_some] at hmove
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hz
    rw [stepCoins_cons, ih _ ?_]
    · refine hstep.workTapes_eq_of_ne fun hzpos => ?_
      rw [hzpos, sub_self, abs_zero] at hz
      omega
    · rw [lt_abs] at hz ⊢
      omega

/-- **Locality of a run.** If two configurations agree on cells `W`, and the work heads of the
first stay in `W` before each replayed bit, then after replaying the same bits they still agree
on `W` and have appended the same word to their outputs. -/
theorem agreeOn_stepCoins {W : Fin k → Set ℤ} {c c' : Cfg k Symbol State input}
    (h : c.AgreeOn W c') (coins : List Bool)
    (hpos : ∀ j < coins.length, ∀ i, (machine.stepCoins (coins.take j) c).workTapePos i ∈ W i) :
    (machine.stepCoins coins c).AgreeOn W (machine.stepCoins coins c') ∧
      ∃ e, (machine.stepCoins coins c).output = c.output ++ e ∧
        (machine.stepCoins coins c').output = c'.output ++ e := by
  induction coins generalizing c c' with
  | nil => exact ⟨h, [], by simp, by simp⟩
  | cons bit coins ih =>
    obtain ⟨hstep, e, he, he'⟩ :=
      MultiTapeTM.agreeOn_step (machine.withCoin bit).toTM h (hpos 0 (by simp))
    obtain ⟨hrest, e', hrest₁, hrest₂⟩ := ih hstep fun j hj => by
      simpa only [List.take_succ_cons, stepCoins_cons] using
        hpos (j + 1) (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hj)
    refine ⟨hrest, e ++ e', ?_, ?_⟩
    · rw [stepCoins_cons, hrest₁, he, List.append_assoc]
    · rw [stepCoins_cons, hrest₂, he', List.append_assoc]

/-- **An interval is determined by its window.** Two configurations agreeing on the three blocks
around each work head of the first still agree there after at most `b` replayed bits, and have
appended the same word to their outputs. -/
theorem agreeOn_blockWindow_stepCoins {b : ℕ} (hb : 0 < b) {coins : List Bool}
    (hlen : coins.length ≤ b) {c c' : Cfg k Symbol State input}
    (h : c.AgreeOn (c.blockWindow b) c') :
    (machine.stepCoins coins c).AgreeOn (c.blockWindow b) (machine.stepCoins coins c') ∧
      ∃ e, (machine.stepCoins coins c).output = c.output ++ e ∧
        (machine.stepCoins coins c').output = c'.output ++ e :=
  machine.agreeOn_stepCoins h coins fun j _ i =>
    machine.headPos_stepCoins_mem_Ico hb (coins := coins.take j)
      ((List.length_take_le' j coins).trans hlen) c (some i)

/-- Within `b` replayed bits, a work-tape cell outside the three blocks around its head is
unchanged. -/
theorem workTapes_stepCoins_eq_of_notMem_blockWindow {b : ℕ} (hb : 0 < b) {coins : List Bool}
    (hlen : coins.length ≤ b) (c : Cfg k Symbol State input) {i : Fin k} {z : ℤ}
    (hz : z ∉ c.blockWindow b i) :
    (machine.stepCoins coins c).workTapes i z = c.workTapes i z := by
  refine machine.workTapes_stepCoins_eq_of_lt_abs coins c ?_
  have hb' : (0 : ℤ) < b := by exact_mod_cast hb
  have hdiv := Int.mul_ediv_add_emod (c.workTapePos i) b
  have hlo := Int.emod_nonneg (c.workTapePos i) hb'.ne'
  have hhi := Int.emod_lt_of_pos (c.workTapePos i) hb'
  have hlen' : (coins.length : ℤ) ≤ b := by exact_mod_cast hlen
  simp only [Cfg.blockWindow, Set.mem_Ico, not_and_or, not_le, not_lt] at hz
  rw [lt_abs]
  rcases hz with hz | hz
  · right
    nlinarith
  · left
    nlinarith

/-! ### Time intervals and schedules -/

/-- The configuration at the start of time interval `i`, of `b` steps each: replay the first
`i * b` bits. -/
@[expose] noncomputable def intervalStart (b : ℕ) (coins : List Bool) (c : Cfg k Symbol State input)
    (i : ℕ) : Cfg k Symbol State input :=
  machine.stepCoins (coins.take (i * b)) c

@[simp] theorem intervalStart_zero (b : ℕ) (coins : List Bool) (c : Cfg k Symbol State input) :
    machine.intervalStart b coins c 0 = c := by
  simp [intervalStart]

/-- Interval `i + 1` starts after replaying the `b` bits of interval `i`. -/
theorem intervalStart_succ (b : ℕ) (coins : List Bool) (c : Cfg k Symbol State input) (i : ℕ) :
    machine.intervalStart b coins c (i + 1) =
      machine.stepCoins ((coins.drop (i * b)).take b) (machine.intervalStart b coins c i) := by
  rw [intervalStart, intervalStart, ← stepCoins_append, Nat.succ_mul, List.take_add]

/-- The bits of an interval number at most `b`. -/
theorem length_intervalCoins_le (b : ℕ) (coins : List Bool) (i : ℕ) :
    ((coins.drop (i * b)).take b).length ≤ b :=
  List.length_take_le _ _

/-- A movement schedule of `q` intervals: the change, in `{-1, 0, 1}`, of the block index of
the input head (`none`) and of each work head (`some i`) across each interval. -/
abbrev Schedule (k q : ℕ) := Fin q → Option (Fin k) → SignType

/-- There are `3 ^ ((k + 1) * q)` movement schedules of `q` intervals. -/
theorem card_schedule (k q : ℕ) : Fintype.card (Schedule k q) = 3 ^ ((k + 1) * q) := by
  simp only [Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
  rw [show Fintype.card SignType = 3 from rfl, ← pow_mul, mul_comm]

/-- The movement schedule of the run replaying `coins` from `c`, in `q` intervals of `b` bits:
the change of the block index of every head across every interval. -/
noncomputable def schedule (b q : ℕ) (coins : List Bool) (c : Cfg k Symbol State input) :
    Schedule k q := fun i head =>
  SignType.sign ((machine.intervalStart b coins c (i + 1)).headPos head / b -
    (machine.intervalStart b coins c i).headPos head / b)

/-- An integer of absolute value at most one is its own sign. -/
private theorem coe_sign_eq_self {d : ℤ} (hd : |d| ≤ 1) :
    ((SignType.sign d : SignType) : ℤ) = d := by
  have : d = -1 ∨ d = 0 ∨ d = 1 := by rw [abs_le] at hd; omega
  rcases this with rfl | rfl | rfl <;> rfl

/-- A schedule entry is the change of block index across the interval. -/
theorem coe_schedule {b : ℕ} (hb : 0 < b) (q : ℕ) (coins : List Bool)
    (c : Cfg k Symbol State input) (i : Fin q) (head : Option (Fin k)) :
    (machine.schedule b q coins c i head : ℤ) =
      (machine.intervalStart b coins c (i + 1)).headPos head / b -
        (machine.intervalStart b coins c i).headPos head / b := by
  refine coe_sign_eq_self ?_
  rw [intervalStart_succ]
  exact machine.abs_blockIndex_stepCoins_sub_le hb (length_intervalCoins_le _ _ _) _ head

/-- **Schedules determine block indices.** At the start of interval `i ≤ q`, the block index of a
head is its starting block index plus the schedule entries of the earlier intervals. -/
theorem blockIndex_intervalStart {b : ℕ} (hb : 0 < b) {q : ℕ} (coins : List Bool)
    (c : Cfg k Symbol State input) (head : Option (Fin k)) {i : ℕ} (hi : i ≤ q) :
    (machine.intervalStart b coins c i).headPos head / b =
      c.headPos head / b +
        ∑ j : Fin i, (machine.schedule b q coins c (Fin.castLE hi j) head : ℤ) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hsum : ∑ j : Fin i, (machine.schedule b q coins c (Fin.castLE hi j.castSucc) head : ℤ) =
        ∑ j : Fin i, (machine.schedule b q coins c (Fin.castLE (by omega) j) head : ℤ) := rfl
    rw [Fin.sum_univ_castSucc, hsum, ← add_assoc, ← ih (by omega)]
    have := machine.coe_schedule hb q coins c ⟨i, by omega⟩ head
    simp only at this
    change _ = _ + (machine.schedule b q coins c ⟨i, by omega⟩ head : ℤ)
    rw [this]
    ring

/-- Across interval `i`, a work-tape cell outside the window of interval `i` is unchanged. -/
theorem workTapes_intervalStart_succ_eq {b : ℕ} (hb : 0 < b) (coins : List Bool)
    (c : Cfg k Symbol State input) (i : ℕ) {h : Fin k} {z : ℤ}
    (hz : z ∉ (machine.intervalStart b coins c i).blockWindow b h) :
    (machine.intervalStart b coins c (i + 1)).workTapes h z =
      (machine.intervalStart b coins c i).workTapes h z := by
  rw [intervalStart_succ]
  exact machine.workTapes_stepCoins_eq_of_notMem_blockWindow hb
    (length_intervalCoins_le _ _ _) _ hz

/-- **Untouched blocks.** A work-tape cell outside the windows of intervals `i₁, …, i₂ - 1` has
the same contents at the start of interval `i₂` as at the start of interval `i₁`. -/
theorem workTapes_intervalStart_eq_of_notMem_blockWindow {b : ℕ} (hb : 0 < b)
    (coins : List Bool) (c : Cfg k Symbol State input) {h : Fin k} {z : ℤ} {i₁ i₂ : ℕ}
    (hle : i₁ ≤ i₂)
    (hz : ∀ i, i₁ ≤ i → i < i₂ → z ∉ (machine.intervalStart b coins c i).blockWindow b h) :
    (machine.intervalStart b coins c i₂).workTapes h z =
      (machine.intervalStart b coins c i₁).workTapes h z := by
  induction i₂, hle using Nat.le_induction with
  | base => rfl
  | succ i₂ hle ih =>
    rw [machine.workTapes_intervalStart_succ_eq hb coins c i₂ (hz i₂ hle (by omega)),
      ih fun i hi hi₂ => hz i hi (by omega)]

end MultiTapePTM

end Turing
