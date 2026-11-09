/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RAM.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Size

/-!
# Cost measures for random-access machines

A *cost measure* charges each instruction, executed on given register contents, an amount of time,
and the *time* of a run is the total charge of the instructions it executes. Two measures are
standard [Cook and Reckhow, Section 1][CookReckhow1973]:

* the *unit* cost measure charges every instruction `1`, so that time counts steps;
* the *logarithmic* cost measure charges every instruction the lengths of the numbers it reads,
  so that time accounts for the size of the numbers in the registers.

Within logarithmic time `T` a RAM never holds a number longer than `T` or than the longest number
it starts with (`Cslib.RAM.bitLength_read_run_le`), whereas within unit time `4 k + 5` a fixed
program builds from `k` a number with `2 ^ k + 1` binary digits
(`Cslib.RAM.computesInTime_unitCost_repeatedSquaring`), so that logarithmic time is not bounded by
any polynomial in unit time (`Cslib.RAM.exists_mul_pow_lt_of_computesInTime_logCost`).

A program computes a function within time `T` (`Cslib.RAM.ComputesInTime`) when on every input it
halts with the value of the function in the output register `0` (`Cslib.RAM.HaltsWithResult`)
after a run of time at most `T`. The time bound is a function of the input tuple, with no chosen
string encoding or input-length measure. Input loading and output extraction are free. For
example, the empty program returns its first preloaded input in time `0` under either measure.
The bit-length bound above therefore retains the initial-size term: it cannot in general be
replaced by a bound in execution time alone. These costs adapt Cook and Reckhow's conventions;
no Turing-machine simulation or equality of polynomial-time language classes is proved here.

The length of a number is `Cslib.RAM.bitLength n = ⌊log₂ n⌋ + 1`, its number of binary digits with
`0` written as one digit: it is `max n.size 1`, Mathlib's `Nat.size n` except at `0`
(`Cslib.RAM.bitLength_eq_max_size`). It is defined through `Nat.log`, which the kernel evaluates,
so that `decide` computes costs, and it is the `⌊log₂ n⌋ + 1` of the bounds of
`Cslib.polynomiallyBounded_two_pow_mul_log`. Cook and Reckhow's logarithmic function `l(n)` is
`⌈log₂ n⌉` for `n ≥ 2` and `1` below, so that `l(n) ≤ bitLength n ≤ 2 * l(n)`.

## Main definitions

* `Cslib.RAM.bitLength`: the length of a natural number.
* `Cslib.RAM.unitCost`, `Cslib.RAM.logCost`: the unit and the logarithmic cost measures.
* `Cslib.RAM.stepCost`: the cost of the next step of a program.
* `Cslib.RAM.time`: the time of a run of a given number of steps.
* `Cslib.RAM.HaltsWithResultInTime`, `Cslib.RAM.ComputesInTime`: halting with a given output, and
  computing a function, within a time bound.

## Main results

* `Cslib.RAM.time_add`: time is additive along a run.
* `Cslib.RAM.bitLength_eq_max_size`: the length of a number is `max n.size 1`.
* `Cslib.RAM.time_le_time_of_le`, `Cslib.RAM.time_mono_cost`, `Cslib.RAM.time_eq_of_le`: time is
  monotone in the number of steps and in the cost measure, and stationary once halted.
* `Cslib.RAM.time_unitCost`: unit time counts the steps taken.
* `Cslib.RAM.time_unitCost_le_time_logCost`: unit time is at most logarithmic time.
* `Cslib.RAM.bitLength_read_run_le`: the numbers held after a run of logarithmic time `T` are no
  longer than `T` or the longest number held at the start.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
-/

@[expose] public section

namespace Cslib.RAM

/-! ## The length of a number -/

/-- The length `⌊log₂ n⌋ + 1` of a natural number `n`: its number of binary digits, where `0` is
written with one digit. This is the logarithmic cost of storing `n`
[Cook and Reckhow, Section 1][CookReckhow1973]. It is `max n.size 1`
(`Cslib.RAM.bitLength_eq_max_size`), and is defined through `Nat.log` so that the kernel
evaluates it. -/
def bitLength (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- The length of a number is Mathlib's `Nat.size`, except that `0` has length `1`. -/
theorem bitLength_eq_max_size (n : ℕ) : bitLength n = max n.size 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · have h₁ : Nat.log 2 n < n.size := Nat.lt_size.2 (Nat.pow_log_le_self 2 hn.ne')
    have h₂ : n.size ≤ Nat.log 2 n + 1 :=
      Nat.size_le.2 (Nat.lt_pow_succ_log_self Nat.one_lt_two n)
    rw [bitLength]
    omega

theorem bitLength_eq_size {n : ℕ} (hn : n ≠ 0) : bitLength n = n.size := by
  have := Nat.size_pos.2 (Nat.pos_of_ne_zero hn)
  rw [bitLength_eq_max_size]
  omega

@[simp]
theorem bitLength_zero : bitLength 0 = 1 := rfl

theorem one_le_bitLength (n : ℕ) : 1 ≤ bitLength n := Nat.le_add_left 1 _

theorem bitLength_mono : Monotone bitLength := fun _ _ h => by
  simpa only [bitLength_eq_max_size] using max_le_max_right 1 (Nat.size_le_size h)

@[simp]
theorem bitLength_two_pow (k : ℕ) : bitLength (2 ^ k) = k + 1 := by
  rw [bitLength_eq_size (Nat.two_pow_pos k).ne', Nat.size_pow]

/-- A nonzero number has as many binary digits as its length. -/
theorem length_digits_two {n : ℕ} (hn : n ≠ 0) : (Nat.digits 2 n).length = bitLength n :=
  Nat.length_digits 2 n Nat.one_lt_two hn

theorem lt_two_pow_bitLength (n : ℕ) : n < 2 ^ bitLength n :=
  (Nat.lt_size_self n).trans_le <| Nat.pow_le_pow_right Nat.two_pos <|
    (bitLength_eq_max_size n).symm ▸ le_max_left _ _

theorem bitLength_le_iff {n k : ℕ} (hk : k ≠ 0) : bitLength n ≤ k ↔ n < 2 ^ k := by
  rw [bitLength_eq_max_size, max_le_iff, Nat.size_le]
  exact and_iff_left (Nat.one_le_iff_ne_zero.2 hk)

theorem bitLength_add_le (m n : ℕ) : bitLength (m + n) ≤ bitLength m + bitLength n := by
  have hm : 2 ≤ 2 ^ bitLength m := by
    simpa using Nat.pow_le_pow_right Nat.two_pos (one_le_bitLength m)
  have hn : 2 ≤ 2 ^ bitLength n := by
    simpa using Nat.pow_le_pow_right Nat.two_pos (one_le_bitLength n)
  rw [bitLength_le_iff (by have := one_le_bitLength m; omega), pow_add]
  have := lt_two_pow_bitLength m
  have := lt_two_pow_bitLength n
  nlinarith

theorem bitLength_mul_le (m n : ℕ) : bitLength (m * n) ≤ bitLength m + bitLength n := by
  rw [bitLength_le_iff (by have := one_le_bitLength m; omega), pow_add]
  exact mul_lt_mul'' (lt_two_pow_bitLength m) (lt_two_pow_bitLength n) (Nat.zero_le _)
    (Nat.zero_le _)

/-! ## Cost measures and time -/

/-- The unit cost measure charges every instruction one unit of time, whatever the size of the
numbers it manipulates. -/
def unitCost : Instr → URM.Regs → ℕ := fun _ _ => 1

/-- The logarithmic cost measure charges every instruction the lengths of the numbers it reads:
its constant, the contents of its operand registers, and, for an indirect operand, both the
address and the contents of the register at that address. This is Cook and Reckhow's measure
[Cook and Reckhow, Table I][CookReckhow1973] with `bitLength` for their `l`, multiplication charged
like addition, and a constant charged its length rather than `1`, so that the bound
`Cslib.RAM.bitLength_read_run_le` does not depend on the program. Register indices written in the
instruction are not charged, since they are bounded by the program. Neither is the number written:
it is never longer than the charge (`Cslib.RAM.bitLength_read_exec_le`). -/
def logCost : Instr → URM.Regs → ℕ
  | .const _ v, _ => bitLength v
  | .add _ i j, r => bitLength (r.read i) + bitLength (r.read j)
  | .sub _ i j, r => bitLength (r.read i) + bitLength (r.read j)
  | .mul _ i j, r => bitLength (r.read i) + bitLength (r.read j)
  | .load _ a, r => bitLength (r.read a) + bitLength (r.read (r.read a))
  | .store a i, r => bitLength (r.read a) + bitLength (r.read i)
  | .jpos i _, r => bitLength (r.read i)

/-- The cost of the next step of `p` from `s` under `cost`: the cost of the current instruction,
or `0` if `s` is halted. -/
def stepCost (cost : Instr → URM.Regs → ℕ) (p : Program) (s : State) : ℕ :=
  match p[s.pc]? with
  | some i => cost i s.regs
  | none => 0

/-- The time of the run of `p` from `s` for `n` steps under `cost`: the total cost of the
instructions it executes. Steps taken after the run halts cost nothing. -/
def time (cost : Instr → URM.Regs → ℕ) (p : Program) (n : ℕ) (s : State) : ℕ :=
  ∑ j ∈ Finset.range n, stepCost cost p (run p j s)

variable {cost cost' : Instr → URM.Regs → ℕ} {p : Program} {s : State} {b m n : ℕ}

theorem stepCost_of_getElem? {i : Instr} (h : p[s.pc]? = some i) :
    stepCost cost p s = cost i s.regs := by
  simp only [stepCost, h]

theorem stepCost_of_isHalted (h : s.isHalted p) : stepCost cost p s = 0 := by
  simp only [stepCost, List.getElem?_eq_none (State.isHalted_iff.mp h)]

theorem stepCost_mono (h : cost ≤ cost') : stepCost cost p s ≤ stepCost cost' p s := by
  unfold stepCost
  split
  · exact h _ _
  · exact le_rfl

@[simp]
theorem time_zero : time cost p 0 s = 0 := rfl

theorem time_succ : time cost p (n + 1) s = stepCost cost p s + time cost p n (step p s) := by
  simp only [time, Finset.sum_range_succ', run_succ, run_zero, Nat.add_comm]

theorem time_succ' : time cost p (n + 1) s = time cost p n s + stepCost cost p (run p n s) :=
  Finset.sum_range_succ _ _

/-- Time is additive along a run. -/
theorem time_add : time cost p (m + n) s = time cost p m s + time cost p n (run p m s) := by
  simp only [time, Finset.sum_range_add, run_add]

/-- A halted state takes no time. -/
theorem time_of_isHalted (h : s.isHalted p) : time cost p n s = 0 :=
  Finset.sum_eq_zero fun _ _ => by rw [run_of_isHalted h, stepCost_of_isHalted h]

/-- Once a run has halted, running longer takes no more time. -/
theorem time_eq_of_le (hmn : m ≤ n) (h : (run p m s).isHalted p) :
    time cost p n s = time cost p m s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [time_add, time_of_isHalted h, Nat.add_zero]

/-- Time is monotone in the number of steps. -/
theorem time_le_time_of_le (hmn : m ≤ n) : time cost p m s ≤ time cost p n s :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hmn)

/-- Time is monotone in the cost measure. -/
theorem time_mono_cost (h : cost ≤ cost') : time cost p n s ≤ time cost' p n s :=
  Finset.sum_le_sum fun _ _ => stepCost_mono h

/-! ### Unit cost -/

theorem stepCost_unitCost_le : stepCost unitCost p s ≤ 1 := by
  unfold stepCost
  split <;> simp [unitCost]

theorem stepCost_unitCost (h : ¬s.isHalted p) : stepCost unitCost p s = 1 := by
  have hlt : s.pc < p.length := by simpa using h
  exact stepCost_of_getElem? (List.getElem?_eq_getElem hlt)

/-- Unit time is at most the number of steps. -/
theorem time_unitCost_le : time unitCost p n s ≤ n :=
  (Finset.sum_le_sum fun j (_ : j ∈ Finset.range n) =>
    stepCost_unitCost_le (p := p) (s := run p j s)).trans_eq (by simp)

/-- Unit time counts the steps taken: a run that has not halted before its last step takes unit
time equal to its number of steps. -/
theorem time_unitCost (h : ∀ j < n, ¬(run p j s).isHalted p) : time unitCost p n s = n := by
  rw [time, Finset.sum_congr rfl fun j hj => stepCost_unitCost (h j (Finset.mem_range.mp hj))]
  simp

/-! ### Logarithmic cost -/

theorem one_le_logCost (i : Instr) (r : URM.Regs) : 1 ≤ logCost i r := by
  cases i with
  | const _ v => exact one_le_bitLength v
  | jpos i _ => exact one_le_bitLength _
  | _ => exact (one_le_bitLength _).trans (Nat.le_add_right _ _)

theorem unitCost_le_logCost : unitCost ≤ logCost := one_le_logCost

/-- Unit time is at most logarithmic time. -/
theorem time_unitCost_le_time_logCost : time unitCost p n s ≤ time logCost p n s :=
  time_mono_cost unitCost_le_logCost

private theorem bitLength_read_write_le {σ : URM.Regs} {c d v : ℕ}
    (hσ : ∀ r, bitLength (σ.read r) ≤ b) (hv : bitLength v ≤ c) (r : ℕ) :
    bitLength ((σ.write d v).read r) ≤ max b c := by
  by_cases h : r = d
  · subst h
    rw [URM.Regs.write_read_self]
    exact le_max_of_le_right hv
  · rw [URM.Regs.write_read_of_ne _ _ _ _ h]
    exact le_max_of_le_left (hσ r)

/-- An instruction writes no number longer than its logarithmic cost: if the registers of `s` hold
numbers of length at most `b`, then after executing `i` they hold numbers of length at most the
larger of `b` and the logarithmic cost of `i`. -/
theorem bitLength_read_exec_le (i : Instr) (hs : ∀ r, bitLength (s.regs.read r) ≤ b) (r : ℕ) :
    bitLength ((i.exec s).regs.read r) ≤ max b (logCost i s.regs) := by
  cases i with
  | const d v => exact bitLength_read_write_le hs le_rfl r
  | add d i j => exact bitLength_read_write_le hs (bitLength_add_le _ _) r
  | sub d i j =>
    exact bitLength_read_write_le hs
      ((bitLength_mono (Nat.sub_le _ _)).trans (Nat.le_add_right _ _)) r
  | mul d i j => exact bitLength_read_write_le hs (bitLength_mul_le _ _) r
  | load d a => exact bitLength_read_write_le hs (Nat.le_add_left _ _) r
  | store a i => exact bitLength_read_write_le hs (Nat.le_add_left _ _) r
  | jpos i q => exact le_max_of_le_left (hs r)

theorem bitLength_read_step_le (hs : ∀ r, bitLength (s.regs.read r) ≤ b) (r : ℕ) :
    bitLength ((step p s).regs.read r) ≤ max b (stepCost logCost p s) := by
  cases h : p[s.pc]? with
  | some i =>
    rw [step_of_getElem? h, stepCost_of_getElem? h]
    exact bitLength_read_exec_le i hs r
  | none =>
    rw [step, h]
    exact le_max_of_le_left (hs r)

/-- **Logarithmic cost bounds the numbers a RAM holds.** If the registers of `s` hold numbers of
length at most `b`, then after a run of logarithmic time `T` they hold numbers of length at most
the larger of `b` and `T`. This is the fact on which Cook and Reckhow's simulation of RAMs by
Turing machines rests [Cook and Reckhow, Section 4, Lemma][CookReckhow1973]. -/
theorem bitLength_read_run_le (hs : ∀ r, bitLength (s.regs.read r) ≤ b) (n r : ℕ) :
    bitLength ((run p n s).regs.read r) ≤ max b (time logCost p n s) := by
  induction n generalizing r with
  | zero => exact le_max_of_le_left (hs r)
  | succ n ih =>
    rw [run_succ', time_succ']
    refine (bitLength_read_step_le ih r).trans ?_
    omega

/-! ## Computing within a time bound -/

/-- `p` halts on `inputs` with `result` in the output register `0` within time `T` under `cost`:
its run from the initial state is halted after some number of steps, with `result` in register
`0`, and takes time at most `T` until then. -/
def HaltsWithResultInTime (cost : Instr → URM.Regs → ℕ) (p : Program) (inputs : List ℕ)
    (result T : ℕ) : Prop :=
  ∃ n, (run p n (State.init inputs)).isHalted p ∧
    (run p n (State.init inputs)).regs.output = result ∧ time cost p n (State.init inputs) ≤ T

/-- `p` computes the function `f` of `k` arguments within time `T` under `cost`: on every input
`x` it halts with `f x` in the output register `0` within time `T x`. As for URMs
(`Cslib.URM.Computes`), the arguments are the inputs in registers `0, …, k - 1`.
Initialization and output extraction are uncharged; `T` is indexed by the input tuple, not by a
specified string-encoding length. -/
def ComputesInTime (cost : Instr → URM.Regs → ℕ) (k : ℕ) (p : Program)
    (f T : (Fin k → ℕ) → ℕ) : Prop :=
  ∀ x : Fin k → ℕ, HaltsWithResultInTime cost p (List.ofFn x) (f x) (T x)

namespace HaltsWithResultInTime

variable {inputs : List ℕ} {result T T' : ℕ}

/-- A program halting with a result within a time bound halts with that result. -/
theorem haltsWithResult (h : HaltsWithResultInTime cost p inputs result T) :
    HaltsWithResult p inputs result :=
  let ⟨n, hn, hr, _⟩ := h
  haltsWithResult_iff_exists_run.2 ⟨n, hn, hr⟩

/-- A time bound can be increased. -/
theorem mono (h : HaltsWithResultInTime cost p inputs result T) (hT : T ≤ T') :
    HaltsWithResultInTime cost p inputs result T' :=
  let ⟨n, hn, hr, ht⟩ := h
  ⟨n, hn, hr, ht.trans hT⟩

/-- A cost measure can be decreased. -/
theorem mono_cost (h : HaltsWithResultInTime cost' p inputs result T) (hc : cost ≤ cost') :
    HaltsWithResultInTime cost p inputs result T :=
  let ⟨n, hn, hr, ht⟩ := h
  ⟨n, hn, hr, (time_mono_cost hc).trans ht⟩

end HaltsWithResultInTime

namespace ComputesInTime

variable {k : ℕ} {f T T' : (Fin k → ℕ) → ℕ}

/-- A program computing `f` evaluates to `f`. -/
theorem eval_eq (h : ComputesInTime cost k p f T) (x : Fin k → ℕ) :
    eval p (List.ofFn x) = .some (f x) :=
  haltsWithResult_iff_eval.1 (h x).haltsWithResult

/-- A time bound can be increased. -/
theorem mono (h : ComputesInTime cost k p f T) (hT : T ≤ T') : ComputesInTime cost k p f T' :=
  fun x => (h x).mono (hT x)

/-- A cost measure can be decreased. -/
theorem mono_cost (h : ComputesInTime cost' k p f T) (hc : cost ≤ cost') :
    ComputesInTime cost k p f T :=
  fun x => (h x).mono_cost hc

end ComputesInTime

end Cslib.RAM

end
