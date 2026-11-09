/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.RAM.Cost
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Repeated squaring separates unit and logarithmic cost

The unit cost measure charges a RAM one unit per instruction, however large the numbers involved.
With multiplication it need not be polynomially comparable to logarithmic cost. The fixed program
`Cslib.RAM.repeatedSquaring` reads `k` in register `0`, puts `2` in register `1`, then squares
register `1` while counting register `0` down to
zero, and copies the result to register `0`: it computes `k ↦ 2 ^ 2 ^ k` within unit time
`4 k + 5`, taking exactly `4 k + 5` steps. The value `2 ^ 2 ^ k` has `2 ^ k + 1` binary digits,
and logarithmic time bounds the length of every number a RAM holds
(`Cslib.RAM.bitLength_read_run_le`), so every program computing `k ↦ 2 ^ 2 ^ k`, this one
included, takes logarithmic time more than `2 ^ k` on input `k`. Hence no polynomial in the unit
time `4 k + 5` bounds the logarithmic time of any program computing this function: unit time and
logarithmic time are not polynomially related.

Hartmanis and Simon showed much more: under unit cost, RAMs with multiplication and bitwise
Boolean operations decide in polynomial time exactly the languages that Turing machines decide in
polynomial space [Hartmanis and Simon][HartmanisSimon1974]. Without multiplication, an
instruction other than loading a constant at most doubles the largest number held. To obtain a
polynomial comparison from this observation, one must also control the initial bit lengths.
Cook and Reckhow use charged input instructions on finite-alphabet strings and time bounds at
least the input length [Cook and Reckhow, Section 1 and Theorem 2][CookReckhow1973]. Here inputs
are arbitrary natural numbers preloaded for free: a single addition has unit cost `1` but
unbounded logarithmic cost across inputs. Thus no bound in unit time alone follows in this API.
Neither the cited complexity-class result nor a RAM-to-Turing-machine simulation is formalized
here. The parameter `k` in the proved separation is the input's numeric value, not its binary
encoding length.

## Main definitions

* `Cslib.RAM.repeatedSquaring`: the program computing `k ↦ 2 ^ 2 ^ k` by repeated squaring.

## Main results

* `Cslib.RAM.run_repeatedSquaring`: the state in which the program halts on input `k`.
* `Cslib.RAM.computesInTime_unitCost_repeatedSquaring`,
  `Cslib.RAM.time_unitCost_repeatedSquaring`: the program computes `k ↦ 2 ^ 2 ^ k` within unit
  time `4 k + 5`, and its run takes exactly that time.
* `Cslib.RAM.two_pow_lt_of_computesInTime_logCost`,
  `Cslib.RAM.two_pow_lt_time_logCost_repeatedSquaring`: every program computing `k ↦ 2 ^ 2 ^ k`
  within logarithmic time `T` has `2 ^ k < T k`; in particular the run of `repeatedSquaring` on
  `k` takes logarithmic time more than `2 ^ k`.
* `Cslib.RAM.exists_mul_pow_lt_of_computesInTime_logCost`: the logarithmic time of a program
  computing `k ↦ 2 ^ 2 ^ k` is bounded by no polynomial in the unit time `4 k + 5`.

## References

* [S. A. Cook and R. A. Reckhow, *Time bounded random access machines*][CookReckhow1973]
* [J. Hartmanis and J. Simon, *On the power of multiplication in random access
  machines*][HartmanisSimon1974]
-/

@[expose] public section

namespace Cslib.RAM

/-- The repeated-squaring program. With `k` in register `0`, it puts `2` in register `1` and `1`
in register `2` (instructions `0` and `1`); while register `0` is positive, it squares register `1`
and decrements register `0` (instructions `2` and `4` to `6`); then it copies register `1` into
register `0` (instructions `3` and `7`). Register `2` holds the constant `1`, which makes the
jumps at instructions `3` and `6` unconditional. -/
def repeatedSquaring : Program :=
  [.const 1 2, .const 2 1, .jpos 0 4, .jpos 2 7, .mul 1 1 1, .sub 0 0 2, .jpos 2 2, .add 0 1 0]

@[simp]
theorem length_repeatedSquaring : repeatedSquaring.length = 8 := rfl

/-- The first two steps load the constants. -/
theorem run_two_repeatedSquaring (k : ℕ) :
    run repeatedSquaring 2 (State.init [k]) = ⟨2, URM.Regs.ofInputs [k, 2, 1]⟩ := by
  ext1
  · rfl
  · funext r
    rcases r with _ | _ | _ | r <;> rfl

/-- One round of the loop squares register `1` and decrements register `0`. -/
theorem run_four_repeatedSquaring (a b : ℕ) :
    run repeatedSquaring 4 ⟨2, URM.Regs.ofInputs [a + 1, b, 1]⟩ =
      ⟨2, URM.Regs.ofInputs [a, b * b, 1]⟩ := by
  ext1
  · rfl
  · funext r
    rcases r with _ | _ | _ | r <;> rfl

/-- After `j ≤ k` rounds of the loop, register `0` holds `k - j` and register `1` holds
`2 ^ 2 ^ j`. -/
theorem run_four_mul_repeatedSquaring {j k : ℕ} (hj : j ≤ k) :
    run repeatedSquaring (4 * j) ⟨2, URM.Regs.ofInputs [k, 2, 1]⟩ =
      ⟨2, URM.Regs.ofInputs [k - j, 2 ^ 2 ^ j, 1]⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    obtain ⟨a, ha⟩ : ∃ a, k - j = a + 1 := ⟨k - j - 1, by omega⟩
    rw [Nat.mul_succ, run_add, ih (by omega), ha, run_four_repeatedSquaring,
      show k - (j + 1) = a by omega, ← pow_two, ← pow_mul, pow_succ]

/-- Once register `0` is zero, the loop exits at instruction `3`. -/
theorem run_four_mul_add_four_repeatedSquaring (k : ℕ) :
    run repeatedSquaring (4 * k + 4) (State.init [k]) =
      ⟨7, URM.Regs.ofInputs [0, 2 ^ 2 ^ k, 1]⟩ := by
  rw [show 4 * k + 4 = 2 + 4 * k + 2 by omega, run_add, run_add, run_two_repeatedSquaring,
    run_four_mul_repeatedSquaring le_rfl, Nat.sub_self]
  rfl

/-- **The run of the repeated-squaring program**: on input `k`, it halts after `4 k + 5` steps
with `2 ^ 2 ^ k` in registers `0` and `1`. -/
theorem run_repeatedSquaring (k : ℕ) :
    run repeatedSquaring (4 * k + 5) (State.init [k]) =
      ⟨8, URM.Regs.ofInputs [2 ^ 2 ^ k, 2 ^ 2 ^ k, 1]⟩ := by
  rw [run_succ', run_four_mul_add_four_repeatedSquaring]
  ext1
  · rfl
  · funext r
    rcases r with _ | _ | _ | r
    · exact Nat.add_zero _
    all_goals rfl

/-- On input `k`, the program halts after `4 k + 5` steps. -/
theorem isHalted_run_repeatedSquaring (k : ℕ) :
    (run repeatedSquaring (4 * k + 5) (State.init [k])).isHalted repeatedSquaring := by
  simp [run_repeatedSquaring]

/-- On input `k`, the program halts with `2 ^ 2 ^ k` in the output register `0`. -/
theorem output_run_repeatedSquaring (k : ℕ) :
    (run repeatedSquaring (4 * k + 5) (State.init [k])).regs.output = 2 ^ 2 ^ k := by
  rw [run_repeatedSquaring]
  rfl

/-- Under unit cost, the run on `k` takes time `4 k + 5`: it halts after `4 k + 5` steps and not
before. -/
theorem time_unitCost_repeatedSquaring (k : ℕ) :
    time unitCost repeatedSquaring (4 * k + 5) (State.init [k]) = 4 * k + 5 := by
  refine time_unitCost fun j hj hhalt => ?_
  have h := run_eq_of_le (show j ≤ 4 * k + 4 by omega) hhalt
  rw [run_four_mul_add_four_repeatedSquaring] at h
  rw [← h] at hhalt
  simp at hhalt

/-- **Repeated squaring computes `k ↦ 2 ^ 2 ^ k` within unit time `4 k + 5`.** -/
theorem computesInTime_unitCost_repeatedSquaring :
    ComputesInTime unitCost 1 repeatedSquaring (fun x => 2 ^ 2 ^ x 0) fun x => 4 * x 0 + 5 :=
  fun x => by
    rw [show List.ofFn x = [x 0] by simp]
    exact ⟨4 * x 0 + 5, isHalted_run_repeatedSquaring _, output_run_repeatedSquaring _,
      (time_unitCost_repeatedSquaring _).le⟩

/-- **Computing `2 ^ 2 ^ k` takes logarithmic time more than `2 ^ k`.** Every program computing
`k ↦ 2 ^ 2 ^ k` within logarithmic time `T` has `2 ^ k < T k`: the output has `2 ^ k + 1` binary
digits, and a run of logarithmic time `T` holds no number longer than `T` or than the input
(`Cslib.RAM.bitLength_read_run_le`). -/
theorem two_pow_lt_of_computesInTime_logCost {p : Program} {T : (Fin 1 → ℕ) → ℕ}
    (h : ComputesInTime logCost 1 p (fun x => 2 ^ 2 ^ x 0) T) (x : Fin 1 → ℕ) :
    2 ^ x 0 < T x := by
  obtain ⟨n, -, hout, htime⟩ := h x
  have hx : List.ofFn x = [x 0] := by simp
  rw [hx] at hout htime
  have hread : (run p n (State.init [x 0])).regs.read 0 = 2 ^ 2 ^ x 0 := hout
  have hinit (r : ℕ) : bitLength ((State.init [x 0]).regs.read r) ≤ bitLength (x 0) := by
    rcases r with _ | r
    · exact le_rfl
    · change bitLength 0 ≤ _
      exact one_le_bitLength _
  have hlen := bitLength_read_run_le (p := p) hinit n 0
  rw [hread, bitLength_two_pow] at hlen
  have hx0 : bitLength (x 0) ≤ 2 ^ x 0 :=
    (bitLength_le_iff (Nat.two_pow_pos _).ne').2
      (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right Nat.two_pos Nat.lt_two_pow_self.le))
  omega

/-- Under logarithmic cost, the run of the repeated-squaring program on `k` takes time more than
`2 ^ k`. -/
theorem two_pow_lt_time_logCost_repeatedSquaring (k : ℕ) :
    2 ^ k < time logCost repeatedSquaring (4 * k + 5) (State.init [k]) :=
  two_pow_lt_of_computesInTime_logCost (p := repeatedSquaring)
    (T := fun x => time logCost repeatedSquaring (4 * x 0 + 5) (State.init [x 0]))
    (fun x => by
      rw [show List.ofFn x = [x 0] by simp]
      exact ⟨4 * x 0 + 5, isHalted_run_repeatedSquaring _, output_run_repeatedSquaring _, le_rfl⟩)
    ![k]

/-- **Unit cost is unsound.** The repeated-squaring program computes `k ↦ 2 ^ 2 ^ k` within unit
time `4 k + 5` (`Cslib.RAM.computesInTime_unitCost_repeatedSquaring`), but the logarithmic time
`T` of any program computing it is bounded by no polynomial in `4 k + 5`: for all `c` and `d`,
some input `k` has `c (4 k + 5) ^ d < T k`. -/
theorem exists_mul_pow_lt_of_computesInTime_logCost {p : Program} {T : (Fin 1 → ℕ) → ℕ}
    (h : ComputesInTime logCost 1 p (fun x => 2 ^ 2 ^ x 0) T) (c d : ℕ) :
    ∃ x : Fin 1 → ℕ, c * (4 * x 0 + 5) ^ d < T x := by
  have hpoly : PolynomiallyBounded fun k => c * (4 * k + 5) ^ d :=
    polynomiallyBounded_iff_le.2 ⟨c * 5 ^ d, d, fun k => by
      rw [mul_assoc, ← mul_pow]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)⟩
  obtain ⟨k, hk⟩ := hpoly.eventually_lt_two_pow.exists
  exact ⟨![k], hk.trans (two_pow_lt_of_computesInTime_logCost h ![k])⟩

end Cslib.RAM

end
