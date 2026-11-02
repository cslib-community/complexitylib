/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Constructible
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Streaming
import Complexity.Foundations.Data.Nat.Doubling
import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes
import Complexity.Computability.Machines.Turing.MultiTape.Run

/-!
# Unary clocks of linear length from time-constructible bounds

A time-constructible bound `T` is computed in binary within `O(T n)` steps
(`Cslib.Complexity.TimeConstructible`). Some constructions need a clock in unary instead: a run of
true cells on a work tape that a machine consumes one cell per step. Converting `T n` exactly
from binary to unary by counting down takes `O((T n + 1) ^ 2)` steps
(`Turing.MultiTapeTM.ComputableInO.natToUnary`), which is too slow for linear clocks.

Rounding up to a power of two avoids the conversion. The binary word of `T n` has
`Nat.size (T n)` digits, and doubling a unary counter once per digit writes
`c * 2 ^ Nat.size (T n)` cells. The `i`-th doubling costs `O(c * 2 ^ i)`, so the doublings cost
`O(c * 2 ^ Nat.size (T n)) = O(T n + 1)` together. The rounded clock lies between
`c * (T n + 1)` and `c * (2 * T n + 1)` (`Nat.two_pow_size_le`).

`Cslib.Complexity.TimeConstructible.exists_prepare_unaryClock` packages this as one deterministic
machine that writes the clock on its last work tape within `O(T n)` steps, leaving every other
work tape blank, its input head at the start and nothing emitted. This mirrors the polynomial
budget of `MultiTape.Plumbing.PrepareClock`.

## Main results

* `Cslib.Complexity.TimeConstructible.exists_prepare_unaryClock`: a unary clock of
  `c * 2 ^ Nat.size (T n)` cells within `O(T n)` steps.
-/

public section

namespace Turing.MultiTapeTM.ComputableTidilyInO

/-- The geometric sum of powers of two below `2 ^ n`. -/
private theorem sum_range_two_pow_lt (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- **`c * 2 ^ l.length` in unary in linear time.** A streaming fold doubles a unary counter once
per bit of `l`. Round `i` costs `O(c * 2 ^ i)`, so the rounds cost `O(c * 2 ^ l.length)` in total,
plus `O(l.length)` for the scan. The tidy realization is private to this file; the public result
is the plain preparation theorem below. -/
private theorem mul_two_pow_length (c : ℕ) :
    ComputableTidilyInO (fun l : List Bool => c * 2 ^ l.length) encBits encUnary
      (fun l => c * 2 ^ l.length + l.length) fun l => c * 2 ^ l.length + l.length := by
  obtain ⟨c₀, hstep, -⟩ := ((ComputableInDegree.unaryAdd (ComputableInDegree.fst encUnary encBool)
    (ComputableInDegree.fst encUnary encBool) le_rfl le_rfl).inO_one).tidy
  have hstate (l : List Bool) (i : ℕ) (hi : i ≤ l.length) :
      (encUnary ((l.take i).foldl (fun m _ => m + m) c)).length = c * 2 ^ i := by
    rw [List.foldl_add_self_eq_mul_two_pow, encUnary_apply, List.length_replicate, List.length_take,
      Nat.min_eq_left hi]
  obtain ⟨K, hK⟩ := ComputableTidilyInTimeAndSpace.foldl_bits_stream_sum (enc := encUnary)
    (step := fun m (_ : Bool) => m + m) c hstep
    (R := fun _ i => (5 * c₀ + 4) * (c * 2 ^ i + 1))
    (Q := fun l => c₀ * (2 * (c * 2 ^ l.length) + 3))
    (B := fun l => c * 2 ^ l.length)
    (fun l i hi => by
      have h₁ := hstate l i hi.le
      have h₂ := hstate l (i + 1) hi
      simp only [length_encPair, encBool_apply, List.length_singleton, h₁, h₂, pow_succ]
      nlinarith)
    (fun l i hi => by
      have h₁ := hstate l i hi.le
      have hpow : c * 2 ^ i ≤ c * 2 ^ l.length :=
        Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by norm_num) hi.le)
      simp only [length_encPair, encBool_apply, List.length_singleton, h₁]
      nlinarith)
    (fun l i hi => by
      rw [hstate l i hi]
      exact Nat.mul_le_mul_left c (Nat.pow_le_pow_right (by norm_num) hi))
  refine of_bounds (hK.of_enc_eq (g := fun l : List Bool => c * 2 ^ l.length)
    fun l => by rw [List.foldl_add_self_eq_mul_two_pow])
    (K * (5 * c₀ + 5) + K * (3 * c₀ + 3) + 1) (fun l => ?_) (fun l => ?_) fun l => ?_
  · have hsum := sum_range_two_pow_lt l.length
    have hs : ∑ i ∈ Finset.range l.length, (5 * c₀ + 4) * (c * 2 ^ i + 1) ≤
        (5 * c₀ + 4) * (c * 2 ^ l.length + l.length) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_range, smul_eq_mul, mul_one]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left c hsum.le) _)
    have h₁ : ∑ i ∈ Finset.range l.length, (5 * c₀ + 4) * (c * 2 ^ i + 1) + c * 2 ^ l.length + 1
        ≤ (5 * c₀ + 5) * (c * 2 ^ l.length + l.length + 1) := by
      have e : (5 * c₀ + 5) * (c * 2 ^ l.length + l.length + 1) =
          (5 * c₀ + 4) * (c * 2 ^ l.length + l.length) + (c * 2 ^ l.length + l.length) +
            (5 * c₀ + 5) := by ring
      rw [e]
      omega
    calc K * (∑ i ∈ Finset.range l.length, (5 * c₀ + 4) * (c * 2 ^ i + 1) + c * 2 ^ l.length + 1)
        ≤ K * ((5 * c₀ + 5) * (c * 2 ^ l.length + l.length + 1)) := Nat.mul_le_mul_left K h₁
      _ = K * (5 * c₀ + 5) * (c * 2 ^ l.length + l.length + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · have h₁ : c₀ * (2 * (c * 2 ^ l.length) + 3) + c * 2 ^ l.length + 1 ≤
        (3 * c₀ + 3) * (c * 2 ^ l.length + l.length + 1) := by
      have e : (3 * c₀ + 3) * (c * 2 ^ l.length + l.length + 1) =
          c₀ * (2 * (c * 2 ^ l.length) + 3) + c₀ * (c * 2 ^ l.length) + 3 * c₀ * l.length +
            3 * (c * 2 ^ l.length + l.length + 1) := by ring
      rw [e]
      omega
    calc K * (c₀ * (2 * (c * 2 ^ l.length) + 3) + c * 2 ^ l.length + 1)
        ≤ K * ((3 * c₀ + 3) * (c * 2 ^ l.length + l.length + 1)) := Nat.mul_le_mul_left K h₁
      _ = K * (3 * c₀ + 3) * (c * 2 ^ l.length + l.length + 1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  · simp only [encUnary_apply, List.length_replicate]
    calc c * 2 ^ l.length ≤ 1 * (c * 2 ^ l.length + l.length + 1) := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

end Turing.MultiTapeTM.ComputableTidilyInO

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM

/-- **A unary clock of linear length.** For a time-constructible `T` and a constant `c`, one
deterministic machine with finitely many states writes `c * 2 ^ Nat.size (T n)` true cells on its
last work tape within `C * T n + C` steps, on every input of length `n`. It halts with every other
work tape blank, all heads at their starting cells and nothing emitted. The clock has between
`c * (T n + 1)` and `c * (2 * T n + 1)` cells (`Nat.lt_size_self`, `Nat.two_pow_size_le`). -/
theorem TimeConstructible.exists_prepare_unaryClock {T : ℕ → ℕ} (hT : TimeConstructible T)
    (c : ℕ) :
    ∃ (r : ℕ) (State : Type) (_ : Finite State) (machine : MultiTapeTM (r + 1) Bool State)
      (C : ℕ), ∀ input,
      machine.runFrom (machine.initCfg input) (C * T input.length + C) =
        wordsCfg input none (Function.update (fun _ => []) (Fin.last r)
          (List.replicate (c * 2 ^ Nat.size (T input.length)) true)) [] := by
  have hbits : ComputableTidilyInO (fun x : List Bool => encNat (T x.length)) encBits encBits
      (fun x => T x.length) fun x => T x.length :=
    hT.computableInO.tidy.of_enc_eq fun _ => rfl
  have hclock := ((ComputableTidilyInO.mul_two_pow_length c).comp hbits).of_enc_eq
    (g := fun x : List Bool => List.replicate (c * 2 ^ Nat.size (T x.length)) true)
    (encOut := encBits) fun x => by
      simp [encUnary_apply, encNat_apply, Nat.size_eq_bits_len]
  have hdigits (m : ℕ) : (encNat m).length = Nat.size m := by
    rw [encNat_apply, Nat.size_eq_bits_len]
  have hlinear (x : List Bool) : T x.length + (c * 2 ^ (encNat (T x.length)).length +
      (encNat (T x.length)).length) ≤ (2 * c + 2) * (T x.length + 1) := by
    have h₁ := Nat.mul_le_mul_left c (Nat.two_pow_size_le (T x.length))
    have h₂ : Nat.size (T x.length) ≤ T x.length := Nat.size_le.mpr Nat.lt_two_pow_self
    rw [hdigits]
    have e : (2 * c + 2) * (T x.length + 1) = c * (2 * T x.length + 1) + c +
        2 * (T x.length + 1) := by ring
    rw [e]
    omega
  obtain ⟨c₁, ⟨r, State, hfinite, machine, hmachine⟩, -⟩ := hclock.mono (2 * c + 2)
    (T' := fun x => T x.length) (S' := fun x => T x.length) hlinear hlinear
  refine ⟨r, State ⊕ RewindWorkState, inferInstance, machine.outputToWord, c₁ + 2 * c + 2,
    fun input => ?_⟩
  have hbound : c₁ * (T input.length + 1) +
      (List.replicate (c * 2 ^ Nat.size (T input.length)) true).length + 2 ≤
      (c₁ + 2 * c + 2) * T input.length + (c₁ + 2 * c + 2) := by
    have h₁ := Nat.mul_le_mul_left c (Nat.two_pow_size_le (T input.length))
    rw [List.length_replicate]
    have e : (c₁ + 2 * c + 2) * T input.length + (c₁ + 2 * c + 2) =
        c₁ * (T input.length + 1) + c * (2 * T input.length + 1) + c + 2 * T input.length + 2 := by
      ring
    rw [e]
    omega
  have hwrite := (hmachine input).outputToWord.mono hbound le_rfl
  obtain ⟨_, _, hrun, ⟨rfl, rfl⟩, _⟩ :=
    transformsTapes_iff_runFrom.mp hwrite input (fun _ => []) [] ⟨rfl, rfl⟩
  simpa only [initCfg_eq_wordsCfg, encBits_apply, List.nil_append] using hrun

end Cslib.Complexity
