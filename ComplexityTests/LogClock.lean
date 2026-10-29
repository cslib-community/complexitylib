/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Computability.Complexity.Classes.Constructible.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.NatPolynomial
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

/-! Concrete binary-arithmetic clients of numeric time bounds and logarithmic clock inflation.
The zero-clock case checks that the closure rule does not silently require an input-length floor.
-/

public section

namespace ComplexityTests.LogClock

open Cslib.Complexity Turing.MultiTapeTM

/-- A padding-style guard, with both a passing and a failing boundary case below. -/
private def fits (p : ℕ × ℕ) : Bool := decide ((p.1 + 1) ^ 2 ≤ p.2)

example : fits (3, 15) = false ∧ fits (3, 16) = true ∧ fits (0, 0) = false := by decide

example : ComputableInO fits (encPair encNat encNat) encBool (fun p => p.1 + p.2)
    fun p => p.1 + p.2 := by
  apply ComputableInPolyTime.natPair_inO
  apply ComputableInPolyTime.of_tidy
  change ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide ((p.1 + 1) ^ 2 ≤ p.2))
    (encPair encNat encNat) encBool
  have hsucc := ComputableTidilyInPolyTime.binary_add'
    (ComputableTidilyInPolyTime.fst encNat encNat) (ComputableTidilyInPolyTime.const 1)
  simpa only [sq] using ComputableTidilyInPolyTime.binary_le'
    (ComputableTidilyInPolyTime.binary_mul' hsucc hsucc)
    (ComputableTidilyInPolyTime.snd encNat encNat)

/-- Binary-polynomial postprocessing gives the expected exponential clock. -/
example : TimeConstructible fun n => 2 ^ (2 * n) := by
  have hmul : ComputableInPolyTime (fun m : ℕ => m * m) encNat encNat := by
    apply ComputableInPolyTime.of_tidy
    exact ComputableTidilyInPolyTime.binary_mul'
      ComputableTidilyInPolyTime.id' ComputableTidilyInPolyTime.id'
  have h := timeConstructible_two_pow.comp_of_computableInPolyTime hmul
    (fun _ => Nat.le_mul_of_pos_right _ Nat.one_le_two_pow)
  have heq : (fun n : ℕ => 2 ^ n * 2 ^ n) = (fun n => 2 ^ (2 * n)) := by
    funext n
    rw [two_mul, pow_add]
  rw [heq] at h
  exact h

/-- The binary length of `2 ^ n` turns logarithmic inflation into an exact linear factor. -/
theorem inflated_exponential : TimeConstructible fun n => 2 ^ n * (n + 2) := by
  simpa only [Nat.size_pow, Nat.add_assoc] using timeConstructible_two_pow.mul_size_succ

/-- Zero values remain valid clocks: no positivity or input-length hypothesis is needed. -/
example : TimeConstructible fun _ => 0 := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_of_const (encIn := encBits) (encOut := encNat) 0
  have hzero : TimeConstructible fun _ => 0 := by
    refine ⟨c, fun _ => 0, ?_⟩
    change ComputableInTimeAndSpace (fun _ : List Bool => 0) encBits encNat
      (fun _ => c * 0 + c) fun _ => 0
    simpa only [Nat.mul_zero, Nat.zero_add, Function.const_def] using hc
  simpa only [Nat.zero_mul] using hzero.mul_size_succ

end ComplexityTests.LogClock
