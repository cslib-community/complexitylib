/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.MassProduction.Uhlig
import Complexity.Foundations.Data.BitString.Parity

/-!
# Uhlig mass-production clients

These clients exercise the recovery code at equal and reversed requests, the vanishing boundary
position, a concrete instance of the layer recursion, families of different circuits on disjoint
blocks, and copy depths on both sides of the `d(n) log₂ n = o(n)` boundary. The theorem then
applies to a superpolynomial number of copies.
-/

namespace ComplexityTests.MassProduction.Uhlig

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.MassProduction
open Cslib.Circuits.Boolean.MassProduction.Uhlig Cslib.BitString.Uhlig Filter

/-! ### The recovery code -/

/-- The sequence `true, false, true` followed by zeros. -/
private def bits (i : ℕ) : Bool := i == 0 || i == 2

-- Adjacent sums, equal and reversed requests, recovery sums, non-overlapping requests, and the
-- vanishing boundary position.
example :
    (List.range 4).map (code bits) = [true, true, true, true] ∧
    (List.range 4).map (first 1 1) = [true, true, false, false] ∧
    (List.range 4).map (second 1 1) = [false, false, true, true] ∧
    (List.range 4).map (first 2 0) = [false, false, false, true] ∧
    (List.range 4).map (second 2 0) = [true, false, false, false] ∧
    ∑ j ∈ Finset.range 4, (first 2 0 j && code bits j) = bits 2 ∧
    ∑ j ∈ Finset.range 4, (second 2 0 j && code bits j) = bits 0 ∧
    second 1 1 0 = false ∧
    ∑ j ∈ Finset.Ico 1 3, code (fun _ => true) j ≠ true ∧
    restriction (0 : BooleanFunction (2 + 3)) 0 4 = false :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    sum_first_code (by decide) (by decide) 0,
    sum_second_code (by decide) (by decide) 2,
    second_eq_false_of_first (by decide : first 1 1 0 = true),
    by decide,
    restriction_two_pow 0 0⟩

/-! ### Circuit families -/

private def notGate : Circuit signature 1 1 := Circuit.oneGate .not (fun _ => 0)
private def andGate : Circuit signature 1 1 := ⟨.gate (.gate .empty
  ⟨.const true, Fin.elim0⟩) ⟨.and, fun i => if i = 0 then .input 0 else .gate 0⟩, fun _ => .gate 1⟩

-- Different members keep their own costs; the constant is charged by size but not by
-- nonconstant cost; the empty family has no gates.
example :
    (Circuit.parallelFamily ![notGate, andGate]).size = 3 ∧
    (Circuit.parallelFamily ![notGate, andGate]).program.cost nonconstantCost = 2 ∧
    (Circuit.parallelFamily ![notGate, andGate]).eval interpretation ![false, true] =
      ![true, true] ∧
    (Circuit.parallelFamily (Fin.elim0 : Fin 0 → Circuit signature 3 2)).size = 0 :=
  ⟨by simp [notGate, andGate, Fin.sum_univ_two],
    by rw [Circuit.cost_program_parallelFamily]; rfl,
    by decide,
    by simp⟩

/-! ### One layer -/

/-- A function of no inputs is a constant, which has one copy of size one. -/
private theorem complexity_directProduct_zero_inputs (g : BooleanFunction 0) :
    complexity interpretation (directProduct g 1) ≤ 1 :=
  complexity_directProduct_one_le.trans
    (Synthesis.of_forall_eq_const (s := inputs 0) (g ![])
      fun _ => congrArg g (Subsingleton.elim _ _)).complexity_le

-- Two copies of negation on one input, and four copies of conjunction on two inputs.
example : complexity interpretation (directProduct (fun x : BitString 1 => !x 0) (2 * 1)) ≤
    (2 ^ 1 + 1) * 1 + 1 * layerOverhead 1 0 :=
  complexity_directProduct_two_mul_le complexity_directProduct_zero_inputs _

example : complexity interpretation (directProduct (fun x : BitString 2 => x 0 && x 1) (2 ^ 2)) ≤
    (2 ^ 1 + 1) ^ 2 * (1 + 2 * 2 ^ 2 * layerOverhead 1 1) :=
  complexity_directProduct_two_pow_le (p := 1) (m := 0) (L := 1) (H := layerOverhead 1 1)
    complexity_directProduct_zero_inputs 2 _ rfl
    (fun e he => layerOverhead_mono (by omega)) _

/-! ### Copy depths -/

-- Single copies: Lupanov's coefficient one.
example : IsUhligDepth fun _ => 0 := fun _ => Eventually.of_forall fun _ => by simp

/-- `n / log₂² n` layers satisfy the depth condition, so `2 ^ (n / log₂² n)` copies of any
function, a superpolynomial number, fit within the asymptotic single-copy ceiling `2 ^ n / n`. -/
theorem isUhligDepth_div_log_sq : IsUhligDepth fun n => n / Nat.log 2 n ^ 2 := by
  intro c
  filter_upwards [eventually_ge_atTop (2 ^ (c + 1))] with n hn
  have hlog : c + 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  set L := Nat.log 2 n
  calc c * (n / L ^ 2) * L ≤ L * (n / L ^ 2) * L := by gcongr; omega
    _ = n / L ^ 2 * L ^ 2 := by ring
    _ ≤ n := Nat.div_mul_le_self n _

/-- With `n / log₂ n` layers the depth condition fails: the multiplier two is never met. -/
theorem not_isUhligDepth_div_log : ¬ IsUhligDepth fun n => n / Nat.log 2 n := by
  intro h
  obtain ⟨n, hn, h4⟩ := ((h 2).and (eventually_ge_atTop 4)).exists
  simp only at hn
  have hL : 0 < Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
  have hlt : n < n / Nat.log 2 n * Nat.log 2 n + Nat.log 2 n := Nat.lt_div_mul_add hL
  have hsmall : 2 * Nat.log 2 n ≤ n :=
    (Nat.mul_le_pow (by decide : 2 ≠ 1) _).trans (Nat.pow_log_le_self 2 (by omega))
  have e : 2 * (n / Nat.log 2 n) * Nat.log 2 n = 2 * (n / Nat.log 2 n * Nat.log 2 n) := by ring
  omega

-- A fixed parity family at the full superpolynomial copy budget, with scale factor two.
example : ∀ᶠ (n : ℕ) in atTop,
    ((2 * n : ℕ) : ℕ∞) * massComplexity (parity n) (2 ^ (n / Nat.log 2 n ^ 2)) ≤
      ((2 + 1) * 2 ^ n : ℕ) := by
  filter_upwards [eventually_mul_massComplexity_le isUhligDepth_div_log_sq 2] with n hn
  exact hn (parity n) _ le_rfl

-- Zero copies cost nothing even for the nonconstant parity function.
example : massComplexity (parity 5) 0 = 0 := massComplexity_zero

end ComplexityTests.MassProduction.Uhlig
