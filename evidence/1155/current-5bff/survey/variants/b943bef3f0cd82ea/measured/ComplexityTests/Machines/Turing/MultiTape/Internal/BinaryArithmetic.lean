/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Lean.Elab.Command


import Diag1155.Measure
/-! Direct binary arithmetic has no higher tidy calculus in its import environment. -/


diag1155_install
open Turing.MultiTapeTM

-- Production clients use the ordinary named certificate and direct composition.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hl : ComputableInPolyTime left input encNat)
    (hr : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a + right a) input encNat :=
  ComputableInPolyTime.binary_add.comp (hl.prod hr)

-- These backend fixtures opt in locally; they are not default-global automation claims.
section LocalAdditionAutomation
attribute [local fun_prop] ComputableInPolyTime.binary_add

example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hl : ComputableInPolyTime left input encNat)
    (hr : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a + right a) input encNat := by
  fail_if_success (clear hr; fun_prop)
  fail_if_success (clear hl; fun_prop)
  fun_prop

example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    (encPair encNat encNat) encNat := by fun_prop

end LocalAdditionAutomation

example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hl : ComputableInPolyTime left input encNat)
    (hr : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => decide (left a < right a)) input encBool := by
  fail_if_success (clear hl; fun_prop)
  exact ComputableInPolyTime.binary_lt.comp (hl.prod hr)

example : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
    (encPair encNat encNat) encBool := by fun_prop

-- The low direct import uses the named captured theorem; facade automation is checked separately.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hl : ComputableInPolyTime left input encNat)
    (hr : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a * right a) input encNat := by
  fail_if_success (clear hr; fun_prop)
  fail_if_success (clear hl; fun_prop)
  exact ComputableInPolyTime.binary_mul' hl hr

example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.2)
    (encPair encNat encNat) encNat :=
  ComputableInPolyTime.binary_mul' (ComputableInPolyTime.fst encNat encNat)
    (ComputableInPolyTime.snd encNat encNat)

-- The moved public word algorithm retains its defining data, not just an extensional theorem.
example (s : ℕ × ℕ) (a : Bool) :
    NatMul.mulStep s a = (if a then s.1 + s.2 else s.1, s.2 + s.2) := rfl

-- The unchanged multiply fold computes arbitrary shifted accumulators, including zero/empty.
example (m acc sh : ℕ) : (m.bits.foldl NatMul.mulStep (acc, sh)).1 = acc + m * sh :=
  NatMul.foldl_mulStep m acc sh

example : ((0 : ℕ).bits.foldl NatMul.mulStep (0, 7)).1 = 0 := rfl
example : NatMul.mulStep (0, 7) false = (0, 14) := rfl
example : NatMul.mulStep (0, 7) true = (7, 14) := rfl

-- Binary length, rather than a unary materialization of either numeric operand, controls the fold.
example (n : ℕ) :
    (((2 ^ n).bits).foldl NatMul.mulStep (0, 3)).1 = 2 ^ n * 3 := by
  simp only [NatMul.foldl_mulStep, zero_add]

example : (encNat (2 ^ 128)).length = 129 := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_pow]

-- Numerically exponential values still have linear-size binary inputs.
example (n : ℕ) : (encNat (2 ^ n)).length = n + 1 := by
  rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_pow]

-- All carry lengths are covered, without materializing a numeric-length unary counter.
example (n : ℕ) : NatAdd.addBits false (2 ^ n - 1).bits (1 : ℕ).bits = (2 ^ n).bits := by
  rw [NatAdd.addBits_bits]
  simp only [Bool.toNat_false, Nat.add_zero]
  congr 1
  have : 0 < 2 ^ n := by positivity
  omega

example : NatAdd.addBits false [] [] = [] := rfl
example : NatAdd.addBits false [true] [true] = [false, true] := rfl
example : decide ((0 : ℕ) < 0) = false := rfl
example : decide ((0 : ℕ) < 8) = true := rfl
example : decide ((8 : ℕ) < 1) = false := rfl

-- The pure highest-differing-bit law covers arbitrary binary lengths and zero operands.
example (m n : ℕ) : m < n ↔ ∃ i < n.size, m.testBit i = false ∧ n.testBit i = true ∧
    ∀ j < m.size + n.size, i < j → m.testBit j = n.testBit j := Nat.lt_iff_exists_testBit m n

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"

/-- info: 'Turing.MultiTapeTM.ComputableInPolyTime.binary_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.binary_add

/-- info: 'Turing.MultiTapeTM.ComputableInPolyTime.binary_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Turing.MultiTapeTM.ComputableInPolyTime.binary_lt
