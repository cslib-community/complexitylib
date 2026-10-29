/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Lean.Elab.Command

/-! Direct binary arithmetic has no higher tidy calculus in its import environment. -/

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
    ComputableInPolyTime (fun a => left a + right a) input encNat ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat := by
  refine ⟨?_, by fun_prop⟩
  fail_if_success (clear hr; fun_prop)
  fail_if_success (clear hl; fun_prop)
  fun_prop

end LocalAdditionAutomation

-- Comparison, multiplication, and concrete bit-level arithmetic laws.
example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hl : ComputableInPolyTime left input encNat)
    (hr : ComputableInPolyTime right input encNat)
    (s : ℕ × ℕ) (a : Bool) (m acc sh n : ℕ) :
    ComputableInPolyTime (fun a => decide (left a < right a)) input encBool ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2)) (encPair encNat encNat) encBool ∧
    ComputableInPolyTime (fun a => left a * right a) input encNat ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.2) (encPair encNat encNat) encNat ∧
    NatMul.mulStep s a = (if a then s.1 + s.2 else s.1, s.2 + s.2) ∧
    (m.bits.foldl NatMul.mulStep (acc, sh)).1 = acc + m * sh ∧
    ((0 : ℕ).bits.foldl NatMul.mulStep (0, 7)).1 = 0 ∧
    NatMul.mulStep (0, 7) false = (0, 14) ∧
    NatMul.mulStep (0, 7) true = (7, 14) ∧
    (((2 ^ n).bits).foldl NatMul.mulStep (0, 3)).1 = 2 ^ n * 3 ∧
    (encNat (2 ^ 128)).length = 129 ∧
    (encNat (2 ^ n)).length = n + 1 ∧
    NatAdd.addBits false (2 ^ n - 1).bits (1 : ℕ).bits = (2 ^ n).bits ∧
    NatAdd.addBits false [] [] = [] ∧
    NatAdd.addBits false [true] [true] = [false, true] ∧
    decide ((0 : ℕ) < 0) = false ∧
    decide ((0 : ℕ) < 8) = true ∧
    decide ((8 : ℕ) < 1) = false ∧
    (m < n ↔ ∃ i < n.size, m.testBit i = false ∧ n.testBit i = true ∧
      ∀ j < m.size + n.size, i < j → m.testBit j = n.testBit j) := by
  refine ⟨?_, by fun_prop, ?_,
    ComputableInPolyTime.binary_mul' (ComputableInPolyTime.fst encNat encNat)
      (ComputableInPolyTime.snd encNat encNat),
    rfl, NatMul.foldl_mulStep m acc sh, rfl, rfl, rfl,
    by simp only [NatMul.foldl_mulStep, zero_add],
    by rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_pow],
    by rw [encNat_apply, Nat.size_eq_bits_len, Nat.size_pow],
    ?_, rfl, rfl, rfl, rfl, rfl, Nat.lt_iff_exists_testBit m n⟩
  · fail_if_success (clear hl; fun_prop)
    exact ComputableInPolyTime.binary_lt.comp (hl.prod hr)
  · fail_if_success (clear hr; fun_prop)
    fail_if_success (clear hl; fun_prop)
    exact ComputableInPolyTime.binary_mul' hl hr
  · rw [NatAdd.addBits_bits]
    simp only [Bool.toNat_false, Nat.add_zero]
    congr 1
    have : 0 < 2 ^ n := by positivity
    omega

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInO, `Turing.MultiTapeTM.ComputableTidilyInDegree] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
