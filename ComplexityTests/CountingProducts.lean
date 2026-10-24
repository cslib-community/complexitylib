/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP.Products
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! # Variable certificate lengths, signed factors and cancellation in uniform products -/

@[expose] public section

namespace Cslib.Complexity.Tests.CountingProducts

open Turing.MultiTapeTM Finset

/-- The certificate polynomial is quadratic in joint instance/index length. -/
def variableCount (x : List Bool × ℕ) : ℕ := 2 ^ ((2 * x.1.length + 1 + x.2) ^ 2 + 1)

private theorem variableCount_mem : variableCount ∈ SharpP (encPair encBits encUnary) := by
  convert SharpP.two_pow_mem (enc := encPair encBits encUnary) (Polynomial.X ^ 2 + 1) using 1
  ext x
  simp [variableCount, encBits_apply, encUnary_apply]

example : (fun w : List Bool => ∏ i ∈ range w.length, variableCount (w, i)) ∈ SharpP encBits :=
  SharpP.prod_range_mem variableCount_mem
    (.of_tidy (by simpa using ComputableTidilyInPolyTime.encoding_length encBits))

/-- The two factors use genuinely different certificate lengths: 10 and 17. -/
example : variableCount ([true], 0) = 2 ^ 10 ∧ variableCount ([true], 1) = 2 ^ 17 := by
  decide

/-- Empty indexed products equal one even when every possible factor is zero. -/
example : (fun _ : List Bool => ∏ _i ∈ range 0, (0 : ℕ)) ∈ SharpP encBits :=
  SharpP.prod_range_mem (SharpP.natCast_mem 0) (.of_tidy (ComputableTidilyInPolyTime.const 0))

example : (∏ _i ∈ range 0, (0 : ℕ)) = 1 := by simp

/-- A zero factor is counted exactly, rather than silently removed. -/
example : acceptCount (SharpP.indexedProductVerifier (fun _ : Unit => 2) (fun _ => 0)
    (fun x => decide (x.1.2 = 0))) () 0 = 0 := by
  change acceptCount _ () (2 * 0) = 0
  rw [SharpP.acceptCount_indexedProductVerifier]
  norm_num [acceptCount, Finset.prod_range_succ]

/-- Factors may vary with the index and may be negative. -/
def signedFactor (x : List Bool × ℕ) : ℤ := if x.2 = 0 then -2 else 3

private theorem signedFactor_mem : signedFactor ∈ GapP (encPair encBits encUnary) :=
  mem_GapP_of_polyTime (f := signedFactor) (.of_tidy (by unfold signedFactor; fun_prop))

example : (fun w : List Bool => ∏ i ∈ range w.length, signedFactor (w, i)) ∈ GapP encBits :=
  GapP.prod_range_mem signedFactor_mem
    (.of_tidy (by simpa using ComputableTidilyInPolyTime.encoding_length encBits))

example : (∏ i ∈ range 2, signedFactor ([], i)) = -6 := by decide

/-- Positive and negative counts overlap at every index; all later factors cancel exactly. -/
def cancelFactor (x : List Bool × ℕ) : ℤ := if x.2 = 0 then -1 else 0

private theorem cancelFactor_mem : cancelFactor ∈ GapP (encPair encBits encUnary) := by
  have h₁ : (fun x : List Bool × ℕ => if x.2 = 0 then (2 : ℕ) else 1) ∈
      SharpP (encPair encBits encUnary) := mem_SharpP_of_polyTime (.of_tidy (by fun_prop))
  have h₂ : (fun x : List Bool × ℕ => if x.2 = 0 then (3 : ℕ) else 1) ∈
      SharpP (encPair encBits encUnary) := mem_SharpP_of_polyTime (.of_tidy (by fun_prop))
  refine ⟨_, h₁, _, h₂, fun x => ?_⟩
  simp only [cancelFactor]
  split_ifs <;> norm_num

example : (fun w : List Bool => ∏ i ∈ range w.length, cancelFactor (w, i)) ∈ GapP encBits :=
  GapP.prod_range_mem cancelFactor_mem
    (.of_tidy (by simpa using ComputableTidilyInPolyTime.encoding_length encBits))

example : (∏ i ∈ range 0, cancelFactor ([], i)) = 1 ∧
    (∏ i ∈ range 1, cancelFactor ([], i)) = -1 ∧
    (∏ i ∈ range 2, cancelFactor ([], i)) = 0 := by decide

/-- info: 'Cslib.Complexity.SharpP.prod_range_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SharpP.prod_range_mem

/-- info: 'Cslib.Complexity.GapP.prod_range_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapP.prod_range_mem

/-- info: 'Cslib.Complexity.SharpP.ite_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.SharpP.ite_mem

/-- info: 'Cslib.Complexity.GapP.ite_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.GapP.ite_mem

end Cslib.Complexity.Tests.CountingProducts
