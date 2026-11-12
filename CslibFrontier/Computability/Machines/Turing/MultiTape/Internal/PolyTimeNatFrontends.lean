/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeUnaryPrimitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.GetD

/-!
# Direct unary comparison and bit-access frontends

These canonical interfaces use direct unary iteration (`ComputableInPolyTime.iterate`): unary
subtraction iterates predecessor, unary-to-binary conversion iterates the binary successor, and
indexed access iterates the word tail before using the existing head codec. No higher tidy calculus
supplies a plain primitive.
-/

public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Truncated subtraction of unary naturals. -/
@[fun_prop]
theorem unary_sub :
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1 - p.2)
      (encPair encUnary encUnary) encUnary := by
  have h := iterate (count := Prod.snd) (init := Prod.fst) (step := Nat.pred)
    (snd encUnary encUnary) (fst encUnary encUnary)
    ComputableInDegree.unary_pred.computableInPolyTime
    (bound := fun p => (encPair encUnary encUnary p).length) .self (fun p i _ => by
      rw [Nat.pred_iterate]
      simp only [encPair_apply, encUnary_apply, List.length_append, length_frame,
        List.length_replicate]
      omega)
  simpa only [Nat.pred_iterate] using h

/-- Comparison of unary naturals. -/
@[fun_prop]
theorem unary_le :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
      (encPair encUnary encUnary) encBool := by
  simpa only [Function.comp_def, Nat.sub_eq_zero_iff_le] using
    ComputableInDegree.unary_isZero.computableInPolyTime.comp unary_sub

/-- Strict comparison of unary naturals. -/
@[fun_prop]
theorem unary_lt :
    ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
      (encPair encUnary encUnary) encBool := by
  simpa only [Function.comp_def, ← decide_not, Nat.not_le] using bool_not.comp
    (unary_le.comp ((snd encUnary encUnary).prod (fst encUnary encUnary)))

/-- Compare computed unary values, with both operand encodings fixed. -/
@[fun_prop]
theorem unary_le' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => decide (left a ≤ right a)) input encBool :=
  unary_le.comp (hleft.prod hright)

/-- Strictly compare computed unary values, with both operand encodings fixed. -/
@[fun_prop]
theorem unary_lt' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => decide (left a < right a)) input encBool :=
  unary_lt.comp (hleft.prod hright)

/-- Convert a unary natural to its binary encoding. -/
@[fun_prop]
theorem unary_to_binary : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat := by
  have hsize (n : ℕ) : (encNat n).length ≤ n := by
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hsucc := ComputableInO.natSucc.computableInPolyTime
    (PolyBounded.of_forall_le 1 2 (fun _ => by simp))
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))
  have h := iterate (count := fun n => n) (init := fun _ => 0) (step := Nat.succ)
    id' (const 0) hsucc
    (bound := fun n => (encUnary n).length) .self (fun n i hi => by
      simpa [Nat.succ_iterate] using (hsize i).trans hi)
  simpa [Nat.succ_iterate] using h

private theorem bitsDropUnary :
    ComputableInPolyTime (fun p : List Bool × ℕ => p.1.drop p.2)
      (encPair encBits encUnary) encBits := by
  have h := iterate (count := Prod.snd) (init := Prod.fst) (step := List.tail)
    (snd encBits encUnary) (fst encBits encUnary) bitsTail
    (bound := fun p => (encPair encBits encUnary p).length) .self (fun p i _ => by
      rw [List.tail_iterate]
      simp only [length_encPair, encBits_apply, List.length_drop]
      omega)
  simpa only [List.tail_iterate] using h

/-- Read a bit at a unary index with a fixed fallback. Fixing the raw encoding avoids
guessing a list-encoding instance during compositional proof search. -/
@[fun_prop]
theorem bitsGetD (fallback : Bool) :
    ComputableInPolyTime (fun p : List Bool × ℕ => p.1.getD p.2 fallback)
      (encPair encBits encUnary) encBool := by
  have hhead : ComputableInPolyTime (fun l : List Bool => l.headD fallback) encBits encBool := by
    exact (ListEncoding.headD
      (enc₁ := encBool) (enc := encBits) fallback).computableInPolyTime
  simpa only [Function.comp_def, List.headD_eq_head?_getD, List.head?_drop,
    List.getD_eq_getElem?_getD] using hhead.comp bitsDropUnary

/-- Read the bit of a computed binary number at a computed unary position. -/
@[fun_prop]
theorem binary_testBit {α : Type} {input : α ↪ List Bool} {n i : α → ℕ}
    (hn : ComputableInPolyTime n input encNat)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => (n a).testBit (i a)) input encBool := by
  have hbits := (of_eq (encIn := encNat) (encOut := encBits) (f := Nat.bits) fun _ => rfl).comp hn
  refine ((bitsGetD false).comp (hbits.prod hi)).of_enc_eq fun a => ?_
  simp only [Function.comp_apply, Nat.testBit_eq_inth, ← List.getD_default_eq_getI]
  rfl

/-- Read the bit of a computed unary number at a computed unary position. -/
@[fun_prop]
theorem unary_testBit' {α : Type} {input : α ↪ List Bool} {n i : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hi : ComputableInPolyTime i input encUnary) :
    ComputableInPolyTime (fun a => (n a).testBit (i a)) input encBool :=
  binary_testBit (unary_to_binary.comp hn) hi

end Turing.MultiTapeTM.ComputableInPolyTime
