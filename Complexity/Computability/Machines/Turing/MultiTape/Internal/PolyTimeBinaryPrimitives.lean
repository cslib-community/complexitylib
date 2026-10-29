/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Karn Seth
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Arithmetic
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.GetD

/-!
# Direct polynomial-time binary arithmetic

The existing carry folds and bit-position scan are certified using plain machine closure.
Reachable word states are bounded by the encoded input length, not the numeric operands.
Captured multiplication uses the original shift-and-add fold over the first operand's bits,
with the unchanged full-prefix state bound; its pair certificate remains private.
-/

@[expose] public section
namespace Turing.MultiTapeTM
open Cslib

namespace ComputableInPolyTime

/-- Addition of binary naturals, using the carry and remaining-word folds.
Compose this certificate with the producers' `.prod` certificate. Global automatic addition
remains separate from this named rule, since an unconstrained intermediate encoding can select
a binary branch where a surrounding computation needs a unary size. -/
theorem binary_add : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    (encPair encNat encNat) encNat :=
  ComputableInO.natAdd.computableInPolyTime
    (PolyBounded.of_forall_le 1 2 (fun _ => by simp))
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))

/-- Strict comparison by scanning binary bit positions, never the numeric operand range. -/
@[fun_prop]
theorem binary_lt : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
    (encPair encNat encNat) encBool := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl
  have hlen : ComputableInPolyTime (fun n : ℕ => n.bits.length) encNat encUnary :=
    Internal.DecoderWords.unary_degree.computableInPolyTime.comp hbits
  have hwords : ComputableInDegree (fun p : ℕ × ℕ => p.1.bits ++ p.2.bits)
      (encPair encNat encNat) encBits 1 1 :=
    (ComputableInDegree.fst encNat encNat).append (ComputableInDegree.snd encNat encNat)
      (fun _ => rfl)
  have hsum : ComputableInPolyTime (fun p : ℕ × ℕ => p.1.bits.length + p.2.bits.length)
      (encPair encNat encNat) encUnary := by
    simpa only [Function.comp_def, List.length_append] using
      Internal.DecoderWords.unary_degree.computableInPolyTime.comp hwords.computableInPolyTime
  have hscan : ComputableInPolyTime (fun p : ℕ × ℕ =>
      (List.range p.2.bits.length).any fun i =>
        !p.1.bits.getD i false && p.2.bits.getD i false &&
          (List.range (p.1.bits.length + p.2.bits.length)).all fun j =>
            decide (j ≤ i) || p.1.bits.getD j false == p.2.bits.getD j false)
      (encPair encNat encNat) encBool := by
    simp only [List.any_eq_not_all_not]
    apply bool_not.comp
    apply allWithInput (range.comp (hlen.comp (snd encNat encNat)))
    apply bool_not.comp
    let input := encPair (encPair encNat encNat) encUnary
    have hlist := range.comp (hsum.comp (fst (encPair encNat encNat) encUnary))
    have hhigh : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ =>
        (List.range (p.1.1.bits.length + p.1.2.bits.length)).all fun j =>
          decide (j ≤ p.2) || p.1.1.bits.getD j false == p.1.2.bits.getD j false)
        input encBool := by
      apply allWithInput hlist
      fun_prop
    have hflags : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ =>
        !p.1.1.bits.getD p.2 false && p.1.2.bits.getD p.2 false) input encBool := by
      fun_prop
    exact bool_and.comp (hflags.prod hhigh)
  refine hscan.of_enc_eq fun p => congrArg encBool ?_
  have hbit (k i : ℕ) : k.bits.getD i false = k.testBit i := by
    rw [Nat.testBit_eq_inth, ← List.getD_default_eq_getI]
    rfl
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.lt_iff_exists_testBit]
  simp only [hbit, Nat.size_eq_bits_len, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    Bool.not_eq_true', List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine exists_congr fun i => and_congr_right fun _ => ?_
  rw [and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun j _ => ?_
  rw [← Nat.not_le, imp_iff_not_or, not_not]

private theorem binaryMulPair :
    ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.2) (encPair encNat encNat) encNat := by
  let encS := encPair encNat encNat
  have hs := fst encS encBool
  have hleft := (fst encNat encNat).comp hs
  have hright := (snd encNat encNat).comp hs
  have hstep : ComputableInPolyTime (fun p : (ℕ × ℕ) × Bool => NatMul.mulStep p.1 p.2)
      (encPair encS encBool) encS := by
    simpa only [NatMul.mulStep, Function.comp_apply] using
      ((snd encS encBool).ite (binary_add.comp hs) hleft).prod
        (binary_add.comp (hright.prod hright))
  have hbits : ComputableInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl
  have hfold := foldl' (encA := encBool) (encL := encBits) (encB := encS)
    (list := fun p : ℕ × ℕ => p.1.bits) (init := fun p => (0, p.2))
    (hbits.comp (fst encNat encNat)) ((const 0).prod (snd encNat encNat)) hstep
    (B := fun p => 3 * (encPair encNat encNat p).length + 1)
    (PolyBounded.of_forall_le 4 1 fun _ => by simp only [pow_one]; omega) (by
      intro p i _
      obtain ⟨h₁, h₂⟩ := NatMul.foldl_mulStep_le (p.1.bits.take i) 0 p.2
      have hi' : (p.1.bits.take i).length ≤ p.1.size := by simp [← Nat.size_eq_bits_len]
      have hacc := NatMul.size_le_of_le _ (by omega :
        (List.foldl NatMul.mulStep (0, p.2) (p.1.bits.take i)).1 ≤
          2 ^ (p.1.bits.take i).length * p.2)
      have hsh := NatMul.size_le_of_le _ h₂.le
      simp only [encS, length_encPair, encNat_apply, Nat.size_eq_bits_len] at hacc hsh hi' ⊢
      omega)
  have h := (fst encNat encNat).comp hfold
  convert h using 1
  funext p
  simp only [Function.comp_apply, NatMul.foldl_mulStep, zero_add]

/-- Multiply computed binary values, fixing their intermediate encodings for proof search. -/
theorem binary_mul' {α : Type}
    {input : α ↪ List Bool}
    {left : α → ℕ}
    {right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun (a : α) => left a * right a) input
  encNat :=
  binaryMulPair.comp (hleft.prod hright)

/-- Non-strict binary comparison, composed from the existing strict comparison certificate.
Automatic composition uses the computed-operand rule `binary_le'`. -/
theorem binary_le : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encNat encNat) encBool := by
  simpa only [Function.comp_def, ← decide_not, Nat.not_lt] using
    bool_not.comp (binary_lt.comp ((snd encNat encNat).prod (fst encNat encNat)))

/-- Compare two binary naturals computed uniformly from the same encoded input. -/
@[fun_prop]
theorem binary_le' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => decide (left a ≤ right a)) input encBool :=
  binary_le.comp (hleft.prod hright)

end ComputableInPolyTime
end Turing.MultiTapeTM
