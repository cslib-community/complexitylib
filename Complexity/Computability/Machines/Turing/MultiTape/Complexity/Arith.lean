/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Nat.Size
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat.Arithmetic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Addition and multiplication with bounds of given degrees

Natural numbers are encoded in binary (`Turing.MultiTapeTM.encNat`). Addition is a left fold over
the digits of the first summand that keeps the carry, the rest of the digits of the second summand
and the digits of the sum so far; at the end the carry is added to the rest of the second summand.
Multiplication is a left fold over the digits of the first factor that keeps the product so far and
the second factor shifted by the digits read, adding the shifted factor for every digit `1`.

## Main results

* `Turing.MultiTapeTM.computableTidilyInDegree_add`: addition in quadratic time and space.
* `Turing.MultiTapeTM.computableTidilyInDegree_mul`: multiplication in cubic time and space.
-/

namespace Turing.MultiTapeTM

open NatSucc


open NatAdd ComputableTidilyInDegree

/-- **Addition is tidily computable in quadratic time and space**, in the binary encoding. -/
public theorem computableTidilyInDegree_add :
    ComputableTidilyInDegree (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat 2 1 := by
  let encS := encPair encBool (encPair encBits encBits)
  -- a round of the first fold
  have hstep : ComputableTidilyInDegree (fun p : _ × Bool => addStep p.1 p.2)
      (encPair encS encBool) encS 1 1 := by
    have hs := fst encS encBool
    have hr := hs.snd'.fst'
    have habc := (snd encS encBool).prod (((headD (enc₁ := encBool) false).comp hr).prod hs.fst')
    have hcarry := (of_finite (encIn := encPair encBool (encPair encBool encBool))
      (encMid := encBool) fun t : Bool × Bool × Bool => carry t.1 t.2.1 t.2.2).comp habc
    have hdigit := (of_finite (encIn := encPair encBool (encPair encBool encBool))
      (encMid := encBool) fun t : Bool × Bool × Bool => t.1 ^^ (t.2.1 ^^ t.2.2)).comp habc
    exact (hcarry.prod ((tail (enc₁ := encBool)).comp hr |>.prod
      (hs.snd'.snd'.append hdigit (encOut := encBits) fun _ => rfl))).mono
  have hsize : DegreeBounded (fun p : ℕ × ℕ => (encPair encNat encNat p).length)
      (fun p => 2 * (encPair encNat encNat p).length + 4) 1 :=
    (DegreeBounded.self.smul 2).add_const 4
  -- the first fold, over the digits of the first summand
  have hfold := foldl' (encL := encBits) (encB := encS)
    (list := fun p : ℕ × ℕ => p.1.bits) (init := fun p => (false, p.2.bits, []))
    (of_eq (encIn := encNat) (encMid := encBits) (f := Nat.bits) (fun _ => rfl) |>.comp
      (fst encNat encNat))
    ((const false).prod ((of_eq (encIn := encNat) (encMid := encBits) (f := Nat.bits)
      (fun _ => rfl) |>.comp (snd encNat encNat)).prod (const [])))
    hstep hsize ?_
  rotate_left
  · intro p i hi
    obtain ⟨h₁, h₂⟩ := length_foldl_addStep (p.1.bits.take i) (false, p.2.bits, [])
    simp only [encS, length_encPair, encBool_apply, List.length_singleton, encBits_apply,
      encNat_apply, List.length_take, List.length_nil] at h₁ h₂ ⊢
    omega
  -- the second fold adds the carry to the rest of the second summand
  have hfin : ComputableTidilyInDegree (fun s : Bool × List Bool × List Bool =>
      succFinish (s.2.1.foldl succStep (s.1, s.2.2))) encS encBits 2 1 := by
    have hs := of_eq (encIn := encS) (encMid := encS) (f := id) fun _ => rfl
    refine ((of_linear linear_succFinish).comp (foldl' (encL := encBits) (encB := encAcc)
      hs.snd'.fst' (hs.fst'.prod hs.snd'.snd')
      (of_linear linear_succStep) (B := fun s => (encS s).length + 3)
      (DegreeBounded.self.add_const 3) fun s i hi => ?_)).mono
    simp only [length_foldl_succStep, encS, length_encPair, encBool_apply, id_eq,
      List.length_singleton, encBits_apply, List.length_take]
    omega
  refine ((hfin.comp hfold).of_enc_eq fun p => ?_).mono
  simp only [Function.comp_apply, encBits_apply, encNat_apply]
  rw [succFinish_foldl, ← foldl_addStep, List.nil_append, addBits_bits]
  rfl


open NatMul in
/-- **Multiplication is tidily computable in cubic time and space**, in the binary encoding. -/
public theorem computableTidilyInDegree_mul :
    ComputableTidilyInDegree (fun p : ℕ × ℕ => p.1 * p.2) (encPair encNat encNat) encNat 3 1 := by
  let encS := encPair encNat encNat
  have hadd := computableTidilyInDegree_add
  -- a round of the fold
  have hstep : ComputableTidilyInDegree (fun p : (ℕ × ℕ) × Bool => mulStep p.1 p.2)
      (encPair encS encBool) encS 2 1 := by
    have hs := fst encS encBool
    exact (((snd encS encBool).ite ((hadd.comp hs).restrict _) (hs.fst'.restrict _)).prod
      (hadd.comp (hs.snd'.prod hs.snd'))).mono
  have hfold := foldl' (encL := encBits) (encB := encS)
    (list := fun p : ℕ × ℕ => p.1.bits) (init := fun p => (0, p.2))
    (of_eq (encIn := encNat) (encMid := encBits) (f := Nat.bits) (fun _ => rfl) |>.comp
      (fst encNat encNat))
    ((const 0).prod (snd encNat encNat)) hstep
    (B := fun p => 3 * (encPair encNat encNat p).length + 1)
    ((DegreeBounded.self.smul 3).add_const 1) fun p i hi => ?_
  · have h : ComputableTidilyInDegree (_ ∘ _) _ encNat 3 1 := ((fst encNat encNat).comp hfold).mono
    convert h using 1
    funext p
    simp [foldl_mulStep]
  · obtain ⟨h₁, h₂⟩ := foldl_mulStep_le (p.1.bits.take i) 0 p.2
    have hi' : (p.1.bits.take i).length ≤ p.1.size := by simp [← Nat.size_eq_bits_len]
    have hacc := size_le_of_le _ (by omega : (List.foldl mulStep (0, p.2) (p.1.bits.take i)).1 ≤
      2 ^ (p.1.bits.take i).length * p.2)
    have hsh := size_le_of_le _ h₂.le
    simp only [encS, length_encPair, encNat_apply, Nat.size_eq_bits_len] at hacc hsh hi' ⊢
    omega

end Turing.MultiTapeTM
