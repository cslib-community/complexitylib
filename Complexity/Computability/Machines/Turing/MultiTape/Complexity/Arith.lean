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
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition
import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm
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

open ComputableTidilyInDegree

/-- **Addition is tidily computable in quadratic time and space**, in the binary encoding. -/
public theorem computableTidilyInDegree_add :
    ComputableTidilyInDegree (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat 2 1 := by
  obtain ⟨c, hc, hl⟩ := Internal.NormalForm.inO ComputableInO.natAdd
  have hT : DegreeBounded (fun p => (encPair encNat encNat p).length)
      (fun p => ((encPair encNat encNat p).length + 1) ^ 2) 2 := ⟨1, fun _ => by simp⟩
  have hS : DegreeBounded (fun p => (encPair encNat encNat p).length)
      (fun p => (encPair encNat encNat p).length + 1) 1 := ⟨1, fun _ => by simp⟩
  have ht := (hT.add_const 1).smul c
  have hs := (hS.add_const 1).smul c
  exact ⟨⟨_, _, ht, hs.mono_deg (by decide), hc⟩, hs.mono hl⟩


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
