/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearCodecPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words
import Mathlib.Tactic.Linarith

/-!
# The framed encoding of pairs

`encPair enc₁ enc₂` encodes a pair as its framed first component (`Turing.MultiTapeTM.frame`)
followed by its second component. It has the capabilities of `Turing.MultiTapeTM.PairEncoding`.

## Main definitions

* `Turing.MultiTapeTM.encFramed`: an encoding with every encoded value framed.
* `Turing.MultiTapeTM.encPair`: the framed encoding of pairs.
-/

namespace Turing.MultiTapeTM

universe u

variable {α β : Type u}

/-- `enc` with every encoded value framed. -/
@[expose] public def encFramed (enc : α ↪ List Bool) : α ↪ List Bool :=
  ⟨fun a => frame (enc a), fun _ _ h => enc.injective (frame_injective h)⟩

/-- Pairs encoded as the framed first component followed by the second component. -/
@[expose] public def encPair (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) :
    α × β ↪ List Bool :=
  ⟨fun p => frame (enc₁ p.1) ++ enc₂ p.2, fun _ _ h =>
    Prod.ext (enc₁.injective (frame_append_inj h).1) (enc₂.injective (frame_append_inj h).2)⟩

@[simp]
public lemma encFramed_apply (enc : α ↪ List Bool) (a : α) : encFramed enc a = frame (enc a) :=
  rfl

variable {enc₁ : α ↪ List Bool} {enc₂ : β ↪ List Bool}

@[simp]
public lemma encPair_apply (p : α × β) : encPair enc₁ enc₂ p = frame (enc₁ p.1) ++ enc₂ p.2 :=
  rfl

public lemma length_encPair (p : α × β) :
    (encPair enc₁ enc₂ p).length = 2 * (enc₁ p.1).length + 1 + (enc₂ p.2).length := by
  simp

public lemma length_le_encPair_left (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (p : α × β) :
    (enc₁ p.1).length ≤ (encPair enc₁ enc₂ p).length := by
  rw [length_encPair]; omega

public lemma length_le_encPair_right (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (p : α × β) :
    (enc₂ p.2).length ≤ (encPair enc₁ enc₂ p).length := by
  rw [length_encPair]; omega

public instance : PairEncoding enc₁ enc₂ (encPair enc₁ enc₂) where
  fst := .of_unframe fun p => by simp
  snd := .of_dropFrame fun p => by simp
  pair := fun {_ encIn f g t s} hf hg => by
    obtain ⟨c₁, k₁, Q₁, _, tm₁, h₁⟩ := Internal.NormalForm.bigO
      (show ComputableInBigO f encIn enc₁ t s from
        ⟨1, hf.mono (fun _ => by omega) (fun _ => by omega)⟩)
    obtain ⟨c₂, k₂, Q₂, _, tm₂, h₂⟩ := Internal.NormalForm.bigO
      (show ComputableInBigO g encIn enc₂ t s from
        ⟨1, hg.mono (fun _ => by omega) (fun _ => by omega)⟩)
    obtain ⟨c₀, k₀, Q₀, _, tm₀, h₀⟩ := Internal.NormalForm.linear
      (ComputableInLinearTimeAndSpace.of_frame (f := id)
        (encIn := enc₁) (encMid := encFramed enc₁) fun _ => rfl)
    let overhead := 6 * max k₁ k₀ + 20 + 2 * max (max k₁ k₀ + 2) k₂
    let ct := c₁ + c₂ + (c₀ + 4) * c₁ + c₀ + 9
    let cs := c₁ + c₂ + c₀ + 5 + overhead
    refine ⟨ct + cs, _, _, inferInstance, appendTM (tm₀.comp tm₁ true) tm₂, fun x => ?_⟩
    have h := ((h₁ x).comp (h₀ (f x)) true).append (h₂ x)
    change (appendTM (tm₀.comp tm₁ true) tm₂).ComputesInTimeAndSpace _ _ _ _
    have hl := (h₁ x).length_output_le
    have hp := length_le_encPair_left enc₁ enc₂ (f x, g x)
    have htime : c₀ * ((enc₁ (f x)).length + 1) + 4 * (enc₁ (f x)).length ≤
        (c₀ + 4) * c₁ * (t x + 1) + c₀ := by nlinarith
    have hspace : c₀ * ((enc₁ (f x)).length + 1) + 5 * (enc₁ (f x)).length ≤
        (c₀ + 5) * (encPair enc₁ enc₂ (f x, g x)).length + c₀ := by nlinarith
    have hct : ct * (t x + 1) ≤ (ct + cs) * (t x + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
    have hcs : cs * (s x + (encPair enc₁ enc₂ (f x, g x)).length + 1) ≤
        (ct + cs) * (s x + (encPair enc₁ enc₂ (f x, g x)).length + 1) :=
      Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
    have hm := h.mono (t' := ct * (t x + 1))
      (s' := cs * (s x + (encPair enc₁ enc₂ (f x, g x)).length + 1))
      (by dsimp [ct]; nlinarith)
      (by
        have ho := Nat.le_mul_of_pos_right overhead
          (Nat.succ_pos (s x + (encPair enc₁ enc₂ (f x, g x)).length))
        simp only [Nat.succ_eq_add_one] at ho
        dsimp [cs, overhead] at *
        nlinarith)
    exact (hm.mono hct hcs).computesInTimeAndSpace

end Turing.MultiTapeTM
