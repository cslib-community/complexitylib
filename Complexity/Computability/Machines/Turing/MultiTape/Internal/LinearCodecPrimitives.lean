/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate
-- vendored: codec machines retain crei/tidy-universal @7f7c0696 credit.
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.CodecWordMachines
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelAppend
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelIte
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Capabilities

/-! # Direct linear capabilities used by codecs

The witnesses normalize only realizing machines. No higher tidy computability rule is used.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInLinearTimeAndSpace

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- Restrict a certificate to the inputs satisfying a proposition, using the same machine. -/
theorem restrict {f : α → β} (h : ComputableInLinearTimeAndSpace f encIn encMid)
    (p : α → Prop) :
    ComputableInLinearTimeAndSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype p).trans encIn) encMid :=
  let ⟨c, k, Q, hfin, tm, htm⟩ := h
  ⟨c, k, Q, hfin, tm, fun a => htm a⟩

/-- Prepend the marker of the existing option encoding. -/
theorem of_cons_true {f : α → β} (h : ∀ a, encMid (f a) = true :: encIn a) :
    ComputableInLinearTimeAndSpace f encIn encMid :=
  of_transducer (Encodings.headT none) fun a => by
    rw [h]; cases encIn a <;> simp [Encodings.headT_run_true, Encodings.headT_q₀,
      Encodings.headT_step, Encodings.headT_final]

/-- Drop the input word's first symbol using the existing head machine. -/
theorem of_tail {f : α → β} (h : ∀ a, encMid (f a) = (encIn a).tail) :
    ComputableInLinearTimeAndSpace f encIn encMid :=
  of_transducer (Encodings.headT (some false)) fun a => by
    rw [h]; cases encIn a <;> simp [Encodings.headT_run_true, Encodings.headT_q₀,
      Encodings.headT_step, Encodings.headT_final]

/-- Keep the input word's first symbol using the existing head machine. -/
theorem of_take_one {f : α → β} (h : ∀ a, encMid (f a) = (encIn a).take 1) :
    ComputableInLinearTimeAndSpace f encIn encMid :=
  of_transducer (Encodings.headT (some true)) fun a => by
    rw [h]; cases encIn a <;> simp [Encodings.headT_run_true, Encodings.headT_q₀,
      Encodings.headT_step, Encodings.headT_final]

/-- Test the encoded input for emptiness using the existing finite transducer. -/
theorem of_isEmpty {f : α → Bool} (h : ∀ a, f a = (encIn a).isEmpty) :
    ComputableInLinearTimeAndSpace f encIn encBool :=
  of_transducer Encodings.isEmptyT fun a => by
    rw [h]; cases encIn a <;> simp [Encodings.isEmptyT_run_true, Encodings.isEmptyT_q₀,
      Encodings.isEmptyT_step, Encodings.isEmptyT_final]

/-- Concatenate two encoded outputs within a common linear bound. -/
theorem append {δ : Type*} {enc₂ : δ ↪ List Bool} {f₁ : α → β} {f₂ : α → δ} {g : α → γ}
    (h₁ : ComputableInLinearTimeAndSpace f₁ encIn encMid)
    (h₂ : ComputableInLinearTimeAndSpace f₂ encIn enc₂)
    (hg : ∀ a, encOut (g a) = encMid (f₁ a) ++ enc₂ (f₂ a)) :
    ComputableInLinearTimeAndSpace g encIn encOut := by
  obtain ⟨c₁, k₁, Q₁, _, tm₁, h₁⟩ := Internal.NormalForm.linear h₁
  obtain ⟨c₂, k₂, Q₂, _, tm₂, h₂⟩ := Internal.NormalForm.linear h₂
  refine ⟨c₁ + c₂ + 2 * max k₁ k₂, _, _, inferInstance, appendTM tm₁ tm₂, fun a => ?_⟩
  rw [hg]
  refine ((h₁ a).append (h₂ a)).mono ?_ ?_ |>.computesInTimeAndSpace
  all_goals
    have hk := Nat.le_mul_of_pos_right (2 * max k₁ k₂) (Nat.succ_pos (encIn a).length)
    simp only [Nat.succ_eq_add_one] at hk
    simp only [Nat.add_mul]
    omega

/-- Choose branches on their actual domains; normalize only their realizing machines. -/
theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableInLinearTimeAndSpace c encIn encC)
    (hf : ComputableInLinearTimeAndSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans encIn) encMid)
    (hg : ComputableInLinearTimeAndSpace (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans encIn) encMid) :
    ComputableInLinearTimeAndSpace (fun a => if c a then f a else g a) encIn encMid := by
  have ht : ComputableInLinearTimeAndSpace c encIn encTest := (of_finite id).comp hc
  obtain ⟨c₀, k₀, Q₀, _, tm₀, h₀⟩ := Internal.NormalForm.linear ht
  obtain ⟨c₁, k₁, Q₁, _, tm₁, h₁⟩ := Internal.NormalForm.linear hf
  obtain ⟨c₂, k₂, Q₂, _, tm₂, h₂⟩ := Internal.NormalForm.linear hg
  refine ⟨c₀ + c₁ + c₂ + 5 * max k₀ (max k₁ k₂) + 20,
    _, _, inferInstance, iteTM tm₀ tm₁ tm₂, fun a => ?_⟩
  have h := (h₀ a).ite (tm₁ := tm₁) (tm₂ := tm₂)
    (y := encMid (if c a then f a else g a))
    (t₁ := c₁ * ((encIn a).length + 1)) (s₁ := c₁ * ((encIn a).length + 1))
    (t₂ := c₂ * ((encIn a).length + 1)) (s₂ := c₂ * ((encIn a).length + 1))
    (fun hw => by
      have hca : c a = true := by cases hca : c a <;> simp_all [encTest_true, encTest_false]
      simpa [hca] using h₁ ⟨a, hca⟩)
    (fun hw => by
      have hca : c a = false := by cases hca : c a <;> simp_all [encTest_true, encTest_false]
      simpa [hca] using h₂ ⟨a, hca⟩)
  refine (h.mono ?_ ?_).computesInTimeAndSpace <;>
    cases hca : c a <;> simp_all only [encTest_true, encTest_false, List.length_cons,
      List.length_nil, List.cons_ne_self, reduceCtorEq, ↓reduceIte] <;>
    have hk := Nat.le_mul_of_pos_right (5 * max k₀ (max k₁ k₂) + 20)
      (Nat.succ_pos (encIn a).length) <;>
    simp only [Nat.succ_eq_add_one, Nat.add_mul] at * <;> omega

/-- A fixed default on the empty word and a linear certificate on nonempty encoded inputs. -/
theorem of_isEmpty_ite {f : α → β} (d : β) (hd : ∀ a, encIn a = [] → f a = d)
    (h : ComputableInLinearTimeAndSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype fun a => (encIn a).isEmpty = false).trans encIn) encMid) :
    ComputableInLinearTimeAndSpace f encIn encMid := by
  convert ite (c := fun a => (encIn a).isEmpty) (of_isEmpty fun _ => rfl)
    ((const d).restrict _) h using 1
  funext a
  split_ifs with ha <;> simp_all

end Turing.MultiTapeTM.ComputableInLinearTimeAndSpace

namespace Turing.MultiTapeTM

universe u

/-- Pairing functions computable in linear time and space. -/
theorem ComputableInLinearTimeAndSpace.pair {α β₁ β₂ : Type u}
    {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {enc : β₁ × β₂ ↪ List Bool} [hP : PairEncoding enc₁ enc₂ enc] {f : α → β₁} {g : α → β₂}
    (hf : ComputableInLinearTimeAndSpace f encIn enc₁)
    (hg : ComputableInLinearTimeAndSpace g encIn enc₂) :
    ComputableInLinearTimeAndSpace (fun x => (f x, g x)) encIn enc := by
  obtain ⟨c₁, h₁⟩ := hf
  obtain ⟨c₂, h₂⟩ := hg
  obtain ⟨c, h⟩ := hP.pair (h₁.mono (t' := fun x => (c₁ + c₂) * ((encIn x).length + 1))
    (s' := fun x => (c₁ + c₂) * ((encIn x).length + 1)) (fun x => by ring_nf; omega)
    (fun x => by ring_nf; omega))
    (h₂.mono (fun x => by ring_nf; omega) (fun x => by ring_nf; omega))
  refine ⟨c * (c + 2) * (c₁ + c₂ + 1), h.mono (fun x => ?_) (fun x => ?_)⟩
  · ring_nf
    omega
  · have := Nat.mul_le_mul_left c (h.length_le x)
    ring_nf at this ⊢
    omega

end Turing.MultiTapeTM
