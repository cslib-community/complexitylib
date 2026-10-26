/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelAppend
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.ConditionalMachine
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# Direct closure of independent degree bounds

These constructions combine machine witnesses, retaining independent resource and encoded-output
degrees, including degree zero. No higher tidy asymptotic calculus is used.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInDegree

variable {α β γ δ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {d₁ e₁ d₂ e₂ : ℕ}

/-- Concatenate encoded outputs without merging their independent cost and output degrees. -/
theorem append {enc₂ : δ ↪ List Bool} {f₁ : α → β} {f₂ : α → δ} {g : α → γ}
    (h₁ : ComputableInDegree f₁ encIn encMid d₁ e₁)
    (h₂ : ComputableInDegree f₂ encIn enc₂ d₂ e₂)
    (hg : ∀ x, encOut (g x) = encMid (f₁ x) ++ enc₂ (f₂ x)) :
    ComputableInDegree g encIn encOut (max d₁ d₂) (max e₁ e₂) := by
  obtain ⟨t₁, s₁, ht₁, hs₁, k₁, Q₁, _, tm₁, htm₁⟩ := Internal.NormalForm.degree h₁
  obtain ⟨t₂, s₂, ht₂, hs₂, k₂, Q₂, _, tm₂, htm₂⟩ := Internal.NormalForm.degree h₂
  refine ⟨⟨_, _, ht₁.add_max ht₂, (hs₁.add_max hs₂).add_const (2 * max k₁ k₂),
    _, _, inferInstance, appendTM tm₁ tm₂, fun a => ?_⟩,
    (h₁.2.add_max h₂.2).mono fun a => by simp [hg]⟩
  simpa only [hg a] using ((htm₁ a).append (htm₂ a)).computesInTimeAndSpace

universe u

/-- Generic pairing retains the resource degree as its encoded-output bound. -/
theorem pair {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {enc : β₁ × β₂ ↪ List Bool} [hP : PairEncoding enc₁ enc₂ enc] {f : α → β₁} {g : α → β₂}
    (hf : ComputableInDegree f encIn enc₁ d₁ e₁)
    (hg : ComputableInDegree g encIn enc₂ d₂ e₂) :
    ComputableInDegree (fun x => (f x, g x)) encIn enc (max d₁ d₂) (max d₁ d₂) := by
  obtain ⟨t₁, s₁, ht₁, hs₁, k₁, Q₁, _, tm₁, h₁⟩ := Internal.NormalForm.degree hf
  obtain ⟨t₂, s₂, ht₂, hs₂, k₂, Q₂, _, tm₂, h₂⟩ := Internal.NormalForm.degree hg
  obtain ⟨c, k, Q, hfin, tm, h⟩ := hP.pair
    (t := fun a => t₁ a + t₂ a) (s := fun a => s₁ a + s₂ a)
    ⟨k₁, Q₁, inferInstance, tm₁, fun a =>
      ((h₁ a).mono (Nat.le_add_right _ _) (Nat.le_add_right _ _)).computesInTimeAndSpace⟩
    ⟨k₂, Q₂, inferInstance, tm₂, fun a =>
      ((h₂ a).mono (Nat.le_add_left _ _) (Nat.le_add_left _ _)).computesInTimeAndSpace⟩
  have ht := ((ht₁.add_max ht₂).add_const 1).smul c
  have hs := ((((hs₁.add_max hs₂).add ht).add_const 1).smul c)
  refine ⟨⟨_, _, ht, hs, k, Q, hfin, tm, fun a => ?_⟩,
    ht.mono fun a => (h a).length_output_le⟩
  refine ⟨(h a).1, (h a).2.1, (h a).2.2.mono ?_⟩
  apply Nat.mul_le_mul_left
  have hl : (enc (f a, g a)).length ≤ c * (t₁ a + t₂ a + 1) :=
    (h a).length_output_le
  omega

/-- Framed pairing retains the independent encoded-output degrees. -/
theorem prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁} {g : α → β₂} (hf : ComputableInDegree f encIn enc₁ d₁ e₁)
    (hg : ComputableInDegree g encIn enc₂ d₂ e₂) :
    ComputableInDegree (fun x => (f x, g x)) encIn (encPair enc₁ enc₂) (max d₁ d₂)
      (max e₁ e₂) :=
  ⟨(hf.pair hg).1, (((hf.2.smul 2).add_const 1).add_max hg.2).mono fun x => by simp⟩

/-- Case distinction retains independent branch output degrees, including zero. -/
theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β} {dc ec : ℕ}
    (hc : ComputableInDegree c encIn encC dc ec)
    (hf : ComputableInDegree (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans encIn) encMid d₁ e₁)
    (hg : ComputableInDegree (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans encIn) encMid d₂ e₂) :
    ComputableInDegree (fun x => if c x then f x else g x) encIn encMid
      (max dc (max d₁ d₂)) (max e₁ e₂) := by
  obtain ⟨tc, sc, htc, hsc, kc, Qc, _, tmc, hmc⟩ := Internal.NormalForm.degree hc
  obtain ⟨tf, sf, ⟨ctf, htf⟩, ⟨csf, hsf⟩, kf, Qf, _, tmf, hmf⟩ :=
    Internal.NormalForm.degree hf
  obtain ⟨tg, sg, ⟨ctg, htg⟩, ⟨csg, hsg⟩, kg, Qg, _, tmg, hmg⟩ :=
    Internal.NormalForm.degree hg
  obtain ⟨clf, hlf⟩ := hf.2
  obtain ⟨clg, hlg⟩ := hg.2
  -- the bounds of the branches, extended to all inputs
  let ext (u : {x // c x = true} → ℕ) (v : {x // c x = false} → ℕ) (x : α) : ℕ :=
    if h : c x = true then u ⟨x, h⟩ else v ⟨x, by simpa using h⟩
  obtain ⟨k, km, Qm, hmfin, tm, htm⟩ := Internal.conditional hmc
    (tf := ext tf tg) (sf := ext sf sg) (tg := ext tf tg) (sg := ext sf sg)
    (fun x => (hmf x).mono (by simp [ext, x.2]) (by simp [ext, x.2]))
    (fun x => (hmg x).mono (by simp [ext, x.2]) (by simp [ext, x.2]))
  have hext {u v} {cu du cv dv : ℕ}
      (hu : ∀ x : {x // c x = true}, u x ≤ cu * ((encIn x).length + 1) ^ du)
      (hv : ∀ x : {x // c x = false}, v x ≤ cv * ((encIn x).length + 1) ^ dv) :
      DegreeBounded (fun a => (encIn a).length) (ext u v) (max du dv) :=
    ((DegreeBounded.mono_deg ⟨cu, fun _ => le_rfl⟩ (le_max_left du dv)).add
      (DegreeBounded.mono_deg ⟨cv, fun _ => le_rfl⟩ (le_max_right du dv))).mono fun x => by
      by_cases hx : c x = true
      · simpa [ext, hx] using Nat.le_add_right_of_le (hu ⟨x, hx⟩)
      · simpa [ext, hx] using Nat.le_add_left_of_le (hv ⟨x, by simpa using hx⟩)
  have hd : max d₁ d₂ ≤ max dc (max d₁ d₂) := le_max_right _ _
  refine ⟨⟨_, _, ((htc.mono_deg (le_max_left _ _)).add ((hext htf htg).mono_deg hd)).add_const k,
    ((hsc.mono_deg (le_max_left _ _)).add ((hext hsf hsg).mono_deg hd)).add_const k,
    km, Qm, hmfin, tm, fun x => ((htm x).mono ?_ ?_).computesInTimeAndSpace⟩,
    (hext hlf hlg).mono fun x => ?_⟩ <;>
  · by_cases hx : c x = true <;> simp [ext, hx]

end Turing.MultiTapeTM.ComputableInDegree
