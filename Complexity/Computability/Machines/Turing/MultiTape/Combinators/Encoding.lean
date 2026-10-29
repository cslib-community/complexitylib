/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words
public import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Append
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Ite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Linear time and space, and encodings of pairs, options and lists

Tidy computability (`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace`) is relative to encodings of
values as words. Tidy computability in linear time and space is closed under composition, case
distinctions, concatenation of encoded values and pairing, and contains constant functions and the
functions computed by finite-state transducers.

This file also states, as classes indexed by the encodings, what is required of encodings of
pairs, options and lists: their basic operations are tidily computable in linear time and space,
and pairing, which builds a value from a common input, preserves tidy computability. Theorems take
these classes as instance arguments, so they hold for every encoding with the required
capabilities.

## Main definitions

* `Turing.MultiTapeTM.encBool`: the encoding `b ↦ [b]` of `Bool`. Case distinctions
  (`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.ite`) accept any encoding of `Bool`, so the
  choice matters only up to a constant.
* `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace`: tidy computability in linear time and
  space, up to a constant.
* `Turing.MultiTapeTM.PairEncoding enc₁ enc₂ enc`: `enc` encodes pairs compatibly with `enc₁` and
  `enc₂`.
* `Turing.MultiTapeTM.OptionEncoding enc₁ enc`: `enc` encodes options compatibly with `enc₁`, with
  `none` encoded by the empty word.
* `Turing.MultiTapeTM.ListEncoding enc₁ enc`: `enc` encodes lists compatibly with `enc₁`.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.of_enc_eq`: reuse identical encoded outputs
  with the same machine and exact time and space bounds.

* `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace.ite`, `.append`: closure properties of
  linear time and space.
* `Turing.MultiTapeTM.ComputableTidilyInLinearTimeAndSpace.const`: constant functions.
* `Turing.MultiTapeTM.Transducer.computableTidilyInLinearTimeAndSpace`: functions computed by
  finite-state transducers.
* `Turing.MultiTapeTM.PairEncoding.pair_mono`: pairing functions computable within different
  bounds.
-/

namespace Turing.MultiTapeTM

universe u

/-- `f` is tidily computable within a constant factor of the length of the encoded input plus one,
in time and in space. -/
@[expose] public def ComputableTidilyInLinearTimeAndSpace {α β : Type*} (f : α → β)
    (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) : Prop :=
  ∃ c, ComputableTidilyInTimeAndSpace f encIn encOut (fun a => c * ((encIn a).length + 1))
    (fun a => c * ((encIn a).length + 1))

-- upstream: candidate
-- vendored: local output-word transport rule; not part of the copied revision.
/-- Reuse the same machine when the new function emits the same encoded output word.
The time and space bounds are unchanged; no encoding conversion is performed. -/
public theorem ComputableTidilyInTimeAndSpace.of_enc_eq
    {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    {encOut : γ ↪ List Bool} {f : α → β} {g : α → γ} {t s : α → ℕ}
    (hf : ComputableTidilyInTimeAndSpace f encIn encMid t s)
    (h : ∀ a, encOut (g a) = encMid (f a)) :
    ComputableTidilyInTimeAndSpace g encIn encOut t s :=
  let ⟨k, State, hfinite, tm, htm⟩ := hf
  ⟨k, State, hfinite, tm, fun a => h a ▸ htm a⟩

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

/-! ### Closure properties of linear time and space -/

namespace ComputableTidilyInLinearTimeAndSpace

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- A function tidily computable in linear time and space on all inputs is so on the inputs
satisfying `p`. -/
public theorem restrict {f : α → β} (h : ComputableTidilyInLinearTimeAndSpace f encIn encMid)
    (p : α → Prop) :
    ComputableTidilyInLinearTimeAndSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype p).trans encIn) encMid :=
  let ⟨c, hc⟩ := h
  ⟨c, hc.restrict p⟩

/-- Case distinctions of functions tidily computable in linear time and space, each branch on the
inputs where it is taken. -/
public theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableTidilyInLinearTimeAndSpace c encIn encC)
    (hf : ComputableTidilyInLinearTimeAndSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans encIn) encMid)
    (hg : ComputableTidilyInLinearTimeAndSpace (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans encIn) encMid) :
    ComputableTidilyInLinearTimeAndSpace (fun x => if c x then f x else g x) encIn encMid := by
  obtain ⟨c₀, h₀⟩ := hc
  obtain ⟨c₁, h₁⟩ := hf
  obtain ⟨c₂, h₂⟩ := hg
  obtain ⟨k, h⟩ := ComputableTidilyInTimeAndSpace.ite h₀
    (tf := fun x => c₁ * ((encIn x).length + 1)) (sf := fun x => c₁ * ((encIn x).length + 1))
    (tg := fun x => c₂ * ((encIn x).length + 1)) (sg := fun x => c₂ * ((encIn x).length + 1))
    h₁ h₂
  refine ⟨c₀ + c₁ + c₂ + k, h.mono (fun x => ?_) (fun x => ?_)⟩ <;> split_ifs <;> nlinarith

/-- Constant functions are tidily computable in linear time and space. -/
public theorem const (b : β) :
    ComputableTidilyInLinearTimeAndSpace (fun _ : α => b) encIn encMid := by
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := encIn) (encOut := encMid) b
  exact ⟨2 * c + 2, h.computableTidilyInTimeAndSpace.mono
    (fun _ => Nat.le_mul_of_pos_right _ (Nat.succ_pos _)) (fun _ => Nat.zero_le _)⟩

/-- Functions whose encoded value is the encoded input. -/
public theorem of_eq {f : α → β} (h : ∀ a, encMid (f a) = encIn a) :
    ComputableTidilyInLinearTimeAndSpace f encIn encMid :=
  ⟨4, 0, _, inferInstance, tidyCopy Bool, fun a => by
    rw [h]
    exact (computesTidily_tidyCopy _).mono (by beta_reduce; omega) (Nat.zero_le _)⟩

/-- A function whose encoded value is the concatenation of the encoded values of two functions
tidily computable in linear time and space. -/
public theorem append {δ : Type*} {enc₂ : δ ↪ List Bool} {f₁ : α → β} {f₂ : α → δ} {g : α → γ}
    (h₁ : ComputableTidilyInLinearTimeAndSpace f₁ encIn encMid)
    (h₂ : ComputableTidilyInLinearTimeAndSpace f₂ encIn enc₂)
    (hg : ∀ x, encOut (g x) = encMid (f₁ x) ++ enc₂ (f₂ x)) :
    ComputableTidilyInLinearTimeAndSpace g encIn encOut := by
  obtain ⟨c₁, h₁⟩ := h₁
  obtain ⟨c₂, h₂⟩ := h₂
  obtain ⟨k, h⟩ := h₁.append h₂ hg
  refine ⟨c₁ + c₂ + k, h.mono (fun x => ?_) (fun x => ?_)⟩ <;> nlinarith

end ComputableTidilyInLinearTimeAndSpace

/-- A function computed by a transducer with finitely many states is tidily computable in linear
time and space. -/
public theorem Transducer.computableTidilyInLinearTimeAndSpace {Q : Type} [Finite Q]
    (τ : Transducer Bool Q) {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} (hf : ∀ a, encOut (f a) = τ.run τ.q₀ (encIn a)) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  ⟨8, (τ.computableTidilyInTimeAndSpace hf).mono (fun _ => by omega) (fun _ => Nat.zero_le _)⟩

end Turing.MultiTapeTM
