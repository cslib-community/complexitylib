/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigOLe
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts
import Mathlib.Tactic.Linarith

/-!
# Direct consequences of charged asymptotic bounds

Time, workspace and encoded output are separate obligations. These rules package or forget the
actual realizing machine; they do not normalize it or import a higher construction calculus.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInO

open Cslib

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {T S : α → ℕ}

/-- Exact plain machine bounds and an explicit output charge supply asymptotic bounds. -/
theorem of_bounds {t s : α → ℕ}
    (hf : ComputableInTimeAndSpace f encIn encOut t s) (k : ℕ)
    (ht : ∀ a, t a ≤ k * (T a + 1)) (hs : ∀ a, s a ≤ k * (S a + 1))
    (hl : ∀ a, (encOut (f a)).length ≤ k * (S a + 1)) :
    ComputableInO f encIn encOut T S :=
  ⟨k, hf.mono ht hs, hl⟩

/-- Weaken both bounds by independent pointwise estimates and a common constant. -/
theorem mono {T' S' : α → ℕ} (h : ComputableInO f encIn encOut T S) (k : ℕ)
    (hT : ∀ a, T a ≤ k * (T' a + 1)) (hS : ∀ a, S a ≤ k * (S' a + 1)) :
    ComputableInO f encIn encOut T' S' :=
  let ⟨c, hc, hl⟩ := h
  of_bounds hc (c * (k + 1)) (fun a => by nlinarith [hT a])
    (fun a => by nlinarith [hS a]) (fun a => by nlinarith [hS a, hl a])

/-- Pointwise larger bounds retain the same encoded-output charge. -/
theorem mono_le {T' S' : α → ℕ} (h : ComputableInO f encIn encOut T S)
    (hT : ∀ a, T a ≤ T' a) (hS : ∀ a, S a ≤ S' a) :
    ComputableInO f encIn encOut T' S' :=
  h.mono 1 (fun a => by have := hT a; omega) (fun a => by have := hS a; omega)

/-- Weaken independent time and charged workspace bounds up to constants. -/
theorem weaken {T' S' : α → ℕ} (h : ComputableInO f encIn encOut T S)
    (hT : T ≼ T') (hS : S ≼ S') : ComputableInO f encIn encOut T' S' :=
  let ⟨k₁, h₁⟩ := hT
  let ⟨k₂, h₂⟩ := hS
  h.mono (k₁ + k₂) (fun a => (h₁ a).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
    (fun a => (h₂ a).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))

/-- An equal encoded output reuses the same machine and both resource budgets. -/
theorem of_enc_eq {γ : Type*} {encC : γ ↪ List Bool} {g : α → γ}
    (h : ComputableInO f encIn encOut T S) (hg : ∀ a, encC (g a) = encOut (f a)) :
    ComputableInO g encIn encC T S := by
  obtain ⟨c, ⟨k, State, hfinite, tm, htm⟩, hl⟩ := h
  exact ⟨c, ⟨k, State, hfinite, tm, fun a => hg a ▸ htm a⟩,
    fun a => by rw [hg a]; exact hl a⟩

/-- Pull back along an input map preserving the complete encoded word. No algorithm for the
semantic map is assumed: the realizing machine receives exactly the same word. -/
theorem of_encIn_eq {δ : Type*} {encD : δ ↪ List Bool}
    (h : ComputableInO f encIn encOut T S) (g : δ → α)
    (hg : ∀ a, encIn (g a) = encD a) :
    ComputableInO (f ∘ g) encD encOut (T ∘ g) (S ∘ g) := by
  obtain ⟨c, ⟨k, State, hfinite, tm, htm⟩, hl⟩ := h
  exact ⟨c, ⟨k, State, hfinite, tm, fun a => hg a ▸ htm (g a)⟩, fun a => hl (g a)⟩

/-- Polynomial bounds on both resource functions give a plain polynomial-time certificate. -/
theorem computableInPolyTime (h : ComputableInO f encIn encOut T S)
    (hT : PolyBounded (fun a => (encIn a).length) T)
    (hS : PolyBounded (fun a => (encIn a).length) S) :
    ComputableInPolyTime f encIn encOut := by
  obtain ⟨c, h, _⟩ := h
  obtain ⟨ct, dt, ht⟩ := hT.exists_le
  obtain ⟨cs, ds, hs⟩ := hS.exists_le
  refine ⟨fun n => c * (ct * (n + 1) ^ dt + 1),
    fun n => c * (cs * (n + 1) ^ ds + 1), by fun_prop, by fun_prop, h.mono ?_ ?_⟩
  · exact fun a => Nat.mul_le_mul_left _ (Nat.add_le_add_right (ht a) 1)
  · exact fun a => Nat.mul_le_mul_left _ (Nat.add_le_add_right (hs a) 1)

end Turing.MultiTapeTM.ComputableInO

namespace Turing.MultiTapeTM

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {T S T' S' t s : α → ℕ}

/-- **Polynomial time gives polynomial charged bounds**: a function computable in polynomial time is
computable within time `O(T)` and space `O(S)` for bounds polynomial in the length of the encoded
input, namely the time of a realizing machine and the sum of its time and space. -/
public theorem ComputableInPolyTime.exists_computableInO (h : ComputableInPolyTime f encIn encOut) :
    ∃ T S, PolyBounded (fun a => (encIn a).length) T ∧ PolyBounded (fun a => (encIn a).length) S ∧
      ComputableInO f encIn encOut T S := by
  obtain ⟨t, s, ht, hs, h⟩ := h
  exact ⟨_, _, .of_polynomiallyBounded _ ht,
    (PolyBounded.of_polynomiallyBounded _ ht).add (.of_polynomiallyBounded _ hs),
    .of_bounds h 1 (fun _ => by omega) (fun _ => by omega) fun a => by
      have := h.length_le a
      omega⟩

/-- Bounds up to constant factors. -/
public theorem ComputableInBigO.of_bounds (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : t ≼ T) (hs : s ≼ S) : ComputableInBigO f encIn encOut T S :=
  let ⟨k₁, h₁⟩ := ht
  let ⟨k₂, h₂⟩ := hs
  ⟨k₁ + k₂, h.mono (fun a => (h₁ a).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
    fun a => (h₂ a).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))⟩

/-- Weakening the bounds, up to constant factors. -/
public theorem ComputableInBigO.weaken (h : ComputableInBigO f encIn encOut T S)
    (hT : T ≼ T') (hS : S ≼ S') : ComputableInBigO f encIn encOut T' S' :=
  let ⟨c, hc⟩ := h
  .of_bounds hc ((BigOLe.const_mul c (u := fun a => T a + 1)
    (.of_le_linear 1 1 fun _ => by omega)).trans hT)
    ((BigOLe.const_mul c (u := fun a => S a + 1) (.of_le_linear 1 1 fun _ => by omega)).trans hS)

end Turing.MultiTapeTM
