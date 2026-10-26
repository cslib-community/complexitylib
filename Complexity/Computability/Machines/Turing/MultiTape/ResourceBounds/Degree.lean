/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (independent growth-bound algebra)

public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
public import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Tactic.Ring

/-!
# Polynomial degree bounds in an arbitrary size measure

These bounds and their arithmetic are independent of machine computability.

## Main definitions

* `Turing.MultiTapeTM.DegreeBounded`: a bound by a constant times `(size + 1) ^ d`.

## Main results

* `DegreeBounded.add_max`, `DegreeBounded.mul`, `DegreeBounded.comp`: arithmetic of degree bounds.
-/

namespace Turing.MultiTapeTM

/-! ### Bounds of a given degree -/

/-- `u` is bounded by a polynomial of degree `d` in `size`. -/
@[expose] public def DegreeBounded {α : Type*} (size u : α → ℕ) (d : ℕ) : Prop :=
  ∃ c, ∀ a, u a ≤ c * (size a + 1) ^ d

namespace DegreeBounded

variable {α β : Type*} {size : α → ℕ} {u v : α → ℕ} {d d₁ d₂ : ℕ}

public theorem mono (h : DegreeBounded size v d) (huv : ∀ a, u a ≤ v a) :
    DegreeBounded size u d :=
  let ⟨c, hv⟩ := h
  ⟨c, fun a => (huv a).trans (hv a)⟩

public theorem mono_deg (h : DegreeBounded size u d₁) (hd : d₁ ≤ d₂) : DegreeBounded size u d₂ :=
  let ⟨c, hu⟩ := h
  ⟨c, fun a => (hu a).trans (Nat.mul_le_mul_left c (Nat.pow_le_pow_right (Nat.succ_pos _) hd))⟩

public theorem const (k : ℕ) : DegreeBounded size (fun _ => k) d :=
  ⟨k, fun _ => Nat.le_mul_of_pos_right k (Nat.pow_pos (Nat.succ_pos _))⟩

public theorem self : DegreeBounded size size 1 :=
  ⟨1, fun _ => by simp⟩

public theorem add (hu : DegreeBounded size u d) (hv : DegreeBounded size v d) :
    DegreeBounded size (fun a => u a + v a) d :=
  let ⟨c₁, h₁⟩ := hu
  let ⟨c₂, h₂⟩ := hv
  ⟨c₁ + c₂, fun a => (add_le_add (h₁ a) (h₂ a)).trans_eq (Nat.add_mul _ _ _).symm⟩

/-- Adding bounds of different degrees gives a bound of their maximum degree. -/
public theorem add_max (hu : DegreeBounded size u d₁) (hv : DegreeBounded size v d₂) :
    DegreeBounded size (fun a => u a + v a) (max d₁ d₂) :=
  (hu.mono_deg (le_max_left _ _)).add (hv.mono_deg (le_max_right _ _))

public theorem smul (k : ℕ) (hu : DegreeBounded size u d) :
    DegreeBounded size (fun a => k * u a) d :=
  let ⟨c, h⟩ := hu
  ⟨k * c, fun a => (Nat.mul_le_mul_left k (h a)).trans_eq (Nat.mul_assoc _ _ _).symm⟩

public theorem add_const (k : ℕ) (hu : DegreeBounded size u d) :
    DegreeBounded size (fun a => u a + k) d :=
  hu.add (const k)

public theorem mul (hu : DegreeBounded size u d₁) (hv : DegreeBounded size v d₂) :
    DegreeBounded size (fun a => u a * v a) (d₁ + d₂) :=
  let ⟨c₁, h₁⟩ := hu
  let ⟨c₂, h₂⟩ := hv
  ⟨c₁ * c₂, fun a => (Nat.mul_le_mul (h₁ a) (h₂ a)).trans_eq (by rw [Nat.pow_add]; ring)⟩

/-- Substitution: if `v` has degree `d₂` in `size'` and `size' ∘ g` has degree `d₁` in `size`,
then `v ∘ g` has degree `d₁ * d₂` in `size`. -/
public theorem comp {size' : β → ℕ} {v : β → ℕ} {g : α → β} (hv : DegreeBounded size' v d₂)
    (hg : DegreeBounded size (fun a => size' (g a)) d₁) :
    DegreeBounded size (fun a => v (g a)) (d₁ * d₂) :=
  let ⟨c₁, h₁⟩ := hg
  let ⟨c₂, h₂⟩ := hv
  ⟨c₂ * (c₁ + 1) ^ d₂, fun a => by
    have h : size' (g a) + 1 ≤ (c₁ + 1) * (size a + 1) ^ d₁ := by
      have := h₁ a
      dsimp only at this
      have := Nat.one_le_pow d₁ (size a + 1) (Nat.succ_pos _)
      rw [Nat.add_one_mul]
      omega
    refine (h₂ (g a)).trans ((Nat.mul_le_mul_left c₂ (Nat.pow_le_pow_left h d₂)).trans_eq ?_)
    rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_assoc]⟩

end DegreeBounded

namespace DegreeBounded

variable {α β : Type*} {size : α → ℕ} {u v : α → ℕ} {d d₁ d₂ : ℕ}

public theorem polyBounded (h : DegreeBounded size u d) : PolyBounded size u :=
  let ⟨c, hu⟩ := h
  .of_forall_le c d hu

end DegreeBounded

end Turing.MultiTapeTM
