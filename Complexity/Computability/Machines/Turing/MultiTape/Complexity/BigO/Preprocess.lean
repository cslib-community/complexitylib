/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives

/-!
# Polynomial-time preprocessing of exponential bounds

A computation within time `2 ^ E` times a polynomial in the length of its input and within
polynomial space keeps bounds of this form when its input is first computed by a polynomial-time
map: the map takes polynomial time, and the length of its value is polynomial in the length of the
original input, so the polynomial factors compose
(`Turing.MultiTapeTM.ComputableInO.comp_polyTime`). Subexponential counters on encoded instances
thereby transfer along polynomial-time reductions from other encodings.

## Main results

* `Turing.MultiTapeTM.ComputableInO.comp_polyTime`: polynomial-time preprocessing keeps a time
  bound `2 ^ E` times a polynomial and a polynomial space bound.
-/

public section

namespace Turing.MultiTapeTM

variable {α β γ : Type} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- **Polynomial-time preprocessing keeps a time bound `2 ^ E` times a polynomial.** If `f` runs,
on the values of a polynomial-time map `g`, within time `2 ^ E a` times a polynomial in the length
of `g a` and within space polynomial in that length, then `f ∘ g` runs within time `2 ^ E a` times
a polynomial in the length of `a`, and within polynomial space. -/
theorem ComputableInO.comp_polyTime {f : β → γ} {g : α → β} {T S : β → ℕ} {E : α → ℕ}
    {e b : ℕ} (hf : ComputableInO f encMid encOut T S) (hg : ComputableInPolyTime g encIn encMid)
    (hT : ∀ a, T (g a) ≤ 2 ^ E a * ((encMid (g a)).length + 1) ^ e)
    (hS : ∀ a, S (g a) ≤ ((encMid (g a)).length + 1) ^ b) :
    ∃ e' b' : ℕ, ComputableInO (fun a => f (g a)) encIn encOut
      (fun a => 2 ^ E a * ((encIn a).length + 1) ^ e')
      (fun a => ((encIn a).length + 1) ^ b') := by
  obtain ⟨d, e₀, hdeg⟩ := hg.exists_degree
  obtain ⟨c, hlen⟩ := hdeg.2
  refine ⟨d + e₀ * e, d + e₀ * b, (hf.comp hdeg.inO).mono ((c + 1) ^ e + (c + 1) ^ b + 1)
    (fun a => ?_) (fun a => ?_)⟩
  all_goals
    set L := (encIn a).length + 1
    have hL : 1 ≤ L := Nat.le_add_left 1 _
    have hM : (encMid (g a)).length + 1 ≤ (c + 1) * L ^ e₀ := by
      have h1 : (encMid (g a)).length ≤ c * L ^ e₀ := hlen a
      have h2 : 1 ≤ L ^ e₀ := Nat.one_le_pow _ _ hL
      nlinarith
    have hpow {k : ℕ} : ((encMid (g a)).length + 1) ^ k ≤ (c + 1) ^ k * L ^ (e₀ * k) := by
      calc _ ≤ ((c + 1) * L ^ e₀) ^ k := Nat.pow_le_pow_left hM k
        _ = _ := by rw [mul_pow, ← pow_mul]
  · have h2 : 1 ≤ 2 ^ E a := Nat.one_le_two_pow
    have hd : L ^ d ≤ 2 ^ E a * L ^ (d + e₀ * e) :=
      (Nat.pow_le_pow_right hL (Nat.le_add_right _ _)).trans (Nat.le_mul_of_pos_left _ h2)
    have hT' : T (g a) ≤ (c + 1) ^ e * (2 ^ E a * L ^ (d + e₀ * e)) := by
      calc T (g a) ≤ 2 ^ E a * ((c + 1) ^ e * L ^ (e₀ * e)) :=
            (hT a).trans (Nat.mul_le_mul_left _ hpow)
        _ ≤ 2 ^ E a * ((c + 1) ^ e * L ^ (d + e₀ * e)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
              (Nat.pow_le_pow_right hL (Nat.le_add_left _ _)))
        _ = _ := by rw [Nat.mul_left_comm]
    calc L ^ d + T (g a)
        ≤ 2 ^ E a * L ^ (d + e₀ * e) + (c + 1) ^ e * (2 ^ E a * L ^ (d + e₀ * e)) :=
          Nat.add_le_add hd hT'
      _ = ((c + 1) ^ e + 1) * (2 ^ E a * L ^ (d + e₀ * e)) := by rw [Nat.add_mul, Nat.one_mul,
          Nat.add_comm]
      _ ≤ _ := Nat.mul_le_mul (by omega) (Nat.le_succ _)
  · have hd : L ^ d ≤ L ^ (d + e₀ * b) := Nat.pow_le_pow_right hL (Nat.le_add_right _ _)
    have hS' : S (g a) ≤ (c + 1) ^ b * L ^ (d + e₀ * b) :=
      (hS a).trans (hpow.trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right hL (Nat.le_add_left _ _))))
    calc L ^ d + S (g a) ≤ L ^ (d + e₀ * b) + (c + 1) ^ b * L ^ (d + e₀ * b) :=
          Nat.add_le_add hd hS'
      _ = ((c + 1) ^ b + 1) * L ^ (d + e₀ * b) := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      _ ≤ _ := Nat.mul_le_mul (by omega) (Nat.le_succ _)

end Turing.MultiTapeTM
