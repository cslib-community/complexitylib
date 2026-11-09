/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Exponential

/-!
# Exponentials of polynomial-time exponents

For an exponent `L x` computable in unary in polynomial time, `2 ^ L x` is computable in unary
within time `O(2 ^ |x| + 4 ^ L x)` and space `O(2 ^ |x| + 2 ^ L x)`
(`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_unary_two_pow`): compute `L x`,
then double `L x` times (`Turing.MultiTapeTM.ComputableInO.unary_two_pow`). The polynomial cost
of computing the exponent is absorbed by `2 ^ |x|`
(`Turing.MultiTapeTM.PolyBounded.exists_le_mul_two_pow`).

*Padding.* If `f` is polynomial-time on pairs `(a, N)` with `N` in unary, then
`a ↦ f (a, 2 ^ ν a)` is computable within time and space `C 2 ^ (D ν a) (|a| + 1) ^ D`, for an
exponent `ν` computable in unary in polynomial time
(`Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_pad`). This turns a polynomial-time
algorithm on padded inputs into a `2 ^ O(ν a)`-time algorithm on the original input.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_unary_two_pow`: `2 ^ L x` in
  unary within exponential time and space.
* `Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO_pad`: polynomial time on inputs
  padded by `2 ^ ν a` gives time and space `2 ^ O(ν a)` times a polynomial in `|a|`.
-/

public section

namespace Turing.MultiTapeTM

/-- **`2 ^ L x` in unary**, for an exponent `L x` computable in unary in polynomial time, within
time `O(2 ^ |x| + 4 ^ L x)` and space `O(2 ^ |x| + 2 ^ L x)`. -/
theorem ComputableInPolyTime.exists_computableInO_unary_two_pow {α : Type} {enc : α ↪ List Bool}
    {L : α → ℕ} (hL : ComputableInPolyTime L enc encUnary) :
    ∃ C, ComputableInO (fun x => 2 ^ L x) enc encUnary
      (fun x => C * 2 ^ (enc x).length + 4 ^ L x) (fun x => C * 2 ^ (enc x).length + 2 ^ L x) := by
  obtain ⟨T, S, hT, hS, h⟩ := hL.exists_computableInO
  obtain ⟨C₁, hC₁⟩ := hT.exists_le_mul_two_pow
  obtain ⟨C₂, hC₂⟩ := hS.exists_le_mul_two_pow
  refine ⟨C₁ + C₂, (ComputableInO.unary_two_pow.comp h).mono_le (fun x => ?_) fun x => ?_⟩
  · have h₁ := hC₁ x
    have h₂ : (L x + 1) * 2 ^ L x ≤ 4 ^ L x := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, mul_pow]
      exact Nat.mul_le_mul_right _ Nat.lt_two_pow_self
    have h₃ : C₁ * 2 ^ (enc x).length ≤ (C₁ + C₂) * 2 ^ (enc x).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · have h₁ := hC₂ x
    have h₃ : C₂ * 2 ^ (enc x).length ≤ (C₁ + C₂) * 2 ^ (enc x).length :=
      Nat.mul_le_mul_right _ (by omega)
    omega

/-- The arithmetic of padding: with `P = 2 ^ n * (L + 1)`, the cost of writing the padding and of
two computations within `c₁ (L + 1) ^ d₁` and `c₂ (|padded| + 1) ^ d₂` is `O(P ^ D)`. -/
private theorem pad_bound_le {L n t₁ e t₂ c₁ d₁ c₂ d₂ D : ℕ}
    (ht₁ : t₁ ≤ c₁ * (L + 1) ^ d₁) (he : e ≤ (n + 1) * 2 ^ n)
    (ht₂ : t₂ ≤ c₂ * (2 * L + 1 + 2 ^ n + 1) ^ d₂) (hd₁ : d₁ ≤ D) (hd₂ : d₂ ≤ D)
    (hD : 2 ≤ D) :
    L + (t₁ + e) + t₂ ≤ (2 + c₁ + c₂ * 4 ^ D) * 2 ^ (D * n) * (L + 1) ^ D := by
  have hPD' : 2 ^ (D * n) * (L + 1) ^ D = (2 ^ n * (L + 1)) ^ D := by
    rw [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_comm n D]
  rw [Nat.mul_assoc, hPD']
  set P := 2 ^ n * (L + 1) with hP
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hLP : L + 1 ≤ P := Nat.le_mul_of_pos_left _ h2n
  have h2P : 2 ^ n ≤ P := Nat.le_mul_of_pos_right _ (Nat.succ_pos L)
  have hn : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have hP1 : 1 ≤ P := le_trans h2n h2P
  have hPD : P ≤ P ^ D := Nat.le_self_pow (by omega) P
  have hPP : P * P ≤ P ^ D := by
    rw [← pow_two]
    exact Nat.pow_le_pow_right hP1 hD
  have hpad : 2 * L + 1 + 2 ^ n + 1 ≤ 4 * P := by omega
  have h₁ : (L + 1) ^ d₁ ≤ P ^ D :=
    (Nat.pow_le_pow_left hLP d₁).trans (Nat.pow_le_pow_right hP1 hd₁)
  have h₂ : (2 * L + 1 + 2 ^ n + 1) ^ d₂ ≤ 4 ^ D * P ^ D := by
    rw [← Nat.mul_pow]
    exact (Nat.pow_le_pow_left hpad d₂).trans (Nat.pow_le_pow_right (by omega) hd₂)
  have he' : e ≤ P * P := he.trans (Nat.mul_le_mul (hn.trans h2P) h2P)
  have ht₁' := ht₁.trans (Nat.mul_le_mul_left c₁ h₁)
  have ht₂' := ht₂.trans (Nat.mul_le_mul_left c₂ h₂)
  have hLP' : L ≤ P := by omega
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc c₂]
  linarith

/-- **Polynomial time on padded inputs.** If `f` is polynomial-time on pairs `(a, N)` with `N` in
unary, then `a ↦ f (a, 2 ^ ν a)` is computable within time and space `C 2 ^ (D ν a) (|a| + 1) ^ D`,
for an exponent `ν` computable in unary in polynomial time: write the padding `2 ^ ν a` in unary,
then run `f`. -/
theorem ComputableInPolyTime.exists_computableInO_pad {α β : Type} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α × ℕ → β} {ν : α → ℕ}
    (hf : ComputableInPolyTime f (encPair encIn encUnary) encOut)
    (hν : ComputableInPolyTime ν encIn encUnary) :
    ∃ C D : ℕ, ComputableInO (fun a => f (a, 2 ^ ν a)) encIn encOut
      (fun a => C * 2 ^ (D * ν a) * ((encIn a).length + 1) ^ D)
      (fun a => C * 2 ^ (D * ν a) * ((encIn a).length + 1) ^ D) := by
  obtain ⟨Tν, Sν, hTν, hSν, hνO⟩ := hν.exists_computableInO
  obtain ⟨Tf, Sf, hTf, hSf, hfO⟩ := hf.exists_computableInO
  obtain ⟨c₁, d₁, h₁⟩ := hTν.exists_le
  obtain ⟨c₁', d₁', h₁'⟩ := hSν.exists_le
  obtain ⟨c₂, d₂, h₂⟩ := hTf.exists_le
  obtain ⟨c₂', d₂', h₂'⟩ := hSf.exists_le
  have hpad := (ComputableInO.of_eq (f := fun a : α => a) (encMid := encIn) fun _ => rfl).prod
    (ComputableInO.unary_two_pow.comp hνO)
  have hcomp := hfO.comp hpad
  set D := d₁ + d₁' + d₂ + d₂' + 2
  have hlen (a : α) : (encPair encIn encUnary (a, 2 ^ ν a)).length + 1 =
      2 * (encIn a).length + 1 + 2 ^ ν a + 1 := by
    simp only [length_encPair, encUnary_apply, List.length_replicate]
  refine ⟨(2 + c₁ + c₂ * 4 ^ D) + (2 + c₁' + c₂' * 4 ^ D), D,
    hcomp.mono_le (fun a => ?_) fun a => ?_⟩
  · have := pad_bound_le (L := (encIn a).length) (n := ν a) (D := D) (e := (ν a + 1) * 2 ^ ν a)
      (h₁ a) le_rfl (hlen a ▸ h₂ (a, 2 ^ ν a)) (by omega) (by omega) (by omega)
    refine this.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_))
    omega
  · have := pad_bound_le (L := (encIn a).length) (n := ν a) (D := D) (e := 2 ^ ν a)
      (h₁' a) (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) (hlen a ▸ h₂' (a, 2 ^ ν a))
      (by omega) (by omega) (by omega)
    refine this.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_))
    omega

end Turing.MultiTapeTM
