/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native.Certificate

/-!
# Polynomial preprocessing and decoding of native algorithms

A polynomial-time preprocessing and a polynomial-time decoder preserve a common running-time
factor when the intermediate native algorithm uses polynomial space. The space hypothesis also
bounds the encoded intermediate output, so the decoder does not multiply the exponential factor.

## Main results

* `NativeCertificate.exists_polynomial_overhead`: uniform polynomial overhead for a native
  algorithm between two polynomial-time transformations, with an arbitrary factor at least one.
-/

public section

namespace Cslib.GenericRAM.NativeCertificate

open Turing.MultiTapeTM

variable {α β γ δ : Type} {ei : α ↪ List Bool} {eb : β ↪ List Bool}
  {ec : γ ↪ List Bool} {eo : δ ↪ List Bool} {prepare : α → β} {f : β → γ} {decode : γ → δ}

/-- Polynomial-time preprocessing and decoding preserve an arbitrary time factor `X ≥ 1`,
provided the intermediate output is charged to polynomial space. The constant is selected before
the input and before `X`. -/
theorem exists_polynomial_overhead (c : NativeCertificate f eb ec)
    (hp : ComputableInPolyTime prepare ei eb) (hd : ComputableInPolyTime decode ec eo) (K : ℕ) :
    ∃ K' : ℕ, ∀ (a : α) (X : ℕ), 1 ≤ X →
      c.time (prepare a) ≤ K * ((eb (prepare a)).length + 1) ^ K * X →
      c.space (prepare a) ≤ K * ((eb (prepare a)).length + 1) ^ K →
      ((ofPolyTime hd).comp (c.comp (ofPolyTime hp))).time a ≤
          K' * ((ei a).length + 1) ^ K' * X ∧
        ((ofPolyTime hd).comp (c.comp (ofPolyTime hp))).space a ≤
          K' * ((ei a).length + 1) ^ K' := by
  obtain ⟨p, hpp, -, hple⟩ := exists_mono_poly_cert hp
  obtain ⟨q, hqp, hqm, hqle⟩ := exists_mono_poly_cert hd
  obtain ⟨aY, dY, hY⟩ := hp.polyBounded_length.exists_le
  obtain ⟨cO, -, hO⟩ := c.computes
  let Y : ℕ → ℕ := fun n => aY * (n + 1) ^ dY
  let Q : ℕ → ℕ := fun n => K * (Y n + 1) ^ K
  let F : ℕ → ℕ := fun n => p n + Q n + q (cO * (Q n + 1))
  have hYp : PolyBounded id Y :=
    (PolyBounded.const aY).mul ((PolyBounded.self.add (PolyBounded.const 1)).pow dY)
  have hQp : PolyBounded id Q :=
    (PolyBounded.const K).mul ((hYp.add (PolyBounded.const 1)).pow K)
  have hFp : PolyBounded id F :=
    ((PolyBounded.of_polynomiallyBounded id hpp).add hQp).add
      ((PolyBounded.of_polynomiallyBounded id hqp).comp
        ((PolyBounded.const cO).mul (hQp.add (PolyBounded.const 1))))
  obtain ⟨aF, dF, hF⟩ := hFp.exists_le
  refine ⟨aF + dF, fun a X hX ht hs => ?_⟩
  set n := (ei a).length
  have hQ : K * ((eb (prepare a)).length + 1) ^ K ≤ Q n :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (hY a) 1) K)
  have ht' : c.time (prepare a) ≤ Q n * X := ht.trans (Nat.mul_le_mul_right X hQ)
  have hs' : c.space (prepare a) ≤ Q n := hs.trans hQ
  have hlen : (ec (f (prepare a))).length ≤ cO * (Q n + 1) :=
    (hO (prepare a)).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hs' 1))
  have hdt : (ofPolyTime hd).time (f (prepare a)) ≤ q (cO * (Q n + 1)) :=
    (hqle (f (prepare a))).1.trans (hqm hlen)
  have hds : (ofPolyTime hd).space (f (prepare a)) ≤ q (cO * (Q n + 1)) :=
    (hqle (f (prepare a))).2.trans (hqm hlen)
  have hbound : F n ≤ (aF + dF) * (n + 1) ^ (aF + dF) :=
    (hF n).trans (Nat.mul_le_mul (by omega)
      (Nat.pow_le_pow_right (by omega) (by omega)))
  have hpt : (ofPolyTime hp).time a ≤ p n := (hple a).1
  have hps : (ofPolyTime hp).space a ≤ p n := (hple a).2
  change (ofPolyTime hp).time a + c.time (prepare a) +
      (ofPolyTime hd).time (f (prepare a)) ≤ _ ∧
    (ofPolyTime hp).space a + c.space (prepare a) +
      (ofPolyTime hd).space (f (prepare a)) ≤ _
  refine ⟨?_, ?_⟩
  · have hpX : p n ≤ p n * X := Nat.le_mul_of_pos_right _ hX
    have hqX : q (cO * (Q n + 1)) ≤ q (cO * (Q n + 1)) * X :=
      Nat.le_mul_of_pos_right _ hX
    calc (ofPolyTime hp).time a + c.time (prepare a) +
          (ofPolyTime hd).time (f (prepare a))
        ≤ p n * X + Q n * X + q (cO * (Q n + 1)) * X := by omega
      _ = F n * X := by simp only [F]; ring
      _ ≤ (aF + dF) * (n + 1) ^ (aF + dF) * X := Nat.mul_le_mul_right _ hbound
  · calc (ofPolyTime hp).space a + c.space (prepare a) +
          (ofPolyTime hd).space (f (prepare a))
        ≤ F n := by dsimp only [F]; omega
      _ ≤ (aF + dF) * (n + 1) ^ (aF + dF) := hbound

end Cslib.GenericRAM.NativeCertificate
