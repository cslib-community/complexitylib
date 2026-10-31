/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native.Combinators

/-!
# Certificates in time `2 ^ E` times a polynomial and polynomial space

A native certificate runs *in time `2 ^ E` times a polynomial and in polynomial space*
(`Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace`) when, for constants `C` and `d`, its time is
at most `C 2 ^ E a (n + 1) ^ d` and its space at most `C (n + 1) ^ d` on inputs `a` of encoded
length `n`. This shape survives pairing, which adds the exponents
(`Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace.prod`), and polynomial-time postprocessing,
since a polynomial space bound also bounds the encoded intermediate value
(`Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace.comp_ofPolyTime`). Simulations that run a few
exponential-time subroutines and combine their answers in polynomial time are assembled this way.

## Main definitions

* `Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace`.

## Main results

* `Cslib.GenericRAM.NativeCertificate.expTimePolySpace_ofPolyTime`: polynomial-time certificates.
* `Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace.prod`,
  `Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace.comp_ofPolyTime`: pairs and
  polynomial-time postprocessing.
* `Cslib.GenericRAM.NativeCertificate.ExpTimePolySpace.computableInO`: the resulting machine bounds.
-/

public section

namespace Cslib.GenericRAM.NativeCertificate

open Turing.MultiTapeTM

variable {α β γ : Type} {enc : α ↪ List Bool} {eβ : β ↪ List Bool} {eγ : γ ↪ List Bool}
  {f : α → β} {g : α → γ}

/-- A certificate **runs in time `2 ^ E` times a polynomial and in polynomial space**: for constants
`C` and `d`, its time is at most `C 2 ^ E a (n + 1) ^ d` and its space at most `C (n + 1) ^ d` on
inputs `a` of encoded length `n`. -/
@[expose] def ExpTimePolySpace (c : NativeCertificate f enc eβ) (E : α → ℕ) : Prop :=
  ∃ C d : ℕ, ∀ a, c.time a ≤ C * 2 ^ E a * ((enc a).length + 1) ^ d ∧
    c.space a ≤ C * ((enc a).length + 1) ^ d

private theorem pow_le_pow_of_le {a d d' : ℕ} (h : d ≤ d') : (a + 1) ^ d ≤ (a + 1) ^ d' :=
  Nat.pow_le_pow_right (Nat.succ_pos a) h

namespace ExpTimePolySpace

variable {c : NativeCertificate f enc eβ} {E E' : α → ℕ}

theorem mono (h : c.ExpTimePolySpace E) (hE : ∀ a, E a ≤ E' a) : c.ExpTimePolySpace E' := by
  obtain ⟨C, d, h⟩ := h
  exact ⟨C, d, fun a => ⟨(h a).1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right (by norm_num) (hE a)))), (h a).2⟩⟩

/-- **Pairs add the exponents.** -/
theorem prod {c' : NativeCertificate g enc eγ} (h : c.ExpTimePolySpace E)
    (h' : c'.ExpTimePolySpace E') : (c.prod c').ExpTimePolySpace fun a => E a + E' a := by
  obtain ⟨C, d, h⟩ := h
  obtain ⟨C', d', h'⟩ := h'
  refine ⟨C + C', d + d', fun a => ?_⟩
  have hd := pow_le_pow_of_le (a := (enc a).length) (Nat.le_add_right d d')
  have hd' := pow_le_pow_of_le (a := (enc a).length) (Nat.le_add_left d' d)
  have hE := Nat.le_mul_of_pos_right (2 ^ E a) (Nat.two_pow_pos (E' a))
  have hE' := Nat.le_mul_of_pos_left (2 ^ E' a) (Nat.two_pow_pos (E a))
  rw [prod_time, prod_space, pow_add 2 (E a) (E' a)]
  constructor
  · calc c.time a + c'.time a
        ≤ C * 2 ^ E a * ((enc a).length + 1) ^ d + C' * 2 ^ E' a * ((enc a).length + 1) ^ d' :=
          Nat.add_le_add (h a).1 (h' a).1
      _ ≤ C * (2 ^ E a * 2 ^ E' a) * ((enc a).length + 1) ^ (d + d') +
          C' * (2 ^ E a * 2 ^ E' a) * ((enc a).length + 1) ^ (d + d') := by
          gcongr
      _ = _ := by ring
  · calc c.space a + c'.space a
        ≤ C * ((enc a).length + 1) ^ d + C' * ((enc a).length + 1) ^ d' :=
          Nat.add_le_add (h a).2 (h' a).2
      _ ≤ C * ((enc a).length + 1) ^ (d + d') + C' * ((enc a).length + 1) ^ (d + d') := by
          gcongr
      _ = _ := by ring

/-- **Polynomial-time postprocessing keeps the shape**: the polynomial space bound also bounds the
encoded intermediate value, on which the postprocessing runs. -/
theorem comp_ofPolyTime (h : c.ExpTimePolySpace E) {r : β → γ}
    (hr : ComputableInPolyTime r eβ eγ) : ((ofPolyTime hr).comp c).ExpTimePolySpace E := by
  obtain ⟨C, d, h⟩ := h
  obtain ⟨K₀, -, hK₀⟩ := c.computes
  have hp := ofPolyTime_isPolynomial hr
  obtain ⟨ct, dt, ht⟩ := hp.1.exists_le
  obtain ⟨cs, ds, hs⟩ := hp.2.exists_le
  set D := K₀ * C + K₀ + 1
  -- the encoded intermediate value
  have hlen (a : α) : (eβ (f a)).length + 1 ≤ D * ((enc a).length + 1) ^ d := by
    have h1 := hK₀ a
    have h2 := (h a).2
    have h3 : 1 ≤ ((enc a).length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
    simp only [D]
    nlinarith
  have hpoly {c₀ d₀ : ℕ} {u : β → ℕ} (hu : ∀ b, u b ≤ c₀ * ((eβ b).length + 1) ^ d₀) (a : α) :
      u (f a) ≤ c₀ * D ^ d₀ * ((enc a).length + 1) ^ (d * d₀) := by
    refine (hu (f a)).trans ?_
    calc c₀ * ((eβ (f a)).length + 1) ^ d₀ ≤ c₀ * (D * ((enc a).length + 1) ^ d) ^ d₀ :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hlen a) d₀)
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  refine ⟨C + ct * D ^ dt + cs * D ^ ds, d + d * dt + d * ds, fun a => ?_⟩
  set Y := ((enc a).length + 1) ^ (d + d * dt + d * ds)
  have hY {e : ℕ} (he : e ≤ d + d * dt + d * ds) : ((enc a).length + 1) ^ e ≤ Y :=
    pow_le_pow_of_le he
  have hZ : Y ≤ 2 ^ E a * Y := Nat.le_mul_of_pos_left Y (Nat.two_pow_pos (E a))
  rw [comp_time, comp_space]
  constructor
  · calc c.time a + (ofPolyTime hr).time (f a)
        ≤ C * 2 ^ E a * ((enc a).length + 1) ^ d +
            ct * D ^ dt * ((enc a).length + 1) ^ (d * dt) :=
          Nat.add_le_add (h a).1 (hpoly ht a)
      _ ≤ C * 2 ^ E a * Y + ct * D ^ dt * (2 ^ E a * Y) :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (hY (e := d) (by omega)))
            (Nat.mul_le_mul_left _ ((hY (e := d * dt) (by omega)).trans hZ))
      _ = (C + ct * D ^ dt) * 2 ^ E a * Y := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  · calc c.space a + (ofPolyTime hr).space (f a)
        ≤ C * ((enc a).length + 1) ^ d + cs * D ^ ds * ((enc a).length + 1) ^ (d * ds) :=
          Nat.add_le_add (h a).2 (hpoly hs a)
      _ ≤ C * Y + cs * D ^ ds * Y :=
          Nat.add_le_add (Nat.mul_le_mul_left _ (hY (e := d) (by omega)))
            (Nat.mul_le_mul_left _ (hY (e := d * ds) (by omega)))
      _ = (C + cs * D ^ ds) * Y := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

/-- **The machine bounds** of a certificate in time `2 ^ E` times a polynomial and polynomial
space. -/
theorem computableInO (h : c.ExpTimePolySpace E) : ∃ e : ℕ,
    ComputableInO f enc eβ (fun a => 2 ^ E a * ((enc a).length + 1) ^ e)
      (fun a => ((enc a).length + 1) ^ e) := by
  obtain ⟨C, d, h⟩ := h
  refine ⟨d, c.computes.mono C (fun a => (h a).1.trans ?_) (fun a => (h a).2.trans ?_)⟩
  · rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.le_succ _)
  · exact Nat.mul_le_mul_left _ (Nat.le_succ _)

end ExpTimePolySpace

/-- **Polynomial-time certificates** run in time `2 ^ E` times a polynomial for every `E`. -/
theorem expTimePolySpace_ofPolyTime (hf : ComputableInPolyTime f enc eβ) (E : α → ℕ) :
    (ofPolyTime hf).ExpTimePolySpace E := by
  have hp := ofPolyTime_isPolynomial hf
  obtain ⟨ct, dt, ht⟩ := hp.1.exists_le
  obtain ⟨cs, ds, hs⟩ := hp.2.exists_le
  refine ⟨ct + cs, dt + ds, fun a => ⟨(ht a).trans ?_, (hs a).trans ?_⟩⟩
  · rw [Nat.mul_assoc]
    exact Nat.mul_le_mul (by omega) ((pow_le_pow_of_le (Nat.le_add_right _ _)).trans
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)))
  · exact Nat.mul_le_mul (by omega) (pow_le_pow_of_le (Nat.le_add_left _ _))

end Cslib.GenericRAM.NativeCertificate
