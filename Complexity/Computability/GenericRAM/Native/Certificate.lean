/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Halting.Computable.Defs
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-!
# Plain native certificates with independent resource bounds

A certificate records arbitrary input-dependent time/workspace bounds and a proposition asserting
that a finite machine realizes its function within them, including the encoded-output charge. The
machine is existential in that proposition, not stored as data. Exact constructors charge output
using its actual clock, so their workspace allowance is exactly `s + t`. Runtime model programs are
defined separately.

## Main definitions

* `NativeCertificate`: one implementation with independent, charged resource bounds.

## Main results

* `Cslib.GenericRAM.exists_mono_poly`, `Cslib.GenericRAM.exists_mono_poly_cert`: monotone polynomial
  bounds extracted from `PolyBounded` and `ComputableInPolyTime`.
-/

@[expose] public section
namespace Cslib.GenericRAM

open Turing.MultiTapeTM

/-- An actual native implementation, with bounds also charging its encoded output length. -/
structure NativeCertificate {α β : Type} (f : α → β)
    (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) where
  /-- Input-dependent time bound, up to a constant factor and additive constant. -/
  time : α → ℕ
  /-- Input-dependent work space and encoded output bound, up to constants. -/
  space : α → ℕ
  /-- One finite machine implements the function on every encoded input. -/
  computes : ComputableInO f encIn encOut time space

namespace NativeCertificate

variable {α β γ : Type} {f : α → β} {g : β → γ}
  {encIn : α ↪ List Bool} {encMid : β ↪ List Bool} {encOut : γ ↪ List Bool}

/-- Forgetting resource bounds retains native computability. -/
theorem isComputable (c : NativeCertificate f encIn encMid) :
    IsComputable f encIn encMid := by
  obtain ⟨_, h, _⟩ := c.computes
  exact h.isComputable

/-- Polynomiality is a separate property of both bounds in the encoded input length. -/
def IsPolynomial (c : NativeCertificate f encIn encMid) : Prop :=
  PolyBounded (fun a => (encIn a).length) c.time ∧
    PolyBounded (fun a => (encIn a).length) c.space

/-- Derive the existing native polynomial-time predicate, for use by its compositional calculus. -/
theorem polyTime (c : NativeCertificate f encIn encMid) (h : c.IsPolynomial) :
    ComputableInPolyTime f encIn encMid :=
  c.computes.computableInPolyTime h.1 h.2

/-- Compose implementations, charging the second bound at the first result. -/
def comp (d : NativeCertificate g encMid encOut) (c : NativeCertificate f encIn encMid) :
    NativeCertificate (g ∘ f) encIn encOut where
  time a := c.time a + d.time (f a)
  space a := c.space a + d.space (f a)
  computes := d.computes.comp c.computes

/-- Composing polynomial certificates preserves polynomiality in the original input encoding. -/
theorem comp_isPolynomial (d : NativeCertificate g encMid encOut)
    (c : NativeCertificate f encIn encMid) (hd : d.IsPolynomial) (hc : c.IsPolynomial) :
    (d.comp c).IsPolynomial :=
  ⟨hc.1.add (hd.1.comp (c.polyTime hc).polyBounded_length),
    hc.2.add (hd.2.comp (c.polyTime hc).polyBounded_length)⟩

/-- Package exact native bounds, including the running time in the space allowance to charge
encoded output length. No polynomial hypothesis is needed. -/
def ofTimeAndSpace {t s : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encMid t s) :
    NativeCertificate f encIn encMid where
  time := t
  space a := s a + t a
  computes := .of_bounds h 1 (fun _ => by simp)
    (fun _ => by simp; omega) (fun a => by
      have := h.length_le a
      simp only [one_mul]
      omega)

/-- Arbitrary-bound certificates impose exactly native computability, not an efficiency
assumption. Polynomial resource bounds remain a separate property. -/
theorem nonempty_iff_isComputable :
    Nonempty (NativeCertificate f encIn encMid) ↔ IsComputable f encIn encMid := by
  refine ⟨fun ⟨c⟩ => c.isComputable, fun h => ?_⟩
  obtain ⟨t, s, h⟩ := h
  exact ⟨ofTimeAndSpace h⟩

/-- Every native polynomial-time proof supplies a certificate with polynomial bounds. The space
bound includes the running time so that it also bounds the emitted output. -/
theorem exists_polynomial (h : ComputableInPolyTime f encIn encMid) :
    ∃ c : NativeCertificate f encIn encMid, c.IsPolynomial := by
  obtain ⟨t, s, ht, hs, hf⟩ := h
  exact ⟨ofTimeAndSpace hf,
    PolyBounded.of_polynomiallyBounded _ ht,
    (PolyBounded.of_polynomiallyBounded _ hs).add (PolyBounded.of_polynomiallyBounded _ ht)⟩

/-- Select resource bounds from an existing polynomial-time implementation proof. -/
noncomputable def ofPolyTime (h : ComputableInPolyTime f encIn encMid) :
    NativeCertificate f encIn encMid := (exists_polynomial h).choose

/-- Bounds selected by `ofPolyTime` are polynomial in the encoded input length. -/
theorem ofPolyTime_isPolynomial (h : ComputableInPolyTime f encIn encMid) :
    (ofPolyTime h).IsPolynomial := (exists_polynomial h).choose_spec

end NativeCertificate

/-- Extract an explicit monotone polynomial bound from a `PolyBounded` witness. -/
theorem exists_mono_poly {α : Type} {size u : α → ℕ} (hu : PolyBounded size u) :
    ∃ p : ℕ → ℕ, Cslib.PolynomiallyBounded p ∧ Monotone p ∧ ∀ a, u a ≤ p (size a) := by
  obtain ⟨c, d, h⟩ := hu.exists_le
  exact ⟨fun n => c * (n + 1) ^ d, by fun_prop,
    fun _ _ hxy => Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.add_le_add_right hxy 1) d), h⟩

/-- Extract a single monotone polynomial bounding both time and workspace of
`NativeCertificate.ofPolyTime hf`. -/
theorem exists_mono_poly_cert {α β : Type} {f : α → β}
    {ei : α ↪ List Bool} {eo : β ↪ List Bool} (hf : ComputableInPolyTime f ei eo) :
    ∃ p : ℕ → ℕ, Cslib.PolynomiallyBounded p ∧ Monotone p ∧
      ∀ a, (NativeCertificate.ofPolyTime hf).time a ≤ p (ei a).length ∧
        (NativeCertificate.ofPolyTime hf).space a ≤ p (ei a).length := by
  have hc := NativeCertificate.ofPolyTime_isPolynomial hf
  obtain ⟨p, hp, hmono, hle⟩ := exists_mono_poly (hc.1.add hc.2)
  exact ⟨p, hp, hmono, fun a => ⟨by have := hle a; omega, by have := hle a; omega⟩⟩

end Cslib.GenericRAM
