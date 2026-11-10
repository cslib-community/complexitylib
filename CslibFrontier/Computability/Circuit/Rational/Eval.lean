/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Rational.Defs

/-!
# Rational hitting lists: evaluation

Basic properties of the partial evaluation of rational formulas: values are unique, they are
transported along ring homomorphisms, and they lift back along homomorphisms reflecting units.

## Main results

* `Cslib.Circuits.Rational.Formula.Eval.unique`: a formula has at most one value.
* `Cslib.Circuits.Rational.Formula.Eval.map`: values are mapped by ring homomorphisms.
* `Cslib.Circuits.Rational.Formula.Eval.lift`: values lift along homomorphisms reflecting units.
* `Cslib.Circuits.Rational.Formula.Eval.unit_of_division_lift`: a nonzero value mapped out of a
  division ring is a unit.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/Evaluation.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational

namespace Formula

variable {n : ℕ} {R S : Type*} [Ring R] [Ring S]

/-- A formula has at most one value at a substitution. -/
theorem Eval.unique {c : ℚ →+* R} {X : Fin n → R} {h : Formula n} {a b : R}
    (ha : h.Eval c X a) (hb : h.Eval c X b) : a = b := by
  induction h using inductionOn generalizing a b with
  | var i => exact (eval_var_iff.mp ha).trans (eval_var_iff.mp hb).symm
  | const q => exact (eval_const_iff.mp ha).trans (eval_const_iff.mp hb).symm
  | add f g ihf ihg =>
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := eval_add_iff.mp ha
    obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := eval_add_iff.mp hb
    rw [ihf ha₁ hb₁, ihg ha₂ hb₂]
  | mul f g ihf ihg =>
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := eval_mul_iff.mp ha
    obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := eval_mul_iff.mp hb
    rw [ihf ha₁ hb₁, ihg ha₂ hb₂]
  | inv f ih =>
    obtain ⟨a', ha', -, hva⟩ := eval_inv_iff.mp ha
    obtain ⟨b', hb', hbw, -⟩ := eval_inv_iff.mp hb
    obtain rfl := ih ha' hb'
    calc
      a = a * (a' * b) := by rw [hbw, mul_one]
      _ = b := by rw [← mul_assoc, hva, one_mul]

/-- A ring homomorphism maps a value of a formula to a value at the mapped substitution. -/
theorem Eval.map {c : ℚ →+* R} {X : Fin n → R} {h : Formula n} {a : R}
    (ha : h.Eval c X a) (f : R →+* S) :
    h.Eval (f.comp c) (fun i => f (X i)) (f a) := by
  induction h using inductionOn generalizing a with
  | var i => rw [eval_var_iff.mp ha]; exact .var i
  | const q => rw [eval_const_iff.mp ha]; exact .const q
  | add g k ihg ihk =>
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := eval_add_iff.mp ha
    simpa only [map_add] using Eval.add (ihg ha₁) (ihk ha₂)
  | mul g k ihg ihk =>
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := eval_mul_iff.mp ha
    simpa only [map_mul] using Eval.mul (ihg ha₁) (ihk ha₂)
  | inv g ih =>
    obtain ⟨b, hb, hba, hab⟩ := eval_inv_iff.mp ha
    exact .inv (ih hb) (by rw [← map_mul, hba, map_one]) (by rw [← map_mul, hab, map_one])

/-- Defined evaluations lift through a homomorphism reflecting units. In particular this handles
every inverse occurrence before considering the root. -/
theorem Eval.lift (f : R →+* S) (hf : ∀ x, IsUnit (f x) → IsUnit x)
    {c : ℚ →+* R} {X : Fin n → R} {h : Formula n} {a : S}
    (ha : h.Eval (f.comp c) (fun i => f (X i)) a) :
    ∃ b : R, h.Eval c X b ∧ f b = a := by
  induction h using inductionOn generalizing a with
  | var i => exact ⟨X i, .var i, (eval_var_iff.mp ha).symm⟩
  | const q => exact ⟨c q, .const q, (eval_const_iff.mp ha).symm⟩
  | add g k ihg ihk =>
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := eval_add_iff.mp ha
    obtain ⟨b₁, hb₁, rfl⟩ := ihg ha₁
    obtain ⟨b₂, hb₂, rfl⟩ := ihk ha₂
    exact ⟨b₁ + b₂, .add hb₁ hb₂, map_add f b₁ b₂⟩
  | mul g k ihg ihk =>
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := eval_mul_iff.mp ha
    obtain ⟨b₁, hb₁, rfl⟩ := ihg ha₁
    obtain ⟨b₂, hb₂, rfl⟩ := ihk ha₂
    exact ⟨b₁ * b₂, .mul hb₁ hb₂, map_mul f b₁ b₂⟩
  | inv g ih =>
    obtain ⟨b, hb, hba, hab⟩ := eval_inv_iff.mp ha
    obtain ⟨b', hb', rfl⟩ := ih hb
    obtain ⟨u, hu⟩ := hf b' ⟨⟨f b', a, hba, hab⟩, rfl⟩
    have heval : (Formula.inv g).Eval c X (↑u⁻¹ : R) :=
      .inv hb' (by rw [← hu]; exact u.mul_inv) (by rw [← hu]; exact u.inv_mul)
    exact ⟨_, heval, (heval.map f).unique ha⟩

/-- Mapping a defined nonzero value out of a division ring makes it a unit. This is used after the
partial-specialization domain proof, not instead of it. -/
theorem Eval.unit_of_division_lift {D : Type*} [DivisionRing D] [Nontrivial R]
    (f : D →+* R) {c : ℚ →+* D} {X : Fin n → D} {h : Formula n} {a : R}
    (ha : h.Eval (f.comp c) (fun i => f (X i)) a) (ha0 : a ≠ 0) : IsUnit a := by
  have hf : ∀ x, IsUnit (f x) → IsUnit x := by
    intro x hx
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    exact hx.ne_zero (by rw [hzero, map_zero])
  obtain ⟨b, hb, heq⟩ := ha.lift f hf
  have hb0 : b ≠ 0 := by
    intro h
    apply ha0
    rw [← heq, h, map_zero]
  exact heq ▸ (isUnit_iff_ne_zero.mpr hb0).map f

end Formula

end Rational

end Cslib.Circuits
