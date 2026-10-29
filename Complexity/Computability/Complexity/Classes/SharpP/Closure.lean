/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SharpP
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Mathlib.Algebra.Ring.Subring.Defs
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Algebra.Ring.Subsemiring.Basic

/-!
# Closure properties of #P and GapP

`#P` (`Cslib.Complexity.SharpP`) is closed under addition and multiplication
[Arora and Barak, Chapter 17][AroraBarak09], so it is a subsemiring of the functions to `ℕ`
(`Cslib.Complexity.SharpP.subsemiring`). Hence `GapP` (`Cslib.Complexity.GapP`), the differences of
functions in `#P`, is closed under addition, negation and multiplication, a subring of the
functions to `ℤ` (`Cslib.Complexity.GapP.subring`)
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994].

For the sum `f₁ + f₂`, the first bit of a certificate chooses which verifier to run
(`Cslib.Complexity.selectVerifier`); since the two verifiers read certificates of different
lengths `p₁(n)` and `p₂(n)`, each is padded to `p₁(n) + p₂(n)` bits by requiring the extra bits to
be `false` (`Cslib.Complexity.acceptCount_andVerifier_allFalseVerifier`). For the product, the two
verifiers read disjoint parts of the certificate (`Cslib.Complexity.acceptCount_andVerifier`).

## Main definitions

* `Cslib.Complexity.SharpP.subsemiring`: `#P` as a subsemiring.
* `Cslib.Complexity.GapP.subring`: `GapP` as a subring.

## Main results

* `Cslib.Complexity.SharpP.comp_mem`, `Cslib.Complexity.GapP.comp_mem`: polynomial-time
  precomposition, preserving counts exactly.

* `Cslib.Complexity.mem_SharpP_of_polyTime_length`: polynomial-time unary certificate lengths
  suffice.
* `Cslib.Complexity.SharpP.add_mem`, `Cslib.Complexity.SharpP.mul_mem`: `#P` is closed under
  addition and multiplication.
* `Cslib.Complexity.SharpP.one_mem`, `Cslib.Complexity.SharpP.add_one_mem`,
  `Cslib.Complexity.SharpP.natCast_mem`, `Cslib.Complexity.SharpP.sum_mem`,
  `Cslib.Complexity.SharpP.prod_mem`, `Cslib.Complexity.SharpP.pow_mem`,
  `Cslib.Complexity.SharpP.two_pow_mem`, `Cslib.Complexity.SharpP.two_pow_mul_mem`.
* `Cslib.Complexity.SharpP.exists_two_pow_sub_mem`: the complementary count of a function in `#P`.
* `Cslib.Complexity.GapP.add_mem`, `Cslib.Complexity.GapP.sub_mem'`,
  `Cslib.Complexity.GapP.mul_mem`: `GapP` is closed under addition, subtraction and
  multiplication.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

namespace SharpP

/-- **`#P` is closed under addition**: the first bit of a certificate chooses the verifier, and
the bits that the chosen verifier does not read must be `false`. -/
theorem add_mem {f₁ f₂ : α → ℕ} (h₁ : f₁ ∈ SharpP enc) (h₂ : f₂ ∈ SharpP enc) :
    f₁ + f₂ ∈ SharpP enc := by
  obtain ⟨p₁, V₁, hV₁, hf₁⟩ := mem_SharpP.mp h₁
  obtain ⟨p₂, V₂, hV₂, hf₂⟩ := mem_SharpP.mp h₂
  refine ⟨p₁ + p₂ + 1, selectVerifier
      (andVerifier (fun a => p₁.eval (enc a).length) V₁ allFalseVerifier)
      (andVerifier (fun a => p₂.eval (enc a).length) V₂ allFalseVerifier), by fun_prop,
    fun a => ?_⟩
  have e₁ := acceptCount_andVerifier_allFalseVerifier (fun a => p₁.eval (enc a).length) V₁ a
    (p₂.eval (enc a).length)
  have e₂ := acceptCount_andVerifier_allFalseVerifier (fun a => p₂.eval (enc a).length) V₂ a
    (p₁.eval (enc a).length)
  rw [Nat.add_comm (p₂.eval _)] at e₂
  rw [Pi.add_apply, hf₁ a, hf₂ a, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_one,
    acceptCount_selectVerifier, e₁, e₂]

/-- **`#P` is closed under multiplication**: the two verifiers read disjoint parts of the
certificate. -/
theorem mul_mem {f₁ f₂ : α → ℕ} (h₁ : f₁ ∈ SharpP enc) (h₂ : f₂ ∈ SharpP enc) :
    f₁ * f₂ ∈ SharpP enc := by
  obtain ⟨p₁, V₁, hV₁, hf₁⟩ := mem_SharpP.mp h₁
  obtain ⟨p₂, V₂, hV₂, hf₂⟩ := mem_SharpP.mp h₂
  refine ⟨p₁ + p₂, andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂, by fun_prop,
    fun a => ?_⟩
  rw [Pi.mul_apply, hf₁ a, hf₂ a, Polynomial.eval_add, acceptCount_andVerifier]

/-- The function `2 ^ q(n)`, where `n` is the length of the encoded instance, is in `#P`: every
certificate of length `q(n)` is accepted. -/
theorem two_pow_mem (q : Polynomial ℕ) : (fun a => 2 ^ q.eval (enc a).length) ∈ SharpP enc :=
  ⟨q, fun _ => true, .const true, fun a => (acceptCount_true a _).symm⟩

/-- The constant function `1` is in `#P`: the empty certificate is accepted. -/
theorem one_mem : (1 : α → ℕ) ∈ SharpP enc :=
  ⟨0, fun _ => true, .const true, fun a => by simp⟩

/-- `#P` as a subsemiring of the functions to `ℕ`. -/
def subsemiring (enc : α ↪ List Bool) : Subsemiring (α → ℕ) where
  carrier := SharpP enc
  mul_mem' := mul_mem
  one_mem' := one_mem
  add_mem' := add_mem
  zero_mem' := zero_mem

@[simp]
theorem coe_subsemiring : (subsemiring enc : Set (α → ℕ)) = SharpP enc :=
  rfl

@[simp]
theorem mem_subsemiring {f : α → ℕ} : f ∈ subsemiring enc ↔ f ∈ SharpP enc :=
  Iff.rfl

/-- `#P` is closed under adding one. -/
theorem add_one_mem {f : α → ℕ} (h : f ∈ SharpP enc) : f + 1 ∈ SharpP enc :=
  add_mem h one_mem

/-- The constant functions are in `#P`. -/
theorem natCast_mem (n : ℕ) : (n : α → ℕ) ∈ SharpP enc :=
  _root_.natCast_mem (subsemiring enc) n

/-- `#P` is closed under powers. -/
theorem pow_mem {f : α → ℕ} (h : f ∈ SharpP enc) (n : ℕ) : f ^ n ∈ SharpP enc :=
  (subsemiring enc).pow_mem h n

/-- `#P` is closed under multiplication by `2 ^ q(n)`, where `n` is the length of the encoded
instance. -/
theorem two_pow_mul_mem (q : Polynomial ℕ) {f : α → ℕ} (h : f ∈ SharpP enc) :
    (fun a => 2 ^ q.eval (enc a).length * f a) ∈ SharpP enc :=
  mul_mem (two_pow_mem q) h

/-- `#P` is closed under finite sums. -/
theorem sum_mem {ι : Type*} (s : Finset ι) {f : ι → α → ℕ} (h : ∀ i ∈ s, f i ∈ SharpP enc) :
    ∑ i ∈ s, f i ∈ SharpP enc :=
  (subsemiring enc).sum_mem h

/-- `#P` is closed under finite products. -/
theorem prod_mem {ι : Type*} (s : Finset ι) {f : ι → α → ℕ} (h : ∀ i ∈ s, f i ∈ SharpP enc) :
    ∏ i ∈ s, f i ∈ SharpP enc :=
  (subsemiring enc).prod_mem h

/-- **The complementary count**: a function `f` in `#P` is at most `2 ^ p(n)` for a polynomial
`p`, where `n` is the length of the encoded instance, with `2 ^ p(n) - f` also in `#P`: the
negated verifier accepts the rejected certificates. -/
theorem exists_two_pow_sub_mem {f : α → ℕ} (hf : f ∈ SharpP enc) :
    ∃ p : Polynomial ℕ, (∀ a, f a ≤ 2 ^ p.eval (enc a).length) ∧
      (fun a => 2 ^ p.eval (enc a).length - f a) ∈ SharpP enc := by
  obtain ⟨p, V, hV, hf⟩ := hf
  refine ⟨p, fun a => (hf a).trans_le acceptCount_le_two_pow,
    p, fun x => !V x, by fun_prop, fun a => ?_⟩
  beta_reduce
  rw [hf a, acceptCount_not]

/-- A function in `#P`, cast to the integers, is in `GapP`. -/
theorem natCast_mem_GapP {f : α → ℕ} (hf : f ∈ SharpP enc) :
    (fun a => (f a : ℤ)) ∈ GapP enc :=
  ⟨f, hf, 0, zero_mem, fun a => by simp⟩

end SharpP

namespace GapP

/-- A power of two with a length-polynomial exponent is in `GapP`. -/
theorem two_pow_mem (p : Polynomial ℕ) :
    (fun a => (2 : ℤ) ^ p.eval (enc a).length) ∈ GapP enc := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    SharpP.natCast_mem_GapP (SharpP.two_pow_mem (enc := enc) p)

/-- The zero function is in `GapP`. -/
theorem zero_mem : (0 : α → ℤ) ∈ GapP enc :=
  ⟨0, SharpP.zero_mem, 0, SharpP.zero_mem, fun a => by simp⟩

/-- The constant function `1` is in `GapP`. -/
theorem one_mem : (1 : α → ℤ) ∈ GapP enc :=
  ⟨1, SharpP.one_mem, 0, SharpP.zero_mem, fun a => by simp⟩

/-- **`GapP` is closed under addition.** -/
theorem add_mem {g₁ g₂ : α → ℤ} (h₁ : g₁ ∈ GapP enc) (h₂ : g₂ ∈ GapP enc) :
    g₁ + g₂ ∈ GapP enc := by
  obtain ⟨f₁, hf₁, f₂, hf₂, hg₁⟩ := h₁
  obtain ⟨f₃, hf₃, f₄, hf₄, hg₂⟩ := h₂
  refine ⟨f₁ + f₃, SharpP.add_mem hf₁ hf₃, f₂ + f₄, SharpP.add_mem hf₂ hf₄, fun a => ?_⟩
  rw [Pi.add_apply, hg₁ a, hg₂ a, Pi.add_apply, Pi.add_apply]
  push_cast
  ring

/-- **`GapP` is closed under multiplication**:
`(f₁ - f₂) (f₃ - f₄) = (f₁ f₃ + f₂ f₄) - (f₁ f₄ + f₂ f₃)`. -/
theorem mul_mem {g₁ g₂ : α → ℤ} (h₁ : g₁ ∈ GapP enc) (h₂ : g₂ ∈ GapP enc) :
    g₁ * g₂ ∈ GapP enc := by
  obtain ⟨f₁, hf₁, f₂, hf₂, hg₁⟩ := h₁
  obtain ⟨f₃, hf₃, f₄, hf₄, hg₂⟩ := h₂
  refine ⟨f₁ * f₃ + f₂ * f₄, SharpP.add_mem (SharpP.mul_mem hf₁ hf₃) (SharpP.mul_mem hf₂ hf₄),
    f₁ * f₄ + f₂ * f₃, SharpP.add_mem (SharpP.mul_mem hf₁ hf₄) (SharpP.mul_mem hf₂ hf₃),
    fun a => ?_⟩
  simp only [Pi.mul_apply, Pi.add_apply, hg₁ a, hg₂ a]
  push_cast
  ring

/-- `GapP` as a subring of the functions to `ℤ`. -/
def subring (enc : α ↪ List Bool) : Subring (α → ℤ) where
  carrier := GapP enc
  mul_mem' := mul_mem
  one_mem' := one_mem
  add_mem' := add_mem
  zero_mem' := zero_mem
  neg_mem' := neg_mem

@[simp]
theorem coe_subring : (subring enc : Set (α → ℤ)) = GapP enc :=
  rfl

@[simp]
theorem mem_subring {g : α → ℤ} : g ∈ subring enc ↔ g ∈ GapP enc :=
  Iff.rfl

/-- **`GapP` is closed under subtraction.** -/
theorem sub_mem' {g₁ g₂ : α → ℤ} (h₁ : g₁ ∈ GapP enc) (h₂ : g₂ ∈ GapP enc) :
    g₁ - g₂ ∈ GapP enc :=
  (subring enc).sub_mem h₁ h₂

end GapP

/-- A polynomial-time unary certificate length can be padded without changing the count. -/
theorem mem_SharpP_of_polyTime_length {V : α × List Bool → Bool} {r : α → ℕ}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun a => acceptCount V a (r a)) ∈ SharpP enc := by
  obtain ⟨p, hle⟩ := hr.polyBounded.exists_polynomial
  refine ⟨p, andVerifier r V allFalseVerifier, by fun_prop, fun a => ?_⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hle a)
  rw [hk, acceptCount_andVerifier_allFalseVerifier]

/-- Polynomial-time precomposition preserves the exact accepting count. Padding bits are
required to be false, so they do not multiply the number of witnesses. -/
theorem SharpP.comp_mem {β : Type} {encB : β ↪ List Bool} {f : β → ℕ} {g : α → β}
    (hf : f ∈ SharpP encB) (hg : ComputableInPolyTime g enc encB) :
    f ∘ g ∈ SharpP enc := by
  obtain ⟨q, W, hW, hWB⟩ := mem_SharpP.mp hf
  have h := mem_SharpP_of_polyTime_length
    (V := fun x => W (g x.1, x.2))
    (r := fun a => q.eval (encB (g a)).length) (by fun_prop) (by fun_prop)
  change (fun a => acceptCount W (g a) (q.eval (encB (g a)).length)) ∈ SharpP enc at h
  simpa only [← hWB, Function.comp_def] using h

/-- `GapP` is closed under polynomial-time precomposition. -/
theorem GapP.comp_mem {β : Type} {encB : β ↪ List Bool} {f : β → ℤ} {g : α → β}
    (hf : f ∈ GapP encB) (hg : ComputableInPolyTime g enc encB) :
    f ∘ g ∈ GapP enc := by
  obtain ⟨f₁, h₁, f₂, h₂, h⟩ := hf
  exact ⟨f₁ ∘ g, SharpP.comp_mem h₁ hg, f₂ ∘ g, SharpP.comp_mem h₂ hg, fun a => h (g a)⟩

end Cslib.Complexity
